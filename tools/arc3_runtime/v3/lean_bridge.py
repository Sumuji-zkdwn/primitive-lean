"""Strict JSON Lean REPL transport. No missing-goals success; no game access.

The bootstrap `sorry` creates a REPL goal ONLY. Acceptance rechecks the complete
script as a fresh theorem with no sorry, then audits its axioms. A completed
proofState alone is not a certificate. See SOURCE_MAPPING.md for proof scope.
"""
from __future__ import annotations
import atexit, json, os, queue, re, signal, subprocess, tempfile, threading
from pathlib import Path
from typing import Any

class LeanError(RuntimeError): pass
class LeanProtocolError(LeanError): pass


def errors(response: dict) -> list:
    if not isinstance(response, dict):
        raise LeanProtocolError('REPL response is not an object')
    out=[]
    for key in ('error','message'):
        if response.get(key): out.append(str(response[key]))
    messages=response.get('messages', [])
    if not isinstance(messages,list): raise LeanProtocolError('invalid messages field')
    for m in messages:
        if not isinstance(m,dict): raise LeanProtocolError('invalid message')
        if str(m.get('severity','')).lower()=='error': out.append(m)
    return out


def tactic_result(response: dict) -> str:
    if errors(response): return 'error'
    if type(response.get('proofState')) is not int:
        raise LeanProtocolError('tactic response lacks proofState')
    if 'goals' not in response or not isinstance(response['goals'], list):
        raise LeanProtocolError('tactic response lacks explicit goals array')
    if any(not isinstance(g,str) for g in response['goals']):
        raise LeanProtocolError('invalid goal element')
    if response.get('sorries'): raise LeanProtocolError('tactic introduced a sorry')
    return 'complete' if response['goals']==[] else 'open'


class LeanREPL:
    """One request at a time; blank-line framing; process group cleanup.

    rpc_timeout is a transport fault detector, not a game/learning time budget.
    A timeout never means success, never resends an uncertain request, and never
    produces an accepted proof. Set it to None to wait without a transport cap.
    """
    def __init__(self, command, *, cwd=None, env=None, rpc_timeout=30.0):
        if not command or not all(isinstance(x,str) for x in command):
            raise ValueError('explicit REPL argv required')
        self.command=list(command); self.cwd=cwd; self.timeout=rpc_timeout
        self._queue=queue.Queue(); self._lock=threading.Lock(); self.closed=False
        self.stderr=tempfile.TemporaryFile(mode='w+b')
        self.process=subprocess.Popen(self.command,cwd=cwd,env={**os.environ,**(env or {})},
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=self.stderr,
            text=True,encoding='utf-8',bufsize=1,start_new_session=os.name=='posix')
        self.reader=threading.Thread(target=self._read,daemon=True)
        self.reader.start(); atexit.register(self.close)
    def _read(self):
        buf=''
        try:
            for line in self.process.stdout:
                if not line.strip() and not buf: continue
                buf+=line
                if len(buf)>8*1024*1024: raise LeanProtocolError('oversized REPL response')
                try: value=json.loads(buf)
                except json.JSONDecodeError: continue
                self._queue.put(value);buf=''
            self._queue.put(LeanProtocolError('REPL exited before a response'+(' (partial JSON)' if buf else '')))
        except BaseException as e:self._queue.put(e)
    def request(self,payload):
        with self._lock:
            if self.closed: raise LeanProtocolError('REPL is closed')
            try:
                self.process.stdin.write(json.dumps(payload,ensure_ascii=True)+'\n\n')
                self.process.stdin.flush()
                result=self._queue.get(timeout=self.timeout)
            except queue.Empty as e:
                self.close();raise LeanProtocolError('REPL response timeout; no retry') from e
            except (BrokenPipeError,OSError) as e:
                self.close();raise LeanProtocolError('REPL transport failed; no retry') from e
            if isinstance(result,BaseException):raise LeanProtocolError(str(result)) from result
            if not isinstance(result,dict):raise LeanProtocolError('REPL response must be an object')
            return result
    def close(self):
        if self.closed:return
        self.closed=True
        p=self.process
        if p.poll() is None:
            try:
                if os.name=='posix':os.killpg(p.pid,signal.SIGTERM)
                else:p.terminate()
                p.wait(timeout=2)
            except (subprocess.TimeoutExpired,ProcessLookupError):
                if p.poll() is None:
                    if os.name=='posix':os.killpg(p.pid,signal.SIGKILL)
                    else:p.kill()
                    p.wait()
        for stream in (p.stdin,p.stdout,self.stderr):
            if stream:
                try:stream.close()
                except OSError:pass
        if threading.current_thread() is not self.reader:self.reader.join(timeout=1)
        atexit.unregister(self.close)
    def __enter__(self):return self
    def __exit__(self,*exc):self.close()


PRELUDE='''import Lean
namespace ARC3Recorded
abbrev Edge := Nat × Nat × Nat
inductive Reach (edges : List Edge) : Nat → Nat → Prop where
  | done (s : Nat) : Reach edges s s
  | via {s a u t : Nat} (h : (s, a, u) ∈ edges)
      (tail : Reach edges u t) : Reach edges s t
end ARC3Recorded
'''


def nat(n):
    if type(n) is not int or n<0:raise ValueError('nonnegative integer required')
    return str(n)

def goal_text(edges,start,target):
    rows=', '.join('('+', '.join(nat(n) for n in e)+')' for e in edges)
    return f'ARC3Recorded.Reach [{rows}] {nat(start)} {nat(target)}'

class ReachSession:
    """Proof search over a fixed, explicit recorded finite graph, not the game."""
    def __init__(self,repl, *, imports=()):
        self.repl=repl;self.serial=0;self.bootstrap_goals=0;self.accepted=0
        for name in imports:
            if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',name):raise ValueError('invalid module name')
        prelude=''.join('import '+n+'\n' for n in imports)+PRELUDE
        r=self.repl.request({'cmd':prelude})
        if errors(r) or type(r.get('env')) is not int or r.get('sorries'):
            raise LeanError('Lean prelude/import failed: '+str(r))
        self.base_env=r['env'];self.active=False
    def start(self,edges,start,target):
        self.goal=goal_text(edges,start,target);self.serial+=1;self.script=[];self.active=False
        r=self.repl.request({'cmd':f'example : {self.goal} := by sorry','env':self.base_env})
        s=r.get('sorries')
        if errors(r) or not isinstance(s,list) or len(s)!=1 or type(s[0].get('proofState')) is not int:
            raise LeanProtocolError('expected exactly one bootstrap proofState: '+str(r))
        self.proof_state=s[0]['proofState'];self.active=True;self.last_status='open';self.bootstrap_goals+=1
        return r
    def advance(self,edge):
        if not self.active:raise LeanProtocolError('no active proof')
        if edge is None:tactic='exact ARC3Recorded.Reach.done _'
        else:
            s,a,u=edge
            tactic=f'refine ARC3Recorded.Reach.via (s := {nat(s)}) (a := {nat(a)}) (u := {nat(u)}) (by decide) ?_'
        r=self.repl.request({'tactic':tactic,'proofState':self.proof_state})
        status=tactic_result(r)
        if status=='error':return status,r
        self.proof_state=r['proofState'];self.script.append(tactic);self.last_status=status
        return status,r
    def finish(self):
        """Re-elaborate without bootstrap sorry, then require a kernel axiom report."""
        if not self.active:raise LeanProtocolError('no active proof')
        if self.last_status!='complete':raise LeanProtocolError('proof state is not explicitly complete')
        name=f'arc3_recorded_path_{self.serial}'
        script='\n  '.join(self.script)
        if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',script):
            raise LeanError('forbidden proof token')
        r=self.repl.request({'cmd':f'theorem {name} : {self.goal} := by\n  {script}', 'env':self.base_env})
        if errors(r) or type(r.get('env')) is not int or r.get('sorries'):
            raise LeanError('full theorem did not recheck: '+str(r))
        audit=self.repl.request({'cmd':f'#print axioms {name}','env':r['env']})
        text='\n'.join(str(m.get('data',m.get('message',''))) for m in audit.get('messages',[]))
        if errors(audit) or name not in text or not re.search(r'(does not depend on any axioms|depends on axioms)',text):
            raise LeanProtocolError('missing explicit axiom audit: '+str(audit))
        # For generated finite-graph proofs only core logical axioms are allowed.
        if 'sorryAx' in text or 'Lean.ofReduceBool' in text:
            raise LeanError('untrusted axiom in completed theorem')
        if 'depends on axioms' in text:
            group=re.search(r'\[(.*?)\]',text,re.S)
            if group is None:raise LeanProtocolError('cannot parse axiom report')
            axioms={x.strip().strip("'") for x in group[1].split(',') if x.strip()}
            if not axioms.issubset({'propext','Classical.choice','Quot.sound'}):
                raise LeanError('unexpected axiom: '+str(axioms))
        self.active=False;self.accepted+=1
        return {'scope':'explicit_recorded_graph_only','theorem':name,'goal':self.goal,
                'tactics':list(self.script),'axiom_report':text,'actual_game_success_proved':False}
    def close(self):self.repl.close()
