"""Real-process tests for the ARC3 offline Linux runtime. No game or secrets."""
from pathlib import Path
import hashlib,json,os,queue,re,subprocess,sys,threading

class REPL:
    def __init__(self,root):
        self.root=Path(root).resolve()
        cfg=json.loads((self.root/'arc3-runtime.json').read_text())
        def expand(v):
            v=str(v).replace('${RUNTIME}',str(self.root))
            return re.sub(r'\$\{([A-Za-z_][A-Za-z_0-9]*)\}',lambda m:os.environ.get(m[1],''),v)
        env={**os.environ,**{k:expand(v) for k,v in cfg['env'].items()}}
        self.p=subprocess.Popen([expand(v) for v in cfg['command']],cwd=expand(cfg['cwd']),env=env,
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,bufsize=1)
        self.q=queue.Queue();self.trace=[]
        def reader():
            buf=''
            for line in self.p.stdout:
                if not buf and not line.strip():continue
                buf+=line
                try:r=json.loads(buf)
                except json.JSONDecodeError:continue
                self.q.put(r);buf=''
            self.q.put(RuntimeError('REPL ended: '+self.p.stderr.read()))
        self.t=threading.Thread(target=reader,daemon=True);self.t.start()
    def call(self,request):
        self.p.stdin.write(json.dumps(request)+'\n\n');self.p.stdin.flush()
        r=self.q.get(timeout=60)
        if isinstance(r,BaseException):raise r
        self.trace.append({'request':request,'response':r})
        return r
    def close(self):
        if self.p.poll() is None:
            self.p.terminate()
            try:self.p.wait(timeout=3)
            except subprocess.TimeoutExpired:self.p.kill();self.p.wait()

PRELUDE='''import Lean
namespace ARC3Recorded
abbrev Edge := Nat × Nat × Nat
inductive Reach (edges : List Edge) : Nat → Nat → Prop where
  | done (s : Nat) : Reach edges s s
  | via {s a u t : Nat} (h : (s, a, u) ∈ edges)
      (tail : Reach edges u t) : Reach edges s t
end ARC3Recorded
'''

def errors(r):
    return bool(r.get('error')) or any(m.get('severity')=='error' for m in r.get('messages',[]))

def main():
    root=Path(sys.argv[1]).resolve();out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
    r=REPL(root)
    report={'actual_lean':True,'mock':False,'scope':'explicit recorded graph only','game_score_claim':False}
    try:
        init=r.call({'cmd':PRELUDE});assert not errors(init),init
        assert type(init.get('env')) is int and not init.get('sorries'),init
        env=init['env']
        bad=r.call({'cmd':'example : False := by exact True.intro','env':env})
        assert errors(bad),bad;report['false_proposition_rejected']=True
        goal='ARC3Recorded.Reach [(0, 1, 1), (1, 2, 2)] 0 2'
        start=r.call({'cmd':'example : '+goal+' := by sorry','env':env})
        assert not errors(start) and len(start.get('sorries',[]))==1,start
        state=start['sorries'][0]['proofState'];assert type(state) is int
        bad_edge=r.call({'tactic':'refine ARC3Recorded.Reach.via (s := 0) (a := 9) (u := 2) (by decide) ?_','proofState':state})
        assert errors(bad_edge),bad_edge;report['unrecorded_edge_rejected']=True
        tactics=['refine ARC3Recorded.Reach.via (s := 0) (a := 1) (u := 1) (by decide) ?_',
                 'refine ARC3Recorded.Reach.via (s := 1) (a := 2) (u := 2) (by decide) ?_',
                 'exact ARC3Recorded.Reach.done _']
        for i,tactic in enumerate(tactics):
            step=r.call({'tactic':tactic,'proofState':state})
            assert not errors(step) and type(step.get('proofState')) is int,step
            assert isinstance(step.get('goals'),list) and not step.get('sorries'),step
            assert bool(step['goals']) == (i<2),step
            state=step['proofState']
        report['tactic_mode_complete']=True
        name='arc3_runtime_real_proof'
        theorem='theorem '+name+' : '+goal+' := by\n  '+'\n  '.join(tactics)
        assert 'sorry' not in theorem
        checked=r.call({'cmd':theorem,'env':env})
        assert not errors(checked) and not checked.get('sorries') and type(checked.get('env')) is int,checked
        audit=r.call({'cmd':'#print axioms '+name,'env':checked['env']})
        text='\n'.join(str(m.get('data','')) for m in audit.get('messages',[]))
        assert not errors(audit) and name in text,text
        assert ('does not depend on any axioms' in text or 'depends on axioms' in text),text
        assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text,text
        if 'depends on axioms' in text:
            group=re.search(r'\[(.*?)\]',text,re.S);assert group,text
            assert {a.strip().strip("'") for a in group[1].split(',') if a.strip()} <= {'propext','Classical.choice','Quot.sound'},text
        report.update(status='PASS',full_theorem_rechecked=True,axiom_audit=text)
        report['lean_version']=subprocess.check_output([str(root/'lean/bin/lean'),'--version'],text=True).strip()
        report['repl_sha256']=hashlib.sha256((root/'bin/repl').read_bytes()).hexdigest()
        (out/'runtime-validation.json').write_text(json.dumps(report,indent=2)+'\n')
        (out/'protocol.json').write_text(json.dumps(r.trace,indent=2)+'\n')
        print(json.dumps(report,indent=2))
    finally:r.close()

if __name__=='__main__':main()
