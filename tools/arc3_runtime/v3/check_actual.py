"""Integration test, not a gameplay limit or a score benchmark."""
from pathlib import Path
import hashlib,json,os,re,socket,sys,time

PINNED = {
 'lean_bridge.py':'c471b48da7650a0e0268fd94c3212180b337124fce182781dc9f6860f573bd08',
 'proof_env.py':'2b463e88bf089a9fdd832f1506d34fd60419192dbb732d90c890a6484ad0664d',
 'proof_ppo.py':'2071202579dc4dee68626cbe7725d6258d9f10a5f719c26a47977c9e834768fb',
}

def main():
    root=Path(sys.argv[1]).resolve();out=Path(sys.argv[2]).resolve();out.mkdir(parents=True,exist_ok=True)
    here=Path(__file__).parent
    hashes={name:hashlib.sha256((here/name).read_bytes()).hexdigest() for name in PINNED}
    (out/'source_hashes.json').write_text(json.dumps({'expected':PINNED,'actual':hashes},indent=2)+'\n')
    assert hashes == PINNED, ('not byte-identical to delivered v3 modules',hashes)
    import numpy,torch,optuna
    from lean_bridge import LeanREPL,ReachSession,errors,tactic_result,LeanProtocolError
    from proof_env import ProofTask
    from proof_ppo import ProofTrainer
    # Reject accidental Python networking during the test; external installation
    # already finished. Lean uses only the packaged executable and libraries.
    def no_network(*args,**kwargs):raise RuntimeError('Network disabled in integration test')
    socket.create_connection=no_network;socket.socket.connect=no_network
    cfg=json.loads((root/'arc3-runtime.json').read_text())
    def expand(v):
        v=str(v).replace('${RUNTIME}',str(root))
        return re.sub(r'\$\{([A-Za-z_][A-Za-z_0-9]*)\}',lambda m:os.environ.get(m[1],''),v)
    report={'actual_lean':True,'mock':False,'source_hashes_match_v3':True,
      'scope':'synthetic finite proof tasks using delivered v3 learning code',
      'kaggle_execution':False,'official_submission':False,'gameplay_limits_added':False,
      'numpy_version':numpy.__version__,'torch_version':torch.__version__,'optuna_version':optuna.__version__}
    repl=LeanREPL([expand(x) for x in cfg['command']],cwd=expand(cfg['cwd']),
         env={k:expand(v) for k,v in cfg['env'].items()},rpc_timeout=cfg.get('rpc_timeout',30))
    original=repl.request
    protocol=(out/'actual_protocol.jsonl').open('w')
    def record(request):
        response=original(request)
        protocol.write(json.dumps({'request':request,'response':response})+'\n');protocol.flush()
        return response
    repl.request=record
    trainer=None;started=time.monotonic()
    try:
        session=ReachSession(repl)
        bad=repl.request({'cmd':'example : False := by exact True.intro','env':session.base_env})
        assert errors(bad);report['false_proposition_rejected']=True
        for response in ({'proofState':1},{'proofState':1,'goals':None}):
            try:tactic_result(response)
            except LeanProtocolError:pass
            else:raise AssertionError('incomplete response accepted')
        report['missing_goals_rejected']=True
        edges=((0,1,1),(1,2,2))
        session.start(edges,0,2)
        assert session.advance((0,9,2))[0]=='error'
        report['unrecorded_edge_rejected']=True
        assert session.advance(edges[0])[0]=='open'
        assert session.advance(edges[1])[0]=='open'
        assert session.advance(None)[0]=='complete'
        cert=session.finish()
        (out/'direct_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
        report['full_theorem_and_axioms_rechecked']=True
        trainer=ProofTrainer(session,seed=0,output=out/'training')
        initial=trainer.learner.state();weights_changed=False
        task=ProofTask(((0,1,1),(0,2,2),(2,3,2)),0,1,scope='synthetic-real-lean-validation')
        # A finite validation run only. No limits are written to the agent.
        for _ in range(150):
            trainer.prove(task)
            if trainer.all_updates:
                current=trainer.learner.state()
                weights_changed |= any(not torch.equal(initial[k],current[k]) for k in initial)
            if trainer.statistics()['optuna_trials_completed']>=1:break
        stats=trainer.statistics();assert stats['ppo_updates']>=2,stats
        assert stats['optuna_trials_completed']>=1,stats
        assert stats['certificates']>0 and weights_changed,stats
        report.update(status='PASS',weights_changed=weights_changed,statistics=stats,
                      elapsed_seconds=time.monotonic()-started)
    finally:
        if trainer:trainer.close()
        else:repl.close()
        protocol.close()
        report['process_exited']=repl.process.poll() is not None
        (out/'actual_integration.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report,indent=2))
    assert report['process_exited']

if __name__=='__main__':main()
