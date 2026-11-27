"""Fixed controller for minimal observation quotients; shadow inputs only."""
from __future__ import annotations
import argparse
from collections import deque
from hashlib import sha256
import json
from pathlib import Path

MAX_STATES = 256
MAX_LETTERS = 32
MAX_INPUT_BYTES = 2_000_000


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(obj):
    return sha256(json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def unique_pairs(items):
    out = {}
    for k, v in items:
        require(k not in out, 'duplicate JSON key')
        out[k] = v
    return out


def read(path):
    require(path.is_file() and not path.is_symlink() and path.stat().st_size <= MAX_INPUT_BYTES,
            'invalid or oversized input')
    return json.loads(path.read_text(), object_pairs_hook=unique_pairs)


def validate(model):
    require(type(model) is dict and set(model) == {'n','observations','actions'}, 'invalid model')
    n = model['n']
    require(type(n) is int and 1 <= n <= MAX_STATES, 'invalid state count')
    for kind in ('observations','actions'):
        maps = model[kind]
        require(type(maps) is dict and len(maps) <= MAX_LETTERS, 'invalid alphabet')
        for name, table in maps.items():
            require(type(name) is str and 0 < len(name) <= 128 and type(table) is list and len(table) == n,
                    'invalid letter/table')
            require(all(type(y) is int and (0 <= y < n if kind == 'actions' else -(2**31) <= y < 2**31)
                        for y in table), 'invalid table value')
    return model


def labels(signatures):
    ids = {}
    return [ids.setdefault(s, len(ids)) for s in signatures]


def vectors(model):
    obs = model['observations']
    return [tuple(obs[k][x] for k in sorted(obs)) for x in range(model['n'])]


def refine(model, start=None):
    n = model['n']; obs = vectors(model)
    p = labels([(0 if start is None else start[x], obs[x]) for x in range(n)])
    actions = [model['actions'][k] for k in sorted(model['actions'])]
    rounds = 0
    while True:
        q = labels([(p[x], tuple(p[a[x]] for a in actions)) for x in range(n)])
        if q == p:
            return p, rounds
        require(len(set(q)) > len(set(p)), 'refinement did not strictly split')
        p = q; rounds += 1
        require(rounds < n, 'refinement bound violated')


def pair(x, y):
    return (x,y) if x < y else (y,x)


def pair_oracle(model):
    """Independent reverse BFS; shortest distinguishing words, not refinement."""
    n = model['n']; obs = vectors(model); actions = model['actions']
    keys = sorted(actions); pairs = [(x,y) for x in range(n) for y in range(x+1,n)]
    rev = {p:[] for p in pairs}; proof = {}; todo = deque()
    for p in pairs:
        x,y = p
        if obs[x] != obs[y]:
            proof[p] = None; todo.append(p)
        for name in keys:
            a = actions[name]; u,v = a[x],a[y]
            if u != v:
                rev[pair(u,v)].append((p,name))
    while todo:
        p = todo.popleft()
        for pred,name in rev[p]:
            if pred not in proof:
                proof[pred] = (name,p); todo.append(pred)
    return proof


def witness(model, proof, x, y):
    p = pair(x,y); require(p in proof, 'indistinguishable pair')
    word = []
    while proof[p] is not None:
        name,p = proof[p]; word.append(name)
    a,b = x,y
    for name in word:
        t = model['actions'][name]; a,b = t[a],t[b]
    obs = vectors(model)
    require(obs[a] != obs[b], 'witness failed')
    return {'states':[x,y], 'word':word, 'endpoints':[a,b],
            'outputs':[list(obs[a]),list(obs[b])]}


def quotient(model, p):
    obs = vectors(model); keys = sorted(model['actions']); rows = {}
    for x,c in enumerate(p):
        sig = {'observation':list(obs[x]), 'next':{k:p[model['actions'][k][x]] for k in keys}}
        require(rows.setdefault(c,sig) == sig, 'unstable quotient')
    return [rows[c] for c in range(len(rows))]


def checkpoint(model, p):
    return {'schema':1, 'model_sha256':digest(model), 'partition':p}


def check_extension(old, new):
    require(old['n'] <= new['n'], 'underlying states may only be appended')
    for kind in ('observations','actions'):
        require(all(k in new[kind] and new[kind][k][:old['n']] == v
                    for k,v in old[kind].items()), 'old letters must agree on old states')


def update(model, previous_model=None, prior=None):
    validate(model); require((previous_model is None) == (prior is None), 'missing prior input')
    n = model['n']; old_n = n; old_p = [0]*n
    if previous_model is not None:
        validate(previous_model); check_extension(previous_model,model)
        old_n = previous_model['n']; old_p,_ = refine(previous_model)
        require(checkpoint(previous_model,old_p) == prior, 'invalid previous checkpoint')
    # New states may be equivalent to old ones. Never pre-separate them.
    p, rounds = refine(model,old_p if old_n == n else None)
    require(all(old_p[x] == old_p[y] or p[x] != p[y]
                for x in range(old_n) for y in range(x+1,old_n)), 'lost old distinction')
    # Audit every unordered pair independently, including indistinguishable ones.
    proof = pair_oracle(model)
    require(all((p[x] != p[y]) == ((x,y) in proof) for x in range(n) for y in range(x+1,n)),
            'minimality audit failed')
    q = quotient(model,p)
    groups = {}; splits = []
    for x in range(old_n):
        groups.setdefault(old_p[x],{}).setdefault(p[x],x)
    for children in groups.values():
        reps = list(children.values())
        for x in reps[1:]:
            splits.append(dict(witness(model,proof,reps[0],x),kind='split'))
    represented = set(p[:old_n])
    for x in range(old_n,n):
        if p[x] not in represented:
            splits.append(dict(witness(model,proof,0,x),kind='new_class'))
            represented.add(p[x])
    before, after = len(set(old_p)),len(q)
    require(len(splits) == after-before, 'split count mismatch')
    return checkpoint(model,p), {'status':'REFINED' if after>before else 'NO_NEW_DISTINCTION',
            'before':before, 'after':after, 'rounds':rounds, 'audited_pairs':n*(n-1)//2,
            'split_witnesses':splits, 'observation_order':sorted(model['observations']), 'quotient':q}


def demo():
    n=8; model={'n':n,'observations':{},'actions':{'cycle':[(x+1)%n for x in range(n)]}}
    previous=prior=None; counts=[]; reports=[]
    steps=[None,('observations','parity',[x%2 for x in range(n)]),
           ('observations','mod4',[x%4 for x in range(n)]),
           ('observations','redundant_parity',[x%2 for x in range(n)]),
           ('actions','swap01',[1,0,*range(2,n)]),('actions','identity',list(range(n)))]
    for step in steps:
        model=json.loads(json.dumps(model))
        if step:
            k,name,table=step; model[k][name]=table
        prior,report=update(model,previous,prior); previous=model
        counts.append(report['after']); reports.append({'step':None if step is None else step[1],
                                                       'count':report['after'],'splits':len(report['split_witnesses'])})
    require(counts == [1,2,4,4,8,8], 'demo regression')
    model=json.loads(json.dumps(previous)); model['n']=9
    for table in model['observations'].values(): table.append(table[0])
    for table in model['actions'].values(): table.append(table[0])
    prior,report=update(model,previous,prior); previous=model
    require(report['after']==8 and prior['partition'][8]==prior['partition'][0], 'new equivalent state was not merged')
    reports.append({'step':'append_equivalent_state','count':8,'splits':0})
    model=json.loads(json.dumps(previous)); model['observations']['marker']=[0]*8+[1]
    prior,report=update(model,previous,prior)
    require(report['after']==9 and len(report['split_witnesses'])==1,'new state did not separate')
    reports.append({'step':'new_marker','count':9,'splits':1})
    return reports


def selftest():
    reports=demo(); cases=0
    # Exhaust all 3-state binary observers and all 3-state transformations.
    from itertools import product
    for obs in product(range(2),repeat=3):
        for a in product(range(3),repeat=3):
            m={'n':3,'observations':{'o':list(obs)},'actions':{'a':list(a)}}
            state,r=update(m); cases+=1
            # With three states, length 0..2 suffices for distinctions.
            traces=[]
            for x in range(3):
                traces.append((obs[x],obs[a[x]],obs[a[a[x]]]))
            require(state['partition']==labels(traces),'bounded trace oracle mismatch')
    # Explicit delayed distinction with a noninjective action.
    m={'n':4,'observations':{'o':[0,0,0,1]},'actions':{'a':[1,2,3,3]}}
    s,r=update(m); require(r['after']==4 and len(witness(m,pair_oracle(m),0,1)['word'])==2,'delayed witness drift')
    bad=dict(s,partition=[0]*4)
    try: update(m,m,bad)
    except ValueError: pass
    else: raise AssertionError('tampered checkpoint accepted')
    try: update({'n':4,'observations':{},'actions':m['actions']},m,s)
    except ValueError: pass
    else: raise AssertionError('removed observation accepted')
    s2,r2=update(m,m,s); require(s==s2 and r2['status']=='NO_NEW_DISTINCTION','idempotence failed')
    # A genuinely new observable class may also appear at state adjunction.
    small={'n':1,'observations':{'o':[0]},'actions':{}}
    big={'n':2,'observations':{'o':[0,1]},'actions':{}}
    prev,_=update(small); _,r3=update(big,small,prev)
    require(r3['after']==2 and r3['split_witnesses'][0]['kind']=='new_class','new class witness drift')
    print(json.dumps({'status':'PASS','demo':reports,'exhaustive_three_state_cases':cases,
                      'delayed_noninjective_witness_length':2,'tamper_rejected':True,
                      'removal_rejected':True,'idempotent':True},sort_keys=True))


def forge_demo(state_path,semantic_path):
    from tools.autonomy import forge_lean_monoid as m
    from tools.autonomy import forge_lean_evolution as e
    from tools.autonomy import semantic_forge as sf
    state=e.read_history(state_path); sem=sf.validate_state(sf.read(semantic_path))
    seeds=m.finite_seeds(); accepted,_=m.reconstruct(state,sem,seeds)
    tables=e.roots(sem,len(sem['receipts']),seeds); tables.update(accepted)
    current={'n':256,'observations':{},'actions':{}}; old=prior=None; reports=[]
    prior,r=update(current); old=current; reports.append({'added':'none','states':r['after']})
    current=json.loads(json.dumps(old)); current['observations']['parity']=[x%2 for x in range(256)]
    prior,r=update(current,old,prior); old=current; reports.append({'added':'parity','states':r['after']})
    for name,table in tables.items():
        current=json.loads(json.dumps(old)); current['actions'][name]=table
        prior,r=update(current,old,prior); old=current
        reports.append({'added':name,'states':r['after'],'splits':len(r['split_witnesses'])})
    require(reports[-1]['states']==256,'snapshot parity did not separate all states')
    return {'status':'PASS','scope':'pinned_forge_snapshot_shadow','stages':reports}


def main():
    p=argparse.ArgumentParser(); p.add_argument('--selftest',action='store_true')
    p.add_argument('--forge-demo',action='store_true'); p.add_argument('--state',type=Path)
    p.add_argument('--semantic',type=Path); p.add_argument('--model',type=Path)
    p.add_argument('--previous-model',type=Path); p.add_argument('--resume',type=Path)
    p.add_argument('--output',type=Path); a=p.parse_args()
    if a.selftest: selftest(); return
    if a.forge_demo:
        require(a.state and a.semantic,'fixture inputs required')
        print(json.dumps(forge_demo(a.state,a.semantic),sort_keys=True)); return
    require(a.model and a.output and not a.output.exists(),'fresh output and model required')
    require(bool(a.previous_model)==bool(a.resume),'both previous inputs required')
    s,r=update(read(a.model),read(a.previous_model) if a.previous_model else None,
               read(a.resume) if a.resume else None)
    a.output.mkdir(parents=True,exist_ok=False)
    for name,data in [('checkpoint.json',s),('report.json',r)]:
        (a.output/name).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:r[k] for k in ('status','before','after','audited_pairs')}))

if __name__=='__main__': main()
