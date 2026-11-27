"""Bounded synthesis of saturation-preserving expansion rules (shadow only)."""
from __future__ import annotations
import argparse
from itertools import product
import json
from pathlib import Path
import hashlib

OPS = ('cycle', 'swap', 'collapse')
SHAPES = ('point', 'product2', 'product3')
ZERO = '0' * 64
MAX_BITS = 1025
MAX_ROWS = 12


def require(ok, why):
    if not ok:
        raise ValueError(why)


def digest(x):
    return hashlib.sha256(json.dumps(x, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def canon(n, op, x):
    if op == 'cycle':
        return (x + 1) % n
    if op == 'swap':
        return 1-x if x < 2 else x
    if op == 'collapse':
        return 1 if x == 0 else x
    raise ValueError('unknown parent operation')


def local(axis, op, guard=()):
    return {'op':op, 'axis':axis, 'guard':[[j,v] for j,v in guard]}


def guard_space(d, axis):
    others = [j for j in range(d) if j != axis]
    for values in product((None, 'zero', 'last'), repeat=d-1):
        yield tuple((j,v) for j,v in zip(others,values) if v is not None)


def rules(shape):
    if shape == 'point':
        for anchor, collapse in product(('zero','last'), ('lift','bridge')):
            yield {'shape':shape, 'anchor':anchor, 'collapse':collapse}
        return
    d = int(shape[-1])
    rotations = [local(i,'cycle') for i in range(d)]
    swaps = [[local(i,'swap',g) for g in guard_space(d,i)] for i in range(d)]
    collapses = [local(i,'collapse',g) for i in range(d) for g in guard_space(d,i)]
    for combo in product(*swaps,collapses):
        yield {'shape':shape, 'gates':rotations+list(combo)}


def cardinality(n, shape):
    require(shape in SHAPES and type(n) is int and n>=2,'invalid shape or cardinality')
    return n+1 if shape=='point' else n**int(shape[-1])


def certify(n, rule):
    """Sound, sufficient structural criterion, not a general monoid decision procedure.

    For a product, independent translations conjugate each isolated axis
    transposition to every edge of that axis. The Cartesian grid is connected;
    its edge transpositions generate the symmetric group. An isolated collapse
    then generates every elementary collapse by permutation conjugation.
    For a point extension, lift the old symmetric group and connect the added
    point by a bridge transposition. Either collapse choice has rank N-1.
    Every map factors into fiber collapses followed by a permutation.
    """
    require(type(rule) is dict and rule.get('shape') in SHAPES,'bad rule')
    shape=rule['shape']; N=cardinality(n,shape)
    if shape=='point':
        require(set(rule)=={'shape','anchor','collapse'} and rule['anchor'] in ('zero','last')
                and rule['collapse'] in ('lift','bridge'),'bad point rule')
        return {'theorem':'connected_extension_plus_elementary_collapse','N':N,
                'alphabet_size':4,'rank_collapse':N-1,'rank_bound_old_lift':n,
                'scope':'classical_structural_certificate'}
    d=int(shape[-1]); gates=rule.get('gates')
    require(set(rule)=={'shape','gates'} and type(gates) is list and len(gates)==2*d+1,'bad product alphabet')
    rotations=set(); swaps=set(); collapses=0
    for g in gates:
        require(type(g) is dict and set(g)=={'op','axis','guard'} and g['op'] in OPS
                and type(g['axis']) is int and 0<=g['axis']<d and type(g['guard']) is list,'bad gate')
        axis=g['axis']; guard=g['guard']; axes=set()
        for term in guard:
            require(type(term) is list and len(term)==2 and type(term[0]) is int
                    and 0<=term[0]<d and term[0]!=axis and term[0] not in axes
                    and term[1] in ('zero','last'),'bad guard')
            axes.add(term[0])
        if g['op']=='cycle':
            require(not guard and axis not in rotations,'not a free translation')
            rotations.add(axis)
        else:
            require(len(axes)==d-1,'not an isolated elementary operation')
            if g['op']=='swap':
                require(axis not in swaps,'duplicate axis transposition')
                swaps.add(axis)
            else:
                collapses+=1
    require(rotations==swaps==set(range(d)) and collapses==1,'incomplete connectivity basis')
    return {'theorem':'cartesian_edge_transpositions_plus_elementary_collapse','N':N,
            'alphabet_size':len(gates),'rank_collapse':N-1,
            'rank_bound_independent_singular':(n-1)*n**(d-1),
            'translation_axes':sorted(rotations),'edge_axes':sorted(swaps),
            'scope':'classical_structural_certificate'}


def evaluate(n, rule, letter, x):
    """Executable child alphabet, using abstract available parent operations."""
    N=cardinality(n,rule['shape'])
    require(type(x) is int and 0<=x<N,'state outside domain')
    if rule['shape']=='point':
        require(0<=letter<4,'bad letter')
        a=0 if rule['anchor']=='zero' else n-1
        if letter<2:
            return canon(n,OPS[letter],x) if x<n else x
        if letter==2:
            return n if x==a else a if x==n else x
        if rule['collapse']=='lift':
            return canon(n,'collapse',x) if x<n else x
        return a if x==n else x
    d=int(rule['shape'][-1]); g=rule['gates'][letter]
    coord=[(x//n**i)%n for i in range(d)]
    if all(coord[j]==(0 if v=='zero' else n-1) for j,v in g['guard']):
        i=g['axis']; coord[i]=canon(n,g['op'],coord[i])
    return sum(v*n**i for i,v in enumerate(coord))


def choose(n, max_bits, policy, allowed):
    require(policy in ('growth','compact') and type(allowed) is list and allowed
            and len(set(allowed))==len(allowed) and all(s in SHAPES for s in allowed),'invalid search policy')
    stats={}; best=None
    for shape in allowed:
        N=cardinality(n,shape)
        st={'generated':0,'certified':0,'rejected':0,'over_budget':N.bit_length()>max_bits}
        stats[shape]=st
        if st['over_budget']:
            continue
        for rule in rules(shape):
            st['generated']+=1
            try:
                proof=certify(n,rule)
            except ValueError:
                st['rejected']+=1
                continue
            st['certified']+=1
            size=proof['alphabet_size']
            score=(-N,size) if policy=='growth' else (size,-N)
            key=(*score,json.dumps(rule,sort_keys=True,separators=(',',':')))
            if best is None or key<best[0]:
                best=(key,rule,proof)
    return (None,None,stats) if best is None else (*best[1:],stats)


def chain(payload, previous):
    row=dict(payload,previous_sha256=previous)
    return dict(row,chain_sha256=digest(row))


def transition(rows, max_bits, policy, allowed):
    old=rows[-1]
    require(old['status']=='SATURATED','parent saturation not established')
    rule,proof,stats=choose(old['n'],max_bits,policy,allowed)
    if rule is None:
        return None,stats
    return chain({'level':len(rows),'n':proof['N'],'status':'SATURATED','rule':rule,
                  'certificate':proof,'search':stats},old['chain_sha256']),stats


def advance(root, config, prior, steps):
    require(set(config)=={'max_bits','policy','allowed'} and type(config['max_bits']) is int
            and 2<=config['max_bits']<=MAX_BITS and type(steps) is int and 0<=steps<MAX_ROWS,'invalid budgets')
    require(root['n'].bit_length()<=config['max_bits'],'root exceeds budget')
    args=(config['max_bits'],config['policy'],config['allowed'])
    rows=[chain({'level':0,'n':root['n'],'status':'SATURATED','criterion':root},ZERO)]
    if prior is not None:
        require(type(prior) is dict and set(prior)=={'schema','config','rows'} and prior['schema']==1
                and prior['config']==config and type(prior['rows']) is list
                and 1<=len(prior['rows'])<=MAX_ROWS and prior['rows'][0]==rows[0],'invalid history')
        for expected in prior['rows'][1:]:
            row,_=transition(rows,*args)
            require(row is not None and row==expected,'history replay mismatch')
            rows.append(row)
    stop='STEP_BUDGET'; final_search=None
    for _ in range(steps):
        if len(rows)>=MAX_ROWS:
            stop='HISTORY_BUDGET'; break
        row,final_search=transition(rows,*args)
        if row is None:
            stop='NO_CERTIFIED_RULE_WITHIN_BUDGET'; break
        rows.append(row)
    return {'schema':1,'config':config,'rows':rows},stop,final_search


def exact_closure(n, gens):
    require(2<=n<=4,'exact closure only for n<=4')
    ident=tuple(range(n)); seen={ident}; queue=[ident]
    for f in queue:
        for g in gens:
            h=tuple(g[x] for x in f)
            if h not in seen:
                seen.add(h); queue.append(h)
    return seen


def model_root():
    gens=[tuple(canon(2,op,x) for x in range(2)) for op in OPS]
    require(len(exact_closure(2,gens))==4,'root not saturated')
    return {'kind':'exhaustive_model','n':2,'count':4,'proof_scope':'finite_exact'}


def selftest():
    root=model_root(); counts={}
    # Every small candidate passing the structural test is independently
    # checked by explicit closure, not just the selected candidate.
    for shape in ('point','product2'):
        N=cardinality(2,shape); valid=invalid=0
        for rule in rules(shape):
            try: proof=certify(2,rule)
            except ValueError:
                invalid+=1; continue
            valid+=1
            gens=[tuple(evaluate(2,rule,i,x) for x in range(N)) for i in range(proof['alphabet_size'])]
            require(len(exact_closure(N,gens[:-1]))==__import__('math').factorial(N),'permutation closure mismatch')
            require(len(exact_closure(N,gens))==N**N,'full closure mismatch')
        counts[shape]={'valid':valid,'rejected':invalid}
    require(counts=={'point':{'valid':4,'rejected':0},'product2':{'valid':16,'rejected':38}},'grammar count drift')
    rule,proof,stats=choose(2,65,'growth',list(SHAPES))
    require(rule['shape']=='product3' and stats['product3']['certified']==768 and stats['product3']['generated']==19683,'triple synthesis drift')
    # For every selected product3 gate, check exact moved points on n=2..5.
    for n in range(2,6):
        N=n**3; p=certify(n,rule)
        for i,g in enumerate(rule['gates']):
            v=[evaluate(n,rule,i,x) for x in range(N)]
            if g['op']=='cycle': require(len(set(v))==N and all(x!=y for x,y in enumerate(v)),'cycle drift')
            if g['op']=='swap': require(len(set(v))==N and sum(x!=y for x,y in enumerate(v))==2,'swap drift')
            if g['op']=='collapse': require(len(set(v))==p['rank_collapse'] and sum(x!=y for x,y in enumerate(v))==1,'collapse drift')
    cfg={'max_bits':65,'policy':'growth','allowed':list(SHAPES)}
    a,_,_=advance(root,cfg,None,2); b,_,_=advance(root,cfg,a,2); c,_,_=advance(root,cfg,None,4)
    require(b==c,'restart drift')
    compact,_,_=advance(root,dict(cfg,policy='compact'),None,2)
    require([r['n'] for r in compact['rows']]==[2,3,4],'compact policy drift')
    tiny,stop,_=advance(root,dict(cfg,max_bits=2),None,4)
    require([r['n'] for r in tiny['rows']]==[2,3] and stop=='NO_CERTIFIED_RULE_WITHIN_BUDGET','budget drift')
    bad=json.loads(json.dumps(b)); bad['rows'][1]['rule']['gates'][0]['axis']=1
    try: advance(root,cfg,bad,0)
    except ValueError: pass
    else: raise AssertionError('tampered rule accepted')
    print(json.dumps({'status':'PASS','closure_cross_checks':counts,'search':stats,
                      'growth_sizes':[r['n'] for r in b['rows']], 'compact_sizes':[r['n'] for r in compact['rows']],
                      'resume_equal':True,'tamper_rejected':True,'budget_stop':stop},sort_keys=True))


def main():
    p=argparse.ArgumentParser(); p.add_argument('--selftest',action='store_true')
    p.add_argument('--root',choices=['model','forge'],default='model'); p.add_argument('--state',type=Path)
    p.add_argument('--semantic',type=Path); p.add_argument('--resume',type=Path); p.add_argument('--output',type=Path)
    p.add_argument('--steps',type=int,default=2); p.add_argument('--max-bits',type=int,default=65)
    p.add_argument('--policy',choices=['growth','compact'],default='growth')
    p.add_argument('--allowed',nargs='+',choices=SHAPES,default=list(SHAPES)); p.add_argument('--kernel',action='store_true')
    a=p.parse_args()
    if a.selftest: selftest(); return
    require(a.output is not None and not a.output.exists(),'fresh shadow output required')
    require(2<=a.max_bits<=MAX_BITS and 0<=a.steps<MAX_ROWS,'invalid budgets')
    a.output.mkdir(parents=True)
    if a.root=='forge':
        require(a.state is not None and a.semantic is not None,'root inputs required')
        from tools.autonomy.forge_tower import root_forge
        root=root_forge(a.state,a.semantic,a.output/'root',a.kernel)
    else:
        require(not a.kernel,'kernel option only checks Forge root'); root=model_root()
    prior=json.loads(a.resume.read_text()) if a.resume else None
    cfg={'max_bits':a.max_bits,'policy':a.policy,'allowed':a.allowed}
    ledger,stop,stats=advance(root,cfg,prior,a.steps)
    (a.output/'rules.json').write_text(json.dumps(ledger,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'stop':stop,'sizes':[r['n'] for r in ledger['rows']],
                      'selected':[r['rule']['shape'] for r in ledger['rows'][1:]],
                      'last_search':stats,'scope':'shadow_classical_rules_not_lean_formalized'},sort_keys=True))

if __name__=='__main__': main()
