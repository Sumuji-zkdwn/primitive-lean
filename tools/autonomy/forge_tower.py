"""Proof-guided bounded tower; shadow state only. No production writes."""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from pathlib import Path

GATES = ('cycle', 'swap', 'collapse')
ZERO = '0' * 64
MAX_BITS = 1025
MAX_LEVELS = 12


def require(ok, why):
    if not ok:
        raise ValueError(why)


def digest(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def canonical(n, gate, x):
    require(n >= 2 and gate in GATES and 0 <= x < n, 'bad gate input')
    if gate == 'cycle':
        return (x + 1) % n
    if gate == 'swap':
        return 1-x if x < 2 else x
    return 1 if x == 0 else x


def apply(sizes, i, gate, x):
    """Recursive product AST evaluator, no exponentially large truth tables."""
    require(0 <= i < len(sizes) and gate in GATES and 0 <= x < sizes[i], 'invalid evaluation')
    if i == 0:
        return canonical(sizes[0], gate, x)
    n = sizes[i-1]
    require(sizes[i] == n*n, 'invalid product')
    h, l = divmod(x, n)
    if gate == 'cycle':
        if l == n-1:
            h = apply(sizes, i-1, 'cycle', h)
        l = apply(sizes, i-1, 'cycle', l)
    elif h == 0:
        l = apply(sizes, i-1, gate, l)
    return h*n+l


def compose(f, g):
    return tuple(g[x] for x in f)


def closure(gens, n):
    require(2 <= n <= 4, 'exhaustive closure limited to n<=4')
    identity = tuple(range(n))
    seen, todo = {identity}, [identity]
    for f in todo:
        for g in gens:
            h = compose(f, g)
            if h not in seen:
                seen.add(h)
                todo.append(h)
    return seen


def root_model():
    gens = [tuple(canonical(2,g,x) for x in range(2)) for g in GATES]
    require(len(closure(gens,2)) == 4, 'model root not saturated')
    return {'kind':'exhaustive_model', 'n':2, 'count':4, 'proof_scope':'finite_exact'}


def root_forge(state_path, semantic_path, out, kernel):
    from tools.autonomy import forge_lean_monoid as m
    from tools.autonomy import forge_lean_evolution as evo
    from tools.autonomy import semantic_forge as sf
    state=evo.read_history(state_path)
    semantic=sf.validate_state(sf.read(semantic_path))
    seeds=m.finite_seeds()
    accepted, stages=m.reconstruct(state,semantic,seeds)
    group=m.verify_group(stages)
    tables=evo.roots(semantic,len(semantic['receipts']),seeds)
    tables.update(accepted)
    recipe,v,bound=m.candidate(tables)
    require(group['stage6']=='S_256' and m.rank(v)==255 and bound==175, 'root saturation witness drift')
    require(recipe==['restrict_at','p:reverse',1] and v[1]==64 and all(v[x]==x for x in range(256) if x!=1), 'collapse witness drift')
    proof='finite_replay_plus_classical_theorems'
    if kernel:
        require(evo.seed_replay(out/'seeds')==seeds, 'seed kernel mismatch')
        require(evo.replay(state,semantic,seeds,out/'history')==accepted, 'history kernel mismatch')
        m.certificate(tables,v,bound,out/'rank')
        evo.check_lean(out/'rank')
        proof='kernel_rank_and_history_plus_classical_group_theorems'
    return {'kind':'forge6_plus_rank255_shadow','n':256,'proof_scope':proof,
            'state_sha256':hashlib.sha256(state_path.read_bytes()).hexdigest(),
            'semantic_sha256':hashlib.sha256(semantic_path.read_bytes()).hexdigest(),
            'group_witness_sha256':digest(group),'candidate_sha256':evo.fingerprint(v),
            'candidate_recipe':recipe,'candidate_rank':255,'old_max_singular_rank':bound,
            'canonical_root_scope':'existence_not_compiled_to_original_alphabet'}


def chain(row, previous):
    row=dict(row,previous_sha256=previous)
    return dict(row,chain_sha256=digest(row))


def initial(root):
    return chain({'level':0,'n':root['n'],'status':'SATURATED','criterion':root},ZERO)


def transition(rows):
    old=rows[-1]
    require(old['status']=='SATURATED', 'no saturation proof')
    n=old['n']
    N=n*n
    sizes=[r['n'] for r in rows]+[N]
    # Child generators are fixed typed controlled applications, not arbitrary code.
    # For all h,l: carry = successor mod n^2, controlled swap = (0 1),
    # controlled collapse = 0 -> 1. These identities follow by divmod cases.
    # Cycle conjugates of swap generate S_N; conjugates of collapse yield all
    # elementary merges; fiber collapse then a permutation yields every endomap.
    # The rank N-1 of the child collapse cannot occur in coordinatewise products:
    # a singular direct product has rank <= n(n-1).
    if N <= 65536:
        for gate in GATES:
            require(all(apply(sizes,len(rows),gate,x)==canonical(N,gate,x) for x in range(N)), 'product semantics drift')
        check='exhaustive_three_gate_identities'
    else:
        # This is an explicitly delimited symbolic theorem, not a table search.
        for gate in GATES:
            for x in sorted({0,1,n-1,n,N-1,N-2}):
                require(apply(sizes,len(rows),gate,x)==canonical(N,gate,x), 'symbolic boundary drift')
        check='divmod_identity_theorem_plus_boundary_checks'
    criterion={'kind':'cycle_adjacent_swap_rank_one_collapse','parent_n':n,
               'construction':'product_carry_and_zero_slice_control',
               'rank_new_collapse':N-1,'old_singular_product_rank_bound':n*(n-1),
               'proof_scope':'elementary_classical_theorem_not_lean_formalized','validation':check}
    return chain({'level':len(rows),'n':N,'status':'SATURATED','criterion':criterion},old['chain_sha256'])


def replay(root, stored):
    require(type(stored)==dict and set(stored)=={'schema','rows'} and stored['schema']==1,'invalid ledger')
    rows=stored['rows']
    require(type(rows)==list and 1<=len(rows)<=MAX_LEVELS,'invalid history length')
    rebuilt=[initial(root)]
    for i,row in enumerate(rows):
        if i:
            require((rebuilt[-1]['n']**2).bit_length()<=MAX_BITS,'history exceeds hard limit')
            rebuilt.append(transition(rebuilt))
        require(rebuilt[-1]==row,'history mismatch')
    return rebuilt


def advance(root, prior, steps, max_bits):
    require(type(steps)==int and 0<=steps<=MAX_LEVELS and 2<=max_bits<=MAX_BITS,'invalid work budget')
    rows=replay(root,prior) if prior is not None else [initial(root)]
    require(rows[-1]['n'].bit_length()<=max_bits,'existing state exceeds work budget')
    stop='STEP_BUDGET'
    for _ in range(steps):
        if len(rows)>=MAX_LEVELS or (rows[-1]['n']**2).bit_length()>max_bits:
            stop='SIZE_BUDGET'
            break
        rows.append(transition(rows))
    return {'schema':1,'rows':rows},stop


def selftest():
    # Test multiple distinct small parent sizes, not just binary.
    for n in range(2,7):
        for g in GATES:
            assert all(apply([n,n*n],1,g,x)==canonical(n*n,g,x) for x in range(n*n))
    n=2; N=4
    old=[tuple((f[x//n]*n+g[x%n]) for x in range(N))
         for f in itertools.product(range(n),repeat=n) for g in itertools.product(range(n),repeat=n)]
    perm=[tuple(apply([2,4],1,g,x) for x in range(N)) for g in GATES[:2]]
    collapse=tuple(apply([2,4],1,'collapse',x) for x in range(N))
    assert len(set(old))==16 and collapse not in old
    assert len(closure(perm,N))==24 and len(closure(perm+[collapse],N))==256
    root=root_model()
    a,_=advance(root,None,1,17)
    b,_=advance(root,a,2,17)
    c,_=advance(root,None,3,17)
    assert b==c and [r['n'] for r in b['rows']]==[2,4,16,256]
    d,stop=advance(root,b,2,9)
    assert d==b and stop=='SIZE_BUDGET'
    bad=json.loads(json.dumps(b)); bad['rows'][1]['n']=5
    try:
        replay(root,bad)
    except ValueError:
        pass
    else:
        raise AssertionError('tampered ledger accepted')
    print(json.dumps({'test':'PASS','direct_product':16,'permutation_closure':24,'full_closure':256,'resumed_sizes':[r['n'] for r in b['rows']],'tamper_rejected':True,'budget_stop':stop}))


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--selftest',action='store_true')
    p.add_argument('--root',choices=['model','forge'],default='model')
    p.add_argument('--state',type=Path)
    p.add_argument('--semantic',type=Path)
    p.add_argument('--resume',type=Path)
    p.add_argument('--output',type=Path)
    p.add_argument('--steps',type=int,default=3)
    p.add_argument('--max-bits',type=int,default=65)
    p.add_argument('--kernel',action='store_true')
    a=p.parse_args()
    if a.selftest:
        selftest(); return
    require(a.output is not None and not a.output.exists(),'require fresh shadow output directory')
    require(0<=a.steps<=MAX_LEVELS and 2<=a.max_bits<=MAX_BITS,'invalid work budget')
    if a.root=='forge':
        require(a.state is not None and a.semantic is not None,'root inputs required')
    else:
        require(not a.kernel,'kernel option only applies to Forge rank proof')
    a.output.mkdir(parents=True)
    root=root_model() if a.root=='model' else root_forge(a.state,a.semantic,a.output/'root',a.kernel)
    prior=json.loads(a.resume.read_text()) if a.resume else None
    ledger,stop=advance(root,prior,a.steps,a.max_bits)
    (a.output/'tower.json').write_text(json.dumps(ledger,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':stop,'sizes':[r['n'] for r in ledger['rows']], 'proof_scope':root['proof_scope'],'mode':'shadow_no_production_writes'}))

if __name__=='__main__':
    main()
