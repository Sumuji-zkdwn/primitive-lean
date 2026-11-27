"""Bounded synthesis and reuse of composed expansion rules. Shadow only."""
from __future__ import annotations
import argparse
from itertools import product
import json
from pathlib import Path
from tools.autonomy import forge_rule_search as base

MAX_LENGTH = 6
SHAPES = base.SHAPES
PRIMITIVES = {'point': (1, 1), 'product2': (0, 0, 1), 'product3': (0, 0, 0, 1)}
require = base.require


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[i+j] += x*y
    return tuple(out)


def compose(outer, inner):
    """Exact polynomial substitution; coefficients are ascending."""
    out = (outer[-1],)
    for c in reversed(outer[:-1]):
        out = mul(out, inner)
        out = (out[0]+c, *out[1:])
    return out


def word_poly(word):
    """Independent oracle: apply only the original three shape operations."""
    p = (0, 1)
    for shape in word:
        if shape == 'point':
            p = (p[0]+1, *p[1:])
        elif shape == 'product2':
            p = mul(p, p)
        elif shape == 'product3':
            p = mul(mul(p, p), p)
        else:
            raise ValueError('unknown shape')
    return p


def value(p, n):
    out = 0
    for c in reversed(p):
        out = n*out+c
    return out


def primitive_rules():
    result = {}
    for shape in SHAPES:
        rule, proof, _ = base.choose(2, 65, 'growth', [shape])
        require(rule is not None and proof == base.certify(2, rule), 'seed not certified')
        result[shape] = rule
    return result


def make_row(word, polynomial, parents):
    require(tuple(polynomial) == word_poly(word), 'composition polynomial drift')
    return {'id': 'r:'+base.digest(list(polynomial)), 'word':list(word),
            'polynomial':list(polynomial), 'length':len(word), 'parents':list(parents)}


def synthesize(through, prior=None):
    """Length-stratified quotient by exact cardinality polynomial equality.

    Minimal representatives suffice: if a subword had a shorter equivalent,
    replacing it would shorten the entire word without changing its polynomial.
    No claim of equality of gate semantics or of new primitive expressivity.
    """
    require(type(through) is int and 1 <= through <= MAX_LENGTH, 'bad length budget')
    roots = primitive_rules()
    rows = [make_row([s], PRIMITIVES[s], []) for s in SHAPES]
    layers = [{'length':1, 'pairs':0, 'new':len(rows), 'known':0, 'duplicates':0,
               'total':len(rows)}]
    known = {tuple(r['polynomial']) for r in rows}
    bylen = {1:rows[:]}
    for k in range(2, through+1):
        pending = {}; pairs = old = duplicates = 0
        for i in range(1,k):
            for left in bylen[i]:
                for right in bylen[k-i]:
                    pairs += 1
                    p = compose(right['polynomial'], left['polynomial'])
                    if p in known:
                        old += 1; continue
                    word = left['word']+right['word']
                    key = (word,left['id'],right['id'])
                    if p in pending:
                        duplicates += 1
                        if pending[p][0] <= key:
                            continue
                    pending[p] = (key,make_row(word,p,[left['id'],right['id']]))
        fresh = sorted((v[1] for v in pending.values()),key=lambda r:(r['word'],r['id']))
        require(len({r['id'] for r in rows+fresh})==len(rows)+len(fresh),'id collision')
        rows.extend(fresh); known.update(pending); bylen[k]=fresh
        layers.append({'length':k,'pairs':pairs,'new':len(fresh),'known':old,
                       'duplicates':duplicates,'total':len(rows)})
        require(pairs==old+duplicates+len(fresh),'count drift')
    ledger = {'schema':1,'equivalence':'cardinality_polynomial_only','roots':roots,
              'through':through,'layers':layers,'rows':rows}
    if prior is not None:
        require(type(prior) is dict and type(prior.get('through')) is int
                and 1<=prior['through']<=through,'invalid prior length')
        m=prior['through']
        prefix=dict(ledger,through=m,layers=layers[:m],rows=[r for r in rows if r['length']<=m])
        require(prior==prefix,'prior library replay mismatch')
    return ledger


def apply_macro(root, library, row, max_bits):
    """Recheck each constituent rule on the actual parent size; return a trace."""
    require(type(max_bits) is int and 2<=max_bits<=base.MAX_BITS,'invalid bit budget')
    n=root['n']; require(n>=2 and n.bit_length()<=max_bits,'root over budget')
    trace=[]
    for shape in row['word']:
        N=base.cardinality(n,shape)
        if N.bit_length()>max_bits:
            return None
        rule=library['roots'][shape]
        proof=base.certify(n,rule)
        require(proof['N']==N,'child certificate drift')
        trace.append({'parent_n':n,'n':N,'rule':rule,'certificate':proof})
        n=N
    require(n==value(row['polynomial'],root['n']),'macro semantics drift')
    return {'rule_id':row['id'],'word':row['word'],'polynomial':row['polynomial'],
            'sizes':[root['n']]+[r['n'] for r in trace],'stages':trace,
            'scope':'composed_classical_sufficient_certificates_not_lean_proofs'}


def select(root, library, max_bits):
    best=None; eligible=0
    for row in library['rows']:
        result=apply_macro(root,library,row,max_bits)
        if result is None:
            continue
        eligible+=1
        key=(-result['sizes'][-1],row['length'],row['word'])
        if best is None or key<best[0]:
            best=(key,result)
    return (None if best is None else best[1]),eligible


def selftest():
    a=synthesize(2); b=synthesize(5,a); c=synthesize(5)
    require(b==c,'restart drift')
    # Exhaust every word independently; compare all polynomials and shortest lengths.
    oracle={}
    for k in range(1,6):
        for w in product(SHAPES,repeat=k):
            p=word_poly(w); oracle.setdefault(p,k)
            for n in (2,3,5,256):
                y=n
                for s in w: y=base.cardinality(y,s)
                require(value(p,n)==y,'numerical oracle drift')
    actual={tuple(r['polynomial']):r['length'] for r in b['rows']}
    require(actual==oracle,'bounded quotient incomplete')
    row_by_id={r['id']:r for r in b['rows']}
    for r in b['rows']:
        if r['parents']:
            left,right=[row_by_id[i] for i in r['parents']]
            require(left['word']+right['word']==r['word'] and left['length']+right['length']==r['length'],'broken lineage')
    require(any(all(row_by_id[i]['parents'] for i in r['parents']) and r['parents'] for r in b['rows']),'no macro reentry')
    # Same two shape steps in opposite order need not have equal semantics.
    require(word_poly(('point','product2')) != word_poly(('product2','point')),'noncommutation lost')
    require(word_poly(('product2','product3')) == word_poly(('product3','product2')),'equal cardinality not quotiented')
    root=base.model_root()
    row=next(r for r in b['rows'] if r['word']==['point','point'])
    tr=apply_macro(root,b,row,65); require(tr['sizes']==[2,3,4],'macro trace drift')
    for stage in tr['stages']:
        n=stage['parent_n']; N=stage['n']; rule=stage['rule']
        gens=[tuple(base.evaluate(n,rule,i,x) for x in range(N)) for i in range(stage['certificate']['alphabet_size'])]
        require(len(base.exact_closure(N,gens))==N**N,'small macro closure mismatch')
    chosen,eligible=select({'n':256},b,65)
    require(chosen is not None and chosen['sizes'][-1].bit_length()<=65,'budget violated')
    bad=json.loads(json.dumps(a)); bad['rows'][-1]['polynomial'][0]+=1
    try: synthesize(3,bad)
    except ValueError: pass
    else: raise AssertionError('tampered history accepted')
    require(select({'n':3},b,2)==(None,0),'budget rejection failed')
    print(json.dumps({'status':'PASS','layers':b['layers'],'oracle_words':sum(3**k for k in range(1,6)),
                      'distinct_polynomials':len(actual),'macro_reentry':True,'restart_equal':True,
                      'tamper_rejected':True,'small_macro_closures':[27,256],
                      'sample_256_eligible':eligible,'sample_256_selected':chosen['word'],
                      'sample_256_sizes':chosen['sizes']},sort_keys=True))


def main():
    p=argparse.ArgumentParser(); p.add_argument('--selftest',action='store_true')
    p.add_argument('--root',choices=['model','forge'],default='model'); p.add_argument('--state',type=Path)
    p.add_argument('--semantic',type=Path); p.add_argument('--resume',type=Path); p.add_argument('--output',type=Path)
    p.add_argument('--through',type=int,default=5); p.add_argument('--max-bits',type=int,default=65)
    p.add_argument('--kernel',action='store_true'); a=p.parse_args()
    if a.selftest: selftest(); return
    require(a.output is not None and not a.output.exists(),'fresh shadow output required')
    require(1<=a.through<=MAX_LENGTH and 2<=a.max_bits<=base.MAX_BITS,'bad budget')
    a.output.mkdir(parents=True)
    if a.root=='forge':
        require(a.state is not None and a.semantic is not None,'root inputs required')
        from tools.autonomy.forge_tower import root_forge
        root=root_forge(a.state,a.semantic,a.output/'root',a.kernel)
    else:
        require(not a.kernel,'kernel option applies only to Forge root'); root=base.model_root()
    prior=json.loads(a.resume.read_text()) if a.resume else None
    lib=synthesize(a.through,prior); result,eligible=select(root,lib,a.max_bits)
    report={'root':root,'layers':lib['layers'],'eligible':eligible,'selected':result,
            'status':'MACRO_SELECTED_SHADOW' if result is not None else 'NO_RULE_WITHIN_BUDGET',
            'novelty_scope':'cardinality_polynomial_only_not_new_primitive_expressivity'}
    for name,obj in [('library.json',lib),('report.json',report)]:
        (a.output/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    print(json.dumps(report,sort_keys=True))

if __name__=='__main__': main()
