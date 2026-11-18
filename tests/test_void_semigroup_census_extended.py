"""Exhaustive four-state semigroup census and five-state powerset blowup.

Run: python -m unittest discover -s tests -p test_void_semigroup_census_extended.py -v
"""
from itertools import product
from collections import Counter
import unittest
from test_void_multivalued_completion import (
    partitions, assoc, classes, congruent, abstract,
    associativity_defects, generated_exact_sets,
    stable_partition, set_product, observed_outputs,
)

def semigroups(n=4):
    triples=tuple(product(range(n),repeat=3))
    def propagate(raw):
        table=list(raw)
        while True:
            modified=False
            for a,b,c in triples:
                ab,bc=table[a*n+b],table[b*n+c]
                if ab<0 or bc<0: continue
                left,right=ab*n+c,a*n+bc
                if table[left]>=0 and table[right]>=0:
                    if table[left]!=table[right]: return None
                elif table[left]>=0:
                    table[right]=table[left]
                    modified=True
                elif table[right]>=0:
                    table[left]=table[right]
                    modified=True
            if not modified: return tuple(table)
    def rec(table):
        table=propagate(table)
        if table is None: return
        try: k=table.index(-1)
        except ValueError:
            yield table
            return
        for value in range(n):
            trial=list(table)
            trial[k]=value
            yield from rec(trial)
    yield from rec((-1,)*(n*n))

def cyclic(n):
    return tuple((a+b)%n for a,b in product(range(n),repeat=2))

def affines(n):
    elements=tuple(product(range(n),repeat=2))
    index={v:i for i,v in enumerate(elements)}
    table=tuple(index[((a*c)%n,(a*d+b)%n)]
                for (a,b),(c,d) in product(elements,repeat=2))
    return elements,table

def exact_word(table,blocks,word):
    fs=classes(blocks)
    U=fs[word[0]]
    for label in word[1:]:
        U=set_product(table,len(blocks),U,fs[label])
    return U

def approx_word(table,blocks,word):
    h=abstract(table,blocks)
    possible=frozenset({word[0]})
    for label in word[1:]:
        possible=frozenset().union(*(h[p,label] for p in possible))
    return possible

class ExtendedCensus(unittest.TestCase):
    def test_all_labelled_four_state_semigroups_and_partitions(self):
        counts=Counter()
        by_classes=Counter()
        defects=Counter()
        semigroup_count=0
        for table in semigroups():
            semigroup_count+=1
            self.assertTrue(assoc(table,4))
            for blocks in partitions(4):
                d=congruent(table,blocks)
                fs=classes(blocks)
                a=not any(associativity_defects(abstract(table,blocks),len(fs)))
                counts[d,a]+=1
                by_classes[len(fs),d,a]+=1
                if not a:
                    ss=generated_exact_sets(table,blocks)
                    _,hist=stable_partition(table,ss,blocks)
                    defects[len(ss),len(set(hist[-1]))]+=1
        self.assertEqual(semigroup_count,3492)
        self.assertEqual(sum(counts.values()),52380)
        self.assertEqual(counts,Counter({
            (True,True):21766, (False,True):19814, (False,False):10800}))
        self.assertEqual(sum(defects.values()),10800)
        self.assertEqual(max(s for s,_ in defects),13)
        self.assertGreater(defects[13,13],0)
        self.assertEqual(by_classes[2,False,True],13934)

    def test_cyclic_four_requires_thirteen_states(self):
        table=cyclic(4)
        partition=(0,0,1,2)
        ss=generated_exact_sets(table,partition)
        _,hist=stable_partition(table,ss,partition)
        self.assertEqual((len(ss),len(set(hist[-1]))),(13,13))
        self.assertTrue(any(associativity_defects(abstract(table,partition),3)))

    def test_cyclic_five_requires_all_nonempty_subsets(self):
        n=5
        table=cyclic(n)
        partition=(0,0,1,2,1)
        ss=generated_exact_sets(table,partition)
        self.assertEqual(set(ss),{
            frozenset(x for x in range(n) if mask & (1<<x))
            for mask in range(1,1<<n)})
        _,hist=stable_partition(table,ss,partition)
        self.assertEqual(len(set(hist[-1])),31)
        self.assertFalse(any(associativity_defects(abstract(table,partition),3)))
        for U,V in product(ss,repeat=2):
            if U==V: continue
            x=next(iter(U.symmetric_difference(V)))
            g=(3-x)%5
            u_obs=observed_outputs(set_product(table,n,U,{g}),partition)
            v_obs=observed_outputs(set_product(table,n,V,{g}),partition)
            self.assertNotEqual(2 in u_obs,2 in v_obs)
        actual=observed_outputs(exact_word(table,partition,(1,1,2)),partition)
        approx=approx_word(table,partition,(1,1,2))
        self.assertEqual(actual,frozenset({0,1}))
        self.assertEqual(approx,frozenset({0,1,2}))

    def test_affine_three_compresses_seven_to_four(self):
        elements,table=affines(3)
        partition=tuple(b for a,b in elements)
        ss=generated_exact_sets(table,partition)
        _,hist=stable_partition(table,ss,partition)
        self.assertTrue(assoc(table,9))
        self.assertEqual((len(ss),len(set(hist[-1]))),(7,4))
        self.assertFalse(any(associativity_defects(abstract(table,partition),3)))

if __name__=='__main__':
    unittest.main()
