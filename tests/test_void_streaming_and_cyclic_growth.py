"""Associativity vs streaming exactness; exhaustive cyclic C3--C9 set closures."""
from collections import Counter,deque
from math import gcd
import unittest
from test_void_multivalued_completion import (
    partitions,classes,congruent,abstract,associativity_defects,
    generated_exact_sets,set_product,observed_outputs,
)
from test_void_semigroup_census_extended import semigroups,cyclic

def reachable_streaming_exact(table,partition):
    """Every left-folded nonempty fiber-word has exactly the predicted readouts."""
    n=len(partition)
    fibers=classes(partition)
    for U in generated_exact_sets(table,partition):
        labels=observed_outputs(U,partition)
        saturation=frozenset(x for x in range(n) if partition[x] in labels)
        for F in fibers:
            actual=observed_outputs(set_product(table,n,U,F),partition)
            predicted=observed_outputs(set_product(table,n,saturation,F),partition)
            if actual!=predicted: return False
    return True

def cyclic_sumset(a,b,n):
    mask=(1<<n)-1
    out=0
    while a:
        bit=a & -a
        k=bit.bit_length()-1
        out |= ((b<<k)|(b>>(n-k)))&mask
        a-=bit
    return out

def cyclic_exact_closure(partition):
    n=len(partition)
    fibers=tuple(sum(1<<i for i in range(n) if partition[i]==label)
        for label in range(max(partition)+1))
    seen=set(fibers)
    todo=deque(fibers)
    while todo:
        U=todo.popleft()
        for F in fibers:
            V=cyclic_sumset(U,F,n)
            if V not in seen:
                seen.add(V)
                todo.append(V)
    return seen,fibers

def has_unique_generator(fibers,n):
    return any(F.bit_count()==1 and gcd(F.bit_length()-1,n)==1 for F in fibers)

class StreamingAndCyclicGrowth(unittest.TestCase):
    def test_complete_four_state_streaming_census(self):
        counts=Counter()
        for table in semigroups(4):
            for partition in partitions(4):
                det=congruent(table,partition)
                hyper=not any(associativity_defects(
                    abstract(table,partition),len(classes(partition))))
                streaming=reachable_streaming_exact(table,partition)
                counts[det,hyper,streaming]+=1
                if det: self.assertTrue(streaming)
        self.assertEqual(counts,Counter({
            (True,True,True):21766,
            (False,True,True):16406,
            (False,True,False):3408,
            (False,False,True):2124,
            (False,False,False):8676,
        }))

    def test_all_partitions_of_cyclic_groups_three_to_nine(self):
        maxima={3:7,4:13,5:31,6:39,7:99,8:123,9:223}
        bell={3:5,4:15,5:52,6:203,7:877,8:4140,9:21147}
        witness={
            3:(0,0,1), 4:(0,0,1,2),
            5:(0,0,1,2,1), 6:(0,0,1,2,1,3),
            7:(0,0,1,2,1,3,2),
            8:(0,0,1,2,1,3,2,4),
            9:(0,0,1,2,3,1,3,2,4),
        }
        for n in range(3,10):
            best=0
            n_partitions=0
            for partition in partitions(n):
                n_partitions+=1
                sets,_=cyclic_exact_closure(partition)
                best=max(best,len(sets))
            self.assertEqual(n_partitions,bell[n])
            self.assertEqual(best,maxima[n])
            sets,fibers=cyclic_exact_closure(witness[n])
            self.assertEqual(len(sets),best)
            self.assertTrue(has_unique_generator(fibers,n))
            self.assertTrue(all((1<<x) in sets for x in range(n)))
            # Independent reference implementation via explicit Python frozensets.
            original=generated_exact_sets(cyclic(n),witness[n])
            self.assertEqual(sets,{sum(1<<x for x in U) for U in original})

if __name__=='__main__':
    unittest.main()
