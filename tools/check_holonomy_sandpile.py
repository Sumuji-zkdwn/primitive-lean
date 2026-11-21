"""Holonomy detected by observer-invariant dissipative sandpile response.

Finite graph 3 base vertices x 6 fibre states (18 sites). Each vertex has
four internal neighbours and one sink edge. Compares two connections with
identical base graph but different triangle holonomy. Standard Python only.
"""
from itertools import product
from check_nonabelian_geometry import (
    E, PERMS, s, t, mul, gauge, edges_from_triplet, lifted_neighbours, relabel
)

NODES = tuple((i, g) for i in E for g in PERMS)
INDEX = {node: i for i,node in enumerate(NODES)}
FLAT = edges_from_triplet((E, E, E))
TWISTED = edges_from_triplet((s, t, E))

def stabilize(U, chips, reverse=False):
    c=list(chips)
    loss=0
    while True:
        eligible=(k for k in (range(17,-1,-1) if reverse else range(18))
                  if c[k] >= 5)
        p=next(eligible,None)
        if p is None: return tuple(c),loss
        c[p]-=5
        outgoing=tuple(lifted_neighbours(U,NODES[p]))
        assert len(outgoing)==4 and len(set(outgoing))==4
        for target in outgoing:
            c[INDEX[target]]+=1
        loss+=1
        assert sum(c)+loss==sum(chips), 'one chip dissipates each firing'
        assert loss<=sum(chips)

def visible(c):
    return tuple(sum(chips for chips,(j,_) in zip(c,NODES) if j==i) for i in E)

def reframe_chips(c,h):
    out=[0]*18
    for k,node in enumerate(NODES):
        out[INDEX[relabel(node,h)]]=c[k]
    return tuple(out)

def source(n):
    c=[0]*18
    c[INDEX[0,E]]=n
    return tuple(c)

def run():
    # Minimal chip count for this *specified* one-site injection experiment.
    for n in range(41):
        chips=source(n)
        a,la=stabilize(FLAT,chips)
        b,lb=stabilize(TWISTED,chips)
        assert visible(a)==visible(b),(n,visible(a),visible(b))
    chips=source(41)
    a,la=stabilize(FLAT,chips)
    b,lb=stabilize(TWISTED,chips)
    assert visible(a)==(12,7,7)
    assert visible(b)==(10,9,9)
    assert (la,lb)==(15,13)
    for U in (FLAT,TWISTED):
        for n in range(65):
            s0=source(n)
            assert stabilize(U,s0,False)==stabilize(U,s0,True)
        stable,loss=stabilize(U,chips)
        for h in product(PERMS,repeat=3):
            G=gauge(U,h)
            inp=reframe_chips(chips,h)
            fin,loss2=stabilize(G,inp)
            assert fin==reframe_chips(stable,h)
            assert loss2==loss
            assert visible(fin)==visible(stable)
    print('PASS: smallest distinguishing load for specified single-vertex protocol = 41')
    print('flat visible final:',visible(a),'sink loss:',la)
    print('twisted visible final:',visible(b),'sink loss:',lb)
    print('PASS: 2 sectors x 216 local gauges, and 130 toppling-order checks')

if __name__=='__main__':
    run()
