"""Exact rational event-driven flight-and-impact audit for 1:2:1 balls.

The state holds free gaps between adjacent balls, not centre distances.
A gap of zero means contact. Mass and radii are fixed, no overlap or
compliance is modeled. On contact we apply the source's binary elastic maps.
"""
from fractions import Fraction as Q
from itertools import product
import json

V0 = (Q(1), Q(0), Q(-1))


def LM(v):
    l, m, r = v
    return ((-l + 4*m)/3, (2*l+m)/3, r)


def MR(v):
    l, m, r = v
    return (l, (m+2*r)/3, (4*m-r)/3)


def momentum(v):
    return v[0] + 2*v[1] + v[2]


def twice_energy(v):
    return v[0]**2 + 2*v[1]**2 + v[2]**2


def flight(g, v, dt):
    return (g[0] + (v[1]-v[0])*dt, g[1] + (v[2]-v[1])*dt)


def next_event(g, v):
    """Exact earliest future collision; a gap=0 separating pair is ignored."""
    arrivals = []
    for index, closing_rate in enumerate((v[0]-v[1], v[1]-v[2])):
        if closing_rate > 0:
            if g[index] == 0:
                raise AssertionError('unmodeled simultaneous/instantaneous contact')
            if g[index] > 0:
                arrivals.append((g[index]/closing_rate, index))
    if not arrivals:
        return None
    return min(arrivals)


def simulate(left_gap, right_gap):
    a, b = Q(left_gap), Q(right_gap)
    if a <= 0 or b <= 0 or a == b:
        raise ValueError('require positive unequal initial free gaps')
    t, g, v, events = Q(0), (a,b), V0, []
    for _ in range(8):
        event = next_event(g,v)
        if event is None:
            return {'initial_gaps': (a,b), 'events': events,
                    'final_time': t, 'final_gaps': g, 'final_velocity': v}
        dt, side = event
        assert dt > 0
        ng = flight(g,v,dt)
        assert ng[0] >= 0 and ng[1] >= 0 and ng[side] == 0
        assert ng[1-side] > 0  # exactly one pair collides
        # Each free gap is affine during flight; nonnegative endpoints
        # guarantee no overlap, and the noncontact gap stays positive.
        assert all(flight(g, v, dt*Q(k,16))[1-side] > 0 for k in range(1,17))
        nv = (LM if side == 0 else MR)(v)
        assert momentum(nv) == momentum(v) and twice_energy(nv) == twice_energy(v)
        t += dt
        events.append({'side': 'L' if side==0 else 'R', 'time': t,
                       'flight': dt, 'gaps': ng, 'before': v, 'after': nv})
        v, g = nv, ng
    raise AssertionError('too many contacts; possible loop')


def expected(a, b):
    d = abs(b-a)
    if a < b:
        return ('LRL',(a,a+3*d/5,a+6*d),
                (Q(-13,27), Q(-10,27), Q(11,9)),(Q(0),9*d))
    return ('RLR',(b,b+3*d/5,b+6*d),
            (Q(-11,9), Q(10,27), Q(13,27)),(9*d,Q(0)))


def check_pair(a, b):
    result=simulate(a,b)
    label, times, final, gaps=expected(Q(a),Q(b))
    assert len(result['events'])==3
    assert ''.join(e['side'] for e in result['events'])==label
    assert tuple(e['time'] for e in result['events'])==times
    assert result['final_velocity']==final
    assert result['final_gaps']==gaps
    assert next_event(result['final_gaps'], result['final_velocity']) is None
    assert all(result['events'][i]['time'] < result['events'][i+1]['time'] for i in range(2))
    return result


def symbolic_affine_certificate():
    """Exact polynomial-identity check in the two formal variables a and d.

    An affine pair (p,q) denotes p*a+q*d with a,d>0. This is not
    sampling a,d. Strict positivity of d and positive rational multipliers
    proves non-simultaneous contact and positive inter-contact flights.
    """
    a, d, zero = (Q(1),Q(0)), (Q(0),Q(1)), (Q(0),Q(0))

    def plus(x,y):
        return (x[0]+y[0],x[1]+y[1])

    def scaled(c,x):
        return (c*x[0],c*x[1])

    def step(g,v,dt):
        return (plus(g[0],scaled(v[1]-v[0],dt)),
                plus(g[1],scaled(v[2]-v[1],dt)))

    def certify(start, left_first):
        # No event-order assumption is hidden in the free-gap equations.
        # Each chosen contact is forced by the nonzero approach speed,
        # and the other pair has strictly positive gap at the contact.
        g1=step(start,V0,a)
        if left_first:
            assert g1 == (zero,d)
            v1=LM(V0)
            assert (v1[1]-v1[0],v1[1]-v1[2])==(Q(1),Q(5,3))
            g2=step(g1,v1,scaled(Q(3,5),d))
            assert g2==(scaled(Q(3,5),d),zero)
            v2=MR(v1)
            assert (v2[0]-v2[1],v2[2]-v2[1])==(Q(1,9),Q(5,3))
            g3=step(g2,v2,scaled(Q(27,5),d))
            assert g3==(zero,scaled(Q(9),d))
            final=LM(v2)
        else:
            assert g1 == (d,zero)
            v1=MR(V0)
            assert (v1[0]-v1[1],v1[2]-v1[1])==(Q(5,3),Q(1))
            g2=step(g1,v1,scaled(Q(3,5),d))
            assert g2==(zero,scaled(Q(3,5),d))
            v2=LM(v1)
            assert (v2[1]-v2[2],v2[1]-v2[0])==(Q(1,9),Q(5,3))
            g3=step(g2,v2,scaled(Q(27,5),d))
            assert g3==(scaled(Q(9),d),zero)
            final=MR(v2)
        assert final[0] < final[1] < final[2]
        assert (final[0]+2*final[1]+final[2],twice_energy(final)) == (Q(0),Q(2))

    certify((a,plus(a,d)), True)
    certify((plus(a,d),a), False)
    return True


def audit():
    values=tuple(sorted({Q(x,y) for x in range(1,9) for y in range(1,7)}))
    symbolic_affine_certificate()
    tested=0
    for a,b in product(values,repeat=2):
        if a==b: continue
        check_pair(a,b)
        tested+=1
    examples={}
    for a,b in ((Q(1),Q(1)+Q(1,1000)),(Q(1)+Q(1,1000),Q(1))):
        r=check_pair(a,b)
        examples[f'{a},{b}']={
          'sequence':''.join(e['side'] for e in r['events']),
          'contact_times':[str(e['time']) for e in r['events']],
          'final_velocity':[str(v) for v in r['final_velocity']],
          'final_gaps':[str(g) for g in r['final_gaps']]
        }
    return {'passed':True,'distinct_positive_gap_pairs_tested':tested,
            'symbolic_affine_certificate_passed': True,
            'examples':examples,
            'scope':'Exact event-driven rational point-contact kinematics and affine formal-variable identities; no Lean proof or compliant three-body simultaneity law.'}


if __name__=='__main__':
    print(json.dumps(audit(),indent=2,ensure_ascii=False))
