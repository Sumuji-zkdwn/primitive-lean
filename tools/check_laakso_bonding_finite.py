#!/usr/bin/env python3
"""Exact finite audit, using the tagged sums/products of the pinned Lean definitions.

Geometry is represented only at vertices and the 1/3, 2/3 edge points hit by
bonding. Distinct labelled parallel edges remain distinct; no metric is used.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
import json
import argparse
from pathlib import Path

@dataclass(frozen=True)
class Graph:
    vertices: tuple
    edges: tuple
    source: dict
    target: dict

def old(v, b): return ('old', (v, b))
def new(e, k): return ('new', (e, k))

def refine(g):
    vertices = tuple(old(v, b) for v, b in product(g.vertices, (False, True)))
    vertices += tuple(new(e, k) for e, k in product(g.edges, (0, 1)))
    edges = tuple(product(g.edges, (False, True), range(3)))
    src, dst = {}, {}
    for e, b, k in edges:
        src[e, b, k] = old(g.source[e], b) if k == 0 else new(e, k - 1)
        dst[e, b, k] = new(e, k) if k != 2 else old(g.target[e], b)
    return Graph(vertices, edges, src, dst)

def raw_vertices(g):
    locations = [('old', v) for v in g.vertices]
    locations += [('new', (e, k)) for e, k in product(g.edges, (0, 1))]
    return tuple((tag, payload, b) for (tag, payload), b in product(locations, (False, True)))

def raw_projection(x):
    tag, payload, b = x
    return old(payload, b) if tag == 'old' else new(*payload)

def advance_right_general(g, x):
    tag, payload, b = x
    if tag == 'old': return x
    e, k = payload
    return ('new', (e, 1), b) if k == 0 else ('old', g.target[e], b)

def rel_step(g, q):
    return {raw_projection(advance_right_general(g, x))
            for x in raw_vertices(g) if raw_projection(x) == q}

def vertex_point(v): return ('vertex', v)

def bonding_on_vertex(g, q):
    tag, payload = q
    if tag == 'old': return vertex_point(payload[0])
    e, k = payload
    return ('interior', e, Fraction(k + 1, 3))

def encode_first(q):
    tag, payload = q
    if tag == 'old':
        v, b = payload
        return 2 * v + int(b)
    return 4 + payload[1]

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, help='Optional full JSON results file')
    args = parser.parse_args()
    g0 = Graph((0, 1), (0,), {0: 0}, {0: 1})
    g1, g2 = refine(g0), refine(refine(g0))
    assert (len(raw_vertices(g0)), len(g1.vertices), len(g1.edges)) == (8, 6, 6)
    assert (len(raw_vertices(g1)), len(g2.vertices), len(g2.edges)) == (36, 24, 36)
    for g in (g0, g1):
        assert {raw_projection(x) for x in raw_vertices(g)} == set(refine(g).vertices)
        for e, b in product(g.edges, (False, True)):
            for k in (0, 1):
                x = ('new', (e, k), b)
                assert raw_projection(x) == refine(g).source[e, b, k + 1]
                assert raw_projection(advance_right_general(g, x)) == refine(g).target[e, b, k + 1]

    w1, w2 = new(0, 0), new(0, 1)
    assert (encode_first(w1), encode_first(w2)) == (4, 5)
    assert rel_step(g0, w1) == {w2}
    assert {encode_first(v) for v in rel_step(g0, w2)} == {2, 3}
    raw_failures = []
    for x, c in product(raw_vertices(g0), (False, True)):
        lifted = ('old', raw_projection(x), c)
        fine_then_project = bonding_on_vertex(g1, raw_projection(advance_right_general(g1, lifted)))
        parent_update = vertex_point(raw_projection(advance_right_general(g0, x)))
        assert bonding_on_vertex(g1, raw_projection(lifted)) == vertex_point(raw_projection(x))
        if fine_then_project != parent_update:
            raw_failures.append([encode_first(raw_projection(x)), x[2], c])
    assert len(raw_failures) == 8

    rows = []
    for q, c in product(g1.vertices, (False, True)):
        child = old(q, c)
        projected = {bonding_on_vertex(g1, y) for y in rel_step(g1, child)}
        lower = {vertex_point(y) for y in rel_step(g0, q)}
        assert projected == {vertex_point(q)}
        rows.append({'parent_label': encode_first(q), 'new_sheet': c,
                     'fine_then_bonding': sorted(encode_first(y[1]) for y in projected),
                     'parent_relation': sorted(encode_first(y[1]) for y in lower),
                     'forward_sound': projected <= lower, 'equal': projected == lower})
    failures = [r for r in rows if not r['equal']]
    assert len(failures) == 4
    assert {r['parent_label'] for r in failures} == {4, 5}
    assert all(not r['forward_sound'] for r in failures)

    # Exhaust the finite replacement relation on the 12 inherited copies.
    inherited = tuple(product(g1.vertices, (False, True)))
    repair_edges = 0
    for x in inherited:
        targets = {y for y in inherited if y[0] in rel_step(g0, x[0])}
        assert {y[0] for y in targets} == rel_step(g0, x[0])
        repair_edges += len(targets)
        if x[0] in (w1, w2): assert x not in targets
    assert repair_edges == 28
    # Replacement W1 -> W2 steps are not single edges of the second graph.
    for c, d in product((False, True), repeat=2):
        assert not any(g2.source[e] == old(w1, c) and g2.target[e] == old(w2, d)
                       for e in g2.edges)
    # The finite set of actual geometric images: 6 vertices + 12 edge interiors.
    geometric_images = {bonding_on_vertex(g1, q) for q in g2.vertices}
    assert len(geometric_images) == 18

    result = {'source_commit': '983fa7cffe88463e63fdacdcff1d6f989118a76e',
              'level1': {'raw_vertices': 8, 'observed_vertices': 6, 'edges': 6},
              'level2': {'raw_vertices': 36, 'observed_vertices': 24, 'edges': 36},
              'bonding_images_of_level2_vertices': {'parent_vertices': 6, 'edge_interior_points': 12},
              'raw_parent_state_and_new_sheet_pairs': 16, 'noncommuting_raw_pairs': len(raw_failures),
              'inherited_observed_copies_checked': 12, 'noncommuting_observed_copies': len(failures),
              'rows': rows,
              'replacement_relation': {'states': 12, 'arrows': repair_edges, 'exact_inputs': 12,
                                       'keeps_original_w1_w2_self_loops': False,
                                       'w1_w2_steps_are_single_second_level_edges': False},
              'boundary': 'Finite vertices and exact rational bonding images only; no continuous or inverse-limit dynamics.'}
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'raw_pairs': 16, 'raw_failures': 8,
                      'inherited_observed_copies': 12, 'observed_failures': 4,
                      'w1_projected_successors': [4], 'w1_parent_successors': [5],
                      'repair_exact_inputs': 12, 'repair_arrows': 28}, indent=2))

if __name__ == '__main__': main()
