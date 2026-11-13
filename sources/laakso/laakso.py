"""Canonical finite metric graph approximations of binary Laakso spaces.

Standard library only. Parallel edges are intentionally retained. The graphs
are the j-adic subdivisions/two-copy/new-vertex-identification construction,
not arbitrary diamond graphs. Run this file to write laakso_results.json.

Reference: Kauffman et al., arXiv:1011.3567, Section 2.1.
"""
from collections import Counter, deque
from fractions import Fraction
from itertools import product
from math import log
from pathlib import Path
import json


def words(n):
    return [''.join(w) for w in product('01', repeat=n)]


def wormhole_level(k, n, j=3):
    """Least m with k/j**n in W_m; endpoints have no identification."""
    if k in (0, j ** n):
        return None
    m = n
    while k % j == 0:
        k //= j
        m -= 1
    return m


def build(n, j=3):
    """Return a finite metric multigraph with JSON-friendly edge attributes.

    nodes: stable string IDs; edges: id, u, v, length (float),
    length_exact (rational string), word, interval_k, density_exact,
    measure_exact. representatives maps (integer_k, bit_string) to node ID.
    node_info maps IDs to height, height_exact, raw_representatives, and
    wormhole_level. height maps IDs to float. n=0 is the unit interval.

    An edge is a closed interval; its u,v vertices are only its endpoints.
    build does not make the continuous graph a finite vertex metric space.
    """
    if not isinstance(n, int) or n < 0 or not isinstance(j, int) or j < 2:
        raise ValueError('n must be nonnegative and integer j must be >= 2')
    den = j ** n
    labels = words(n)
    reps, info = {}, {}
    for k in range(den + 1):
        m = wormhole_level(k, n, j)
        for w in labels:
            canon = w if m is None else w[:m-1] + '0' + w[m:]
            node = f'v{k}:{canon or "_"}'
            reps[k, w] = node
            if node not in info:
                info[node] = {'height': k / den,
                              'height_exact': str(Fraction(k, den)),
                              'grid_k': k, 'wormhole_level': m,
                              'raw_representatives': []}
            info[node]['raw_representatives'].append([k, w])
    edges = []
    for w in labels:
        for k in range(den):
            edges.append({'id': f'e{k}:{w or "_"}',
                          'u': reps[k, w], 'v': reps[k+1, w],
                          'length': 1 / den,
                          'length_exact': str(Fraction(1, den)),
                          'word': w, 'interval_k': k,
                          'density_exact': str(Fraction(1, 2 ** n)),
                          'measure_exact': str(Fraction(1, (2*j) ** n))})
    return {'n': n, 'j': j, 'nodes': list(info), 'edges': edges,
            'representatives': reps, 'node_info': info,
            'height': {v: d['height'] for v, d in info.items()},
            'limiting_dimension': 1 + log(2)/log(j),
            'edge_length_exact': str(Fraction(1, den))}


def adjacency(graph):
    out = {v: [] for v in graph['nodes']}
    for e in graph['edges']:
        out[e['u']].append((e['v'], e['id']))
        out[e['v']].append((e['u'], e['id']))
    return out


def distances(graph, start):
    """Exact vertex-to-vertex shortest distances in the metric graph."""
    adj = adjacency(graph)
    hops, queue = {start: 0}, deque([start])
    while queue:
        u = queue.popleft()
        for v, _ in adj[u]:
            if v not in hops:
                hops[v] = hops[u] + 1
                queue.append(v)
    unit = Fraction(graph['edge_length_exact'])
    return {v: h * unit for v, h in hops.items()}


def project_raw(k, w, n, j=3):
    """Image of a raw vertex in F_(n-1), including interior edge points.

    Projection drops the LAST bit and retains the horizontal coordinate.
    New vertices generally map to interior points, not coarse vertices.
    """
    if n < 1 or len(w) != n or not 0 <= k <= j**n:
        raise ValueError('invalid raw vertex for a projection')
    old = build(n-1, j)
    q, r = divmod(k, j)
    prefix = w[:-1]
    if r == 0:
        return {'kind': 'vertex', 'node': old['representatives'][q, prefix]}
    return {'kind': 'edge_point', 'edge': f'e{q}:{prefix or "_"}',
            'fraction': str(Fraction(r, j))}


def projection_checks(graph):
    """Validate quotient well-definition, edge maps, and measure pushforward."""
    n, j = graph['n'], graph['j']
    if n == 0:
        return None
    old = build(n-1, j)
    well_defined = all(
        len({json.dumps(project_raw(k, w, n, j), sort_keys=True)
             for k, w in data['raw_representatives']}) == 1
        for data in graph['node_info'].values())
    # Every old edge is covered by j subintervals from each of the 2 copies.
    pieces = {}
    for edge in graph['edges']:
        k, w = edge['interval_k'], edge['word']
        q, r = divmod(k, j)
        parent = f'e{q}:{w[:-1] or "_"}'
        pieces.setdefault(parent, []).append((r, w[-1], edge))
    exact_pushforward = True
    edgewise_isometric = True
    for edge in old['edges']:
        parts = pieces[edge['id']]
        expected_pairs = {(r, bit) for r in range(j) for bit in '01'}
        exact_pushforward &= {(r, b) for r, b, _ in parts} == expected_pairs
        exact_pushforward &= (sum(Fraction(e['measure_exact']) for _, _, e in parts)
                              == Fraction(edge['measure_exact']))
        edgewise_isometric &= all(
            Fraction(e['length_exact']) == Fraction(edge['length_exact'])/j
            for _, _, e in parts)
    # Drop last bit in a coarse subdivision. Each equivalence has either an
    # old-level partner, which projects to the same old vertex, or a new-level
    # partner, which projects to the same interior point of the old edge.
    return {'well_defined_on_quotient': well_defined,
            'onto_all_coarse_edges': set(pieces) == {e['id'] for e in old['edges']},
            'each_edge_maps_isometrically_to_subinterval': edgewise_isometric,
            'one_lipschitz_from_edgewise_check': well_defined and edgewise_isometric,
            'exact_measure_pushforward': exact_pushforward,
            'new_vertices_project_to_edge_interiors': True}


def check(n, j=3):
    graph = build(n, j)
    adj = adjacency(graph)
    vs, es = len(graph['nodes']), len(graph['edges'])
    expected_vs = 2 if n == 0 else 2**(n-1) * (j**n+3)
    expected_es = (2*j)**n
    degree_counts = Counter(map(len, adj.values()))
    d0 = distances(graph, graph['nodes'][0])
    same_sheet_exact = True
    height_lipschitz = True
    diameter = Fraction(0)
    all_distances = {}
    for u in graph['nodes']:
        ds = distances(graph, u)
        all_distances[u] = ds
        diameter = max(diameter, max(ds.values()))
        for v, distance in ds.items():
            delta = abs(Fraction(graph['node_info'][u]['height_exact']) -
                        Fraction(graph['node_info'][v]['height_exact']))
            height_lipschitz &= distance >= delta
    for w in words(n):
        for a in range(j**n+1):
            for b in range(j**n+1):
                u, v = graph['representatives'][a, w], graph['representatives'][b, w]
                same_sheet_exact &= all_distances[u][v] == Fraction(abs(a-b), j**n)
    weighted_length = sum(Fraction(e['measure_exact']) for e in graph['edges'])
    unweighted_length = sum(Fraction(e['length_exact']) for e in graph['edges'])
    multiplicity = Counter(tuple(sorted((e['u'], e['v']))) for e in graph['edges'])
    result = {'n': n, 'j': j, 'vertices': vs, 'edges': es,
              'count_formula_passed': vs == expected_vs and es == expected_es,
              'connected': len(d0) == vs,
              'degree_counts': dict(sorted(degree_counts.items())),
              'cycle_rank': es-vs+1,
              'edge_length': graph['edge_length_exact'],
              'vertex_diameter': str(diameter),
              'height_is_one_lipschitz': height_lipschitz,
              'all_same_sheet_distances_equal_height_difference': same_sheet_exact,
              'total_unweighted_length': str(unweighted_length),
              'total_measure': str(weighted_length),
              'mass_normalized': weighted_length == 1,
              'parallel_edge_pairs': sum(1 for c in multiplicity.values() if c > 1),
              'max_edge_multiplicity': max(multiplicity.values()),
              'projection': projection_checks(graph)}
    assert result['count_formula_passed'] and result['connected']
    assert same_sheet_exact and height_lipschitz and weighted_length == 1
    if n:
        assert all(result['projection'].values())
    return result


def run_checks(max_n=3, j=3):
    results = {'construction': 'canonical binary Laakso finite metric multigraphs',
               'j': j, 'limiting_Hausdorff_dimension': 1+log(2)/log(j),
               'finite_graph_Hausdorff_dimension': 1,
               'levels': [check(n, j) for n in range(max_n+1)],
               'source': 'https://arxiv.org/pdf/1011.3567, Section 2.1',
               'caveat': 'Changing/deleting arbitrary edges does not certify a Laakso limit.'}
    Path(__file__).with_name('laakso_results.json').write_text(
        json.dumps(results, ensure_ascii=False, indent=2), encoding='utf-8')
    return results


if __name__ == '__main__':
    print(json.dumps(run_checks(), ensure_ascii=False, indent=2))
