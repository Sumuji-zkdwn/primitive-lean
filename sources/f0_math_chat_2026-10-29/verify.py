#!/usr/bin/env python3
"""Reproduce the finite mathematical calculations in this archive. No dependencies."""
from collections import Counter
from itertools import combinations, product
from math import comb, factorial, prod
from pathlib import Path
import csv
import hashlib
import json

ROOT = Path(__file__).resolve().parent
MAX_N = 12


def partitions(n, minimum=1):
    """Positive integer partitions, in ascending order within each tuple."""
    if n == 0:
        yield ()
    for a in range(minimum, n + 1):
        for rest in partitions(n - a, a):
            yield (a,) + rest


def b_count(p, d=1):
    return prod(sum(b ** (a - 1) for b in p) for a in p) ** d


def k_type_count(p):
    denominator = prod(factorial(a - 1) for a in p)
    denominator *= prod(factorial(c) for c in Counter(p).values())
    numerator = factorial(sum(p))
    assert numerator % denominator == 0
    return numerator // denominator


def merges(p):
    return sorted({
        tuple(sorted([a for k, a in enumerate(p) if k not in (i, j)]
                     + [p[i] + p[j]]))
        for i, j in combinations(range(len(p)), 2)
    })


def fmt(p):
    return '(' + ','.join(map(str, reversed(p))) + ')'


def factors(n):
    ans = []
    p = 2
    while p * p <= n:
        while n % p == 0:
            ans.append(p)
            n //= p
        p += 1
    if n > 1:
        ans.append(n)
    return ans


def csv_write(path, fields, rows):
    with path.open('w', encoding='utf-8', newline='') as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)


def direct_commuting_check():
    """Compare the closed formula against actual maps, N=1..4, d=1."""
    results = []
    for n in range(1, 5):
        maps = list(product(range(n), repeat=n))
        ks = [k for k in maps if all(k[k[x]] == k[x] for x in range(n))]
        for k in ks:
            p = tuple(sorted(Counter(k).values()))
            actual = sum(all(s[k[x]] == k[s[x]] for x in range(n)) for s in maps)
            assert actual == b_count(p), (n, k, actual, b_count(p))
        results.append({'N': n, 'idempotents_checked': len(ks),
                        'candidate_maps_per_K': len(maps), 'passed': True})
    return results


def oeis_a322725(degree=9):
    """Formal power-series iteration of A=sum x^k (2+x*A^k)^k."""
    def mul(a, b):
        out = [0] * (degree + 1)
        for i, ai in enumerate(a):
            for j, bj in enumerate(b[:degree + 1 - i]):
                out[i + j] += ai * bj
        return out

    def power(a, n):
        out = [1] + [0] * degree
        for _ in range(n):
            out = mul(out, a)
        return out

    a = [1] + [0] * degree
    for _ in range(degree + 2):
        new = [0] * (degree + 1)
        for k in range(degree + 1):
            ak = power(a, k)
            inner = [2] + ak[:degree]
            term = power(inner, k)
            for j in range(degree + 1 - k):
                new[k + j] += term[j]
        a = new
    return a


def main():
    data = ROOT / 'data'
    data.mkdir(exist_ok=True)
    rows, rank_rows, totals, graph_stats = [], [], [], []
    transfer_checks, violations = 0, []
    for n in range(1, MAX_N + 1):
        ps = list(partitions(n))
        for p in ps:
            value = b_count(p)
            rows.append({'N': n, 'r': len(p), 'partition': fmt(p),
                         'K_type': k_type_count(p), 'S_B_d1': value,
                         'S_B_d2': value * value})
            for i, j in combinations(range(len(p)), 2):
                lo, hi = sorted((p[i], p[j]))
                if lo <= 1:
                    continue
                q = list(p)
                if p[i] >= p[j]:
                    q[i] += 1
                    q[j] -= 1
                else:
                    q[j] += 1
                    q[i] -= 1
                q = tuple(sorted(q))
                transfer_checks += 1
                if b_count(q) <= value:
                    violations.append({'N': n, 'source': p, 'target': q})
        total = 0
        for r in range(1, n + 1):
            count = comb(n, r) * r ** (n - r)
            from_types = sum(k_type_count(p) for p in ps if len(p) == r)
            assert count == from_types
            rank_rows.append({'N': n, 'r': r, 'K_count': count})
            total += count
        totals.append({'N': n, 'partition_types': len(ps), 'K_total': total})
        if n in (7, 8):
            edges = [{'source': fmt(p), 'target': fmt(q)} for p in ps for q in merges(p)]
            csv_write(data / f'merge_edges_N{n:02}.csv', ['source', 'target'], edges)
            graph_stats.append({'N': n, 'vertices': len(ps), 'distinct_edges': len(edges)})
    assert not violations
    assert [t['K_total'] for t in totals[:8]] == [1, 3, 10, 41, 196, 1057, 6322, 41393]
    assert graph_stats == [
        {'N': 7, 'vertices': 15, 'distinct_edges': 28},
        {'N': 8, 'vertices': 22, 'distinct_edges': 47}]
    csv_write(data / 'partition_counts_N01_to_N12.csv',
              ['N', 'r', 'partition', 'K_type', 'S_B_d1', 'S_B_d2'], rows)
    csv_write(data / 'idempotents_by_rank.csv', ['N', 'r', 'K_count'], rank_rows)

    searches = {}
    for target in (34634, 34643):
        hits, near = [], []
        for row in rows:
            for kind in ('K_type', 'S_B_d1', 'S_B_d2'):
                item = {'N': row['N'], 'partition': row['partition'],
                        'quantity': kind, 'value': row[kind]}
                if row[kind] == target:
                    hits.append(item)
                near.append(dict(item, distance=abs(row[kind] - target)))
        searches[str(target)] = {
            'factorization': factors(target), 'exact_type_hits': hits,
            'exact_total_K_hits': [t for t in totals if t['K_total'] == target],
            'nearest': sorted(near, key=lambda x: (x['distance'], x['N'], x['partition'], x['quantity']))[:6]
        }
        assert not hits and not searches[str(target)]['exact_total_K_hits']

    coefficients = oeis_a322725()
    assert coefficients == [1, 2, 5, 14, 50, 220, 1107, 6030, 34643, 207704]
    report = {
        'scope': {'N_min': 1, 'N_max': MAX_N, 'partition_rows': len(rows),
                  'S_output_arities': [1, 2]},
        'idempotents': totals, 'graphs': graph_stats,
        'direct_B_formula_checks': direct_commuting_check(),
        'imbalance_conjecture': {
            'index_pair_checks': transfer_checks,
            'note': 'Checks include separate index pairs that induce the same type transition.',
            'violations': violations, 'general_proof_included': False},
        'integer_search': searches,
        'A322725_coefficients_0_to_9': coefficients,
        'lean_verification_performed': False,
    }
    (data / 'verification.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

    lines = [
        '# 塊サイズ型と合流チェイン', '',
        '## 1. 型と総量', '',
        'λ=(m₁,…,mᵣ)を塊サイズ型とする。各成分は正整数、総和はN。'
        '塊と代表点のラベルを忘れた情報であり、整数分割として扱う。', '',
        '同じNでもrだけでは型は定まらない。例えば(4,1)と(3,2)はともにN=5,r=2。', '',
        '## 2. 一点に見えることと、一点集合であること', '',
        '型(5)は5点の基礎集合を一つのファイバーにしたもの。'
        '型(1)は基礎集合自体が一点であり、Nが違う。代表点の数はどちらも1だが、同じF0の全構造ではない。', '',
        '固定したNのもとでは、例えば', '',
        '$$ (1,1,1,1,1)\to(2,1,1,1)\to(3,1,1)\to(4,1)\to(5) $$', '',
        'と総量5を保つ合流チェインを書ける。型だけでは、どのラベル付き点を合流したかは失われる。', '',
        '## 3. 二塊合流グラフ', '',
        '二つの成分a,bを選びa+bに置き換え、並べ直す。'
        '同じ始点・終点になる辺は一つにまとめる。この規約では7点が15頂点28辺、8点が22頂点47辺。', '',
        '各辺で塊数rが1減るため有向閉路はない。任意の型から(N)へ到達できる。'
        '(1,…,1)から(N)への全経路はN−1辺。逆辺は型の細分化を表すが、元のSによる実現は別の問題。', '',
        '例：(3,2,1,1)の異なる合流先は(5,1,1),(4,2,1),(3,3,1),(3,2,2)。', '',
        '例：(3,2,2,1)の異なる合流先は(5,2,1),(4,2,2),(4,3,1),(3,3,2)。', '',
        '以下のK数はラベル付き集合上の型別個数、S数はその型の固定したK一つに対する個数。', '',
    ]
    for n in (7, 8):
        lines += [f'## {n}点世界の全表', '',
                  '| r | 型λ | Kの個数 | B適合S（d=1） | B適合S（d=2） |',
                  '| --- | --- | ---: | ---: | ---: |']
        selected = sorted((r for r in rows if r['N'] == n), key=lambda r: (r['r'], r['S_B_d1']))
        for row in selected:
            lines.append(f"| {row['r']} | {row['partition']} | {row['K_type']:,} | {row['S_B_d1']:,} | {row['S_B_d2']:,} |")
        lines += ['', f"冪等K総数：{sum(r['K_type'] for r in selected):,}。", '',
                  '| r | 冪等Kの個数 |', '| --- | ---: |']
        for row in rank_rows:
            if row['N'] == n:
                lines.append(f"| {row['r']} | {row['K_count']:,} |")
        lines += ['']
    lines += [
        '## 4. 固定した塊数での偏在比較', '',
        'N=8,r=2,d=2では、(4,4),(5,3),(6,2),(7,1)に対し、'
        '268,435,456 < 576,192,016 < 3,901,751,296 < 55,366,090,000。', '',
        'N=8,r=3では、(3,3,2),(4,2,2),(4,3,1),(5,2,1),(6,1,1)の順に'
        '14,992,384 < 26,214,400 < 51,494,976 < 237,406,464 < 4,900,280,004。', '',
        'N=8,r=4では、(2,2,2,2),(3,2,2,1),(3,3,1,1),(4,2,1,1),(5,1,1,1)の順に'
        '16,777,216 < 21,233,664 < 40,960,000 < 89,718,784 < 1,615,396,864。', '',
        'これらの有限の大小関係は再計算で一致する。一般のN,rでの予想は別文書に分ける。', '',
    ]
    (ROOT / '02_partitions_and_chains.md').write_text('\n'.join(lines), encoding='utf-8')

    hashes = []
    for path in sorted(ROOT.rglob('*')):
        if path.is_file() and path.name != 'SHA256SUMS.txt' and '__pycache__' not in path.parts:
            hashes.append(hashlib.sha256(path.read_bytes()).hexdigest() + '  ' + path.relative_to(ROOT).as_posix())
    (ROOT / 'SHA256SUMS.txt').write_text('\n'.join(hashes) + '\n', encoding='utf-8')
    print(json.dumps({'partition_rows': len(rows), 'graphs': graph_stats,
                      'imbalance_index_pair_checks': transfer_checks,
                      'direct_formula_check': 'passed for every K and every s, N=1..4',
                      'A322725_x8': coefficients[8], 'all_assertions_passed': True},
                     ensure_ascii=False))


if __name__ == '__main__':
    main()
