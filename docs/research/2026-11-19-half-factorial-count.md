# ⟨4, 6, 9⟩ の全既約分解の個数：⌊min(v₂, v₃)/2⌋ + 1

## 位置づけ

[半階乗モノイドの検証記録](../verification/2026-11-03-half-factorial-probe.md) の「数学的な全分解数（Lean未形式化）」は、乗法モノイド \(G=\langle4,6,9\rangle\subseteq\mathbb N\) の元 \(n\) について \(a=v_2(n)\)、\(b=v_3(n)\) とおくと全既約分解の個数が \(N(n)=\lfloor\min(a,b)/2\rfloor+1\) になると手計算で述べ、この閉形式を直接与える Lean 宣言はないとしていた。この追加でそれを証明する。

- Lean：[lean/Research/HalfFactorialCount.lean](../../lean/Research/HalfFactorialCount.lean)（名前空間 `HalfFactorialCount`、14定理・6定義）
- 独立検算：[tests/test_half_factorial_count.py](../../tests/test_half_factorial_count.py)
- 専用CI：[.github/workflows/half-factorial-count.yml](../../.github/workflows/half-factorial-count.yml)。統合検査 `tools/pr_integration.py` にも `--trust=0` 段として登録した。

## 結果

| 内容 | Lean 宣言 |
|---|---|
| \(2r+s=a,\ s+2t=b\) の自然数解の個数は、\(a\equiv b\pmod 2\) なら \(\lfloor\min(a,b)/2\rfloor+1\)、そうでなければ0 | `card_sol`（`solEquiv`） |
| \(4^r6^s9^t=4^{r'}6^{s'}9^{t'}\) ⇔ 2 と 3 の指数が等しい | `value_eq_iff`、`two_three_pow_inj` |
| **\(4^r6^s9^t=n\) となる \((r,s,t)\) の個数** \(=\lfloor\min(v_2n,v_3n)/2\rfloor+1\) | `card_counts_eq`、`card_counts_eq_factorization` |
| **4・6・9 の多重集合で積が \(n\) のものの個数** \(=\lfloor\min(v_2n,v_3n)/2\rfloor+1\) | `card_factorizations_eq`（`factorizationEquiv`） |
| 同じ積の分解は同じ長さ（半階乗性） | `length_eq` |
| 資料の例 36, 216, 1296, 46656 はそれぞれ 2, 2, 3, 4 通り | `example_counts` |

ここで \(n=4^{r_0}6^{s_0}9^{t_0}\in G\)。4・6・9 が \(G\) の既約元のすべてであることは joint 検査側の `AtomicGeneratorClassification.inc`（`atom_iff_three_generators`）にあり、このモジュールは「4・6・9 の多重集合」として数える。両者を一つの Lean 環境で合成した定理は含まない。

## 手書きの証明

\(4^r6^s9^t=2^{2r+s}3^{s+2t}\) なので、積が \(n\) に等しいことは \((2r+s,\ s+2t)=(a,b)\) と同値（素因数分解の一意性、Lean では `Nat.factorization`）。解は \(s\) で決まり、\(s\le\min(a,b)\)、\(s\equiv a\equiv b\pmod2\)。\(s=\min(a,b)-2k\)（\(0\le k\le\lfloor\min(a,b)/2\rfloor\)）と並べれば全単射になる。多重集合 \(w\) は 4・6・9 の出現回数で決まるので、多重集合の分解と \((r,s,t)\) は一対一に対応する。

## 実行された検証

2026-11-19、クラウドコンテナ上で実行した（Lean `v4.36.0-rc2`、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`）。

- `lake env lean --trust=0 Research/HalfFactorialCount.lean`：終了コード0、`error:`・`warning:`・`sorryAx` なし。全14定理の使用公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内。
- `python -B tests/test_half_factorial_count.py`：3テスト合格。\(r,s,t\le8\) の全ての \(n=4^r6^s9^t\)（重複を除く）で、原子の非増加列による別実装の再帰探索で数えた分解数が \(\lfloor\min(v_2,v_3)/2\rfloor+1\) に一致し、長さが一意であることを確認。

GitHub Actions の結果はこの記録の時点では未確認であり、専用CIの完了を別途確認する。

## 論理的境界

1. \(G\) の外の \(n\) では分解は存在しない（個数0）。主定理は \(n\in G\) の場合に述べている。
2. 分解を見つける計算費用・素因数分解の計算量は扱わない。
