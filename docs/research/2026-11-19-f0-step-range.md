# F0：更新 T = K∘C∘K^(d)∘S が取りうる写像と、その個数

## 位置づけ

F0 の会話資料 [03_conjecture_and_cautions.md](../../sources/f0_math_chat_2026-10-29/03_conjecture_and_cautions.md) 第4節は「S の個数が多い」ことを異なる T の個数・表現能力と同一視しないよう注意し、第7節で「\((K,S,C)\) の同値類、異なる T の個数、型間経路数の定義と計数」を今後の課題に挙げていた。この追加は、冪等な \(K\) を固定したとき、更新 \(T=K\circ C\circ K^{(d)}\circ S\) が取りうる写像の集合を三つの条件設定で完全に決定し、個数を与える。

- Lean：[lean/Research/F0StepRange.lean](../../lean/Research/F0StepRange.lean)（名前空間 `F0StepRange`、9定理）
- 独立検算：[tests/test_f0_step_range.py](../../tests/test_f0_step_range.py)
- 専用CI：[.github/workflows/f0-step-range.yml](../../.github/workflows/f0-step-range.yml)。統合検査 `tools/pr_integration.py` にも `--trust=0` 段として登録した。

定義 `liftK`・`Compatible`（条件 B）・`Reconstructs`（条件 A）・`step` は [F0Retractions.inc](../../linear_input/lean_check/F0Retractions.inc) と同じ本文で写して持つ（joint 検査の宣言との同一視は Lean では行わない）。出力成分の添字型 \(I\) は空でない（\(d\ge1\)）とする。

## 結果

\(F=\mathrm{Fix}\,K\)、\(r=\lvert F\rvert\)、\(N=\lvert\mathcal B\rvert\) とする。

| 条件 | 取りうる \(T\) の集合 | 個数（有限の場合） | Lean 宣言 |
|---|---|---|---|
| なし | 値が \(F\) に入る写像すべて | \(r^N\) | `range_free`、`card_free` |
| B | 値が \(F\) に入り \(T\circ K=T\) となる写像すべて（\(F\to F\) の写像と一対一） | \(r^r\) | `range_compatible`、`card_compatible`（`compatibleEquiv`） |
| A と B | \(\{K\}\) | 1 | `range_reconstructs_compatible`、`card_reconstructs_compatible` |

例：7点で型 \((4,3)\)、\(d=2\) のとき、B 適合な \(S\) は 5,175,625 個あるが、B のもとで異なる \(T\) は \(2^2=4\) 個、条件なしでも \(2^7=128\) 個（`example_seven_points`）。B 適合な \(S\) の個数と異なる \(T\) の個数がまったく違う量であることを、具体的に示す。

## 手書きの証明

**条件なし。** \(T\) の値は外側の \(K\) により \(F\) に入る。逆に値が \(F\) に入る \(T\) は、\(S(x)=(T x,\dots,T x)\)、\(C\) を第 \(i_0\) 成分への射影とすれば \(K(C(K^{(d)}S x))=K(Tx)=Tx\)。

**条件 B。** B より \(K^{(d)}S(Kx)=K^{(d)}K^{(d)}S(x)=K^{(d)}S(x)\) なので \(T(Kx)=Tx\)。逆に \(T\circ K=T\) で値が \(F\) に入る \(T\) は、対角写像 \(S(x)=(Kx,\dots,Kx)\)（B を満たす）と \(C(v)=T(v_{i_0})\) で実現される。このような \(T\) は \(F\) への制限で決まり、任意の \(F\to F\) が現れる。

**条件 A と B。** B より \(K^{(d)}S(x)=S(Kx)\)、A より \(C(S(Kx))=Kx\) なので \(T=K\)。対角写像 \(S(x)=(x,\dots,x)\) と射影 \(C\) は A・B を同時に満たすので、この集合は空でない。

## 実行された検証

2026-11-19、クラウドコンテナ上で実行した（Lean `v4.36.0-rc2`、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`）。

- `lake env lean --trust=0 Research/F0StepRange.lean`：終了コード0、`error:`・`warning:`・`sorryAx` なし。全9定理の使用公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内。
- `python -B tests/test_f0_step_range.py`：3テスト合格。1〜3点（一成分）と1〜2点（二成分）の全ての冪等 \(K\) について、全ての \(S,C\) を列挙して \(T\) の集合を直接計算し、上の特徴づけと個数 \(r^N\)、\(r^r\)、\(\{K\}\) を確認。

GitHub Actions の結果はこの記録の時点では未確認であり、専用CIの完了を別途確認する。

## 論理的境界

1. 条件 A だけの場合の \(T\) の集合は扱わない。
2. \((K,S,C)\) の同値類（同じ \(T\) を与える組の分類）や、型間経路数は扱わない。ここでは各条件のもとで \(T\) の像集合を決めただけである。
3. 異なる \(T\) の個数を表現能力・計算効率・学習性能と同一視しない（元資料の注意を維持）。
