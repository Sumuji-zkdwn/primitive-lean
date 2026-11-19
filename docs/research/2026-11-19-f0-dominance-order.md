# F0：二塊移動の到達可能性 ⇔ 優越順序、Φ_d の優越順序に沿った厳密増加

## 位置づけ

[F0 偏在単調性](2026-11-19-f0-imbalance-monotonicity.md) は二塊移動 \((a,b)\mapsto(a+1,b-1)\)（\(a\ge b\ge2\)）で \(\Phi_d\) が厳密に増加することを示し、「優越（majorization）で比較できる型どうしなら \(\Phi_d\) の大小も決まる」ことは Muirhead の整数移動補題に頼る手書きの帰結として、Lean 未形式化のまま残していた。この追加はその補題を Lean で証明し、帰結を形式化する。

- Lean：[lean/Research/F0DominanceOrder.lean](../../lean/Research/F0DominanceOrder.lean)（名前空間 `F0DominanceOrder`、21定理・4定義）。`Research.F0ImbalanceMonotonicity` を import する。
- 独立検算：[tests/test_f0_dominance_order.py](../../tests/test_f0_dominance_order.py)
- 専用CI：[.github/workflows/f0-dominance-order.yml](../../.github/workflows/f0-dominance-order.yml)。統合検査 `tools/pr_integration.py` には、`Research` の出力ディレクトリ作成、`F0ImbalanceMonotonicity` の `.olean` 出力、このモジュールの `--trust=0` 検査を段として加えた。

Muirhead の補題自体は古典的であり、新定理は主張しない。

## 定義

正整数の多重集合 \(p\) と閾値 \(t\in\mathbb N\) について、超過量

\[
E_p(t)=\sum_{m\in p}(m-t)^+
\]

（`excess`、自然数の切り捨て減算）を使う。`Dominates x y` は「塊数と総和が等しく、\(x\) が正で、すべての \(t\) で \(E_y(t)\le E_x(t)\)」とする。総和の等しいベクトルについて、これは降順に並べた部分和による古典的な majorization と同値であることが知られている。ただしこの同値性は Lean では証明しておらず、独立検算で \(N\le12\) の全組について一致を確かめただけである。

## 結果

| 内容 | Lean 宣言 |
|---|---|
| 二塊移動で超過量は各閾値で減らず、ちょうど \([b,a]\) で1増える | `excess_transfer`、`excess_le_of_transfer` |
| 超過量は正整数の型を決める | `eq_of_excess_eq` |
| 到達可能 ⇒ 優越 | `dominates_of_reachable` |
| 優越していて異なれば、優越を保つ二塊移動が一回できる | `exists_transfer_toward` |
| **Muirhead の整数移動補題**：優越 ⇒ 到達可能 | `reachable_of_dominates` |
| **到達可能性の特徴づけ** | `reachable_iff_dominates` |
| **\(\Phi_d\) は優越順序で狭義単調**（\(d\ge1\)） | `phi_lt_of_dominates`、`phi_le_of_dominates` |
| 例：\((4,2,1)\) は \((3,3,1)\) に優越／\((5,2,2,1,1)\) と \((4,4,1,1,1)\) は比較不能 | `example_dominates`、`example_incomparable` |

## 手書きの証明（優越 ⇒ 到達可能）

\(D(t)=E_x(t)-E_y(t)\ge0\) とおく。総和が等しいので \(D(0)=0\)、塊数も等しく正なので \(E_p(1)=\sum p-|p|\) より \(D(1)=0\)。十分大きい \(t\) でも \(D(t)=0\)。\(x\ne y\) なら（超過量が型を決めるので）\(D(t_0)>0\) となる \(t_0\ge2\) がある。\(t_0\) の左の最後の零点を \(L\ge1\)、右の最初の零点を \(U\) とすると、\(D>0\) が \((L,U)\) 全体で成り立つ。

\(c_p(t)=\#\{m\in p: m>t\}\) とおくと \(E_p(t)-E_p(t+1)=c_p(t)\)。これと \(D(L)=D(U)=0\) から、区間 \((L,U)\) にある \(y\) の塊の個数は

\[
\#\{m\in y: L<m<U\}=\#\{m\in x: L<m<U\}+D(L+1)+D(U-1)\ \ge\ 2 .
\]

その二つを \(a\ge b\) とすれば \(b\ge L+1\ge2\) で、二塊移動は \(E_y\) を \([b,a]\subseteq(L,U)\) 上でだけ1増やすので、移動後も \(E\le E_x\) が保たれる。測度 \(\sum_{t\le N}D(t)\) は真に減るので、有限回で \(x\) に到達する。逆向き（到達可能 ⇒ 優越）は移動ごとに超過量が増えることから従う。

\(\Phi_d\) の狭義単調性は、\(x\ne y\) なら到達に1回以上の移動が必要なことと、`phi_lt_of_transGen` から従う。

## 実行された検証

2026-11-19、クラウドコンテナ上で実行した（Lean `v4.36.0-rc2`、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`）。

- `F0ImbalanceMonotonicity.lean` を `-o` で `.olean` に出力した後、`lake env lean --trust=0 Research/F0DominanceOrder.lean`：終了コード0、`error:`・`warning:`・`sorryAx` なし。出力ディレクトリを消した状態から統合検査と同じ順序で再現した。
- 全21定理の `#print axioms`：11定理が `propext`・`Classical.choice`・`Quot.sound`、10定理が `propext`・`Quot.sound`。
- `python -B tests/test_f0_dominance_order.py`：3テスト合格。\(N\le12\) の同じ塊数の全組で、幅優先探索による到達可能性 ⇔ 超過量の優越 ⇔ 部分和による majorization を確認。真に優越する 732 組すべてで \(\Phi_1\) が真に大きい。

GitHub Actions の結果はこの記録の時点では未確認であり、専用CIの完了を別途確認する。

## 論理的境界

1. 優越順序は全順序ではない。比較できない型どうしの \(\Phi_d\) の大小は主張しない。
2. 部分和による古典的定義と `excess` による定義の同値性は Lean 未形式化（数値確認のみ）。
3. 塊数が異なる型（合流で移る型）は比較の対象外で、そこでは \(\Phi_d\) は単調でない（`merge_can_increase`）。
