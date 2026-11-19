# 非負重みの隣接行列：冪零 ⇔ 有向閉路なし

## 位置づけ

[Square-zero network](2026-11-17-square-zero-network.md) の論理的境界1と「次の継ぎ目」で、「DAG iff \(A^n=0\) は単位・非負辺重みの有向グラフについての関係で、Lean での普遍命題（任意の有限 \(n\)・グラフ）は未形式化」とされていた命題を証明した。

- Lean：[lean/Research/AcyclicNilpotent.lean](../../lean/Research/AcyclicNilpotent.lean)（名前空間 `AcyclicNilpotent`、18定理・3定義）
- 独立検算：[tests/test_acyclic_nilpotent.py](../../tests/test_acyclic_nilpotent.py)
- 専用CI：[.github/workflows/acyclic-nilpotent.yml](../../.github/workflows/acyclic-nilpotent.yml)。統合検査 `tools/pr_integration.py` にも `--trust=0` 段として登録した。

隣接行列の冪零性と有向非巡回性の同値はグラフ理論でよく知られた事実であり、新定理は主張しない。ここでの寄与は、係数の条件を明示した一般形の Lean 証明と、既存の square-zero 模型への接続である。

## 定義と仮定

有限の頂点型 \(n\)、係数 \(R\)、行列 \(A\in R^{n\times n}\) について、辺 \(i\to j\) を \(A_{ij}\ne0\)（`Edge`）、長さ \(k\) の有向歩道を `Walk A k i j`、有向閉路の存在を「ある \(i\) から \(i\) への長さ1以上の歩道」（`HasCycle`、`Relation.TransGen` で定義）とする。

係数 \(R\) には、半環であること、加法が標準順序（`CanonicallyOrderedAdd`：和が零なら各項が零）、零因子がないこと、\(0\ne1\) を課す。\(\mathbb N\) と \(\mathbb R_{\ge0}\) はこれを満たす（\(\mathbb R_{\ge0}\) への適用はコンテナ上で型検査した）。整数・実数は満たさない。

## 結果

| 内容 | Lean 宣言 |
|---|---|
| \((A^k)_{ij}\ne0\) ⇔ 長さ \(k\) の歩道 \(i\to j\) がある | `pow_apply_ne_zero_iff` |
| 推移閉包 ⇔ 長さ1以上の歩道 | `transGen_iff_walk` |
| 頂点数以上の長さの歩道は閉路を含む（鳩の巣原理） | `hasCycle_of_walk` |
| 閉路があればどの冪も零でない | `pow_ne_zero_of_hasCycle`、`pow_diag_ne_zero_of_cycle` |
| **\(A^{\lvert n\rvert}=0\) ⇔ 閉路なし** | `pow_card_eq_zero_iff_acyclic` |
| **冪零 ⇔ 閉路なし** | `isNilpotent_iff_acyclic` |
| 冪零なら頂点数の冪で零 | `isNilpotent_iff_pow_card` |
| 例：三頂点の推移的トーナメントは冪零、二頂点の往復は冪零でない | `tournament_nilpotent`、`two_cycle_not_nilpotent` |
| 打ち消しのある係数では崩れる：\(\begin{pmatrix}1&1\\-1&-1\end{pmatrix}^2=0\) だが自己ループあり | `signed_counterexample` |

## 手書きの証明

\((A^{k+1})_{ij}=\sum_l A_{il}(A^k)_{lj}\)。標準順序の加法では和が零なら各項が零、零因子がなければ積が零なら因子が零なので、\((A^{k+1})_{ij}\ne0\) ⇔ ある \(l\) で \(A_{il}\ne0\) かつ \((A^k)_{lj}\ne0\)。帰納法で冪の成分と歩道が対応する。

閉路 \(i\to\cdots\to i\)（長さ \(k+1\)）があれば、それを \(N\) 回回る長さ \(N(k+1)\) の歩道があるので \((A^{N(k+1)})_{ii}\ne0\)。\(A^N=0\) なら \(A^{N(k+1)}=0\) となり矛盾。逆に閉路がなければ、長さ \(|n|\) の歩道は \(|n|+1\) 個の頂点を通るので鳩の巣原理で同じ頂点を二度通り、その区間が閉路になる。したがって長さ \(|n|\) の歩道はなく、\(A^{|n|}=0\)。

## 実行された検証

2026-11-19、クラウドコンテナ上で実行した（Lean `v4.36.0-rc2`、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`）。

- `lake env lean --trust=0 Research/AcyclicNilpotent.lean`：終了コード0、`error:`・`warning:`・`sorryAx` なし。主定理の使用公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内。
- `python -B tests/test_acyclic_nilpotent.py`：6テスト合格。1〜4頂点のループ込みの全0/1行列（2, 16, 512, 65,536個）で \(A^n=0\) ⇔ 深さ優先探索で閉路なし、を確認。ループなしの非巡回グラフの数は 1, 3, 25, 543（OEIS A003024 と一致）。重み \(\{0,1,2\}\) の1〜3頂点でも同じ同値を確認し、0/1行列では冪の成分が歩道の個数に一致することを確認。

GitHub Actions の結果はこの記録の時点では未確認であり、専用CIの完了を別途確認する。

## 論理的境界

1. 同値は打ち消しのない係数についてのもの。符号付き重みでは、閉路があっても冪零になりうる（`signed_counterexample`）。
2. 冪の成分が零でないことと歩道の存在の対応であり、成分の値が歩道の個数に等しいのは 0/1 行列の場合に限る（Python 検算のみ、Lean では値の等式は扱わない）。
3. square-zero 模型の辺写像 \(T_e\) の和 \(S\) の冪零性と、ここでの隣接行列の冪零性を結ぶ一般定理は今回含めない。
