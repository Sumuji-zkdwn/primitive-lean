# F0：冪等写像の粗化は塊サイズ型の合流チェインをちょうど実現する

## 位置づけ

F0 の会話資料 [03_conjecture_and_cautions.md](../../sources/f0_math_chat_2026-10-29/03_conjecture_and_cautions.md) 第6節は、二塊合流グラフが整数分割から定義した構造であり、個別の写像からこのグラフの各辺が生成されるという実現定理は証明されていないと注意し、第7節で「元の写像の合成と、型の合流・細分化の対応条件」を今後の課題に挙げていた。本文第8.15節「分割型の合流チェイン」も、型グラフと写像の更新は対応写像が証明されるまで別の構造として扱うとしていた。この追加は、冪等写像の**粗化**について、その対応を両方向で証明する。

- Lean：[lean/Research/F0CoarseningMerge.lean](../../lean/Research/F0CoarseningMerge.lean)（名前空間 `F0CoarseningMerge`、19定理）
- 独立検算：[tests/test_f0_coarsening_merge.py](../../tests/test_f0_coarsening_merge.py)
- 専用CI：[.github/workflows/f0-coarsening-merge.yml](../../.github/workflows/f0-coarsening-merge.yml)。統合検査 `tools/pr_integration.py` にも `--trust=0` 段として登録した。

## 定義

有限集合 \(\alpha\) 上の冪等写像 \(K\) について、固定点（代表点）の集合 `fixSet K`、塊 `fiber K a` \(=K^{-1}(a)\)、塊サイズ型 `type K`（固定点ごとの塊の大きさの多重集合）を置く。`Merge`・`Chain` は [F0MergeChains.inc](../../linear_input/lean_check/F0MergeChains.inc) と同じ本文で定義する（joint 検査の宣言との同一視は Lean では行わない）。

\(K'\) が \(K\) の**粗化**であるとは \(K'\circ K=K'\)（`Coarsens K K'`）。冪等な \(K\) ではこれは「\(Kx=Ky\Rightarrow K'x=K'y\)」と同値（`coarsens_iff_ker`）。

## 結果

| 内容 | Lean 宣言 |
|---|---|
| 二つの塊 \(K^{-1}(a_1),K^{-1}(a_2)\) をまとめた写像 `mergeFibers K a₁ a₂` は冪等で \(K\) の粗化、固定点は \(a_2\) が抜け、型は二塊合流 | `mergeFibers_idempotent`、`mergeFibers_coarsens`、`fixSet_mergeFibers`、`type_mergeFibers` |
| **合流の実現**：`type K` の任意の二塊合流は、二つの塊をまとめる冪等な粗化で実現される | `merge_realized` |
| 固定点の数が等しい冪等な粗化では型は変わらない | `type_eq_of_coarsens_card` |
| **粗化 ⇒ 合流チェイン**：冪等な粗化 \(K'\) の型へは `type K` から長さ \(r-r'\) の合流チェインで到達する | `coarsening_chain` |
| 合流チェインは固定点がその長さだけ少ない冪等な粗化で実現される | `chain_realized` |
| **対応**：長さ \(n\) の合流チェインで \(q\) へ行ける ⇔ 固定点が \(n\) 個少ない冪等な粗化 \(K'\) で `type K' = q` | `chain_iff_coarsening` |

## 手書きの証明

**合流の実現。** 型の二つの成分 \(a,b\) に対応する相異なる代表点 \(a_1,a_2\) を取り、\(K^{-1}(a_2)\) の点をすべて \(a_1\) に送る。\(a_1\) の塊は \(K^{-1}(a_1)\cup K^{-1}(a_2)\) になり、他の塊は変わらない。

**粗化 ⇒ 合流チェイン。** \(\varphi:\mathrm{Fix}\,K\to\mathrm{Fix}\,K'\)、\(a\mapsto K'a\) は全射（\(b=K'(Kb)\)）。\(r>r'\) なら鳩の巣原理で \(K'a_1=K'a_2\) となる相異なる代表点があり、その二つの塊をまとめても \(K'\) への粗化は保たれ、固定点は1つ減る。帰納法で \(r=r'\) に帰着し、そのとき \(\varphi\) は全単射で \(K'^{-1}(K'a)=K^{-1}(a)\) なので型は一致する。

## 実行された検証

2026-11-19、クラウドコンテナ上で実行した（Lean `v4.36.0-rc2`、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`）。

- `lake env lean --trust=0 Research/F0CoarseningMerge.lean`：終了コード0、`error:`・`warning:`・`sorryAx` なし。全19定理の使用公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内。
- `python -B tests/test_f0_coarsening_merge.py`：3テスト合格。1〜5点上の全ての冪等写像の対で、粗化なら型が幅優先探索でちょうど \(r-r'\) 回の合流で到達可能であること、逆に各 \(K\) について \(n\) 回の合流で到達する型の集合が、固定点が \(n\) 個少ない粗化の型の集合と一致することを確認。

GitHub Actions の結果はこの記録の時点では未確認であり、専用CIの完了を別途確認する。

## 論理的境界

1. 対応は粗化（\(K'\circ K=K'\)）についてのもの。一般の \(S\)・\(C\) を経由する更新 \(T=K\circ C\circ K^{(d)}\circ S\) が型を合流させるとは主張しない。
2. 型は塊のラベルを忘れるので、同じ合流に対応する粗化は一般に複数ある。
3. 細分化（逆向きの辺）は扱わない。
