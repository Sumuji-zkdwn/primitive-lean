# Laakso有限近似と観測の保存

このページは第一段階の有限構成と更新則の記録である。後続の[区間実現と幾何的逆系](geometric.md)では、実閉区間の端点を接合する空間、連続な尺度射影、実際の幾何的互換列を追加している。

標準的な二枚化・三分割・新規分点接合による有限多重グラフを定義し、第一近似上で「平均を取れば更新を縮約できる」という主張の反例と、同期部分空間に制限したときの正確な縮約を扱う。既存の未来観測・多操作系の定理に接続する。距離測度空間としての無限Laakso空間はこの拡張の対象に含めない。

## 定義と一般の有限構成

`LaaksoFiniteGraph.inc` の `Graph V E` は、辺IDの型 `E` と二つの端点写像を持つ。隣接関係だけへ潰さないため、同じ端点を持つ平行辺も区別される。

各段階で古い頂点を二枚へ複製し、各辺を三分割する。新しく入れた二つの分点だけを二枚の間で同一視する。実装上の頂点型と辺型は

```text
V' = (V × Bool) ⊕ (E × Fin 2)
E' = E × Bool × Fin 3
```

である。生の二枚の分割頂点からの写像 `rawProjection` は、古い頂点のsheetを保持し、新分点のsheetだけを忘れる。`rawProjection_eq_iff` と `rawQuotientEquiv` が、その同一視の規則と商との一致を証明する。

初期区間の組合せ的表現を二頂点・一辺から始め、任意の自然数段 `n` の `level n` を構成する。辺数は `6^n`、頂点数は `2 |V_n| = 6^n + 3·2^n`。これらは有限個の段の検算だけでなく、自然数に関するLeanの一般定理である。

第一近似の頂点を `L0,L1,R0,R1,W1,W2`、辺を

```text
L0—W1, L1—W1, W1—W2, W1—W2, W2—R0, W2—R1
```

と番号付けする。`firstVertexEquiv`、`firstEdgeEquiv` と端点の可換性が、この六頂点六辺の表と再帰構成の第一段を結ぶ。二本の中央辺のIDは異なる。

## 選んだ非線形更新

第一近似の頂点値 `x : Fin 6 → ℝ` に対して、反応 `f(z)=3z−4z³` とベクトル場 `Fλ(x)=f(x)−λLx` を別途定義する。`L` は六つの辺IDにわたるincidenceの有限和から定義した非重み付きLaplacianであり、座標式はその有限和から証明する。この更新則を静的な曲線変分から自動的に導いたとは主張しない。

観測 `P(x)=((x0+x1)/2,(x2+x3)/2)` は、端点の各対の平均だけを残す。次の二状態は同じ観測を持つ。

```text
x = (1/2,1/2,1/2,1/2,1/2,1/2)
y = (3/4,1/4,1/2,1/2,1/2,1/2)
P(x) = P(y) = (1/2,1/2)
```

しかし任意の実数 `λ` について `P(Fλ(x))=(1,1)`、`P(Fλ(y))=(5/8,1)`。したがって全状態で `P ∘ Fλ = V ∘ P` を満たす `V` は存在しない。

離散更新は明示Euler写像 `Uλ,h(x)=x+hFλ(x)` として定義する。任意の非零実数刻み `h` に対して、上記二状態の次の平均が異なる。既存の `FutureObservations.encode_iff_future` に接続し、現在の平均が同じでも予測状態は異なることを証明する。これは離散写像の代数であり、ODEの解の存在、Euler法の安定性、連続時間極限への収束は含まない。

## 同期部分空間では正確に縮約できる

`J(L,R,W1,W2)=(L,L,R,R,W1,W2)` とすると、同期状態は四変数で表せる。頂点の対応 `syncVertexMap` と辺の対応 `syncEdgeMap` は端点写像と可換である。縮約した四頂点の質量 `(2,2,1,1)` と三辺のconductance `2` は、元の頂点・辺のfiberの個数として証明される。

この質量・conductanceによるLaplacianを `M⁻¹Lc` として、四変数場 `FH(q)=f(q)−λM⁻¹Lc q` を定義すると、

```text
Fλ(Jq) = J(FH(q))
Uλ,h(Jq) = J(UH,λ,h(q))
```

が成り立つ。既存の `representation_iterate` を適用して全自然数回の反復へ延長し、同期状態の未来観測同値と四変数モデルの未来観測同値を対応付ける。

これは六変数全体から任意状態の平均を取る縮約ではない。同期部分空間へ制限した際の正確な持上げであり、二つのwormhole変数も保持している。

## 集合としての逆系と多操作の接続

`InverseTowerObservation.inc` は、互換列 `p_n(x_(n+1))=x_n` の集合を定義する。各更新がbonding mapと可換なら座標ごとに更新でき、各射影が既存の `ExactBridge` になる。任意の有限操作列と射影の可換性、射影観測の未来同値・操作列同値の対応を証明する。

有限bit列と末尾忘却の逆系を具体例にする。任意の無限bit列が互換列を与え、全bit反転は非自明な互換操作である。任意の有限階層への射影は非単射だが、この操作族に対して観測保存が成立する。

第一段階の一般逆系は、Laaksoの幾何射影をまだ実装していない。新分点は粗いグラフの辺の内部へ写るため、後続の[区間実現](geometric.md)で辺内部の点を含めた尺度射影を導入する。有限離散頂点集合の逆極限、幾何的接合、状態値の平均、冪等F0写像を区別する。

## 命題と原稿の対応

| 内容 | 原稿 | 主な宣言 |
|---|---|---|
| 新分点だけの接合と商 | `LaaksoFiniteGraph.inc` | `rawProjection_eq_iff`, `rawQuotientEquiv`, `old_vertices_keep_sheet`, `new_vertices_glue_sheets` |
| 任意段の構成と個数 | 同上 | `level`, `edge_card`, `twice_vertex_card` |
| 第一近似と辺表の一致 | 同上 | `first_source_compatible`, `first_target_compatible`, `first_parallel_middle_edges` |
| 全結合係数で平均への降下が不可能（Eulerは非零刻み） | `LaaksoNonlinearObstruction.inc` | `pairMean_field_does_not_descend`, `pairMean_step_does_not_descend` |
| 縮約の質量と辺重みの由来 | 同上 | `syncMass_eq_multiplicity`, `syncConductance_eq_multiplicity` |
| 同期部分系と全反復 | 同上 | `fineField_syncLift`, `fineStep_iterate_syncLift`, `synchronized_future_iff` |
| 現在の観測と予測状態の相違 | 同上 | `witnesses_same_mean`, `witnesses_predictive_states_distinct` |
| 互換逆系と多操作 | `InverseTowerObservation.inc` | `project_exactBridge`, `project_run`, `projected_wordEq_iff` |
| 非空で非自明な具体逆系 | 同上 | `bitLimit`, `bit_action_true_changes_zero`, `bit_project_not_injective` |

## 再現と証拠

統合証明は既存の共通入口 `python -B -X utf8 tools/verify.py --proof-only` で実行する。新しい三原稿を既存の正確な組立てと全宣言公理監査に登録した。`python -B -X utf8 tools/verify.py --integration-only` は元からある統合検査に加え、新規の有限検査も実行する。

独立した有限検査は `python -B -X utf8 tools/check_laakso_finite.py`。グラフを再帰的に再構成して `n=0..4` の個数・連結性・次数・有理辺長、反例、同期Euler反復を検査する。中央の平行辺を一本消す、または縮約の質量を一律1にする変更を不正と検出する。実数全体についてのLean証明と、これら有限の厳密有理数検査は別の証拠である。

実行結果は `verification/proof-only.json`、`verification/main-result.json`、`verification/laakso-finite.json` に保存される。追加部分の出典とハッシュは [provenance.json](provenance.json)、実行記録は [検証記録](../verification/2026-11-14-laakso-finite.md) を参照する。

## 出典と次の段階

構成は Kauffman et al., [Quantum Mechanics on Laakso Spaces, §2.1](https://arxiv.org/abs/1011.3567) の有限近似、およびResearchに保存されている二枚化・三分割コードを参照した。既存の有限検算・会話の由来を `provenance.json` に記録する。Laakso原論文の次元・Poincaré主結果をここで再証明したとは扱わない。

辺の商位相による実現と連続尺度射影は[第二段階](geometric.md)で扱う。距離測度空間への拡張には、長さ距離、非拡大性とfiber径、測度pushforward、極限距離・測度の構成が必要である。Ahlfors正則性、Hausdorff次元、Poincaré不等式、Dirichlet形式はそれぞれ追加の証明義務となる。[Cheeger–Kleinerの逆極限理論](https://arxiv.org/abs/1312.5227)
