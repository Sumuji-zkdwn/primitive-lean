# カーネル受理済み宣言の依存関係（primitive-lean）

対象コミット: `67fdf6b74bbbcb20dc70e7bf98b90471e329aa91`（main）。自動生成定理は `autonomy/verified-operator-growth` の台帳 cycle 1–2 と SHA-256 が一致するソースを、その上に積んでコンパイルしたものです。

## 読み方の前提

- 辺は「Lean が受理した項の中に、その定数が現れる」ことだけを表します。その依存が数学的に必要だという意味ではありません。
- 初期層への経路がないことは、初期層から導出できないことの証明ではありません。
- 4 種類の関係を混ぜずに出力します。
  1. **proof**：定理の証明項に現れる定数
  2. **statement / definition**：命題の型、または定義本体に現れる定数
  3. **module**：import によるモジュール依存。Elastica ライブラリのみ。線形入力側は 1 ファイルに連結されるため、登録順しかありません
  4. **conceptual**：このツールは生成しません。ERG/HMDG の ConceptBridge・ProofBridge は未検証の候補のまま扱います
- 層の定義
  - **initial**：`lean/Elastica/` の 24 モジュールと、`All.lean` を構成する 36 部品
  - **subsequent**：`MainResult.lean` に登録順に連結される 60 の追補
  - **autonomy**：自動生成された有限模型
  - **mathlib / core / batteries**：外部ライブラリ
- 補助定数（`eq_1`、`match_1`、`_proof_N`、`_simp_N` など）は持ち主の宣言にまとめています。自分の補助定数の中身は自分の辺として扱い、他の宣言の補助定数への参照はその持ち主への参照として扱います。

## 抽出の検証

- 検証レポートの全 1901 宣言について、層とソースファイルが一致しました（不一致 0）。レポートにないノード 48 個は、`private` 宣言・構造体・自動生成分です。
- 主定理 2 の証明項から抽出した定理参照は、ソースのタクティクに書かれた 6 補題と一致しました。
- 字句照合との比較（後続定理の証明内のプロジェクト定理参照）：両方にあるもの 1200、カーネル項だけにあるもの 7（インスタンス解決・型クラス経由）、字句だけにあるもの 3（名前は書かれているが、最終的な項には残らない）。

## 規模

| 層 | 定理 | 定義・型 |
|---|---:|---:|
| initial | 476 | 46 |
| subsequent | 984 | 427 |
| autonomy | 10 | 6 |

「初期 465 定理」は、既存の検証器が正規表現で `theorem`/`lemma` 行を数えた値です。ここでの initial の定理数は、その正規表現が拾わない `private` 定理、インスタンス、自動生成された合同補題を含むため、数が異なります（差 11）。

## 小規模検証：主定理・自動生成・代表的な後続定理

証明の深さは、プロジェクト内の定理だけをたどる証明項の連鎖の最長段数です（0 なら、証明がプロジェクトの定理を使っていない）。距離 0 は、その宣言自身が初期層であることを示します。

### README の主定理 5 件

| 宣言 | 層 | 証明の深さ | 初期層までの距離（証明のみ / 全種類） | 推移的依存（層別） | 証明の形 |
|---|---|---:|---|---|---|
| `Elastica.locallyMinimizing_necessary_conditions` | initial | 7 | 0 / 0 | initial 65 | 複合 |
| `LinearInputMainResult.locallyMinimizing_pressure_curvature_phase` | subsequent | 11 | 1 / 1 | initial 98 | 複合 |
| `LinearInputMainResult.pressure_parameters_global_feedback` | subsequent | 10 | 1 / 1 | initial 69 | 既存定理1つの適用（`LinearInputGlobalConsequences.exists_global_injective_convergent_solution`） |
| `LinearInputQuarticClassification.unique_global_minimum_iff` | subsequent | 6 | 2 / 1 | initial 17, subsequent 5 | 複合 |
| `LinearInputBranchFibers.real_inverse_card_regular` | subsequent | 5 | なし / なし | subsequent 19 | 複合 |

### 自動生成定理（cycle 1。cycle 2 は数値だけが異なる同形）

| 宣言 | 層 | 証明の深さ | 初期層までの距離（証明のみ / 全種類） | 推移的依存（層別） | 証明の形 |
|---|---|---:|---|---|---|
| `LinearInputAutoCycle00001.minimal_quotient_splits` | autonomy | 2 | なし / なし | autonomy 6, subsequent 14 | 既存定理1つの適用（`LinearInputOperatorRefinement.strict_refinement_splits_quotient`） |
| `LinearInputAutoCycle00001.new_distinguishes` | autonomy | 0 | なし / なし | autonomy 3, subsequent 3 | 決定手続きのみ |
| `LinearInputAutoCycle00001.no_old_word_dictionary` | autonomy | 3 | なし / なし | autonomy 6, subsequent 8 | 複合 |
| `LinearInputAutoCycle00001.old_indistinguishable` | autonomy | 1 | なし / なし | autonomy 3, subsequent 2 | 複合 |
| `LinearInputAutoCycle00001.old_run_identity` | autonomy | 0 | なし / なし | autonomy 1, subsequent 1 | mathlib/core のみ |

### 代表的な後続定理

| 宣言 | 層 | 証明の深さ | 初期層までの距離（証明のみ / 全種類） | 推移的依存（層別） | 証明の形 |
|---|---|---:|---|---|---|
| `LinearInputOperatorRefinement.strict_refinement_splits_quotient` | subsequent | 1 | なし / なし | subsequent 13 | 複合 |
| `LinearInputMetaRuleExtension.metaStep_sound` | subsequent | 1 | なし / なし | subsequent 19 | 複合 |
| `LinearInputBayes.posterior_commute` | subsequent | 3 | なし / なし | subsequent 6 | 複合 |
| `LinearInputWFSObservation.observationDistance_triangle` | subsequent | 1 | なし / なし | subsequent 4 | 複合 |
| `LinearInputF16UnexpectedBridges.singular_iff_chebyshev_critical` | subsequent | 8 | なし / なし | subsequent 52 | 複合 |
| `LinearInputCurvatureRigidity.locallyMinimizing_phase_minimum_exclusion` | subsequent | 12 | 2 / 1 | initial 98, subsequent 3 | 複合 |

## 全体：後続定理は初期層からどこまで届いているか

- 後続 984 定理のうち、全種類の辺で初期層に到達するもの：**57（5%）**
- 証明項の連鎖だけで初期定理に到達するもの：**34（3.4%）**
- 後続層・自動生成層から直接参照される初期ノード：46 / 522。そのうち後続の**証明**で使われる初期**定理**は 28 / 476
- 後続から初期層への接続の大半は、定義（`LinearInputDesign.f`・`E`・`input`、`Elastica.xCoord` など）を命題の中で再利用する形です。初期の**定理**を証明に使う形は少数です。

よく参照される初期ノード（後続層からの直接参照数、全種類合計）：

| 参照数 | 初期ノード | 種類 |
|---:|---|---|
| 35 | `LinearInputDesign.E` | def |
| 23 | `LinearInputObservation.energy` | def |
| 22 | `Elastica.xCoord` | def |
| 22 | `Elastica.yCoord` | def |
| 17 | `LinearInputDesign.input` | def |
| 9 | `LinearInputDesign.f` | def |
| 9 | `LinearInputAreaVariation.area` | def |
| 8 | `LinearInputPressureStationary.Stationary` | def |
| 7 | `LinearInputAreaMinimum.LocallyMinimizing` | def |
| 7 | `LinearInputGradient.gx` | def |
| 7 | `LinearInputGradient.gy` | def |
| 6 | `Elastica.exponentialWeight` | def |

### 追補ファイル別

| 追補 | 定理数 | 初期層に到達（全種類） | 証明のみで到達 | 最大の証明の深さ | 既存定理1つの適用 | 決定手続きのみ |
|---|---:|---:|---:|---:|---:|---:|
| BranchFibers.inc | 40 | 0 | 0 | 8 | 0 | 6 |
| ComplementaryObservationExamples.inc | 20 | 0 | 0 | 1 | 0 | 1 |
| ComplementaryPencilRecovery.inc | 24 | 0 | 0 | 6 | 0 | 0 |
| EWFSFenchel.inc | 24 | 0 | 0 | 2 | 0 | 0 |
| EWFSFutureBridge.inc | 15 | 0 | 0 | 4 | 0 | 0 |
| EnergyWfsFenchel.inc | 28 | 0 | 0 | 2 | 0 | 0 |
| F0Counting.inc | 10 | 0 | 0 | 3 | 0 | 0 |
| F0FutureMinimality.inc | 6 | 0 | 0 | 3 | 0 | 1 |
| F0MergeChains.inc | 26 | 0 | 0 | 3 | 0 | 8 |
| F0Retractions.inc | 41 | 0 | 0 | 4 | 2 | 0 |
| F0UpdateDescent.inc | 10 | 0 | 0 | 1 | 0 | 1 |
| F16CompleteRank.inc | 9 | 0 | 0 | 7 | 0 | 0 |
| F16ConstructiveRecovery.inc | 15 | 0 | 0 | 7 | 1 | 0 |
| F16FullMatrix.inc | 13 | 0 | 0 | 4 | 0 | 6 |
| F16FullRank.inc | 13 | 0 | 0 | 6 | 0 | 0 |
| F16Holonomy.inc | 7 | 0 | 0 | 1 | 0 | 6 |
| F16RankCertificate.inc | 10 | 0 | 0 | 3 | 0 | 4 |
| F16RealDeterminant.inc | 5 | 0 | 0 | 2 | 0 | 2 |
| F16RecoverySpectrum.inc | 15 | 0 | 0 | 3 | 0 | 11 |
| F16SaddleCantor.inc | 14 | 0 | 0 | 3 | 0 | 0 |
| F16UnexpectedBridges.inc | 15 | 0 | 0 | 8 | 0 | 4 |
| FiniteSelfSynthesis.inc | 18 | 0 | 0 | 4 | 0 | 3 |
| FourBayes.inc | 21 | 0 | 0 | 5 | 1 | 2 |
| FutureFiniteHorizon.inc | 14 | 0 | 0 | 6 | 0 | 3 |
| FutureObservations.inc | 14 | 0 | 0 | 4 | 0 | 0 |
| GaloisChebyshev.inc | 13 | 0 | 0 | 5 | 0 | 2 |
| HannaJetCorrection.inc | 4 | 0 | 0 | 1 | 0 | 3 |
| HigherOrderLiftSelfRewriting.inc | 22 | 0 | 0 | 2 | 0 | 11 |
| KummerDihedral.inc | 9 | 0 | 0 | 0 | 0 | 0 |
| MetaRuleSelfExtension.inc | 20 | 0 | 0 | 2 | 0 | 7 |
| ObservationRetractionPolarity.inc | 16 | 0 | 0 | 8 | 2 | 0 |
| OperatorBisimulation.inc | 21 | 0 | 0 | 2 | 0 | 0 |
| OperatorFiniteHorizon.inc | 16 | 0 | 0 | 6 | 0 | 2 |
| OperatorSemanticClosure.inc | 17 | 0 | 0 | 3 | 2 | 0 |
| OperatorVocabularyRefinement.inc | 22 | 0 | 0 | 3 | 2 | 1 |
| OperatorWordObservations.inc | 28 | 0 | 0 | 3 | 0 | 1 |
| RecursiveOperatorReentry.inc | 17 | 0 | 0 | 3 | 0 | 6 |
| RepresentationBridges.inc | 7 | 0 | 0 | 6 | 1 | 0 |
| Rule481Symmetry.inc | 12 | 0 | 0 | 2 | 1 | 5 |
| RuleSelfModification.inc | 17 | 0 | 0 | 2 | 0 | 6 |
| SemanticIntervalNecessity.inc | 16 | 0 | 0 | 5 | 0 | 4 |
| StrangeOperatorBoundary.inc | 5 | 0 | 0 | 1 | 0 | 1 |
| StrangeOperatorConjugacy.inc | 22 | 0 | 0 | 3 | 0 | 0 |
| StrangeOperatorFixedSets.inc | 6 | 0 | 0 | 2 | 0 | 0 |
| StrangeOperatorGalois.inc | 18 | 0 | 0 | 4 | 0 | 2 |
| TemporalSampling.inc | 20 | 0 | 0 | 4 | 1 | 1 |
| VariablePairGaloisBridge.inc | 27 | 0 | 0 | 5 | 0 | 3 |
| WFSCanonicalLift.inc | 8 | 0 | 0 | 1 | 0 | 2 |
| WFSMobiusFourier.inc | 14 | 0 | 0 | 3 | 0 | 2 |
| WFSProjectiveSampling.inc | 22 | 0 | 0 | 2 | 0 | 5 |
| FiniteBayes.inc | 32 | 3 | 1 | 5 | 0 | 0 |
| ShearCommutator.inc | 28 | 3 | 0 | 8 | 0 | 0 |
| VariablePairObservations.inc | 43 | 5 | 0 | 5 | 0 | 1 |
| BranchForgetting.inc | 9 | 5 | 1 | 3 | 0 | 0 |
| HistorySignature.inc | 17 | 13 | 11 | 3 | 1 | 0 |
| SupportComposition.inc | 5 | 4 | 2 | 2 | 0 | 0 |
| CurvatureRigidity.inc | 3 | 3 | 3 | 12 | 0 | 0 |
| GeneralMinimum.inc | 6 | 6 | 3 | 5 | 0 | 1 |
| MainResult.inc | 10 | 10 | 8 | 11 | 2 | 0 |
| QuarticClassification.inc | 5 | 5 | 5 | 6 | 0 | 0 |

どの定理も初期層に到達しない追補は 50 / 60 ファイルです。これらは初期層と無関係に、mathlib と自前の定義の上に立っています。初期層から導出できないという意味ではありません。

## 証明の深さの分布（後続定理）

| 深さ | 定理数 |
|---:|---:|
| 0 | 460 |
| 1 | 196 |
| 2 | 132 |
| 3 | 79 |
| 4 | 43 |
| 5 | 33 |
| 6 | 21 |
| 7 | 11 |
| 8 | 5 |
| 10 | 2 |
| 11 | 1 |
| 12 | 1 |

## 一般定理の単なる具体化と考えられる箇所（ヒューリスティック）

判定規則：束縛変数とメタデータを外した証明項の先頭が、別のソースファイルにあるプロジェクト定理 1 つです。かつ、他に使うプロジェクト定理が同じファイル内の補題だけである場合、「既存定理1つの適用」とします。これは項の形だけに基づく判定で、数学的に新しい内容がないことの証明ではありません。

- initial：既存定理1つの適用 6、決定手続きのみ 8、mathlib/core のみ 144、複合 318
- subsequent：既存定理1つの適用 16、決定手続きのみ 124、mathlib/core のみ 336、複合 508
- autonomy：既存定理1つの適用 2、決定手続きのみ 2、mathlib/core のみ 2、複合 4

| 定理 | 層 | 適用している定理 |
|---|---|---|
| `LinearInputAutoCycle00001.minimal_quotient_splits` | autonomy | `LinearInputOperatorRefinement.strict_refinement_splits_quotient` |
| `LinearInputAutoCycle00002.minimal_quotient_splits` | autonomy | `LinearInputOperatorRefinement.strict_refinement_splits_quotient` |
| `LinearInputF0.branchPiK_idempotent` | subsequent | `LinearInputBranchFibers.pi_retraction_idempotent` |
| `LinearInputF0.branchZeroK_idempotent` | subsequent | `LinearInputBranchFibers.zero_retraction_idempotent` |
| `LinearInputF16ConstructiveRecovery.baseMatrix_isUnit` | subsequent | `LinearInputF16UnexpectedBridges.zero_probe_isUnit` |
| `LinearInputFourBayes.forgotten_stays_zero` | subsequent | `LinearInputBayes.posterior_zero_prior` |
| `LinearInputHistorySignature.two_inputs_determine_area` | subsequent | `LinearInputObservation.two_inputs_iff_pair` |
| `LinearInputMainResult.example_feedback_global` | subsequent | `LinearInputGlobalConsequences.exists_global_injective_convergent_solution` |
| `LinearInputMainResult.pressure_parameters_global_feedback` | subsequent | `LinearInputGlobalConsequences.exists_global_injective_convergent_solution` |
| `LinearInputObservationRetractionPolarity.close_retract_of_surjective` | subsequent | `LinearInputStrangeFixedSets.close_singleton_top_of_all_fixed` |
| `LinearInputObservationRetractionPolarity.retract_self_stops` | subsequent | `LinearInputStrangeGalois.idempotent_self_stops` |
| `LinearInputOperatorRefinement.generated_preserves_old` | subsequent | `LinearInputOperatorWords.word_run` |
| `LinearInputOperatorRefinement.witness_old_equiv` | subsequent | `LinearInputOperatorWords.base_cannot_distinguish` |
| `LinearInputOperatorSemanticClosure.compatible_constant` | subsequent | `LinearInputOperatorWords.word_refl` |
| `LinearInputOperatorSemanticClosure.compatible_word` | subsequent | `LinearInputOperatorWords.word_run` |
| `LinearInputRepresentationBridges.reconstruct_leftMatrix_observations` | subsequent | `LinearInputF16ConstructiveRecovery.reconstruct_observations` |
| `LinearInputRule481.step_preserves_mirror` | subsequent | `LinearInputF0Descent.equivariant_preserves_fixed` |
| `LinearInputTemporalSampling.spin_full_iff_equal` | subsequent | `LinearInputEWFSFuture.E_x_future_iff_eq` |

## モジュール依存（import、Elastica のみ）

| モジュール | import しているプロジェクト内モジュール |
|---|---|
| `AutonomyProbe` | `PrimitiveMain` |
| `Elastica` | `Elastica.AffineEquivalence`, `Elastica.CombinedConsequences`, `Elastica.Composition`, `Elastica.ConstrainedSecondVariation`, `Elastica.ConstraintRegularity`, `Elastica.Derivation`, `Elastica.Equations`, `Elastica.ExactVariation`, `Elastica.Examples`, `Elastica.ExponentialWeight`, `Elastica.Geometry`, `Elastica.LocalMinimum`, `Elastica.MinimumConditions`, `Elastica.PowerLogResponse`, `Elastica.Reconstruction`, `Elastica.ReplacementConsequences`, `Elastica.ScalarMinimum`, `Elastica.Scaling`, `Elastica.ScalingMinima`, `Elastica.SecondVariation`, `Elastica.Stationary`, `Elastica.StraightConstraint`, `Elastica.Variation`, `Elastica.WeightResponse` |
| `Elastica.AffineEquivalence` | `Elastica.Examples`, `Elastica.MinimumConditions`, `Elastica.PowerLogResponse` |
| `Elastica.CombinedConsequences` | `Elastica.AffineEquivalence`, `Elastica.ScalingMinima` |
| `Elastica.Composition` | `Elastica.Geometry`, `Elastica.Variation` |
| `Elastica.ConstrainedSecondVariation` | `Elastica.SecondVariation`, `Elastica.Stationary` |
| `Elastica.ConstraintRegularity` | `Elastica.Reconstruction`, `Elastica.Stationary` |
| `Elastica.Derivation` | `Elastica.Equations`, `Elastica.Stationary`, `Elastica.Variation` |
| `Elastica.Equations` | — |
| `Elastica.ExactVariation` | `Elastica.ConstraintRegularity`, `Elastica.Stationary`, `Elastica.Variation` |
| `Elastica.Examples` | `Elastica.Geometry`, `Elastica.Variation` |
| `Elastica.ExponentialWeight` | `Elastica.Composition`, `Elastica.ConstrainedSecondVariation`, `Elastica.Derivation`, `Elastica.LocalMinimum` |
| `Elastica.Geometry` | — |
| `Elastica.LocalMinimum` | `Elastica.Stationary`, `Elastica.Variation` |
| `Elastica.MinimumConditions` | `Elastica.ConstrainedSecondVariation`, `Elastica.Derivation`, `Elastica.ExactVariation`, `Elastica.LocalMinimum`, `Elastica.ScalarMinimum` |
| `Elastica.PowerLogResponse` | `Elastica.Examples` |
| `Elastica.Reconstruction` | `Elastica.Geometry`, `Elastica.Variation` |
| `Elastica.ReplacementConsequences` | `Elastica.Composition`, `Elastica.ExponentialWeight`, `Elastica.LocalMinimum` |
| `Elastica.ScalarMinimum` | — |
| `Elastica.Scaling` | `Elastica.Geometry`, `Elastica.Variation` |
| `Elastica.ScalingMinima` | `Elastica.ExponentialWeight`, `Elastica.Scaling` |
| `Elastica.SecondVariation` | `Elastica.Variation` |
| `Elastica.Stationary` | — |
| `Elastica.StraightConstraint` | `Elastica.Examples`, `Elastica.Reconstruction`, `Elastica.SecondVariation` |
| `Elastica.Variation` | — |
| `Elastica.WeightResponse` | `Elastica.ExponentialWeight`, `Elastica.PowerLogResponse` |
| `PrimitiveMain` | `Elastica`, `Elastica.AffineEquivalence`, `Elastica.ConstraintRegularity`, `Elastica.Equations`, `Elastica.ExactVariation`, `Elastica.Geometry`, `Elastica.MinimumConditions`, `Elastica.Stationary`, `Elastica.Variation` |

`PrimitiveMain` は検証済みの `MainResult.lean` のコピーで、`AutonomyProbe` は自動生成ソースを積んだ検査用モジュールです。

## データ

- `data/deps.json`：全ノードの直接依存（proof / statement / definition 別）、外部ライブラリ参照数、到達距離、深さ、証明の形
- `data/transitive.json`：プロジェクト内の推移的依存（全種類の辺）
- `data/source_edges.json`：ソースファイル間の集約辺
- `data/validation.json`：上記の検証結果

再生成：`bash tools/deps/run.sh`（Lean と mathlib のキャッシュが必要。約 5 分）
