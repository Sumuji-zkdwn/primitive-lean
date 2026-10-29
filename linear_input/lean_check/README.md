# 線形入力と接続のLean証明

同日の続く追補 [VariablePairObservations.inc](VariablePairObservations.inc) は、実エネルギーと実偏微分から変数対・符号・観測の選択を形式化する。43定理・13定義を加え、全体は563定理・628宣言。原式との代入関係、(x,u)の明示逆と非零入力係数の必要十分条件、全32符号、(x,y)の符号変更例、観測階層の輸送と最小値での忘却を含む。[実行証拠](../../docs/verification/2026-10-29-variable-pairs.md)・[宣言と仮定](../../sources/variable_pairs_2026-10-29.json)。Researchの15組全分類は未移植である。

2026年10月29日に [HistorySignature.inc](HistorySignature.inc) と [BranchForgetting.inc](BranchForgetting.inc) を追補した。実際の座標・面積積分から二次の履歴観測と面積分割を導き、実微分の停留入力からチェビシェフの正規化を導く。既存の線形入力エネルギーから最小値だけでは見えなくなる状態の条件も証明する。17+9定理と6+2定義を追加し、全体の検証対象は520定理・572宣言となる。全次数のsignature一意性や人間予測の検証は含めない。[検証記録](../../docs/verification/2026-10-29-history-branch.md)と[宣言・条件・依存の台帳](../../sources/history_branch_2026-10-29.json)に範囲を記載する。

現在のGitHub版の再実行入口は `python -X utf8 tools/verify.py --proof-only`。従来の5追補の後に履歴・分岐の2追補、続いて変数対の1追補を結合して、元の全宣言とともに `--trust=0` と公理監査で検査する。以下の旧件数と保存版へのリンクは以前の追加段階の記録として保持する。

本文と利用・検証入口は [原始の形式化](../../原始の形式化.html) に統合しました。証明原稿の配置と分担は従来どおりです。このフォルダーの36原稿が線形入力・面積拘束・帰還系の251定理を担当し、エラスティカ側の214定理を実際にimportして接続します。

[全体の定理対応・条件・再実行](../../検証と再実行.html)、[結合検証の全宣言と公理監査](../lean_results.json)、[生成されたAll.lean](All.lean)を参照してください。編集する正本は個々の `.lean` と `.inc` 原稿であり、All.leanは検証時に生成します。

追加の [MainResult.inc](MainResult.inc) の10定理は、同じ乗数による主結果、実際の最小円弧、非零入力の例、同じ係数を使う帰還問題をまとめます。さらに [GeneralMinimum.inc](GeneralMinimum.inc) の6定理を名前空間 `LinearInputMinimum` に追加します。新しい定義は追加せず、既存の `LinearInputObservation.energy` と四次模型の証明を使います。元の465定理・509宣言と既存36原稿を保持し、MainResultまでの475定理・519宣言に続き、GeneralMinimumまでの合計は **481定理・525宣言**です。

GeneralMinimumの最初の2定理は、任意の V:ℝ→ℝ と固定した実数 a,u に対する大域最小と支持不等式の同値、一意な大域最小点と a 以外での厳密な支持不等式の同値です。連続性・微分可能性・凸性は仮定しません。一意性の対象は最小点であり、一般の支持入力の存在は証明していません。残る4定理は四次模型の全平面最小への接続、λ>0での入力・非負余裕の必要十分条件と支持入力の存在条件、λ≥0かつ正の余裕の下での厳密な支持の十分条件です。正の余裕の必要性は主張しません。本文第6.0節、[定理対応表](../../検証と再実行.html)、[追補の出典](../../sources/general_minimum_2026-10-21.json) に対応と仮定を記載します。

2026年10月21日の定理合成では、次の3原稿に13定理を追加し、全体の検証対象を **494定理・538宣言**とします。新しい定義は0件です。

| 原稿と名前空間 | 追加定理数 | 合成する内容 |
|---|---:|---|
| [SupportComposition.inc](SupportComposition.inc) — `LinearInputSupportComposition` | 5 | 支持と既存の観測定理から最小点の順序・支持入力の補間・共通最小点の一致を導出。実際の微分が与えられた点では支持入力がその微分値に一致 |
| [QuarticClassification.inc](QuarticClassification.inc) — `LinearInputQuarticClassification` | 5 | λ>0 の四次模型の零余裕での全最小点、唯一最小性、支持入力および厳密支持入力の存在一意条件 |
| [CurvatureRigidity.inc](CurvatureRigidity.inc) — `LinearInputCurvatureRigidity` | 3 | 保存される位相エネルギーの大域最小点への到達から一定曲率を導き、非一定曲率では到達を排除。実際の面積拘束付き局所最小への接続を含み、入力・面積乗数が零でも成り立つ |

一般支持の5定理と四次模型の5定理の完全名・仮定・直接依存は [定理対応表](../../検証と再実行.html)、今回の採用範囲と出典は [定理合成の台帳](../../sources/theorem_composition_2026-10-21.json) を参照してください。最小点の一意性、支持入力の一意性、曲線の変分問題の局所最小性は異なる主張として記載します。

曲率位相の3定理は `forced_phase_minimum_rigidity`、`forced_phase_not_minimum_of_nonconstant`、`locallyMinimizing_phase_minimum_exclusion` です。最初の定理は k≠0、C²の曲率、開区間での強制曲率方程式と一つの内部位相点の大域最小性を仮定します。保存量と同じ横座標での谷との比較から曲率微分が全区間で零となり、曲率の一定性が従います。位相最小点の一意性は使いません。最後の定理は正の長さ・曲げ係数、C³の角度、実際の面積拘束付き局所最小、非一定曲率を仮定し、既存主結果と同じ p,σ,c による停留性・曲率方程式・保存量と、全内部位相点での大域最小性の排除を同時に導きます。弧長の保存系についての結論であり、物理時間の帰還則を導出するものではありません。

生成ファイル `MainResult.lean` は、検査済みの `All.lean` に `MainResult.inc`、`GeneralMinimum.inc`、`SupportComposition.inc`、`QuarticClassification.inc`、`CurvatureRigidity.inc` の順で追補を加え、元の宣言も含めて監査するためのものです。既存36原稿と従来の検証器 `linear_input/verify_lean.py` は変更せず、追補は `tools/verify_main_result.py` が別に監査します。

上位の `primitive` フォルダーから `python -X utf8 tools/verify.py --rebuild` で追補を含む全体を検査します。従来の `python -X utf8 linear_input/verify_lean.py` は既存36原稿の結合検証を担当します。既存の証明原稿は本文統合前の [保存ZIP](../../archive/before_unification_2026-10-20.zip) と同じ内容です。追補の記録は [main-result.json](../../verification/main-result.json)、全体の合計は [lean.json](../../verification/lean.json) に保存します。ここでの件数は検証対象を示し、実行済みの成否は各記録の対象ハッシュと実行日時で確認します。
