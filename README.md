# primitive-lean

## 現在の入口（2026-11-05）

本リポジトリは **公開** されています。従来のElastica／線形入力の証明原稿を移設せず、出典・統合検証入口と個別研究モジュールを合わせて管理します。

- **正典本文・証明入口**: [原始の形式化.md](原始の形式化.md) · [Elastica](lean/Elastica.lean) · [線形入力](linear_input/lean_check/README.md)
- **統合台帳・検証**: [ソースSHA-256台帳](docs/integration/manifest.json) · [2026-11-02統合説明](docs/integration/2026-11-02-review.md) · `python -B -X utf8 tools/verify.py --integration-only`
- **多項式・Orbit-trace**: [OrbitTrace入口](lean/OrbitTrace.lean) · [研究上の成立条件と未証明事項](docs/research/2026-11-04-orbit-trace-integrals.md)（[PR #68](https://github.com/Sumuji-zkdwn/primitive-lean/pull/68)）
- **演算器の観測・有限自己拡張**: `linear_input/lean_check/OperatorWordObservations.inc` から `HigherOrderLiftSelfRewriting.inc` までの段階的な証明 · [系列の統合境界](docs/integration/2026-11-05-operator-rulefold-consolidation.md)（[PR #74](https://github.com/Sumuji-zkdwn/primitive-lean/pull/74)）
- **操作可能なデモ**: [Rulefold × デジタル曼荼羅](demos/rulefold_mandala.html) · [数学モデルとの区別](demos/RULEFOLD_MANDALA_README.md)
- **未統合の研究系列**: [PR #75](https://github.com/Sumuji-zkdwn/primitive-lean/pull/75) は履歴非保存・局所接合の証明群を統合提案中。#70 と #71 は同名の異なるLean原稿なので未選定です。

**統合状態:** #3・#68・#74 は `main` に取り込み済み。各先端コミットに関する過去のLean／有限検算の成功記録はありますが、それだけで異なる枝を組み合わせた全体検証の成功は主張しません。CI実行の状態・固定コミットは各PRとActionsで確認してください。以下の旧版の定理数・「未マージ」記述は各日付当時の履歴記録です。


**2026-11-02 統合版:** [18件の PR の統合範囲・修正・拡張・再実行](docs/integration/2026-11-02-review.md)。`python -B -X utf8 tools/verify.py --integration-only` で、原本ハッシュ、登録漏れ、オフライン検算、Lean 全宣言の公理監査を実行します。以下の数値はそれぞれ記載された過去版の記録です。今回の実測値は同じコミットの CI と `verification/pr-integration.json` を参照してください。

実験・配布用ツール: [ARC 公開デモのローカル統合検査](experiments/arc3/README.md) · [494 定理の歴史的 Kaggle handoff](docs/KAGGLE.md) · [717 定理の歴史的 handoff](docs/KAGGLE_717.md)。両 handoff は固定された過去の証明集合を対象とし、現在の拡張された証明集合用ではありません。[2026-11-02 統合範囲と再実行](docs/verification/2026-11-02-tooling-integration.md)。

**2026-11-01 F16一手復元と左乗法の退化ブロックをLean検証:** PR #11のF0忘却モデルを拡張。探針1〜8では現在・後続の2観測から全32符号状態を復元でき、それとF0非両立は必要十分で一致する。右乗法・符号表から16次元左乗法の8個の2×2符号付きブロックを構成し、t=±1の各4本の明示的零ベクトルを証明。新規15定理・11定義／略記。固定Leanの[Actions #41227143919](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41227143919)で `--trust=0`・全公理監査に成功、**804定理・982宣言**、警告・未許可公理0。[追補ソース](linear_input/lean_check/F16RecoverySpectrum.inc) / [検証記録](docs/verification/2026-11-01-f16-recovery-degeneracy.md) / [PR #14](https://github.com/Sumuji-zkdwn/primitive-lean/pull/14)。16×16行列全体の行列式・階数12のLean定理はまだ含まない。以下の789定理・956宣言は前段階の検証記録。

**2026-11-01 F16有限ホロノミー・F0忘却降下をLean検証:** EアトラスF16 v4の符号表に基づく128比較四角形、64対64の局所障害、全8比較積が+1となる集約忘却、符号付き高ビット忘却の冪等性と右乗法16種の降下条件を追加（7定理・10定義）。固定Leanの[Actions #41224405790](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41224405790)で `--trust=0` と全公理監査が成功、**789定理・956宣言**、警告・未許可公理0。[証明原稿](linear_input/lean_check/F16Holonomy.inc) / [検証記録](docs/verification/2026-11-01-f16-holonomy.md) / [PR #11](https://github.com/Sumuji-zkdwn/primitive-lean/pull/11)。有限F16と滑らかなSO(2)ホロノミーやクンマー拡大を同一視したものではありません。以下の782定理・939宣言は前段階の記録です。

**2026-11-01 符号の反転軌道8分類を必要十分条件でLean証明:** 先行の`signShape`不変量に対し、`sameReflectionOrbit σ τ ↔ signShape τ = signShape σ` を追加。反転群による商集合と `Fin 3 → Bool` の明示的な同型、軌道数8、および反転を通じたエネルギー同値を証明。固定Leanの[Actions #41218537964](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41218537964)で `--trust=0`、**782定理・939宣言**、全公理監査成功・警告0。[検証記録](docs/verification/2026-11-01-sign-orbits-complete.md) / [PR #10](https://github.com/Sumuji-zkdwn/primitive-lean/pull/10)。8分類は形式的符号の座標反転軌道で、固定値・拘束を含む全15変数対の無条件な同値類数ではありません。以下の776定理・930宣言は前段階の記録です。

**2026-11-01 変数対Eのガロア接続（Lean検証成功）:** 2026-10-20の15組比較に出る四次エネルギーを既存 `gradXY` の偏微分から三次方程式へ縮約し、ヘッセ退化・判別式・チェビシェフ臨界値を接続。`x,y` 反転のエネルギー等式と、32形式的符号を3ビットの8種類へ縮約する不変量も形式化。追加21定理・10定義、GitHub Actions [#41216334895](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41216334895) で `--trust=0` / 全公理監査成功、**776定理・930宣言**、警告・エラー・未許可公理0。[検証記録](docs/verification/2026-11-01-variable-pair-galois.md) / [PR #8](https://github.com/Sumuji-zkdwn/primitive-lean/pull/8)。15組すべてのガロア分類や、二面体ガロア同型を証明したわけではない。以下の755定理・899宣言は前段階の検証記録。

**2026-10-31 クンマー分解体・二面体作用の追加検証成功:** 新しい `KummerDihedral.inc` で実際の分解体・根添加体と二次→クンマー拡大塔を構成し、既約性・原始根の存在を仮定して巡回ガロア群同型と拡大次数を証明。二面体群のラベル作用も検証。GitHub Actions [#41212071155](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41212071155) による固定Lean・`--trust=0` 全監査に成功し、**755定理・899宣言**、警告・許可外公理0。[検証詳細](docs/verification/2026-10-31-kummer-dihedral.md) / [PR #6](https://github.com/Sumuji-zkdwn/primitive-lean/pull/6)。**注：一般のチェビシェフ分解体のガロア群が二面体群になる完全な同型は未証明**。以下の746定理・880宣言は前段階の実行記録です。


**2026-10-31 円分根・クンマー型冪根・チェビシェフ逆像接続（Lean統合検証成功）:** Joukowski写像の衝突因数分解、原始根の円分多項式への接続、冪根ラベルの保存、ZMod上の反転、F0核への橋渡しを6定義・13定理で追加。GitHub Actions [#41207011344](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41207011344) で固定Lean 4.30.0-rc2 + mathlibの `--trust=0` 統合検査・全公理監査に成功し、**746定理・880宣言**（エラー・警告・許可外公理なし）。検証成果物・ソースハッシュも照合済み。PR #5 はPR #3作業ブランチへマージ済み、`main` は未マージ。[検証記録](docs/verification/2026-10-31-galois-chebyshev.md) / [ソース](linear_input/lean_check/GaloisChebyshev.inc)。


原始の形式化に関する Lean ソースと検証入口を管理する公開リポジトリ。

**状態追記（2026-10-30、PR #3）:** `F0MergeChains.inc` に、Fin 5 上の `q₀…q₄、その非空ファイバーサイズ、各段階のK/S/C実現を追加しました（16定理・9定義）。既存717定理・836宣言の検証はコミット `185a1713f2fca219e5f9fb1c5aa11955925cb97f` までの状態を対象とし、この追補は含みません。今回の実行環境には `lake` / `lean` がなく、追加分のLean検査は未実施です。現ブランチの全体検証結果としては扱わず、Windowsで `python -B -X utf8 tools/verify.py --proof-only` を再実行してください。

**2026-10-30 追補：有限ベイズ更新・指数傾斜・忘却との可換条件・四つの操作の有限例を53定理・17定義で形式化。全717定理・836宣言のLean証明・公理検査が成功しました。** 既存のエラスティカ指数重みと区間分割、F0のチェビシェフ代表元へ接続します。固定更新の可換性、途中の削除による順序差、二値分配関数の微分まで含みます。[検証記録](docs/verification/2026-10-30-bayes.md)・[宣言と条件](sources/bayes_formalization_2026-10-30.json)・[提供資料](sources/four_bayes_2026-10-29.md)。以下は各追加段階の記録です。

**2026-10-30 追補：F0の冪等写像・K/S/C合成・適合Sの一般計数・ランク別Kの計数・合流チェインを61定理・30定義/略記で形式化。全664定理・766宣言のLean証明・公理検査が成功しました。** 既存のチェビシェフ代表元写像へ接続し、A+BによるT=Kを証明します。提供ZIPの原本13ファイルを保存し、有限検算もコピー上で再実行しました。[検証記録](docs/verification/2026-10-30-f0.md)・[宣言と条件](sources/f0_formalization_2026-10-30.json)。以下は各追加段階の記録です。

**2026-10-29 追補：チェビシェフ反復の候補等値条件・臨界ファイバー・代表元・全実逆像の個数を40定理・7定義で形式化。全603定理・675宣言のLean証明・公理検査が成功しました。** 通常値では3^n個、±1では(3^n+1)/2個を、候補の網羅性とともに証明します。[今回の検証記録](docs/verification/2026-10-29-branch-fibers.md)・[宣言と条件](sources/branch_fibers_2026-10-29.json)。以下は前段階の記録です。

**2026-10-29 追補：変数対・符号・観測の選択を43定理・13定義で形式化し、全563定理・628宣言のLean証明・公理検査が成功しました。** 原式と既存エネルギーの一致、実偏微分の明示逆、全32符号、符号による可逆性の逆転、観測階層と忘却への接続を含みます。[今回の検証記録](docs/verification/2026-10-29-variable-pairs.md)・[宣言と条件の台帳](sources/variable_pairs_2026-10-29.json)。以下は前段階の記録です。

**2026-10-29：原始の定義から履歴観測・チェビシェフの正規化・最小値観測の忘却条件を導く26定理と8定義を追加し、全520定理・572宣言のLean証明・公理検査が今回のWindows環境で成功しました。** [導出の範囲と実行証拠](docs/verification/2026-10-29-history-branch.md)・[既存宣言との接続台帳](sources/history_branch_2026-10-29.json)。全signatureの一意性定理と人間予測の検証は、この追加には含めていません。

**Kaggleで494定理・538宣言のLeanビルド／証明・公理検査が成功しました。結果ZIPの生ログと固定コミットのソース117ファイルを照合済みです。**

- [2026-10-25の検証結果と証拠](docs/verification/2026-10-25-kaggle.md)
- [Kaggle Notebook](notebooks/primitive_lean_kaggle.ipynb)・[実行手順](docs/KAGGLE.md)
- [統合本文の原稿](原始の形式化.md)
- [全定理の対応・条件・再実行](検証と再実行.md)
- [Elastica の入口](lean/Elastica.lean)
- [線形入力の原稿構成](linear_input/lean_check/README.md)
- [登録状況と残る検証条件](docs/TRANSFER_STATUS.md)
- [スマートフォンからの追加手順](docs/MOBILE_UPLOAD.md)

## 登録したもの

添付 `archive.zip` は5,469,476 bytes、585ファイル、展開後22,654,971 bytesでした。
そのうち、固定設定、Elasticaの24モジュールと入口・監査ソース、線形入力の36原稿と5追補、既存の検証スクリプト、本文原稿・出典資料など116ファイルを7コミットに分けて登録しました。
初回取り込みでは証明・設定・検証スクリプトの内容や元の改行を保持しました。その後、統合入口に明示的な `--proof-only` を追加しています。65個の証明原稿と既存の個別検証器は変更していません。

過去版、生成済みの結合Leanファイル、実験用workファイル、ログ、描画結果、任意の描画依存物など469ファイルは登録対象から外しました。元ZIPは変更していません。
[全585ファイルのSHA-256・登録区分](docs/import/archive_inventory.json)と[登録コミット・照合記録](docs/import/registered_commits.json)を参照できます。

## 検証の状態

ユーザーのKaggle Notebookで `python -X utf8 tools/verify.py --proof-only` が終了コード0で完了しました。Elasticaビルド、`--trust=0` でのjoint検査と追補検査、全538宣言の公理監査をログで確認しています。所要235.365秒。警告・エラー・許可外公理はいずれも0件です。

対象は固定ソースコミット `2e058f2d76e7c7d1fb0f811bcb26a990c47b10d9`。こちらでは提供された実行結果ZIPを照合しており、別環境でビルドを再実行したものではありません。過去版保存・配送・描画監査は今回の結果に含めません。詳細は[検証記録](docs/verification/2026-10-25-kaggle.md)を参照してください。

統合入口 `tools/verify.py` の `--proof-only` で、保存版監査を別扱いにして今回の証明検査だけを実行できます。元の全体検査・`--lean-only` の保存版照合で必要な
`archive/before_unification_2026-10-20.zip` は添付に含まれていません。
描画用vendorや過去出力も移していないため、全体の配送・描画監査は別途資材を整えてから実行します。
固定したLean設定は `lean/` に置いています。

## スマートフォンから続ける

[ファイル追加画面](https://github.com/Sumuji-zkdwn/primitive-lean/upload/main)から少量ずつ追加できます。
変更したソースや小さなZIPをこの対話に添付して、GitHub連携で登録を継続することもできます。
ZIP、`.lake/`、ビルド生成物、認証情報をGit履歴に入れない方針です。

