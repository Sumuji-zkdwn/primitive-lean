# 2026-11-07〜08 オープン PR の一括統合

71 件あったオープン PR を、検証を通したうえで main にまとめた記録。各 PR の証明ソースは、下の「改変」に挙げたものを除いてバイト単位で保存している（[manifest.json](manifest.json) で照合）。

## 統合した PR

| 統合 PR | 内容 |
|---|---|
| #111 | #102（#98・#75・#87・#81・#83・#91 の統合ドラフト）と、依存関係抽出の LEAN_PATH 修正 |
| #112 | 11月5〜8日の 20 件（#76〜#110）と 11月3〜4日の 8 件（#29・#31・#40・#43・#44・#47・#48・#70） |
| 本 PR | #108 の続き（語の正規形と端点の観測可能性）、#58・#59（演算器の文脈同値・方策・積・到達性・感知族・F0 橋渡し・意味モノイド・有限写像の数え上げ）、#45（重力観測の二次モーメント）、#30（五座標の拘束・書換え橋渡し）、#71（並列書き込みの貼り合わせ、`ParallelWriteGluing` として）、#50〜#54（素因数観測。#53・#54 経由） |

途中段階の PR（後続 PR にコミットが丸ごと含まれていたもの）は個別にマージせずクローズした。

## 統合のしくみ

PR 同士の競合は、ほぼすべて次の登録一覧の取り合いだった。

- `docs/integration/manifest.json`：保持ソースの SHA-256 台帳。path ごとの和集合で合体。中身が同じで出典コミットだけ違う行は既存の記録を残す。
- `tools/verify_main_result.py` の `SUPPLEMENTS`：joint 検査に組み込む `.inc` の登録。和集合。
- `tools/verify_main_result.py` の `EXTRA_IMPORTS`：`MainResult.lean` の先頭に足す Mathlib の import。以前は各 PR が組み立て式に直接書き足していたため毎回競合した。一覧にまとめたので、新しい import は一覧に 1 行足せばよい。
- `tools/verify.py` の `supplemental_scopes`：各追補の説明。和集合。
- `.github/workflows/primitive-lean-ci.yml`：pytest の対象ファイル一覧と push 用ブランチ一覧。和集合。

新しい研究 PR を足すときも、この 5 か所に項目を追加するだけで、既存の行を書き換えないようにすると競合しない。

## 改変したソース

pinned の Lean `v4.30.0-rc2` と Mathlib で通らなかった箇所だけを、主張を変えずに直した。台帳では `adapted_retained_source` として理由を記録している。

| ファイル | 改変 |
|---|---|
| `OperatorContextualEquivalence.inc`（#58） | 束縛変数名 `prefix` を `pre` に変更（`prefix` は Lean の予約語で、元のソースは構文解析できなかった） |
| `OperatorF0SemanticBridge.inc`（#58） | `fiber_stable_eq_F0_respects` の未使用の暗黙型引数 `ι` を削除（推論できず、未使用警告も出ていた） |
| `OperatorProductSystems.inc`（#58） | 非推奨の `push_neg` を `push Not` に置き換え |
| `OperatorFiniteMapCounts.inc`（#59） | `simpa ... using rfl` を `simp [eligibleThree]` に置き換え（linter の警告） |
| `OperatorSemanticMonoid.inc`（#59） | `evaluate_injective` を `fun h => evaluate_injective K step h` として適用（`Function.Injective` の強い暗黙引数のため） |
| `GravityObservations.inc`（#45） | `moment_one_formula` の末尾の不要な `ring` を削除（`simp` で証明が終わっていた） |
| `FiveDimLagrange.inc`（#30） | `zero_confirmed_horizontal_step` で、残っていた線形のゴールを `ring` で閉じ、実行されない `<;> ring` を削除 |
| `ParallelWriteGluing.inc`（#71） | #70 と同じ `ParallelLocalGluing.inc`・`LinearInputParallelGluing` だったため、ファイル名と名前空間を `ParallelWriteGluing`・`LinearInputParallelWriteGluing` に変更（名前空間の 2 行だけ） |
| `PrimeFactorFiniteLength.inc`（#53） | `simpa` 3 か所を `simp` に置き換え（`import Mathlib` 全体ではなく必要なモジュールだけで検査したときの linter の警告） |

#50〜#54 の素因数観測の証明は、元は `import Mathlib` 全体を使う単独のプローブとしてだけ検査されていた。Mathlib 全体を `MainResult.lean` に import すると他の証明の型クラス探索が時間切れになるため、必要な `Mathlib.Tactic.NormNum.Prime` と `Mathlib.Data.Sym.Card` だけを `EXTRA_IMPORTS` に足して joint 検査に登録した。

## ワークフローの変更

- `iut-crossrepo-probe.yml`（#78）は手動実行のみ。外部リポジトリ `lana-agents/iut` と Lean v4.32 を使い、元の PR でも 90 分で打ち切られていた。起動条件に `manifest.json` を含んでいたため、研究 PR のたびに走っていた。
- `dependency-graph.yml`（#79）は PR のブランチに bot のコミットを push する。bot の push では他の PR 用ワークフローが起動しないので、先頭が bot のコミットになったときは `primitive-lean-ci.yml` を workflow_dispatch で実行して確認する。

## まだ統合していない PR

| PR | 状態 |
|---|---|
| #49 | `F16SpectralProjectors.inc` の 16×16 行列の全成分を `norm_num` で計算する証明 6 つが、`maxHeartbeats` を 1,000,000 に上げても時間切れになる（自分のブランチの CI でも失敗していた）。定義より前で `plus`・`minus`・`zero` を展開している箇所もある |

取り込まなかった理由は PR にコメントしてある。
