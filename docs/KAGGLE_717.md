# 717定理版 Kaggle 検証受け渡し

## 検証対象と範囲

この受け渡しは PR #3 の証明ソース `185a1713f2fca219e5f9fb1c5aa11955925cb97f` に固定する。PR #2 の494定理版とは別の Notebook、マニフェスト、Kaggle Saved Version、結果ZIP監査として記録する。

PR #3 のローカル検証記録では、Lean 4.30.0-rc2 と同じ9依存 revisionを固定し、717定理・836宣言を検査して、全836宣言の公理監査に成功している。`tools/verify.py --proof-only` は joint 検査と supplement 検査を新規実行する。

## PR #2の既存記録

| 項目 | 既存の成功記録 |
|---|---|
| ソースコミット | `5d23c590398680aa7a67919a54fc2bdd915614b4` |
| 定理・宣言数 | 494 / 538 |
| GitHub Actions | Run `40703848720` 成功 |
| Kaggle Saved Version | `363335255`、358.1秒で完了 |
| Kaggle結果監査 | ZIP SHA-256 `becc42a804a5915466ae68514853848d2ba48fd7a9d436a05956e96685e2bc8c`、監査器PASS |

この旧版のKaggle検証は再実行しない。

## PR #3での差分照合

- ソースコミットは `185a1713f2fca219e5f9fb1c5aa11955925cb97f`。
- Lean toolchainは `leanprover/lean4:v4.30.0-rc2`。mathlibを含む9依存のrevisionはPR #2の受け渡し方式と同一。
- 494/538に対する追加分は223定理・298宣言（75定義/略記）。PR #3の統合レポート上では465/509のjoint基線に14補助群252/327を加え、717/836となる。先行5補助群が29/29、今回の9群が223/298を占めるため、PR #2の494/538からの増分と整合する。
- 既存のKaggle ZIPは原本入力として再利用し、PR #3で追加された9個の .inc、更新された検査器、原本以降に更新された3つの説明ファイルをソースコミットからNotebookへ埋め込む。差し替えはKaggleの作業コピー内だけで行い、原本・検査済み成果物には書き込まない。
- 受け渡しには原本ZIP由来の116ファイルに、`tools/proof_only.py`と新しい9原稿を足した126ファイルを含める。Kaggle上でファイルハッシュ、Lean設定、9依存を照合する。
- 新NotebookはKaggleコンペ提出とGitHubへの書き戻しを行わない。

## 新版の実行状況

この記録の初期版では、新しいGitHub Actions実行とKaggle Saved Versionはまだ未確認。後続の証拠は、Actions Run ID、検証コミット、Notebook・マニフェスト・監査器のSHA-256、Kaggle scriptVersionId、結果ZIP SHA-256と監査結果を個別に追記する。
