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

GitHub Actions Run `41048557250` は検証コミット `dd2dd7bb4fa2a8099335dc4fe74f82b5c777a263` で成功した。固定した証明ソースは `185a1713f2fca219e5f9fb1c5aa11955925cb97f`。

- Lean 4.30.0-rc2上でjoint検査・supplement検査を新規実行し、両方が終了コード0、警告なしで完了した。
- 結果は717定理・836宣言。全836宣言の公理監査とbaseline照合がPASSし、エラー・警告・予期しない公理は0件。
- mathlibを含む9依存revisionは固定manifestに記録。Kaggleへ渡す入力ファイルは126件で、検査器、9個の追加証明原稿、原本から更新された3説明ファイルをコミット内容に合わせて作業コピー内で上書きする。
- Actions artifact `kaggle-handoff-717-41048557250-1`（artifact ID `12974595335`、ZIP SHA-256 `8886a204b422ad94ed3df7c420cd17fe8a37dbcdbc7b26512337d79bcd95857b`）にNotebook 2種、handoff manifest、結果監査器を保存した。生成物のNotebookハッシュはproof-check `653d6be0c82801a7c0c7fe2e7633704be53d9aedfc3362a75cd8f57d4d715adc`、setup `2d2e625b8349a3fbd028d522908bcc09ba9438b66faad88d4bdc98f2ce8f5c36`。監査器は `c028e79aa88a8534a1bb433d1f4c1274d9d6d7a7313c1abadb4925bdcf94765e`。

この環境ではKaggleへのサインイン済みセッションがなく、717定理版のSaved Version実行と結果ZIP監査は未実施。したがって新しいscriptVersionIdと結果ZIPハッシュはまだ存在しない。PR #2の494/538 Saved Version成功およびZIP監査記録は上表のとおり独立して保持する。競技用Kaggle提出枠は使用していない。
