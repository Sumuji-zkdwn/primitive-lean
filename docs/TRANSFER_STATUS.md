# 転送状況

2026-10-25（日本時間）

## 確認した事実

- 初回登録前：GitHub の repository size は 0。コミット取得は `Git Repository is empty`（409）。
- 初回コミット：`04863df1363f04a0b8195c32b0e826bedfd4c5e0`。
- 初回コミット後：README.md の内容を GitHub から読み返し、コミット履歴にも初回コミットがあることを確認。
- 初回以後、この初期整備で追加する対象は README.md、.gitignore、docs/MOBILE_UPLOAD.md、docs/TRANSFER_STATUS.md の4ファイルのみ。
- 今回は Lean ソース、依存設定、GitHub Actions のワークフローを登録していない。

## 元ファイルの取得状況

既存の「検証と再実行.md」は読めた。記載された構成・再実行方法は参考情報であり、ソースの実物や今回のビルド記録の代わりにしない。

取得して調べた「私.zip」（2026-10-20、9,897,641 bytes、105エントリ）は別の統合Webアプリであり、今回必要な Lean 設定・MainResult.inc を収録していなかった。今回の転送元には採用していない。

Kaggle 側の約5.2 MB / 585ファイルはユーザー報告のみ。実体・全パス・ハッシュ・最新版との一致は未確認。Kaggle 環境には今回アクセスしていない。

## 未転送・未照合

| 候補 | 状態 |
|---|---|
| lean/lean-toolchain | 原本未取得・未転送 |
| lean/lakefile.toml | ファイル名は対話で報告。原本未取得・未転送 |
| lean/lake-manifest.json | 原本未取得・未転送 |
| lean/Elastica/*.lean と入口モジュール | 原本未取得・未転送 |
| linear_input/lean_check の既存原稿 | 原本未取得・未転送 |
| MainResult.inc / GeneralMinimum.inc / SupportComposition.inc / QuarticClassification.inc / CurvatureRigidity.inc | 原本未取得・未転送 |
| tools/verify.py / tools/verify_main_result.py / linear_input/verify_lean.py | 原本未取得・未転送 |
| 上記スクリプトが読む補助ソース・監査データ | 原本取得後に依存を調べる |

## 検査の状態

- このリポジトリの Lean ビルド：未実行。
- このリポジトリの公理監査・証明検査：未実行。
- 過去の文書にある定理数・合格記述を、このコミットの合格結果として扱わない。
- ソース取得後は、小さい単位ごとに元のパス・内容と GitHub の実ファイルを照合し、コミットSHAを記録する。
