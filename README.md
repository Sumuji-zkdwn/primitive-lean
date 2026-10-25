# primitive-lean

原始の形式化に関する Lean ソースと検証入口を管理する非公開リポジトリ。

**初回コミットは作成済みです。Lean ソースは未転送、ビルド・証明検査は未実行です。**

## スマートフォンから続ける

- [追加の手順と必須ファイルの確認表](docs/MOBILE_UPLOAD.md)
- [実際の登録状況・未転送の内容](docs/TRANSFER_STATUS.md)
- [ブラウザで新しいファイルを作る](https://github.com/Sumuji-zkdwn/primitive-lean/new/main)
- [ブラウザでファイルをアップロードする](https://github.com/Sumuji-zkdwn/primitive-lean/upload/main)

少量の原本ファイルやソース ZIP をこの対話に渡せば、GitHub 連携による分割登録も継続できます。ZIP 自体は Git 履歴に含めません。

## 登録方針

既存ソースの相対パスを保ち、小さい単位で追加して GitHub 側で確認します。
`.lake/` などの依存キャッシュ、ビルド生成物、認証情報、大きな ZIP は登録しません。
Lean のバージョンや依存 revision は取得した実ファイルを使い、推測で作成しません。

Kaggle 側で報告された約 5.2 MB / 585 ファイルとの照合は、原本取得後に行います。
