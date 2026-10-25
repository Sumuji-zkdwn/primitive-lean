# Kaggle Notebookとの対応

## 環境準備を1セルで実行する版

`STATE is not defined` が出る場合は、初期化セルが現在のカーネルで実行されていません。[環境準備・1セル版](../notebooks/primitive_lean_setup_one_cell.ipynb)なら、初期化、原本照合、環境準備を一つのセルで実行できます。同じ原本ZIPをInputに用意し、InternetをOnにして、唯一のコードセルの▶を押してください。初期設定は `RUN_SETUP=True`、`RUN_PROOFS=False` です。

この版は、空のPython名前空間からの初期化・117ファイルの照合・結果保存をローカルで確認しました（ネットワーク環境準備を無効化した確認）。Kaggleでの環境準備成功やLean検査成功を確認したものではありません。

再生成は `python scripts/build_kaggle_notebook.py --source-ref 2e058f2d76e7c7d1fb0f811bcb26a990c47b10d9 --setup-one-cell` です。

[primitive_lean_kaggle.ipynb](../notebooks/primitive_lean_kaggle.ipynb)をKaggleのImport Notebookで読み込んでください。CPUで使うNotebookです。GPUは不要です。

## 最初の実行

1. 同じ `archive.zip` をKaggleのInputに追加するか、元の原本フォルダがある環境でNotebookのセルを実行します。
2. 設定セルは最初のまま `Run All`。自動検出できない場合だけ `SOURCE_PATH` にZIPまたは原本フォルダのパスを指定します。
3. `source: passed`、`setup: not_run`、`proofs: not_run` と、対応コミット・117ファイルの照合結果・結果ZIPを確認します。

別Notebookや別セッションの `/kaggle/working` に原本がある場合、そのパスが現在のセッションにも存在するか確認してください。見つからなければ原本ZIPをInputに追加します。元Notebookをそのまま使う場合は、このNotebookの6つのコードセルを同じ順序でコピーしても使えます。

初期状態のファイル照合にはInternetもGitHubトークンも不要です。GitHubから直接読み込む場合だけ `SOURCE_MODE="github"` とし、Kaggle Secretsで `GITHUB_TOKEN` をNotebookに許可します。対象リポジトリのContents読み取り権限だけを使います。トークンをセルの本文へ貼り付けません。

## 次の段階

| 目的 | 設定セル | 実行内容 |
|---|---|---|
| ファイルの対応確認 | 初期設定のまま | 原本を検出、固定ハッシュを照合、アダプターを適用、結果保存 |
| Lean環境を用意 | `RUN_SETUP=True`、Internet On | 原本のLean版・mathlib revisionを保持、依存キャッシュ取得とrevision照合 |
| 実ビルド・公理監査 | `RUN_SETUP=True`、`RUN_PROOFS=True` | `python -X utf8 tools/verify.py --proof-only` |

各段階の成否は別々に記録します。環境準備やファイル照合の成功を証明検査の成功として表示しません。初回の依存取得には時間がかかります。Kaggleの作業フォルダに使える同じ依存キャッシュがあれば再利用します。キャッシュのrevisionは検査します。

`REBUILD=True` はこのプロジェクトの `.lake/build` だけを再作成する設定です。依存キャッシュや原本ZIPを削除しません。

## GitHubと一致させる範囲

初期版が対応するソースコミットは `2e058f2d76e7c7d1fb0f811bcb26a990c47b10d9` です。
Notebookはそのコミットの検査対象ソースの部分集合を扱い、リポジトリ全体をcloneしたとは記録しません。

- 原本116ファイルのパスとSHA-256を照合します。
- 原本ZIPにある旧 `tools/verify.py` を受け入れ、Notebook同梱の固定版に置き換えます。`tools/proof_only.py` も配置します。
- 結果の117ファイルを再照合します。65個の証明原稿と元の個別検証器は変更しません。
- 実検査の直前・直後にも同じハッシュを照合し、途中で書き換わったソースを固定コミットの合格とは扱いません。
- `notebook_run.json` に対応コミット・全対象ハッシュ・実行段階を記録します。

ソースを更新した場合、古いNotebookはそのまま最新版と一致するとは限りません。更新したcheckoutで次を実行して固定版を再生成します。

```bash
python scripts/build_kaggle_notebook.py --source-ref <アダプターを含むソースコミットの40桁SHA>
```

## 証明検査と保存監査の違い

新しい `--proof-only` は元の統合入口から、既存の `linear_input/verify_lean.py` と `tools/verify_main_result.py` を順に呼びます。今回生成されたレポート・終了コードを使います。前回の成功レポートは退避してから実行するため、その流用による合格を防ぎます。

このモードは、欠けている `archive/before_unification_2026-10-20.zip` による過去版保存監査を実行しません。レポートに `historical_preservation: not_checked` と明記します。元の全体検証・`--lean-only` は従来どおり別に残ります。過去ZIP、描画用vendor、配送用資材の不足は、証明検査とは別の条件です。

`--proof-only` の `passed` は、その実行のLeanライブラリビルドとjoint/supplementの証明・公理検査の範囲だけを指します。

## 結果の受け渡し

Notebookの最後に表示される結果ZIPを保存して、この対話へ添付できます。失敗時にも今回のログ・段階別状態を保存します。古い成功記録、依存キャッシュ、ソースZIP、認証情報は結果ZIPに含めません。NotebookからGitHubへの書き戻しやKaggleコンペへの提出は行いません。

## 今回確認した範囲

- 添付原本ZIPからの取り込み、117ファイルの再照合、未実行状態の区別、結果ZIP生成をローカルで実行しました。
- Notebookの全コードセルを構文検査しました。
- 古い成功レポートの拒否、非零終了コードの拒否、追補失敗時の扱い、途中のソース変更の拒否、失敗ログの保存について5テストが成功しました。
- Kaggle実機の操作、ネットワーク経由の環境準備、Leanコンパイルはまだ実行していません。

## 参照

- [Kaggle公式のSecretsクライアント](https://github.com/Kaggle/docker-python/blob/main/patches/kaggle_secrets.py)
- [Lean公式の環境構築手順](https://lean-lang.org/install/manual/)
- [固定したElanインストーラー](https://github.com/leanprover/elan/blob/9605b24b08cf68b78dce0014b6fa01be1f8e2cee/elan-init.sh)
