# ARC3 Explorer 0.1.1

公開の探索エージェント「Explore It Till You Solve It」を現在のARC SDKに接続した、
CPUで動くオフライン版です。比較用の自作モデル、記録モデル、ランダム版も含みます。
GPUと外部LLMのAPIキーは不要です。Python 3.12で動作確認しています。

## 起動

ZIPを展開して、`arc3-explorer-0.1.1` を作業ディレクトリにします。
Python仮想環境を作成・有効化した上で実行してください。

```bash
python -m pip install -r runtime/requirements.lock
python check_release.py --test
python run.py --version
python run.py --games vc33 --seeds 3 --budget 500 --environments /path/to/environment_files --output runs/first
```

`--environments` には公開ゲームのSDK環境ファイルがあるディレクトリを指定します。
環境ファイルはこの配布物に含めません。SDKのインストールだけではゲームは入りません。
既存のARC SDK環境ファイルを指定してください。
`--output` は未作成のディレクトリを指定します。
初期リセットもbudgetに含め、終了時には結果を `summary.json` に保存します。
行動・観測の記録は `*.jsonl.gz`、依存版とコードのハッシュは `metadata.json` です。

既存リポジトリ内で使う場合は `python experiments/arc3/run.py ...` と実行できます。
共通の研究用検証入口は `python -X utf8 tools/verify.py --arc3-only` です。

## 比較

```bash
python run.py --agents explore model hybrid structure random --games ls20 ft09 vc33 --seeds 3 --budget 500 --environments /path/to/environment_files --output runs/comparison
```

既存探索器は `explore`、自作の観測グラフ型モデルは `model`、
意味づけ前の記録モデルは `structure`、ランダム版は `random` です。
省略時は `explore` を実行します。既存探索器はACTION7の選択には対応しません。

## 確認済みの結果

公開3ゲーム、seed=3、初期リセットを含む最大500呼び出しの測定です。

| 方式 | ls20の突破レベル | ft09 | vc33 |
|---|---:|---:|---:|
| 既存探索器 explore | 0 | 0 | 2 |
| 自作モデル model | 1 | 1 | 1 |
| 記録モデル structure | 0 | 0 | 0 |
| random | 0 | 0 | 0 |

完全クリアはいずれも0です。生の測定結果と条件は `reports/` にあります。
既存探索器の例外後の回復も記録しており、測定中のKeyErrorからの回復は3・0・3回です。
競技への提出結果や未知ゲームの一般化成績ではありません。

## 出典と検証の範囲

既存探索器の出典は `dolphin-in-a-coma/arc-agi-3-just-explore`、固定コミットは
`c2d98318ecca38c8ee9fb49b5af159e51770bad7` です。
MIT LICENSEと導入ファイルのハッシュを `vendor/explore/` に同梱しています。
他の公開実装の調査は `EXISTING_AGENTS.md` にあります。

475定理の原本との接続はGitHubリポジトリ側にあり、このZIP単独ではLeanの再検証は行いません。
定理の自動適用や汎用的なARC攻略モデルの完成を主張する配布物ではありません。

## 配布物の再作成

この配布物は固定したファイル一覧から作成され、各ファイルを `MANIFEST.json` で照合できます。
ビルダーを使う場合は既存リポジトリ内で実行してください。

```bash
python experiments/arc3/make_release.py --output /path/to/arc3-explorer-0.1.1.zip
```

## 混成方策の比較

`--agents hybrid` はseed=3の公開比較に基づき、ls20/ft09で旧モデル、vc33で公開探索器を選びます。
未登録ゲームでは旧モデルにフォールバックします。これは公開3ゲームへの当てはめであり、
未知ゲームの汎化を示すものではありません。切替器は元のエージェントを変更せず、
`observe`、`after_reset`、`act`を委譲します。

`reports/hybrid-comparison.json` に既存実測値と今回の実行可否を分けて記録しています。
この作業環境には公開ゲーム環境ファイルがないため、混成方策と複数seedのゲーム実測は未実施です。
Kaggle公開環境を取得して比較する手順は [ACTIONS.md](ACTIONS.md) を参照してください。
