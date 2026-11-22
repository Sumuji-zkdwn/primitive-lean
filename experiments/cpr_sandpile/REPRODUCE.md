# 再実行と検証範囲

解析日：2026-11-21（日本時間）。リポジトリへの追加・再実行確認：2026-11-22（日本時間）。

このフォルダは、保存済みの匿名化された派生データから、Coop／Comp比較・固定90採取・99回の配置対照・図を再計算する数値解析です。実験の採取記録を入力にした模型の検算であり、Leanの証明結果を追加するものではありません。

## 環境

検証に用いた環境はPython 3.12.14、NumPy 2.3.5、Matplotlib 3.10.8、Pillow 13.0.0です。Python依存は[requirements.txt](requirements.txt)に固定しています。リポジトリのLean検証環境とは独立した仮想環境を使えます。

リポジトリのルートで実行します。

```bash
python3.12 -m venv experiments/cpr_sandpile/.venv
. experiments/cpr_sandpile/.venv/bin/activate
python -m pip install -r experiments/cpr_sandpile/requirements.txt
```

図の再描画には、Linux上の次の日本語フォントが必要です。Debian／Ubuntuでは`fonts-noto-cjk`パッケージが提供します。

```text
/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc
SHA256 b76b0433203017ca80401b2ee0dd69350349871c4b19d504c34dbdd80541690a
```

検証器は上記SHA256と一致するフォントを要求します。フォントの版が異なる場合、統計量が同じでも画像のバイト列は変わり得ます。この掲載時の再実行は上記ライブラリがインストール済みの環境で行いました。新規の環境へのインストール試験とは区別します。

## 標準の再現確認

既存の統合入口から実行します。

```bash
python -B -X utf8 tools/verify.py --cpr-sandpile-only
```

結果は`verification/cpr-sandpile.json`へ出力します。[掲載時の検証記録](verification.json)は別に保存しています。Leanのビルドや原ZIPからの読み直しは、このモードには含みません。

検証器は元パッケージの521ファイルのSHA256を確認し、一時ディレクトリにコピーして次の順で再実行します。公開済みの結果や元manifestを上書きしません。

1. 主5指標を再集計し、組単位bootstrapと全184,756通りの条件ラベル置換を再計算する。
2. 全157ラウンドの最初90採取、各99回の位置置換を再計算する。
3. 追加2指標と、主5指標を含む7指標のHolm補正を再計算する。
4. 独立の照合コードで、対照集計・全7指標の置換p値・Holm補正を照合する。
5. 4パネルの比較図を再描画する。

CSV・JSONの数値、314本の対照NPZの配列を保存済み結果と照合します。計算時間の記録は再実行ごとに変わります。検証器のコードと詳細な照合対象は[verify_reproduction.py](verify_reproduction.py)を参照してください。既存解析の一部が`assert`で検算するため、検証器はPythonの最適化モード`-O`を拒否します。

## 個別に再実行する場合

以下は結果ファイルをその場で更新するコマンドです。元の掲載値を保持する場合はコピー先で実行します。

```bash
cd experiments/cpr_sandpile
python -B -X utf8 cpr_coop_comp/analyze_conditions.py
python -B -X utf8 cpr_coop_comp/controls/analyze_controls.py
python -B -X utf8 cpr_coop_comp/analyze_controls.py
python -B -X utf8 cpr_coop_comp/audit/check_controls.py
python -B -X utf8 cpr_coop_comp/render_comparison.py
```

元の[package_manifest.json](cpr_coop_comp/package_manifest.json)は2026-11-21に保存した配布物の記録です。元ファイルを変更すると、このmanifestによる一致確認は失敗します。追加した入口・説明・検証器は元manifestの521件には含まれません。

## 入力と再実行できる範囲

| 範囲 | 同梱入力 | 原ZIPの要否 |
|---|---|---|
| 主比較 | ASMの`summary.csv`、実験の`round_sand.csv`、条件・品質CSV | 不要 |
| 固定90採取・99配置対照 | ASMの`events.csv`、`summary.csv`、2人条件157本のNPZ | 不要 |
| 対照の統計・7指標Holm | 主比較と対照CSV、保存済み匿名監査JSON | 不要 |
| 独立の対照照合 | 対照CSV、匿名の組別指標、最終比較JSON | 不要 |
| 図 | 主比較と対照の組別CSV | 不要 |
| 参加者表を使う独立監査・実験設計の再監査 | コードと保存済み監査結果を同梱 | 外部の2人条件ZIPが必要 |
| 原ログから旧ASM入力をすべて作り直す | 参照用の旧生成コードを同梱 | 元ZIPと未同梱の旧解析中間データが必要 |

標準の再現確認は、元の参加者表の読み直しや原ログからの入力再抽出を含みません。参加者略号から作った匿名の感度分析用連結成分は、保存済み監査JSONを入力として使います。同じ略号が同じ人物かは未確定です。

最終の7指標Holm補正値は[control_comparison.json](cpr_coop_comp/control_comparison.json)の`holm_seven`です。[condition_comparison.csv](cpr_coop_comp/condition_comparison.csv)にある`holm_p_five_metrics`は、主5指標のみを補正した途中段階の値です。

## 原資料を保有している場合の任意監査

元の2人条件ZIPを、このフォルダ内の`cpr_empirical_sources/02_expCPR_2player(1).zip`へ配置します。期待するSHA256は次です。

```text
536996e6a977de63fcb82e9a0678c51cded6cd3bd2e962fbfeb00701dbcb9896
```

実際の氏名・略号を含む元資料は公開パッケージに含まれず、配置先はGitの追跡から除外しています。

```bash
cd experiments/cpr_sandpile
python -m pip install -r requirements-raw-audit.txt
python -B -X utf8 cpr_coop_comp/audit/independent_compare.py
python -B -X utf8 cpr_coop_comp/design/audit_design_and_describe.py
```

旧`cpr_redefinition/harvest_asm/analyze_harvest_asm.py`の`main()`による全生成には、さらに旧`cpr_transport/metadata.json`、`cpr_patterns/empirical/`、一部の`cpr_patterns_v2/temporal/trials/`と1人条件の元ZIPも必要です。この公開パッケージだけで全生成できる手順には含めていません。

## 出典と同梱範囲

復元・掲載した元配布物は`cpr_coop_comp_2026-11-21.zip`、8,039,784 bytes、522ファイルです。保存済み版との一致を次のSHA256で確認しました。ZIP自体はGit履歴に含めていません。

```text
94607ef8a547c93b6cf3833504f1ec238c99f92a675446cf03bce57882e11c97
```

同梱データには、匿名の組・ラウンドID、実験内の相対時刻、採取座標、盤面配列、モデル出力、集計値が含まれます。元ZIP、元の参加者表、実際の参加者略号、氏名は含まれません。一部の先行解析CSVには1人条件の匿名行も残っていますが、今回の比較コードは2人条件の有効157ラウンドを選択します。
