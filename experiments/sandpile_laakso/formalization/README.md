# 亜Laakso空間の形式化

元の問い、モデルを決定する観測仕様、二つの指数判定とその証明は[構成定理](FORMALIZATION.md)にまとめた。統合されたLeanの入口は [Main.lean](Main.lean) の `SingleSquare.single_square_realization` である。

2026年11月21日のクリーンビルドでは、9モジュール・82宣言の公理依存を確認し、二つの実験群は合計8件すべて成功した。`SingleSquare.raw_failure` は標準空間のPIと正則性を入力とせずに未変換側の不成立を証明する。主定理の公理依存は `Classical.choice`、`Quot.sound`、`propext`。実行後に入力20ファイルのSHA-256も再照合した。[宣言別の検証記録](verification.json)

| 構成の段階 | 形式化した内容 |
|---|---|
| [正方格子の力学](SquareClock.lean) | 合法発火と安定化、最小戻り周期、桁反転、角での正逆回転、全角度・全ラベルへの到達性 |
| [非カントール層と商](ObservedQuotient.lean) | 円周とビット列の積の非カントール性、商の同型、有限道の費用とその逆極限距離、球平均・上勾配を含むPIと正則性の移送 |
| [標本の確率法則](HeightLaw.lean) | 閉区間の一様測度、公平なビット、角度の積測度と、校正後に中央帯や両端へ割り当てられる質量 |
| [未変換の道距離](RawGeometry.lean) | ゲートを訪れる高さ区間からの距離、高さ射影の1-Lipschitz性、直径の一様上界 |
| [中央帯の上勾配](CutObstruction.lean)・[PIが破れる証明](RawFailure.lean) | リプシッツ経路の帯内滞在時間によるランプの変動評価、左右の質量と帯の質量によるPIの反証 |
| [WFSの積分](WeightedPI.lean) | 実指数全域の区間質量・振動・勾配の積分、球の比較から重み付きPIへの移送、二つの指数条件の交わり |
| [円周との積](ProductPI.lean) | 確率測度での平均振動のFubini評価、拡大球を用いる積のPI評価 |
| [統合定理](Main.lean) | 実際の物理ゲート、非カントール性、同一の測度と読出し上の未変換PIの反証・変換後PI・正則性を同じ正の実指数について結合 |

変換後のPIと正則性には標準の「三進Laakso空間 × 円周」の二性質を定理の引数として用いる。これらはLaaksoのPI定理・標準球の評価と円周での積から証明される。未変換時の不成立は具体的な試験関数から導く。文献定理、紙上で格子極限に照合したこと、Leanが述べる命題の対応は[構成定理の第3・5節](FORMALIZATION.md)を参照されたい。

## 再実行

Git、Python と elan（`elan` と `lake`）が使える環境で、初回はリポジトリのルートから次を実行する。`experiments/mobius_430` のマニフェストが指定する mathlib とそのコンパイル済み依存を準備する。

```powershell
python -m pip install -r requirements.txt
elan toolchain install leanprover/lean4:v4.35.0
elan toolchain install leanprover/lean4:v4.30.0-rc2
Push-Location experiments/mobius_430
lake exe cache get
Pop-Location
```

リポジトリの共通入口から砂山だけを検査するには、次を実行する。

```powershell
python -B -X utf8 tools/verify.py --sandpile-laakso-only
```

砂山の検証器を直接実行する場合も、同じリポジトリのルートから起動できる。

```powershell
python -B experiments/sandpile_laakso/formalization/verify.py
```

同じ mathlib リビジョンの依存キャッシュを持つ別の Lake プロジェクトを用意した場合は、`--mathlib-root <prepared checkout>` でそのディレクトリを指定する。検証器は Lean・mathlib の版と mathlib のコミットを照合し、各ソースをカーネル検査してから二つの Python 実験群を再実行する。

単独の砂山力学はLean 4.35.0、mathlibを含む統合定理はLean 4.30.0-rc2で検証した。mathlibは `5450b53e5ddc75d46418fabb605edbf36bd0beb6` に固定した。[検証スクリプト](verify.py) · [ソースハッシュ・宣言別の公理依存・実行結果](verification.json)

同一の二粒操作と戻りを実際に安定化した小格子で試すには、次のコマンドだけでよい。

```powershell
python -B -m unittest discover -s experiments/sandpile_laakso/formalization -p test_single_square.py
```

2×2格子では全再帰状態、8×8格子では全観測値の代表を使う。さらに有限段の各頂点対で、最短路探索と積距離の公式を照合する。以前の五つの回帰検査も[統合検証](verification.json)に含む。[有限検査のソース](test_single_square.py)
