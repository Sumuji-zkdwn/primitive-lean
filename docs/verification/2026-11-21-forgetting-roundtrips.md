# 記憶・理解・忘却：宣言対応と検証記録

2026年11月21日。[研究ノート](../research/2026-11-21-forgetting-roundtrips.md)のうち、関係の三段合成と既存の多項式写像 `E` への接続を形式化する。

基点は `8ed4c9347609ff350f947da7e44101abcd993ed9`。既存の `SiphonPolynomialE`、`ElasticaObservationQuotient`、`SiphonPredictiveQuotient` の定義を変更せず、新規 [ForgettingRoundTrips.lean](../../lean/Research/ForgettingRoundTrips.lean) から利用する。名前空間は `Elastica.ForgettingRoundTrips`。

## 1. 形式化の範囲

`Rel X Y := X → Y → Prop` は、空集合も許す集合値写像としての関係である。`comp r s` は先に `s`、次に `r` を作用させ、中間候補に関して存在量化する。`graph f` は関数のグラフ、`fullInverse f` は全逆像関係、`FiberSupported f g` は各ラベルの候補が非空で、全候補がそのラベルへ再符号化される条件である。

一般の全射 `f` と任意の復号関係 `g` について、第一三段式 `fgf = f`、`fg = id`、`FiberSupported f g` が同値であり、そこから第二三段式 `gfg = g` が従う。全逆像関係を使う場合は、全射を仮定せず両三段式が成立する。

研究ノートの数学的な商 `q : ℝ² → ℝ × [0,∞)` と、既存Leanの `signature : ℝ² → ℝ × ℝ` は余域が異なる。Leanでは第二座標が負のラベルの逆像は空であり、`signature` が `ℝ × ℝ` へ全射だとは主張しない。`signature_inverse_roundtrips` は全射不要の全逆像定理を使う。

## 2. 本文とLean宣言の対応

宣言名の名前空間は、すべて `Elastica.ForgettingRoundTrips`。

| 研究ノート | 宣言 | 証明する内容・仮定 |
|---|---|---|
| §1.1 | `comp_assoc` | 関係合成の結合則。 |
| §1.1–1.2 | `graph_decoder_iff_supported` | `fg = id` と非空・ファイバー内復号の同値。 |
| §1.1–1.2 | `first_roundtrip_iff_identity`, `first_roundtrip_iff_supported` | 全射 `f` に対する第一三段式の必要十分条件。 |
| §1.1 | `second_roundtrip_of_identity`, `second_roundtrip_of_first` | 第一条件から第二三段式が従う。後者のみ全射を仮定する。 |
| §1.2、§2.3 | `saturation_idempotent_of_identity` | `fg = id` の下で関係 `gf` が冪等。確率核の定理ではない。 |
| §1.2 | `full_inverse_first_roundtrip`, `full_inverse_second_roundtrip` | 全逆像を復号関係に使う両三段式。全射不要。 |
| §1.2 | `full_inverse_saturation_iff`, `full_inverse_contains_original`, `full_inverse_saturation_idempotent` | 全逆像への往復は同じラベルを持つ状態間の関係であり、元状態を含み、冪等。集合上の閉包作用素の単調性は今回独立には形式化しない。 |
| §1.2 | `full_inverse_iff_contains_all` | ファイバー内復号の下で、全元状態を候補に残すことと全逆像であることの同値。 |
| §1.2、§2 | `representative_consistent`, `representative_roundtrips`, `representative_omits_original` | `Bool → Unit` と一代表の復号で、両三段式が成立しても元状態を候補から落とせる。本文の4点例と同じ論理を2点例で証明。 |
| §1.2 | `second_only_counterexample` | `Bool × Bool → Bool` に非空復号関係を組み合わせ、第二三段式だけが成立する反例。 |
| §3.1–3.2 | `signature_inverse_roundtrips`, `signature_inverse_contains_mirror` | 既存 `signature` の全逆像で両三段式が成立し、符号反転状態も候補に入る。 |
| §3.2 | `signature_has_distinct_pair`, `no_full_state_decoder` | 異なる二状態が同じ署名を持つため、署名だけから全状態を常に一意復元する関数は存在しない。数値的な誤差下界は別の手証明。 |
| §3.3 | `fresh_does_not_descend` | 追加操作 `R = freshStep ()` の署名更新は旧署名のみの関数として表せない。 |
| §3.3 | `sequential_invariant_reconstruction`, `sequentialSignature_injective` | 一つの保持状態へ `E,R,E` を順に作用させた三読出しから不変量と初期状態を復元する。観測自体による状態更新は仮定していない。 |

明示的な新規 `theorem` は24個。全24宣言に `#print axioms` を付けるほか、検証器は新規モジュールとローカル依存の所有する全定理宣言を、生成された宣言も含めて公理監査する。

## 3. 有限検算の範囲

[tools/forgetting_roundtrips.py](../../tools/forgetting_roundtrips.py) と [tests/test_forgetting_roundtrips.py](../../tests/test_forgetting_roundtrips.py) は標準ライブラリだけを使用する。整数と `Fraction` による厳密計算を中心とし、表示用のエントロピーのみ浮動小数点を使う。検算条件は `python -O` でも有効な明示的検査関数で評価する。

| 検算 | 実際に検査する有限範囲と結果 |
|---|---|
| 関係 | 3点から2点への全射6個 × 復号関係64個 = 384組。第一三段式18組、第二三段式174組、両方18組。 |
| 任意の関係 | 2点×2点の全16関係。逆関係との三段等号と長方形条件が一致し、成立12個。 |
| 確率核 | 分母3の分布から構成した600組。第一三段TV誤差がファイバー外確率 `δ`、第二誤差が `δ` 以下。7点一様分布の例では周辺TV誤差0、個体復元率1/7。 |
| 実数系の初期条件 | 15初期条件から署名9種、追加観測15種。`E` の像の8点が初期集合外に出る。閉じた15状態系ではない。 |
| 閉じた有限体模型 | `𝔽₅²` の全25状態上で `E,R` が置換。署名15種、追加観測25種。復元式と半共役を全点検査。 |
| 接続の商 | 最大次数2→4、距離3→2。商の短い経路を元のグラフの同長経路として持ち上げられない。 |
| relay | 現在入力が同じでもマスクが違う二履歴と、異なる履歴でも同じマスクになる例を検査。全履歴を保存する模型ではない。 |

600個の確率核を調べることは、一般の確率核のTV評価の機械証明ではない。TV評価は研究ノートの手証明を参照する。神経生理、費用、流体繊維の実験装置との対応もLean定理ではない。

## 4. 再実行

Lean `leanprover/lean4:v4.36.0-rc2` と、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2` を既存のファイルで固定する。依存バージョンを変更しない。

Pythonだけの検算：

```bash
python3 -B tools/forgetting_roundtrips.py
python3 -B -m unittest discover -s tests -p test_forgetting_roundtrips.py -v
```

Lean・Pythonを合わせる統一入口：

```bash
python3 -B tools/verify.py --forgetting-roundtrips-only
```

専用入口はPythonの検算とテスト、`Elastica.Geometry` の前提ビルド、既存の `verify_toolchain_modules.run` による新規モジュールとローカル依存のソースコンパイル・公理監査を実行する。Leanは `--trust=0` を指定し、警告・禁止された証明迂回・標準3公理以外の依存を拒否する。検証時のコミット・ソースハッシュ・toolchain・manifestを結果に記録する。

全体の `tools/verify.py --integration-only` も同じ専用入口を呼ぶ。既存の全standaloneモジュール検証は新規ファイルを追跡対象に含める。新規Leanファイルをローカル検証するときは、先にGitの追跡対象へ追加する必要がある。

CIは [.github/workflows/forgetting-roundtrips.yml](../../.github/workflows/forgetting-roundtrips.yml)。PRのhead SHAをcheckoutし、固定Lean環境で専用入口を実行して検証ログをartifactとして保存する。

## 5. 実行記録

初回push前のローカル検査：

- `python3 -m unittest discover -s tests -p test_forgetting_roundtrips.py -v`：6件成功。
- `python3 -O tools/forgetting_roundtrips.py`：全有限検算成功。
- ローカル環境にLean/Lake実行ファイルがないため、この段階ではLeanのコンパイル成功を主張しない。専用CIの実行結果をここへ追記する。

既存の依存グラフworkflowは `docs/dependency/generated/` のみを更新するbot commitをPRブランチへ追加することがある。証明ソースを検証したコミットと、その生成物更新後のheadを区別する。
