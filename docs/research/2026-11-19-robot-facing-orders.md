# 6方向の円弧歩行と方位帰還の必要十分条件

PR #159 の円弧を使い、任意の弧長 `h > 0` で、7歩の語 `-+++++-` の終点が複素数の零、累積回転角が π、最終接線の回転が −1 になることを Lean で証明した。これは6方向で最短の方位不一致であり、同じ長さのもう一語は左右を反転した `+-----+` である。

さらに、初期方位を 0 とし、各歩で ±2π/N だけ曲がる PR の模型で、**N ≥ 2 のとき、位置が閉じるすべての語が方位も閉じる必要十分条件は、N が奇数または2の冪であること**を証明した。

## PR の定義との対応

基準コミットは `7191629bea1c503bd9ebd165a160edb29645f293`。PR の `arcWord` は、実際の円弧の積分から得る状態 `arcState` を `join` でつなぐ。`true` が正の回転、`false` が負の回転である。方位の一致は `rotation (angle …) = 1` で表し、整数の `turns` には一周分の回転も残る。[RobotWalkArc](https://github.com/Sumuji-zkdwn/primitive-lean/blob/7191629bea1c503bd9ebd165a160edb29645f293/linear_input/lean_check/RobotWalkArc.inc)

| 現在の持ち上げた方位 | 文字 | 次の方位 | `edges` に加える整数 |
|---|---|---|---|
| j | `+` | j+1 | j |
| j | `-` | j−1 | j−1 |

どちらから同じ辺を通っても、正規化された弦の変位は同じになる。原点での最初の正の弦を D、ζ = exp(2πi/N) とし、`edgeResidues N 0 w` で辺 i が現れる回数を cᵢ とすると、`endpoint_eq_residue_counts` は終点を D ∑ᵢ cᵢζⁱ とする。N ≥ 2 かつ h > 0 では `chord_ne_zero` により D ≠ 0。

指定コミットの `RobotCyclotomic.sum_zero_iff_periodic` と `RobotWalkClassification.facing_of_closed` は、素数 q と N = q^(a+1) を仮定する。q = 2 も含む。正の閉路長の二系列を与える `closed_length_iff` には別途 `Odd q` がある。[RobotCyclotomic](https://github.com/Sumuji-zkdwn/primitive-lean/blob/7191629bea1c503bd9ebd165a160edb29645f293/linear_input/lean_check/RobotCyclotomic.inc) · [RobotWalkClassification](https://github.com/Sumuji-zkdwn/primitive-lean/blob/7191629bea1c503bd9ebd165a160edb29645f293/linear_input/lean_check/RobotWalkClassification.inc)

## 7歩の証明

| | 初期 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 文字 | | − | + | + | + | + | + | − |
| 方位の整数値 | 0 | −1 | 0 | 1 | 2 | 3 | 4 | 3 |
| 通過辺の整数値 | | −1 | −1 | 0 | 1 | 2 | 3 | 3 |
| 通過辺 mod 6 | | 5 | 5 | 0 | 1 | 2 | 3 | 3 |

辺の回数は順に (1,1,1,2,0,2)。対応する多項式は厳密に次のように分解する。

$$
1+X+X^2+2X^3+2X^5=(X^2-X+1)(1+2X+2X^2+2X^3).
$$

Lean 証明は mathlib の `Polynomial.cyclotomic_six` と PR の `step_root_primitive` から ζ²−ζ+1 = 0 を取り出す。任意の語について、変位を D(A+Bζ) と書く整数対 (A,B) を得る。

$$
A=c_0-c_2-c_3+c_5,\qquad B=c_1+c_2-c_4-c_5.
$$

Im(ζ) > 0 と D ≠ 0 より、終点が零であることと (A,B) = (0,0) が同値になる。この語では回転の差は 3 歩分で、3 · (2π/6) = π。複素回転は −1 である。

## 7歩以下の全探索

| 歩数 | 検査語数 | 位置が閉じた語 | 最終方位 mod 6 |
|---:|---:|---|---|
| 0 | 1 | 空語 | 0 |
| 1〜5 | 62 | 0件 | — |
| 6 | 64 | `++++++`、`------` | ともに 0 |
| 7 | 128 | `+-----+`、`-+++++-` | ともに 3 |

Lean では既存の `LinearInputCurveWordFinite.allWords` と `mem_allWords` から列挙の網羅性を導いた。整数対によるフィルターは元の幾何的終点と同値であり、列挙結果は `by decide` でカーネル計算している。最短性は `IsLeast` として証明した。

独立の `tools/check_robot_six.py` は Python 標準ライブラリだけで空語を含む255語を生成する。各語について、法6の方位から弦の整数対を足す計算と、整数上の通過辺から多項式を作り Φ₆ で筆算除算する計算を照合する。全語の件数、帰還語、最終方位を JSON で出力する。

## 一般の N に対する証明

**奇数 N**　各語の通過辺を非負指数に直した整数多項式を P とする。原点へ戻ると P(ζ) = 0 なので、ζ の整数上の最小多項式 Φₙ が P を割る。N が奇数なら、標数2の代数閉体にも位数がちょうど N の元 u があり、そこで P(u) = 0 となる。ある一歩が方位 j と j′ の間の辺 e を通るとき、標数2では (u+1)uᵉ = uʲ+uʲ′ が両方向で成立する。全歩を足すと途中の方位が2回ずつ現れて消え、最終の整数方位 t について

$$
(u+1)P(u)=1+u^t.
$$

従って uᵗ = 1、すなわち N ∣ t。もとの複素接線の向きも初期値へ戻る。この証明では N が素数冪である必要がない。

**2の冪**　PR の `facing_of_closed` を q = 2 で適用する。

**奇数因子 m > 1 を持つ偶数**　N = 2md、m = 2k+1、d ≥ 1 と書く。F を d 回の正回転、B を d 回の負回転とし、V = FFBF と置く。連結と反復で作る語

$$
W = F^m V^k F^{m+1}
$$

は原点へ戻り、接線は反対を向く。x = ζᵈ は位数 2m、xᵐ = −1。F の変位を E とすると、B の変位は x⁻¹E、V の変位は (1+3x)E、V の回転は x² である。Gₙ(x) = 1+x+⋯+xⁿ⁻¹ と書いたとき、W の変位は次の係数と E の積になる。

$$
G_m(x)+x^m\bigl(G_k(x^2)(1+3x)+(x^2)^kG_{m+1}(x)\bigr)=0 .
$$

等比和の公式、(x²)ᵏ = −x⁻¹、xᵐ⁺¹ = −x から消去できる。W の正味の回転は 3md 歩分で、mod N では N/2 になる。この構成は反例の存在を全対象位数で保証する。N = 6 の最短7歩は別途、上の全探索で決定した。

一般の N に対する正の閉路長の分類と、N ≠ 6 における反例の最短長は、この追加で証明していない。

## Lean 宣言と検証

| 内容 | 宣言 |
|---|---|
| 7歩の整数トレース、終点・角度・接線 | `RobotSix.witness_trace`、`RobotSix.witness_closes_reversed` |
| N = 6 の全語に対する整数対と幾何的終点の同値 | `RobotSix.endpoint_formula`、`RobotSix.endpoint_zero_iff` |
| 7歩以下の完全な帰還リスト、反例2語、最短性 | `RobotSix.short_returns_exact`、`RobotSix.short_counterexamples_iff`、`RobotSix.least_counterexample_length` |
| 一般の N での整除判定、辺の回数が周期的な場合の十分条件 | `RobotSix.facing_iff_dvd`、`RobotSix.facing_of_periodic_counts` |
| 位置が閉じる場合の円分多項式の整除性、奇数位数の方位帰還 | `RobotFacingOdd.cyclotomic_dvd_of_closed`、`RobotFacingOdd.facing_of_closed_odd` |
| 偶数位数の反例族、位数による必要十分条件 | `RobotFacingOrders.even_factor_reversal`、`RobotFacingOrders.facing_for_all_closed_iff` |

環境は Lean 4.36.0-rc2、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`。独立検証した3個の Lean 原稿は、冒頭の import を組み立て側に移して登録した。全原稿を連結したときにも読めるよう、`short_returns_exact` のリスト先頭にある空語を `List.nil` と明記した。各断片の Git 上の初出は `3321562f80de5effd076ffb5a0c5fbd9ed287aff` であり、独立原稿の SHA-256 も統合台帳に記録している。[6方向の有限証明](../../linear_input/lean_check/RobotSix.inc) · [奇数位数の証明](../../linear_input/lean_check/RobotFacingOdd.inc) · [偶数の反例族と必要十分条件](../../linear_input/lean_check/RobotFacingOrders.inc)

リポジトリのルートで次を実行する。最初のコマンドは255語を独立に検算する。二つ目は現在のチェックアウトの8個の先行断片から親モジュールを組み立て、追加3モジュールを `--trust=0` で型検査する。公開14定理の公理監査と `leanchecker` による3モジュールのカーネル再検査も行う。三つ目は他の研究原稿と一緒に統合証明を検証する。初回の環境準備は `lean` ディレクトリで `lake exe cache get` を実行する。

```sh
python -B tools/check_robot_six.py
python -B tools/verify_robot_facing.py
python -B -X utf8 tools/verify.py --proof-only
```
