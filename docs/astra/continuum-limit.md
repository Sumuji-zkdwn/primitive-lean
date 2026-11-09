# 空間モードに一様な評価と非粘性 Maxwell PDE への極限

この段階では、共通の解析的初期値クラスについて、実際の Fourier–Galerkin 系から、構成した非粘性 Kerr–Maxwell 方程式の解への極限を接続する。初期値と時間区間を入力し、未知の PDE 解や将来の Fourier 尾部評価を入力仮定にしない。原本は従来と同じ `kerr-koopman-lean` のコミット `51a49be2e8f8b440c891240b574fdf97e08b9e84` に固定する。

対象は周期 2π の一次元系

```text
D = E + E³/3,     D_t = −H_x,     H_t = −E_x
```

である。物理時間のまま扱い、粘性項は追加しない。この証明は、任意の滑らかな周期初期値や衝撃波後の解までを覆うものではない。

## 初期値だけに課す条件

`AnalyticFields.Data` に入る条件は次の四つである。

- 実時間の終端 `T` が `0 ≤ T ≤ 1/5`。
- 左右の枝を表す重み付き Fourier 係数 `initial : ℓ¹(ℤ, ℂ × ℂ)`。
- この共通の空間のノルムが `‖initial‖ ≤ 57/250`。
- 実数の場を復元するための共役対称性。

係数の `ℂ × ℂ` には二成分の最大ノルムを使い、その ℓ¹ 和を取る。復元した物理場の `L²` 二成分ノルムとは区別する。

初期の解析幅は `1/2`、時間に依存する幅は `ρ(t)=1/2−t ≥ 3/10` である。係数に織り込んだ指数重みを復元時に取り除く。背景場は `D=4/3, E=1, H=3/10`。左右両方向の成分を許し、初期波形ごとに別の座標系を組み立てる必要はない。単なる滑らかさから、この指数重み付き小球の条件が従うとは主張しない。

`AnalyticAssembly` は具体的な畳み込み、自由伝播、Duhamel 写像を構成し、`AnalyticFixedPoint` が収縮を使って解を得る。`AnalyticTransport` は全 Fourier 級数の微分を正当化し、`AnalyticPDE.maxwell_equations` が上の PDE を導く。PDE の微分等式は **`0<t<T`**、初期値到達・連続性・近似誤差は **`0≤t≤T`** で扱う。

## 有限系を実際の空間微分へ接続する

`P_N` は周波数 `|k|≤N` の実直交 Fourier 射影、`Q_N` はその切断空間上の空間微分とする。有限系の材料作用は

```text
G_N(D_N) = P_N(g(D_N)),     g(D) = 2 sinh(asinh(3D/2)/3)
D_N' = −Q_N H_N,           H_N' = −Q_N G_N(D_N)
```

である。ここでは、空間の各点で材料逆関数を作用させてから Fourier 射影する。前段の `AstraFiniteFlow` のように有限座標へ成分ごとに `g` を適用した系へ Fourier 行列を渡すだけでは、この非線形射影系にならない。

`RealGalerkin.projectedMaterial` と `GalerkinFlow` が正しい射影・微分・材料作用を構成し、既存の `HilbertShear` と同じ二段の部分流へ接続する。初期の `D,H` を射影し、各段で

```text
D₊ = D − h Q_N H
H₊ = H − h Q_N P_N(g(D₊))
```

を実行する。最後に `E=g(D)` を復元する。Lean の定義で使う厳密な非線形射影を、有限精度の求積・丸めで評価した際の誤差は、この定理とは別である。

## モード数によらない空間誤差

`z₀` を初期の `D,H`、`u(t)=(E(t),H(t))` を構成した連続体の場とする。`Φ_N` は上の正しい Galerkin 系の流れである。`AnalyticGalerkinCertificate.control` が、古典解・初期一致・正則性・尾部に関する条件を実際の構成からすべて埋める。

`actual_spatial_error` は、すべての `N` と `t∈[0,T]` について

```text
‖decode_N(Φ_N(t, encode_N(z₀))) − u(t)‖
  ≤ 2 exp(−3(N+1)/20)
```

を証明する。ノルムは Haar 正規化された実 `L²` の二成分ノルムであり、前係数 **2** と時間区間は `N` に依存しない。相対エネルギーの比較は `exp(4t)` を使い、空間微分の作用素ノルムによる `exp(Nt)` の増大をこの空間評価へ持ち込まない。

ただし、切断空間上の空間微分そのものが `N` 一様な有界作用素になったわけではない。周波数 `N` の sine/cosine 成分には `N` 倍で作用する。証明は解析幅と Fourier 尾部、相対エネルギーを使って、特定の共通初期値クラスからの解を制御する。

## 分割反復と空間切断の同時極限

分割数 `n>0` の `finiteFormula(p,N,n,t)` には、閉時間区間で

```text
‖finiteFormula(p,N,n,t) − u(t)‖
  ≤ 2 exp(−3(N+1)/20) + C_N(t, ‖z₀‖)/n
C_N(T,r) = (3/2) N² T² r exp(NT)
```

という評価がある。**この時間分割の定数 `C_N` は `N` 一様ではない。** そこで、初期値と終端時刻だけから、区間全体に共通の分割数

```text
n_N = max(N+1, ceil(C_N(T, ‖z₀‖) (N+1)))
```

を定める。`uniform_error` はすべての `t∈[0,T]` で

```text
‖finiteFormula(p,N,n_N,t) − u(t)‖
  ≤ 2 exp(−3(N+1)/20) + 1/(N+1)
```

を与える。右辺は `t` と初期波形に依存せず、`N→∞` でゼロになる。分割数の選択には `‖z₀‖` を使う。同じ `n_N` を区間の全時刻に使うため、これは時刻ごとに反復数を選ぶだけの点ごとの収束より強い。

`finiteFormula_tendstoUniformlyOn` が、物理時間の閉区間に一様な、復元後の実 `L²` 場への収束を証明する。小さい誤差を得るために `n_N` が非常に大きくなり得るので、この保証を効率の良い有限回の閉形式と読み替えない。

## 空でない共通入力クラス

`ExplicitAnalyticInput` が重み付き初期値のノルム条件と共役対称性を証明し、`AnalyticExample` が同じ構成で

```text
D₀(x) = 4/3 + (1/25) cos(x)
H₀(x) = 3/10 + (3/100) sin(x)
```

という非定数の周期混合波を復元する。これは数値実験で誤差が小さかったという主張ではなく、一般構成に入る具体的初期値を Lean で同定した例である。

## 出典・証明の役割・再実行

原本の依存閉包を保存し、`import` 行だけを除いた追補を共通 `MainResult` へ組み込む。原本コピーとこのリポジトリで書いた最終接続 `AstraContinuumLimit.inc` は台帳上で区別する。入れ子の namespace、複数原稿で共有する namespace、構造体の宣言も追跡し、原稿の完全修飾名と Lean 環境の実宣言を照合する。

追加の原本57原稿には658定理・890名前付き宣言があり、構造体4件と名前付き instance 5件も宣言数に含める。新規接続は23定理・37名前付き宣言で、別に登録する。今回の増分は58原稿・681定理・927名前付き宣言、Astra累計は74原稿・891定理・1,190名前付き宣言となる。既存の原始29定理の再利用と、構造体から生成される補助宣言はこの追加数へ加算しない。生成宣言は別の環境全体の公理監査で検査する。

新規接続の `certificate` は、物性則、初期値到達、実PDE、空間誤差、有限公式の誤差と同時極限を、同じ入力・同じ場についてまとめる。`solution_restoration` と `scalar_restoration` が、微分したスカラー場と極限の `L²` 場を対応させる。`spatial_tendsto_uniformly` は厳密 Galerkin 流れの空間極限、`approximation_tendsto_uniformly` は分割反復も含む極限である。`mixed_certificate` と `mixed_initial_nonconstant` は、具体的混合波がこの接続の非定数な実例であることを証明する。

- [原本・変換・新規接続の台帳](manifest.json)
- [最終接続](../../linear_input/lean_check/AstraContinuumLimit.inc)
- [この段階の検証記録](verification-continuum.md)
- [前段の有限系と分割反復](finite-flow.md)

```bash
python -B -X utf8 tools/check_astra_physics.py
python -B -X utf8 tools/verify.py --integration-only --rebuild
```

証明の範囲は、上記の共通解析的初期値クラスと短時間の非粘性 PDE の構成・空間評価・同時極限である。任意の古典解を対象にした一般 PDE 一意性、任意の滑らかな大初期値、衝撃波後の解、一般の粘性ゼロ極限、全モードの Koopman スペクトル射影やレゾルベントの一様収束は、この追加の結論に含めない。
