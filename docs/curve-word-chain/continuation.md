# 曲線文字チェインの解析・最適化への拡張

PR #128 の代数と整数語の55定理を土台に、原文B・D・E・G・J・K・Lの未形式化部分を進めた追補である。原文と旧検証記録は変更せず、今回の宣言・ハッシュは [追補台帳](continuation-provenance.json)、実行結果は [追補検証記録](verification-continuation.md) に保存する。

## 実積分から円弧の文字状態へ

[CurveWordArc.inc](../../linear_input/lean_check/CurveWordArc.inc) は、長さ $h>0$、総角 $a$ の接線角を $\theta(s)=(a/h)s$ と定義する。座標と費用には既存の `Elastica.xCoord`、`yCoord`、`energy` の実積分を使う。$a\ne0$ のとき

$$
x(h)=\frac{h\sin a}{a},\quad y(h)=\frac{h(1-\cos a)}a,
\qquad F=\frac{a^2}{2h}
$$

を導出し、$a=\pi/2,3\pi/2$ から原文のA・Bの係数を得る。単位速度・定曲率・実総角も証明する。$\xi=2h/(3\pi)$、$c_0=\pi^2/(8h)$ は正で、A/Bの端点は $(3\xi,3\xi)$ と $(-\xi,\xi)$、費用は $c_0,9c_0$ となる。

[CurveWordRealization.inc](../../linear_input/lean_check/CurveWordRealization.inc) は、整数状態をこの単位で復号し、回転と一段更新が実角の接合積に一致することを証明する。`wordState_eq_decode` は任意のBoolean語について成立する。一文字の実積分から得た状態を順に接合する評価と、既存整数語評価の一致であり、角度の持ち上げは保持する。

ここでは単一の区分曲線関数を任意語から構成し、その継ぎ目の正則性をすべて検査したとは主張しない。特に滑らかな拘束付きエラスティカの停留性・最小性とは別の模型である。

## 有限状態の厳密最適化と長時間極限

[CurveWordFiniteState.inc](../../linear_input/lean_check/CurveWordFiniteState.inc) は、有限非空の文字集合に対するBellman再帰を定義し、長さ $n$ の全語への下界、最小値を実現する語の存在、全語の `Finset.inf'` との等式を証明する。四状態の場合には、実際の整数模型の目的関数 $F-u_xx-u_yy$ の一段差分を導出して接続する。任意長について全語を列挙実行したという意味ではなく、長さに関する帰納証明である。

[CurveWordCycleLimit.inc](../../linear_input/lean_check/CurveWordCycleLimit.inc) は、x方向の正規化入力 $v$ に対し

$$
\mu(v)=\min\{1,5-|v|\}
$$

を証明済みの極限として与える。全8遷移について補助関数 $p_v$ を構成し、辺費用 $c(q,a)$ に

$$
c(q,a)\ge\mu(v)+p_v(q')-p_v(q)
$$

を証明する。各状態で等号を満たす文字を具体的に選び、任意長の実在語を構成する。$M(v)=\max_q|p_v(q)|$ は $n$ に依存せず、実際の最適値 $B_n(v)$ に

$$
n\mu(v)-M(v)\le B_n(v)\le n\mu(v)+M(v)
$$

が成立する。これを $n>0$ で割り、`bellman_average_tendsto` と `exhaustive_average_tendsto` で収束を証明する。一般グラフの最小平均閉路定理を仮定したものではなく、この四状態模型の直接証明である。

物理入力 $u$ と正規化入力の関係は $v=u\xi/c_0$。`CurveWordRealization` の物理費用との一致を通じて、原文の

$$
\mu_h(u)=\min\left\{\frac{\pi^2}{8h},\frac{5\pi^2}{8h}-\frac{2h|u|}{3\pi}\right\}
$$

に接続する。`minimumEnergy_average_explicit` はこの明示式への `Tendsto`、`physicalRate_pureA`・`physicalRate_alternating`・`physicalRate_at_threshold` は切替値 $u_*(h)=3\pi^3/(4h^2)$ の両側と閾値での同率を証明する。これは自由な終点を持つ語集合の平均費用であり、時間発展やヒステリシスを述べない。

## 有限温度と零温度

[CurveWordThermodynamics.inc](../../linear_input/lean_check/CurveWordThermodynamics.inc) は、有限非空集合 $S$ の最小値 $m$ を `Finset.inf'` から定義する。$N=|S|$、$\beta>0$ とし、$Z=\sum_{w\in S}\exp(-\beta E_w)$、$q=-\log Z/\beta$ と置くと

$$
m-\frac{\log N}{\beta}\le q\le m,\qquad
|q-m|\le\frac{\log N}{\beta}
$$

が成立し、**一つの固定有限集合**について $\beta\to\infty$ の $q\to m$ を `Tendsto` で証明する。語長 $n\to\infty$ と温度の二重極限、Perron–Frobenius、スペクトル半径による自由エネルギーは別である。

既存の状態エネルギー相似定理を実際に参照し、入力と温度の変換を含む $Z$ と $q$ の相似則も証明する。終点ごとの合算重みから多重度へ戻す等式には、費用が既知の共通値である条件を明記する。一般のラプラス変換の一意性は仮定も証明もしていない。

## 三次観測と全次数の相似

[CurveWordSignature.inc](../../linear_input/lean_check/CurveWordSignature.inc) は、速度座標 $v_i(t)$ の実反復積分を任意の有限語に対して再帰定義する。幾何学的なpath signatureとしての読み方は連続速度に限定する。Leanの積分は非可積分関数にも値を与えるため、型上で定義できることだけから幾何学的意味を主張しない。内部では最後の積分座標を先頭に置き、公開の `signature` では語を反転して通常の時系列順に戻す。任意次数 $m$ について

$$
S_{i_1\ldots i_m}(\sigma v)=\sigma^mS_{i_1\ldots i_m}(v)
$$

を帰納的に証明する。これは固定したパラメータ上の速度の空間相似で、弧長パラメータ変換の一般定理は含まない。連続速度について一次・二次のChen分割式を実積分から導く。接線角から復元した曲線については

$$
\int x^2\,dy=2S_{xxy}
$$

を証明し、平行移動時の二次・一次の交差項も導出する。

[CurveWordCircularMoment.inc](../../linear_input/lean_check/CurveWordCircularMoment.inc) は、円周の明示座標 $x=c+R\sin t,\ y=d-R\cos t$ と実際の $y'$ に対する線積分を扱う。任意開始角から $n$ 周すると

$$
\int x^2\,dy=2n\pi cR^2
$$

である。A円を分割してB円の3周を挿入する二つの明示的な線積分和について、接合位置・周回後の戻りと積分加法性から差 $-12\pi R^3$、$R=2h/(3\pi)$ では $-32h^3/(9\pi^2)\ne0$ を証明する。

符号付き面積も実際の $\tfrac12\int(xy'-yx')$ から定義し、任意開始角のn周の値 $n\pi R^2$ を証明する。上の二構成はどちらも $12\pi R^2=16h^2/(3\pi)$ の面積を持ち、`equal_area_distinct_moments` は面積一致と三次積分不一致を合わせて述べる。

これは原文の三次モーメント計算を実積分として検査したもの。Boolean語評価とこの区分的な円周列を同一の曲線構成として結ぶ写像はまだ別に残る。一般の全次数Chen恒等式、shuffleからの完備自由リー代数、Hambly–Lyons、tree-like商、BCHは今回の定理には含めない。

## 残る形式化

- 任意語から単一の区分曲線を作る構成、面積状態との全面的同定、滑らかな継ぎ目への近似と正則性。
- 一般の有限グラフに対する最小平均閉路定理、通常行列のスペクトル半径と長語自由エネルギー。
- 一般の凸共役・Fenchel–Moreauとラプラス変換の一意復元。
- Booleanの8文字評価から明示円周列への曲線レベルの同定、全次数Chen、Hambly–Lyons、完備自由リー代数とBCH。

これらの境界を保ったまま、今回の形式化を共通組立・全宣言の公理監査・出典ハッシュ監査へ登録する。
