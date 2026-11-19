# Laakso第一近似の最小エネルギーと結合の臨界値

2026年11月19日。対象は六頂点・六辺、実数の二成分状態、外部入力 \(u=0\)、全頂点で共通の \(\lambda>0\)、全辺で共通の \(\kappa>0\)。この有限模型では、偶数類と奇数類の最小値差はすべての正係数で正になる。奇数類で零状態が最小になる境界は

\[
\kappa_*=\frac{\sqrt2-1}{(5-\sqrt{17})/2}
=0.944728520273278791\ldots
\]

である。境界を含む \(\kappa\ge\kappa_*\) で奇数類の最小値は \(3/(2\lambda)\)、等号は零状態のみ。境界より下には零状態のエネルギーを下回る状態がある。これらの主張はこのディレクトリの独立したLean原稿で型検査した。

PR #154 の指定ヘッドは `099b77ae5b9bad7bdcafe70a70cf31f6fb8c98b9`。同PRの固定係数の分解を出発点として、新規の `CoefficientBounds.lean` で一般係数を扱う。[PR #154](https://github.com/Sumuji-zkdwn/primitive-lean/pull/154) · [基準コミット](https://github.com/Sumuji-zkdwn/primitive-lean/commit/099b77ae5b9bad7bdcafe70a70cf31f6fb8c98b9)

## エネルギーと四組の分解

頂点は外側 \(0,1,2,3\)、中央 \(4,5\)。辺ID順の端点は \((0,4),(1,4),(4,5),(4,5),(5,2),(5,3)\)。\(\sigma_e\in\{\pm1\}\) とし、中央二辺の符号積が \(+1\) なら偶数類、\(-1\) なら奇数類と呼ぶ。頂点で二成分を同時に反転し、接続の符号も切り替えると、正の共通係数のもとでエネルギーは保存される。[グラフの原稿](https://github.com/Sumuji-zkdwn/primitive-lean/blob/099b77ae5b9bad7bdcafe70a70cf31f6fb8c98b9/linear_input/lean_check/LaaksoFiniteGraph.inc#L166-L168) · [切り替えの原稿](https://github.com/Sumuji-zkdwn/primitive-lean/blob/099b77ae5b9bad7bdcafe70a70cf31f6fb8c98b9/linear_input/lean_check/LaaksoSignedGauge.inc)

研究原典第4節の係数規約を使う。\(q_i=(x_i,y_i)\) とおくと

\[
 F_{\lambda,\kappa}^{\tau}(q)
 =\sum_{i=0}^{5}\left[\frac{\lambda}{4}(x_i^2-\lambda^{-1})^2+
 \frac12(y_i-\sqrt2 x_i)^2\right]
 +\frac{\kappa}{2}\sum_{e=0}^{5}\|q_{s(e)}-\sigma_e q_{t(e)}\|^2 .
\]

各辺を一回ずつ数え、中央二辺は個別に含める。四次ポテンシャルを展開すると \(\lambda x^4/4-x^2/2+1/(4\lambda)\)。したがって \(\lambda\) は四次項と原点の費用を変え、局所井戸は \(\pm(1,\sqrt2)/\sqrt{\lambda}\) に移る。\(\kappa\) は辺費用全体に掛かる。[原典の一般係数式](https://github.com/Sumuji-zkdwn/primitive-lean/blob/099b77ae5b9bad7bdcafe70a70cf31f6fb8c98b9/sources/laakso/signed/SIGNED_CONNECTIONS.md#L70-L100) · [固定係数のLean定義](https://github.com/Sumuji-zkdwn/primitive-lean/blob/099b77ae5b9bad7bdcafe70a70cf31f6fb8c98b9/linear_input/lean_check/LaaksoSignedEnergy.inc#L17-L37)

奇数類を辺3だけ負の代表へ移す。四組の（外側, 中央）は
\(\mathcal P=\{(0,4),(1,4),(2,5),(3,5)\}\) である。\(p=(x,y), c=(a,b)\) に対し

\[
 A(p,c)=x^4/4+a^4/8,\qquad
 D(p,c)=\bigl(\|p-c\|^2+\|c\|^2\bigr)/2 .
\]

中央の異符号二辺からの合計は \(\kappa(\|q_4\|^2+\|q_5\|^2)\)。各中央頂点の寄与を二つの隣接組へ半分ずつ配ると \(D\) を得る。PRの `leafExcess` は一組につき

\[
 B_{1,1}=A+(x-\sqrt2\,y/2-a/2)^2+
 (y-\sqrt2\,a/2-b)^2/2+\tfrac34(a-2\sqrt2\,b/3)^2+b^2/12 .
\]

PRの「四つの非負項」はこの \(B_{1,1}\) を四組について足したものである。一般係数の恒等式は

\[
 \begin{aligned}
 B_{\lambda,\kappa}(p,c)&=B_{1,1}(p,c)+(\lambda-1)A(p,c)+(\kappa-1)D(p,c),\\
 F_{\lambda,\kappa}^{\rm flip}(q)
   &=\frac{3}{2\lambda}+\sum_{(i,j)\in\mathcal P} B_{\lambda,\kappa}(q_i,q_j).
 \end{aligned}
\]

補正の係数は負にもなるため、この恒等式だけでは補正後の四組の非負性は従わない。新規Lean補題 `block_correction` が一組の恒等式、`decomposition` が総和である。[固定係数の平方和](https://github.com/Sumuji-zkdwn/primitive-lean/blob/099b77ae5b9bad7bdcafe70a70cf31f6fb8c98b9/linear_input/lean_check/LaaksoSignedMinimum.inc#L12-L61)

## 偶奇の差と臨界値

**偶数類。** 正の両係数では最小値は \(0\)。全辺正の代表でエネルギーが零なら、各辺の両端の状態が一致し、連結性により全頂点は同一状態になる。局所ポテンシャルも零なので、その共通値は二つの井戸のいずれかである。任意の偶数配置の最小化状態は、この2状態を元の頂点ラベルへ戻したものに尽きる。`even_least`、`even_eq_iff` を型検査した。

**奇数類の全域下界。** 状態を頂点ごとに \(\sqrt{\lambda}\) 倍すると、\(F_{1,\kappa}(\sqrt{\lambda}q)=\lambda F_{\lambda,\kappa}(q)\)。局所費用と辺費用がいずれも非負だから、\(F_{1,\kappa}\ge\min(1,\kappa)F_{1,1}\)。PRの `odd_minimum` をここでそのまま使える。奇数類の全実数状態について

\[
 F_{\lambda,\kappa}(q)\ \ge\
 \frac{3\min(1,\kappa)}{2\lambda}>0 .
\]

局所ポテンシャルの劣位集合では \(x\) と \(y-\sqrt2 x\) がともに有界になり、有限次元でエネルギーは連続である。したがって最小値は達成される。下界は `odd_positive_bound` として型検査した。劣位集合からの一般の達成性はこの段落の手証明である。また、奇数代表で全頂点を同じ井戸に置くと、負の辺一本の費用 \(6\kappa/\lambda\) で済む。固定した \(\lambda\) で \(\kappa\downarrow 0\) とすると、偶奇の最小値差も \(0\) に近づく。

**零状態が最小になるための必要十分条件。** 中央二辺の交差項が相殺されるので、奇数代表の符号付きラプラシアンは、順序 \((0,1,4)\), \((2,3,5)\) で同じ三頂点行列二つに分かれる。

\[
 L_0=\begin{pmatrix}1&0&-1\\0&1&-1\\-1&-1&4\end{pmatrix},
 \qquad \det(tI-L_0)=(t-1)(t^2-5t+2).
\]

\(\mu=(5-\sqrt{17})/2\)、\(d=1-\mu=(\sqrt{17}-3)/2\) とおく。局所二次項の最も低い方向は \(x=y\)、グラフ側の最小固有値は \(\mu\) で、最低二次係数の符号は \(1-\sqrt2+\kappa\mu\) で決まる。Leanでは固有値定理を使わず、同じ境界を与える一組・一座標の恒等式 `edge_square` を用いた。

\[
 (v-w)^2+w^2=\mu(v^2+w^2/2)+(d v-w)^2/d .
\]

これは \(d>0,\ d^2+3d=2\) から展開して得られる。二成分に適用すると一組の費用は、\(\lambda A\)、\(\frac{\sqrt2}{2}[(x-y)^2+(a-b)^2/2]\)、\(\frac{1-\sqrt2+\kappa\mu}{2}(\|p\|^2+\|c\|^2/2)\)、\(\frac{\kappa}{2d}\|dp-c\|^2\) の和になる。境界を含む \(\kappa\ge\kappa_*\) ではすべて非負で、四次項と成分差の項だけで等号は \(x=a=y=b=0\) に限られる。

逆に \(\kappa<\kappa_*\) で、四つの外側頂点を \((s,s)\)、二つの中央頂点を \((ds,ds)\) に置くと

\[
 F_{\lambda,\kappa}^{\rm flip}(q)-F_{\lambda,\kappa}^{\rm flip}(0)
 =\lambda(1+d^4/2)s^4+(1-\sqrt2+\kappa\mu)(4+2d^2)s^2 .
\]

右辺を \(a_0s^4+b_0s^2\) と書くと \(a_0>0,b_0<0\) である。\(s^2=-b_0/(2a_0)\) を選ぶと右辺は \(-b_0^2/(4a_0)<0\)。代表から任意の奇数配置への移送もLeanで検査した。対応する定理は `odd_least`、`odd_eq_iff`、`odd_below_critical`、`odd_origin_minimal_iff`。

## 有理数4例の独立計算

表の個数はそれぞれの符号配置あたり。各例で全64配置を調べた。\(y=\sqrt2 z\) を用い、有理係数の多項式と行列で検算した。

| \(\lambda\) | \(\kappa\) | 偶数類の最小値と状態数 | 奇数類の最小値と状態数 |
|---:|---:|---|---|
| 1 | 1 | 0、2状態 | \(3/2\)、零状態のみ |
| 4 | 1 | 0、2状態 | \(3/8\)、零状態のみ |
| 1 | \(19/20\) | 0、2状態 | \(3/2\)、零状態のみ |
| 1 | \(1/8\) | 0、2状態 | \(0.5270521484230 < m < 0.5270521484231\)、4状態 |

`check_coefficients.py` はPRの検算コードをインポートしない。六辺の接続行列から \(L\) を構成し、原式の展開と二次形式の全係数を両代表で照合する。全配置について代表への対角符号変換を、偶数配置では両方の井戸解を、奇数配置では有理数の厳密な対称消去を検算する。\(A=I+\kappa L\) とおくと、変数順序 \((x_0,\ldots,x_5,z_0,\ldots,z_5)\) の二次部分のヘッセ行列は \(\bigl(\begin{smallmatrix} A&-2I\\-2I&2A\end{smallmatrix}\bigr)\)。上3行の全32奇数配置で12個のピボットはすべて正である。弱結合の行では負のピボットが現れる。各ピボットは `exact-results.json` に収録した。

### \((1,1/8)\) の大域最小と等号条件

奇数代表で全頂点を \((1,\sqrt2)\) にするだけでもエネルギーは \(3/4\) になり、零状態の \(3/2\) を下回る。この試行状態の値は `weak_rational_witness` としても型検査した。実際の最小値と達成状態には次の独立した代数的証明を用いた。

一方の三頂点について \(A=I+L_0/8,\ S=A-2A^{-1}\) とおく。\(A\) は正定値で、\(S\) の非対角成分はすべて厳密に負。\(z\) は平方完成で消去でき、固定した \(x\) での最適値は \(z=A^{-1}x\) である。\(P(t)=39t^4+97t^3+20t-78\) とし、その唯一の正根を \(t\) とおく。\(P(0)<0<P(1)\) で、\(t\ge0\) では \(P'(t)>0\)。正数 \(a\) を \(a^2=(291+117t)/424\)、\(r=a(1,1,t)^T\) とおくと、\(Sr=-(r_1^3,r_2^3,r_3^3)^T\) が成り立つ。この \(r\) の構成に解の対称性や一意性を仮定する必要はない。任意の実数ベクトル \(x,z\) に対し、一方の三頂点の費用 \(F_{\rm side}\) について

\[
 \begin{aligned}
 F_{\rm side}(x,z)-F_{\rm side}(r,A^{-1}r)
  ={}&(z-A^{-1}x)^TA(z-A^{-1}x)
  +\tfrac14\sum_i(x_i^2-r_i^2)^2\\
  &+\tfrac12\sum_{i<j}(-S_{ij})r_i r_j
             (x_i/r_i-x_j/r_j)^2 .
 \end{aligned}
\]

全項非負で、等号は \(x=r\) または \(x=-r\)、かつ \(z=A^{-1}x\) の場合に限る。二つの三頂点群は独立なので各群の符号を個別に選べる。元の変数は \(y=\sqrt2 z\) であり、任意の奇数配置ではこの4状態を頂点切り替えで戻す。全六頂点の最小値は厳密に

\[
 m=\frac32-\frac{2+t^4}{2}\left(\frac{291+117t}{424}\right)^2 .
\]

証明書の検算では行列恒等式を \(\mathbb Q[t]\) の \(P(t)\) による剰余で確かめ、平方完成の残りの係数もすべて照合した。根を有理二分法で挟んだ後、上式の単調性から表中の有理区間を得た。この代数的最小値と4状態の分類は手証明と記号計算で確認した。これら二点のLean形式化、および任意の \(0<\kappa<\kappa_*\) における最小値・全達成状態の明示式は今回の検証範囲外である。

## 検証の再実行

新規の [Lean原稿](CoefficientBounds.lean) は、PR #154 のヘッドと Lean 4.36 移行後の基底で同じ命題を検査する。[再実行スクリプト](replay_lean.py) は指定したチェックアウトの Lean バージョンに応じて、上流6ファイルのSHA-256と mathlib のコミットを照合し、一時ディレクトリで2モジュールを `--trust=0` で型検査する。主定理・恒等式10件について `propext`、`Classical.choice`、`Quot.sound` のみを許す公理監査を行う。

| 基底 | Lean | mathlib | 検査ログ |
|---|---|---|---|
| PR #154 `099b77ae5b9bad7bdcafe70a70cf31f6fb8c98b9` | 4.30.0-rc2 | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` | [4.30の出力](lean-check-430.txt) |
| この追補の親 `8ed4c9347609ff350f947da7e44101abcd993ed9` | 4.36.0-rc2 | `2ddf59c8f14245864e6c0ed227a2dab76b9efea2` | [4.36の出力](lean-check-436.txt) |

リポジトリのルートから次を実行する。Lean 用には `lean/` で普段使用するツールチェーンと、指定した版の mathlib キャッシュを使う。Python 側は Python 3.12.14 と SymPy 1.14.0 で検算した。[独立検算](check_coefficients.py) · [全64配置の結果と有理数証明書](exact-results.json)

```bash
python linear_input/lean_check/laakso_coefficients/replay_lean.py . lean/.lake/packages/mathlib
python linear_input/lean_check/laakso_coefficients/check_coefficients.py
```

4.30での再現には、同じスクリプトの第1引数に元のPRヘッドをチェックアウトしたディレクトリを、第2引数に4.30用のmathlibチェックアウトを渡す。
