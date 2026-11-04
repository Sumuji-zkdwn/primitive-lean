# 軌道和・ヴィエタトレース・積分・有限ジョルダン鎖

2026-11-04 / 独立追加ノート（既存の研究中 E との同一視はしない）

## 検証境界

本ノートの一般命題は明記した仮定の下での数学的証明である。
lean/OrbitTrace.lean が形式化するのは、元の3次式の代数恒等式、判別式、
有限巡回多項式写像の具体例、不変量、望遠鏡和である。
一般のヴィエタ剰余トレースは、根の相異性・多項式の根分解・剰余証明書を明示的に仮定した形で、
`lean/OrbitTraceVieta.lean` に形式化した。任意の根と重みの線形漸化式は
`lean/OrbitTraceMoment.lean` に、次数低下からの一般冪零性は
`lean/OrbitTraceNilpotence.lean` に証明原稿を追加した。解析的なルベーグ測度保存・積分の変数変換、
具体的転送作用素の一般ジョルダン分解は引き続き Lean 未形式化。
tools/check_orbit_trace.py は SymPy 1.14 の有限な厳密計算であり、全称証明ではない。

## 1. 出発点：位数3のメビウス変換と積分

\[
P(x)=x^3-3x+1,\quad Q(x)=x^2-x,\quad
S(x)=P(x)/Q(x),\quad T(x)=1/(1-x).
\]

極を除き T³=id、S∘T=S。3区間
[-1,-1/2]、[1/2,2/3]、[2,3] は T による巡回軌道。
各区間で S は [3/2,19/6] への増加全単射である。

\[
S'(x)=\frac{(x^2-x+1)^2}{(x^2-x)^2}
=1+T'(x)+(T^2)'(x)>0.
\]

従って n≥2 について

\[
\sum_{J}\int_J \left(\frac{x^2-x}{x^3-3x+1}\right)^n dx
=\int_{3/2}^{19/6}s^{-n}ds
=\frac{(2/3)^{n-1}-(6/19)^{n-1}}{n-1}.
\]

n=2 では 20/57。さらに

\[
P(x)-sQ(x)=x^3-sx^2+(s-3)x+1,\qquad
\operatorname{disc}_x(P-sQ)=(s^2-3s+9)^2.
\]

## 2. 一般の剰余係数・ヴィエタトレース定理

標数0の体 K、モニックな m 次式 P、deg Q<m を考え、
F_s(X)=P(X)-sQ(X) とする。F_s が分解体で m 個の相異なる根
r_1,…,r_m を持つと仮定し、Q(r_j)≠0 とする。

\[
\boxed{\mathcal L W(s)
:=\sum_{j=1}^{m} \frac{W(r_j)Q(r_j)}{F_s'(r_j)}
=[X^{m-1}]\operatorname{rem}_{F_s}(WQ).}\tag{A}
\]

証明：剰余 R=rem(WQ,F_s) にラグランジュ補間を適用し、
R の最高次数係数を比較する。Q の X^{m-1} 係数を c とすれば
\(\mathcal L1=c\) となる。

逆根 r_j(s) が実数・単根で連続微分可能な区間 [a,b] では
r_j'(s)=Q(r_j)/F_s'(r_j) より、向き付き積分として

\[
\sum_j\int_{r_j(a)}^{r_j(b)} W(x)\Phi(P(x)/Q(x))\,dx
=\int_a^b(\mathcal L W)(s)\Phi(s)\,ds.\tag{B}
\]

(A) は代数的、(B) は解析的である。符号付きのトレースと、
絶対値を使う実測度の押し出しを混同してはならない。

## 3. 実数上での測度保存：正の留数の多極Boole型写像

実数 a_1<⋯<a_{m-1} と正数 b_j、および任意の c∈ℝ について

\[
S_m(x)=x+c-\sum_{j=1}^{m-1}\frac{b_j}{x-a_j}
\]

を考える。極で分割された m 開区間上 S_m' >0 で、
それぞれ ℝ に全単射となる。逆分枝 r_j の和はヴィエタにより
Σ_j r_j(s)=s-c+Σ_j a_j、ゆえに Σ_j r_j'(s)=1。
変数変換より任意の非負可測関数（または可積分関数）について

\[
\int_{\mathbb R}\Phi(S_m(x))\,dx
=\int_{\mathbb R}\Phi(s)\,ds.\tag{C}
\]

元の S は S(x)=x+1-1/x-1/(x-1) という m=3 の場合。
A_n=(S^{∘n})^{-1}([3/2,19/6]) は 3^n 個の区間を持ち、

\[
\int_{A_n}(S^{\circ n}(x))^{-2}dx=20/57.
\]

一方、後述の x+a/x^p では一般に実逆分枝の単調性が失われる。
その場合に代数的トレース (A) の成立から測度保存 (C) を推論してはいけない。

## 4. 元の S の転送作用素・次数降下

M_k(s)=\mathcal L(x^k)(s) とおくと

\[
M_0=1,\quad M_1=s-1,\quad M_2=s^2-2s+3,
\quad M_{k+3}=sM_{k+2}-(s-3)M_{k+1}-M_k.
\]

V_d=K[s]_{≤d}, N=\mathcal L-I とすると N(V_d)⊆V_{d-1}。
したがって V_d 上 N^{d+1}=0 かつ

\[
\mathcal L^n W=\sum_{j=0}^d\binom{n}{j}N^jW.
\]

実例：\(\mathcal L^n(x^2)=s^2-2ns+n^2+2n\) であるから

\[
\int_{A_n}\frac{x^2}{(S^{\circ n}(x))^2}dx
=\frac53-2n\log(19/9)+(n^2+2n)\frac{20}{57}.
\]

## 5. 任意本数のジョルダン鎖の構成

p≥1、a≠0、K は標数0 として

\[
R_{p,a}(x)=x+a/x^p,\qquad
F_s(X)=X^{p+1}-sX^p+a.
\]

ここではすべての代数的根（必要なら複素根）を数える。
(A) の係数公式を使うと

\[
\boxed{\mathcal L_{p,a}(x^k)(s)
=\sum_{j=0}^{\lfloor k/(p+1)\rfloor}
(-a)^j\binom{k-pj}{j}s^{k-(p+1)j}.}\tag{D}
\]

証明：M_k=[X^p]rem(X^{k+p},F_s)、M_k=s^k (0≤k≤p)、
M_{k+p+1}=sM_{k+p}-aM_k。従って母関数は
Σ_{k≥0}M_kz^k=(1-sz+az^{p+1})^{-1}。
幾何級数と二項定理の係数比較から (D) を得る。

N=\mathcal L_{p,a}-I とすると

\[
N(s^k)=-a(k-p)s^{k-(p+1)}+\text{同剰余類内の低次項}
\quad(k≥p+1),
\]

かつ N(s^k)=0 (k≤p)。
各剰余類 r mod (p+1) は不変で、連鎖の主係数が非零なので
d≥p に対して長さ

\[
\ell_r=1+\left\lfloor\frac{d-r}{p+1}\right\rfloor
\quad(r=0,\ldots,p)
\]

のジョルダン鎖が p+1 本生じる。
p=3、d=11、a=1 なら J_3(1)⊕J_3(1)⊕J_3(1)⊕J_3(1)。
N^0,N^1,N^2,N^3 の階数は 12,8,4,0。

## 6. ヤコビアン1の多項式写像、固定不変量、差分

L(u,v)=(v,v-u)、H_d(u,v)=(u+v^d,v) と置く。
奇数 d≥3 に対し E_d=H_d^{-1}∘L∘H_d を考えると、
det DE_d=1、E_d³=-id、E_d⁶=id。
Q(u,v)=u²-uv+v² は L 不変なので Q∘H_d は E_d 不変。

これとは独立に、任意の集合 A、写像 E:A→A、関数 G:A→ℝ について

\[
\boxed{\sum_{j=0}^{n-1}
\bigl(G(E^jz)-G(E^{j+1}z)\bigr)
=G(z)-G(E^nz).}\tag{E}
\]

これは任意の E に成立し、微分形式の巡回和にも拡張可能だが、
微分形式・線積分の一般解析的設定は本追加では未形式化。
Lean では上式の関数としての望遠鏡和を証明する。

## 7. 証明と再実行

- Lean: cd lean && lake env lean --trust=0 OrbitTrace.lean
- Python: python -m pip install sympy==1.14.0 && python tools/check_orbit_trace.py
- Python の有限検算は 125 件の (p,k) 係数比較、p=3,d=11 の階数、
  元の3次式の不変性・判別式・積分、別のヤコビアン1多項式写像の具体例を含む。
- Lean 統合外のため、既存証明数には加算しない。
  一般定理 (A)-(D)、解析的測度保存 (C)、一般ジョルダン分解、
  およびユーザーの研究中の多項式写像 E への同一化は未形式化・未確認。

既存の lean/Elastica と linear_input/lean_check および統合検証器は変更しない。


## 8. 一般定理のLean追加（2026-11-04 続編）

- `lean/OrbitTraceVieta.lean`
  - `OrbitTrace.nodal_remainder_trace`：任意の体 K と相異なる節点、
    任意の W,Q,R,U∈K[X] について、
    WQ=R+(∏(X−r_i))U、deg R<m なら
    Σ_i W(r_i)Q(r_i)/F'(r_i)=[X^{m−1}]R。
    Mathlib の `Lagrange.coeff_eq_sum` と節点多項式の導関数公式を使用。
  - `OrbitTrace.parametric_remainder_trace`：
    F=P−C(t)Q がこの節点積に一致する場合の直接的な系。
    根の具体値・具体次数に依存しない。
- `lean/OrbitTraceMoment.lean`
  - `OrbitTrace.weighted_moment_recurrence`：
    すべての重み w_i と r_i^(p+1)=s*r_i^p−a を満たす根について、
    M_(k+p+1)=s*M_(k+p)−a*M_k。
    任意の可換環で成立する。元のトレース公式で使う
    w_i=Q(r_i)/F'(r_i) はその特殊例。
- `lean/OrbitTraceNilpotence.lean`
  - `OrbitTrace.iterDrop_nilpotent_of_rank_drop`：
    零点を固定し、零でない点からの非零遷移が自然数ランクを
    真に減少させるなら、ランク d 以下から d+1 回以内に零へ達する。
  - `OrbitTrace.polynomial_degree_drop_nilpotent`：
    線形写像 N:K[X]→ₗ[K]K[X] にこれを自然次数で適用。
    **N=ℒ−I が実際に次数を下げることの証明は別途必要**であり、
    この一般命題だけで具体的ジョルダン分解が成立するとは主張しない。

今回のCIで独立に検査するコマンド：

```bash
cd lean
lake env lean --trust=0 OrbitTrace.lean
lake env lean --trust=0 OrbitTraceVieta.lean
lake env lean --trust=0 OrbitTraceMoment.lean
lake env lean --trust=0 OrbitTraceNilpotence.lean
cd ..
python tools/check_orbit_trace.py
```

**残課題**：一般 p,a の閉形式 (D) をLean上の
剰余で実装し、(D) による厳密な次数降下を証明し、
p+1本のジョルダン鎖への基底変換を証明する。
12×12 の階数計算だけでは、任意次数の一般分類は形式的に確定しない。


## 9. p=3、次数≤11の厳密なジョルダン鎖証明書

`lean/OrbitTraceMoment12.lean` は、M₀=1, M₁=s, M₂=s², M₃=s³ と
M_(k+4)=sM_(k+3)−aM_k を仮定し、次の8項をすべて一般可換環上で導く：

- M₄=s⁴−a, M₅=s⁵−2as, M₆=s⁶−3as², M₇=s⁷−4as³。
- M₈=s⁸−5as⁴+a², M₉=s⁹−6as⁵+3a²s。
- M₁₀=s¹⁰−7as⁶+6a²s², M₁₁=s¹¹−8as⁷+10a²s³。

`lean/OrbitTraceJordan3.lean` は各 r=0,1,2,3 に対応する
(s^r,s^(r+4),s^(r+8)) 座標で、N=ℒ−I の候補行列

```
  [ 0   −(r+1)a   (r+1)(r+2)a²/2 ]
  [ 0      0        −(r+5)a       ]
  [ 0      0            0         ]
```

を具体的に定義し、N³=0、a≠0 なら N² の最右上成分が
(r+1)(r+5)a²≠0 であることを形式化する。
4つの直和モデルについても三乗零を証明する。

**証明の境界**：モーメントの初期値と漸化式の条件付き帰結、
および上記の明示行列恒等式までは Lean の対象。
「この行列が一般に定義した剰余トレース演算子 ℒ と同じである」
という結合と、任意 p の全ジョルダン分類は別の Lean 定理を要する。
ただし p=3 の数式上の対応は (D) の有限次数代入で直接確認できる。
