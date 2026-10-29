# 定義と証明付き命題

## 1. この資料でのF0

参照できる会話に現れた式を、次の型で固定する。会話の省略部分に別の公理がある可能性までは補完しない。

\[
K:\mathcal B\to\mathcal B,\qquad K^2=K,\qquad
S:\mathcal B\to\mathcal B^d,\qquad
C:\mathcal B^d\to\mathcal B,\quad d\ge1.
\]

\[
K^{(d)}(x_1,\ldots,x_d)=(Kx_1,\ldots,Kx_d),\qquad
T=K\circ C\circ K^{(d)}\circ S.
\]

追加条件は、必要な命題に限って課す。

\[
\tag{A} C\circ S=\operatorname{id}_{\mathcal B},\qquad
\tag{B} S\circ K=K^{(d)}\circ S.
\]

元の会話の出力成分数nを、この資料ではdと書く。集合の点数Nと混同しないためである。主な数値例はd=2。

以下、\(\mathcal B\)は空でないとする。\(F=\operatorname{Fix}(K)\)とおくと、冪等性により\(F=\operatorname{im}(K)\)。

## 2. 塊への分解

各\(a\in F\)に対して\(B_a=K^{-1}(a)\)とする。

\[
\mathcal B=\bigsqcup_{a\in F}B_a,\qquad a\in B_a.
\]

証明：任意のxについてKxは固定点であり、xはただ一つのファイバーに属する。またKa=a。

したがって冪等写像は「各塊に代表点を一つ指定した集合分割」である。有限の場合、

\[
N=|\mathcal B|,\quad r=|F|,\quad
m_a=|B_a|,\qquad \sum_{a\in F}m_a=N.
\]

代表点数rと、各塊の大きさの列\((m_a)\)を区別する。後者は代表点・塊のラベルを忘れると整数分割になる。

## 3. 像と周期の上限（A・B不要）

\[
T(\mathcal B)\subseteq F.
\]

証明：Tの最外側がKなので、Tの出力はKの像に入る。

有限集合の場合、Tを反復した任意の軌道は最初の一回の後Fに入り、最終的に周期軌道に到達する。異なる周期点はすべてFに属するから、

\[
\text{任意の周期の長さ}\le r.
\]

これは周期長の制約であり、可能な力学の個数や「能力」全般をrだけで定める命題ではない。

## 4. Bが保証する区別不能性

\(\mathcal S_B\)を条件Bを満たすS全体とする。このとき、

\[
Kx=Ky\quad\Longleftrightarrow\quad
\forall S\in\mathcal S_B,\quad K^{(d)}S(x)=K^{(d)}S(y).
\]

証明（順方向）：Bより\(K^{(d)}S(x)=S(Kx)\)。Kx=Kyなら両者は等しい。

証明（逆方向）：対角写像\(\Delta(x)=(x,\ldots,x)\)はBを満たす。Kx≠Kyなら\(K^{(d)}\Delta(x)\ne K^{(d)}\Delta(y)\)。

重要な限定：区別不能なのは**Kを各成分に作用させた後のSの出力**。生のS(x)まで同じになるとは限らない。

たとえば\(\mathcal B=\{0,1,2\}\)、K=(0,0,2)、d=1、S=idとするとBを満たし、K0=K1だがS(0)≠S(1)。

また、BのもとではT自体もファイバー上で一定である。

\[
T=KCSK,\qquad TK=T.
\]

よってKx=KyならTx=Ty。これは「Kが捨てた区別を、Bと整合するこの合成Tでは復活させられない」という正確な形になる。

## 5. B適合Sの計数

有限集合でファイバーサイズを\(m_1,\ldots,m_r\)とする。B適合なSの個数は、

\[
\boxed{N_{B,d}(m_1,\ldots,m_r)=
\prod_{i=1}^{r}\left(\sum_{j=1}^{r}m_j^{m_i-1}\right)^d.}
\]

証明：Sを成分ごとに\(s_1,\ldots,s_d\)と書く。Bは各成分について\(s_\ell K=Ks_\ell\)と同値で、成分間の選択は独立。

一成分sと一つの入力ファイバー\(B_i\)を考える。その代表点a_iの像s(a_i)はKの固定点a_jでなければならない。a_jを選ぶと、残る\(m_i-1\)点はそれぞれ\(B_j\)の任意の点へ送れるため、\(m_j^{m_i-1}\)通り。jで足し、iで掛け、最後にd成分分の冪を取る。

ここで数えているのは、**固定した一つのKに対する写像Sの個数**。Aを満たすCとの組や、Sの単射性・全射性、Tの異なる個数は数えていない。

端点：

\[
N_{B,d}(1,\ldots,1)=N^{dN},\qquad
N_{B,d}(N)=N^{d(N-1)}.
\]

前者はK=idでSが任意。後者はKが定値で、代表点の像だけが強制される。

## 6. 冪等Kの個数

像の大きさrを固定すると、

\[
\#K_{N,r}=\binom Nr r^{N-r},\qquad
\#K_N=\sum_{r=1}^{N}\binom Nr r^{N-r}.
\]

証明：r個の固定点を選び、それ以外のN−r点の像をそのr点から自由に選ぶ。

型\(\lambda=(m_1,\ldots,m_r)\)を固定し、大きさsの塊の個数をc_sとすれば、

\[
\#K_\lambda=
\frac{N!\prod_i m_i}{\prod_i m_i!\,\prod_s c_s!}
=\frac{N!}{\prod_i(m_i-1)!\,\prod_s c_s!}.
\]

これはラベル付きN点集合上の写像数。型の個数そのものとは別の量である。

## 7. A+B縮退

\[
\boxed{A+B\implies T=K.}
\]

証明：

\[
T=KCK^{(d)}S=KCSK=K\operatorname{id}_{\mathcal B}K=K^2=K.
\]

したがってA+Bのもとでは\(T^2=T\)であり、固定点以外の周期はない。

正確な対偶は、

\[
T\ne K\implies \neg A\ \lor\ \neg B.
\]

AまたはBの不成立だけからT≠Kが従うわけではない。またT=Kでも初回に非固定点が代表点へ移ることはある。「運動の消滅」は、この初回の移動まで否定する表現ではない。
