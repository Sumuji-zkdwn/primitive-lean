# 曲線文字の定理チェイン — 原文・証明・形式化の対応

2026-10-20 の「クソ玉定理チェイン」を、primitive-lean の既存の曲線・面積・観測の定理へ接続する案内です。[保存原文](../../sources/curve_word_chain_20261110/theorem-chain-2026-10-20.md)は歴史資料として保持し、条件の補足と形式化の範囲をこの文書で明示します。本文の入口は引き続き[原始の形式化](../../原始の形式化.md)です。

第一段階の55定理・81宣言はPR #128でmainへ統合しました。その[検証記録](verification.md)を保持し、未形式化だった解析・最適化への追加は[今回の追補](continuation.md)と[追補検証記録](verification-continuation.md)に分けます。原文の手証明、有限全列挙、既知定理の適用、Leanの核による検査を区別します。

## 模型と適用範囲

原始の変分問題は長さ・端点位置・端点接線角を固定します。一方、このチェインでは曲線片を文字として接ぎ、**終点が異なってよい語集合**を比較します。固定端点のままでは終点への線形入力は境界定数なので、この語集合の選別を元の変分問題へそのまま持ち込めません。

各片の初期接線を水平にそろえ、変位を $z\in\mathbb C$、実数値の総角変化を $\alpha\in\mathbb R$、加法的費用を $F\in\mathbb R$ とします。角度は $2\pi$ を法として同一視せず、向きを求めるときに $e^{i\alpha}$ を使います。曲線からこれらを定める式は

$$
z=\int_0^L e^{i\theta(s)}\,ds,\qquad
\alpha=\theta(L)-\theta(0),\qquad
F=\int_0^L\varepsilon(\kappa(s))\,ds.
$$

円弧の具体例は $h>0$、二次密度 $\varepsilon(\kappa)=\kappa^2/2$ を使います。継ぎ目で接線は連続でも曲率は跳ぶので、**区分的に滑らかな単位速度曲線**の補助模型です。一般の滑らかなエラスティカの停留性・最小性や、任意の接合の正則性を証明したという意味ではありません。

## A〜M と証明原稿の対応

| 原文 | 数学上の主張と根拠 | このリポジトリでの位置づけ |
|---|---|---|
| A | 接合積は結合的。終点の交換差は一般に非零。指数の加法則と代数展開で示す。 | [CurveWordAlgebra.inc](../../linear_input/lean_check/CurveWordAlgebra.inc)に実装。 |
| B | 長さ $h>0$、総角 $\pi/2,3\pi/2$ の二円弧は、順序だけで終点が変わる。 | `CurveWordArc.inc` が実積分からA/Bの係数を導出し、`CurveWordRealization.inc` が任意語の片状態接合を `CurveWordFinite.inc` の整数評価へ接続する。単一の区分曲線構成と継ぎ目正則性は別。 |
| C | 一方向で見えない差が $\pi/2$ の接頭辞で見える。二つの文脈観測が状態を完全判定する。 | `CurveWordAlgebra.inc` に実装。具体的な AB/BA と AAB/ABA は `CurveWordFinite.inc`。 |
| D | 語の状態は接合則で逐次計算できる。有限個の向きに閉じる場合、線形終点費用は有限状態化できる。 | `CurveWordFiniteState.inc` がBellman再帰と全固定長語の有限最小値の一致を証明し、四状態の実目的関数へ接続。一般の等比級数とmin-plus行列べきの表記は別。 |
| E | 四状態模型の最適長時間平均と切替閾値。 | `CurveWordCycleLimit.inc` が全遷移の補助関数下界と達成語から一様誤差界と `Tendsto` を証明。`CurveWordRealization.inc` が物理単位へ接続。一般グラフの閉路平均定理は未形式化。 |
| F | 同費用の終点集合の全入力最小値は凸包の支持関数で決まり、内部の点や語数を忘れる。 | 具体的な格子点は `CurveWordFinite.inc`。既存 [BranchForgetting.inc](../../linear_input/lean_check/BranchForgetting.inc) の `hidden_state_above_chord`・`minimum_forgets_hidden_state` は関連する限定命題。一般の Fenchel–Moreau 定理の形式化とは区別する。 |
| G | 有限温度の誤差評価、零温度、終点合算重み、長語自由エネルギー。 | `CurveWordThermodynamics.inc` が有限集合のlog-sum-exp上下界・零温度極限・共通費用時の多重度関係を証明。ラプラス一意性とスペクトル半径による長語極限は未形式化。 |
| H | 面積を加えると、接合に外積の交差項が現れる。交差項はコサイクル条件を満たす。 | 既存 [HistorySignature.inc](../../linear_input/lean_check/HistorySignature.inc) の `area_split_cross_term` は実積分の分割則を証明。新規 `LinearInputCurveWordAlgebra.area_cocycle_identity`・`joinArea_assoc` は抽象状態でのコサイクルと結合律を証明。任意の曲線文字接合への解析的な橋渡しは別の命題。 |
| I | 3A3B の20語は終点では12状態、面積までなら20状態になる。 | `CurveWordFinite.inc` の有限例・全列挙に実装。面積差は文字固有面積が同数で相殺することを使う。 |
| J | 4A4B の70語は面積まででも50状態。特定の衝突は三次モーメントで分かれる。 | 二次までの語衝突は `CurveWordFinite.inc`。`CurveWordCircularMoment.inc` が明示円周列の実面積一致と三次積分差を証明。Boolean語からその円周列への曲線構成の同定は残る。 |
| K | Chen の接合則と、全 signature による tree-like 同値までの一意性。 | `HistorySignature.inc` の二次結果に加え、`CurveWordSignature.inc` が実反復積分を全有限次数で定義し、一次・二次Chen式と三次モーメントの係数を証明。全次数ChenとHambly–Lyonsは未形式化。 |
| L | 相似倍率に応じて変位・曲げ費用・面積・高次積分の次数が変わる。 | 既存の状態相似に加え、`CurveWordArc.inc` の実円弧相似、`CurveWordThermodynamics.inc` の分配関数相似、`CurveWordSignature.inc` の任意有限次数の空間相似を証明。一般の弧長再パラメータ化は別。 |
| M | 全 signature の形式的対数は、次数で完備化した自由リー代数に入り、接合は BCH 級数で記述される。 | 既知接続として保持。自由リー代数の完備化・全対数・BCH は今回の Lean 追加範囲外。 |

この表は内容の対応であり、Lean の証明項から抽出した依存グラフではありません。正確な形式命題と仮定は各宣言を参照してください。

## 接合と文脈観測：A〜D

接合積は

$$
(z,\alpha,F)\star(w,\beta,G)
  =(z+e^{i\alpha}w,\alpha+\beta,F+G).
$$

$e^{i(\alpha+\beta)}=e^{i\alpha}e^{i\beta}$ により結合律が成り立ちます。二文字の交換差は

$$
D(A,B)=(1-e^{i\beta})z_A-(1-e^{i\alpha})z_B.
$$

AB と BA の総角は同じなので、同一接頭辞 P と同一接尾辞 Q を付けたときの終点差は $e^{i\alpha(P)}D(A,B)$ です。後続の変位は相殺し、接頭辞は差を回転させます。

観測 $O=(F,\alpha,\operatorname{Re}z)$ に、総角 $\pi/2$ の接頭辞を付けた観測を加えると、

$$
\operatorname{Re}(i(z_v-z_w))=-\operatorname{Im}(z_v-z_w)
$$

から虚部も復元できます。逆に状態が等しい二語は、同じ前後の文脈を付けても状態が等しく、この観測では区別できません。「観測の完全性」は指定した状態・接合・観測に対するものです。

## 円弧の整数単位系：B・F・I・J

$\xi=2h/(3\pi)$、$c_0=\pi^2/(8h)$ とすると、A と B の変位・角・費用は次の整数で表せます。

| 文字 | 変位 $z/\xi$ | 総角 $\alpha/(\pi/2)$ | 費用 $F/c_0$ |
|---|---:|---:|---:|
| A | $(3,3)$ | 1 | 1 |
| B | $(-1,1)$ | 3 | 9 |

向きによる回転は四種類ですが、総角そのものは整数の累積として保持します。総角を単に 4 で割った余りへ置き換えると、原文の状態 $S=(z,\alpha,F)$ から情報を落とします。

順序に依存する面積の交差項は

$$
D=\frac{2(A_{\rm signed}-\sum A_{\rm letter})}{\xi^2},\qquad
D_{n+1}=D_n+x_n\Delta y-y_n\Delta x
$$

で整数計算できます。同じ個数の文字を使う語では文字固有面積の和が同じなので、D の差から実面積の差を求められます。

- AB/BA は、単位化した終点が $(2,2)/(2,-2)$。費用と実総角は同じです。
- AAB/ABA は、終点が $(1,5)/(5,5)$ となり、x 方向でも区別できます。
- AABBBA/BAAABB は終点などが同じで、D が 8/24。面積差は $8\xi^2=32h^2/(9\pi^2)$ です。
- AAAABBBB/AAABBBBA は整数模型では終点・総角・費用・面積が同じです。追補は、対応するA円/B円の明示的な線積分和について実面積の一致と三次モーメント差 $-32h^3/(9\pi^2)$ を微積分から証明します。整数語評価とこの区分曲線構成の完全な同定は分けて残します。

有限の全列挙は、指定した語集合についての証明です。任意の長さの語を二次または三次までで識別できるとは主張しません。また、元の `check_chain_exact.py` にある三次モーメント式の表示は、その式を計算機が導出・証明した証拠ではありません。

## 最小化と有限温度：E〜G

四状態グラフの単純閉路は A の四周期、B の四周期、隣接状態の二周期です。閉路平均を比較し、長い道を閉路と長さ高々3の単純路へ分解すると、原文の模型では

$$
\mu(u)=\min\left\{\frac{\pi^2}{8h},\frac{5\pi^2}{8h}-\frac{2h|u|}{3\pi}\right\},
\qquad u_*=\frac{3\pi^3}{4h^2}
$$

を得ます。追補の `CurveWordCycleLimit` は、この四状態模型について閉路分解の一般定理を仮定せず、全辺の補助関数評価と達成語から同じ極限を形式証明します。これは長語の平均費用の切替で、時間発展やヒステリシスの主張ではありません。

同費用の有限語集合では $m(u)=F_{\rm fixed}-h_{\operatorname{conv}X}(u)$ なので、全入力の最小値から分かるのは凸包までです。3A3B の端点は単位化すると $[-2,6]\times[-6,6]$ を凸包に持ち、内部の点の個数とラベルは支持関数からは復元できません。

有限非空の語集合 $W$、$N=|W|$、$\beta>0$ に対し

$$
Z(u,\beta)=\sum_{w\in W}e^{-\beta(F_w-u\cdot z_w)},\qquad
q=-\beta^{-1}\log Z
$$

を定めると、$m-\log N/\beta\le q\le m$ です。固定した $\beta$ で全 u の Z を厳密に知ることは、有限測度のラプラス変換を知ることに対応します。復元対象は各終点 z の重み

$$
\mu_\beta(\{z\})=\sum_{w:z_w=z}e^{-\beta F_w}
$$

です。**費用が異なる語の個数や費用の内訳は、この合算重みだけでは一般に分かりません。** 共通費用 F が既知なら $e^{\beta F}\mu_\beta(\{z\})$ が多重度になります。原文概略の「分布と多重度まで」はこの条件付きで読みます。

原文Fの四次ポテンシャルの凸包公式には **$\lambda>0,r<0$** が必要です。$a=\sqrt{-r/\lambda}$ と置いた中央の平坦部分 $-r^2/(4\lambda)$ と外側の $V(x)$ の式は、この条件で用います。

## 面積・全署名・対数：H〜M

面積を加えた接合の交差項は $\Omega(g,h)=\tfrac12\operatorname{Im}(\bar z e^{i\alpha}w)$ です。外積の双線形性と回転不変性により、コサイクル恒等式

$$
\Omega(g,h)+\Omega(gh,k)=\Omega(h,k)+\Omega(g,hk)
$$

が成り立ちます。実曲線の面積積分からの分割則は `LinearInputHistorySignature.area_split_cross_term`、二次反復積分との関係は `area_eq_second_antisymmetric`、`second_shuffle`、`mixed_second_reconstruction` に対応します。

全署名はすべての反復積分を並べた形式級数です。Chen の公式では、後半の曲線の増分を前半の総角だけ回転させてからテンソル代数の積を取ります。有限長の有界変動曲線について、全署名が同じであることと tree-like 同値であることの同値は、[Hambly–Lyons の既知定理](https://annals.math.princeton.edu/2010/171-1/p02)です。始点はそろえ、パラメータ時刻や tree-like な往復まで復元するとはしません。

全署名の形式的対数は、厳密には**次数で完備化した自由リー代数**の元です。有限次数で打ち切った対数と、無限の形式級数である全対数は区別します。

$$
\log\operatorname{Sig}(\gamma)
=z_xX+z_yY+A_{\rm signed}[X,Y]+\text{三次以上}.
$$

接合と BCH 級数の接続は既知数学として参照し、今回の新規 Lean 定理には含めません。原文が示した [Chen identity・log-signature の参照先](https://link.springer.com/chapter/10.1007/978-3-031-97239-3_1)も保持します。

相似倍率 $\sigma>0$ では、変位は $\sigma$、二次曲げ費用は $\sigma^{-1}$、面積は $\sigma^2$、m 次反復積分は $\sigma^m$ 倍です。原文の

$$
J^{(\sigma h)}_u=\sigma^{-1}J^{(h)}_{\sigma^2u},\qquad
Z^{(\sigma h)}_n(u,\beta)=Z^{(h)}_n(\sigma^2u,\beta/\sigma)
$$

は入力と温度も一緒に変換する式です。同じ数値入力を固定したまま、異なる大きさの模型を同一視するものではありません。

## 残る形式化と検証の読み方

第一段階に残した項目の一部は[解析・最適化の追補](continuation.md)で閉じました。現在も次を分けて残します。

- 任意語を単一の区分曲線として構成する解析的同定、面積を含めた全面的な接続、滑らかな接合の構成と正則性。一文字の実積分と任意語の状態評価の一致は追加済み。
- 一般のmin-plus行列べき表示、一般グラフの最小平均閉路定理、スペクトル半径による自由エネルギーと二重極限。四状態の長時間極限と固定有限族の零温度極限は追加済み。
- 一般の Fenchel–Moreau 定理、固定温度のラプラス変換からの一意復元。
- Boolean語と明示円周列の曲線レベルでの同定、全次数 Chen 恒等式、Hambly–Lyons 定理、tree-like 商、完備自由リー代数と BCH。明示円周列の三次実積分、一次・二次Chen、全有限次数の空間相似は追加済み。
- 曲線の停留性から独立した時間発展・履歴選択・自己増殖の法則。

`LinearInputHistorySignature.finite_family_separating_cutoff` は、異なる二対象がある段で区別できるという仮定の下で、有限族に共通の識別段数を与えます。その仮定を証明せずに、全署名の一意性や任意長の語の識別へ読み替えることはできません。

共通検証入口はリポジトリ直下の `python -B -X utf8 tools/verify.py --integration-only` です。結果は対象ソース・依存 revision・実行ログに結び付けて報告します。有限検算の成功は全チェインの形式証明完了を意味せず、過去の成功記録は今回の実行結果として数えません。
