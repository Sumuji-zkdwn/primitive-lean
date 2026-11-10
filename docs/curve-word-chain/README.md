# 曲線文字の定理チェイン — 原文・証明・形式化の対応

2026-10-20 の「クソ玉定理チェイン」を、primitive-lean の既存の曲線・面積・観測の定理へ接続する案内です。[保存原文](../../sources/curve_word_chain_20261110/theorem-chain-2026-10-20.md)は歴史資料として保持し、条件の補足と形式化の範囲をこの文書で明示します。本文の入口は引き続き[原始の形式化](../../原始の形式化.md)です。

第一段階の55定理・81宣言はPR #128、次の150定理・196宣言はPR #129でmainへ統合しました。その[第一段階の検証記録](verification.md)と[解析・最適化の追補記録](verification-continuation.md)を保持します。続く[全次数・一般極限への拡張](extensions.md)では、一本の曲線の構成、一般グラフ、ラプラス一意性、スペクトル極限、全次数Chen・自由Lie・BCHに加え、連続BV曲線の一般Hambly–Lyonsまで証明し、A〜Mの数学的核心を接続しました。各主張の条件は以下の表と証明原稿に明示します。原文の手証明、有限全列挙、既知定理の引用、Leanの核による検査は、それぞれの証拠として区別します。

最終のHambly–Lyons・二曲線同値・有限次元座標転送は、最新依存原稿を含む個別検査で `lake env lean --trust=0` が終了コード0・警告0となり、公理監査は `propext`・`Classical.choice`・`Quot.sound` のみでした。[拡張の検証記録](verification-extensions.md)は43ファイル時点のクリーンな全26段階検査の記録として保持します。現在の登録原稿・ハッシュは[台帳](extension-provenance.json)を参照してください。最終原稿全体の共通組立・総合検査については完成検証記録を別途追加予定です。途中コミットの総合検査を、その後の追加原稿の検査結果として扱いません。

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
| B | 長さ $h>0$、総角 $\pi/2,3\pi/2$ の二円弧は、順序だけで終点が変わる。 | `CurveWordArc.inc` がA/Bの実積分を評価し、`CurveWordPiecewise.inc` が任意語を一本のC1単位速度曲線として構成して整数状態へ同定する。曲率の跳びは許す。 |
| C | 一方向で見えない差が $\pi/2$ の接頭辞で見える。二つの文脈観測が状態を完全判定する。 | `CurveWordAlgebra.inc` に実装。具体的な AB/BA と AAB/ABA は `CurveWordFinite.inc`。 |
| D | 語の状態は接合則で逐次計算できる。有限個の向きに閉じる場合、線形終点費用は有限状態化できる。 | `CurveWordFiniteState.inc` がBellman再帰と全固定長語の有限最小値の一致を証明し、四状態の実目的関数へ接続。`CurveWordGenerating.inc`・`CurveWordWordGenerating.inc` が実行列べきの全語長形式級数とレゾルベント・有理性を証明する。 |
| E | 四状態模型の最適長時間平均と切替閾値。 | 四状態の直接証明に加え、`CurveWordGraphLimit.inc` と `CurveWordDirectedGraph.inc` が一般有限グラフの最小平均閉路の存在と、到達可能な始点からの最適平均費用の収束を証明する。 |
| F | 同費用の終点集合の全入力最小値は凸包の支持関数で決まり、内部の点や語数を忘れる。 | `CurveWordConvexObservation.inc`・`CurveWordConvexSeparation.inc` が有限非空集合の実支持関数・凸包上の最小値と、全連続線形観測の一致⇔凸包の一致を証明する。一般の Fenchel–Moreau 定理とは区別する。 |
| G | 有限温度の誤差評価、零温度、終点合算重み、長語自由エネルギー。 | `CurveWordThermodynamics.inc` が固定有限非空集合の実最小値への零温度極限を証明。`CurveWordLaplace.inc` が指数可積分性の下で有限測度の一意性、`CurveWordSpectral.inc`・`CurveWordTransfer.inc` が通常のスペクトル半径への長語極限と、その後の零温度極限を証明。`CurveWordArcGenerating.inc` は四状態Laurent重みの係数を実端点・費用の語数へ同定し、有理母関数を得る。 |
| H | 面積を加えると、接合に外積の交差項が現れる。交差項はコサイクル条件を満たす。 | `HistorySignature.inc` の実積分分割則と `CurveWordAlgebra.inc` の代数則に加え、`CurveWordPiecewise.inc` が任意語の実面積を整数交差項と固有面積の和へ同定する。 |
| I | 3A3B の20語は終点では12状態、面積までなら20状態になる。 | `CurveWordFinite.inc` の有限例・全列挙に実装。面積差は文字固有面積が同数で相殺することを使う。 |
| J | 4A4B の70語は面積まででも50状態。特定の衝突は三次モーメントで分かれる。 | `CurveWordFinite.inc` の整数衝突と `CurveWordCircularMoment.inc` の実積分を、`CurveWordCircleWords.inc` がBoolean語から作った同じ曲線上で接続する。 |
| K | Chen の接合則と、全 signature による tree-like 同値までの一意性。 | 一般連続BVの全次数Chen・shuffle・canonical署名と、実任意語の回転付きChenを証明。`CurveWordTreeLimit.inc`・`CurveWordBVHamblyLyons.inc` が独立な高さ条件によるtree-like性⇔全署名自明を証明し、`CurveWordBVEquivalence.inc` が実際の接合・反転による二曲線同値へ接続する。`CurveWordBVCoordinates.inc` で任意有限次元実ノルム空間へ核定理を転送する。 |
| L | 相似倍率に応じて変位・曲げ費用・面積・高次積分の次数が変わる。 | 状態・円弧・分配関数・任意次数の空間相似に加え、`CurveWordReparametrization.inc` がC1時間変換の全署名不変性、`CurveWordBoundedVariation.inc` が一般連続BV曲線の変動量時計と1-Lipschitz因子化を証明する。 |
| M | 全 signature の形式的対数は、次数で完備化した自由リー代数に入り、接合は BCH 級数で記述される。 | 形式指数の全次数逆、通常の交代冪対数との一致、group-like対数のprimitive性、有限文字集合での実自由Lie元の次数別展開とBCH接合を証明。`CurveWordBVAlgebra.inc` で一般BV署名へ接続する。 |

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
- AAAABBBB/AAABBBBA は終点・総角・費用・面積が同じです。`CurveWordCircleWords.inc` はBoolean語から構成した実曲線を明示円周列へ同定し、その曲線上で実面積の一致と、三次モーメントの差「AAABBBBA − AAAABBBB」$=-32h^3/(9\pi^2)$ を証明します。

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

を定めると、$m-\log N/\beta\le q\le m$ です。この零温度極限は固定した有限集合 $W$ に対するもので、語長を無限にする極限とは別です。一般有限状態模型の長語極限は転送行列から別に証明し、その極限値の零温度極限へ接続しています。固定した $\beta$ で全 u の Z を厳密に知ることは、有限測度のラプラス変換を知ることに対応します。復元対象は各終点 z の重み

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

全署名はすべての反復積分を並べた形式級数です。一般のChen公式は実曲線の接合をテンソル代数の積へ送ります。この円弧文字模型では、後半の曲線の増分を前半の総角だけ回転させてから接ぐので、その回転の各次数テンソル作用も含めて証明しています。

有限次元実ノルム空間に値を取る、コンパクト区間 $[a,b]$ 上の連続有界変動曲線について、**全署名が単位であることと幾何学的なtree-like性の同値**を証明しました。単位署名は空語の係数が1、すべての非空語の係数が0です。tree-like性は署名を使わず、連続な非負高さ $h$ が $h(a)=h(b)=0$ と

$$
d(\gamma(s),\gamma(t))\le h(s)+h(t)-2\min_{r\in[s,t]}h(r)
\qquad(a\le s\le t\le b)
$$

を満たすこととして定義しています。一般の連続BV曲線の署名は実Stieltjes積分から定め、Jordan対・区間外の延長・連続単調時計の選択に依存しないことも証明済みです。

`CurveWordBVHamblyLyons.treeLike_iff_pathSignature_eq_unit` が有限座標空間での核定理、`CurveWordBVCoordinates.finiteDimensionalSignature_eq_unit_iff` が実際の有限基底を通じた一般有限次元実ノルム空間版です。座標を変えると個々の署名係数は変わりますが、「全署名が単位」という性質は座標に依存しません。

二曲線版 `CurveWordBVEquivalence.based_pathSignature_eq_iff_tree_equivalent` は、同じコンパクト区間を持つ有限座標空間の連続BV曲線で、始点が同じときに、**署名の一致⇔終点の一致かつ一方を進み他方を逆に戻る実接合曲線がtree-like**と述べます。終点の一致は署名の一次係数から導きます。これは[Hambly–Lyons の既知定理](https://annals.math.princeton.edu/2010/171-1/p02)に対応する形式命題であり、外部の定理を公理として取り込んだものではありません。パラメータ時刻やtree-likeな往復そのものを復元する主張ではありません。

全署名の形式的対数は、厳密には**次数で完備化した自由リー代数**の元です。有限次数で打ち切った対数と、無限の形式級数である全対数は区別します。

$$
\log\operatorname{Sig}(\gamma)
=z_xX+z_yY+A_{\rm signed}[X,Y]+\text{三次以上}.
$$

接合と BCH の全次数等式は `signature_logarithm_chen`、対数署名の実自由Lie元による次数別展開は `signature_logarithm_completed_lie` に対応します。形式指数の両側逆と通常の交代冪対数との一致、group-like対数のprimitive性を証明し、有限文字集合について各次数のLie元を実際に構成しています。ここで保証するのは次数別の係数展開であり、自由Lie代数からテンソル代数への写像の単射性やPBW同型を追加したという意味ではありません。幾何学的なHambly–Lyonsは、この代数結果とは別に実曲線・最小代表・内部距離を構成して証明しています。原文が示した [Chen identity・log-signature の参照先](https://link.springer.com/chapter/10.1007/978-3-031-97239-3_1)も保持します。

相似倍率 $\sigma>0$ では、変位は $\sigma$、二次曲げ費用は $\sigma^{-1}$、面積は $\sigma^2$、m 次反復積分は $\sigma^m$ 倍です。原文の

$$
J^{(\sigma h)}_u=\sigma^{-1}J^{(h)}_{\sigma^2u},\qquad
Z^{(\sigma h)}_n(u,\beta)=Z^{(h)}_n(\sigma^2u,\beta/\sigma)
$$

は入力と温度も一緒に変換する式です。同じ数値入力を固定したまま、異なる大きさの模型を同一視するものではありません。

## 適用境界と検証の読み方

第一段階の後に[解析・最適化の追補](continuation.md)、さらに[全次数・一般極限への拡張](extensions.md)を加えました。`continuation.md` はPR #129時点の到達点を残す歴史記録です。現在のA〜M対応と一般HLの完成範囲は、このREADMEと `extensions.md` を参照してください。次の追加主張は今回の完成範囲に含めません。

- 曲率の跳びを持つ接合部を滑らかに近似する構成と、元の拘束付き変分問題での性質。単一のC1曲線・状態・面積・円周列との同定は追加済み。
- 一般のmin-plus行列べきとの表記上の同定、および仮定を追加しない二重極限の交換。一般有限グラフの平均閉路、長語のスペクトル極限、その後の零温度極限は追加済み。
- 一般の Fenchel–Moreau 定理。指数可積分性の下での有限測度のラプラス一意性と終点測度への適用は追加済み。
- 無限次元空間・不連続BV曲線・粗い経路への同じ一意性定理の拡張。ここで完成したHLは、任意有限次元実ノルム空間の連続BV曲線を対象にします。
- 曲線の停留性から独立した時間発展・履歴選択・自己増殖の法則。

`LinearInputHistorySignature.finite_family_separating_cutoff` は、異なる二対象がある段で区別できるという仮定の下で、有限族に共通の識別段数を与えます。その仮定を証明せずに、全署名の一意性や任意長の語の識別へ読み替えることはできません。

共通検証入口はリポジトリ直下の `python -B -X utf8 tools/verify.py --integration-only` です。結果は対象ソース・依存 revision・実行ログに結び付けて報告します。今回の全次数・一般極限・HLの根拠は各形式証明であり、有限検算の成功から一般命題を推測したものではありません。過去の成功記録は今回の実行結果として数えません。
