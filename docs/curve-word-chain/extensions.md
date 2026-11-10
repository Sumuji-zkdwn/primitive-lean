# 曲線文字チェインの全次数・一般極限・幾何学的一意性

PR #128・#129 の原稿を保持し、その時点で残っていた曲線の構成、一般の有限グラフ、ラプラス一意性、スペクトル極限、全次数署名を接続した。連続BV曲線の一般Hambly–Lyonsも両方向を証明し、A〜Mの数学的核心に対応する形式定理をそろえた。本文では定理の仮定、実曲線と代数模型の対応、完成範囲に含まない追加主張を明示する。

最終のHL・二曲線同値・有限次元座標転送まで含む依存原稿は、個別の `lake env lean --trust=0` で終了コード0・警告0、公理監査は `propext`・`Classical.choice`・`Quot.sound` のみとなった。[verification-extensions.md](verification-extensions.md) は43ファイル時点のクリーンな全26段階検査の記録として保持し、登録原稿とハッシュは [extension-provenance.json](extension-provenance.json) に記録する。最終原稿全体の共通組立・総合検査については完成検証記録を別途追加予定である。個別検査、総合検査、CI、mainへの統合はそれぞれ別の状態である。

## 一本の曲線と整数状態の同定

[CurveWordPiecewise.inc](../../linear_input/lean_check/CurveWordPiecewise.inc) は、長さ $h>0$ の A/B 円弧を任意の Boolean 語に従って接ぐ実数値接線角 `wordAngle` を再帰的に構成する。その角度から既存の `Elastica.xCoord`・`yCoord` により一本の曲線を作る。角度は継ぎ目で連続であり、曲線は連続な単位接線を持つ。曲率は継ぎ目で跳んでよい。

実座標の端点、持ち上げた実総角、曲率の二次費用、実符号付き面積を積分から評価し、文字状態の接合および整数評価に一致させる。代表的な接続は `reconstructedState_eq_integer_decode`、`reconstructedAreaState_eq_integer_decode`、`curve_area_integer_formula`。面積には各円弧の固有面積と、整数交差項 $D$ の $\xi^2D/2$ 倍の両方を含める。

[CurveWordCircleWords.inc](../../linear_input/lean_check/CurveWordCircleWords.inc) は、この実際の曲線と明示円周列を各時間区間で点ごとに同定する。AAAABBBB と AAABBBBA は、端点・実総角・曲げ費用が一致し、

$$
A_{\rm signed}=\frac{16h^2}{3\pi},\qquad
\left(\int x^2dy\right)_{\rm AAABBBBA}
-\left(\int x^2dy\right)_{\rm AAAABBBB}
=-\frac{32h^3}{9\pi^2}\ne0
$$

を満たす。`actual_curve_collision` は同じ曲線構成上の状態一致・面積一致・三次不一致を合わせる。6文字の例でも `six_word_same_state` と `six_word_actual_area_difference` により実状態の一致と実面積差を接続する。これは区分的に定曲率の許容曲線の構成であり、継ぎ目の平滑化や、元の拘束付き変分問題での停留性・最小性を付け加えない。

## 一般の有限グラフと最小平均閉路

[CurveWordGraphLimit.inc](../../linear_input/lean_check/CurveWordGraphLimit.inc) は、有限非空の状態・文字、全域遷移 $q'=\operatorname{next}(q,a)$、任意の実辺費用から最小平均閉路を構成する。鳩の巣原理で短い閉路を取り出し、閉路除去で任意長の道の下界を与える。`minimum_simple_cycle_exists` は最小平均を達成し内部頂点が重複しない閉路の存在を証明する。補助関数や極限の存在を仮定しない。

始点 $q_0$ から全状態へ到達できる場合、実際の Bellman 最小値 $B_n(q_0)$ に対し

$$
\frac{B_n(q_0)}n\longrightarrow\mu
$$

を `bellman_average_tendsto` で証明する。到達できない閉路の平均を始点の極限に使うことはしない。

[CurveWordDirectedGraph.inc](../../linear_input/lean_check/CurveWordDirectedGraph.inc) は、頂点ごとに異なる有限非空の出辺型 `Out q` を持つ有向多重グラフを扱う。各頂点から実在する一辺ずつを選ぶ policy で語へ符号化し、実際の道への復号と長さ・終点・費用の保存を証明する。人工的な辺を追加せず、`minimum_closed_walk` と `optimum_average_tendsto` を導く。この符号化は最小費用を保存するためのものであり、policy の重複を数えた分配関数を元グラフの経路数と同一視しない。

## ラプラス一意性と長語自由エネルギー

[CurveWordLaplace.inc](../../linear_input/lean_check/CurveWordLaplace.inc) は、第二可算な完備実ノルム空間上の有限Borel測度について、各連続線形汎関数方向で原点近傍に指数可積分性があり、ラプラス変換が一致するなら測度が一致することを証明する。実一変量から複素母関数の解析接続・特性関数の一意性を経由する。有限語集合では

$$
\mu_\beta=\sum_{w\in S}e^{-\beta F_w}\delta_{z_w},\qquad
Z(u,\beta)=\int e^{\beta u(z)}\,d\mu_\beta(z)
$$

という実測度と実積分の等式を証明する。`endpointMeasure_eq_of_partition_eq` は固定した $\beta\ne0$ で全入力の分配関数が一致すると終点測度が一致することを与える。同じ終点に集約された語の費用内訳やラベルまでは復元しない。

[CurveWordSpectral.inc](../../linear_input/lean_check/CurveWordSpectral.inc) は、非負行列の行和増大を通常の複素スペクトル半径に接続する。Gelfand の公式と、到達可能性から得る行和・行列ノルムの一様比較により、非負既約行列 $M$ の任意の始点 $q$ について

$$
\frac1n\log\sum_j(M^n)_{qj}\longrightarrow\log\rho(M)
$$

を証明する。周期のある既約行列も含み、正の対角や非周期性を仮定しない。スペクトル半径を増大率そのものとして定義してはいない。

[CurveWordThermodynamics.inc](../../linear_input/lean_check/CurveWordThermodynamics.inc) の $m-\log N/\beta\le q\le m$ と $q\to m$ は、固定した有限非空集合の実最小値についての定理である。語長を増やす極限には別の証明が必要となる。[CurveWordTransfer.inc](../../linear_input/lean_check/CurveWordTransfer.inc) は、有限非空の状態・文字、全域遷移、到達可能性を持つ模型で、全長 $n$ 語の Boltzmann 和を転送行列の行和に厳密に一致させ、

$$
f_\beta=-\frac{\log\rho(M_\beta)}\beta,\qquad
\mu-\frac{\log|\mathcal A|}\beta\le f_\beta\le\mu,
\qquad f_\beta\longrightarrow\mu\quad(\beta\to\infty)
$$

を導く。`wordFreeEnergy_average_tendsto` はまず語長の極限を、`spectralFreeEnergy_zero_temperature` はその極限値の零温度極限を証明する。無条件の極限交換を述べるものではない。

[CurveWordGenerating.inc](../../linear_input/lean_check/CurveWordGenerating.inc) は実際の係数 $M^n$ から形式級数行列 $G(t)$ を作り、$(I-tM)G(t)=I$ を証明する。余因子行列から、各行和について定数項1の多項式分母 $D$ と多項式分子 $P$ を構成し、$DG=P$ を得る。[CurveWordWordGenerating.inc](../../linear_input/lean_check/CurveWordWordGenerating.inc) は任意の可換係数環で、実際の有限語の重み積の和を行列べきへ同定する。[CurveWordArcGenerating.inc](../../linear_input/lean_check/CurveWordArcGenerating.inc) は四状態A/B模型に適用し、整数のx・y指数と自然数の費用指数を持つモノイド環の単項式を使う。係数が実際の整数端点・費用を持つ語の個数そのものであり、その全語長母関数が上記の多項式分子・分母を持つことを証明する。

## 全次数 Chen・対数・自由 Lie・BCH

[CurveWordChen.inc](../../linear_input/lean_check/CurveWordChen.inc) の `signature_chen` と `signature_shuffle` は、連続速度の実反復積分について、任意の有限語に対する接合式と shuffle 式を証明する。同じ文字がある場合も shuffle の重複数を保持する。

[CurveWordLinearAction.inc](../../linear_input/lean_check/CurveWordLinearAction.inc) は任意の有限座標行列の各次数テンソル作用を有限和で定義し、実反復積分との可換性を証明する。平面回転を明示的な二行二列行列として代入する。[CurveWordWordSignature.inc](../../linear_input/lean_check/CurveWordWordSignature.inc) の `actual_word_signature_cons` は、任意語から実際に構成した同じ曲線に、後片の回転と時間原点の移動を含む全次数Chen式を接続する。

[CurveWordFormalSeries.inc](../../linear_input/lean_check/CurveWordFormalSeries.inc) は `List ι → ℝ` の全係数列を使い、各係数では有限の切り方の和で積を定める。正次数級数の形式指数 `formalExp` と、次数ごとの補正で構成する `logarithm` は全次数で互いに逆であり、指数の単射性も証明する。

$$
\operatorname{BCH}(A,B)=\log(\exp A\exp B)
$$

をこの実際の逆写像で定め、`formalExp_bch`、`bch_assoc`、`signature_logarithm_chen` を全係数の等式として証明する。二次では通常の $A+B+\tfrac12[A,B]$ の項になる。[CurveWordScalarLog.inc](../../linear_input/lean_check/CurveWordScalarLog.inc) と [CurveWordLogFormula.inc](../../linear_input/lean_check/CurveWordLogFormula.inc) は、スカラー形式級数の合成逆と次数ごとの多項式評価を使い、通常の交代冪和 `formalLog` と `logarithm` の全次数一致も証明する。

[CurveWordCoproduct.inc](../../linear_input/lean_check/CurveWordCoproduct.inc) は unshuffle coproduct の積保存と、group-like 級数の対数が primitive になることを証明する。[CurveWordFriedrichs.inc](../../linear_input/lean_check/CurveWordFriedrichs.inc) は Dynkin 作用素を単語上の入れ子交換子に同定し、有限文字集合について、primitive な級数の各次数に実際の `FreeLieAlgebra ℝ ι` の元を構成する。

`signature_logarithm_completed_lie` の結論は、$L_0=0$、各 $L_n$ は長さ $n$ の入れ子Lie括弧の線形包に属し、その係数展開が対数署名の次数 $n$ 成分に等しい、という全次数の存在証明である。有限次数で切った計算に留めず、次数の関数 $n\mapsto L_n$ を与える。自由Lie代数からテンソル代数への写像の単射性や PBW 同型は追加主張しない。

## 有界変動曲線の実署名と解析

[CurveWordBoundedVariation.inc](../../linear_input/lean_check/CurveWordBoundedVariation.inc) は、一般の距離空間に値を取る連続な有界変動曲線に、連続・単調・全射な変動量の時計を構成する。その時計が一定の部分では曲線も一定であることを示し、全長区間上の1-Lipschitz曲線へ因子化する。`arcLength_factorization_with_length` は合成による元曲線の回収と変動量保存を含む。

[CurveWordStieltjes.inc](../../linear_input/lean_check/CurveWordStieltjes.inc) は、連続BV座標の正負Jordan対から実Stieltjes測度を構成する。区間の外は端点の値で定数延長し、その連続性と有界変動を証明する。連続速度の場合には測度を `volume.withDensity` と同定し、`c1_stieltjesSignature_eq_signature` で全次数の既存反復積分に一致させる。特異なBV曲線を単に導関数の積分で置き換えない。

[CurveWordBVSignature.inc](../../linear_input/lean_check/CurveWordBVSignature.inc) は、署名の各係数の連続性と、Jordan対の選択独立性を証明する。`stieltjesSignature_independent` の仮定は全実数区間での座標増分の一致であり、署名自体の一致を仮定しない。この定理だけでcompact区間外の選択独立性を済ませず、以下の局所版へ接続する。

この局所的な接続を [CurveWordBVCanonical.inc](../../linear_input/lean_check/CurveWordBVCanonical.inc) で証明した。区間内の座標増分が一致する任意のStieltjes対との全次数一致を示し、曲線から直接 `curveSignature`・有限次元の `pathSignature` を定義する。区間外の変更に依存せず、連続単調な時計による再パラメータ化、C1反復積分との一致、弧長1-Lipschitz因子化での署名保存までをこの曲線APIで接続する。

[CurveWordBVReparam.inc](../../linear_input/lean_check/CurveWordBVReparam.inc) は、連続・単調な時計に平坦区間がある場合も、区間制限した測度の押し出しから全次数署名の不変性を証明する。[CurveWordBVChen.inc](../../linear_input/lean_check/CurveWordBVChen.inc) と [CurveWordBVShuffle.inc](../../linear_input/lean_check/CurveWordBVShuffle.inc) は一般の連続Stieltjes座標対で全次数Chen・shuffleを証明する。後者の積分部分積分は、無原子測度の積空間を二つの三角領域へ分けるFubiniの議論から導く。

[CurveWordBVAlgebra.inc](../../linear_input/lean_check/CurveWordBVAlgebra.inc) は、この一般BV署名のgroup-like性・対数のprimitive性・全次数の実自由Lie展開・BCH接合を接続する。[CurveWordBVTopology.inc](../../linear_input/lean_check/CurveWordBVTopology.inc) はBV署名像のコンパクト性と座標の一様稠密性を証明し、全署名が自明な場合の、署名像上の任意の連続係数を持つ実Stieltjes one-formの消滅へ拡張する。compact interval上のBV座標をStieltjes対へ表す存在証明と、対を受け取るこれらのAPIを、`CurveWordBVCanonical.inc` の表現独立性によって実曲線の署名へ接続している。

[CurveWordReparametrization.inc](../../linear_input/lean_check/CurveWordReparametrization.inc) は、連続な導関数 $g'$ を持つ時間変換について、Jacobianを含む速度 $g'(t)v(g(t))$ の署名が元の区間 $[g(a),g(b)]$ の署名と一致することを全次数で証明する。反転や、元の時刻へ戻る時間経路も含む。このC1命題と、一般の連続BV時間変換は区別する。

[CurveWordTreeLike.inc](../../linear_input/lean_check/CurveWordTreeLike.inc) では、tree-like を署名とは独立の連続高さ関数の距離不等式で定義する。閉曲線性、Lipschitz写像による保存、曲線と高さ関数の両方が一様収束する場合の保存、および1次元C1曲線の「自明な署名とtree-likeの同値」を証明する。

[CurveWordHeightMetric.inc](../../linear_input/lean_check/CurveWordHeightMetric.inc) は高さ関数 $h$ から $d_h(s,t)=h(s)+h(t)-2\min_{[s,t]}h$ を実際に構成する。距離ゼロを同一視した商がコンパクト・弧状連結なFourPoint距離空間になること、元曲線がその商上の1-Lipschitz写像を通じて回収されることを証明する。[CurveWordSignatureTree.inc](../../linear_input/lean_check/CurveWordSignatureTree.inc) はFourPoint距離空間の連続ループから独立の高さ条件を導く。以下の逆方向では、実署名経路から内部距離とFourPoint条件を構成して、この幾何定理の仮定を満たす。

[CurveWordSignatureBounds.inc](../../linear_input/lean_check/CurveWordSignatureBounds.inc) は実Stieltjes署名の $|S_w|\le V^{|w|}/|w|!$ を証明し、有限個の座標変動量から共通制御を構成する。[CurveWordSignatureUniform.inc](../../linear_input/lean_check/CurveWordSignatureUniform.inc) は一様な座標差が $\varepsilon$、両曲線の共通変動制御が $M\ge1$ 以下なら $|S_w-T_w|\le2|w|\varepsilon M^{|w|}$ を示し、一様収束と一様BV上界から全係数の収束を導く。差曲線の変動量の収束を追加仮定しない。

[CurveWordSignatureTopology.inc](../../linear_input/lean_check/CurveWordSignatureTopology.inc) は、実署名の像のコンパクト性、shuffleから得る座標代数の一様稠密性、自明な全署名なら署名像上の任意の連続係数の線積分が消えることを証明する。

## 一般Hambly–Lyons：高さ条件と全署名の同値

ここでtree-likeは署名に言及しない独立の条件である。曲線 $\gamma$ とともに連続な非負高さ $h$ を取り、$h(a)=h(b)=0$ と

$$
d(\gamma(s),\gamma(t))\le h(s)+h(t)-2\min_{r\in[s,t]}h(r)
\qquad(a\le s\le t\le b)
$$

を要求する。Leanの `HasTreeHeight` は区間内のある点を使う証人形式で定義し、連続高さが最小値を達成することから、この最小値表示と対応させる。

[CurveWordSamplingOrder.inc](../../linear_input/lean_check/CurveWordSamplingOrder.inc)・[CurveWordTreeSampling.inc](../../linear_input/lean_check/CurveWordTreeSampling.inc) は、有限高さ集合への最初・最後の到達時刻を選び、任意に小さい時間meshを持つ厳密単調な有限標本を実際に構成する。高さ商上の有限レベルの辺が非巡回になることを証明し、[CurveWordTreeSignature.inc](../../linear_input/lean_check/CurveWordTreeSignature.inc) で実直線区間の署名の往復消去へ接続する。[CurveWordPolygonal.inc](../../linear_input/lean_check/CurveWordPolygonal.inc) は実折れ線補間の連続性・変動量非増大・各辺署名の順序積との一致を証明する。[CurveWordTreeSampleProduct.inc](../../linear_input/lean_check/CurveWordTreeSampleProduct.inc) と [CurveWordTreeLimit.inc](../../linear_input/lean_check/CurveWordTreeLimit.inc) により、有限座標空間の連続BV曲線について **tree-likeなら全署名が自明** が成立する。退化区間 $a=b$ も含む。有限近似の存在を追加仮定として残さない。一般有限次元実ノルム空間への転送は後述の `CurveWordBVCoordinates.inc` が行う。

逆方向では [CurveWordBVSubinterval.inc](../../linear_input/lean_check/CurveWordBVSubinterval.inc) が、署名のfiber上で一定な連続時間係数を実署名像へ降ろし、部分積分と座標分散ゼロを使って実署名liftの非定数単純loopを排除する。自明な署名を持つ実BV曲線から、真に短い時間区間の自明な署名を持つ閉subcurveを取り出す。ただし任意の署名像内のarcを元曲線のsubintervalと同一視してはいない。

[Hambly–Lyonsの原論文](https://annals.math.princeton.edu/2010/171-1/p02)と、[署名像と線積分を使う2026年の参照先](https://arxiv.org/html/2609.12283v1)は参考文献として保持する。以下では実曲線の最小代表、署名像内の経路、内部距離を構成して逆方向も閉じている。これら外部文献の結論をLeanの公理として取り込まない。

### 逆方向：最小代表から実際の高さ関数へ

[CurveWordBVPathOperations.inc](../../linear_input/lean_check/CurveWordBVPathOperations.inc) は、実際の連続BV曲線の反転・二曲線の接合、その変動量、全次数のChen式と逆元を証明する。同じ署名を持つ二曲線について、一方を進みもう一方を逆に戻る実曲線の署名が自明になることを接続する。

[CurveWordBVCompactness.inc](../../linear_input/lean_check/CurveWordBVCompactness.inc) は有限時間区間上の1-Lipschitz曲線のコンパクト性、変動量の下半連続性、全署名係数の連続性を証明する。任意の閉署名集合内を進む実候補があれば、その集合内で端点署名を固定した変動量最小の実曲線を構成する。最小曲線の存在を仮定しない。

[CurveWordBVLoopErase.inc](../../linear_input/lean_check/CurveWordBVLoopErase.inc) は署名が自明な部分曲線を実際に削除し、残る全prefix署名を保つことを示す。非定数部分を削除すると変動量が厳密に減る。[CurveWordBVReduced.inc](../../linear_input/lean_check/CurveWordBVReduced.inc) はこの構成から、最小代表の等しいprefix署名で挟まれた区間では元曲線が一定であることを導く。

[CurveWordBVArc.inc](../../linear_input/lean_check/CurveWordBVArc.inc) は最小代表の弧長再パラメータ化を構成し、全prefix署名像が厳密に保存されること、得られる署名liftが単射であることを証明する。[CurveWordBVOrientation.inc](../../linear_input/lean_check/CurveWordBVOrientation.inc) は単調または反単調な実時計と、任意向きの部分区間に対する署名の対応を扱う。

[CurveWordBVArcUnique.inc](../../linear_input/lean_check/CurveWordBVArcUnique.inc) は、同じ始点と終点署名を持つ二つの実単射署名liftの像が一致することを証明する。一方が他方の像を外れるなら、閉集合への最初・最後の到達時刻を実際に取り、その二つの部分曲線を時間変更して接合する。この実BV曲線の署名liftが非定数単純loopとなることを示し、既存の単純loop排除と矛盾させる。任意の位相的arcを元の時間区間とみなす段階は使わない。

[CurveWordBVIntrinsic.inc](../../linear_input/lean_check/CurveWordBVIntrinsic.inc) は、閉じた署名集合 $K$ 内の二点を結ぶ**実際の大域1-Lipschitz座標曲線**を `Route` として定義する。各途中時刻の署名も $K$ に属する条件を持ち、費用は非負の所要時間とする。固定した時間上界の下で曲線と停止時刻を同時に最小化し、所要時間の最小値を達成する実経路を構成する。この最小時間から、基点より到達可能な署名の空間 `IntrinsicPoint` に実際の距離を定め、対称性・三角不等式・非退化性を証明する。最小経路の各部分も最小であることから、等長測地線と `intrinsicGeodesicSystem` を得る。一次係数への射影が1-Lipschitzであることも、実曲線の端点変位から証明する。

[CurveWordGeodesicTree.inc](../../linear_input/lean_check/CurveWordGeodesicTree.inc) は、実際の等長測地線があり、各三角形の一辺が他二辺の和集合に含まれる場合に、標準の四点不等式を導く。[CurveWordBVIntrinsicTree.inc](../../linear_input/lean_check/CurveWordBVIntrinsicTree.inc) は二つの実測地線の像の和集合を制約として最小代表を構成し、`CurveWordBVArcUnique.inc` の実単射署名liftの像の一意性から、第三辺がその和集合内にあることを示す。`intrinsic_fourPoint` は、閉じた $K$ と空語係数1の基点に対して、上で構成した内部距離がFourPoint条件を満たすことを証明する。「測地線が一意だから木である」という未証明の飛躍や、FourPoint条件そのものの仮定は残さない。

[CurveWordBVHamblyLyons.inc](../../linear_input/lean_check/CurveWordBVHamblyLyons.inc) は元の連続BV曲線を変動量時計で大域1-Lipschitz曲線へ因子化し、**すべての途中時刻の実署名**が保存されることを示す。そのコンパクトな署名像を $K$ に選び、上の内部距離空間への連続な閉liftを実際に構成する。一次係数の距離支配とFourPoint条件から高さ関数を得て、連続単調な時計で元の時間区間へ引き戻す。`treeLike_of_pathSignature_eq_unit` は、有限座標空間の連続BV曲線について **全署名が自明ならtree-like** を結論とし、`treeLike_iff_pathSignature_eq_unit` が両方向の同値をまとめる。最終定理の前提に、木への因子化・署名像のFourPoint性・最小代表の存在を置いていない。

### 二曲線同値と任意有限次元実ノルム空間

[CurveWordBVEquivalence.inc](../../linear_input/lean_check/CurveWordBVEquivalence.inc) は、空語以外の全係数が0であることと単位署名の一致を結び、実際の二曲線の接合・反転へ核定理を適用する。`based_pathSignature_eq_iff_tree_equivalent` の入力は、有限座標空間に値を取る同じ区間 $[a,b]$ 上の二つの連続BV曲線、$a\le b$、始点の一致である。結論は

$$
S(\gamma)=S(\eta)\quad\Longleftrightarrow\quad
\gamma(b)=\eta(b)\ \land\ \operatorname{TreeLike}(\gamma*\overleftarrow\eta).
$$

右辺の接合は `joinCurve b γ (mirrorPath η b)` という実曲線で、時間区間は $[a,2b-a]$ である。終点の一致は左辺の一次係数から導くので、同署名から出発する側の追加仮定ではない。終点が一致する一般の二曲線向けには `pathSignature_eq_iff_join_reverse_treeLike` も提供する。

[CurveWordBVCoordinates.inc](../../linear_input/lean_check/CurveWordBVCoordinates.inc) は、任意の有限次元実ノルム空間 $E$ の実際の有限基底と連続線形同型を使い、`finiteDimensionalSignature` を定義する。高さ条件は実作用素ノルムで高さを拡大して双方向に転送するので、Pi型の最大値ノルムに結果を限定しない。`finiteDimensionalSignature_eq_unit_iff` は任意の連続BV曲線 $\gamma:[a,b]\to E$ について

$$
S_E(\gamma)=1\quad\Longleftrightarrow\quad\operatorname{TreeLike}(\gamma)
$$

を証明する。`signature_triviality_coordinate_independent` が保証するのは「全署名が単位であること」の座標独立性であり、座標を変えた後の個々の係数が同じという主張ではない。二曲線版の公開定理は有限座標型で述べ、一般 $E$ の署名はこの明示した座標APIを通じて扱う。有限次元・連続・有界変動の条件を外した一意性定理までは述べない。

最終の数学原稿は依存込みの個別Lean検査を通過している。43ファイル時点のクリーンな総合検査は [verification-extensions.md](verification-extensions.md) に固定し、最終原稿全体の共通検証には別の完成検証記録を追加予定である。[extension-provenance.json](extension-provenance.json) のハッシュを対応するログと照合し、前段階の成功を未検査の版へ持ち越さない。

## 有限終点集合の凸包による忘却

[CurveWordConvexObservation.inc](../../linear_input/lean_check/CurveWordConvexObservation.inc) は、有限非空の実線形空間内の集合 $S$ と線形観測 $L$ について、$\min_{z\in S}(F-Lz)=F-\max_{z\in S}Lz$ を証明し、同じ最小値が実際の $\operatorname{conv}(S)$ 上でも元の点で達成されることを示す。凸包が一致する二集合は全線形入力で同じ最小値を与える。一般Fenchel–Moreauの定理を仮定せず、原文Fの有限集合の忘却機構を直接証明する。

[CurveWordConvexSeparation.inc](../../linear_input/lean_check/CurveWordConvexSeparation.inc) は実ノルム空間で逆方向も証明する。有限集合の凸包がコンパクトであることと、実際のHahn–Banach分離から、全連続線形入力での同費用最小値の一致と凸包の一致が同値になる。

原文Fに関連する一般Fenchel–Moreau、接合部の平滑化、変分的停留性からの独立した時間発展・履歴選択も、この追補で暗黙に証明されたことにはしない。
