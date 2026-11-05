# 質量1–2–1の三球衝突：接触順序と履歴の忘却

2026-11-05。独立したLean原稿：[ThreeBallCollision.lean](../../lean/ThreeBallCollision.lean)。厳密分数による独立回帰テスト：[test_three_ball_collision.py](../../tests/test_three_ball_collision.py)。

## モデル

一直線上の三球の質量は (1,2,1)、初期速度は (1,0,-1)。速度状態を \(v=(l,m,r)\in\mathbb Q^3\) とする。二体の完全弾性衝突規則を、次の写像として定義する。

\[
L(l,m,r)=\left(\frac{-l+4m}{3},\frac{2l+m}{3},r\right),
\qquad
R(l,m,r)=\left(l,\frac{m+2r}{3},\frac{4m-r}{3}\right).
\]

運動量と二倍の運動エネルギーを

\[
P(l,m,r)=l+2m+r,\qquad K_2(l,m,r)=l^2+2m^2+r^2
\]

と定義した。lm_preserves_momentum、mr_preserves_momentum、lm_preserves_energy、mr_preserves_energy は、**すべての有理数速度状態**について各衝突写像がこの2量を保存することを証明する。さらに、各二体衝突の相対速度が反転することも証明する。

## 逐次履歴

左先行では L → R → L（合成として \(L\circ R\circ L\)）。

| 段階 | 左 | 中央 | 右 |
|---|---:|---:|---:|
| 初期 | 1 | 0 | −1 |
| L | −1/3 | 2/3 | −1 |
| R | −1/3 | −4/9 | 11/9 |
| L | **−13/27** | **−10/27** | **11/9** |

右先行では R → L → R（合成として \(R\circ L\circ R\)）。

| 段階 | 左 | 中央 | 右 |
|---|---:|---:|---:|
| 初期 | 1 | 0 | −1 |
| R | 1 | −2/3 | 1/3 |
| L | −11/9 | 4/9 | 1/3 |
| R | **−11/9** | **10/27** | **13/27** |

各段階の相対接近速度、および最終段階での離反方向の速度順序もLeanで確認する。ただし、位置・半径・連続時間の衝突時刻方程式までは形式化しない。

## Leanで証明する結論

1. impacts_do_not_commute：初期状態で \(L(R(v))\ne R(L(v))\)。
2. middle_velocity_jump：中央球の二つの終速度差は厳密に \(20/27\)。
3. same_conserved_observations：異なる二つの終状態は運動量と運動エネルギーの両方が一致する。
4. no_history_free_middle_predictor：初期速度だけを見る一つの決定的関数で、左先行と右先行の両終速度を同時に予測することはできない。
5. middleByOffset：左先行を正、右先行を負とした有理到着時刻差 \(\varepsilon\) により正負でそれぞれ \(-10/27\)、\(+10/27\) を返す。厳密な \(\varepsilon=0\) は none（未規定）とする。
6. jump_persists_arbitrarily_close：任意の有理数 \(\delta>0\) に対して \(0<\varepsilon<\delta\) である \(\varepsilon=\delta/2\) を選べ、正負の微小時間差による終速度の相違は変わらない。

これは**完全同時衝突に一意な解が存在しないという証明ではない**。指定した二体逐次衝突モデルを正負から同時接触へ近づけた場合の不連続性である。接触時間、弾性変形、三体接触則を追加した現実系の振る舞いとは区別する。

## 既存の理論との関係

運動量とエネルギーを保存しながら局所演算の合成順序だけで観測終値が分岐する、具体的な独立モデルである。既存の ShearCommutator.inc（非可換な操作）、OperatorWordObservations.inc（演算語の観測）、BranchForgetting.inc（忘却）との**構造的比較**が可能。ただし、その三ファイルとの間のLean定理の直接的な同一視やインポートは、このPRでは行っていない。

## 再検証手順

Leanディレクトリで lake env lean --trust=0 ThreeBallCollision.lean を実行する。リポジトリ直下で python tests/test_three_ball_collision.py -v を実行する。自動検証の入口は [.github/workflows/three-ball-collision.yml](../../.github/workflows/three-ball-collision.yml)。

原稿末尾の #print axioms は主要な証明が利用する公理を表示する。GitHub Actionsの成功・失敗はこの文書の記載だけから判断せず、実行コミットとログで判断する。
