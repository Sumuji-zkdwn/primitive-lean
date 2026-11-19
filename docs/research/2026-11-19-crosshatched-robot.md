# 格子寸法の復元と円弧列の閉路長

研究ログ「外部数学の鉱脈探索」で取り上げた二題を、第8章の観測と曲線文字に接続する。原題は格子内の矩形の総数と、72度ずつ曲がるロボットの70歩の帰路数を問う。ここでは格子寸法の逆問題と、角度を変えた場合の閉路長の存在条件を扱う。[Project Euler 147](https://projecteuler.net/problem=147)・[Project Euler 208](https://projecteuler.net/problem=208)

## 二種類の斜め矩形

縦横が正整数 $m,n$ の格子で各マスに両対角線を引く。座標を二倍すると、交点は二座標の偶奇がそろう点になる。右上・右下に沿った最小の一刻みを単位として、辺長 $1,1$ の矩形を $C_2$、辺長 $1,2$ と $2,1$ の矩形を合わせて $C_3$ と数える。四頂点の格子内条件を外接箱の座標と偶奇条件に書き換え、その座標を偶奇ごとに全単射で数えると

$$
C_2=2mn-m-n,\qquad C_3=4(m-1)(n-1).
$$

したがって $2(m+n)=2C_2+4-C_3$、$2mn=C_2+m+n$ である。和と積が分かれば二辺は順序を除いて決まる。Lean では $m\le n$ を選び、二つの観測を組み合わせる既存の `joint_injective_iff` にこの復元を適用した。[四頂点・二つの計数・寸法復元](../../linear_input/lean_check/CrosshatchedRecovery.inc)・[観測の単射性](../../linear_input/lean_check/FiniteObservationSeparation.inc)

| 寸法 | $C_2$ | $C_3$ |
|---|---:|---:|
| 1 × 8 | 7 | 0 |
| 2 × 3 | 7 | 8 |
| 2 × 5 | 13 | 16 |
| 3 × 3 | 12 | 16 |

上の二行は $C_2$ だけで、下の二行は $C_3$ だけで観測したときの衝突である。[具体例 `first_count_collision` と `second_count_collision`](../../linear_input/lean_check/CrosshatchedRecovery.inc#L153)

## 左右の円弧列が原点に戻る条件

弧長 $h>0$ を固定し、左右に $2\pi /N$ だけ曲がる円弧を端の接線をそろえてつなぐ。向き $i$ と $i+1$ の間をどちらに渡っても、変位は同じ複素弦ベクトルである。したがって全変位は、向きの各辺の通過回数を係数とする1の冪根の和に、最初の一歩の弦ベクトルを掛けたものになる。[円弧の積分と通過回数](../../linear_input/lean_check/RobotWalkArc.inc)

素数 $q$、整数 $b\ge 1$ に対して $N=q^b$ とする。終点が原点であることは、通過回数が $d=N/q$ ごとに反復することと同値である（`closed_iff_periodic`）。閉じた語では接線の向きも元に戻る（`facing_of_closed`）。ここでの方位の一致は、実数で表した累積回転角 $\theta$ に対して $e^{i\theta}=1$ となることを指す。[円分多項式と周期](../../linear_input/lean_check/RobotCyclotomic.inc)・[位置と向きの定理](../../linear_input/lean_check/RobotWalkClassification.inc)

$q$ が奇素数のとき、正の歩数 $n$ で閉じられる条件は、ある整数 $t\ge 0$ について

$$
n=N+2qt\quad\text{または}\quad n=2N+2qt
$$

となることである（`closed_length_iff`）。必要性では、空でない歩行が向きの全辺を通ることと、各辺の通過回数の偶奇がそろうことを使う。十分性では、往復を挟んだ一つの語を回転させながら $q$ 回つないで、両系列の語を構成する。$b\ge 2$ で $N$ の倍数にならない最短の閉路長は $N+2q$ となる（`least_nonmultiple`）。[全辺の通過と歩数](../../linear_input/lean_check/RobotWalkSupport.inc)・[閉路の構成](../../linear_input/lean_check/RobotWalkLengths.inc)・[分類と最短性](../../linear_input/lean_check/RobotWalkClassification.inc)

例えば $N=9$ では `+-++++-++++-+++` の15歩で帰還する。この語の累積回転角はちょうど $2\pi$ で、終点と接線の向きがともに初期値に戻る。[具体的な円弧列と証明](../../linear_input/lean_check/RobotWalkArc.inc)

## 再現

リポジトリのルートで次を実行する。Lean の検証には既存の移行履歴も使うため、Git の履歴を含む通常のクローンを用いる。

```powershell
python -B -X utf8 tools/check_crosshatched_robot.py
python -B -X utf8 tools/verify.py --proof-only
```

最初のコマンドは回転座標で四頂点を直接検査し、$1\le m\le n\le 12$ の78格子で計数式と復元を確認する。ロボットでは9乗根の関係を整数係数で扱い、1〜18歩の全524,286列を調べる。閉じた列は9歩に2列、15歩に10列、18歩に20列ある。二つ目のコマンドは登録された Lean 原稿を組み立て、定理と公理依存を検査する。[有限列挙の実装](../../tools/check_crosshatched_robot.py)
