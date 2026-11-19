# 三球衝突：自由間隙モデルの Lean 形式化と速度定理への接続

## 位置づけ

[三球衝突の再投入検証](2026-11-14-three-ball-position-reentry.md) は、半径の等しいハード球が正で相異なる自由間隙 \(a,b\) から等速飛行するとき、既存の `ThreeBallCollision.lean` の LRL／RLR の衝突順が実際に起こることを手計算と Python の Fraction で確かめ、「自由間隙模型の Lean 形式化と既存 Lean 速度定理との接続」を未証明としていた。この追加はそれを形式化する。

- Lean：[lean/ThreeBallFreeFlight.lean](../../lean/ThreeBallFreeFlight.lean)（名前空間 `ThreeBallFreeFlight`、9定理）。`ThreeBallCollision` を import し、衝突写像 `collideLM`・`collideMR` と終速度 `leftFirst`・`rightFirst` をそのまま使う。元のファイルは変更しない。
- 独立検算：[tests/test_three_ball_free_flight.py](../../tests/test_three_ball_free_flight.py)
- 専用CI：[.github/workflows/three-ball-free-flight.yml](../../.github/workflows/three-ball-free-flight.yml)

## モデル

状態は左右の自由間隙 \(g_L=x_M-x_L-2\rho\)、\(g_R=x_R-x_M-2\rho\)、速度、時計の組（`State`）。飛行中は \(\dot g_L=v_M-v_L\)、\(\dot g_R=v_R-v_M\)（`rateL`、`rateR`）。`outcome` が次の事象を決める：

- `separated`：どちらの間隙も閉じつつない。以後接触は起こらない（`separated_gaps_never_close`、`outcome_separated_iff`）。
- `simultaneous`：両方が同時に閉じる。二体衝突則では未規定なので、ここでモデルを止める。
- `contact side τ`：`side` の間隙が先に、時間 `τ` 後に閉じる。

`advance` は時間 `τ` 自由飛行してから、その側に既存の二体衝突写像を適用する。接触までの飛行中、両方の間隙は非負のまま（`flight_gaps_nonneg`、`contact_time_le`）。

## 結果

| 内容 | Lean 宣言 |
|---|---|
| \(0<a<b\)、\(d=b-a\)：接触は L, R, L、時刻 \(a,\ a+3d/5,\ a+6d\)、そのときの他方の間隙 \(d,\ 3d/5,\ 9d\)、その後 `separated`、終速度は `leftFirst` | `left_first_schedule` |
| \(0<b<a\)、\(d=a-b\)：接触は R, L, R、同様の時刻と間隙、終速度は `rightFirst` | `right_first_schedule` |
| 等しい間隙では同時接触（未規定） | `equal_gaps_simultaneous` |
| 中央の終速度は \(a<b\) で \(-10/27\)、\(b<a\) で \(10/27\)：\(a-b\to0\) で極限を持たない | `middle_velocity_jump` |
| 最終衝突時刻は両側とも \(\min(a,b)+6\lvert b-a\rvert\) | `final_time` |

各遷移は `step` の値として、状態（間隙・速度・時計）の等式で述べている。速度は元ファイルの `collideLM initial` などの合成そのものなので、既存の `left_first_exact`・`right_first_exact`（\((-13/27,-10/27,11/9)\) と \((-11/9,10/27,13/27)\)）や保存則の定理がそのまま適用できる。

## 実行された検証

2026-11-19、クラウドコンテナ上で実行した（Lean `v4.36.0-rc2`、mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`）。

- `ThreeBallCollision.lean` を `-o` で出力したのち `lake env lean --trust=0 ThreeBallFreeFlight.lean`：終了コード0、`error:`・`warning:`・`sorryAx` なし。全9定理の使用公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内。
- `python -B tests/test_three_ball_free_flight.py`：3テスト合格。間隙ではなく球の中心座標を進める別実装のイベント駆動シミュレーションで、500組を超える相異なる正有理数 \((a,b)\) について、衝突順・時刻・他方の間隙・終速度・運動量・エネルギーが上の閉形式に一致することを確認。

GitHub Actions の結果はこの記録の時点では未確認であり、専用CIの完了を別途確認する。

## 論理的境界

1. 仮定：等半径の剛体球、正で相異なる初期間隙、等速の自由飛行、瞬間的な完全弾性二体衝突。摩擦・外力・変形・有限接触時間は含まない。
2. 同時三体衝突（\(a=b\)）の力学は構成しない。
3. Lean の `left_first_schedule` 自体は代数的に \(a<b\) だけを使う。\(0<a\) は初期間隙が非負という物理的な前提として仮定に残している。
