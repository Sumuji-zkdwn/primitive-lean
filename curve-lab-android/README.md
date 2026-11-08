# 曲線実験室 / Curve Lab for Android

完全オフラインで動く、指描きの接線・内在高さ・符号付き曲率の観測器です。Android 8.0 (API 26) 以降。

- 「描く」：指で曲線を何本でも重ねて描く（24本まで）。起動直後はサンプル曲線を表示。
- 「観測」：曲線をなぞると、基準点の接線（橙）、左法線（水色）、基準点（白）を表示。
- 上段グラフ：基準点の左法線から測った高さ `H(s)`。下段グラフ：符号付き曲率 `κ(s)`。
- 基準点について、`H(0)=H'(0)=0`, `H''(0)=κ(0)` を有限差分で比較。基準点の座標は画面 dp、曲線は弧長でパラメータ化。
- CSV 保存：各点の弧長、x、y、曲率、および選択した曲線の基準点からの高さ。
- PNG 保存：描画キャンバスとグラフを一枚に保存。保存先は Android 標準のファイル選択画面で決定。
- 元に戻す／全消去、画面回転時の作業状態保存。

## Build

JDK 17、Android SDK 35、Gradle 8.9 が必要です。アプリ本体は Java、Android framework だけで構成されています（広告、トラッキング、ネットワーク権限なし）。

```sh
# Repository root if stored under curve-lab-android/
cd curve-lab-android
gradle :app:assembleDebug
# Output: app/build/outputs/apk/debug/app-debug.apk
```

GitHub Actions では `app/curve-lab-android` ブランチへの push 時にビルドされ、`curve-lab-android-apk` アーティファクトで APK を公開します。

## Independent geometry checks

```sh
mkdir -p /tmp/curve-test
javac -d /tmp/curve-test app/src/main/java/com/primitive/curvelab/Geometry.java tests/GeometryTest.java
java -cp /tmp/curve-test GeometryTest
```

直線のゼロ曲率、円弧の `κ≈1/R`、`H''≈κ`、逆順の符号反転、平行移動不変性を検査します。

## Numerics

入力ストロークは約5dpごとにサンプリングし、二回の局所的な二項平滑化後、三点の外接円による符号付き曲率を計算します。数値二階微分は非等間隔の弧長ステップを用います。離散近似なので非常に短い線や折れ点では誤差が大きくなります。曲率は `dp^-1`、画面表示は読みやすいよう `100dp × κ` と `100dp × H''` を表示します。

本アプリは特定の既存理論に属する高度な定理を証明するものではなく、滑らかな正則曲線における接線座標系の局所微分幾何を可視化する最小実験器です。
