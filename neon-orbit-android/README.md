# NEON ORBIT — ネオン重力アーケード

指をホールドすると重力の中心が生まれ、ドラッグで青い球を操縦する、Android向け一画面アーケードゲーム。

- 60秒のスコアアタック。星を回収してコンボをつなげると得点倍率が最大8倍。
- オレンジの時計で残り時間+5秒、紫のFEVER星で5秒間の得点2倍。
- 赤い機雷を避ける。接触でライフ-1、少しの無敵時間。ライフ3個。
- 回収数に応じて機雷が増加。再挑戦しながらハイスコアを更新。
- パーティクル、残像、重力リング、効果音（オン/オフ）、触覚フィードバック。
- Android 8.0以上。オフライン、広告なし、ログイン不要、個人情報収集なし。

## Controls

スタート→画面上を長押し・ドラッグ。青い球が指に引き寄せられます。画面上部のIIで一時停止、SFXで効果音を切り替え。終わったらRETRY。

## Build

JDK17 / Gradle 8.9 / Android SDK 35。

```sh
cd neon-orbit-android
gradle :app:assembleDebug
# app/build/outputs/apk/debug/app-debug.apk
```

CI uses GitHub Actions on `app/neon-orbit-android`, producing a downloadable debug APK artifact.

### Independent physics check

```sh
mkdir -p /tmp/neon-test
javac -d /tmp/neon-test app/src/main/java/com/primitive/neonorbit/OrbitPhysics.java tests/OrbitPhysicsTest.java
java -cp /tmp/neon-test OrbitPhysicsTest
```

This is a small, deliberately self-contained native Java Android game (one Activity and a custom Canvas View, no third-party runtime libraries, no permissions). High scores and sound preferences stay on the device in SharedPreferences.
