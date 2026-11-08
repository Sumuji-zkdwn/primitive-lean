# SPORE POP / 連鎖培養ゲーム

Android / iPhone / browser で遊べる、1本指のオフライン連鎖爆発ゲーム。

## ゲーム
- 画面をタップすると、微生物を巻き込む衝撃波が発生する
- 微生物が破裂すると新しい衝撃波が生まれ、連鎖する
- 少ないタップでクリア条件数を開花させると次のステージへ
- ピンクは広い爆発、金色は特大爆発＋タップ回復、青は小さめの爆発、紫は高得点
- ステージ制、ZENモード、ハイスコアと進行状況の保存、効果音・消音
- 画像も音も動的生成。外部API、広告、トラッキング、通信権限なし

## すぐ遊ぶ

`Web/index.html` を静的サイト（HTTPS）へデプロイするとPWAとしてホーム画面追加可能。
`SPORE-POP-iPhone-Play.html` はCSS・JavaScriptを1ファイルにまとめた持ち運び版。

## Android

`android` ディレクトリで `gradle :app:assembleDebug` 。Android 8.0 / API 26 以降。
Android WebViewでWebアセットをローカルに読み込むため、ネット接続は不要。
Debug APKはGitHub Actionsから取得。Play Store署名は行っていない。

## iOS

`ios/SporePop.xcodeproj` をXcodeで開いて、開発チームを選択し、署名して実機へ転送。
SwiftUI + WKWebViewでWebアセットをオフライン表示。iOS 16以降。
GitHub Actionsで `generic/platform=iOS Simulator` 向けの **署名なし** ビルド検証を行う。
署名なしアプリはiPhone実機へ直接インストール不可。

## 検査

- `node tests/engine.test.js` : ステージ生成、衝突、得点、壁反射
- `python tests/smoke.py` : Chromiumのモバイルビューで操作・画面・JavaScriptエラーを検証

No third-party dependencies in the game itself. Java, Swift wrappers are thin offline viewers.
