# NEON ORBIT — iOS edition

A native iOS port of the Android NEON ORBIT neon-gravity arcade, plus an offline-ready iPhone web app. It is a one-finger 60-second arcade game, **not** a curve/physics research tool.

## What is included?

- `NeonOrbit.xcodeproj`, `NeonOrbit/GameScene.swift`, `NeonOrbit/GameCore.swift`, `NeonOrbit/NeonOrbitApp.swift`: native Swift 5 / SpriteKit / SwiftUI iOS game, iOS 16+.
- `Web/index.html`, `Web/game.js`, `Web/styles.css`, `Web/manifest.webmanifest`, `Web/sw.js`, `Web/icons/`: installable, offline-capable PWA for Safari on iOS 16+, or any modern browser.
- `Tests/main.swift`: portable deterministic physics/scoring tests, running on Linux or macOS.
- `.github/workflows/build-ios.yml`: verified CI pipeline that builds an unsigned **iOS Simulator** `.app`. It does not sign for real devices.

## Game rules

Hold your finger and drag to create a gravity target that attracts the blue ball. Collect gold stars for 100 points, clock pickups for +5s (150 base points), and pink stars for 5 seconds of FEVER at double points (150 base points). Stars collected within 4 seconds build a combo up to ×8. Mines cost one of three lives and grant brief invincibility; hitting five pickups adds a mine (max 7). Time normally starts at 60s; pause/resume, high scores, and sound preference are saved locally. No accounts, network permissions, analytics, ads, or external libraries.

## Play on an actual iPhone without an Apple developer account

Open the **hosted HTTPS version** of `Web/index.html` in Safari, tap Share (共有) > Add to Home Screen (ホーム画面に追加). The service worker caches files on first visit; offline behavior requires a successful first visit and browser support.

A static server can host the `Web/` directory. For local testing on a Mac: `cd Web && python3 -m http.server 8080`, then visit from Safari on the same network via your Mac's LAN IP address. Local HTTP outside `localhost` does not permit service workers; HTTPS is needed for install/offline caching.

A single-file HTML version is shipped separately as `NEON-ORBIT-iPhone-Play.html`, for browser preview, but on iOS using a hosted HTTPS URL is much more reliable than opening a local file through Files.

## Install the native app on a real iPhone

An iPhone **cannot** install an unsigned `.ipa` or an iOS Simulator app by tapping a download link. Native apps require Apple code signing and provisioning; we do not have the user's signing identity.

On a Mac, open `NeonOrbit.xcodeproj` in Xcode 16+ (newer Xcode versions are fine), choose the `NeonOrbit` target > Signing & Capabilities > your Personal Team or Apple Developer team, change the bundle identifier if necessary, select a connected iPhone and press Run. Apple account, provisioning and device trust requirements apply.

## Build & test

Pure game-core verification (Linux or macOS):

```sh
swiftc NeonOrbit/GameCore.swift Tests/main.swift -o /tmp/neo-test
/tmp/neo-test
```

Simulator app (macOS + Xcode):

```sh
xcodebuild -project NeonOrbit.xcodeproj -scheme NeonOrbit \
  -destination 'generic/platform=iOS Simulator' \
  CODE_SIGNING_ALLOWED=NO build
```

PWA: no dependencies. `Web/index.html` can be hosted by a static server; the JavaScript and styles are local. This project does not automatically publish a website. If you publish the Web folder, it must be served over HTTPS for offline installation.

## Parity / limitations

The attraction, drag, max speed, wall bounce, pickup radius, four-second combo, fever multiplier, collision and damage rules match the Android implementation. Audio and visual effects are implemented with iOS APIs in the native version, and Web Audio/Canvas in Safari. The iPhone layout respects its safe-area insets. Native build CI checks compilation and deterministic rules, not physical-device play-testing. Web canvas flow was smoke-tested in a mobile-sized Chromium browser; actual iOS Safari testing remains to be done.
