# RULEFOLD TOUCH — iOS/iPadOS Safari

Open `demos/RULEFOLD_TOUCH_iOS.html` in an iPhone/iPad browser, preferably over HTTPS. This is a self-contained HTML web app, not a native App Store app; no third-party JS/CDN is required.

Use your finger to touch or sweep the white-and-black triangular tiles. **混ぜる** randomizes them, **育てる** advances the finite RULEFOLD machine, **戻す** restores one step, and **保存** generates a PNG. **詳細** opens the optional mathematical controls.

On iOS, export results are shown in a separate save dialog; tap **共有して保存** and choose **画像を保存** or **ファイルに保存**. Original PNG/GIF/JSON formats remain available. MP4 is only offered when the Safari runtime advertises canvas capture and H.264 MediaRecorder support; unsupported environments can switch to GIF instead. Other Safari versions may still fail MP4 encoding, so GIF is the fallback.

Implemented: safe-area insets and dynamic viewport resizing for mobile browser chrome and orientation; tap/drag plus touch fallback and guarded pointer capture; touch-only rendering budget capped near 240k pixels / 29fps; auto-resume of the finite tile+machine state through localStorage when browser policy permits; user-initiated file sharing after asynchronous encoding; smaller default mobile export.

Verification: Node source checks and Chromium iPhone/iPad viewport emulation with touch interactions, PNG/GIF generation, saved-state recovery using a mocked origin storage API, share-sheet invocation, and orientation resizing. **This is not a real iOS WebKit device test.** Safari in a file-preview or in-app sandbox can restrict JavaScript, sharing, and storage; using an HTTPS site in Safari is the reliable deployment method.

Mathematics: the Fin4 reference follows `HigherOrderLiftSelfRewriting.inc`; the creative tile-to-pattern mapping and bounded lab are separate JS experiments, not newly Lean-proved theorems.

