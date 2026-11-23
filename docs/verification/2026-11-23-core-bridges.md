# 核の定理による接続の検証（2026-11-23）

基底コミット `a5e7db1eff95b6c2777bd04f3de23b8d00057cde`（main）。検証は、この基底に下記の変更を加えた未コミットの作業ツリーで行った（記録上 `dirty: true`）。検証したソースは同じバイト列のままコミットした（末尾のSHA-256）。README の追記とこの記録は、検証の後に加えた文書である。本文は[第8.28節](../../原始の形式化.md)、宣言の対応は[検証と再実行 1.7](../../検証と再実行.md)、宣言・仮定・再利用した定理は[追補台帳](../../sources/core_bridges_2026-11-23.json)にある。

## 実行環境

- Lean (version 4.36.0-rc2, x86_64-unknown-linux-gnu, commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a, Release)
- mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`（`lake exe cache get` のビルド済みキャッシュ）
- Python 3.13、pytest 9.2.0、numpy 2.5.4

## 統合検査

```sh
python -B -X utf8 tools/verify.py --integration-only
```

| 項目 | 結果 |
|---|---|
| 統合検査全体 | 合格（40段階、失敗0） |
| 来歴・登録の監査（source-audit） | 合格（追補グループ279→281） |
| リポジトリのテスト | 418件合格 |
| 有限検算・ARC3オフライン | 合格 |
| joint検査と追補の結合検査（`--trust=0`） | 合格、警告0。proof-only 段階 422 秒、うち `MainResult.lean` のコンパイル 384 秒 |
| 全宣言の公理監査 | 合格。許可外の公理0。新しい20宣言はすべて `propext`・`Classical.choice`・`Quot.sound` のみ |
| 独立モジュール（MovingCurve・Okanohara・FiniteMarkov ほか） | 合格 |
| 検証対象の総数 | 4,976定理・6,652宣言（基底は4,959定理・6,632宣言。差は今回の17定理・20宣言） |

基底のみの `tools/verify_main_result.py` も同じ環境で実行し、コンパイル終了コード0・警告0・許可外の公理0、4,959定理・6,632宣言を確認した。

## 核への到達の測定

`tools/deps/ExtractDeps.lean` を、`All.lean` と `FiniteBayes.inc` までの登録済み追補を前置きにしてコンパイルした2原稿に適用した。初期層は Elastica の24モジュールと `All.lean` の36部品の名前空間とする（[依存関係の報告](../dependency/README.md)と同じ定義）。

| 原稿 | 定理 | 証明項が初期層の定理に届く定理 |
|---|---:|---:|
| `ScaleTemperature.inc` | 4 | 4（`Elastica.energy_scaling_of_homogeneous`・`energy_scaling_quadratic` を直接使用） |
| `ArcChebyshev.inc` | 13 | 3（主結果を経由。初期層の定理78個に到達） |

`ArcChebyshev.inc` の残り10定理は正規化と判別式の代数補題で、初期層には届かない。`docs/dependency/` の生成物はこの変更では再生成していない。

## 検査したソースのSHA-256

| ファイル | SHA-256 |
|---|---|
| `linear_input/lean_check/ScaleTemperature.inc` | `becdbfb5465f5739fba8b4b942b23476a55863aec8cbab24d8ab6f861b99a876` |
| `linear_input/lean_check/ArcChebyshev.inc` | `9b1107b41016895ffb04db75ff8258655188d8d484a81fb946e805995bab1cb2` |
| `tools/verify_main_result.py` | `c1951d8aacd4821099c4bb2460981fcd7cf754812fb24c5eb09650904076b80b` |
| `tools/verify.py` | `b4fc6c668777d13e1a26f94f1841e48a3559c08fc69db44ba8254e1354107fcf` |
| `docs/integration/manifest.json` | `ff50eba9fea5f57fc0a71ee42cfad5003507d52a63aed9ed76549fdaf6f1ae5c` |
| `docs/lean436/post-migration.json` | `04c453a2f173216967f4a24408ed203cc7e64a269a35ba7ea85b5f6f85ff6df7` |
| `sources/core_bridges_2026-11-23.json` | `53a564a9323c0e3536e0ea1732455845dc47e2c8cc95f1ac5af81e959b85bc75` |
