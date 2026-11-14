# Lean 4.36への移行

LMLExplore接続実験と同じLean・mathlibで主体系を検証できるよう、次の組合せへ移行する。

| 対象 | 移行前 | 移行後 |
|---|---|---|
| Lean | `v4.30.0-rc2` | `v4.36.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` | `2ddf59c8f14245864e6c0ed227a2dab76b9efea2` |
| 移行基点 | `1f83367f9680319849a1e0c5288cf7b5a19efb86` | [移行台帳](migration.json)に各ファイルの旧・新SHA-256を記録 |

この移行は、既存の定理と定義を新しい環境で再検証するためのもの。PR #138の接続実験の採否や、追加の数学的主張は別途評価する。

## 原本と検証記録

過去のintegration/Astra manifest、保存したResearch原本、過去の検証結果は当時の記録として保持する。`tools/check_lean_migration.py` は、Gitの移行基点にある原本、旧manifestのハッシュ、現在のソース、固定した依存関係を照合する。記録にない変更、元のmanifestの改変、旧ハッシュまたは現行ハッシュの不一致を拒否する。

移行台帳はソースの対応を示すものであり、形式証明の検査結果ではない。新環境のコンパイルと公理監査は下記の検証コマンドで別途実行する。

Windowsでも保存原本のハッシュを再現できるよう、必要な歴史ファイルの改行変換を`.gitattributes`で止めている。元のGit blobのbytesを保持し、元資料の内容を書き直していない。

## 互換性への対応

- 移動したmathlib import、変更された補題名、帰納法のcase名を更新する。
- 関数の等式や演算の展開を証明内で明示し、新しいelaboratorの推論に依存しすぎない形にする。
- 従来の`simpa ... using`が既約性の差で失敗する箇所は、`using!`で周囲の透明性設定を使用する。Lean 4.36の`Lean.Elab.Tactic.Simpa`にある互換機構であり、証明項は引き続きカーネル検査される。
- mathlibで局所化されたinstanceは必要な場所で明示する。同じ構造・演算を使用する。
- 型に現れるmathlib APIも更新する。`NoAtoms`の現行名`NullSingletonClass`、`PowerSeries.derivative (R := ℝ)`、構造化された`AddMonoidAlgebra`の`.coeff`を使用し、同じ仮定・微分・係数を表す。
- 従来のmodule/exportの扱いを維持するため、Lakeの`allowNonModules = true`を使用する。
- 一部の導出処理・証明では`backward.isDefEq.respectTransparency`を局所的に指定する。影響範囲は当該宣言に限定し、Leanカーネルによる検査と公理監査は継続する。

## 再検証

Python 3.12以降とelanを用意し、CIと同じPython依存をインストールする。

```text
python -m pip install pytest==9.2.0 numpy==2.5.4
cd lean
lake update
lake exe cache get
lake build Elastica
cd ..
python -B -X utf8 tools/verify.py --integration-only
python -B -X utf8 tools/verify.py --toolchain-modules-only
python -B -X utf8 tools/verify.py --elastica-boundary-only
```

`--integration-only`は保存原本の照合、Python検査、主体系36部品と登録された追補、MovingCurve・Okanohara・FiniteMarkovの独立検査を行う。`--toolchain-modules-only`はGit管理下の独立Leanモジュールを依存順に再コンパイルし、そのモジュールが実際に定義した定理の公理を検査する。`--elastica-boundary-only`は固定境界の橋を検査する。

検証結果は`verification/pr-integration.json`、`verification/proof-only.json`、`verification/toolchain-modules/latest.json`などに保存される。部分的な診断runと、対象一覧がすべて完了したrunを区別する。失敗したrunや途中で中断したrunを成功の根拠として使わない。

メモリの少ない環境では、これらのLean検査を順番に実行する。CIでは検証対象を分けたjobで実行し、対象commitと検証結果を記録する。
