# Siphon一般次数有限測定の検証

2026年11月17日（日本時間）。
基底は PR #146 の `763d5d88d26d5fe8a8830c3b74f57461213ba4ed`。
この追加を同PRに積み重ねる独立ブランチとして公開する。

## 数学的主張と検査範囲

| 内容 | 状態 |
|---|---|
| 曲線内次数 ≤3d、横断方向次数 ≤d | Lean型検査済み |
| 零不変量の非原点を最初のL一回で処理 | Lean型検査済み |
| d+2候補から相異なる非零曲線d+1本を選択 | Lean型検査済み |
| 元の長方形 (d+2)(3d+1) 点での多項式一致 | Lean型検査済み |
| (d+1)(3d+1) 点以下の到達可能な決定集合の存在 | Lean型検査済み |
| 最適値 (d+1)(d+2)/2 と下界 | 研究記録の手証明。Lean形式化はしていない |
| 次数0〜12・非零初期点9種で最小個数の測定点を選択 | 117例の厳密有限検算成功。一般定理の代用ではない |

## ローカルLean検証

- Lean `4.36.0-rc2`、commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`。
- mathlib `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`。
- 上流原文の `Research/SiphonPolynomialE.lean`、`OrbitTrace.lean` を独立ディレクトリで `--trust=0` によりコンパイル。
- それらをimportする追加モジュールを、下記コマンドで検査。終了コード **0**。

```sh
lean --trust=0 -o Research/SiphonFiniteDetermination.olean Research/SiphonFiniteDetermination.lean
```

検査対象ソースのSHA-256:
`d7fc006763a4f3b8545ee37b79f113d33455e1858ed91634420b9dc3efff4694`。
本PRに載せたLeanファイルは検査済みのファイルとバイト一致している。

また、同じ三ファイルの宣言本体をまとめ、mathlibのimportを必要なものに絞った独立版も
`--trust=0` で成功した。宣言本体の同一性を検査した記録を同梱する。
重複宣言をリポジトリの全体監査に混入させないため、その独立版ソース自体は本PRには追加しない。

出力した六宣言（最終二定理を含む）の公理一覧はすべて
`[propext, Classical.choice, Quot.sound]`。`sorryAx` や追加未証明公理は無い。

### 新宣言と上流依存

名前空間は `SiphonFiniteDetermination`。

- `pathPoly_eval`, `pathPoly_natDegree_le`, `fibre_degree`, `transverse_degree`: 明示的代入と次数評価。
- `outgoing_strictAnti`, `outgoing_injective`, `select_curves`: 曲線選択。
- `regular_after_turn`, `regularSeed_regular`: 初期不変量が零の場合。
- `fill_fibre_finite`, `polynomial_zero_of_selected`: 二段階補間。
- `polynomial_zero_of_rectangle`, `polynomial_eq_of_rectangle`: 元の上限。
- `exists_finite_determining_set`: 改善された有限集合の上限。

上流の `I`, `iterate`, `closedOrbit`, `iterate_eq_closedOrbit`, `OrbitTrace.linearE` を参照する。
PR #146の単調性・零不変量の前処理の補題はprivateなので、短い証明を新名前空間で再構成した。
`readPoly` はPR #146の同名評価関数と定義的に等しい。
既存のザリスキー稠密性定理を新しい有限上限の根拠としてそのまま呼ぶことはしていない。

## Python検証

Python 3.12、sympy 1.14.0。次数0〜12、非零初期点9種の117例で成功。
原点、初期の零不変量、途中の候補に零不変量を含む場合も確認した。
`Fraction` による反復式と閉形式の照合、455件の単項式次数検査、
独立行選択後の非零小行列式の法p検査を行う。
既存 `test_siphon_operational_world.py` の4テストも成功。

保存時の修正は未使用importの削除と証明書の出力先を
`verification/siphon-finite-determination/` に移すことのみ。
変更後のスクリプトでも同じ117例を再実行している。

## 証跡と再現

[保存したローカル証跡](siphon-finite-determination-20261117/) には、
Leanログ、Pythonログ、ソースハッシュ、既存PRの取得記録を含む。
これらはローカル検証の証拠であり、新PRのCI成功記録とは区別する。
既存run `43982007551` のsuccessはあくまで元のPR #146のヘッドについてのもの。

```sh
python3 -m pip install sympy==1.14.0
python3 -B tools/check_siphon_finite_determination.py
python3 -B tools/verify_toolchain_modules.py --module Research.SiphonFiniteDetermination
```

専用CIはPRの実際のhead SHAをcheckoutし、依存二モジュールを含むソース再コンパイルと、
新規モジュール内の全定理の公理監査を実施する。
生成される証明書と監査結果はActions artifactとして保存する。
