# F16実左乗法の階数12：Lean形式検証記録（2026-11-01）

## 対象・境界

F16は有限体GF(16)ではなく、元資料の十六元数（sedenion）16次元実係数空間を指す。本追補の出発点は既存の `LinearInputF16Holonomy.epsTable` に明示的に埋め込まれた符号表であり、Cayley–Dickson再帰自体のLean形式化ではない。

既存 `F16RecoverySpectrum.inc` の`leftPencil`と同じ符号・基底添字の計算規則から、行列`intPencil t : Matrix (Fin 16) (Fin 16) ℤ`を定義し、`Int.castRingHom ℝ`で実数上の`realPencil t`へ輸送する。

本追補は次を証明する：

```lean
theorem realPencil_plus_rank : (realPencil 1).rank = 12
theorem realPencil_minus_rank : (realPencil (-1)).rank = 12
```

ここで`Matrix.rank`はMathlibの実数上の行列階数である。

## 証明書の構造

`C_t`を`intPencil t`の最初の12列からなる16×12整数行列、`R_t`を明示的な12×16整数行列とすると、各`t=±1`で

```text
intPencil(t) = C_t * R_t
```

を`factor_plus`・`factor_minus`で全成分有限計算から証明した。この因数分解から実階数の上限12が従う。

さらに元行列の左上12×12部分行列`B_t`と明示的な12×12整数行列`U_t`に対し、

```text
U_t * B_t = 2 * I_12
```

を`unmix_plus`・`unmix_minus`で証明した。実数上では`2I_12`の階数は12であるから、部分行列・積の階数不等式により元行列の階数の下限12が従う。これらを合わせて`realPencil_rank`を導出し、`t=1,-1`へ特殊化した。

整数行列の等式は16×16・12×12の有限の各成分を、`fin_cases`と`decide`で証明する。`native_decide`や`sorry`は使用しない。

## 検証結果

- 原稿：`linear_input/lean_check/F16RankCertificate.inc`
- 元の804定理・982宣言を保持し、新規10定理・18宣言を追加
- GitHub Actions：https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41231121631
- 検証対象コミット：`117211b6bc9faa4f022dc064fe8f8afe2e14c324`
- 全体：814定理・1,000宣言
- 固定Lean：`4.30.0-rc2`、固定mathlib：`5450b53e5ddc75d46418fabb605edbf36bd0beb6`
- `python -B -X utf8 tools/verify.py --proof-only`：成功
- `lake env lean --trust=0 ../linear_input/lean_check/MainResult.lean`：終了コード0
- 全1,000宣言の公理監査成功、従来宣言の公理依存一致。許可外公理・警告・禁止トークン・検証中のソース変化はなし
- 原稿のほか、`tools/verify.py`・`tools/verify_main_result.py`への登録、検証用`linear_input/verify_lean.py`への`Mathlib.LinearAlgebra.Matrix.Rank` import追加だけを行った。既存の36原稿は変更しない。
- PR #18（https://github.com/Sumuji-zkdwn/primitive-lean/pull/18）を研究用PR #3（https://github.com/Sumuji-zkdwn/primitive-lean/pull/3）のブランチへマージ。統合コミット：`0120277552395429612e0a8fea28955d9ec1d53e`。`main`へはマージしていない。

## 今回は証明していないこと

- 任意の実数`t`に対する16×16行列の行列式`(1-t²)^4(1+t²)^4`の独立Lean定理。
- 任意の実数`t`に対する完全な階数・スペクトルの分類。
- Cayley–Dickson再帰による`epsTable`の生成のLean内検証。
- 行列`realPencil`と、元資料のあらゆる表現の`leftPencil`の同一性の一般的な行列作用定理。
- 21断面の曲率分類や非結合代数の結合子／滑らかな接続との同一視。

次の最小課題は、既存の8個の2×2ブロック分解を実係数パラメータに一般化して、`Matrix.det`の全16×16恒等式を証明すること。
