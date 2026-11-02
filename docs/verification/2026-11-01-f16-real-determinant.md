# F16の実16×16左乗法行列式：Lean形式検証（2026-11-01）

## 対象と出典

- F16 は有限体 GF(16) ではなく、提供された十六元数（sedenion）の実16次元係数空間。
- 符号表は既存 `LinearInputF16Holonomy.epsTable` の 16×16整数データ。表の出典は `E_atlas_F16_smooth_v4_2026-10-22.zip` に同梱の `sedenion16.py`（元資料のSHA-256は `docs/verification/2026-11-01-f16-holonomy.md` に記録）。
- `linear_input/lean_check/F16RealDeterminant.inc` は `L(t)=L_(e3)+tL_(e10)` を実数上の `Matrix (Fin 16) (Fin 16) ℝ` として定義し、その **実際の `Matrix.det`** を証明する。

## 定理

```lean
theorem LinearInputF16Determinant.realPencilAll_det (t : ℝ) :
  (realPencilAll t).det = (1 - t ^ 2) ^ 4 * (1 + t ^ 2) ^ 4
```

これは実数パラメータ `t` の任意性を保つ定理。特定点の数値検証だけからの補間ではない。

## 方法：有限係数 → 実線形代数

1. 左乗法 `L_(e3)` と `L_(e10)` の各16×16整数係数を `entryThree`・`entryTen` として抽出する。
2. `Fin 2 × Fin 8 ≃ Fin 16` の行・列座標 `rowEquiv`・`colEquiv` を、逆写像 `rowDecode`・`colDecode` とともに明示的に定義。両方向の逆関係を有限判定で証明する。
3. 組み合わされた行列式の置換符号 `Equiv.Perm.sign (colEquiv.symm.trans rowEquiv)=1` を、反転数の有限積公式から証明する。
4. `block_entry_coefficients` により、異なるブロック間では両整数係数が0、同じブロック内では明示した2×2係数に一致することを、すべての有限添字について証明する。実数変数 `t` を伴う256個の項を個別正規化しない。
5. `reindexed_blocks` で、実16×16行列が `Matrix.blockDiagonal` の8ブロックに正確に一致することを証明。
6. 既存の検証済み `LinearInputF16Recovery.block_coefficients` を使い `block_det` を導出。ブロック0,3は `-(1+t²)`、1,2は `1+t²`、4〜7は `1-t²`。
7. Mathlibの `Matrix.det_reindex`・`Matrix.det_blockDiagonal`・`Matrix.det_fin_two` と有限積の整理から、全16×16行列式公式を得る。

この形式化では `sorry`・`admit`・`native_decide`・新公理を使用しない。

## GitHub検証

- 元の研究ブランチ：`codex/primitive-history-derivation-20261029`（PR #3）
- 追補PR：https://github.com/Sumuji-zkdwn/primitive-lean/pull/20
- 証明検証ソースコミット：`9f2bf2c2e828880cd75848c9e337ec9b256dc9cb`
- GitHub Actions：https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41233416093
- 検証アーティファクトID：`13055091625`
- 固定Lean：`4.30.0-rc2`、固定mathlib：`5450b53e5ddc75d46418fabb605edbf36bd0beb6`
- 検証入口：`python -B -X utf8 tools/verify.py --proof-only`
- `lake env lean --trust=0 ../linear_input/lean_check/MainResult.lean`：終了コード0
- `proof-only.passed=true`、`main-result.passed=true`
- 証明済み合計：**819定理・1,017宣言**。この追補は新規**5定理・17宣言**。
- 全1,017宣言の公理監査 `joint_axiom_audit=true`、既存証明の公理依存一致 `baseline_axioms_match=true`。
- `warnings`、`unexpected`、`errors`、`forbidden_tokens`、`changed_during_verification` は全て空。
- 新原稿 SHA-256：`73314e8ea6bd96740da090c591dab6d64cb9544e239645dc71f2e83ecf5ebc91`
- PR #20 から PR #3 の研究ブランチへ統合したマージコミット：`cf7598a9fc4ac500ff11c6b2a5653ec0289205bf`。既存36原稿と `main` は変更しない。

## 帰結と境界

実数上では `1+t²>0` のため、数学的には `det L(t)=0 ↔ t=±1`。既存の `F16RankCertificate.inc` は `t=±1` の階数12を独立にLeanで証明済みなので、数理的帰結は次のとおり：

- `t ≠ ±1`：階数16、核次元0。
- `t = ±1`：階数12、核次元4。

ただし、**この完全な特異点分類およびすべての実数 `t` に対する階数の必要十分条件は、今回、独立のLean定理として追加していない。** 行列式からの通常の実線形代数的帰結である。

同様に、符号表をCayley–Dickson再帰からLean内で生成する証明、21断面の曲率分類、非結合代数とガロア拡大体の同一視は今回の対象外。

次の最小課題は、既存の階数12定理と今回の行列式公式を接続し、`∀ t : ℝ, rank L(t)=12 ↔ t=1 ∨ t=-1` および非特異点で階数16をLean定理にすること。
