# クンマー拡大体と二面体ガロア作用の段階的実装

作成日: 2026-10-31
PR #6 / ブランチ: `chatgpt/kummer-dihedral-20261031`（PR #3へ積み重ねる）。

## 構築したもの

`linear_input/lean_check/KummerDihedral.inc` に追加。
既存 `GaloisChebyshev.inc` の複素数中の候補表示を、field extension と group structure に上げる。

1. `kummerPoly n a = X^n - C a`。
2. `kummerField n a = (kummerPoly n a).SplittingField`: 実際の拡大体。
3. `kummerAdjoinRoot n a = AdjoinRoot (kummerPoly n a)`: 実際の根添加環。既約なら体となり、primitive rootsがある場合は分解体となることをmathlibの既存定理へ接続。
4. `kummerGaloisEquiv`: `IsPrimitiveRoot ζ n` と二項式の既約性を仮定して、実際のガロア群 `Gal(SplittingField(X^n-a)/K) ≃* Multiplicative (ZMod n)`。
5. `kummer_isGalois`、`kummer_finrank`: 実際のガロア性と拡大次数 n。
6. `labelAction`、`labelAction_mul`、`labelAction_one`、反転対合、および `DihedralGroup n` の位数 `2n`。
7. `quadraticResolvent y = X² - 2yX + 1` の既約性を明示的に仮定した `quadraticField y` とその根 `quadraticGenerator y`。
8. `chebyshevKummerTower n y`: 上記の二次拡大体で `X^n - quadraticGenerator y` の分解体を構成する二段階の拡大。
9. `chebyshevUpperGalEquiv`: 上側の巡回ガロア群（上側二項式の既約性と原始根を仮定）。

## 大事な数学的区別

`Gal(SplittingField(X^n-a)/K) ≃ C_n` は、`K` が原始n乗根を含み、二項式が既約という仮定の下での**巡回拡大の定理**。

generic Chebyshev `T_n(X)-y` の`Gal(C(y)(roots)/C(y)) ≃ D_n` は、これとは別の**二次降下と全体群の定理**。適切な拡大塔の二次自己同型が冪根に `z ↦ z⁻¹` と作用し、巡回自己同型を逆元に共役することを体の自己同型として実装し、基礎体上の分解体との一致と拡大次数 `2n` を証明する必要がある。

`DihedralGroup` のラベル作用だけを実装した段階では、**ガロア群そのものが二面体群であるとは証明していない**。このギャップを明示する。特に `y=±1` の特殊化と generic なガロア群を混同しない。

## 検証

再実行:

```bash
python -B -X utf8 tools/verify.py --proof-only
```

固定環境: Lean 4.30.0-rc2、mathlib commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
全宣言を `--trust=0` で検査し、禁止トークン、警告、未許可公理、既存定理の公理依存変更、固定依存の不一致がないことを成功条件とする。

本記録作成時点のPR #6の新規ソースはLean実機コンパイルがまだ確定していない。GitHub Actions の結果とコミットSHAを確認するまでは、旧746定理・880宣言に新規定理を足して「検証済み」とはしない。
