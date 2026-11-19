# クンマー拡大体と二面体ガロア作用の段階的実装

## 検証確定（2026-10-31）

GitHub Actions [#41212071155](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41212071155) は **completed / success**。対象コミット `f93118dd67afdd0188b04d7cd96b2c64b9592c32`。固定Lean 4.30.0-rc2、固定mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を使用。

- `python -B -X utf8 tools/verify.py --proof-only`: `passed=true`。joint / supplement の終了コード0。
- `lake env lean --trust=0 ../linear_input/lean_check/MainResult.lean`: 終了コード0。755定理・899宣言の統合証明を検査。
- 新規 `KummerDihedral.inc`: 9定理・19宣言（定義・略記10件）。新規19宣言を含む全899宣言について公理監査成功（`joint_axiom_audit=true`）。従来宣言の公理依存一致（`baseline_axioms_match=true`）。
- `warnings`、`errors`、`unexpected`、`forbidden_tokens`、`changed_during_verification`：すべて空。承認公理は `propext`、`Classical.choice`、`Quot.sound` のみ。`sorryAx` なし。
- [証拠ZIP](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41212071155/artifacts/13047455212)、アーティファクトID `13047455212`（86,090 bytes）。
- `linear_input/lean_check/KummerDihedral.inc` SHA-256: `8b522f412c683f56b4cfe5cda75cc4b81a32368af46c09e977b90e5dc116876e`。
- `linear_input/verify_lean.py` SHA-256: `f57b26d0002ea3413612def7b1724ba938d266b8a5f9c195e6124cff280e6aa9`。
- `tools/verify_main_result.py` SHA-256: `84e997a94eb75143d77e1b3eaa754826e38a7c5a3ce9ae447371c8afd2ff9ca6`。
- `tools/verify.py` SHA-256: `4ddb70a16e6ae3dc38494c8c3112af89e044a78d05ae77e65c6b476a21e20d7d`。

**数学的範囲に関する注意:** 成功した定理は、実際のクンマー分解体の構成・既約性を仮定した巡回ガロア群同型・拡大次数・二面体群のラベル作用と合成則、明示的な二次→クンマー拡大塔まで。一般の `Gal(C(y)(T_n^{-1}(y))/C(y)) ≃ D_n` という *体のガロア群の同型*、および二段階の拡大塔がそのチェビシェフ分解体と一致する命題は **まだLean証明していない**。


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


## 全二面体ガロア群同型へ進むための数学的証明（Lean未形式化）

以下は**紙上の代数的証明**であり、既存の9新定理によるLean証明済み命題ではない。

整数 \`m = 3^n\`、\`n ≥ 1\` とし、\`ζ\` を複素数上の原始 \`m\` 乗根とする。
形式的な変数 \`z\` に対し、関数体 \`F = ℂ(z)\` 内で

\`\`\`text
t = (z^m + z^(-m))/2 ,
K = ℂ(t) ⊂ F
x_j = (ζ^j z + ζ^(-j) z^(-1))/2   (j mod m)
\`\`\`

を定める。

1. チェビシェフ恒等式により \`T_m(x_j)=t\`。逆像 \`x_j\` はすべて \`F\` にある。
2. \`t(z)=(z^(2m)+1)/(2z^m)\` は分子・分母が互いに素な次数 \`2m\` の有理関数なので、関数体の拡大次数 \`[F:K]=2m\`。
3. \`r_a(z)=ζ^a z\`、\`s(z)=z^(-1)\` の置換は \`t\` を固定し、\`r_a r_b=r_(a+b)\`、\`s²=1\`、\`s r_a s=r_(-a)\` を満たす。これら \`2m\` 個の相異なる自己同型が存在するため \`Gal(F/K)≅D_m\`。
4. \`x_0=(z+z^(-1))/2\`、\`x_1=(ζz+ζ^(-1)z^(-1))/2\`。 \`m≥3\` より \`ζ-ζ^(-1)≠0\` なので、

\`\`\`text
z = 2 (x_1 - ζ^(-1) x_0)/(ζ - ζ^(-1)).
\`\`\`

従って、\`x_j\` 全体の生成体は \`F\` に一致する。すなわち \`F\` は \`T_m(X)-t\` の分解体であり、上記の群同型がその多項式のガロア群同型そのものを与える。

**形式化に必要な追加命題:**
- \`RatFunc ℂ\` 上で \`t=(z^m+z^{-m})/2\` による基礎体の代入・埋め込みを構成する。
- 一般有理関数の次数から \`[ℂ(z):ℂ(t)]=2m\` を導く。
- \`z↦ζ^a z\`、\`z↦z⁻¹\` を基礎体上の \`AlgEquiv\` として構成し、二面体群の作用が忠実であることを示す。
- \`x_j\` が \`T_m(X)-t\` の根であり、それらで \`z\` を復元できることをLeanで証明する。

この4群がLeanで成立するまでは、\`Gal(... ) ≃* DihedralGroup m\` を既存の検証済み宣言数に含めない。


## 2026-11-19 追記：全二面体ガロア群同型の Lean 証明

上の「形式化に必要な追加命題」4群を、独立モジュール `lean/Research/ChebyshevDihedral.lean`（50定理、`Mathlib` のみ import）で証明した。係数体は \(\mathbb C\) に限らず、原始 \(m\) 乗根 \(\zeta\) をもつ任意の体 \(k\)。関数体は `RatFunc k`（変数 \(X\) が上の \(z\)）。joint 検査の宣言数（`KummerDihedral.inc` の9定理を含む既存の数）には含めない。

| 追加命題 | Lean 宣言 |
| --- | --- |
| 基礎体 \(K=k(t)\) を中間体として構成 | `baseField k m = k⟮X^m + X^{-m}⟯`。\(2\ne0\) なら \(k⟮(X^m+X^{-m})/2⟯\) と同じ体（`adjoin_half_eq`） |
| \([k(z):k(t)]=2m\) | `finrank_baseField`。上界は \(X\) が \(Y^{2m}-tY^m+1\) の根であること（`finrank_le`）、下界は次の \(2m\) 個の自己同型 |
| \(z\mapsto\zeta^a z\)、\(z\mapsto z^{-1}\) の自己同型と忠実性 | `sigma : DihedralGroup m →* (k⟮X⟯ ≃ₐ[k] k⟮X⟯)`（`r i : X ↦ ζ^i X`、`sr i : X ↦ ζ^i/X`）、`sigma_injective`、`sigma_tInv`。代入による作用なので、自己同型 \(g\) の後に \(h\) を合成すると点写像は \(h\circ g\) の順になる |
| \(x_j\) が根で \(z\) を復元 | `aeval_root`・`root_injective`（\(y_j=\zeta^jX+\zeta^{-j}X^{-1}\) は Dickson 多項式 \(D_m(Y,1)-t\) の相異なる根）、`adjoin_rootSet`（\(m\ge3\)、\(X=(y_1-\zeta^{-1}y_0)/(\zeta-\zeta^{-1})\)）、`chebyshev_T_root_half`（ノートの正規化 \(T_m(y_j/2)=t/2\)） |

結論として `galEquiv : DihedralGroup m ≃* Gal(k⟮X⟯/baseField k m)`（\(m\ge1\)）、`isGalois_baseField`、`isSplittingField`（\(m\ge3\)、\(k(X)\) は \(D_m(Y,1)-t\) の分解体）。証明は \(|D_m|=2m\le|\mathrm{Gal}|\le[k(X):k(t)]\le2m\) による（`card_gal_and_finrank`、mathlib の `AlgEquiv.card_le`）。\(m=3^n\) は特別な役割をもたない。

検証（2026-11-19、Lean `v4.36.0-rc2`、mathlib `2ddf59c8`）：`lake env lean --trust=0 Research/ChebyshevDihedral.lean` は警告なしで通り、全50定理の使用公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内（3定理は `propext`・`Quot.sound` のみ）。数値検算 `python -B tests/test_chebyshev_dihedral.py`（複素浮動小数点、証明ではない）は \(m\le9\) で合成則・\(2m\) 写像の相異・\(t\) の不変性・軌道が \(Y^{2m}-tY^m+1\) の全根であること、\(3\le m\le11\) で \(D_m(y_j)=t\)・\(T_m(y_j/2)=t/2\)・\(y_j\) の相異と \(z\) の復元を確認した。専用CI `.github/workflows/chebyshev-dihedral.yml`、統合検査 `tools/pr_integration.py` の `chebyshev-dihedral` 段。

境界：基礎体は \(k(X)\) の中の \(k(t)\) であり、独立変数 \(y\) の有理関数体 \(\mathbb C(y)\) との同型（\(t\) の超越性から従う）は Lean では書いていない。`GaloisChebyshev.inc`・`KummerDihedral.inc` の宣言との同一視も行わない。
