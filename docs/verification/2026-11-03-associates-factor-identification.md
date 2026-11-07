# 分解の一意性を「同伴元の商」と「最小識別観測」で特徴づける

2026-11-03 JST — PR #42: https://github.com/Sumuji-zkdwn/primitive-lean/pull/42

基盤: PR #36（三進零配置と有限識別）→ PR #38（一般書換えと標準形）→ PR #39（正整数の素数分解）。

## 一般化の境界

型 `M` に `CommMonoidWithZero M` を仮定し、`Multiset M` に対して
`AtomicWord f := ∀ p ∈ f, Irreducible p` を定義する。

同伴関係は
`Associated a b ↔ ∃ u : Mˣ, a * (u : M) = b`。
単元による違いを保ったまま因子数を比較するのは不適切なので、
`AssociatedWords f g := Multiset.Rel Associated f g` とする。

分解の最終値からの識別を次で定義:
`ProductIdentifiesAtoms M` :=
「任意の原子的多重集合 `f,g` について、`Associated f.prod g.prod` なら
`Multiset.Rel Associated f g`」。

正整数での「積だけで素数多重集合を識別」と比べ、同伴を含めた一般化になっている。

## 一意分解との関係

既存Mathlib `UniqueFactorizationMonoid.factors_unique` によって、
`UniqueFactorizationMonoid M → ProductIdentifiesAtoms M`。

逆向きは**無条件ではない**。\
`IsCancelMulZero M`、および
任意の非零元が既約元多重集合へ同伴元まで分解される存在条件が必要。
この条件下で `UniqueFactorizationMonoid.of_existsUnique_irreducible_factors`
を用いて、
`UniqueFactorizationMonoid M ↔ ProductIdentifiesAtoms M`
を形式化する。

`IdentifiesWithUnits probe chosen` は、原子的多重集合の
同伴評価衝突を追加観測で被覆する条件。
観測追加の単調性、観測集合が空であるときの必要十分条件、
UFMなら追加観測0、そして同伴評価を保存する書換え経路の
終端が同伴多重集合として一致する定理を含める。

## 可換性と約分可能性だけでは不足する具体的反例

正整数の乗法部分モノイド
`G = Submonoid.closure ({4,6,9} : Set ℕ)`
を考える。

`one_or_at_least_four`:
任意の `x∈G` は `x=1` または `x≥4`。
よって `4,6,9` はGの非単元2個の積では書けず、G内で原子的。

それでも `4×9=6×6`。単位元は1のみであるため、
既約因子の多重集合が異なる真の非一意分解である。
またGで6は原子的だが、
`6 | 4×9` に対し `6 ∤ 4`, `6 ∤ 9`。
これで「既約元と素元が異なる」ことを具体的に表せる。
Gは正整数乗法の部分モノイドであり、約分可能である。
Leanでは相対的な`Atomic`/`Primal`条件を直接定義した。

有限二候補 `[4,9]` と `[6,6]` だけを識別する際には、
積は両方36で区別不能。追加観測`count(4)`は1対0となり、
**許容された観測族の下で最小追加観測数1**。
これは無限のG全体に対する最小観測数を主張しない。

## 形式化・検証範囲

- `linear_input/lean_check/AssociatesFactorIdentification.inc`
- `linear_input/lean_check/GeneratedNonUniqueMonoid.inc`
- `.github/workflows/associates-unique-factorization.yml`
- `tools/verify_main_result.py`と`tools/verify.py`への宣言登録
- `docs/integration/manifest.json`への個別SHA256出典登録

Lean v4.30.0-rc2、固定Mathlibで独立`--trust=0`と全体統合・公理監査を別ジョブで実施する。
**新規PR #42のCI成否は実行結果を確認した後にのみ確定する。**

この一般化では、一般可換モノイドに一意分解を仮定していない。
また高速素因数分解法、任意モノイドの最適観測数、非可換積の
因子列分類、無限生成・無限因子列は未対象。
