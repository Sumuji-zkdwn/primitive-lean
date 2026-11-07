# 素因数分解を「分解の標準形」と「識別作用素」から再構成する

日時: 2026-11-03 (JST)
PR: https://github.com/Sumuji-zkdwn/primitive-lean/pull/39
基盤: PR #38 (一般書換えの停止・標準形一意性・最小識別作用素)

## 1. Mathlibに存在する数学的核心

固定Lean: v4.30.0-rc2、Mathlib: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

Mathlibの `PNat.factorMultisetEquiv`、`PNat.prod_factorMultiset`、
`PrimeMultiset.factorMultiset_prod` から、正整数の素因子多重集合と
正整数は互いに逆な写像を持つ。

`PrimeFactorIdentification.inc` では
`evaluatePrimeWord : PrimeMultiset → ℕ+` と
`primeNormalForm : ℕ+ → PrimeMultiset` を導入し、
相互逆、両単射、積と多重集合の和の対応を明示した。

既存の `TerminalValueInjective` と `IdentifiesWith` を利用すると、
素数だけからなる標準形は積の値そのもので識別可能であり、
「**積の値を既知としたときの追加観測数**」は0となる。
この値は素因数を計算で発見する費用を表さない。

`Multiset ℕ` についても、各要素が素数であるという仮定の下で、
同じ積なら同じ素因子多重集合という定理
`natural_prime_multiset_injective` を形式化した。

一方、既存PR #38にある生成子4/6/9の例は、
`4×9=6×6` で同じ積から異なる原子ラベル多重集合が生じることを示す。

## 2. 具体的な分解書換え

`PrimeSplitNormalForm.inc` では、非自明な二因子分解

`(a*b) :: rest → a :: b :: rest` （`a,b ≥ 2`）

を `SplitStep` と定義する。積を保存し、因子数をちょうど1つ増やす。

ポテンシャル

`V(s) = Σ_(a∈s)(a-1)`

は分割一回で `(a-1)(b-1) ≥ 1` だけ減少する。
`split_rank_decreases` と既存の `terminating_normal_form` を合成し、
無限の非自明分解が起きないことを証明する。

全ての因子が2以上という `Admissible` 条件を満たすとき、
終端条件は「全ての因子が素数」と同値である
(`split_terminal_iff_all_prime`)。

`FactorWord := {s : Multiset ℕ // Admissible s}` を定義し、
実際の分割の停止性・素数終端の存在・終端の一意性・
追加観測数0を、既存の一般書換え理論に接続した。

`SplitChain k s t` を実行回数つきの分解経路として定義し、
`t.card = s.card + k` をLeanで証明した。
単一初期因子 `{n}` に対し、素数終端の因子数を `Ω(n)` と呼ぶなら
分解回数は数学的に `Ω(n)-1`（n≥2）となる。
ただし `Ω` の名で定義した算術関数への等式自体は、このPRの
公開Lean宣言にはまだ追加していない。

## 3. 数の区別・操作の区別・費用を混同しない

- 演算の**種類**：通常の可換乗法ひとつ。
- 非自明分解の**実行回数**：二分割木の内部節点数（上の式）。
- **最終値による標準形の識別**：素数のみ・0と単位元1を除く構成では追加観測0。
- **分解相手を探索する計算量**：このPRでは扱わない。

整数0は乗法の吸収元、1は単位元。今回の
`Admissible` は各因子を2以上に制限する。
一般環の単元・同伴元の同一視、整域の一般一意分解、
複数の観測候補がある場合の最適化アルゴリズム、
計算量の下界も未証明である。

## 4. 検証記録

独立Lean検証:
https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41596601238
（source head `bc9a518ab8df73ad07c898d027df8a84b467089d`, success）

PR headに対する統合CI:
https://github.com/Sumuji-zkdwn/primitive-lean/actions/workflows/prime-factor-identification.yml
（このリンクの最新commit SHA、独立Lean/統合の両ジョブを確認して判断する）

統合検証器には原本 `All.lean` を一切書換えず、
生成した `MainResult.lean` の先頭に
`import Mathlib.Data.PNat.Factors` を追加する。
既存原本や追補ソースのバイト列は保持し、登録された全宣言の
`--trust=0` と公理監査を統合CIで行う。
