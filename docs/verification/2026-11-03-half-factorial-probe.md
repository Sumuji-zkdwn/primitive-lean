# 半階乗モノイドと全既約分解の最小識別作用素

日時: 2026-11-03 JST
PR: https://github.com/Sumuji-zkdwn/primitive-lean/pull/46
基盤: PR #42（4・6・9 の可換・約分可能な非一意分解モノイド）、PR #38（一般の書換えと識別作用素）。

## 定義

対象は実際の乗法部分モノイド `G = ⟨4,6,9⟩ ⊆ ℕ`。
既存の `LinearInputGeneratedNonUnique.Atomic` は非単元への二分割不能性。

生成子の出現回数 `(r,s,t)` を `Counts` として表す：
`value(r,s,t) = 4^r * 6^s * 9^t`。
この分解を評価するのは通常の可換乗法1種類のみ。
ただし分解を発見するための計算費用は数えない。

指数観測は
`signature(r,s,t) = (2r+s, s+2t)`。
`Nat.factorization` によって `value` の2と3の指数を取ると、
厳密にこの組になる。

## 生成子分解の一般定理

1. `same_value_same_signature`：積が同じなら2つの指数が同じ。
2. `same_value_same_length`：積が同じなら `r+s+t` が同じ。
3. `value_and_six_injective`：`(積, s)` は全ての生成子計数に単射。
4. `actual_G_value_and_six_injective`：抽象数値だけでなく、
   実際のGの元とsを観測しても同じ単射性が成立。
5. `every_element_has_generator_counts`：Gの任意の元は
   何らかの `(r,s,t)` で表現される。
6. `one_probe_necessary_and_sufficient`：
   積だけでは `4*9 = 6*6` により非単射だが、sを追加すると単射。

## 全ての既約元・全ての既約因子多重集合へ

`AtomicGeneratorClassification.inc` の `atom_iff_three_generators`：
生成閉包の帰納法と原子性から、任意の実際の原子は
4,6,9のいずれかであり、逆にそれらは全て原子。

`AtomicHalfFactorial.inc`：
全原子について `v₂(a)+v₃(a)=2`。
任意の原子多重集合 `w` について、
`v₂(prod w)+v₃(prod w)=2 * card w`。
したがって **実際のGの全既約分解は長さが一意**。

`AtomicWordProbe.inc`：
任意の原子多重集合 `w` を、出現回数の記録 `Counts` へ
変換することを証明し、
「積が同じで、因子6の個数も同じなら多重集合そのものが一致」
という全称的な識別定理を得る。
反例 `[4,9]` と `[6,6]` により、積のみの識別は不可能。
したがって追加可能な観測を `count 6` に限定した
**最小追加観測数は厳密に1**。

これは分解の実行回数や素因子探索の時間計算量とは全く異なる指標である。

## 数学的な全分解数（Lean未形式化）

n∈G として `a=v₂(n), b=v₃(n)` と置くと
全分解は `s = 0,…,min(a,b)` のうち `s≡a≡b (mod 2)`
を満たす整数sで一意に決定する。
この条件から分解数は

`N(n) = ⌊min(a,b)/2⌋ + 1`

と分かる。
n=36 は2通り、n=216も2通り、n=1296は3通り、
n=46656は4通り。

この `N(n)` の閉形式を直接与えるLean宣言は、今回のPRに含めない。
全既約元に関する半階乗性と全分解への1観測識別は別命題として検証する。

## CIと成立条件

固定ツールチェーン `leanprover/lean4:v4.30.0-rc2`、
Mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
実行入口 `.github/workflows/half-factorial-probe.yml`。

- 独立検証：`lake env lean --trust=0 HalfFactorialProbe.lean`
- 統合検証：`python -B -X utf8 tools/verify.py --integration-only`
- 生成された統合ファイルについて全宣言の公理監査と
  出典ファイルのSHA256照合を実施する。

**今回のPR #46に追加した全ソースのCIは、最終コミットの結果が出るまで未確認として扱う。**
古いコミットでの成功を新しい宣言に流用しない。

## 一般の次数関数による半階乗性（数学的な追加考察）

可換モノイドMに加法的次数 `λ:M→ℕ` があり、
`λ(xy)=λ(x)+λ(y)`、かつ全既約元aで `λ(a)=1` なら
任意の既約分解の長さは `λ(x)` となり一定。
Gでは `λ(n)=(v₂(n)+v₃(n))/2` がそれに当たる。
この抽象次数定理は、現時点では独立したLean定理として追加していない。

## 非主張

本研究は Mathlib の素因数分解と一般書換えの既知事実に基づく
形式的な識別体系の接続であり、高速素因数分解法・RSA破り・
任意のモノイドの一意分解・許容観測を固定しない普遍的最小値を
主張しない。
