# 多項式写像 E × 予測状態商：符号不可視性を操作で破る（2026-11-17）

## 既存モジュールからの接合

- `lean/Research/SiphonPolynomialE.lean` の多項式自己同型 `E`、不変量 `I` と `I_E` を変更せずに再使用。
- `lean/Research/ElasticaObservationQuotient.lean` の操作語 `run`、`ObsEq`、商 `PredState`、`strict_refinement_splits_quotient` を再使用。
- 新規の接合部だけを `lean/Research/SiphonPredictiveQuotient.lean` に配置する。

ここでの状態 `(u,v)∈ℝ²` は抽象的であり、水理や時間発展の実測モデルではない。

## 正確な構造

既存の更新と不変量は次のとおり。

\[
r=I(u,v)=v+u^3,\qquad
E(u,v)=(u+r^2,\,r-(u+r^2)^3).
\]

第一座標のみを観測する `K(u,v)=u`、既存操作 `oldStep ()=E` を置く。
`I(Ez)=I(z)` および `E^n` の既存公式から、すべての自然数 `n` について

\[
K(E^nz)=u+nr^2.
\]

したがって無限個の将来観測が区別できるのは、**二つの量 `(u,r²)` だけ**。
新規の `signature=(K,I²)` が、既存の `ObsEq K oldStep` を厳密に分類することを
`old_obs_iff_signature` として形式化する。商の更新は

\[
T(u,q)=(u+q,q),\quad signature(Ez)=T(signature(z)).
\]

`mirror(u,v)=(u,-r-u³)` は `I` の符号を反転し、第一座標を維持する。
`I(z)≠0` なら `mirror(z)≠z` だが `ObsEq K oldStep z (mirror z)`。
**不可視性は測定回数の不足ではない**。

## 操作を一種類追加すると商がほどける

新規の操作 `freshStep ()(u,v)=R(u,v)=(u,v+1)` は、
`I(Rz)=I(z)+1` を満たす。すると観測語 `[]`, `[E]`, `[R,E]` だけから

\[
 k_0=u,\qquad k_E=u+r^2,\qquad k_{RE}=u+(r+1)^2
\]

が得られ、

\[
 r=\frac{k_{RE}-k_E-1}{2},\qquad v=r-u^3
\]

と全状態を復元できる。`extended_obs_iff_eq` は、追加後の操作アルファベットで
**任意の二状態が観測同値であることと実際に等しいことが同値**であることを示す。
`extended_encode_injective` は商写像の単射性を、
`nonzero_mirror_quotient_split` は既存の抽象 `strict_refinement_splits_quotient` を使い、
ゼロでない隠れ符号がすべて真に分離することを示す。

具体例：`z=(0,1)` と `mirror(z)=(0,-1)` は、`E` だけなら
どちらも観測列 `0,1,2,3,…` を返す。ところが `[R,E]` による最終読み取りは
それぞれ `4` と `0` になる。

## 検証の境界

- Lean の全称命題：新設ファイルの `signature_E`, `old_obs_iff_signature`,
  `extended_obs_iff_eq`, `extended_encode_injective`, `nonzero_mirror_quotient_split`。
  **GitHub Actions による Lean カーネル検査の完了までは未検証**。
- Python の独立有限検算：`tests/test_siphon_predictive_quotient.py`。整数の
  `[-3,3]²` 49状態、2,401状態対、0〜8ステップの観測列、および
  3種類の読み取りでの状態復元を exact integer arithmetic で検証。
- 非主張：一般の観測者が自動的に全情報を取り戻すこと、任意の未知システムで
  1操作の追加が十分であること、あるいは実際のサイフォン／流体の法則との一致。

## 検証方法

```bash
python3 -m unittest discover -s tests -p 'test_siphon_predictive_quotient.py' -v
# CIでは Lean v4.36.0-rc2 (PR #140) に固定し、依存 .olean を生成後、
# lake env lean --trust=0 Research/SiphonPredictiveQuotient.lean を実行する。
```

PR #140 の移行ブランチを基点とする独立ドラフトPRであり、main に自動統合しない。
