# F16左乗法の16次元行列式と階数12の完全形式化

2026-11-01。前段の [F16RecoverySpectrum.inc](../../linear_input/lean_check/F16RecoverySpectrum.inc) の8個の符号付き2×2ブロックから、16次元の実数行列そのものの行列式と階数を扱う。

## 実際の作用素

有限のケーリー＝ディクソン基底 `e_i` に対し、既存の `eps(i,j)` とXOR添字を使って

```text
M(t)[row,col]
  = (if row = col xor 3 then eps(3,col) else 0)
  + t * (if row = col xor 10 then eps(10,col) else 0).
```

と定義する。元の十六元数の左乗法 `L_(e3 + t e10)` に対応し、`t ∈ ℝ`。

行と列の順序をそれぞれ `Fin 2 × Fin 8` で明示的に列挙する：

```text
column(a,0)=a,           column(a,1)=a xor 9
row(a,0)=a xor 3,        row(a,1)=a xor 10
```

（a=0,...,7）。元の演算表でこれらはどちらも全単射であり、相対置換の符号は+1。さらに再配列された16×16行列は8個の2×2行列のblockDiagonalと一致する。

各ブロックは

```text
B_a(t) =
[ eps(3,a)       t*eps(10,a xor 9) ]
[ t*eps(10,a)    eps(3,a xor 9)    ].
```

そのdetはa=0,3で−(1+t²)、a=1,2で+(1+t²)、a=4,5,6,7で1−t²。これより相対置換の符号が+1であることと合わせ、

```text
det M(t)=(1+t²)^4*(1−t²)^4=(t²+1)^4*(t²−1)^4.
```

が導かれ、実数の特異点は正確にt=1または−1。

## 階数12の証明計画

個々のブロック `B=[[α,β],[γ,δ]]` は `α²=1`。左右の三角行列

```text
U = [[α,0],[-αγ,1]]
V = [[1,-αβ],[0,1]]
```

は行列式がそれぞれα（非零）と1であり、

```text
U*B*V=diag(1, α*det B).
```

を満たす。8個についてblockDiagonalをとると、実16次元行列全体を可逆な行・列操作で対角化できる。t=±1では第1成分8個とdet非零の4ブロックの第2成分が残るため、`rank M(±1)=12`。それ以外ではdet≠0なのでrank16。

## Leanへの登録状況

- `linear_input/lean_check/F16FullMatrix.inc`：行列式と特異点の証明原稿。共通監査に登録。
- `linear_input/lean_check/F16FullRank.inc`：可逆な2×2 Gaussian消去と階数12の証明原稿。現在は作業原稿であり、固定版Leanに登録・検証されるまでは未証明として扱う。
- 既存の789定理・956宣言（PR #11）と804定理・982宣言（PR #14）は変更しない。

固定Lean 4.30.0-rc2 とmathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、`python -B -X utf8 tools/verify.py --proof-only` による`--trust=0`・全宣言公理監査を成功条件にする。

初回CIの完了結果、証拠ID、コンパイルの正確な対象ソースSHAを追記してから検証済み範囲を確定する。ここに書いた計算・行列分解は代数的導出であり、CI未完了の証明原稿を「Lean証明済み」とは記さない。

数値的な原始資料はユーザー提供`E_atlas_F16_smooth_v4_2026-10-22.zip`に含まれ、十六元数は非結合代数であってガロア拡大体ではない。この区別は維持する。
