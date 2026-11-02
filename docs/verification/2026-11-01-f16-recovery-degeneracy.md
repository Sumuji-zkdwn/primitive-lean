# F16の一手復元と十六元数の左乗法ブロック


## Lean統合検証結果（2026-11-01）

**[GitHub Actions #41227143919](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41227143919) — completed / success.** 証明ソースコミット `0b2e32d4755d45f5871b6e82b069f86e80959e75`。固定Lean `4.30.0-rc2` と固定mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` で実行した。

- `python -B -X utf8 tools/verify.py --proof-only`: `passed=true`、joint/supplementとも終了コード0。
- `lake env lean --trust=0 ../linear_input/lean_check/MainResult.lean`: 終了コード0、**804定理・982宣言**。
- 新規 `F16RecoverySpectrum.inc`: 15定理・26宣言（略記・定義11）。全982宣言の公理監査成功（`joint_axiom_audit=true`）、旧宣言の公理依存一致（`baseline_axioms_match=true`）。
- `warnings`、`errors`、`unexpected`、`forbidden_tokens`、`changed_during_verification` は全て空。許可公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
- 新原稿のSHA-256: `fa96ebb4fa9b05e41c77771fb386c1af0e851bec1fd59b556cafa1cf7f62f0fc`。
- [生ログ・公理監査アーティファクト](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41227143919/artifacts/13052048324)、artifact ID `13052048324`、91,671 bytes、ZIP SHA-256 `a5c018fa15068643104497746aa8b4e8709598196684d20d2252183f9de1adb3`。

元の789定理・956宣言を維持し、**新しい15定理と11定義・略記の実際のLean検査が成功**した。依存キャッシュ利用の実行で、完全クリーンビルドではない。歴史保存物・HTML再描画・Kaggle実機の検証ではない。

**特に重要な境界:** `blockDet_formula` は各2×2ブロックの**整数係数に関する**恒等式をLeanで証明した。全16×16作用素の実数パラメータに関する行列式公式と階数12は、本ノートのブロック分解に基づく数学的証明とPython検算の対象で、独立したLeanの`Matrix.det`・`rank`定理としてはまだ登録していない。


2026-11-01。PR #11の `F16Holonomy.inc` を加法的に拡張する追補。
出典はユーザー提供の `E_atlas_F16_smooth_v4_2026-10-22.zip`。
元のF16を有限体 `GF(16)` と同一視せず、**実16次元の十六元数（sedenion）**の符号付き基底乗法として扱う。

- 元ZIP SHA-256: `2a6a3d0540944d301096dcda2dcd049ae0d1f23778bae840f85dce5420aef44a`
- 内包されたv3 ZIP SHA-256: `baa2bd8c24cedfffe6c06891e549c15fce4e64730cc1cdc3fb24038703f74162`
- `sedenion16.py` SHA-256: `a42a94fcc979530946565f720498036b8d2cbc79ebc5aae96b0b68d47fea68ce`

## 1. 32状態の一手復元

状態は `S = Bool × Fin 16`。忘却は `K(s,a)=(s,a mod 8)`（`Fin16` に戻す代表）。
前回の `observedRight b s = K(R_b(s))` を使い、

```text
pairedObservation b s = (K(s), K(R_b(s)))
```

と定義した。1 ≤ b ≤ 8 では、元の符号付き状態 `s` をこの2観測から復元する具体的関数 `decodeProbe` がある。新しい定理 `decodeProbe_exact` により左逆の成立を目指す。

```text
Injective (pairedObservation b)
  ↔ 1 ≤ b.val ∧ b.val ≤ 8
```

さらに `pairedObservation_injective_iff_noncompatible` で、**この一手観測が単射であることと、既存 `LinearInputF0.Compatible` が成立しないことが必要十分**で一致する定理も追加した。
逆方向の非単射は `(true,e0)` と `(true,e8)` のペアで全ての降下する8探針について具体化できる。
両者は現在のK観測が等しいが、e1探針で後続観測が区別される。

旧 `LinearInputF0.Compatible` と接続する境界は、
`b∈{0,9..15}` では降下可能、`b∈{1..8}` では1手で完全復元可能、という二分である。
「忘れた記憶が自然回復する」との主張ではない。異なる隠れ状態が現在の粗い観測で合流し、**異なる後続観測の選択によって分離される**という有限モデルである。

## 2. 左乗法の8個の2×2ブロック

元ZIPの符号表 `eps(i,j)`、基底添字の排他的論理和を用い、

```text
P=L_(e3),  Q=L_(e10),  L(t)=P+tQ.
j = 0..7, partner(j) = j xor 9.
rows(j) = (j xor 3, j xor 10).
```

とする。 `L(t)` の列 `(j,j xor 9)` から行 `(j xor 3,j xor 10)` への部分行列は

```text
[ eps(3,j)        t eps(10,j xor 9) ]
[ t eps(10,j)     eps(3,j xor 9)    ]
```

である。その符号付き2×2行列式 `blockDet(j,t)` は

```text
j = 0,3: -(1+t²)
j = 1,2: +(1+t²)
j = 4,5,6,7: 1-t²
```

に等しい。8列組が16列全体を分割し、8行組も16行全体を分割する。
行・列の置換の符号は `t=0` で `det(P)=+1` と突き合わせて確定すると、

```text
det L(t) = (1-t²)^4 (1+t²)^4
         = (t²-1)^4 (t²+1)^4.
```

実数tに対しては `t=±1` が唯一の特異点。そこで4つの2×2ブロックが階数1になり、残り4ブロックが階数2なので `rank L(±1)=12`。 `H_t=L(t)^T L(t)` も同じ階数で、`det H_t=det L(t)^2`。

**検証範囲の区別:** `block_index_swap`・`block_coefficients`・`blockDet_formula` はLean追加原稿の対象だが、16×16行列全体の行列式公式・階数12を直接述べるLean定理は今回含まない。この全体への組み直しは紙上のブロック置換の議論である。

## 3. 零因子と4つの具体的な零方向

左作用を整数係数上に定義し `leftPencil(t,v)=L(t)v` とする。
`t=1` では次の4つがゼロへ写る（互いに異なる2要素の支持を持つ）。

```text
e4+e13, e5-e12, e6-e15, e7+e14
```

`t=-1` では

```text
e4-e13, e5+e12, e6+e15, e7-e14.
```

`kernelVector_coordinates` により、各ベクトルの独立した座標に係数を読める。従ってこれら4つのベクトルは整数・有理数・実数上で一次独立である。
`(e3+e10)(e6-e15)=0` という具体的な十六元数の零因子も含める。

## 4. 出典への検算

ユーザー添付の `verify_smooth.py` は実行して `ALL CHECKS PASS`。さらに元の `sedenion16.py` から生成した `eps` を使い、16探針×32状態の全復元・非復元分類、8ブロックの係数の符号、`t=±1` の各4本の零ベクトルを純Pythonの整数演算で検算済み。

これらは有限の例示的再計算であり、Lean統合検証の代用ではない。

## 5. Lean検証入口

対象: `linear_input/lean_check/F16RecoverySpectrum.inc`。
登録先: `tools/verify_main_result.py`、`tools/verify.py`。

```sh
python -B -X utf8 tools/verify.py --proof-only
```

Lean 4.30.0-rc2 / 固定mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持し、`--trust=0`、全公理監査、警告・禁止トークン・ソース変更0を成功条件とする。
本追補のCIは成功。統合先はPR #3の研究用ブランチとし、`main` へは直接マージしない。

なお非結合な十六元数の演算とクンマー拡大体のガロア群は同じ代数構造ではない。ここに構成したのはF0の観測/未来識別および有限の線形代数との厳密な接続である。
