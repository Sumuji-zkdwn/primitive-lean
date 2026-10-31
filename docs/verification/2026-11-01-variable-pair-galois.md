# 多項式Eの変数対：三次判別式・ヘッセ退化・符号の8分類

## Lean統合検証結果（2026-11-01 JST）

GitHub Actions [#41216334895](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41216334895)（対象ソースコミット `55c39a38ac3a40361f9956d27f9963d48b271d4f`）で **completed / success**。

- 固定Lean 4.30.0-rc2、固定mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。
- `python -B -X utf8 tools/verify.py --proof-only`：passed=true。joint / supplement とも終了コード0。
- `lake env lean --trust=0 ../linear_input/lean_check/MainResult.lean`：成功。**776定理・930宣言**を検査。
- 新規 `VariablePairGaloisBridge.inc`：21定理・10定義、31宣言。全930宣言の公理監査成功（`joint_axiom_audit=true`）。既存宣言の公理依存一致（`baseline_axioms_match=true`）。
- `warnings`、`errors`、`unexpected`、`forbidden_tokens`、`changed_during_verification` はいずれも空。未許可公理および `sorryAx` なし。
- [完全な検証アーティファクト](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/41216334895/artifacts/13048746733)（artifact ID `13048746733`、88,058 bytes）。
- 新規原稿のSHA-256 `952c002986aa5ba44f350478ef7e327d65ac87763173419e023b7dcda814b0a3`。

なお、`signShape` の像が8種類であることと、`flipX`・`flipY` がその値を保存することはLeanで証明済み。**4元の反転群の軌道と `signShape` の各ファイバーが完全に一致する一般定理は今回のLean原稿には含まない。** 有限の32通りでは、`flipY` が第4ビットを反転し `flipX` が第4・第5ビットを反転するため、これらからその2ビットを独立に変えられ、1クラス4個・計8軌道と直接確かめられる。


2026-11-01 JST、PR #8 の加法的Lean追補。参考：ローカル研究原稿
`abstract_elastica_reference_2026-10-19/variable_pairs_2026-10-20/読む.html`
に対応する「二変数の選び方の比較.md」。元の15組全分類と32符号選択を保持する。

## 対象と、実際の既存Lean定義への接続

既存 `LinearInputVariablePairs.energy` を変えない。

```math
E(x,y)= kx^2/2 + λx^4/4 + ay^2/2 -cxy-ux.
```

`a≠0` のとき、`E_y=0` は `y=cx/a` と同値。従って
```math
E_x=E_y=0 \iff y=cx/a,\quad
F(x)=λx^3+(k-c^2/a)x-u=0.
```

既存 `gradXY_formula`、`gradXY_jacobian` から、新しい縮約係数
`b=k-c^2/a` を用いて
```math
\det D^2E(x,y)=a(3λx^2+b)=aF'(x).
```

三次判別式の式
```math
\Delta=-4λb^3-27λ^2u^2
```
から、`F=F'=0 ⇒ Δ=0`、`Δ≠0 ⇒ F=0でF'≠0` および
「退化した停留点なら判別式0」を形式化する。**λ=0の場合はΔ=0が自明になり得るため、Δ=0から重根の存在を無条件に結論しない。**

`3λs²=-4b` を仮定すると
```math
F(st)=\frac{\lambda s^3}{4} T_3(t)-u.
```
特に `λ=4,b=-3` では `Δ=432(1-u²)`、臨界値は `u=±1`。
これは実際の定理 `LinearInputBranchForgetting.chebyshevThree` に接続しており、ガロア群が二面体群に同型だと無条件に主張するものではない。

## 符号32通りの扱い

既存の `signedEnergy (σ : Fin 5→Bool)` を使用する。
`flipX` は符号3,4（混合項と入力項）を反転、
`flipY` は符号3（混合項）を反転する。

目標となる具体的な座標変換は
```math
E_{\mathrm{flipX}(\sigma)}(x,y)=E_\sigma(-x,y),\qquad
E_{\mathrm{flipY}(\sigma)}(x,y)=E_\sigma(x,-y).
```

3個の固定符号（`k,λ,a`）を抽出する `signShape` を定義し、
`signShape` の像は正確に`2^3=8`種類とする。
有限計算で全32パターンは4個ずつの8組となる。固定値・定義域の移送を忘れると一般の15変数対の同値性とはならない。係数が0の場合、異なる形式的符号が同じ関数を定めることもある。

## コード・検証範囲

- `linear_input/lean_check/VariablePairGaloisBridge.inc`: 既存のLean証明原稿に追加する定理群。
- `tools/verify_main_result.py`: `LinearInputVariablePairGalois` 名前空間の補助原稿として登録。
- `tools/verify.py`: 定理群の監査スコープを追加。
- 新規原稿の`--trust=0`と公理監査が成功するまで、既存の755定理・899宣言を検証済み基準として保持する。

検証コマンド：

```bash
python -B -X utf8 tools/verify.py --proof-only
```

初回Actions #41214458722 は既存joint検査成功、追補検査失敗。
原因：Leanの `unnecessarySeqFocus` の警告3件と、
`signedEnergy_flipX` の簡約で未解決の明らかな論理式、
`signedEnergy_flipY` の過剰な `ring` 呼び出し。
新規数学命題の反例を示す失敗ではなく、証明スクリプトを修正し再検査する。
