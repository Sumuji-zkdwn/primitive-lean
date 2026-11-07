#!/usr/bin/env python3
"""Summarise the two-stage copy check (CopyCheck.lean + copy_ring_stage.py) into README.md."""
import glob
import json
import os
import sys

D = sys.argv[1] if len(sys.argv) > 1 else "docs/dependency/grounding/copies"
rows = []
for f in sorted(glob.glob(D + "/stage1-*.json")):
    t = os.path.basename(f)[7:-5]
    d = json.load(open(f))
    s2 = f"{D}/stage2-{t}.json"
    e = json.load(open(s2)) if os.path.exists(s2) else dict(proved_equal=0, attempted=0, skipped_private=0)
    rows.append((t, d["candidates"], d["type_matches"], d["copies"], e["attempted"], e["proved_equal"], e["skipped_private"],
                 [r for r in d["rows"] if r["value"] == "definitionally_equal"]))
L = ["# 初期の定義の「作り直された写し」の検出", "",
     "「新しい対象」（初期層に触れずに定義されたプロジェクトの定義）が、名前を変えただけの初期の定義ではないかを調べた。", "",
     "## 方法", "",
     "1. **第 1 段（定義の展開による同一性）**：候補と初期の定義 46 個の全組について、型が定義的に等しいかを `isDefEq` で調べ、"
     "等しい組は定数そのものの `isDefEq` を調べる（`tools/deps/CopyCheck.lean`）。宇宙パラメータは新しいメタ変数で単一化する。",
     "2. **第 2 段（代数による同一性）**：型が等しく第 1 段で同一とされなかった組について、`funext` → 両方を展開 → `ring` で "
     "`C = I` の証明を試みる（`tools/deps/copy_ring_stage.py`）。",
     "3. **対照**（`control/`）：`f`・`E`・`input` を別名で書き写したものは第 1 段で、項の順序を入れ替えた `f` は第 2 段で同一と判定された。"
     "値の違う関数は同一とされなかった。", "",
     "## 結果", "",
     "| 環境 | 候補 | 型が一致した組 | 第 1 段で同一 | 第 2 段の試行 | 第 2 段で同一 | private のため試行不可 |",
     "|---|---:|---:|---:|---:|---:|---:|"]
for t, c, tm, cp, at, pr, sk, eq in rows:
    L.append(f"| {'main' if t == 'main' else 'PR 測定 ' + t} | {c} | {tm} | {cp} | {at} | {pr} | {sk} |")
hits = [(t, r) for t, *_, eq in rows for r in eq]
L += ["", "第 1 段で同一とされた組：" + ("、".join(f"`{r['candidate']}` = `{r['initial']}`（{t}）" for t, r in hits) or "なし") + "。",
      "`DarkBrightObservation.Summary` と Elastica 内部の `Parameters` は、どちらも実数の組を表す型の名前で、数学的な対象の写しではない。",
      "第 2 段の失敗は、ログを確認したところ、すべて目標の値が実際に異なる（`unsolved goals`、`ring_nf made no progress`）ものだった。", "",
      "副産物として、初期層の内部で `LinearInputCalculus.potential` と `LinearInputDesign.f` が定義として同一であることが分かった（対照実験の出力）。", "",
      "## この検査が見ないもの", "",
      "- 型の形が違う写し：引数の順序が違う、パラメータを固定した特殊化、組にまとめた引数など。"
      "例：`LinearInputBranchForgetting.chebyshevThree`（4x³−3x）は、定理 `chebyshevThree_eq_input` によって初期の `input 4 (-3)` と等しいことが示されているが、型の形が違うのでこの検査では同一とされない。"
      "こうした関係は `../README.md` の「橋渡し」の分類で別に数えている。",
      "- `private` な定義との第 2 段の比較（別ファイルから名前を参照できないため）。",
      "- 展開と `ring` で示せない同一性（三角関数の恒等式、場合分け、極限など）。"]
open(D + "/README.md", "w").write("\n".join(L) + "\n")
print("wrote", D + "/README.md")
