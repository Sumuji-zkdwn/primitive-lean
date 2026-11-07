#!/usr/bin/env python3
"""Write docs/dependency/pr-inventory/README.md from the inventory data and the ERG evidence."""
import json
import sys

D = "docs/dependency/pr-inventory"
EVIDENCE = sys.argv[1]  # ERG-Aout logs/.../evidence.json (decision proposals)
C = json.load(open(D + "/data/compare.json"))["prs"]
S = {p["number"]: p for p in json.load(open(D + "/data/structure.json"))["prs"]}
F = json.load(open(D + "/data/failures.json"))
E = {r["number"]: r for r in json.load(open(EVIDENCE))["prs"]}
LABEL = {"integrate": "本線候補", "branch": "分岐", "absorb": "吸収", "choose_version": "版の選択", "defer": "保留", "tooling": "道具類"}


def ci(r):
    c = r["ci"]
    if not c:
        return "記録なし"
    if not any("integration" in x["name"].lower() for x in c) and r["kernel"]["status"] != "ok":
        return "統合検証の記録なし"
    return "成功" if all(x["conclusion"] == "success" for x in c) else \
        "失敗あり" if any(x["conclusion"] == "failure" for x in c) else "/".join(sorted({x["conclusion"] for x in c}))


ok = [r for r in C.values() if r["kernel"]["status"] == "ok"]
L = ["# 未統合 PR の棚卸し：カーネル水準の測定（2026-11-07）", "",
     "`main` = `67fdf6b` に対して、未統合 PR 58 件を測定した結果。判定案と ERG のラウンド記録は ERG-Aout の "
     "`logs/2026-11-07-primitive-lean-pr-inventory/` にある。ここでは測定方法と数値を記録する。", "",
     "## 読み方の前提", "",
     "- 数値は「Lean が受理した項に現れる定数」に基づく。依存の数学的な必要性や、内容の新規性を判定したものではない。",
     "- `main` を参照しないことは、`main` から導出できないことの証明ではない。",
     "- 判定案は候補で、採否は人が決める。",
     "- Lean が宣言の間で使い回す補助証明（`_proof_N` など）は、作った宣言への依存とは数えず、中身を展開している"
     "（初版はこれを依存と数えており、#31・#36・#40・#41 を誤って `main` 参照ありとしていた）。", "",
     "## 方法", "",
     "1. **構造（git のみ）**：`tools/deps/pr_inventory.py`。`main` との分岐点からヘッドまでの Lean ファイルを、パスとブロブ SHA で記録。"
     "積み重なった PR では、親 PR のヘッドにない分をその PR 固有の内容とし、すでに `main` に同一バイトで入っているファイルは除外。",
     "2. **カーネル**：`tools/deps/pr_kernel.py`。他の PR に含まれない先端のヘッドごとに、そのヘッド自身の `tools/verify.py --proof-only` を実行し、"
     "組み立て・未登録のプローブ・独立した `lean/*.lean` をコンパイルして依存を抽出。PR 自身の CI がプローブを単独ファイルとしてコンパイルしている場合"
     "（#50〜#54）は同じ方法で単独に測定。",
     "3. **集計**：`tools/deps/pr_compare.py`。`main` にない宣言のうち PR 固有ファイルに属するものを、その PR の新しい内容とする。",
     "4. **CI**：GitHub Actions の実行履歴（1200 件）を PR ヘッドの SHA で突き合わせ。", "",
     "## 全体", "",
     f"- 未統合 PR：58 件。PR 固有ファイルの字句上の定理数の合計は {sum(S[int(n)]['own_theorem_count'] for n in C)}",
     f"- カーネル測定に成功：{len(ok)} 件。新しい定理の合計は {sum(r['kernel']['new_theorems'] for r in ok)}、吸収案の重複を除くと "
     f"{sum(r['kernel']['new_theorems'] for r in ok if E[int(r['number'])]['proposal'] != 'absorb')}",
     f"- ヘッド自身の証明検査が通らない PR：{len(F['proof_check_failures'])} 件（下表）",
     "- Lean ソースを持たない PR：4 件（#76、#79、#84、#90）", "",
     "### ヘッド自身の証明検査が通らない PR", "",
     "| PR | 最初のエラー | エラー行数 | CI の記録 |", "|---|---|---:|---|"]
for n, v in F["proof_check_failures"].items():
    L.append(f"| #{n} | `` {v['first_error']} `` | {v['error_lines']} | {ci(C[str(n)])} |")
L += ["", "### PR ごとの数値", "",
      "新定理・新定義は `main` にない宣言のうち PR 固有ファイルに属するもの。main 参照は推移的依存に `main` の宣言を含む定理の数、"
      "main 定理を証明に使用は証明項の連鎖に `main` の定理を含む定理の数。", "",
      "| PR | 判定案 | 測定 | 新定理 | 新定義 | main 参照 | main 定理を証明に使用 | 初期層に到達 | 最大の深さ | 既存定理1つの適用 | 決定手続きのみ | CI |",
      "|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---|"]
for n in sorted(C, key=int):
    r, k, e = C[n], C[n]["kernel"], E[int(n)]
    if k["status"] == "ok":
        sh = k["shapes"]
        L.append(f"| #{n} | {LABEL[e['proposal']]} | {r['kernel_tip']} | {k['new_theorems']} | {k['new_definitions']} | "
                 f"{k['theorems_using_main_any_edge']} | {k['theorems_using_main_theorem_in_proof']} | {k['theorems_reaching_initial']} | "
                 f"{k['max_proof_depth']} | {sh.get('application_of_earlier_theorem', 0)} | {sh.get('decision_procedure_only', 0)} | {ci(r)} |")
    else:
        L.append(f"| #{n} | {LABEL[e['proposal']]} | — | — | — | — | — | — | — | — | — | {ci(r)} |")
L += ["", "「測定」列は数値を取ったヘッド（`53s` は単独ファイルとしての測定）。", "",
      "## データ", "",
      "- `data/structure.json`：構造の棚卸し（ファイル、ブロブ、親子、包含、同一内容、同名異版、宣言名の衝突）",
      "- `data/compare.json`：PR ごとのカーネル水準の集計と、新しい宣言の名前の一覧",
      "- `data/ci.json`：PR ヘッドごとの CI 実行",
      "- `data/failures.json`：証明検査とプローブのコンパイルが失敗した箇所",
      "- `data/status-*.json`：各測定の段階ごとの終了コードと所要時間"]
open(D + "/README.md", "w").write("\n".join(L) + "\n")
print("wrote", D + "/README.md")
