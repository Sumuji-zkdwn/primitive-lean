#!/usr/bin/env python3
"""Write the human-readable dependency report and the compact data files."""
from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path

FOCUS_MAIN = [
    "Elastica.locallyMinimizing_necessary_conditions",
    "LinearInputMainResult.locallyMinimizing_pressure_curvature_phase",
    "LinearInputMainResult.pressure_parameters_global_feedback",
    "LinearInputQuarticClassification.unique_global_minimum_iff",
    "LinearInputBranchFibers.real_inverse_card_regular",
]
FOCUS_REPRESENTATIVE = [
    "LinearInputOperatorRefinement.strict_refinement_splits_quotient",
    "LinearInputMetaRuleExtension.metaStep_sound",
    "LinearInputBayes.posterior_commute",
    "LinearInputWFSObservation.observationDistance_triangle",
    "LinearInputF16UnexpectedBridges.singular_iff_chebyshev_critical",
    "LinearInputCurvatureRigidity.locallyMinimizing_phase_minimum_exclusion",
]
SHAPE_JA = {
    "application_of_earlier_theorem": "既存定理1つの適用",
    "decision_procedure_only": "決定手続きのみ",
    "library_only": "mathlib/core のみ",
    "composite": "複合",
}


def short(src):
    return (src or "?").split("/")[-1]


def transitive(N):
    adj = {n: set(r["direct"]["proof"]) | set(r["direct"]["statement"]) | set(r["direct"]["definition"])
           for n, r in N.items()}
    memo = {}
    for n in N:
        seen, stack = set(), [n]
        while stack:
            x = stack.pop()
            for y in adj.get(x, ()):
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        memo[n] = sorted(seen)
    return memo


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--deps", required=True)
    ap.add_argument("--validation", required=True)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--commit", required=True)
    a = ap.parse_args()
    g = json.loads(Path(a.deps).read_text())
    v = json.loads(Path(a.validation).read_text())
    N = g["nodes"]
    out = Path(a.outdir)
    (out / "data").mkdir(parents=True, exist_ok=True)

    T = {n: r for n, r in N.items() if r["kind"] == "theorem"}
    layers = ("initial", "subsequent", "autonomy")
    lines = []
    w = lines.append

    w("# カーネル受理済み宣言の依存関係（primitive-lean）")
    w("")
    w(f"対象コミット: `{a.commit}`（main）。自動生成定理は `autonomy/verified-operator-growth` の台帳 cycle 1–2 と SHA-256 が一致するソースを、その上に積んでコンパイルしたものです。")
    w("")
    w("## 読み方の前提")
    w("")
    w("- 辺は「Lean が受理した項の中に、その定数が現れる」ことだけを表します。その依存が数学的に必要だという意味ではありません。")
    w("- 初期層への経路がないことは、初期層から導出できないことの証明ではありません。")
    w("- 4 種類の関係を混ぜずに出力します。")
    w("  1. **proof**：定理の証明項に現れる定数")
    w("  2. **statement / definition**：命題の型、または定義本体に現れる定数")
    w("  3. **module**：import によるモジュール依存。Elastica ライブラリのみ。線形入力側は 1 ファイルに連結されるため、登録順しかありません")
    w("  4. **conceptual**：このツールは生成しません。ERG/HMDG の ConceptBridge・ProofBridge は未検証の候補のまま扱います")
    w("- 層の定義")
    w("  - **initial**：`lean/Elastica/` の 24 モジュールと、`All.lean` を構成する 36 部品")
    w("  - **subsequent**：`MainResult.lean` に登録順に連結される 60 の追補")
    w("  - **autonomy**：自動生成された有限模型")
    w("  - **mathlib / core / batteries**：外部ライブラリ")
    w("- 補助定数（`eq_1`、`match_1`、`_proof_N`、`_simp_N` など）は持ち主の宣言にまとめています。自分の補助定数の中身は自分の辺として扱い、他の宣言の補助定数への参照はその持ち主への参照として扱います。")
    w("")

    w("## 抽出の検証")
    w("")
    rd = v["report_declarations"]
    w(f"- 検証レポートの全 {rd['expected']} 宣言について、層とソースファイルが一致しました（不一致 {rd['mismatched']}）。レポートにないノード {rd['extra_nodes']} 個は、`private` 宣言・構造体・自動生成分です。")
    ke = v["known_edges_main_result"]
    w(f"- 主定理 2 の証明項から抽出した定理参照は、ソースのタクティクに書かれた 6 補題と{'一致しました' if ke['equal'] else '一致しませんでした'}。")
    lv = v["lexical_vs_kernel"]
    w(f"- 字句照合との比較（後続定理の証明内のプロジェクト定理参照）：両方にあるもの {lv['kernel_and_lexical']}、カーネル項だけにあるもの {lv['kernel_only']}（インスタンス解決・型クラス経由）、字句だけにあるもの {lv['lexical_only_unambiguous']}（名前は書かれているが、最終的な項には残らない）。")
    w("")

    w("## 規模")
    w("")
    w("| 層 | 定理 | 定義・型 |")
    w("|---|---:|---:|")
    for L in layers:
        w(f"| {L} | {sum(r['layer']==L for r in T.values())} | {sum(r['layer']==L and r['kind']!='theorem' for r in N.values())} |")
    w("")
    w("「初期 465 定理」は、既存の検証器が正規表現で `theorem`/`lemma` 行を数えた値です。ここでの initial の定理数は、その正規表現が拾わない `private` 定理、インスタンス、自動生成された合同補題を含むため、数が異なります（差 11）。")
    w("")

    def focus_table(names, title):
        w(f"### {title}")
        w("")
        w("| 宣言 | 層 | 証明の深さ | 初期層までの距離（証明のみ / 全種類） | 推移的依存（層別） | 証明の形 |")
        w("|---|---|---:|---|---|---|")
        for n in names:
            r = N.get(n)
            if not r:
                w(f"| `{n}` | （見つからない） | | | | |")
                continue
            hp = r["hops_to_initial_proof_only"]
            ha = r["hops_to_initial_any_edge"]
            tl = ", ".join(f"{k} {v}" for k, v in sorted(r["transitive_by_layer"].items()))
            shape = SHAPE_JA.get(r["proof_shape"], r["proof_shape"])
            if r["proof_shape"] == "application_of_earlier_theorem":
                shape += f"（`{r['head']}`）"
            w(f"| `{n}` | {r['layer']} | {r['proof_depth']} | {'なし' if hp is None else hp} / {'なし' if ha is None else ha} | {tl} | {shape} |")
        w("")

    w("## 小規模検証：主定理・自動生成・代表的な後続定理")
    w("")
    w("証明の深さは、プロジェクト内の定理だけをたどる証明項の連鎖の最長段数です（0 なら、証明がプロジェクトの定理を使っていない）。距離 0 は、その宣言自身が初期層であることを示します。")
    w("")
    focus_table(FOCUS_MAIN, "README の主定理 5 件")
    auto = sorted(n for n, r in T.items() if r["layer"] == "autonomy" and n.startswith("LinearInputAutoCycle00001"))
    focus_table(auto, "自動生成定理（cycle 1。cycle 2 は数値だけが異なる同形）")
    focus_table(FOCUS_REPRESENTATIVE, "代表的な後続定理")

    sub = [r for r in T.values() if r["layer"] == "subsequent"]
    reach_any = sum(r["reaches_initial_any_edge"] for r in sub)
    reach_proof = sum(r["hops_to_initial_proof_only"] is not None for r in sub)
    w("## 全体：後続定理は初期層からどこまで届いているか")
    w("")
    w(f"- 後続 {len(sub)} 定理のうち、全種類の辺で初期層に到達するもの：**{reach_any}（{reach_any*100//len(sub)}%）**")
    w(f"- 証明項の連鎖だけで初期定理に到達するもの：**{reach_proof}（{reach_proof*1000//len(sub)/10}%）**")
    init_nodes = [n for n, r in N.items() if r["layer"] == "initial"]
    used = collections.Counter()
    used_proof_thm = set()
    for r in N.values():
        if r["layer"] in ("subsequent", "autonomy"):
            for cat in ("proof", "statement", "definition"):
                for t in r["direct"][cat]:
                    if N.get(t, {}).get("layer") == "initial":
                        used[t] += 1
                        if cat == "proof" and N[t]["kind"] == "theorem":
                            used_proof_thm.add(t)
    w(f"- 後続層・自動生成層から直接参照される初期ノード：{len(used)} / {len(init_nodes)}。そのうち後続の**証明**で使われる初期**定理**は {len(used_proof_thm)} / {sum(N[n]['kind']=='theorem' for n in init_nodes)}")
    w("- 後続から初期層への接続の大半は、定義（`LinearInputDesign.f`・`E`・`input`、`Elastica.xCoord` など）を命題の中で再利用する形です。初期の**定理**を証明に使う形は少数です。")
    w("")
    w("よく参照される初期ノード（後続層からの直接参照数、全種類合計）：")
    w("")
    w("| 参照数 | 初期ノード | 種類 |")
    w("|---:|---|---|")
    for t, k in used.most_common(12):
        w(f"| {k} | `{t}` | {N[t]['kind']} |")
    w("")

    w("### 追補ファイル別")
    w("")
    w("| 追補 | 定理数 | 初期層に到達（全種類） | 証明のみで到達 | 最大の証明の深さ | 既存定理1つの適用 | 決定手続きのみ |")
    w("|---|---:|---:|---:|---:|---:|---:|")
    per = collections.defaultdict(list)
    for r in sub:
        per[r["source"]].append(r)
    for s, rs in sorted(per.items(), key=lambda kv: (sum(r["reaches_initial_any_edge"] for r in kv[1]) / len(kv[1]), kv[0])):
        w(f"| {short(s)} | {len(rs)} | {sum(r['reaches_initial_any_edge'] for r in rs)} | "
          f"{sum(r['hops_to_initial_proof_only'] is not None for r in rs)} | {max(r['proof_depth'] for r in rs)} | "
          f"{sum(r['proof_shape']=='application_of_earlier_theorem' for r in rs)} | {sum(r['proof_shape']=='decision_procedure_only' for r in rs)} |")
    w("")
    zero = [s for s, rs in per.items() if not any(r["reaches_initial_any_edge"] for r in rs)]
    w(f"どの定理も初期層に到達しない追補は {len(zero)} / {len(per)} ファイルです。これらは初期層と無関係に、mathlib と自前の定義の上に立っています。初期層から導出できないという意味ではありません。")
    w("")

    w("## 証明の深さの分布（後続定理）")
    w("")
    w("| 深さ | 定理数 |")
    w("|---:|---:|")
    for d, k in sorted(collections.Counter(r["proof_depth"] for r in sub).items()):
        w(f"| {d} | {k} |")
    w("")

    w("## 一般定理の単なる具体化と考えられる箇所（ヒューリスティック）")
    w("")
    w("判定規則：束縛変数とメタデータを外した証明項の先頭が、別のソースファイルにあるプロジェクト定理 1 つです。かつ、他に使うプロジェクト定理が同じファイル内の補題だけである場合、「既存定理1つの適用」とします。これは項の形だけに基づく判定で、数学的に新しい内容がないことの証明ではありません。")
    w("")
    for L in layers:
        c = collections.Counter(r["proof_shape"] for r in T.values() if r["layer"] == L)
        w(f"- {L}：" + "、".join(f"{SHAPE_JA[k]} {c.get(k,0)}" for k in SHAPE_JA))
    w("")
    w("| 定理 | 層 | 適用している定理 |")
    w("|---|---|---|")
    for n, r in sorted(T.items()):
        if r["proof_shape"] == "application_of_earlier_theorem" and r["layer"] != "initial":
            w(f"| `{n}` | {r['layer']} | `{r['head']}` |")
    w("")

    w("## モジュール依存（import、Elastica のみ）")
    w("")
    w("| モジュール | import しているプロジェクト内モジュール |")
    w("|---|---|")
    for m in sorted(g["module_imports"], key=lambda x: x["module"]):
        ims = [i for i in m["imports"] if i.startswith(("Elastica", "PrimitiveMain"))]
        w(f"| `{m['module']}` | {', '.join('`'+i+'`' for i in ims) or '—'} |")
    w("")
    w("`PrimitiveMain` は検証済みの `MainResult.lean` のコピーで、`AutonomyProbe` は自動生成ソースを積んだ検査用モジュールです。")
    w("")

    w("## データ")
    w("")
    w("- `data/deps.json`：全ノードの直接依存（proof / statement / definition 別）、外部ライブラリ参照数、到達距離、深さ、証明の形")
    w("- `data/transitive.json`：プロジェクト内の推移的依存（全種類の辺）")
    w("- `data/source_edges.json`：ソースファイル間の集約辺")
    w("- `data/validation.json`：上記の検証結果")
    w("")
    w("再生成：`bash tools/deps/run.sh`（Lean と mathlib のキャッシュが必要。約 5 分）")

    (out / "README.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    (out / "data/deps.json").write_text(json.dumps({k: g[k] for k in ("scope", "inputs", "source_spans", "nodes")},
                                                   ensure_ascii=False, separators=(",", ":")))
    (out / "data/transitive.json").write_text(json.dumps(transitive(N), separators=(",", ":")))
    (out / "data/source_edges.json").write_text(json.dumps(g["source_edges"], ensure_ascii=False, indent=1))
    (out / "data/validation.json").write_text(json.dumps(v, ensure_ascii=False, indent=1))
    print("wrote", out)


if __name__ == "__main__":
    main()
