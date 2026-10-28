"""Generate a staged, self-bootstrapping Kaggle notebook from this checkout."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def committed_bytes(source_ref, relative_path):
    """Return Git's canonical committed bytes, independent of checkout newlines."""
    try:
        return subprocess.check_output(
            ["git", "show", f"{source_ref}:{relative_path}"], cwd=ROOT,
            stderr=subprocess.DEVNULL,
        )
    except (subprocess.CalledProcessError, FileNotFoundError):
        return (ROOT / relative_path).read_bytes()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-ref", required=True, help="GitHub commit containing both proof-only adapter files")
    parser.add_argument("--source-mode", choices=("auto", "path", "github"), default="auto")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--setup-one-cell", action="store_true", help="Combine initialization and setup into one executable cell")
    modes.add_argument("--proof-check-one-cell", action="store_true", help="Combine initialization, setup and proof checks into one executable cell")
    parser.add_argument("--output", type=Path, help="Write the notebook to this path instead of the tracked notebooks directory")
    args = parser.parse_args()
    if len(args.source_ref) != 40 or any(c not in "0123456789abcdef" for c in args.source_ref):
        parser.error("source-ref must be a full commit SHA")
    try:
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True, stderr=subprocess.DEVNULL
        ).strip()
    except Exception:
        head = None
    if head is not None and head != args.source_ref:
        parser.error(f"source-ref must match the checked-out source commit ({head})")
    inventory = json.loads((ROOT / "docs/import/archive_inventory.json").read_text("utf-8"))
    rows = [r for r in inventory["files"] if r["imported"]]
    expected = {r["path"]: hashlib.sha256(committed_bytes(args.source_ref, r["path"])).hexdigest() for r in rows}
    # Accept the original verifier in the uploaded ZIP, then apply the exact
    # adapter from the selected GitHub snapshot. Proof sources are not overlaid.
    expected["tools/verify.py"] = next(r["sha256"] for r in rows if r["path"] == "tools/verify.py")
    overlays = {p: committed_bytes(args.source_ref, p).decode("utf-8")
                for p in ["tools/verify.py", "tools/proof_only.py"]}
    support = (ROOT / "notebooks/kaggle_support.py").read_text("utf-8")
    snapshot = {"repository": "Sumuji-zkdwn/primitive-lean", "source_commit": args.source_ref,
                "original_import_commit": "b358f1a2753637992cdcfbaa5f354db3562ecc46",
                "support_sha256": hashlib.sha256(support.encode()).hexdigest()}
    installer = {"url": "https://raw.githubusercontent.com/leanprover/elan/9605b24b08cf68b78dce0014b6fa01be1f8e2cee/elan-init.sh",
                 "sha256": "a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53"}
    cells = []

    def cell(kind, text, hidden=False):
        value = {"cell_type": kind, "id": hashlib.sha256((str(len(cells)) + text).encode()).hexdigest()[:12],
                 "metadata": {"jupyter": {"source_hidden": True}} if hidden else {},
                 "source": text.splitlines(keepends=True)}
        if kind == "code":
            value.update(execution_count=None, outputs=[])
        cells.append(value)

    cell("markdown", """# primitive-lean × Kaggle

GitHubの固定コミットと、Kaggle側の原本をハッシュで対応させます。まず設定を変えずに **Run All** でファイルの対応確認だけを実行してください。

1. Kaggleに既存の原本フォルダ、または同じ **archive.zip** をInputとして用意します。自動検出できなければ下の `SOURCE_PATH` を指定します。
2. 環境準備に進むときはNotebookの **InternetをOn**、`RUN_SETUP=True`。
3. 実際の検査に進むときは `RUN_SETUP=True` と `RUN_PROOFS=True`。CPUで実行します。

ローカル原本の利用にはGitHubトークン不要です。GitHubから直接取得する場合だけ `SOURCE_MODE='github'` とし、Kaggle Secretsに `GITHUB_TOKEN`（対象リポジトリのContents読み取り）を登録します。トークンをコードへ貼り付けません。

検査結果の `passed` は今回のLean証明・公理検査の範囲だけを表します。過去ZIPの保存監査・本文描画・配送監査は別です。NotebookはKaggleコンペへの提出やGitHubへの書き戻しを行いません。
""")
    cell("code", f"""# ここだけ必要に応じて変更します
SOURCE_MODE = {json.dumps(args.source_mode)}       # auto / path / github
SOURCE_PATH = ""           # 例: /kaggle/input/your-data/archive.zip または原本フォルダ
RUN_SETUP = False           # 初回はFalseのままファイル対応だけ確認
RUN_PROOFS = False          # 実ビルドする段階でTrue（RUN_SETUPもTrue）
REBUILD = False             # Trueでこのプロジェクトのビルド生成物だけ再作成

WORKSPACE = "/kaggle/working/primitive-lean"
SOURCE_SEARCH_ROOTS = ["/kaggle/working", "/kaggle/input"]
GITHUB_SECRET_LABEL = "GITHUB_TOKEN"
REUSE_EXISTING_CACHE = True
""")
    bootstrap = support + "\nEXPECTED = " + repr(expected) + "\nOVERLAYS = " + repr(overlays) + "\nSNAPSHOT = " + repr(snapshot) + "\nINSTALLER = " + repr(installer)
    bootstrap += """
RUN_ID = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S") + "-" + str(time.time_ns())[-6:]
REPORT_DIR = Path(WORKSPACE).parent / "primitive-lean-results" / RUN_ID
REPORT_DIR.mkdir(parents=True, exist_ok=True)
STATE = {"run_id": RUN_ID, "source_commit": SNAPSHOT["source_commit"],
         "source": {"status": "not_run"}, "setup": {"status": "not_run"},
         "proofs": {"status": "not_run"},
         "historical_preservation": "not_checked", "delivery_and_rendering": "not_checked"}

def show_output(path):
    path = Path(path)
    download = Path(WORKSPACE).parent / "primitive_lean_result.zip"
    if path.resolve() != download.resolve():
        shutil.copy2(path, download)
    print("結果ZIP:", download, "(", download.stat().st_size, "bytes)")
    print("KaggleのOutput欄を更新し、primitive_lean_result.zipのメニューからDownloadしてください。")

def notebook_stage(name, action):
    STATE[name] = {"status": "running"}
    save_json(REPORT_DIR / "notebook_run.json", STATE)
    try:
        STATE[name] = action()
    except Exception as error:
        STATE[name] = {"status": "failed", "error": str(error)}
        show_output(export_results(WORKSPACE, REPORT_DIR, STATE))
        raise
    save_json(REPORT_DIR / "notebook_run.json", STATE)
    print(name, STATE[name]["status"])
"""
    cell("code", bootstrap, hidden=True)
    cell("markdown", "## 1. 原本とGitHubの対応確認\n元の証明原稿は変更せず、統合入口のアダプター2ファイルだけNotebookに同梱した固定版を適用します。117ファイルを再照合し、対応するソースコミットを記録します。")
    cell("code", """config = {"workspace": WORKSPACE, "source_mode": SOURCE_MODE, "source_path": SOURCE_PATH,
          "search_roots": SOURCE_SEARCH_ROOTS, "secret_label": GITHUB_SECRET_LABEL,
          "reuse_cache": REUSE_EXISTING_CACHE}
notebook_stage("source", lambda: prepare_sources(config, EXPECTED, OVERLAYS, SNAPSHOT))
print("対応コミット:", SNAPSHOT["source_commit"])
print("一致したファイル:", STATE["source"]["verified_files"])
print("依存キャッシュ再利用:", STATE["source"]["dependency_cache_reused"])
""")
    cell("markdown", "## 2. Lean環境の準備\n`RUN_SETUP=True` のときだけ実行します。原本のLean・mathlib revisionを保持し、依存revisionを照合します。初回は取得に時間がかかります。")
    cell("code", """if RUN_SETUP:
    if STATE["source"]["status"] != "passed":
        raise RuntimeError("先に段階1を完了してください")
    notebook_stage("setup", lambda: setup_lean(WORKSPACE, Path(WORKSPACE).parent / "primitive-runtime", REPORT_DIR, INSTALLER))
else:
    print("環境準備: 未実行（RUN_SETUP=False）")
""")
    cell("markdown", "## 3. 実際の証明・公理検査\n元の統合入口 `tools/verify.py --proof-only` から、既存のjoint checker、続いて5追補のcheckerを実行します。前回の合格結果を流用せず、今回生成されたレポートと終了コードを確認します。")
    cell("code", """if RUN_PROOFS:
    if STATE["setup"]["status"] != "passed":
        raise RuntimeError("RUN_SETUP=Trueにして段階2も実行してください")
    STATE["proof_attempt_started_ns"] = time.time_ns()
    notebook_stage("proofs", lambda: run_proofs(WORKSPACE, REPORT_DIR, STATE["source"]["sha256"], REBUILD))
    print("今回の検査対象:", STATE["proofs"]["result"]["theorem_count"], "定理 /",
          STATE["proofs"]["result"]["declaration_count"], "宣言")
else:
    print("証明検査: 未実行（RUN_PROOFS=False）")
""")
    cell("markdown", "## 結果を保存\n段階別の成否、ソースハッシュ、実際の実行ログをZIPにまとめます。ソースZIP、キャッシュ、認証情報は含めません。失敗時にも、その時点の記録を保存します。結果は `/kaggle/working/primitive_lean_result.zip` をOutput欄からダウンロードします。")
    cell("code", """output = export_results(WORKSPACE, REPORT_DIR, STATE)
print(json.dumps({name: STATE[name]["status"] for name in ("source", "setup", "proofs")}, ensure_ascii=False, indent=2))
show_output(output)
""")
    if args.setup_one_cell or args.proof_check_one_cell:
        combined = "\n\n".join("".join(c["source"]) for c in cells if c["cell_type"] == "code")
        combined = combined.replace('RUN_SETUP = False', 'RUN_SETUP = True', 1)
        if args.proof_check_one_cell:
            combined = combined.replace('RUN_PROOFS = False', 'RUN_PROOFS = True', 1)
        cells = []
        if args.proof_check_one_cell:
            cell("markdown", """# primitive-lean：証明検査・1セル版

原本照合、Lean環境準備、証明・公理検査を一つのコードセルで順番に実行します。前のセルや前セッションの変数には依存しません。

生成時に固定されたGitHubコミットを読み取り、そのコミットと今回の実行ログを結果ZIPに記録します。原本ZIPをNotebook Inputから使う場合は、コード冒頭のSOURCE_MODEをautoに変更してください。

初期設定はRUN_SETUP=True、RUN_PROOFS=Trueです。Kaggle SecretsにContents読み取り専用のGITHUB_TOKENを登録し、InternetをOnにして唯一のコードセルを実行します。トークンをコードへ貼り付けないでください。

成功・失敗どちらの場合も、今回の段階別状態とログを /kaggle/working/primitive_lean_result.zip に保存します。KaggleのOutput欄からダウンロードしてください。NotebookはGitHubへ書き戻さず、コンペへ提出しません。
""")
        else:
            cell("markdown", """# primitive-lean：環境準備・1セル版

この版は初期化・原本の照合・Lean環境の準備を**1つのコードセル**で順番に実行します。前のセルや前のセッションの変数は不要です。

1. 同じ `archive.zip` をInputに追加するか、原本フォルダのあるKaggle環境で使います。
2. Notebookの **InternetをOn** にします。
3. 下のコードセルの **▶** を押します。設定変更は不要です。

この版の初期設定は `RUN_SETUP=True`、`RUN_PROOFS=False` です。今回の目標は `source: passed`、`setup: passed`、`proofs: not_run`。Lean証明検査の合格を意味しません。

原本が見つからない場合だけ、コード冒頭の `SOURCE_PATH` を指定してください。初回のツール・依存取得には時間がかかります。実行結果ZIPは末尾または失敗時に `/kaggle/working/primitive_lean_result.zip` に保存します。Output欄からダウンロードしてください。
""")
        cell("code", combined)
    notebook = {"nbformat": 4, "nbformat_minor": 5, "metadata": {
        "kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
        "language_info": {"name": "python", "version": "3.11"},
        "primitive_lean": snapshot}, "cells": cells}
    if args.proof_check_one_cell:
        filename = "primitive_lean_proof_check.ipynb"
    elif args.setup_one_cell:
        filename = "primitive_lean_setup_one_cell.ipynb"
    else:
        filename = "primitive_lean_kaggle.ipynb"
    path = args.output or (ROOT / "notebooks" / filename)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(notebook, ensure_ascii=False, indent=1) + "\n",
                    encoding="utf-8", newline="\n")
    print(path)


if __name__ == "__main__":
    main()
