"""Kaggle notebook support: select exact sources, prepare tools, record real runs.

The 717-theorem notebook embeds this module so the existing Kaggle archive can be
extended with commit-pinned proof sources without GitHub credentials. It never uploads or pushes to GitHub.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile


def sha_bytes(value):
    return hashlib.sha256(value).hexdigest()


def save_json(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", "utf-8")


def read_candidate(path, expected):
    """Read only known source paths; no general ZIP extraction is performed."""
    path = Path(path)
    if path.is_dir():
        return {p: (path / p).read_bytes() for p in expected if (path / p).is_file()}
    if not path.is_file() or not zipfile.is_zipfile(path):
        raise ValueError("Not a source directory or ZIP")
    if path.stat().st_size > 64 * 1024 * 1024:
        raise ValueError("Use a source-only ZIP smaller than 64 MiB")
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        if len(names) != len(set(names)):
            raise ValueError("Duplicate ZIP entries")
        suffix = "lean/lean-toolchain"
        prefixes = [n[:-len(suffix)] for n in names if n.endswith(suffix)]
        if len(prefixes) != 1:
            raise ValueError("ZIP must contain exactly one Lean project root")
        prefix = prefixes[0]
        result = {}
        for rel in expected:
            name = prefix + rel
            if name in names:
                info = archive.getinfo(name)
                if info.file_size > 4 * 1024 * 1024:
                    raise ValueError("Unexpected oversized source file")
                result[rel] = archive.read(info)
        return result


def source_matches(files, expected, overlays):
    return [p for p, digest in expected.items()
            if ((p not in files and p not in overlays)
                or (p not in files and p in overlays
                    and sha_bytes(overlays[p].encode("utf-8")) != digest)
                or (p in files and sha_bytes(files[p]) not in
                    {digest, sha_bytes(overlays[p].encode("utf-8")) if p in overlays else digest}))]


def find_candidates(roots):
    candidates = []
    for base in roots:
        base = Path(base)
        if not base.exists():
            continue
        for current, dirs, names in os.walk(base):
            here = Path(current)
            dirs[:] = [d for d in dirs if d not in
                       {".lake", ".git", "node_modules", "__pycache__", "primitive-lean-results"}]
            if (here / "lean/lean-toolchain").is_file():
                candidates.append(here)
                dirs[:] = []
            if "archive.zip" in names:
                candidates.append(here / "archive.zip")
            if len(here.relative_to(base).parts) >= 4:
                dirs[:] = []
            if len(candidates) >= 100:
                return candidates
    return candidates


class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        redirected = super().redirect_request(req, fp, code, msg, headers, newurl)
        if redirected is not None and urllib.parse.urlsplit(req.full_url).netloc != urllib.parse.urlsplit(newurl).netloc:
            redirected.remove_header("Authorization")
        return redirected


def github_download(repository, commit, secret_label, destination):
    """Read-only private archive download; no token in URL, log or Git config."""
    try:
        from kaggle_secrets import UserSecretsClient
        token = UserSecretsClient().get_secret(secret_label)
        request = urllib.request.Request(
            "https://api.github.com/repos/" + repository + "/zipball/" + commit,
            headers={"Authorization": "Bearer " + token, "Accept": "application/vnd.github+json",
                     "User-Agent": "primitive-lean-kaggle"})
        opener = urllib.request.build_opener(SafeRedirect())
        with opener.open(request, timeout=120) as response, open(destination, "wb") as target:
            total = 0
            while chunk := response.read(1024 * 1024):
                total += len(chunk)
                if total > 64 * 1024 * 1024:
                    raise ValueError("Source ZIP exceeds 64 MiB")
                target.write(chunk)
    except Exception:
        raise RuntimeError("GitHub取得に失敗。InternetとKaggle Secretsの読み取り権限を確認してください。") from None


def prepare_sources(config, expected, overlays, snapshot):
    root = Path(config["workspace"]).resolve()
    root.mkdir(parents=True, exist_ok=True)
    candidates = ([Path(config["source_path"])] if config["source_path"] else
                  find_candidates(config["search_roots"]))
    temporary = None
    if config["source_mode"] == "github":
        temporary = tempfile.TemporaryDirectory(prefix="primitive-github-")
        downloaded = Path(temporary.name) / "sources.zip"
        github_download(snapshot["repository"], snapshot["source_commit"], config["secret_label"], downloaded)
        candidates = [downloaded]
    elif config["source_mode"] not in {"auto", "path"}:
        raise ValueError("SOURCE_MODE must be auto, path or github")
    errors = []
    try:
        for candidate in candidates:
            try:
                files = read_candidate(candidate, expected)
                mismatches = source_matches(files, expected, overlays)
                if mismatches:
                    errors.append({"source": str(candidate), "missing_or_changed": mismatches[:8]})
                    continue
                source_root = candidate if candidate.is_dir() else None
                files.update({p: text.encode("utf-8") for p, text in overlays.items()})
                for rel, data in files.items():
                    target = root / rel
                    if not target.resolve().is_relative_to(root):
                        raise ValueError("Destination path escapes workspace")
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(data)
                hashes = {p: sha_bytes(data) for p, data in files.items()}
                if any(sha_bytes((root / p).read_bytes()) != digest for p, digest in hashes.items()):
                    raise ValueError("Copied source hash mismatch")
                cache = source_root / "lean/.lake/packages" if source_root is not None else None
                dest_cache = root / "lean/.lake/packages"
                reused = False
                if (config.get("reuse_cache", True) and cache is not None and cache.is_dir()
                        and str(cache.resolve()).startswith("/kaggle/working/")
                        and cache.resolve() != dest_cache.resolve() and not dest_cache.exists()):
                    dest_cache.parent.mkdir(parents=True, exist_ok=True)
                    dest_cache.symlink_to(cache.resolve(), target_is_directory=True)
                    reused = True
                return {"status": "passed", **snapshot, "source_subset_only": True,
                        "selected_input": "private GitHub snapshot" if temporary else str(candidate),
                        "verified_files": len(hashes), "sha256": hashes, "workspace": str(root),
                        "dependency_cache_reused": reused,
                        "adapter_overlay_paths": sorted(overlays), "lean_proofs": "not_run"}
            except (OSError, ValueError, zipfile.BadZipFile) as error:
                errors.append({"source": str(candidate), "error": str(error)})
    finally:
        if temporary is not None:
            temporary.cleanup()
    raise RuntimeError("対応する原本が見つかりません。SOURCE_PATHに原本フォルダ/ZIPを指定するか、archive.zipをInputへ追加してください。詳細: " + json.dumps(errors[:4], ensure_ascii=False))


def run_logged(args, cwd, logfile, timeout=1800):
    started = time.monotonic()
    print("実行:", " ".join(str(x) for x in args), flush=True)
    with open(logfile, "w", encoding="utf-8") as log:
        try:
            proc = subprocess.run(args, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                                  text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            raise RuntimeError("時間上限に達しました。ログを確認してください: " + str(logfile)) from None
    row = {"command": [str(x) for x in args], "exit_code": proc.returncode,
           "seconds": round(time.monotonic() - started, 3), "log": str(logfile)}
    if proc.returncode:
        print(Path(logfile).read_text("utf-8", errors="replace")[-5000:])
        raise RuntimeError("コマンドが失敗しました。ログ: " + str(logfile))
    return row


def setup_lean(root, runtime, report_dir, installer):
    root, runtime, report_dir = Path(root), Path(runtime), Path(report_dir)
    runtime.mkdir(parents=True, exist_ok=True)
    project = root / "lean"
    manifest_bytes = (project / "lake-manifest.json").read_bytes()
    toolchain_bytes = (project / "lean-toolchain").read_bytes()
    os.environ.pop("ELAN_TOOLCHAIN", None)
    binaries = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan"))) / "bin"
    os.environ["PATH"] = str(binaries) + os.pathsep + os.environ.get("PATH", "")
    runs = []
    if shutil.which("elan") is None:
        script = runtime / "elan-init.sh"
        try:
            with urllib.request.urlopen(installer["url"], timeout=120) as response:
                raw = response.read()
        except Exception:
            raise RuntimeError("Lean環境の取得に失敗。KaggleのInternetをOnにしてください。") from None
        if sha_bytes(raw) != installer["sha256"]:
            raise ValueError("Elan installer checksum mismatch")
        script.write_bytes(raw)
        runs.append(run_logged(["sh", str(script), "-y", "--default-toolchain", "none", "--no-modify-path"], runtime, report_dir / "elan-install.log"))
    runs.append(run_logged(["elan", "toolchain", "install", toolchain_bytes.decode().strip()], project, report_dir / "toolchain-install.log"))
    runs.append(run_logged(["lake", "env", "lean", "--version"], project, report_dir / "lean-version.log"))
    # Limit cache retrieval to the imported Mathlib modules and their closure.
    sources = list((project / "Elastica").glob("*.lean")) + list((root / "linear_input/lean_check").glob("*.lean")) + list((root / "linear_input/lean_check").glob("*.inc"))
    imports = sorted({m for p in sources for m in re.findall(r"(?m)^import\s+(Mathlib\.[A-Za-z0-9_.]+)", p.read_text("utf-8"))})
    if not imports:
        raise ValueError("No Mathlib imports found")
    runs.append(run_logged(["lake", "exe", "cache", "get", *imports], project, report_dir / "mathlib-cache.log", timeout=3600))
    if manifest_bytes != (project / "lake-manifest.json").read_bytes() or toolchain_bytes != (project / "lean-toolchain").read_bytes():
        raise ValueError("Pinned configuration changed during setup; do not continue")
    dependencies = []
    for package in json.loads(manifest_bytes)["packages"]:
        proc = subprocess.run(["git", "rev-parse", "HEAD"], cwd=project / ".lake/packages" / package["name"], capture_output=True, text=True)
        dependencies.append({"name": package["name"], "expected": package["rev"], "actual": proc.stdout.strip(), "match": proc.returncode == 0 and proc.stdout.strip() == package["rev"]})
    if not all(row["match"] for row in dependencies):
        raise ValueError("Pinned dependency revision mismatch")
    return {"status": "passed", "runs": runs, "dependencies": dependencies,
            "toolchain": toolchain_bytes.decode().strip(), "proofs": "not_run"}


def run_proofs(root, report_dir, expected_hashes, rebuild=False):
    root, report_dir = Path(root), Path(report_dir)

    def check_snapshot():
        changed = [p for p, digest in expected_hashes.items()
                   if not (root / p).is_file() or sha_bytes((root / p).read_bytes()) != digest]
        if changed:
            raise ValueError("Source snapshot changed: " + ", ".join(changed))

    check_snapshot()
    started_ns = time.time_ns()
    args = [sys.executable, "-X", "utf8", "tools/verify.py", "--proof-only"]
    if rebuild:
        args.append("--rebuild")
    run = run_logged(args, root, report_dir / "proof-run.log", timeout=10800)
    path = root / "verification/proof-only.json"
    if not path.is_file() or path.stat().st_mtime_ns < started_ns:
        raise ValueError("No fresh proof-only report")
    result = json.loads(path.read_text("utf-8"))
    if result.get("passed") is not True:
        raise ValueError("The current proof check did not pass")
    check_snapshot()
    return {"status": "passed", "run": run, "result": result}


def export_results(root, report_dir, state):
    root, report_dir = Path(root), Path(report_dir)
    save_json(report_dir / "notebook_run.json", state)
    since = state.get("proof_attempt_started_ns")
    if state["proofs"]["status"] in {"passed", "failed"} and since is not None:
        for rel in ["verification/proof-only.json", "verification/main-result.json", "verification/main-result.log",
                    "verification/proof-only-joint.log", "verification/proof-only-supplement.log",
                    "linear_input/lean_results.json", "linear_input/lean_check/build.log", "linear_input/lean_check/elastica-build.log"]:
            path = root / rel
            if path.is_file() and path.stat().st_mtime_ns >= since:
                dest = report_dir / "proofs" / rel
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path, dest)
    output = report_dir.with_suffix(".zip")
    with zipfile.ZipFile(output, "w", zipfile.ZIP_DEFLATED) as archive:
        for path in sorted(report_dir.rglob("*")):
            if path.is_file():
                archive.write(path, path.relative_to(report_dir))
    return output
