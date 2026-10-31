#!/usr/bin/env bash
set -euo pipefail
REPO_ROOT="$(pwd)"
WORK="${RUNNER_TEMP:-/tmp}/arc3-runtime-build"
mkdir -p "$WORK"
cd "$WORK"
LEAN_TAG=v4.30.0-rc2
LEAN_ARCHIVE=lean-4.30.0-rc2-linux.tar.zst
LEAN_SHA=5b51625f154f0a13b37bd892f1d95f79e9fd5b9f0d095b4126215ee2bc8dbe86
REPL_SHA=f0a88bfca1fa6ac75e2a33d1678a3b67c90fb492
curl --fail --location --retry 3 --output "$LEAN_ARCHIVE" "https://github.com/leanprover/lean4/releases/download/$LEAN_TAG/$LEAN_ARCHIVE"
echo "$LEAN_SHA  $LEAN_ARCHIVE" | sha256sum -c -
tar --zstd -xf "$LEAN_ARCHIVE"
export LEAN_HOME="$WORK/lean-4.30.0-rc2-linux"
export PATH="$LEAN_HOME/bin:$PATH"
lean --version
mkdir repl-src
cd repl-src
git init
git remote add origin https://github.com/leanprover-community/repl.git
git fetch --depth 1 origin "$REPL_SHA"
git checkout --detach FETCH_HEAD
test "$(git rev-parse HEAD)" = "$REPL_SHA"
test "$(cat lean-toolchain)" = "leanprover/lean4:$LEAN_TAG"
lake build
cd "$WORK"
export OUTPUT_ROOT="$REPO_ROOT/runtime-output"
python - <<'PY'
import hashlib,json,os,shutil,subprocess
from pathlib import Path
home=Path(os.environ['LEAN_HOME']);work=home.parent
out=Path(os.environ['OUTPUT_ROOT']);out.mkdir(exist_ok=True)
root=out/'arc3-lean-runtime';root.mkdir()
(root/'lean/bin').mkdir(parents=True)
for name in ('lean','lake'):
    shutil.copy2(home/'bin'/name,root/'lean/bin'/name)
# Runtime interpretation/imports require olean/ir/shared libraries, not the C
# compiler or static link archives. No user proof sources are changed.
shutil.copytree(home/'lib',root/'lean/lib',symlinks=False,
    ignore=lambda d,n:[x for x in n if x.endswith('.a') or x in ('clang','cmake')])
(root/'bin').mkdir();shutil.copy2(work/'repl-src/.lake/build/bin/repl',root/'bin/repl')
(root/'licenses').mkdir()
for f in home.glob('LICENSE*'):shutil.copy2(f,root/'licenses'/('lean-'+f.name))
shutil.copy2(work/'repl-src/LICENSE',root/'licenses/REPL-LICENSE')
shutil.copytree(work/'repl-src',root/'repl-source',ignore=shutil.ignore_patterns('.git','.lake'))
cfg={'schema':'arc3-lean-runtime-v1','lean_version':subprocess.check_output([str(home/'bin/lean'),'--version'],text=True).strip(),
 'backend':'leanprover-community/repl','command':['${RUNTIME}/bin/repl'],'cwd':'${RUNTIME}',
 'env':{'LEAN_SYSROOT':'${RUNTIME}/lean','LEAN_PATH':'${RUNTIME}/lean/lib/lean',
 'PATH':'${RUNTIME}/lean/bin:${PATH}',
 'LD_LIBRARY_PATH':'${RUNTIME}/lean/lib:${RUNTIME}/lean/lib/lean:${LD_LIBRARY_PATH}'},
 'imports':[],'rpc_timeout':30,
 'notes':'Actual Linux runtime for v3 recorded-graph proofs. No gameplay budgets. Original 733 research theorems are not bundled or reverified.'}
(root/'arc3-runtime.json').write_text(json.dumps(cfg,indent=2)+'\n')
provenance={'lean_version':'v4.30.0-rc2','lean_archive_sha256':'5b51625f154f0a13b37bd892f1d95f79e9fd5b9f0d095b4126215ee2bc8dbe86',
 'lean_source':'https://github.com/leanprover/lean4/releases/tag/v4.30.0-rc2',
 'repl_commit':'f0a88bfca1fa6ac75e2a33d1678a3b67c90fb492','repl_source':'https://github.com/leanprover-community/repl',
 'research_toolchain_ref':'47083b67942c28878cda7a04b304203158c3d2e4','architecture':'linux-x86_64',
 'build_commit':os.environ.get('GITHUB_SHA'),'run_id':os.environ.get('GITHUB_RUN_ID'),
 'scope':'runtime plus Lean standard library; no claim of rebuilding primitive-lean or Kaggle execution'}
(root/'PROVENANCE.json').write_text(json.dumps(provenance,indent=2)+'\n')
print('Runtime copied',root)
PY
ROOT="$OUTPUT_ROOT/arc3-lean-runtime"
mkdir "$ROOT/wheelhouse"
# Optuna's binary dependencies vary by Python ABI; include CPU Linux wheels for
# Python 3.10 through 3.13. NumPy and torch are supplied by the Kaggle CPU image.
for py in 310 311 312 313; do
  python -m pip download --only-binary=:all: --platform manylinux2014_x86_64 \
    --python-version "$py" --implementation cp --abi "cp$py" \
    --dest "$ROOT/wheelhouse" 'optuna==4.5.0'
done
python "$REPO_ROOT/tools/arc3_runtime/verify_runtime.py" "$ROOT" "$ROOT/verification"
# Check a relocated copy and remove executable permissions to exercise the
# notebook's restore-on-extract requirement independently of Kaggle metadata.
RELOCATED="$WORK/relocated-runtime"
cp -a "$ROOT" "$RELOCATED"
python "$REPO_ROOT/tools/arc3_runtime/verify_runtime.py" "$RELOCATED" "$ROOT/verification/relocated"
python - <<'PY'
from pathlib import Path
import hashlib,json,os
root=Path(os.environ['OUTPUT_ROOT'])/'arc3-lean-runtime'
rows={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.rglob('*')) if p.is_file()}
(root/'FILES_SHA256.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Files:',len(rows));print('Bytes:',sum(p.stat().st_size for p in root.rglob('*') if p.is_file()))
PY
# Preserve executable modes inside this tar. The notebook expands it into /tmp,
# never tries to chmod the read-only Kaggle input mount.
tar -C "$OUTPUT_ROOT" -czf "$OUTPUT_ROOT/arc3-lean-runtime-linux-x86_64.tar.gz" arc3-lean-runtime
cd "$OUTPUT_ROOT"
sha256sum arc3-lean-runtime-linux-x86_64.tar.gz > arc3-lean-runtime-linux-x86_64.tar.gz.sha256
cp arc3-lean-runtime/verification/runtime-validation.json .
cp arc3-lean-runtime/PROVENANCE.json .
ls -lh *.tar.gz
