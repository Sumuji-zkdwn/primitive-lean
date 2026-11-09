"""Audit the selected Astra source closure and its exact assembly adapters.

This is a source/provenance check, not a substitute for Lean proof checking.
The unchanged joint checker and the registered supplemental checker perform
the separate --trust=0 proof and all-declaration axiom checks.
"""
import ast
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = 'docs/astra/manifest.json'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def strip_imports(raw):
    """The only permitted adaptation: remove whole import lines, byte exactly."""
    return b''.join(line for line in raw.splitlines(keepends=True)
                    if not line.startswith(b'import '))


def assignment(path, name):
    tree = ast.parse(path.read_text('utf-8'))
    values = [node.value for node in ast.walk(tree) if isinstance(node, ast.Assign)
              and any(isinstance(t, ast.Name) and t.id == name for t in node.targets)]
    if len(values) != 1:
        raise ValueError(f'{path}: expected one {name} assignment')
    return ast.literal_eval(values[0])


def local_file(root, relative):
    path = (root / relative).resolve()
    if not path.is_relative_to(root.resolve()):
        raise ValueError('Source path escapes repository: ' + relative)
    return path


def code_only(text):
    """Discard nested Lean comments and strings before counting declarations."""
    result = []; i = 0; depth = 0; string = False
    while i < len(text):
        c = text[i]; pair = text[i:i + 2]
        if depth:
            if pair == '/-': depth += 1; result.extend('  '); i += 2; continue
            if pair == '-/': depth -= 1; result.extend('  '); i += 2; continue
            result.append('\n' if c == '\n' else ' '); i += 1; continue
        if string:
            if c == '\\': result.extend('  '); i += 2; continue
            if c == '"': string = False
            result.append('\n' if c == '\n' else ' '); i += 1; continue
        if pair == '/-': depth = 1; result.extend('  '); i += 2; continue
        if pair == '--':
            end = text.find('\n', i); end = len(text) if end < 0 else end
            result.extend(' ' * (end - i)); i = end; continue
        if c == '"': string = True; result.append(' '); i += 1; continue
        result.append(c); i += 1
    return ''.join(result)


def declarations(text, namespace):
    return [(kind, namespace + '.' + name) for kind, name in re.findall(
        r'(?m)^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([^\s({:]+)',
        code_only(text))]


def proof_contract(root=ROOT):
    root = Path(root)
    manifest = json.loads((root / MANIFEST).read_text('utf-8'))
    contract = json.loads(local_file(root, manifest['bridge_contract']['preserved_copy']).read_text('utf-8'))
    pairs = [(source, target) for source, targets in contract['required_proof_edges'].items() for target in targets]
    if any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)+', name)
           for pair in pairs for name in pair):
        raise ValueError('Invalid Lean declaration name in proof contract')
    if len(pairs) != len(set(pairs)):
        raise ValueError('Duplicate proof dependency in contract')
    return pairs


def proof_edge_commands(root=ROOT):
    """Commands appended to the same fresh, trust=0 MainResult compilation."""
    pairs = ',\n    '.join(f'(`{source}, `{target})' for source, target in proof_contract(root))
    return '''
open Lean Elab Command in
elab "audit_astra_proof_edges" : command => do
  let env \u2190 getEnv
  let required : Array (Name \u00d7 Name) := #[
    ''' + pairs + ''']
  for (source, target) in required do
    let some info := env.find? source
      | throwError "Astra source theorem missing: {source}"
    let some value := info.value? (allowOpaque := true)
      | throwError "Astra theorem has no proof value: {source}"
    unless value.getUsedConstants.contains target do
      throwError "Astra direct proof dependency missing: {source} -> {target}"
    logInfo m!"ASTRA_PROOF_EDGE|{source}|{target}|present"

audit_astra_proof_edges
'''


def audit_proof_edges(root, log):
    expected = proof_contract(root)
    observed = re.findall(r'ASTRA_PROOF_EDGE\|([^|\r\n]+)\|([^|\r\n]+)\|present', log)
    missing = sorted(set(expected) - set(observed))
    extra = sorted(set(observed) - set(expected))
    duplicates = len(observed) != len(set(observed))
    return dict(passed=not missing and not extra and not duplicates,
                theorem_nodes=len({source for source, _ in expected}),
                direct_references=len(expected), observed_references=len(observed),
                missing=missing, unexpected=extra, duplicate_results=duplicates,
                scope='Direct constants in elaborated proof values; this witnesses reuse, not logical necessity or an unconditional PDE derivation')


def audit(root=ROOT):
    root = Path(root).resolve()
    errors = []; new_declarations = []; module_results = []
    result = dict(passed=False, errors=errors, modules=module_results,
                  scope='Exact source adaptation, dependency closure and registration; proof validity is checked separately')
    try:
        manifest = json.loads((root / MANIFEST).read_text('utf-8'))
        if manifest['schema_version'] != 1:
            raise ValueError('Unsupported Astra manifest schema')
        rows = manifest['modules']; by_module = {row['module']: row for row in rows}
        if len(by_module) != len(rows): errors.append('Duplicate source module')
        registry = assignment(root / 'tools/verify_main_result.py', 'SUPPLEMENTS')
        extra_imports = set(assignment(root / 'tools/verify_main_result.py', 'EXTRA_IMPORTS'))
        position = {path: i for i, (path, _) in enumerate(registry)}
        registered = dict(registry)
        adapter_paths = [row['destination'] for row in rows if row['role'] == 'import_only_adapter']
        actual_astra = [path for path, _ in registry if Path(path).stem.startswith('Astra')]
        if adapter_paths != actual_astra:
            errors.append('Astra registry differs from declared adapter order')
        all_declarations = set(); new_theorems = reused_theorems = 0
        for row in rows:
            module = row['module']; raw = local_file(root, row['preserved_copy']).read_bytes()
            if sha(raw) != row['source_sha256']:
                errors.append('Preserved source hash mismatch: ' + module)
            text = raw.decode('utf-8'); code = code_only(text)
            imports = re.findall(r'(?m)^import ([^\r\n]+)', code)
            if imports != row['imports']:
                errors.append('Source import list mismatch: ' + module)
            namespaces = re.findall(r'(?m)^namespace\s+(\S+)', code)
            expected_ns = [row['namespace']] if row['namespace'] else []
            if namespaces != expected_ns:
                errors.append('Source namespace mismatch: ' + module)
            decls = declarations(text, row['namespace']) if row['namespace'] else []
            theorem_count = sum(kind in ('theorem', 'lemma') for kind, _ in decls)
            if theorem_count != row['theorem_count']:
                errors.append('Source theorem count mismatch: ' + module)
            if all_declarations.intersection(name for _, name in decls):
                errors.append('Duplicate source declaration: ' + module)
            all_declarations.update(name for _, name in decls)
            role = row['role']
            if role in ('import_only_adapter', 'reuse_existing'):
                destination = row['destination']; target = local_file(root, destination).read_bytes()
                if sha(target) != row['sha256']:
                    errors.append('Destination hash mismatch: ' + destination)
                if role == 'import_only_adapter':
                    if row['transformation'] != 'remove_import_lines_exact_bytes' or target != strip_imports(raw):
                        errors.append('Adapter changes bytes beyond import removal: ' + destination)
                    if registered.get(destination) != row['namespace']:
                        errors.append('Adapter namespace registration mismatch: ' + destination)
                    new_theorems += theorem_count
                    new_declarations.extend(name for _, name in decls)
                    missing = set(i for i in imports if i.startswith('Mathlib.')) - extra_imports
                    if missing: errors.append('Missing additive Mathlib import: ' + ', '.join(sorted(missing)))
                else:
                    if (row['transformation'] != 'compare_after_crlf_to_lf_only' or
                            target.replace(b'\r\n', b'\n') != raw.replace(b'\r\n', b'\n')):
                        errors.append('Reused primitive source differs beyond line endings: ' + destination)
                    reused_theorems += theorem_count
            elif role != 'import_aggregator' or code.strip() != '\n'.join('import ' + i for i in imports):
                errors.append('Unexpected aggregator body or role: ' + module)
            module_results.append(dict(module=module, role=role, theorem_count=theorem_count))

        visiting = set(); visited = set()
        def resolve(module):
            if module in visiting: raise ValueError('Cyclic source import: ' + module)
            if module in visited: return
            if module not in by_module: raise ValueError('Missing source dependency: ' + module)
            visiting.add(module)
            row = by_module[module]
            for dependency in row['imports']:
                if dependency.startswith('KerrKoopman.'):
                    resolve(dependency)
            visiting.remove(module); visited.add(module)

        def adapter_dependencies(module):
            row = by_module[module]; found = set()
            for dependency in row['imports']:
                if dependency.startswith('KerrKoopman.'):
                    other = by_module[dependency]
                    if other['role'] == 'import_only_adapter': found.add(other['destination'])
                    found.update(adapter_dependencies(dependency))
            return found

        for row in rows:
            if row['role'] == 'import_only_adapter': resolve(row['module'])
        if visited != set(by_module): errors.append('Manifest contains sources outside the selected dependency closure')
        for row in rows:
            if row['role'] == 'import_only_adapter':
                for dependency in adapter_dependencies(row['module']):
                    if position.get(dependency, -1) >= position.get(row['destination'], -1):
                        errors.append('Adapter dependency appears after dependent: ' + row['destination'])
        contract_row = manifest['bridge_contract']
        contract_raw = local_file(root, contract_row['preserved_copy']).read_bytes()
        if sha(contract_raw) != contract_row['sha256']: errors.append('Bridge contract hash mismatch')
        edges = json.loads(contract_raw)['required_proof_edges']
        if len(edges) != contract_row['theorem_nodes'] or sum(map(len, edges.values())) != contract_row['direct_references']:
            errors.append('Bridge contract count mismatch')
        for source, targets in edges.items():
            if source not in all_declarations or not set(targets) <= all_declarations:
                errors.append('Bridge contract references missing declaration: ' + source)
        counts = dict(source_modules=len(rows), new_proof_modules=len(adapter_paths),
                      new_theorems=new_theorems, new_physics_theorems=new_theorems - 1,
                      new_original_koopman_theorems=1, reused_original_theorems=reused_theorems)
        if counts != manifest['counts']: errors.append('Integration theorem/module counts mismatch')
        result.update(counts=counts, new_declarations=new_declarations,
                      bridge_theorem_nodes=len(edges), bridge_direct_references=sum(map(len, edges.values())),
                      proof_edges_checked=False, source_commit=manifest['source_commit'])
    except (OSError, ValueError, KeyError, TypeError, RecursionError) as error:
        errors.append(str(error))
    result['passed'] = not errors
    return result


def main():
    result = audit()
    (ROOT / 'verification').mkdir(exist_ok=True)
    (ROOT / 'verification/astra-source-audit.json').write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + '\n', 'utf-8')
    print(json.dumps({k: v for k, v in result.items() if k not in ('modules', 'new_declarations')}, indent=2))
    return 0 if result['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
