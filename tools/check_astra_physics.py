"""Audit the selected Astra source closure and its exact assembly adapters.

This is a source/provenance check, not a substitute for Lean proof checking.
The joint and supplemental checkers perform the separate --trust=0 proof,
named-declaration and generated-environment axiom checks.
"""
import ast
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = 'docs/astra/manifest.json'
# Fixed assembly-only context, never arbitrary Lean text read from the ledger.
# The aliases are namespace qualified and may persist after the section ends;
# they resolve to the existing Set declarations, not new proof declarations.
ASSEMBLY_CONTEXTS = {
    'linear_input/lean_check/AstraHilbertFlow.inc': (
        'hilbertflow_set_exports',
        b'section\nnamespace KerrKoopman.HilbertFlow\n'
        b'export Set (piecewise union_comm)\nend KerrKoopman.HilbertFlow\n',
        b'\nend\n',
    ),
    'linear_input/lean_check/AstraFourierProjection.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraMaterialL2.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraRealGalerkin.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraFourierDerivative.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraRealFourierDerivative.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraFiniteRepresentatives.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraFourierSupBounds.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraFiniteRepresentativeCalculus.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraRelativeDynamics.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraContinuumCalculus.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraIntervalFourier.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraContinuumRelative.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraIntegralTail.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraContinuumGalerkin.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraIntervalFourierProjection.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraCircleProjection.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraGalerkinFlow.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraGalerkinClassical.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraContinuumFourier.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraGalerkinRelative.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraGalerkinRestoration.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraInitialRelativeEnergy.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraStoppingCertificate.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraInteriorGronwall.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraGalerkinGronwall.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraGalerkinRegularity.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraJointGalerkinLimit.inc': ('continuum_joint_filter_alias', b'section\nnamespace KerrKoopman.GalerkinClassical\nexport Filter (tendsto_atTop)\nend KerrKoopman.GalerkinClassical\n', b'\nend\n'),
    'linear_input/lean_check/AstraUniformGalerkinLimit.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraPolynomialInverse.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticFixedPoint.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticLpMap.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticLift.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraWeightedConvolution.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraAnalyticKernel.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticDuhamel.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticFourierDuhamel.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticAssembly.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraWeightedDecoder.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraWeightedReality.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraAnalyticReality.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraWeightedDerivative.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraWeightedRealDecode.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraAnalyticModeODE.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticFields.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticPhysicalMode.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticTransport.inc': ('continuum_transport_extend_alias', b'section\nnamespace KerrKoopman.AnalyticTransport\nexport KerrKoopman.AnalyticDuhamel (extend)\nend KerrKoopman.AnalyticTransport\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticPDE.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticClassical.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraRealFourierProjection.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraAnalyticTails.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraAnalyticTraceTails.inc': ('continuum_file_scope', b'section\n', b'\nend\nend\n'),
    'linear_input/lean_check/AstraAnalyticFieldTails.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticInitial.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticInitialTails.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticGalerkinCertificate.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraExplicitAnalyticInput.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraAnalyticExample.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraFiniteFlow.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
    'linear_input/lean_check/AstraContinuumLimit.inc': ('continuum_file_scope', b'section\n', b'\nend\n'),
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def strip_imports(raw):
    """The only permitted adaptation: remove whole import lines, byte exactly."""
    return b''.join(line for line in raw.splitlines(keepends=True)
                    if not line.startswith(b'import '))


def assembly_context_errors(contexts, registered_paths):
    errors = []
    sources = [row['source'] for row in contexts]
    required = set(ASSEMBLY_CONTEXTS).intersection(registered_paths)
    if len(sources) != len(set(sources)):
        errors.append('Duplicate assembly context')
    if set(sources) != required:
        errors.append('Assembly context coverage mismatch')
    for row in contexts:
        allowed = ASSEMBLY_CONTEXTS.get(row['source'])
        if (set(row) != {'source', 'kind', 'reason'} or not allowed or
                row['kind'] != allowed[0] or not isinstance(row['reason'], str) or not row['reason'].strip()):
            errors.append('Unapproved assembly context: ' + row['source'])
    return errors


def assembly_fragment(source, raw, contexts):
    """Apply fixed scope isolation and aliases outside the exact source bytes."""
    selected = [row for row in contexts if row['source'] == source]
    if not selected:
        return raw
    errors = assembly_context_errors(selected, [source])
    if errors:
        raise ValueError('; '.join(errors))
    _, prefix, suffix = ASSEMBLY_CONTEXTS[source]
    return prefix + raw + suffix


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
    if depth or string:
        raise ValueError('Unclosed Lean comment or string')
    return ''.join(result)


def declarations(text, namespace):
    return [(row['kind'], row['name']) for row in source_declarations(text, namespace)]


def source_declarations(text, namespace, filename='<source>'):
    """Index named source declarations; independently audit generated constants in Lean.

    Only the selected public-source grammar is supported. In particular private
    declarations cannot silently acquire public names in this ledger.
    """
    stack = []; result = []; roots = []; names = set()
    for number, line in enumerate(code_only(text).splitlines(), 1):
        command = re.sub(r'^(?:@\[[^\]]*\]\s*)*', '', line.lstrip())
        if re.match(r'(?:(?:noncomputable|protected)\s+)*private\b', command):
            raise ValueError(f'Private source declarations are unsupported: {filename}:{number}')
        if re.match(r'(?:noncomputable\s+)?(?:protected|opaque|class|inductive|mutual|public|local\s+(?:def|theorem|lemma|instance))\b', command):
            raise ValueError(f'Unsupported source declaration grammar: {filename}:{number}')
        if line != line.lstrip() and re.match(
                r'(?:noncomputable\s+)?(?:namespace|section|end|theorem|lemma|def|abbrev|structure|instance)\b', command):
            raise ValueError(f'Unsupported indented source command: {filename}:{number}')
        opening = re.fullmatch(r'(?:noncomputable\s+)?(namespace|section)(?:\s+(\S+))?\s*', line)
        if opening:
            kind, name = opening.groups()
            if kind == 'namespace':
                if not name: raise ValueError(f'Unnamed namespace: {filename}:{number}')
                prefix = '.'.join(n for k, n in stack if k == 'namespace')
                full = prefix + '.' + name if prefix else name
                if full != namespace and not full.startswith(namespace + '.'):
                    raise ValueError(f'Source namespace mismatch: {filename}:{number}: {full}')
                if not prefix: roots.append(full)
            stack.append((kind, name)); continue
        closing = re.fullmatch(r'end(?:\s+(\S+))?\s*', line)
        if closing:
            if not stack: raise ValueError(f'Unmatched scope end: {filename}:{number}')
            _, name = stack.pop()
            if closing.group(1) is not None and closing.group(1) != name:
                raise ValueError(f'Mismatched scope end: {filename}:{number}')
            continue
        found = re.match(r'^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?'
                         r'(theorem|lemma|def|abbrev|structure|instance)\s+([^\s({:\[]+)', line)
        if found:
            prefix = '.'.join(n for k, n in stack if k == 'namespace')
            name = prefix + '.' + found.group(2) if prefix else found.group(2)
            if not name.startswith(namespace + '.') or found.group(2).startswith('_root_.'):
                raise ValueError(f'Declaration outside registered namespace: {filename}:{number}')
            if name in names: raise ValueError('Duplicate source declaration: ' + name)
            names.add(name)
            result.append(dict(name=name, kind=found.group(1), file=filename, line=number))
    # Lean permits file-wide sections to end at EOF. Namespaces in these
    # import-only source adapters must nevertheless close explicitly.
    if any(kind == 'namespace' for kind, _ in stack):
        raise ValueError('Unclosed source namespace: ' + filename)
    if not roots or any(root != namespace for root in roots):
        raise ValueError('Source namespace mismatch: ' + filename)
    return result


def proof_contract(root=ROOT):
    root = Path(root)
    manifest = json.loads((root / MANIFEST).read_text('utf-8'))
    pairs = []
    for row in [manifest['bridge_contract'], *manifest.get('additional_bridge_contracts', [])]:
        contract = json.loads(local_file(root, contract_path(row)).read_text('utf-8'))
        pairs += [(source, target) for source, targets in contract['required_proof_edges'].items() for target in targets]
    if any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)+', name)
           for pair in pairs for name in pair):
        raise ValueError('Invalid Lean declaration name in proof contract')
    if len(pairs) != len(set(pairs)):
        raise ValueError('Duplicate proof dependency in contract')
    return pairs


def contract_path(row):
    paths = [row[key] for key in ('preserved_copy', 'path') if key in row]
    if len(paths) != 1:
        raise ValueError('Proof contract must have exactly one preserved or repository-native path')
    return paths[0]


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


def environment_roots(root=ROOT):
    manifest = json.loads((Path(root) / MANIFEST).read_text('utf-8'))
    roots = sorted({row['namespace'] for row in
                    manifest['modules'] + manifest.get('native_bridges', []) if row['namespace']})
    if any(not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', n) for n in roots):
        raise ValueError('Invalid Astra environment namespace')
    return roots


def environment_audit_commands(root=ROOT):
    roots = ', '.join('`' + name for name in environment_roots(root))
    return '''
open Lean Elab Command in
elab "audit_astra_environment" : command => do
  let env ← getEnv
  let roots : Array Name := #[''' + roots + ''']
  let entries ← env.constants.foldM (init := #[]) fun entries name info => do
    if roots.any (·.isPrefixOf (privateToUserName name)) then
      return entries.push (name, info)
    else
      return entries
  if entries.isEmpty then throwError "No Astra environment declarations"
  for (name, info) in entries do
    let axioms ← Lean.collectAxioms name
    for a in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Forbidden Astra environment axiom: {name}: {a}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    logInfo m!"ASTRA_ENV|{name}|{kind}|{String.intercalate "," (axioms.toList.map toString)}"
  logInfo m!"ASTRA_ENV_TOTAL|{entries.size}"

audit_astra_environment
'''


def audit_environment(root, log):
    roots = environment_roots(root)
    records = re.findall(r'ASTRA_ENV\|([^|\r\n]+)\|([^|\r\n]+)\|([^\r\n]*)', log)
    totals = re.findall(r'ASTRA_ENV_TOTAL\|(\d+)', log)
    names = [name for name, _, _ in records]
    errors = []
    if len(totals) != 1 or int(totals[0]) != len(records) or not records:
        errors.append('Missing or inconsistent Astra environment total')
    if len(names) != len(set(names)): errors.append('Duplicate Astra environment declaration')
    observed = {}
    kinds = {'theorem', 'definition', 'axiom', 'opaque', 'inductive', 'constructor', 'recursor', 'quotient'}
    for name, kind, raw_axioms in records:
        normalized = re.sub(r'^_private\..*?\.\d+\.', '', name)
        if not any(normalized.startswith(ns + '.') for ns in roots) or kind not in kinds:
            errors.append('Unexpected Astra environment declaration: ' + name)
        axioms = [a.strip() for a in raw_axioms.split(',') if a.strip()]
        if set(axioms) - {'propext', 'Classical.choice', 'Quot.sound'}:
            errors.append('Forbidden Astra environment axiom: ' + name)
        observed[name] = dict(kind=kind, axioms=axioms)
    manifest = json.loads((Path(root) / MANIFEST).read_text('utf-8'))
    expected = []
    for row in manifest['modules'] + manifest.get('native_bridges', []):
        if row.get('destination'):
            expected += declarations(local_file(Path(root), row['destination']).read_text('utf-8'), row['namespace'])
    for kind, name in expected:
        actual = observed.get(name, {})
        wanted = ({'theorem'} if kind in ('theorem', 'lemma') else {'inductive'} if kind == 'structure'
                  else {'theorem', 'definition'} if kind == 'instance' else {'definition'})
        if actual.get('kind') not in wanted:
            errors.append('Missing or wrong-kind Astra source declaration: ' + name)
    return dict(passed=not errors, errors=errors, namespace_roots=roots,
                source_named_declarations=len(expected), environment_declarations=len(records),
                declarations=observed,
                scope='All constants under registered Astra source namespaces, including instances, structures, constructors, recursors, private generated names and auxiliaries; source counts remain separate')


def audit(root=ROOT):
    root = Path(root).resolve()
    errors = []; new_declarations = []; module_results = []
    result = dict(passed=False, errors=errors, modules=module_results,
                  scope='Exact source adaptation, dependency closure and registration; proof validity is checked separately')
    try:
        manifest = json.loads((root / MANIFEST).read_text('utf-8'))
        if manifest['schema_version'] not in (1, 2):
            raise ValueError('Unsupported Astra manifest schema')
        rows = manifest['modules']; by_module = {row['module']: row for row in rows}
        native_rows = manifest.get('native_bridges', [])
        if native_rows and manifest['schema_version'] != 2:
            errors.append('Repository-native bridge requires schema version 2')
        if len(by_module) != len(rows): errors.append('Duplicate source module')
        registry = assignment(root / 'tools/verify_main_result.py', 'SUPPLEMENTS')
        extra_imports = set(assignment(root / 'tools/verify_main_result.py', 'EXTRA_IMPORTS'))
        position = {path: i for i, (path, _) in enumerate(registry)}
        registered = dict(registry)
        adapter_paths = [row['destination'] for row in rows if row['role'] == 'import_only_adapter']
        native_paths = [row['destination'] for row in native_rows]
        contexts = manifest.get('assembly_contexts', [])
        errors.extend(assembly_context_errors(contexts, adapter_paths + native_paths))
        result['assembly_contexts'] = contexts
        actual_astra = [path for path, _ in registry if Path(path).stem.startswith('Astra')]
        if adapter_paths + native_paths != actual_astra:
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
            decls = declarations(text, row['namespace']) if row['namespace'] else []
            theorem_count = sum(kind in ('theorem', 'lemma') for kind, _ in decls)
            if theorem_count != row['theorem_count']:
                errors.append('Source theorem count mismatch: ' + module)
            if ('declaration_count_including_structures' in row and
                    len(decls) != row['declaration_count_including_structures']):
                errors.append('Source named declaration count mismatch: ' + module)
            if 'declaration_count' in row and len(decls) != row['declaration_count']:
                errors.append('Source declaration count mismatch: ' + module)
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

        native_theorems = 0
        native_modules = {row['module']: row for row in native_rows}
        if len(native_modules) != len(native_rows) or set(native_modules) & set(by_module):
            errors.append('Duplicate repository-native module')
        for row in native_rows:
            module = row['module']; destination = row['destination']
            raw = local_file(root, destination).read_bytes(); text = raw.decode('utf-8'); code = code_only(text)
            if row.get('role') != 'repository_native_proof' or row.get('origin') != 'authored_in_primitive_lean':
                errors.append('Native bridge lacks explicit repository authorship: ' + module)
            if not row.get('authored_on_parent_commit') or not row.get('authorship_description'):
                errors.append('Native bridge lacks creation provenance: ' + module)
            if 'preserved_copy' in row or 'transformation' in row:
                errors.append('Native bridge cannot claim import-only adaptation: ' + module)
            if sha(raw) != row['sha256'] or row['sha256'] != row.get('original_sha256'):
                errors.append('Native bridge creation hash mismatch: ' + destination)
            if re.search(r'(?m)^\s*import\b', code) or re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', code):
                errors.append('Native bridge contains forbidden assembly/proof token: ' + module)
            if registered.get(destination) != row['namespace']:
                errors.append('Native bridge registration mismatch: ' + destination)
            decls = declarations(text, row['namespace'])
            theorem_count = sum(kind in ('theorem', 'lemma') for kind, _ in decls)
            if theorem_count != row['theorem_count'] or len(decls) != row['declaration_count']:
                errors.append('Native bridge declaration count mismatch: ' + module)
            if all_declarations.intersection(name for _, name in decls):
                errors.append('Duplicate native bridge declaration: ' + module)
            all_declarations.update(name for _, name in decls)
            new_declarations.extend(name for _, name in decls)
            native_theorems += theorem_count
            for dependency in row['dependencies']:
                other = by_module.get(dependency, native_modules.get(dependency))
                if other is None:
                    errors.append('Missing native bridge dependency: ' + dependency)
                elif other.get('destination') in position and position[other['destination']] >= position.get(destination, -1):
                    errors.append('Native bridge dependency appears after dependent: ' + module)
            missing = set(row['required_mathlib_imports']) - extra_imports
            if missing: errors.append('Missing native bridge Mathlib import: ' + ', '.join(sorted(missing)))
            contracts = manifest.get('additional_bridge_contracts', [])
            if row['proof_contract'] not in [contract_path(c) for c in contracts]:
                errors.append('Native bridge lacks registered proof contract: ' + module)
            module_results.append(dict(module=module, role=row['role'], theorem_count=theorem_count))

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
        for contract_row in [manifest['bridge_contract'], *manifest.get('additional_bridge_contracts', [])]:
            contract_raw = local_file(root, contract_path(contract_row)).read_bytes()
            if sha(contract_raw) != contract_row['sha256']: errors.append('Bridge contract hash mismatch')
            edges = json.loads(contract_raw)['required_proof_edges']
            if len(edges) != contract_row['theorem_nodes'] or sum(map(len, edges.values())) != contract_row['direct_references']:
                errors.append('Bridge contract count mismatch')
            for source, targets in edges.items():
                if source not in all_declarations or not set(targets) <= all_declarations:
                    errors.append('Bridge contract references missing declaration: ' + source)
        pairs = proof_contract(root)
        counts = dict(source_modules=len(rows), new_proof_modules=len(adapter_paths) + len(native_paths),
                      new_theorems=new_theorems + native_theorems,
                      new_physics_theorems=new_theorems + native_theorems - 1,
                      new_original_koopman_theorems=1, reused_original_theorems=reused_theorems)
        if manifest['schema_version'] == 2:
            counts.update(import_only_modules=len(adapter_paths), import_only_theorems=new_theorems,
                          repository_native_modules=len(native_paths), repository_native_theorems=native_theorems)
        if counts != manifest['counts']: errors.append('Integration theorem/module counts mismatch')
        result.update(counts=counts, new_declarations=new_declarations,
                      bridge_theorem_nodes=len({source for source, _ in pairs}), bridge_direct_references=len(pairs),
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
