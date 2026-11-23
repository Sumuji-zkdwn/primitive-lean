"""Standard-library tests for the commit-pinned, intentionally lexical catalog."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

TOOL = Path(__file__).resolve().parents[1] / 'tools/export_agent_catalog.py'
spec = importlib.util.spec_from_file_location('export_agent_catalog', TOOL)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), *args], check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout


class CatalogTests(unittest.TestCase):
    def test_comments_strings_and_nested_comments_do_not_create_fake_declarations(self):
        code = '''/- theorem fake1 : True := by trivial\n /- lemma fake2 : True := by trivial -/\n-/\n-- def fake3 := 1\ndef realThing : String := "theorem fake4"\nnamespace X\nlemma actual : True := by trivial\n'''
        records = mod.extract_declarations(code, 'lean/A.lean', 'f' * 40)
        self.assertEqual([d['declared_name'] for d in records], ['realThing', 'actual'])
        self.assertEqual([d['line'] for d in records], [5, 7])
        self.assertTrue(all(d['verification_status'] == 'not_assessed' for d in records))

    def test_pinned_export_reproducible_despite_dirty_worktree(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            git(repo, 'init', '-q')
            git(repo, 'config', 'user.email', 'test@example.invalid')
            git(repo, 'config', 'user.name', 'Catalog Test')
            (repo/'lean').mkdir()
            (repo/'linear_input'/'lean_check').mkdir(parents=True)
            (repo/'lean'/'Proof.lean').write_text('theorem demo : True := by trivial\n', encoding='utf-8')
            (repo/'linear_input'/'lean_check'/'Other.inc').write_text('lemma exampleOne : True := by trivial\n', encoding='utf-8')
            (repo/'skip.txt').write_text('theorem skip : False := sorry\n', encoding='utf-8')
            git(repo, 'add', '.')
            git(repo, 'commit', '-qm', 'Initial')
            jsonl1, man1 = mod.export(repo)
            (repo/'lean'/'Proof.lean').write_text('theorem mutated : False := by sorry\n', encoding='utf-8')
            jsonl2, man2 = mod.export(repo)
            self.assertEqual((jsonl1, man1), (jsonl2, man2))
            rows = [json.loads(line) for line in jsonl1.splitlines()]
            manifest = json.loads(man1)
            self.assertEqual([r['declared_name'] for r in rows], ['demo', 'exampleOne'])
            self.assertEqual(manifest['lexical_declaration_count'], 2)
            self.assertEqual(manifest['verification_status'], 'not_assessed')
            self.assertTrue(len(manifest['jsonl_sha256']) == 64)
            out = repo/'output'
            self.assertEqual(mod.main(['--repo',str(repo),'--out-dir',str(out)]), 0)
            self.assertEqual(mod.main(['--repo',str(repo),'--out-dir',str(out),'--check']), 0)
            (out/'manifest.json').write_text('{}\n')
            self.assertEqual(mod.main(['--repo',str(repo),'--out-dir',str(out),'--check']), 1)


if __name__ == '__main__':
    unittest.main()
