"""Offline fixture tests; no GitHub credentials or network access required."""
import importlib.util
from pathlib import Path
import unittest

TOOL = Path(__file__).resolve().parents[1] / 'tools' / 'commercial' / 'triage_public_pr.py'
spec = importlib.util.spec_from_file_location('triage_public_pr', TOOL)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class TriageTests(unittest.TestCase):
    def test_only_canonical_public_pr_urls(self):
        self.assertEqual(m.parse_pr_url('https://github.com/owner/repo/pull/166'), ('owner','repo',166))
        for value in ['https://evil.test/owner/repo/pull/1',
                      'https://github.com/o/r/pull/1?token=1',
                      'https://github.com/o/../pull/1',
                      'https://github.com/o/r/pull/0',
                      'https://github.com/o/r/pull/1/files']:
            with self.subTest(value=value), self.assertRaises(ValueError):
                m.parse_pr_url(value)

    def test_complete_intake_with_matching_ci_and_no_certificate_claim(self):
        sha = 'a'*40
        requests = []
        def get(path, token=None):
            requests.append(path)
            if path.endswith('/pulls/4'):
                return {'head':{'sha':sha},'base':{'sha':'b'*40},'changed_files':3,'draft':True,'state':'open'}
            if '/files?' in path:
                return [{'filename':'lean/A.lean'}, {'filename':'README.md'}, {'filename':'.github/workflows/ci.yml'}]
            if '/actions/runs?' in path:
                return {'workflow_runs':[{'head_sha':sha,'id':100,'status':'completed','conclusion':'success'}, {'head_sha':'c'*40,'id':101}]}
            raise AssertionError(path)
        report = m.triage('https://github.com/o/r/pull/4', get=get)
        self.assertTrue(report['intake']['eligible_for_manual_scope_review'])
        self.assertEqual(report['intake']['audit_file_count'],2)
        self.assertEqual(len(report['observed_actions_runs']),1)
        self.assertIn('successful run does not prove', ' '.join(report['evidence_limitations']).lower())
        self.assertEqual(len(requests),3)

    def test_missing_or_oversized_file_inventory_is_never_eligible(self):
        sha = 'f'*40
        def get_missing(path, token=None):
            if path.endswith('/pulls/7'): return {'head':{'sha':sha},'base':{},'changed_files':2}
            if '/files?' in path: return [{'filename':'lean/A.lean'}]
            return {'workflow_runs':[]}
        report = m.triage('https://github.com/o/r/pull/7', get=get_missing)
        self.assertFalse(report['intake']['eligible_for_manual_scope_review'])
        self.assertIn('file_inventory_incomplete', report['intake']['issues'])
        def get_many(path, token=None):
            if path.endswith('/pulls/8'): return {'head':{'sha':sha},'base':{},'changed_files':3001}
            if '/files?' in path: raise AssertionError('should skip files on oversized PR')
            return {'workflow_runs':[]}
        report = m.triage('https://github.com/o/r/pull/8', get=get_many)
        self.assertFalse(report['intake']['eligible_for_manual_scope_review'])
        self.assertIn('file_inventory_incomplete', report['intake']['issues'])

    def test_out_of_scope_lean_file_count(self):
        sha='0'*40
        def get(path, token=None):
            if path.endswith('/pulls/8'): return {'head':{'sha':sha}, 'changed_files':11}
            if '/files?' in path:return [{'filename':f'lean/{i}.lean'} for i in range(11)]
            return {'workflow_runs':[]}
        report=m.triage('https://github.com/o/r/pull/8',get=get)
        self.assertFalse(report['intake']['eligible_for_manual_scope_review'])
        self.assertIn('changed_lean_or_workflow_files_exceed_limit',report['intake']['issues'])


if __name__=='__main__':unittest.main()
