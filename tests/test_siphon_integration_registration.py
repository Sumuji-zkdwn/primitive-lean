"""Fast orchestration regressions for the unified siphon verification stages.

Mock external commands: the real Lean proof check remains the integration CI.
"""
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from tools.pr_integration import run_integration


class SiphonIntegrationRegistrationTests(unittest.TestCase):
    def run_fake_integration(self, sorry_module=None):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            out = root / 'verification'
            out.mkdir()
            calls = []

            def fake_command(args, name, cwd=None):
                calls.append((name, args))
                log = out / (name + '.log')
                log.write_text(
                    'axioms: [sorryAx]\n' if name == 'integration-' + str(sorry_module)
                    else 'axioms: []\n', encoding='utf-8')
                if name == 'integration-proof-only':
                    (out / 'proof-only.json').write_text(json.dumps({
                        'passed': True, 'theorem_count': 1,
                        'declaration_count': 1,
                    }), encoding='utf-8')
                return {'exit_code': 0, 'log': 'verification/' + name + '.log',
                        'warnings': []}

            with patch('tools.pr_integration.subprocess.check_output',
                       side_effect=['deadbeef\n', '']):
                report = run_integration(root, fake_command)
            return report, dict(calls)

    def test_both_modules_are_compiled_at_trust_zero(self):
        report, calls = self.run_fake_integration()
        self.assertTrue(report['passed'], report['errors'])
        for name, path in (
            ('siphon-interaction', 'Research/SiphonInteraction.lean'),
            ('siphon-polynomial-e', 'Research/SiphonPolynomialE.lean'),
        ):
            self.assertEqual(calls['integration-' + name],
                             ['lake', 'env', 'lean', '--trust=0', path])
        self.assertEqual(calls['integration-repository-tests'][-4:],
                         ['discover', '-s', 'tests', '-v'])

    def test_sorry_axiom_is_not_accepted_as_success(self):
        report, calls = self.run_fake_integration(sorry_module='siphon-interaction')
        self.assertFalse(report['passed'])
        self.assertIn('integration-siphon-interaction', calls)
        self.assertTrue(any('sorryAx' in error for error in report['errors']))


if __name__ == '__main__':
    unittest.main()
