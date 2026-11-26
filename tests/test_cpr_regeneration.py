"""Independent finite CPR checks and a synthetic observation interval."""

import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from zipfile import ZipFile

from experiments.cpr_regeneration import check_observations, verify_model


class TestCPRRegeneration(unittest.TestCase):
    def test_finite_certificate(self):
        certificate = Path(verify_model.__file__).with_name("model_results.json")
        expected = json.loads(certificate.read_text(encoding="utf-8"))
        actual = json.loads(json.dumps(verify_model.main()))
        self.assertEqual(actual, expected)

    def test_sweeps_visit_each_target_at_most_once(self):
        board = verify_model.Board(3)
        for order in ((4, 4), (-1,), (9,)):
            for evaluate in (verify_model.conditional_law, verify_model.expected_births):
                with self.subTest(order=order, method=evaluate.__name__):
                    with self.assertRaises(ValueError):
                        evaluate(board, 1, order, board.units("fixed8"))

    def test_trace_support_and_tied_harvest(self):
        coords = [(x, y) for x in range(-1, 2) for y in range(-1, 2)]
        seed, middle, far = coords[3:6]
        header = "time," + ",".join(f"token_{x}_{y}" for x, y in coords)
        lines = [header]
        for time, state in ((0, {seed}), (0.1, {seed, middle, far}), (0.2, set())):
            lines.append(str(time) + "," + ",".join(str(int(c in state)) for c in coords))
        with TemporaryDirectory() as tmp:
            path = Path(tmp) / "synthetic.zip"
            for harvest, count in (("", 1), ("0.1,test,0,0\n", 0)):
                with ZipFile(path, "w") as archive:
                    folder = "synthetic/03_rawdata/01_fixture/round1/"
                    archive.writestr(folder + "TokenField.csv", "\n".join(lines) + "\n")
                    archive.writestr(folder + "Harvest.csv", "rt,player,x,y\n" + harvest)
                result = check_observations.inspect_archive(path, 3, set())
                self.assertEqual(result["counts"]["rounds_reaching_zero"], 1)
                self.assertEqual(result["order_support_in_ineligible_intervals"]["forward_only"], count)
                self.assertNotIn("witnesses", result)


if __name__ == "__main__":
    unittest.main()
