"""Reproducible finite checks, separate from the Lean structural theorems."""
import importlib.util
from pathlib import Path

import pytest

MODULE_PATH = Path(__file__).resolve().parents[1] / "tools" / "elliptic_modular_probe.py"
spec = importlib.util.spec_from_file_location("elliptic_modular_probe", MODULE_PATH)
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)


def test_form_initial_coefficients():
    assert probe.eta_coefficients(12)[1:] == [1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, -2]


def test_observations_all_good_primes_through_97():
    rows = probe.observation_rows()
    assert len(rows) == 24
    assert 11 not in {row["p"] for row in rows}
    assert all(row["curve_a_p"] == row["form_a_p"] for row in rows)
    assert {row["p"]: (row["points"], row["curve_a_p"]) for row in rows if row["p"] in (2, 3, 7, 13, 47)} == {
        2: (5, -2), 3: (5, -1), 7: (10, -2), 13: (10, 4), 47: (40, 8)}


def test_hecke_recursions_degree_200():
    assert probe.hecke_failures(200) == []


def test_negative_control_changing_curve_changes_observations():
    a = probe.eta_coefficients(97)
    assert any(p + 1 - probe.points_on_curve(p, constant=21) != a[p]
               for p in range(2, 98) if probe.is_prime(p) and p != 11)


def test_rejects_invalid_inputs():
    with pytest.raises(ValueError):
        probe.eta_coefficients(0)
    with pytest.raises(ValueError):
        probe.points_on_curve(4)
    with pytest.raises(ValueError):
        probe.observation_rows(97, 30)
