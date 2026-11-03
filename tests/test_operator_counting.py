"""Check compatible-map count products against independent full enumeration."""
from itertools import combinations
import importlib.util
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
SPEC=importlib.util.spec_from_file_location(
    'count_operator_compatibility',
    ROOT/'tools/count_operator_compatibility.py')
mod=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mod)


def compositions(n):
    for mask in range(1 << (n-1)):
        sizes=[]
        last=0
        for j in range(n-1):
            if mask & (1 << j):
                sizes.append(j+1-last)
                last=j+1
        sizes.append(n-last)
        yield tuple(sizes)


def test_all_compositions_up_to_five_states():
    for n in range(1,6):
        for sizes in compositions(n):
            record=mod.report(sizes)
            assert all(record['checks'].values()), record


def test_two_plus_one_count():
    record=mod.report((2,1))
    assert record['compatible_raw_maps']==15
    assert record['all_raw_maps']==27
    assert record['effective_quotient_maps']==4


def test_symmetric_blocks_counts():
    assert mod.report((2,2))['compatible_raw_maps']==64
    assert mod.report((3,1))['compatible_raw_maps']==112
    assert mod.report((2,2,1))['compatible_raw_maps']==405


def test_distinguish_syntactic_vs_semantic():
    # An identity-only language on a partition (2,1) produces
    # exactly one word action, whereas the compatible raw-map count is 15.
    assert mod.formula((2,1))>1
    assert mod.effective_count((2,1))==4


def test_invalid_partition_sizes():
    for vals in ((), (0,1), (1,-1)):
        try:
            mod.normalize(vals)
        except ValueError:
            pass
        else:
            raise AssertionError("expected validation failure")
