"""Exact constraint transport for a supplied reversible XOR model.

This backend represents all compatible bit states without listing them.
It does NOT infer the gates or assert that an unknown ARC environment is linear.
Each CNOT update substitutes the inverse map into the retained constraints.
"""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class LinearObservable:
    mask: int
    bias: int = 0

    def cnot(self, control: int, target: int) -> LinearObservable:
        # Original observable expressed in the NEW state's coordinates.
        mask = self.mask ^ ((1 << control) if self.mask & (1 << target) else 0)
        return LinearObservable(mask, self.bias)


class AffineBelief:
    def __init__(self, width: int, equations=()):
        if width < 1:
            raise ValueError("Positive width required")
        self.width = width
        self.basis: dict[int, tuple[int, int]] = {}
        self.inconsistent = False
        for mask, value in equations:
            self.observe(mask, value)

    def _check(self, mask: int, value: int):
        if not 0 <= mask < (1 << self.width) or value not in (0,1):
            raise ValueError("Invalid linear constraint")

    def reduce(self, mask: int, value: int = 0) -> tuple[int, int]:
        self._check(mask, value)
        for pivot in sorted(self.basis, reverse=True):
            if mask & (1 << pivot):
                row, rhs = self.basis[pivot]
                mask ^= row
                value ^= rhs
        return mask, value

    def observe(self, mask: int, value: int):
        self._check(mask, value)
        if self.inconsistent:
            return
        mask, value = self.reduce(mask, value)
        if not mask:
            self.inconsistent |= bool(value)
            return
        self.basis[mask.bit_length()-1] = (mask, value)

    def cnot(self, control: int, target: int):
        if control == target or not (0 <= control < self.width and 0 <= target < self.width):
            raise ValueError("Distinct in-range CNOT wires required")
        rows = [(mask ^ ((1 << control) if mask & (1 << target) else 0), rhs)
                for mask, rhs in self.basis.values()]
        self.basis = {}
        for mask, rhs in rows:
            self.observe(mask, rhs)

    def known(self, observable: LinearObservable) -> int | None:
        if self.inconsistent:
            return None
        mask, rhs = self.reduce(observable.mask, observable.bias)
        return rhs if mask == 0 else None

    @property
    def dimension(self) -> int | None:
        return None if self.inconsistent else self.width-len(self.basis)

    @property
    def cardinality(self) -> int:
        return 0 if self.inconsistent else 1 << self.dimension

    def contains(self, state: int) -> bool:
        return (not self.inconsistent and 0 <= state < (1 << self.width) and
                all((state & mask).bit_count() % 2 == rhs for mask,rhs in self.basis.values()))


def parity_macro(data_bits: int) -> tuple[tuple[int, int], ...]:
    """Compute shared XOR into scratch, use it at wire 0, then clean scratch.

    Requires scratch wire=data_bits initially zero to make the left wire equal
    the original data parity. Scratch is returned to its incoming value.
    """
    if data_bits < 2:
        raise ValueError("At least two data wires required")
    compute = tuple((i,data_bits) for i in range(1,data_bits))
    return compute + ((data_bits,0),) + tuple(reversed(compute))


def transport(belief: AffineBelief, observable: LinearObservable, gates):
    for control, target in gates:
        belief.cnot(control,target)
        observable = observable.cnot(control,target)
    return observable


def demonstrate(data_bits: int, initial_left: int, measured_parity: int) -> dict:
    scratch = 1 << data_bits
    belief = AffineBelief(data_bits+1, [(1,initial_left), (scratch,0)])
    target = LinearObservable((1 << data_bits)-1)
    gates = parity_macro(data_bits)
    before = belief.dimension
    target = transport(belief,target,gates)
    scratch_cleared = belief.known(LinearObservable(scratch)) == 0
    # One actual observed bit is added; the backend never invents this measurement.
    belief.observe(1,measured_parity)
    resolved = belief.known(target)
    target = transport(belief,target,reversed(gates))
    return {
        "data_bits": data_bits,
        "initial_left": initial_left,
        "observed_parity": measured_parity,
        "initial_affine_dimension": before,
        "remaining_affine_dimension": belief.dimension,
        "remaining_states": f"2^{belief.dimension}",
        "retained_independent_constraints": len(belief.basis),
        "gates_forward": len(gates),
        "gates_round_trip": 2*len(gates),
        "scratch_cleared_after_compute_use_clean": scratch_cleared,
        "goal_value_after_measurement": resolved,
        "goal_value_after_restore": belief.known(target),
        "initial_left_restored": belief.known(LinearObservable(1)) == initial_left,
        "scratch_zero_after_restore": belief.known(LinearObservable(scratch)) == 0,
        "target_expression_restored": target == LinearObservable((1 << data_bits)-1),
    }


if __name__ == "__main__":
    import json
    from pathlib import Path
    result = {
        "scope": "Exact GF(2) affine backend with known legal reversible operations, not ARC performance",
        "explicit_state_enumeration": False,
        "runs": [demonstrate(n,left,parity) for n in [3,9,1000]
                 for left in [0,1] for parity in [0,1]],
    }
    Path("affine_belief_results.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"scope":result["scope"],"sample":result["runs"][-1]},indent=2))
