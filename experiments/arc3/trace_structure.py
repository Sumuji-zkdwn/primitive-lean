"""Observation records before assigning state, goal, cost, or object semantics.

Tokens support equality/hash only. Contexts are caller-supplied experiment
anchors, NOT inferred hidden states. Reusing an anchor is an experimental
claim by the caller; this layer does not certify reset or reproducibility.
Different samples are evidence, not proof of distinct stochastic processes.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Hashable

Token = Hashable
Word = tuple[Token, ...]


@dataclass(frozen=True)
class Record:
    context: Token
    actions: Word
    observations: Word

    def __post_init__(self):
        if len(self.observations) != len(self.actions) + 1:
            raise ValueError("Record initial observation and one per action")
        hash((self.context, self.actions, self.observations))


@dataclass(frozen=True)
class Comparison:
    status: str
    # Include all shortest contrasts: ordering/names of tokens cannot select one.
    witnesses: tuple[tuple[Word, Word, Word], ...] = ()


class TraceEvidence:
    def __init__(self):
        self.records: list[Record] = []
        self._table: dict[Token, dict[Word, set[Word]]] = {}

    def add(self, record: Record) -> None:
        self.records.append(record)  # Preserve repeats, including frequencies.
        table = self._table.setdefault(record.context, {})
        for size in range(len(record.actions) + 1):
            table.setdefault(record.actions[:size], set()).add(
                record.observations[:size + 1])

    def outcomes(self, context: Token, actions: Word) -> frozenset[Word]:
        return frozenset(self._table.get(context, {}).get(actions, ()))

    def compare(self, left: Token, right: Token) -> Comparison:
        """Report observed contrasts; never certify continuation equivalence.

        All observations along a word count, not only its final observation.
        If repeat outcomes conflict, retain them; do not invent a deterministic
        transition. Absence of a contrast is not transitive equivalence.
        """
        a, b = self._table.get(left, {}), self._table.get(right, {})
        common = a.keys() & b.keys()
        if not common:
            return Comparison("untested")
        witnesses = [(word, x, y) for word in common
                     for x in a[word] for y in b[word] if x != y]
        if not witnesses:
            return Comparison("no_difference_observed")
        shortest = min(len(word) for word, _, _ in witnesses)
        return Comparison("different_samples", tuple(
            item for item in witnesses if len(item[0]) == shortest))

    def conflicting_words(self, context: Token) -> frozenset[Word]:
        """Repeated action words with multiple recorded observation sequences."""
        return frozenset(word for word, outcomes
                         in self._table.get(context, {}).items()
                         if len(outcomes) > 1)
