# Composed expansion rules

Stacked research on #294, #293, #292. The controller synthesizes macros
from already generated and certified expansion rules. It records ordered
parent IDs, flattened words, exact cardinality polynomials and minimum
word lengths. New macros can themselves be parents. All work is shadow
only; there are no production ledger or scheduling changes.

## Semantics and exact quotient

Use P(n)=n+1, Q(n)=n^2, R(n)=n^3. A word applies its letters left to right.
The comparison is exact equality of integer-coefficient polynomials,
not equality of generator implementations, structure-preserving maps,
or equivalence of the full expansion programs. Composition is
substitution of polynomials. The retained representative is a shortest
word, with deterministic tie-breaking. It executes a trace of the
constituent typed expansion rules, checking each classical sufficient
saturation criterion at the new parent size. Macro creation is
compression/reuse, not new primitive expressivity.

The search is stratified by minimum word length. If a shortest word had
a subword with a shorter polynomial-equivalent representative, replacing
it would shorten the original word. Therefore composing minimum-length
representatives from earlier layers suffices for exact bounded coverage.
This argument applies to the cardinality quotient only.

## Normal form theorem (classical, not Lean-formalized)

Two words have equal cardinality polynomials iff they have the same
normal form obtained by sorting each maximal Q/R block, leaving P letters
in their original positions. Thus the only relations are adjacent Q/R
commutations, and no words of different lengths coincide.

Proof: Every non-linear word polynomial is monic and can be written as
F=U^m+b, where b counts trailing P letters, m=2^i 3^j>=2 is the exponent
of its final maximal Q/R block, and U is the preceding word polynomial
(or x). The following elementary lemma determines the outer shift:

If nonconstant complex polynomials satisfy F=U^m+b=V^k+c with m,k>=2
and b!=c, then U and V have no common root. Hence U^(m-1) V^(k-1)
divides F'. Writing D=deg(F), the divisor has degree
2D-deg(U)-deg(V)>=D, while deg(F')=D-1, a contradiction.

Consequently b=c. Each preceding U is either linear or has a strictly
positive final shift, so it cannot be a proper perfect power over C by
the same lemma (compare a power with shift zero). Equivalently the gcd
of its complex root multiplicities is one. Therefore U^m=V^k implies
m=k from the gcd of the root multiplicities of the common polynomial,
and U=V by monicity. Unique factorization of m determines i,j.
Recursing through the preceding blocks proves the assertion; degree
one is exactly a sequence of P letters and is determined by its shift.

A normal form is a word over three letters with no adjacent RQ.
Let a_k be the number of normal forms of length k. Appending any letter
gives 3 a_(k-1) words, but appending Q to a word ending R gives exactly
a_(k-2) forbidden words. Thus a_0=1, a_1=3 and
a_k=3a_(k-1)-a_(k-2)=F_(2k+2). The cumulative nonempty count through k
is F_(2k+3)-2, with F_0=0, F_1=1.

## Verified local results

| Minimum length | New polynomials | Cumulative |
|---:|---:|---:|
| 1 | 3 | 3 |
| 2 | 8 | 11 |
| 3 | 21 | 32 |
| 4 | 55 | 87 |
| 5 | 144 | 231 |
| 6 | 377 | 608 |

All 1,092 nonempty words up to length six were independently enumerated,
and the resulting polynomial set and minimum lengths matched the
composed library exactly. Normal forms and the recurrence matched every
tested layer. Numerical evaluations at n=2,3,5,256 matched direct shape
execution. At least one generated macro uses two previously generated
macros as parents. The point-point trace 2->3->4 was independently
checked by complete closures (27 and 256 endomaps). Resume, corrupted
library rejection and budget rejection passed.

For a 256-state sample, with a cardinality bit-length cap of 65, 173 of
608 polynomials fit the cap. Maximizing final cardinality selects
P,P,P,Q,Q,Q, i.e. (n+3)^8:
256 -> 257 -> 258 -> 259 -> 67,081 -> 4,499,860,561 ->
20,248,745,068,443,234,721. This is a cardinality/proof trace, not a
dense transformation table. The objective maximizes only size, not
utility, runtime performance or structural diversity.

## Reproduction

```sh
python -B -m tools.autonomy.forge_rule_composition --selftest
python -B -m tools.autonomy.forge_rule_composition --output verification/composition-a --through 2
python -B -m tools.autonomy.forge_rule_composition --resume verification/composition-a/library.json --output verification/composition-b --through 6
python -B -m tools.autonomy.forge_rule_composition --root forge --state tests/fixtures/forge_monoid_evolution6.json --semantic tests/fixtures/forge_monoid_semantic4.json --output verification/composition-forge --through 6
```

CLI maximum length is six. The full library is replayed deterministically
on restart, rather than trusted as an input assertion. CI reconstructs the
actual six-generation Forge snapshot and adds the rank-255 candidate in
shadow. The original root's rank and history proofs were kernel-audited
in prior PRs; the child saturation theorems and normal form theorem
remain classical arguments. Canonical parent gates are still abstract
available operations, not compiled words in the original Forge alphabet.
