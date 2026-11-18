# Verification of switching on the signed first Laakso approximant

The new fragment contains three definitions and nine theorems. Its base is `1f83367f9680319849a1e0c5288cf7b5a19efb86`. The source ledger records the hashes of the fragment, the finite checker and their inputs. [Source ledger](../laakso/provenance-switching.json)

| Local check | Result |
|---|---|
| Lean 4.30.0-rc2, component compilation with `--trust=0` | Exit 0, no warnings. Axiom output for all 12 declarations contained only `propext`, `Classical.choice` and `Quot.sound`. |
| Finite orbit enumeration | All 64 signatures, all 64 vertex switches for each signature. The two orbits have 32 signatures each. Each signature normalizes along the tree obtained by omitting edge 3. |
| Exact energy replay | The checker covers both vertex switch choices at each endpoint and both edge signs on all six edges. For one rational-coordinate state all 4,096 simultaneous switches preserve energy. The fixed-state control distinguishes switching the signature alone. |

The all-real bound for every odd signature follows from the existing bound for the flipped representative. The rational replay provides a separate check of the conventions and code. The model fixes the first approximant, zero input and both coefficients at one. [Theorem map and parameter choices](../laakso/switching.md)

To reproduce the finite replay, run `python -B -X utf8 tools/check_laakso_signed.py`. The registered integration entry point is `python -B -X utf8 tools/verify.py --integration-only`.
