# Generic Forge — an autonomous operator laboratory beyond mathematics

Generic Forge is a GitHub Actions research loop which **does not require
Lean, ChatGPT, Codex, an LLM or a continuously running PC**. It builds
*reusable, typed data-defined operators*, runs them in a finite environment,
evaluates their observable behavior, and adds certified operators back to
the next run's generation vocabulary.

It is a proof-of-architecture for a domain-independent
**Generator → Environment → Evaluator → Memory → Generator** cycle,
not a claim of artificial general intelligence or scientific creativity.

## Initial non-mathematical environments

The shared controller exposes two interchangeable finite environments.

| Domain | Artifact | Evaluation inputs | Example operations |
| --- | --- | ---: | --- |
| \`grid3\` | 3×3 monochrome pixel image | all 512 bitmaps | rotate, mirror, invert, translate, neighbor XOR, dilation |
| \`signal4\` | Four-sample quantized signal (levels 0..3) | all 256 sequences | reverse, rotate samples, add one modulo 4, adjacent XOR, clip, swap pairs |

Each environment's output stays within the same finite type.
This is software behavior, not a formal theorem about the real world.

The selected program is a **list of approved primitive names**, such as
\`["rotate_cw", "dilate", "mirror_lr"]\`. No generated Python source,
JavaScript, shell commands, or Lean tactics are executed. Program steps
are interpreted by a trusted, fixed main-branch controller.

## Using the result as a real tool

The verified library is not just a research scorecard. Once a macro is
certified, it can be invoked to transform a concrete image or signal:

~~~bash
python -m tools.autonomy.generic_forge run \
  --state docs/autonomy/generic-forge-state.json \
  --operator-id gf_XXXXXXXXXXXXXXXX \
  --value 1
~~~

Use an actual operator ID from the state branch. The command validates the
whole stored chain, then runs the certified macro through both implementations.
For images, the output JSON also includes an ASCII 3×3 bitmap (`#` for on
pixels, `.` for off); for signals, it includes four quantized samples.
No dynamically generated code is executed.

The PR CI demonstrates invocation of its first certified operator against
a real input image, saving `example-execution.json` as an inspectable
artifact. This creates a usable computational component, rather than only
another theorem/benchmark count.

## The central change: generated operations are reused

Initially, the generation vocabulary contains six primitive operators
per domain. Every candidate is **a composition of two operator tokens**,
each token either an original primitive or a *previously certified macro*.

A macro is stored in the verified JSON ledger as its expanded typed
primitive program, stable ID, parent IDs, and exhaustive behavior
fingerprint. The following run can compose **that new macro** with
another macro or primitive. As a result:

- The next program is derived from earlier observed behavior, not from
  a fixed list of final candidate models.
- Distinct behavior is determined by an exact finite-domain function
  fingerprint, not by a new or longer source string.
- Prior results define a growing library of certified components.
- A bounded, inspectable novelty heuristic prefers macro reuse, input
  coverage and behavioral diversity; domain counts balance image and
  signal experiments.

This is **composition and promotion of new data-defined operators**, not
creation of new trusted primitive semantics. The latter would need a
separate reviewable typed interpreter and independent acceptance gate.

## Independent evaluation and durability

For every candidate, **two independent implementations** run across
*every possible input* (512 images or 256 signals). One uses explicit
cell arrays; the other uses integer and bitwise operations.

The implementations must agree for all inputs. The evaluator records:
1. A SHA-256 fingerprint of the complete output truth table.
2. Number of inputs whose outputs differ from their inputs.
3. Number of distinct output states.
4. Deterministic example outputs for human inspection.

An identity operator or an operator with an already verified behavior
fingerprint is rejected. This is a complete **finite exhaustive
verification**, not kernel-certified Lean mathematics or a
generalization to other image/signal resolutions.

Accepted results go to the isolated, append-only branch
\`autonomy/generic-forge-state\`, path
\`docs/autonomy/generic-forge-state.json\`, with versioned evaluator ID,
typed composition parents, exact source commit, observable results,
UTC day or scheduled 30-minute slot, and a SHA-256-linked history.

Historical records are checked again against the current trusted
interpreter and their recorded composition ancestry before being used
as new generator operations. Modified/unknown operations fail closed.

## GitHub-native control plane

The workflow \`.github/workflows/generic-forge.yml\` has:
- A read-only PR job that runs unit tests, executes finite evaluations,
  and rehearses a complete receipt transition in ephemeral output.
- A default-branch-only scheduled/main-push job that reads the isolated
  state **as data** and proposes at most one new operator per UTC 30-minute slot.
- A separately privileged write job that regenerates the plan using
  the reviewed main controller, checks exact byte equality, independently
  repeats the exhaustive evaluation, validates the full receipt chain,
  and pushes **only one JSON state file** to the isolated branch.

The ongoing UTC schedule is **:07 and :37 every hour** (also :07/:37 JST).
Each job rounds the actual start time down to the current 30-minute UTC
slot, so a late or duplicate delivery cannot save the same slot twice.
GitHub schedules can run late or occasionally be skipped.

No external paid model call, external software execution, unrestricted
self-modification, auto PR merge or write to main is possible in the
research loop. At most 1,000 pairs of generation tokens are considered
per run, programs have at most eight primitive steps, and the generation
has a 96-receipt maintenance ceiling. At the limit, runs continue to
report no new candidate without mutating the state branch; raising or
archiving the limit requires a separate reviewed change. These are bounded
resource conditions, not a pre-listed fixed set of candidate outputs.

An operator whose behavior is unique is **not necessarily useful**.
Future evaluators can introduce real-world utility tests: e.g. image
quality, compressibility, execution throughput, human-judged usability,
or software reliability. Such tests must be implemented and documented
independently of the candidate generator so the generator cannot simply
rewrite the definition of success.

## Reproduction

Run from repository root, with Python 3.12 and no extra dependencies:

~~~bash
python -m unittest discover -s tests -p test_generic_forge.py -v
python -B -m tools.autonomy.generic_forge prepare \
  --state tests/fixtures/generic_forge_empty.json \
  --day 2026-11-24 --head "$(git rev-parse HEAD)" \
  --output verification/generic-forge/replay
python -B -m tools.autonomy.generic_forge receipt \
  --state tests/fixtures/generic_forge_empty.json \
  --head "$(git rev-parse HEAD)" \
  --evidence verification/generic-forge/replay \
  --output verification/generic-forge/ephemeral-next-state.json
~~~

The permanent half-hour cadence is implemented only for the Generic Forge
workflow; it does not expand controller permissions, install a paid model,
auto-merge PRs, or rewrite other autonomy workflows.

## Next steps outside this PR

Extend the domain registry to new environments such as workflow
optimizers, small software utilities and compression algorithms, each
with its own trust-isolated evaluation suite. Connect independently
verified finite-math tools only as optional adapters, not the purpose
of the system. Consider symbolic generation of **new typed operator
descriptions** that can be verified before they are promoted, rather
than changing executable Python itself.
