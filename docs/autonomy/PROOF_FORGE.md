# Proof Forge: bounded finite observer certificates

Status: **new prototype**. Every result remains PENDING_KERNEL_VERIFICATION until
the pinned CI has compiled the generated Lean file with --trust=0 and checked
the printed theorem axioms. A green unrelated CI job is not sufficient.

## What it does

This is a finite Moore-style observer model checker. Given an observation
for each state, deterministic transition maps for a finite action alphabet,
and a pair of starting states, it searches the product transition system.

The result is *exactly one* of:

- **DISTINGUISHABLE**: a shortest action word that produces different
  observations, with a Lean theorem verifying the explicit witness and
  a Lean theorem proving that *every* shorter action word fails to distinguish.
- **EQUIVALENT**: the complete reachable product-state relation, with Lean
  theorems proving it contains the initial pair, preserves observation, and
  is closed under every action. Induction then proves equality of the final
  readout for *all finite action words*, with no search depth bound.

The search takes at most the number of ordered state pairs (n squared), since
each pair is explored only once. This is a theorem about the **supplied finite
deterministic model**, not an inference about a physical continuum or an
unexamined transition system. The AI is not making an unverified assertion:
the selected finite claim is turned into a generated Lean certificate and
checked by the Lean kernel. Axioms are audited separately.

## Input: data only

Create a JSON file named proof_forge/requests/NAME.json in a new working
branch, using this schema:

~~~json
{
  "schema_version": 1,
  "name": "delayed_split",
  "observations": [0, 0, 0, 1],
  "transitions": [
    [1, 2, 3, 3],
    [0, 1, 2, 3]
  ],
  "pair": [0, 1]
}
~~~

There are four states (0..3) and two action types (0 and 1). Each row
transitions[action][state] is a destination state. The readout of a state is
observations[state]. Words are applied from left to right. The example finds
the shortest distinguishing word [0,0], whereas invisible_histories.json
demonstrates unbounded indistinguishability.

Bounds: 2..12 states, 1..4 actions, 0..7 observation labels, 1..12
request files per batch, 8192 bytes/file, and strictly validated names
and integers. Unknown JSON keys, duplicate keys, symlinks, Boolean
integers, or code-like names are rejected.

## From ChatGPT to GitHub to evidence

1. Create a branch from a known main commit. Add one or more JSON request
   files without touching the original models; open a **draft PR**.
2. The Proof Forge Actions workflow runs Python regression tests and the
   deterministic finite-state search, recording the exact checked-out
   Git commit SHA and SHA-256 hashes of the request and generated Lean.
3. GitHub-hosted Actions installs the repository's **pinned** Lean / Mathlib,
   compiles each generated Lean theorem using --trust=0, and checks each
   #print axioms result for disallowed dependencies.
4. Even on failure, logs, source and reports are retained as a workflow
   artifact. The JSON status is LEAN_VERIFIED only if the compilation and
   all audits passed; otherwise KERNEL_CHECK_FAILED.
5. Read the evidence from Chat using the GitHub connector. If a toolchain
   or proof error occurs, submit a **separate, bounded repair commit** and
   recheck the new exact head. Nothing automatically merges into main.

Run offline tests locally:

~~~sh
python -m unittest discover -s tests -p test_proof_forge.py -v
python tools/autonomy/proof_forge.py generate \
  --requests proof_forge/requests \
  --output verification/proof-forge \
  --head "$(git rev-parse HEAD)"
~~~

The first command runs without Lean or network. The generated Lean files
are not classified as proved until CI or a separately audited pinned Lean
kernel actually compiles them.

## Deliberate boundaries

This stage requires **no external AI API key or paid inference**. It does
not enable the paused legacy autonomous growth schedule, modify the main
branch, auto-merge PRs, request elevated GitHub permissions, or execute text
from research notes as commands. Every job has a hard execution limit.
A PR from an untrusted source receives only read access in this workflow.

Potential extension: connect the existing research scout's unverified
candidates to *human-reviewed* finite JSON requests. Do not promote a
scout note into a theorem without constructing and auditing the model.
