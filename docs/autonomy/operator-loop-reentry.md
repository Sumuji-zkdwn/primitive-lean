# Operator Loop reintegration — finite gate

The portable extracted system is reintroduced as an **additional** checked
component of primitive-lean. It does **not** replace the existing trusted Lean
build, source audit or proof registrar.

- `loopcore/engine.py`: domain-selected, deterministic finite candidates,
  exact verification, hash-linked persistent record, refusal on mutation.
- `loopcore/adapters/finite.py`: 84 Fin(3..8) witnesses; Python exhaustive
  finite verification; generated `.lean` snippets are **candidates only**.
- `tools/autonomy/check_extracted_loop.py`: independently replay the original
  autonomy ledger's models, compare exact generated proof source/hash, reject
  duplicates, and save verification/operator-loop-reentry.json.
- `.github/workflows/primitive-autonomy.yml`: checks the candidate before
  the original pinned Lean/mathlib verification and checks the sealed state
  after successful original validation. Failing the extra check stops the job.
- `.github/workflows/operator-loop-ci.yml`: dry-run smoke with a temporary
  workspace only; never pushes results, submits to Kaggle or consumes cloud
  inference APIs.

Local run from repository root:

```bash
python -m unittest discover -s tests -p test_loopcore.py -v
python -m loopcore run --domain finite --root /tmp/operator-loop-finite
python -m loopcore audit --domain finite --root /tmp/operator-loop-finite --recheck
```

The existing autonomous generator remains sole owner of
`autonomy/verified-operator-growth` and its verified Lean ledger. The
portable loop must not write to that branch by itself.

## Private quantum boundary

The original `kb-ndtjm` is private. Its WFS/Kickmix code is not copied
into this public repository. A private adapter in that repository can use
the same portable loop contract. Python WFS polynomial verification is
distinct from Kickmix parsing, full DQI verification and official Kaggle
scoring.

## Verification discipline

The finite check is neither proof of AGI nor proof that arbitrary generated
Lean code is valid. All actual Lean claims continue to require the original
`--trust=0` and all-declaration axiom auditing. Stop without commits if any
stage fails. Review PR and exact GitHub Actions run before merging.
