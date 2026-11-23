# Public PR intake preflight for the Lean 4 CI trust-boundary audit

This is a **read-only, no-checkout** intake utility for the [fixed-scope pilot offer](https://github.com/Sumuji-zkdwn/primitive-lean/issues/168). The pilot has an **indicative price of JPY 24,800 per accepted audit**, but this utility is free to inspect and is neither an order form nor a payment link. It does not run, reproduce, certify, or redistribute any external Lean code.

## What it automates

The tool accepts a canonical public GitHub PR URL and asks only the public GitHub REST API for:

- The PR's exact head and base commits, state, and reported changed-file count.
- A paginated file inventory (up to GitHub's 3,000-file cap). Only changed Lean source (`.lean`, `.inc`) and GitHub workflow files count toward the pilot's 10-file technical boundary.
- A *bounded first-page snapshot* of GitHub Actions runs matching the PR **head SHA** exactly. It excludes mismatched SHAs, but cannot see synthetic merge-commit checks, non-Actions providers, or later pages.
- A JSON record of collected evidence URLs and an honest eligibility flag. **Eligibility only means the small-scope candidate can be reviewed manually; it is not a quotation, acceptance, reservation, or guaranteed delivery.**

Examples:

~~~sh
python3 tools/commercial/triage_public_pr.py \
  https://github.com/Sumuji-zkdwn/primitive-lean/pull/166 \
  --output /tmp/lean-intake-166.json
python3 -m unittest discover -s tests -p 'test_commercial_pr_intake.py' -v
~~~

No dependency outside Python's standard library is needed. Anonymous access to the public GitHub API may be rate limited. Optionally set an appropriately scoped `GH_TOKEN` environment variable for rate limits. Do **not** embed tokens in a PR URL or a public output file; the program does not print token values. If GitHub is unavailable, it fails instead of inventing results.

## Deliberate distinction from free Lean verification tools

The official [leanprover/lean-action](https://github.com/leanprover/lean-action) already supports Lean builds, tests, linting, optional axiom audits, and independent checking with nanoda. Selling "yet another green build" would duplicate important free capabilities. The proposed audit instead compares a specific **customer claim** with actual execution: workflows, dispatch conditions, changed files, job logs, declarations reached, and whether an asserted guarantee is supported. This preflight automates **only the intake metadata**, not the paid claim-to-check analysis.

The example published in [draft PR #184](https://github.com/Sumuji-zkdwn/primitive-lean/pull/184) demonstrates a real mismatch inside this repository's own PR #166 and its correction in PR #167. It is not an external customer success story.

## What remains manual / unestablished

A reviewer must separately examine workflow source, exact CI job logs, actual build commands, test selection, axiom settings, artifact hashes, and scope agreed with the buyer. The tool never asserts that a successful workflow compiled a given theorem, never makes a kernel-correctness claim, and cannot determine which CI steps cover a target claim merely from the API result. Do not turn absent CI metadata into a categorical "CI never ran" finding.

**Commercial status:** no checkout, automated fulfillment, or paid engagement has been set up by this change. The existing public Issue #168 remains only an inquiry channel. An accepted order, tax treatment, payment instrument, and delivery time must be agreed before collecting money. No customer, order or revenue is asserted.
