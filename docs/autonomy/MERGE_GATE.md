# Merge Gate — safe, read-only PR integration planner

Merge Gate makes the *review order and blockers* of open primitive-lean PRs
inspectable. It is deliberately not a merger, conflict resolver, or
authorization service. It cannot push, rebase, close or merge any PR.

## Two different kinds of dependencies

The repository already has Lean declaration dependency extraction in
tools/deps and a lexical source dependency graph. Merge Gate is an
additional **Git history and changed-file layer**, not a replacement.

- For two PRs, GitHub's compare API is applied to the *immutable head SHAs*.
  An ancestry edge A -> B is confirmed only when GitHub reports that B is
  ahead of A, B has no commits behind A, and the merge-base SHA is exactly
  A's head SHA. The reverse condition detects B -> A.
- Overlapping changed paths, including renamed old paths, are shown as
  **review obligations**. They do NOT prove a merge conflict. Git's actual
  three-way merge and the Lean kernel must still be rechecked after any
  integration.
- Disjoint changed files DO NOT mean independence of theorem hypotheses.
- CI observations are attached to the exact PR HEAD. Observed green checks
  are NOT a claim about which checks are required, completed approvals,
  branch protection, or the current PR base. Every row has
  merge_approval=false; the global report always has approval_granted=false
  and automated_merges=0.

No results from incomplete snapshots are promoted to "merge ready."

## Concrete historical fixture: Proof Forge PR #196 and #198

The fixture tests/fixtures/merge_gate_pair.json records data read from
GitHub on 2026-11-22. Both PRs were draft, targeted main at
8ed4c9347609ff350f947da7e44101abcd993ed9, and were unmerged.

- #196 HEAD 8c0f86b1618e997df5efd051952bf06365d18c48.
- #198 HEAD 15b068a3e12e50691cd7e48c89adae2fa4b9a8bf.
- GitHub compare #196 ... #198 returned "ahead", behind_by=0, ahead_by=21,
  with merge-base equal to #196's head SHA.
- #198's proposed change list contains seven files from #196; it has
  17 changed paths in total.

The confirmed edge is #196 -> #198. This is **ancestry evidence only**.
The report says "review parent first, then rebase child" and forbids
automatically merging either. The fixture is only a two-PR observation;
its total open PR inventory and current CI observations are explicitly
unknown. Never infer current live readiness from this dated fixture.

Replay offline using standard Python 3.12:

~~~sh
python -m unittest discover -s tests -p test_merge_gate.py -v
python tools/merge_gate.py \
  --snapshot tests/fixtures/merge_gate_pair.json \
  --report /tmp/merge-gate-report.json \
  --markdown /tmp/merge-gate-report.md
~~~

This yields exact ordered ancestry, shared-path evidence, missing-data
blockers, a JSON review queue, and human-readable Markdown.

## GitHub Actions execution

Workflow: .github/workflows/merge-gate.yml.

- In pull requests: ONLY offline regression and historical fixture
  analysis. Checkout uses the proposed PR head with
  persist-credentials=false. No GitHub API secrets are handed to this code.
  A JSON and Markdown evidence artifact is saved, even on regression failure.
- Once reviewed and merged into main: a separate trusted controller
  runs on **Mondays 11:17 Japan time**, or by manual workflow_dispatch
  on main. It checks out **main only**, with GITHUB_TOKEN limited to
  contents:read, pull-requests:read, checks:read. It inventories at most
  300 open PR metadata entries for selection, then examines the most
  recently updated 24 plus explicitly focused open #196 and #198.
  Per-PR files and exact-head check runs are bounded, and up to
  45 candidate ancestry comparisons are performed.
- If the open set exceeds the sample or the compare budget, or an API
  permission, pagination, check result, or commit pin is missing, this
  is recorded as **incomplete**, not silently marked clean.
- Live snapshots and JSON+Markdown reports are uploaded as artifacts,
  with the controller SHA, observed main SHA and all observed PR head SHAs.
  Nothing is written back to PR branches or main.

The trusted live job is disabled for pull_request events. It also requires
github.ref==refs/heads/main. Thus reviewing a malicious PR cannot cause
the workflow to execute untrusted PR code with a privileged API token.

After this PR is merged, the workflow becomes available on the default
branch. Before then, this PR proves only its offline regression behavior;
there is no claim that an unmerged workflow has already conducted a
live scheduled inventory.

## Limits and review workflow

GitHub's merge-base compare gives valid ancestry for the observed commits
but is not a semantic Lean dependency proof. A change to either head SHA
invalidates that specific prior relation until the compare is repeated.

The output review_order_only is a **dependency-respecting reading order**.
It is not a safe merge sequence or a permission to merge. Human-controlled
integration must separately confirm retained source hashes, current
base revision, axiom audit, all required CI, and appropriate PR approvals.

No auto-merge, force-push, automatic PR closing, paid AI inference, or
runtime execution of downloaded PR artifacts is implemented.
