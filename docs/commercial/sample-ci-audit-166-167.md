# Sample deliverable — Lean 4 PR CI claim-to-check audit

*Public demonstration, 22 Nov 2026 (UTC). No external client or fee. This examines our own repository and cannot establish third-party demand. The matching [machine-readable evidence](sample-ci-audit-166-167.json) pins all essential IDs and boundaries.*

**Audit object:** [primitive-lean PR #166](https://github.com/Sumuji-zkdwn/primitive-lean/pull/166) at head `f004045716476c9e9eed91af70bedaf5cd52f503`. The PR adds a lexical Lean declaration exporter, two regression tests, and documentation. The specific checkable promise is that the newly introduced exporter runs correctly and produces reproducible, commit-pinned output. **This is not a claim that any indexed theorem is kernel-certified.**

## Decision matrix (observed, not inferred)

| Claim / question | Direct evidence | Disposition |
| --- | --- | --- |
| Did PR #166's green integration run exercise the new catalog exporter and targeted tests? | [Run #44621681312](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/44621681312) succeeded at `f004045`. Both job logs ([job 135904716278](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/44621681312/job/135904716278), [job 135904716728](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/44621681312/job/135904716728)) were searched for `test_export_agent_catalog`, `export_agent_catalog.py`, and `agent-catalog`; none occurred. | **Finding F-001:** green CI alone did **not** establish targeted exporter behavior. This is an evidence coverage gap, not a finding that the exporter was incorrect. |
| Has a specifically scoped exporter check now run? | [Draft PR #167](https://github.com/Sumuji-zkdwn/primitive-lean/pull/167) adds `.github/workflows/agent-catalog.yml`. [Run #44846643820](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/44846643820), [job 136667877536](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/44846643820/job/136667877536) at `2ddb0391320df9e7ee983b3f1fdc1fefb6074264`, succeeded; the log shows `Ran 2 tests` and `OK`. | **Targeted CI passes** for that exact head. This does not retroactively enlarge the test coverage of the earlier #166 run. |
| Will the initial workflow run on ordinary source-only pushes to `main`? | The original PR #167 `push.paths` list lacked `lean/**` and `linear_input/lean_check/**`. [Commit 2ddb039](https://github.com/Sumuji-zkdwn/primitive-lean/commit/2ddb0391320df9e7ee983b3f1fdc1fefb6074264) adds both patterns. | **Finding F-002:** initial event filter gap repaired in the draft. A post-merge `main` push has **not** been demonstrated, since PRs remain unmerged. |
| Is there an inspectable, pinned output? | Successful run uploaded [artifact #14682484755](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/44846643820/artifacts/14682484755), expiring **2026-12-21 00:52:23 UTC**. Its recorded source SHA is `2ddb0391320df9e7ee983b3f1fdc1fefb6074264`. | **Yes, at the verified CI head.** Artifact retention is finite and the GitHub-hosted ZIP is not an immutable long-term repository release. |
| Does 7,946 imply 7,946 verified theorems? | Job log reports 7,946 **lexically recognized declarations**, in 414 files, with `verification_status: not_assessed`. | **No.** The exporter neither elaborates statements nor audits per-declaration axioms. |

## Artifact fingerprint / acceptance evidence

| Field | Observed value |
| --- | --- |
| Repository | `Sumuji-zkdwn/primitive-lean` |
| Remediation head | `2ddb0391320df9e7ee983b3f1fdc1fefb6074264` |
| CI run and job | `44846643820` / `136667877536` |
| Workflow result | `success` |
| Unit tests | 2 passing |
| Source files scanned | 414 |
| Lexical declarations | 7,946 |
| JSONL SHA-256, reported by CI | `f26a14354cbbaa60ddd5d082ecb450ecdb7e6a35e2ee86c06365cc262f68ec42` |
| Artifact ID | `14682484755` |

**Important boundary:** the SHA-256 above was printed by the successful CI job after its own local re-generation/hash comparison. We **did not** independently download and hash the archive during this audit. Treat it as evidence of the CI step, not an independent third-party receipt.

Reproduction, while the artifact is available:

```sh
git clone https://github.com/Sumuji-zkdwn/primitive-lean.git
cd primitive-lean
git checkout --detach 2ddb0391320df9e7ee983b3f1fdc1fefb6074264
python3 -m unittest discover -s tests -p 'test_export_agent_catalog.py' -v
python3 tools/export_agent_catalog.py --ref HEAD --out-dir /tmp/primitive-audit
python3 tools/export_agent_catalog.py --ref HEAD --out-dir /tmp/primitive-audit --check
sha256sum /tmp/primitive-audit/declarations.jsonl
```

The `git` commands pin the same source commit used by the CI run. Compare the printed hash with the value in the table. This procedure is **provided for customer replication**; it was not re-executed locally for this case study. The GitHub workflow successfully performed the corresponding export and check.

## Scope / exclusions / commercial meaning

The deliverable covers only the provenance of particular CI invocations and the observable event-filter defect. It does not establish that the mathematical statements match the author's intention; a full Lean kernel replay and `#print axioms` review were **not** performed by this catalog audit; nor does it say the other pre-existing integration checks failed. This is a narrow check of **claim versus actual check**, not a security certification or theorem validity report.

For a third-party fixed-scope engagement the buyer would receive a similar Markdown/JSON evidence packet with source SHA, run and job URLs, a tested defect or an explicit negative finding, and a non-claims section. Only public repository data should be supplied. Any independent fix remains a draft pending the maintainer's review.

**Service inquiry:** [Paid pilot issue #168](https://github.com/Sumuji-zkdwn/primitive-lean/issues/168), indicative **¥24,800** for one accepted PR (up to 10 changed source/workflow files). This is a public inquiry route, **not a checkout or placed order**. Payment, tax treatment, acceptance, and delivery are not established. External customers: **0 verified**; revenue: **¥0 confirmed**.

*日本語要約：PR #166のCI成功は新設のカタログ出力・テストを直接検証していませんでした。PR #167で専用CIを追加し、ソース変更時の起動漏れも修正しました。上記は修正後のコミットに限定した検証資料であり、Lean定理全般の正しさや入金を証明するものではありません。*
