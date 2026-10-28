# ARC3 GitHub Actions workflow

`.github/workflows/arc3-staged-evaluation.yml` follows the staged validation pattern used by `kb-ndtjm`. It keeps routine repository checks separate from public environment downloads and does not submit anything to Kaggle.

## Stages

| Stage | Trigger | What it does | ARC API key |
|---|---|---|---|
| `unit` | Automatically on relevant pushes and pull requests; also manual | Installs the pinned ARC runtime and runs `tools/verify.py --arc3-only` | Not needed |
| `public-smoke` | Manual | Downloads selected public environments with the ARC Toolkit, then compares `explore`, `model`, and `hybrid` at seed 3 and the selected call budget | Required |
| `multi-seed` | Manual | Runs the same three agents and games for the selected seeds; defaults to seeds 0–4 and 500 calls | Required |

The evaluation uses the same Python process, ARC SDK, downloaded environment files, call budget, and reset limit for all three agents. The existing evaluator records completed levels, total calls including the initial reset, gameplay actions, subsequent resets, final status, and elapsed time in `summary.json`. It also saves compressed traces and source/dependency metadata.

The default game list (`ls20 ft09 vc33`) reproduces the original public comparison scope. Additional game IDs can be supplied in the manual workflow inputs when the ARC API key can access them. Multiple seeds on these three games measure seed sensitivity; they do not establish generalization to other games. Hidden competition games are unavailable to this local evaluation.

## ARC API setup

For either public evaluation stage, add the API key as a repository Actions secret named `ARC_API_KEY` under **Settings → Secrets and variables → Actions**. Keep the key in the secret store; do not paste it into workflow inputs or source files. The workflow fails with a short setup message if the secret is missing.

The workflow passes the key to the existing SDK download utility, which saves the selected public game environments under a temporary directory. The comparison then runs offline against those files. The artifact contains evaluation reports, traces, and environment file hashes, not the downloaded game source. It contains no Kaggle submission command.

## Running before the default-branch merge

The same workflow can run from an execution branch while the integration PR is
still a draft. A relevant push to `codex/arc3-public-smoke-*` selects
`public-smoke`; a relevant push to `codex/arc3-multi-seed-*` selects `multi-seed`.
Both retain the default games, budgets and seeds above. Ordinary main-branch
pushes and pull requests still select `unit`. A separate queue per branch/event
prevents an independent evaluation or PR check from replacing a pending run.
These execution branches use the repository `ARC_API_KEY` secret and do not
require copying it into a different repository or any local file.

The authorized seed-3 public smoke on 2026-10-29 completed successfully in
[run 40745544075](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/40745544075),
including the toolkit download, all three agents and the result artifact.
The follow-up execution branch requests the existing five-seed defaults on the
same three games and 500-call budget. These are public development measurements,
not official competition scores or measurements on the other 22 public games.
