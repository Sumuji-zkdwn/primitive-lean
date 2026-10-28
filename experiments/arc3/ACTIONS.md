# ARC3 GitHub Actions workflow

## Dataset role

The official 25 public environments are **Public Demo** examples of the format
and basic mechanics, not a representative training/test set for the hidden games.
The earlier `ls20 ft09 vc33` runs are connection/regression checks on three familiar
examples. More seeds on those games do not create new held-out environments.
The `hybrid` game-ID lookup is retained as an example-specific diagnostic, not as
a general-policy improvement. Generic candidate promotion belongs to the separate
frozen-policy Kaggle rerun path, with public and final private scores distinguished.
Source: [ARC-AGI-3 technical report, Table 1 and Section 3.2](https://arcprize.org/media/ARC_AGI_3_Technical_Report.pdf).

`.github/workflows/arc3-staged-evaluation.yml` follows the staged validation pattern used by `kb-ndtjm`. It keeps routine repository checks separate from public environment downloads and does not submit anything to Kaggle.

## Stages

| Stage | Trigger | What it does | ARC API key |
|---|---|---|---|
| `unit` | Automatically on relevant pushes and pull requests; also manual | Installs the pinned ARC runtime and runs `tools/verify.py --arc3-only` | Not needed |
| `catalog` | Manual or an execution-branch push | Lists the API-visible demo inventory; no game is opened or played | Required |
| `public-smoke` | Manual | Downloads selected public environments with the ARC Toolkit, then compares `explore`, `model`, and `hybrid` at seed 3 and the selected call budget | Required |
| `multi-seed` | Manual | Runs the same three agents and games for the selected seeds; defaults to seeds 0–4 and 500 calls | Required |

The evaluation uses the same Python process, ARC SDK, downloaded environment files, call budget, and reset limit for all three agents. The existing evaluator records completed levels, total calls including the initial reset, gameplay actions, subsequent resets, final status, and elapsed time in `summary.json`. It also saves compressed traces and source/dependency metadata.

The default game selection is `all`: discover the current API-visible catalog
rather than silently using three example IDs. Exact IDs and versions, the count
and dataset role are saved in `arc3-demo-catalog.json`. Explicit game IDs remain
available for quick development checks. Catalog discovery and even all-demo
diagnostics do not measure hidden-game generalization. Hidden competition games
are unavailable to this local evaluation.

## ARC API setup

For either public evaluation stage, add the API key as a repository Actions secret named `ARC_API_KEY` under **Settings → Secrets and variables → Actions**. Keep the key in the secret store; do not paste it into workflow inputs or source files. The workflow fails with a short setup message if the secret is missing.

The workflow passes the key to the existing SDK download utility, which saves the selected public game environments under a temporary directory. The comparison then runs offline against those files. The artifact contains evaluation reports, traces, and environment file hashes, not the downloaded game source. It contains no Kaggle submission command.

## Running before the default-branch merge

The same workflow can run from an execution branch while the integration PR is
still a draft. A relevant push to `codex/arc3-public-smoke-*` selects
`public-smoke`; a relevant push to `codex/arc3-multi-seed-*` selects `multi-seed`.
An execution branch `codex/arc3-catalog-*` only records the catalog. Comparison
branches retain the budgets and seeds above and now default to the full API-visible
demo catalog. Ordinary main-branch
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
