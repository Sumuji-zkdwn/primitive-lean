# ARC3 GitHub Actions workflow

`.github/workflows/arc3-staged-evaluation.yml` follows the staged validation pattern used by `kb-ndtjm`. It keeps routine repository checks separate from Kaggle data downloads and does not submit anything to Kaggle.

## Stages

| Stage | Trigger | What it does | Kaggle token |
|---|---|---|---|
| `unit` | Automatically on relevant pushes and pull requests; also manual | Installs the pinned ARC runtime and runs `tools/verify.py --arc3-only` | Not needed |
| `public-smoke` | Manual | Downloads the public competition bundle, then compares `explore`, `model`, and `hybrid` on the selected games at seed 3 and the selected call budget | Required |
| `multi-seed` | Manual | Runs the same three agents and games for the selected seeds; defaults to seeds 0–4 and 500 calls | Required |

The evaluation uses the same Python process, ARC SDK, downloaded environment files, call budget, and reset limit for all three agents. The existing evaluator records completed levels, total calls including the initial reset, gameplay actions, subsequent resets, final status, and elapsed time in `summary.json`. It also saves compressed traces and source/dependency metadata.

The default game list (`ls20 ft09 vc33`) reproduces the original public comparison scope. Additional public game IDs can be supplied in the manual workflow inputs when present in the downloaded bundle. Multiple seeds on these three games measure seed sensitivity; they do not establish generalization to other games. Hidden competition games are unavailable to this local evaluation.

## Kaggle setup

For either public evaluation stage, accept the ARC-AGI-3 competition rules on Kaggle and add the Kaggle API token as a repository Actions secret named `KAGGLE_API_TOKEN` under **Settings → Secrets and variables → Actions**. Keep the token in the secret store; do not paste it into workflow inputs or source files. The workflow fails with a short setup message if the secret is missing.

The workflow downloads the latest competition data with pinned `kagglehub==1.0.3`, locates its `environment_files` directory, and passes it to the existing offline evaluator. It uploads only the evaluation reports and traces, not the downloaded competition bundle. It contains no Kaggle submission command.
