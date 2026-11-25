# Forge Dialogue v0.1.0

A local Android experiment, not an LLM or a Japanese-language chatbot.

The APK build uses the existing `forge_lean_evolution.prepare_cycle` unchanged:
replay the actual semantic and evolution ledgers, regenerate and run the original
Lean proofs, export the ordered 256-entry tables and exact source/ledger SHAs.
A failed proof fails the APK build. The app embeds the existing Python modules
with Chaquopy (Python 3.12), not a new evaluator.

On each submitted string, UTF-8 bytes and the previous latent state form a
16-byte probe. The next input supplies a byte-distance feedback signal to
previous operators. The app uses original typed productions (independently
evaluated over all 256 inputs) and compositions, admitting distinct tables
into an isolated local alphabet. Responses use the evolving observed character
alphabet and selected operator. No dictionary, pretrained NLP, network
permission or API key. Feedback is not a semantic correctness measure.

"Forge探索" invokes the original `search` algorithm on the experimental alphabet.
Local additions are labeled FINITE_CHECKED_NOT_LEAN_VERIFIED. They never
enter the upstream proof ledger. No Python or Lean code is learned or executed
from dialogue input. The current app does not run Lean on Android or implement
the production daily gate locally; the original GitHub Actions remain intact.

Local state saves atomically, replays local recipes and checks fingerprints on
startup. Limit: 128 local operators (chat remains usable after the cap).
Recent 100 turns are shown; JSON export contains all turns, recipes and the
entire immutable build snapshot. JSON import, migration between different
snapshots, native Lean, and Android runtime benchmarking are deferred. Keep
exports before uninstalling. The snapshot is exact for the build, not live sync.

APK: the "Forge Android Dialogue - proof snapshot and APK" workflow, artifact
"Forge-Dialogue-Android", arm64-v8a and x86_64, API 24+. Debug signature, not a
Play Store release. Host tests check persistence, deterministic dialogue,
feedback, local reentry and rejection of changed fingerprints; no device test
yet. Source and proof artifacts are separate from the APK.
