# Forge Core for Android

Offline, isolated mobile prototype of the finite deterministic observational quotient. Contains the 256-state, 18-operator snapshot through evolution generation 6 and four semantic receipts. Starts with one observable class when there is no observation. New observations and operators refine to the exact coarsest stable partition, independently audited by pair reachability. Local state is saved by WebView DOM storage, with Android document picker import/export.

Build: `gradle -p mobile/forge-core :app:assembleDebug`. No INTERNET permission or remote code. Debug-signed APK, not a Play Store release. Finite bounds: 512 states, 32 observations, 32 operations, 2,100,000 pair/action combinations. No production ledger access, native Lean, background evolution or automatic external problem discovery. Device runtime remains to be tested.
