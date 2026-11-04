# RULEFOLD × 曼荼羅メーカー

`demos/rulefold_mandala.html` is a **standalone offline HTML** integrating the user's original `曼荼羅メーカー_v0.1_iOS.html` with a JavaScript reference of PR #73's finite higher-order rule machine.

## Run and operate

Open the HTML in a browser. The original full-screen **strict black/white continuous three-phase** artwork remains the primary interface. Touch / long press still influence the continuous field. The original top-right menu still provides pause, mutate, new pattern, PNG, ordinary GIF, MP4/H.264 on compatible browsers, and mandala JSON save/load.

Tap **RF** at bottom-left to open the optional Rulefold control panel. Its two modes are:

- **LAB (default):** 24-descriptor finite experiment. Step, run, inject a rule into E/M/L/D, or externally graft a finite rule cassette when the frontier stops. The optional auto-graft is a **fixed external control policy**, not an internal mathematical discovery mechanism.
- **PR #73 Fin4:** Exact finite JavaScript reference of the `HigherMachine` four-state witness. Mutable lift reaches `[0,1,2,3]`; frozen control reaches `[0,1,2]` and stalls. Both saturate.

Every machine state is deterministically encoded as a spatial-field coefficient vector, including harmonics, phase offsets, duty cycle, and three-phase XOR/majority composition. Transitions morph between configurations while holding winding fixed. This **art mapping is a new visual layer**, not a theorem claimed by PR #73.

## Export

The original PNG, GIF and MP4 functions remain unchanged. Their recording describes a periodic phase animation of the **current frozen visual configuration**, not the entire Rulefold history.

**変異のGIF** creates a separate **256 × 256, 48-frame, four-second, strict two-color GIF** from all visited rule-state patterns, with a closing transition. **履歴JSON / 読込** round-trip the machine program and visited states in schema `rulefold-mandala-v1`. The legacy mandala JSON schema `mandala-maker-v0.1` still works independently.

## Validation

```sh
node --test demos/higher_order_playground.test.cjs demos/rulefold_mandala.test.cjs
```

The integration has 10 Node regression tests covering Fin4 parity, frozen control, correct transition update order, reproducible visual signatures, bounded grafting, E/M/L/D edits, malformed import rejection, and original controls.

Local Chromium smoke tests additionally exercised actual pixel changes (exactly black and white), pointer contact/release, both reference traces, original PNG, ordinary GIF (GIF89a), H.264 MP4 (`ftyp` container), a 48-frame evolution GIF (GIF89a), and rule history JSON import. MediaRecorder support varies by browser and device.

## Formal boundary

The finite Rulefold transition interpreter is implemented in JavaScript, not verified directly by Lean. The `Fin4` portion mirrors the particular PR #73 Lean machine; the 24-descriptor LAB mode and artwork mapping are **independent experiments**. No unrestricted self-programming, unbounded novelty, guaranteed discovery of new theorem families, or Lean verification of the pixels is claimed. The original renderer and exporter source is retained, with additive methods only.

Sources: [primitive-lean PR #73](https://github.com/Sumuji-zkdwn/primitive-lean/pull/73), [Rulefold playground PR #74](https://github.com/Sumuji-zkdwn/primitive-lean/pull/74).
