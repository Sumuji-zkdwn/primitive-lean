# primitive-lean dependency graphs

Snapshot: main 956fe5c9f18f1360a84a1736dcf038ebc0cdf7b3, PR metadata 2026-11-05.
Main sources, registries and PR snapshot were read from Git blobs at main_commit.
PR overlays use immutable base/head SHAs listed in graph.json pr_inputs.

A --> B means A references B. It does NOT mean A mathematically implies B.

This graph distinguishes (1) exact Lean import, (2) literal qualified declaration
references, (3) globally unique bare-name candidates, and (4) PR base-target edges.
Only (1) and (2) appear in the graphical source edges.

Main files: 381; PR overlay files: 17.
Declaration names scanned: 7632.
Source edges: {"exact_import": 122, "qualified_reference": 283, "unique_identifier_candidate": 895}.

## Source group dependencies

~~~mermaid
flowchart LR
  g0["Arithmetic / Galois (20)"]
  g1["Bayes / Jets (3)"]
  g2["Elastica (25)"]
  g3["F0 / Observation (16)"]
  g4["F16 / Recovery (14)"]
  g5["IUT comparison / Pilot (4)"]
  g6["LinearInput foundation (36)"]
  g7["Local / Global gluing (16)"]
  g8["Operator / Rulefold (19)"]
  g9["OrbitTrace (18)"]
  g10["Other (40)"]
  g11["Other supplements (177)"]
  g12["WFS / Fenchel (10)"]
  g10 -->|36 source refs| g2
  g11 -->|22 source refs| g6
  g6 -->|17 source refs| g2
  g11 -->|13 source refs| g2
  g11 -->|10 source refs| g3
  g11 -->|9 source refs| g8
  g0 -->|8 source refs| g3
  g3 -->|5 source refs| g4
  g7 -->|5 source refs| g12
  g10 -->|4 source refs| g8
  g3 -->|3 source refs| g6
  g4 -->|3 source refs| g3
  g1 -->|2 source refs| g2
  g1 -->|2 source refs| g3
  g3 -->|2 source refs| g12
  g5 -->|2 source refs| g3
  g8 -->|2 source refs| g3
  g12 -->|2 source refs| g3
  g12 -->|2 source refs| g11
  g0 -->|1 source refs| g11
  g10 -->|1 source refs| g11
  g11 -->|1 source refs| g0
  g11 -->|1 source refs| g4
~~~

## PR targets (not theorem dependencies)

~~~mermaid
flowchart LR
  main["main"]
  p3["PR #3 merged"]
  p31["PR #31 open"]
  p55["PR #55 closed"]
  p56["PR #56 closed"]
  p57["PR #57 closed"]
  p60["PR #60 closed"]
  p61["PR #61 closed"]
  p62["PR #62 closed"]
  p63["PR #63 closed"]
  p64["PR #64 closed"]
  p65["PR #65 open"]
  p66["PR #66 open"]
  p67["PR #67 open"]
  p69["PR #69 open"]
  p70["PR #70 open"]
  p71["PR #71 open"]
  p72["PR #72 open"]
  p73["PR #73 closed"]
  p74["PR #74 merged"]
  p75["PR #75 open"]
  p77["PR #77 open"]
  p78["PR #78 open"]
  p3 -.->|PR base| main
  p31 -.->|PR base| p3
  p55 -.->|PR base| p3
  p56 -.->|PR base| p55
  p57 -.->|PR base| p56
  p60 -.->|PR base| p57
  p61 -.->|PR base| p60
  p62 -.->|PR base| p61
  p63 -.->|PR base| p62
  p64 -.->|PR base| p63
  p65 -.->|PR base| p64
  p66 -.->|PR base| p65
  p67 -.->|PR base| p66
  p69 -.->|PR base| p67
  p70 -.->|PR base| p69
  p71 -.->|PR base| p69
  p72 -.->|PR base| main
  p73 -.->|PR base| p64
  p74 -.->|PR base| main
  p75 -.->|PR base| main
  p77 -.->|PR base| main
  p78 -.->|PR base| main
~~~

## Complete machine-readable outputs

- graph.json: source files, declaration names, evidence and confidence classes
- modules.mmd: exact import and qualified reference module graph
- groups.mmd: overview by subject area
- branches.mmd: PR target graph
- source-edges.tsv: source-to-dependency evidence table

## Limits

Concatenation order in the generated All.lean / MainResult.lean is recorded,
but is not itself considered a proof dependency.
The scanner does not invoke Lean elaboration or trace theorem premises.
The #70/#71 ParallelLocalGluing.inc implementations conflict and remain distinct.
No IUT III 3.11 -> 3.12 proof is inferred from superficial thematic links.
