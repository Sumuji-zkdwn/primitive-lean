# Finite information mowing (2026-11-06)

Base: PR #81, fixed source commit d75b7309b3e972f836494c1fc34df8202c869a7b. This experiment creates no Lean declarations and does not revisit the selected Lean certificate-verification task.

## Three independent inputs

Relation graph: a labelled simple undirected graph with fixed vertices V and edge state E subset of U, where U is the set of all unordered pairs of distinct vertices. A state is an integer bitmask.

Observation: choose connected (one component), components (the exact component partition including isolates), edge:u-v (direct edge membership) or reachable:u-v (two vertices in the same component).

Allowed actions: independently choose an ordered alphabet consisting of delete:u-v, add:u-v, and stay. These are deterministic total actions. Deleting a nonexistent edge is a no-op.

Current preservation is O(E)=O(F), for a retained subgraph F subset of E. Future preservation means O(T_w(E))=O(T_w(F)) for EVERY finite action word w in the selected alphabet, including the empty word. These are different requirements.

The graph_machine function enumerates all 2^|U| graphs on the fixed vertices. For each candidate F the new tool calls the *existing* shortest_cross_trace.shortest_word(M,M,actions,(E,F)) from PR #81. The result is a minimum-length distinguishing word with observation trace, or a reachable observation-preserving and action-closed relation. Every result is checked using the existing Python verify_certificate function. No Lean proof of the Python algorithm is claimed.

The finite exhaustive toy permits 1 to 4 vertices and considers all 2^|E| subgraphs, including the unpruned state. This is an exhaustive optimum *within the chosen graph, observation, actions and finite state semantics*.

## Reproduced results for the triangle

Graph V={A,B,C}, E={AB,AC,BC}; 8 candidate subgraphs.

| Observation | Allowed actions | Minimum retained edges | Safe deletion |
| --- | --- | --- | --- |
| connected | stay | 2 (any of the three paths) | any one edge |
| connected | delete AB only | 2 (AC,BC) | AB |
| connected | delete AB, delete AC, delete BC | 3 (AB,AC,BC) | none |
| direct existence of AB | delete AB, delete AC, delete BC | 1 (AB) | AC and BC |

One-step counterexample: delete AC first, so E'={AB,BC}. At the empty word, connected(E)=connected(E')=true. Applying operation delete AB gives original {AC,BC}, connected=true, versus pruned {BC}, connected=false. The shortest separator is [delete:A-B], length 1. The other single-edge trims are similarly distinguished at length 1 under all deletion actions. Removing any two edges breaks connectivity immediately: the shortest word is empty, length 0.

For four vertices, compare K4 to K4 minus AC with all six edge deletions. Removing just one further edge does not separate connectivity; [delete:A-B, delete:A-D] separates it at length 2. A shortest-word certificate is checked by the same existing Python verifier.

## Exact code and curve are distinct from equivalence

The canonical addition word, starting from the empty graph with fixed named vertices, recreates each retained graph exactly. For triangle it is [add:A-B, add:A-C, add:B-C].

A connected graph can also be encoded by ONE continuous edge-covering *labelled vertex walk*. If Eulerian, no edge repeats; otherwise DFS backtracking covers each edge at most twice. Triangle is [A,B,C,A], while the pruned path (AC removed) is [A,B,C]. With coordinates assigned to vertices, these become piecewise-linear parametrized curves. The labelled vertex sequence is needed to reconstruct edges; the geometric image alone may conflate crossing lines. A disconnected graph with isolates generally has no continuous walk covering its full relation graph; the result is null, while edge-addition words remain available.

The following are three separate claims: (1) encoding/reconstruction of the retained graph F, (2) observational equivalence between E and F under all SELECTED action words, and (3) dynamical/physical equivalence under separately supplied laws. This tool establishes or refutes (2) for its finite setup, and encodes (1), but makes NO claim about (3).

Counterpoint for dynamics: the spring energy U_E(x)=1/2 sum over edges uv of (x_u-x_v)^2 has value 3 for the triangle with (x_A,x_B,x_C)=(0,1,2), but 1 for the path E minus AC. Identical present connectivity does not preserve energy.

## Reproduction

From the repository root on the PR #81-based branch:

    python -m unittest discover -s tests -p 'test_relation_pruning.py' -v
    python tools/relation_pruning.py --demo triangle
    python tools/relation_pruning.py --actions stay
    python tools/relation_pruning.py --actions delete:A-B
    python tools/relation_pruning.py --observe edge:A-B

Observed in the local authoring environment on 2026-11-06: 11 of 11 unittest cases passed, including the triangle, 4-vertex two-step witness, curve reconstruction and malformed-input checks. This is local Python evidence, not a claim about GitHub CI or a formal verification of algorithmic soundness.
