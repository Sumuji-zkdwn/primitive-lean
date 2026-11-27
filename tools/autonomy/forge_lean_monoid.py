"""Read-only proof-gated rank extension after reversible Forge saturation.

No production ledger writes. A candidate may not become a receipt without a
kernel audit and a separately reviewed schema/replay migration.
"""
from __future__ import annotations
import argparse
from collections import deque
from itertools import product
from math import factorial
from pathlib import Path
import json
from tools.autonomy import forge_lean_evolution as evo
from tools.autonomy import forge_lean_certificate as cert
from tools.autonomy import forge_lean_feedback as fb
from tools.autonomy import forge_lean_reentry as reentry
from tools.autonomy import semantic_forge as sf

N = 256
X = range(N)
WORD = [4,2,7,4,8,4,4,2,6,7,9,4,4,5,4,6,5,9,1,0,1,2,0,9,1,0,6,1,9,8,8,8,0,4,7,5,5,2,4,5,1,1,0,6,7,9,0,5,5,6,5,3,3,5,2,1,0,8,0,8]
POWER = 71060
require = evo.require

def rank(v):
    return len(set(v))

def compose(f, g):
    return [g[x] for x in f]

def power(v, n):
    result = list(X)
    while n:
        if n & 1:
            result = compose(result, v)
        v = compose(v, v)
        n >>= 1
    return result

def cycles(v):
    require(rank(v) == N, "cycle decomposition needs a permutation")
    seen, result = set(), []
    for x in X:
        if x in seen:
            continue
        cycle, y = [], x
        while y not in seen:
            seen.add(y)
            cycle.append(y)
            y = v[y]
        require(y == x, "invalid permutation")
        result.append(cycle)
    return result

def pair_orbit(gens):
    seen = bytearray(N*N)
    seen[1] = 1
    todo = deque([1])
    count = 1
    while todo:
        a, b = divmod(todo.popleft(), N)
        for g in gens:
            y = N*g[a] + g[b]
            if not seen[y]:
                seen[y] = 1
                todo.append(y)
                count += 1
    return count

def finite_seeds():
    """Reproduce the source ranking, using both original interpreters."""
    constants = cert.CONSTANTS
    ranks, reversibles = [], []
    for r in fb.recipes():
        v = cert.table(lambda x: fb.reference(r,x), lambda x: fb.packed(r,x))
        if rank(v) > 4 and any(v[x] not in constants for x in constants):
            ranks.append((r,v))
    for r in reentry.recipes():
        v = cert.table(lambda x: reentry.reference(r,x), lambda x: reentry.packed(r,x))
        if any(v[x] not in constants for x in constants):
            reversibles.append((r,v))
    r,a = min(ranks,key=lambda rv:(-rank(rv[1]),rv[0]))
    s,b = min(reversibles,key=lambda rv:(-sum(x!=y for x,y in enumerate(rv[1])),rv[0]))
    require(evo.fingerprint(a) == evo.OLD_SEED and rank(a)==175, "rank seed drift")
    require(rank(b)==N and sum(x!=y for x,y in enumerate(b))==128, "reversible seed drift")
    return {"seed:rank":a,"seed:reversible":b}

def reconstruct(state, semantic, seeds):
    accepted, stages, runs = {}, [], {}
    previous, count, prior = evo.ZERO, 1, None
    for i,row in enumerate(state["receipts"],1):
        require(row["generation"]==i and row["previous_sha256"]==previous
                and row["chain_sha256"]==evo.digest({k:v for k,v in row.items() if k!="chain_sha256"}),
                "history chain drift")
        evo.validate_receipt_order(row,prior,runs)
        n = row["semantic_count"]
        require(count<=n<=len(semantic["receipts"]) and
                row["semantic_prefix_sha256"]==semantic["receipts"][n-1]["chain_sha256"],"ancestry drift")
        tables=evo.roots(semantic,n,seeds)
        tables.update(accepted)
        v=evo.evaluate(row["recipe"],tables)
        require(v==evo.evaluate(row["recipe"],tables,independent=True)
                and evo.fingerprint(v)==row["behavior_sha256"]
                and all(v[v[x]]==x for x in X),"historical behavior drift")
        accepted["e:"+row["chain_sha256"][:24]]=v
        tables.update(accepted)
        stages.append(tables)
        previous,count,prior=row["chain_sha256"],n,row
    return accepted,stages

def verify_group(stages):
    require(len(stages)==6,"this saturation witness is pinned to six generations")
    p5={k:v for k,v in stages[4].items() if rank(v)==N}
    p6={k:v for k,v in stages[5].items() if rank(v)==N}
    gs=list(p5.values())
    require(len(gs)==10 and all((N-len(cycles(v)))%2==0 for v in gs),"stage five parity drift")
    orbit=pair_orbit(gs)
    require(orbit==N*(N-1),"not two-transitive")
    w=list(X)
    for i in WORD:
        w=compose(w,gs[i])
    three=power(w,POWER)
    nontrivial=[c for c in cycles(three) if len(c)>1]
    require(nontrivial==[[69,183,104]] and
            evo.fingerprint(three)=="70d777ddaf8da6e43451b13684508f09956964c9c3b2db336c3279a0c0b4bd9c",
            "3-cycle witness drift")
    require(all(p6[k]==v for k,v in p5.items()) and any((N-len(cycles(v)))%2 for v in p6.values()),
            "stage six odd extension drift")
    # Jordan's theorem: two-transitive implies primitive; a primitive group
    # containing a 3-cycle contains A_n for n >= 6. The parity tests give equality.
    return {"stage5":"A_256","stage6":"S_256","stage5_order":str(factorial(N)//2),
            "stage6_order":str(factorial(N)),"pair_orbit":orbit,"generator_ids":list(p5),
            "word":WORD,"power":POWER,"three_cycle":nontrivial[0]}

def candidate(tables):
    singular=[rank(v) for v in tables.values() if rank(v)<N]
    require(bool(singular) and max(singular)<N-1,"rank separation exhausted")
    # New typed construction: restrict the action of a parent to one state.
    # The two evaluators check every input independently.
    for name,parent in tables.items():
        for a in X:
            if parent[a]==a:
                continue
            v=cert.table(lambda x: parent[x] if x==a else x,
                         lambda x: x+int(x==a)*(parent[x]-x))
            require(rank(v)==N-1 and all(v[v[x]]==v[x] for x in X),"rank-one collapse drift")
            return ["restrict_at",name,a],v,max(singular)
    raise ValueError("no nonidentity parent")

CORE = r"""
namespace ForgeMonoid
open LinearInputOperatorWords
abbrev Signal := Fin 256
def tableStep (xs : List Signal) (x : Signal) : Signal :=
  (xs[x.val]?).getD 0
def Small (T : Signal → Signal) : Prop :=
  ∃ g : Fin BOUND → Signal, ∀ x : Signal, ∃ j : Fin BOUND, T x = g j
def Good (T : Signal → Signal) : Prop :=
  Function.Injective T ∨ Small T
theorem good_comp {f g : Signal → Signal} (hf : Good f) (hg : Good g) :
    Good (fun x => g (f x)) := by
  rcases hf with hf | ⟨a, ha⟩
  · rcases hg with hg | ⟨b, hb⟩
    · apply Or.inl
      intro x y h
      exact hf (hg h)
    · exact Or.inr ⟨b, fun x => hb (f x)⟩
  · refine Or.inr ⟨fun j => g (a j), ?_⟩
    intro x
    obtain ⟨j, hj⟩ := ha x
    exact ⟨j, congrArg g hj⟩
theorem good_word {ι : Type*} (step : ι → Signal → Signal)
    (hstep : ∀ i, Good (step i)) (word : List ι) :
    Good (run step word) := by
  induction word with
  | nil =>
    apply Or.inl
    intro x y h
    exact h
  | cons i rest ih =>
    change Good (fun x => run step rest (step i x))
    exact good_comp (hstep i) ih
theorem not_small_of_injective (T : Signal → Signal)
    (probe : Fin PROBES → Signal)
    (hinj : Function.Injective (fun i => T (probe i))) :
    ¬ Small T := by
  classical
  rintro ⟨g, hg⟩
  let f : Fin PROBES → Fin BOUND := fun i => Classical.choose (hg (probe i))
  have hf : ∀ i, T (probe i) = g (f i) :=
    fun i => Classical.choose_spec (hg (probe i))
  have hi : Function.Injective f := by
    intro i j h
    apply hinj
    change T (probe i) = T (probe j)
    calc
      T (probe i) = g (f i) := hf i
      _ = g (f j) := congrArg g h
      _ = T (probe j) := (hf j).symm
  have hcard := Fintype.card_le_of_injective f hi
  norm_num at hcard
"""

def literal(xs):
    return "["+", ".join(map(str,xs))+"]"

def lookup(name,dom,cod,xs):
    return f"def {name} (x : Fin {dom}) : Fin {cod} := (({literal(xs)} : List (Fin {cod}))[x.val]?).getD 0\n"

def certificate(tables, v, bound, out):
    probes=bound+1
    names=["good_comp","good_word","not_small_of_injective"]
    parts=["import Mathlib\nset_option maxRecDepth 16384\nset_option maxHeartbeats 100000000\n",
           cert.WORDS.read_text(),CORE.replace("BOUND",str(bound)).replace("PROBES",str(probes))]
    for i,t in enumerate(tables.values()):
        op=f"op_{i}"
        parts.append(lookup(op,N,N,t))
        if rank(t)==N:
            inverse=[0]*N
            for x,y in enumerate(t):inverse[y]=x
            parts.append(lookup(f"inv_{i}",N,N,inverse))
            parts.append(f"""
theorem left_{i} : ∀ x : Signal, inv_{i} ({op} x) = x := by decide
theorem letter_{i} : Good {op} := by
  apply Or.inl
  intro x y h
  exact (left_{i} x).symm.trans ((congrArg inv_{i} h).trans (left_{i} y))
""")
            names.append(f"left_{i}")
        else:
            image=sorted(set(t))
            require(len(image)<=bound,"bad rank bound")
            idx={y:j for j,y in enumerate(image)}
            cover=image+[image[0]]*(bound-len(image))
            parts.extend([lookup(f"cover_{i}",bound,N,cover),lookup(f"index_{i}",N,bound,[idx[y] for y in t])])
            parts.append(f"""
theorem covered_{i} : ∀ x : Signal, {op} x = cover_{i} (index_{i} x) := by decide
theorem letter_{i} : Good {op} := Or.inr ⟨cover_{i}, fun x => ⟨index_{i} x, covered_{i} x⟩⟩
""")
            names.append(f"covered_{i}")
        names.append(f"letter_{i}")
    n=len(tables)
    parts.append(f"def alphabet (i : Fin {n}) : Signal → Signal := match i.val with\n")
    parts.extend(f"  | {i} => op_{i}\n" for i in range(n))
    parts.append("  | _ => op_0\ntheorem alphabet_good (i : Fin "+str(n)+") : Good (alphabet i) := by\n  fin_cases i <;> first\n")
    parts.extend(f"    | exact letter_{i}\n" for i in range(n))
    first={}
    for x,y in enumerate(v):first.setdefault(y,x)
    sample=list(first.values())[:probes]
    require(len(sample)==probes,"too few distinct probes")
    decoder=[0]*N
    for i,x in enumerate(sample):decoder[v[x]]=i
    a,b=reentry.collision(v)
    parts.extend([lookup("candidate",N,N,v),lookup("probe",probes,N,sample),lookup("decoder",N,probes,decoder)])
    parts.append(f"""
theorem candidate_collision : candidate {a} = candidate {b} := by decide
theorem candidate_not_injective : ¬ Function.Injective candidate := by
  intro h
  exact (by decide : ({a} : Signal) ≠ {b}) (h candidate_collision)
theorem probe_left : ∀ i : Fin {probes}, decoder (candidate (probe i)) = i := by decide
theorem candidate_not_small : ¬ Small candidate := by
  apply not_small_of_injective candidate probe
  intro i j h
  exact (probe_left i).symm.trans ((congrArg decoder h).trans (probe_left j))
theorem candidate_not_word (word : List (Fin {n})) :
    candidate ≠ run alphabet word := by
  intro h
  have hg := good_word alphabet alphabet_good word
  rw [← h] at hg
  exact hg.elim candidate_not_injective candidate_not_small
theorem candidate_not_macros {{κ : Type*}} (code : κ → List (Fin {n})) (word : List κ) :
    candidate ≠ run (generated alphabet code) word := by
  intro h
  apply candidate_not_word (compile code word)
  funext y
  exact (congrFun h y).trans (run_generated alphabet code word y)
end ForgeMonoid
""")
    names+=["alphabet_good","candidate_collision","candidate_not_injective","probe_left","candidate_not_small","candidate_not_word","candidate_not_macros"]
    parts.extend(f"#print axioms ForgeMonoid.{name}\n" for name in names)
    out.mkdir(parents=True,exist_ok=True)
    (out/"Certificate.lean").write_text("".join(parts),encoding="utf-8")
    fb.write(out/"mapping.json",{"status":"GENERATED_PENDING_KERNEL_VERIFICATION","receipt_count":1,
             "theorem_count":len(names),"theorems":names,"behavior_sha256":evo.fingerprint(v),
             "certificate_sha256":fb.sha(out/"Certificate.lean")})

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--state",type=Path,required=True)
    p.add_argument("--semantic",type=Path,required=True)
    p.add_argument("--output",type=Path,required=True)
    p.add_argument("--kernel",action="store_true")
    a=p.parse_args()
    require(a.output.resolve() not in (a.state.resolve(),a.semantic.resolve()),"output must be separate")
    state=evo.read_history(a.state)
    semantic=sf.validate_state(sf.read(a.semantic))
    seeds=finite_seeds()
    accepted,stages=reconstruct(state,semantic,seeds)
    group=verify_group(stages)
    tables=evo.roots(semantic,len(semantic["receipts"]),seeds)
    tables.update(accepted)
    recipe,v,bound=candidate(tables)
    require(recipe==["restrict_at","p:reverse",1] and bound==175 and v[1]==64,"snapshot regression")
    require(evo.fingerprint(v)=="f9fdd6687e635000fdec6a4f4aba333918956dd8c7ed7751669d3c2425ed86f8","candidate drift")
    a.output.mkdir(parents=True,exist_ok=True)
    certificate(tables,v,bound,a.output/"new")
    report={"status":"FINITE_AUDIT_PASSED_LEAN_PENDING","group":group,
            "ranks":{k:rank(t) for k,t in tables.items()},"recipe":recipe,"rank":rank(v),
            "old_max_singular_rank":bound,"behavior_sha256":evo.fingerprint(v),
            "full_monoid_order":str(N**N),"full_monoid_log2_order":2048,
            "scope":"group and monoid conclusions use classical theorems; only rank separation is submitted to Lean"}
    fb.write(a.output/"report.json",report)
    if a.kernel:
        kernel_seeds=evo.seed_replay(a.output/"seeds")
        require(kernel_seeds==seeds,"kernel seed mismatch")
        kernel_history=evo.replay(state,semantic,seeds,a.output/"history")
        require(kernel_history==accepted,"kernel history mismatch")
        evo.check_lean(a.output/"new")
        report["status"]="KERNEL_AND_AXIOM_AUDIT_PASSED_RANK_EXTENSION"
        fb.write(a.output/"report.json",report)
    print(json.dumps(report,sort_keys=True))

if __name__=="__main__":
    main()
