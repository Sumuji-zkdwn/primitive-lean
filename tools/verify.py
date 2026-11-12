"""Verify retained proof groups and additive compositions through one entry point.

Usage: python -X utf8 tools/verify.py [--rebuild] [--lean-only | --proof-only]
--rebuild removes only lean/.lake/build; pinned dependency caches are retained.
--proof-only checks fresh proofs without requiring the separate historical archive audit.
--lean-only runs the unchanged joint checker, then audits all registered
supplements together with all original declarations.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re, shutil, subprocess, sys, time, zipfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
OUT = ROOT / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

def strip_comments_strings(source):
    """Keep source line offsets while excluding nested comments and strings."""
    result=[]; i=0; depth=0; string=False
    while i<len(source):
        c=source[i]; pair=source[i:i+2]
        if depth:
            if pair=='/-':depth+=1;result.extend('  ');i+=2;continue
            if pair=='-/':depth-=1;result.extend('  ');i+=2;continue
            result.append('\n' if c=='\n' else ' ');i+=1;continue
        if string:
            if c=='\\':result.extend('  ');i+=2;continue
            if c=='"':string=False
            result.append('\n' if c=='\n' else ' ');i+=1;continue
        if pair=='/-':depth=1;result.extend('  ');i+=2;continue
        if pair=='--':
            end=source.find('\n',i);end=len(source) if end<0 else end
            result.extend(' '*(end-i));i=end;continue
        if c=='"':string=True;result.append(' ');i+=1;continue
        result.append(c);i+=1
    return ''.join(result)

def command(args, name, cwd=ROOT):
    started=time.monotonic()
    proc=subprocess.run(args,cwd=cwd,text=True,encoding="utf-8",errors="replace",capture_output=True)
    output=proc.stdout+proc.stderr
    (OUT/(name+".log")).write_text(output,encoding="utf-8")
    warnings=[line for line in output.splitlines() if re.search(r"\bwarning:",line)]
    return dict(command=args,working_directory=str(cwd),exit_code=proc.returncode,
                seconds=round(time.monotonic()-started,3),log="verification/"+name+".log",
                warnings=warnings)

def canonical_path(relative):
    return (ROOT / "linear_input" / relative).resolve().relative_to(ROOT).as_posix()


def verify_lean(rebuild):
    if rebuild:
        target = (LEAN / ".lake/build").resolve()
        if target != LEAN.resolve() / ".lake/build":
            raise RuntimeError("Unsafe project build path")
        if target.exists():
            shutil.rmtree(target)
    # The proof files and their existing checker retain their separate roles.
    run = command([sys.executable, "-X", "utf8", "linear_input/verify_lean.py"], "joint-lean-run")
    current = json.loads((ROOT / "linear_input/lean_results.json").read_text("utf-8"))
    original_declarations = [{**d, "file": canonical_path(d["file"])}
                    for d in current["parent_declarations"] + current["declarations"]]
    before = json.loads((OUT / "before-unification.json").read_text("utf-8"))
    archive_path = ROOT / before["archive"]
    assert sha(archive_path) == before["archive_sha256"]
    with zipfile.ZipFile(archive_path) as archive:
        old = json.loads(archive.read("linear_input/lean_results.json"))
        old_names = {d["name"]: d["kind"] for d in old["parent_declarations"] + old["declarations"]}
        new_names = {d["name"]: d["kind"] for d in original_declarations}
        proof_files = sorted(set(d["file"] for d in original_declarations))
        unchanged = [rel for rel in proof_files if (ROOT / rel).read_bytes() == archive.read(rel)]
    preservation = dict(passed=len(unchanged) == len(proof_files) and old_names == new_names,
        proof_files=len(proof_files), byte_identical_proof_files=len(unchanged),
        same_public_names_and_kinds=old_names == new_names,
        missing=sorted(old_names.keys() - new_names.keys()), added=sorted(new_names.keys() - old_names.keys()),
        archive=before["archive"])
    warnings = []
    for rel in (current["compile"]["log"], current["parent_library_build"]["log"]):
        warnings += [line for line in (ROOT / "linear_input" / rel).read_text("utf-8").splitlines()
                     if re.search(r"\bwarning:", line)]
    supplement_run = command([sys.executable, "-X", "utf8", "tools/verify_main_result.py"], "main-result-run")
    supplement_path = OUT / "main-result.json"
    supplement = json.loads(supplement_path.read_text("utf-8"))
    declarations = original_declarations + supplement["declarations"]
    axioms = supplement["axioms"]
    hashes = {canonical_path(rel): digest for rel, digest in current["source_sha256"].items()}
    hashes.update(supplement["source_hashes"])
    hashes["tools/verify.py"] = sha(Path(__file__))
    hashes["verification/main-result.json"] = sha(supplement_path)
    warnings += supplement["warnings"]
    changed = [rel for rel, digest in hashes.items() if not (ROOT / rel).is_file() or sha(ROOT / rel) != digest]
    passed = (run["exit_code"] == 0 and current["passed"] and preservation["passed"]
              and supplement_run["exit_code"] == 0 and supplement["passed"]
              and supplement["all_declarations"] == declarations
              and len(axioms) == len(declarations) and not warnings and not changed)
    supplemental_scopes = {
        'MainResult': 'Additive connection and worked example',
        'GeneralMinimum': 'General fixed-input minimum and strict-support criteria, with quartic bridges',
        'SupportComposition': 'Support interpolation, ordering, derivative identification and shared-minimizer restrictions',
        'QuarticClassification': 'Exact quartic minimum uniqueness and supporting-input classification',
        'CurvatureRigidity': 'Conserved phase energy and the transverse square force constant curvature at a phase minimum',
        'HistorySignature': 'Actual primitive coordinates, second iterated integrals, area composition and explicit observation hierarchy',
        'CurveWordAlgebra': 'Lifted-angle curve-word composition, contextual observation, signed-area cocycle and quadratic-cost similarity; an algebraic auxiliary model',
        'CurveWordFinite': 'Kernel-checked integer quarter-turn words, first- and second-level collisions and balanced-word cardinalities; no analytic arc integral identification',
        'CurveWordArc': 'Actual circular-arc coordinate and bending-energy integrals, unit speed, normalized A/B letters and geometric similarity',
        'CurveWordFiniteState': 'Bellman recursion equals the fixed-length global word minimum; exact four-state lattice-objective bridge and periodic cycle candidates',
        'CurveWordCycleLimit': 'Four-state optimal average-cost limit from explicit potentials and attaining policies; no assumed cycle-mean limit',
        'CurveWordRealization': 'All-word agreement between products of integrated arc states and the lifted integer model, with physical energy normalization',
        'CurveWordThermodynamics': 'Finite-family log-sum-exp bounds and zero-temperature convergence, energy/input/temperature similarity and equal-cost multiplicity',
        'CurveWordSignature': 'Actual iterated interval integrals at arbitrary finite degree, homogeneous scaling, degree-two Chen identity and the cubic moment bridge',
        'CurveWordCircularMoment': 'Actual circular line integrals and the cubic moment difference for explicit inserted circular loops; separate from Boolean-word curve realization',
        'CurveWordPiecewise': 'A single C1 unit-speed curve for every Boolean word, with actual cost, endpoint and area integrals equal to the integer-state decoding',
        'CurveWordCircleWords': 'Pointwise identification of the Boolean eight-letter curves with the explicit circle pieces, actual equal areas and distinct cubic moments',
        'CurveWordGraphLimit': 'Finite labelled directed graphs: short-cycle extraction, existence of a minimizing simple cycle, and the fixed-start average-cost limit under reachability',
        'CurveWordDirectedGraph': 'State-dependent finite outgoing edge types with no dead ends, exact walk-policy encoding, attained minimum closed-walk mean and reachable fixed-start optimum limit',
        'CurveWordLaplace': 'Uniqueness of finite measures from Laplace data with exponential integrability, and the actual weighted endpoint-measure interpretation of partition functions',
        'CurveWordSpectral': 'Nonnegative irreducible matrix row-sum logarithmic growth equals the logarithm of the usual complex spectral radius, including periodic matrices',
        'CurveWordTransfer': 'All-word partition sums equal transfer-matrix row sums; spectral free energy and its zero-temperature minimum-cycle-mean limit',
        'CurveWordChen': 'All-degree Chen and shuffle identities proved from actual iterated integrals for continuous velocities',
        'CurveWordFormalSeries': 'Completed coefficient series with cut convolution, finite-coefficient exponential, a constructed two-sided inverse logarithm and all-degree associative BCH laws',
        'CurveWordCoproduct': 'Unshuffle coproduct compatibility, primitive exponentials and group-like logarithms in completed coefficient series',
        'CurveWordFriedrichs': 'Dynkin identities and explicit homogeneous free-Lie witnesses for every primitive series over a finite alphabet',
        'CurveWordTreeLike': 'Independent geometric height definition, uniform-limit and Lipschitz-map closure, and the scalar C1 signature equivalence; not general Hambly-Lyons',
        'CurveWordSignatureTopology': 'Compact signature range, Stone-Weierstrass density of word coordinates and vanishing continuous-coefficient line integrals for a trivial C1 signature',
        'CurveWordReparametrization': 'All-degree actual C1 time-change, reversal and closed-time-excursion signature identities with the derivative Jacobian',
        'CurveWordBoundedVariation': 'Continuous metric-valued BV curves factor through a continuous monotone variation clock and a length-preserving 1-Lipschitz path',
        'CurveWordStieltjes': 'Actual Stieltjes measures for continuous BV Jordan pairs, compact-interval extension and all-degree agreement with continuous-velocity iterated integrals',
        'CurveWordBVSignature': 'Continuity and Jordan-decomposition independence of all-degree iterated Stieltjes signatures, derived from equality of signed coordinate increments',
        'CurveWordBVReparam': 'All-degree Stieltjes signature invariance under continuous monotone time changes, including flat fibers and explicit compact-interval extension',
        'CurveWordBVChen': 'All-degree Chen identity for continuous Stieltjes coordinate pairs representing continuous BV paths',
        'CurveWordBVShuffle': 'Atom-free measure integration by parts from Fubini triangle decomposition, and the all-degree continuous BV signature shuffle identity',
        'CurveWordSignatureTree': 'The metric four-point condition implies a geometric tree-height witness for every continuous loop and its Lipschitz images; no four-point metric on the signature range is assumed to exist',
        'CurveWordHeightMetric': 'A geometric height witness constructs an actual compact path-connected four-point metric quotient, a continuous surjective loop and a 1-Lipschitz factor recovering the curve',
        'CurveWordScalarLog': 'The standard scalar formal power-series logarithm and exponential are actual compositional inverses',
        'CurveWordLogFormula': 'The ordinary alternating-power formal logarithm equals the constructed inverse in every degree, with primitive, free-Lie and BCH corollaries',
        'CurveWordBVTopology': 'Compact BV signature range, density of word coordinates and vanishing of genuine continuous-coefficient Stieltjes one-forms for trivial total signature',
        'CurveWordBVAlgebra': 'All-degree group-like, primitive logarithm, actual homogeneous free-Lie expansion and BCH laws for continuous BV Stieltjes signatures',
        'CurveWordConvexObservation': 'Attained finite equal-cost minima depend only on the actual convex hull of endpoints, through its linear support function',
        'CurveWordSignatureBounds': 'Factorial bounds for actual BV signatures, finite coordinate variation controls and coefficient continuity under variation convergence',
        'CurveWordSignatureUniform': 'Uniform convergence and uniformly bounded coordinate variation imply convergence of every actual Stieltjes signature coefficient',
        'CurveWordConvexSeparation': 'All continuous linear equal-cost observations determine exactly the convex hull of a finite endpoint set via strict Hahn-Banach separation',
        'CurveWordLinearAction': 'Actual degreewise tensor powers of arbitrary finite coordinate matrices, including planar rotations, commute with all iterated-integral signature coefficients',
        'CurveWordBVCanonical': 'Compact-interval BV curve signatures independent of local Jordan representations and extension choices, preserving continuous monotone reparametrization and arc-length factorization',
        'CurveWordWordSignature': 'All-degree rotated Chen identity on the actual single tangent-angle curve constructed from every Boolean word',
        'CurveWordGenerating': 'Actual matrix-power formal series satisfy the resolvent equation and explicit polynomial rationality certificates over commutative rings',
        'CurveWordWordGenerating': 'Genuine finite weighted-word sums equal transfer-matrix power row sums and have a rational formal generating function',
        'CurveWordSamplingOrder': 'Finite consecutive sampling laws survive interval gluing and admit an exact strictly increasing finite enumeration with mesh control',
        'CurveWordTreeSignature': 'Actual straight-segment signatures cancel on all closed walks in acyclic graphs, including stuttering vertex sequences',
        'CurveWordPolygonal': 'Actual polygonal interpolation preserves variation bounds, has the product of segment signatures, and converges uniformly and in every signature coefficient as the mesh shrinks',
        'CurveWordBVSubinterval': 'Actual BV signature lifts cannot be nonconstant simple loops; every trivial-signature BV curve has a proper trivial-signature subinterval via continuous time forms',
        'CurveWordTreeSampling': 'Actual first/last-hit finite height samples with arbitrarily small time mesh and their edges in an acyclic graph on the height metric quotient',
        'CurveWordTreeSampleProduct': 'Every independent tree-height witness constructs arbitrarily fine time samples whose actual straight-segment signature product is the unit series',
        'CurveWordTreeLimit': 'Every finite-dimensional continuous BV tree-like path has trivial canonical all-degree Stieltjes signature, by constructed sampling, cancellation and the verified uniform BV limit',
        'CurveWordArcGenerating': 'The four-state Laurent-weight transfer matrix counts exactly the integer endpoint and bending-cost multiplicities of every word length and gives their rational generating function',
        'CurveWordBVPathOperations': 'Actual continuous BV path reversal and joining, all-degree canonical Chen and inverse identities, and signature equality reduced to a closed joined path',
        'CurveWordBVCompactness': 'Actual compact speed-controlled path classes, lower semicontinuous variation, continuous signatures and attained least variation in closed based-signature-range classes',
        'CurveWordBVLoopErase': 'Actual zero-signature loop deletion preserving every remaining based prefix while strictly reducing variation for a nonconstant deleted loop',
        'CurveWordBVReduced': 'Constructed least-variation signature representatives are constant on every equal-prefix-signature interval',
        'CurveWordBVArc': 'Actual arc-length reparametrization preserves all based prefix signatures and produces injective signature lifts inside any closed range with an actual candidate',
        'CurveWordBVOrientation': 'Canonical Stieltjes signature transport under actual continuous monotone or antitone clocks, including arbitrary oriented subintervals',
        'CurveWordGeodesicTree': 'Actual isometric geodesics whose triangles are covered by the other two sides satisfy the standard metric four-point condition',
        'CurveWordBVArcUnique': 'Two actual simple based signature lifts with the same endpoints have the same image, proved by attained excursions, actual joined BV curves and exclusion of simple signature loops',
        'CurveWordBVIntrinsic': 'The infimum of actual bounded-speed route durations is attained, gives a genuine metric on reachable signatures, and admits actual isometric shortest-curve geodesics',
        'CurveWordBVIntrinsicTree': 'Actual route minimization and simple-lift uniqueness give thin triangles and the standard four-point condition for the constructed intrinsic signature metric',
        'CurveWordBVHamblyLyons': 'The actual canonical signature of a continuous BV path is trivial exactly when the path admits an independent geometric tree-height witness, via the constructed intrinsic metric and variation-clock pullback',
        'CurveWordBVEquivalence': 'Equality of all canonical Stieltjes signature coefficients is equivalent to geometric tree-likeness of the actual forward/reverse joined BV path, with endpoint conditions explicit',
        'CurveWordBVCoordinates': 'Operator-norm height transport and actual finite normed coordinates extend trivial-signature equivalence to every finite-dimensional real normed space and prove coordinate independence of triviality',
        'BranchForgetting': 'Chebyshev normalization of the actual stationary input and an explicit minimum-only forgetting criterion',
        'VariablePairObservations': 'Actual partial derivatives, explicit inverses, sign changes and transport of observation hierarchies in the primitive energy family',
        'BranchFibers': 'Cosine candidate equality, explicit critical fibers and retractions, and exhaustive counts of the real inverse images of the ternary iterate',
        'F0Retractions': 'Idempotent retractions, K-S-C composition, compatible-map counting by an explicit equivalence, finite orbit bounds, and bridges to the critical branch representatives',
        'F0Counting': 'Actual labelled idempotent maps counted by fixed-point rank, with exact seven- and eight-point totals',
        'F0MergeChains': 'Positive integer-partition merge chains and an explicit Fin 5 fiber-mass chain realized by sequential idempotent K-S-C steps, with mass preservation, strict rank decrease, acyclicity and exact-length paths to the singleton',
        'FiniteBayes': 'Finite normalization and posterior composition, support constraints, log-loss comparison, observation pushforwards, and actual Elastica exponential-weight bridges',
        'FourBayes': 'Exploration mixtures, calibrated disappointment, binary log-partition derivatives, cancellation of opposite tilts, and exact deletion and predictive-forgetting counterexamples',
        'GaloisChebyshev': 'Elementary Joukowski/Chebyshev collision identity, cyclotomic and Kummer root labels, modular reflections and existing critical-fiber kernels (not a full Galois group identification)',
        'KummerDihedral': 'Actual splitting and adjoining-root fields, cyclic Kummer Galois group equivalence, Galois degree, and dihedral group action on root labels (not yet a dihedral field-Galois identification)',
        'ChebyshevDihedralDescent': 'All ternary Chebyshev iterates, genuine polynomial root identities and reconstruction of a multiplicative radical from two candidates; not yet a full dihedral Galois equivalence',
        'ChebyshevRatFuncDegrees': 'Exact degrees of all cubic Chebyshev iterates and nonconstancy of the square of the generic rational-function coordinate',
        'ChebyshevDegreeTower': 'Exact Bezout coprimality, reduced rational-function numerator and denominator, degree 2m of the generic quotient and half-normalized Joukowski parameter',
        'ChebyshevSplittingField': 'The generic Chebyshev polynomial over C(t) has C(X) as its actual splitting field, using distinct roots and radical reconstruction',
        'ChebyshevGaloisAutomorphisms': 'Base-field rotation and inversion automorphisms for the ternary Chebyshev model, the dihedral relations, and an injective representation; not yet a full Galois group equivalence',
        'ChebyshevGaloisCompletion': 'Surjectivity via the degree and algebra-hom cardinal bound; full dihedral Galois group equivalence over C(t) for generic ternary Chebyshev splitting fields, k ≥ 1',
        'VariablePairGaloisBridge': 'Actual variable-pair stationary reduction to a cubic, Hessian-discriminant degeneracies, Chebyshev normalization, and the eight sign classes under coordinate reflections',
        'FoldCount': 'Normalized cusp fold root counting, stationary sign types, ordinary discriminant, and triple-root cusp tip',
        'FoldCountOriginal': 'Original-variable cusp/fold classification for every positive leading coefficient, including all discriminant regimes and explicit Hessian signs',
        'F16Holonomy': 'Finite Cayley-Dickson epsilon table, 128 signed observation squares, F0 idempotent forgetting and right-probe descent classification',
        'F16RecoverySpectrum': 'Constructive recovery of the forgotten bit by an obstructed probe, explicit signed 2x2 pencil factors, and four null vectors at each singular input',
        'F16RankCertificate': 'Exact integer factor and 12-by-12 pivot certificates imply real Matrix.rank 12 at t = +1 and -1',
        'F16RealDeterminant': 'Eight 2-by-2 sedenion left-pencil blocks, verified row/column bijections and parity, and the full real Matrix.det identity',
        'F16CompleteRank': 'Exact real-pencil comparison at integer parameters, determinant-zero characterization, and complete rank-12/rank-16 classification',
        'F16UnexpectedBridges': 'Exact signed F16 block normal forms, D4 reflection-rotation relations, cubic discriminant degeneracy, and two singular probes jointly identifying the full state',
        'ShearCommutator': 'Actual energy partial derivatives generate horizontal and vertical shears through coordinate exchange; inverse-order cancellation, unit-determinant hyperbolic commutator, and a certified exponential lower bound',
        'ComplementaryPencilRecovery': 'Constructive inverse for opposite matrix-pencil observations, compatible-data equivalence, uniqueness, and exact kernel criteria',
        'F16ConstructiveRecovery': 'General inverse theorem instantiated with the original rank-12 F16 real matrices and exact reconstruction of both observations',
        'ComplementaryObservationExamples': 'Counterexamples at missing assumptions and an independent PR19 four-phase coordinate observation model',
        'StrangeOperatorGalois': 'F0-derived self-stopping, fiber obstruction and relational Galois closure',
        'StrangeOperatorConjugacy': 'Naturality, one-point F0 closure classification and conjugacy orbit',
        'StrangeOperatorBoundary': 'Finite non-idempotent obstruction to extending the spike-orbit theorem to arbitrary F0 maps',
        'StrangeOperatorFixedSets': 'Complete singleton Galois closure classification by fixed-point sets',
        'StrangeOperatorCounting': 'Exact finite fixed-set map and idempotent counts, connected to Stops closure with explicit empty and full fixed-set boundaries',
        'F16SaddleCantor': 'F16 reflection-derived hyperbolic saddle, finite two-branch ternary coding and the F0 two-cycle obstruction; no infinite fractal/dimension theorem.',
        'F16FullMatrix': 'Actual real 16-by-16 sedenion left-pencil matrix, explicit eight-block row/column permutation equivalence, full determinant and real singularity classification',
        'F16FullRank': 'Invertible 2-by-2 Gaussian elimination, global diagonalization and rank 12 exactly at t=±1 (rank 16 otherwise)',
        'F0UpdateDescent': 'Induced dynamics on F0 fixed representatives, descent iff fiber respect, composition, symmetry preservation and a finite counterexample',
        'Rule481Symmetry': 'Local Rule 481 reflection/complement and finite 3x3 torus mirror equivariance and two-cycle (not infinite-lattice OEIS coefficient proof)',
        'HannaJetCorrection': 'First-jet formal-series calculation: the k=3 denominator correction changes the local x^7 coefficient by eight (not the whole generating function)',
        'FutureObservations': 'Future observation equivalence, induced deterministic quotient state, universal minimal predictive kernel, and observation-invisible symmetries',
        'FutureFiniteHorizon': 'Finite observation signatures, monotone trace rank, and stabilization after at most N-r refinement steps',
        'OperatorWordObservations': 'Operator-word observational equivalence, canonical quotient states, compilation without new distinctions, and an independent-action counterexample',
        'MonoEyeComposition': 'Open-eye product quotient commutation, observable-boundary feedback soundness and a finite inaccessible-input obstruction',
        'OperatorBisimulation': 'Greatest observational bisimulation, closure operations, representation fibers and invisible symmetries',
        'OperatorVocabularyRefinement': 'Conservative extension criterion, strict new-action witnesses, quotient surjection and quotient splits',
        'OperatorFiniteHorizon': 'Finite-state multi-action trace profiles, plateau test, N-r bound and short separating words',
        'OperatorSemanticClosure': 'Semantically compatible operators, induced quotient endomorphisms, functoriality, and a conservative nonword-generatable finite witness',
        'CrossSystemObservation': 'Cross-system bisimulation, trace preservation, predictive-quotient transport, and a precise finite forgetting obstruction',
        'SemanticIntervalNecessity': 'Finite prefix-time survival of local systems, old invariant extinction barrier, fresh-operation necessity, finite strict-quotient example and one-local extinction counterexample',
        'FiniteSelfSynthesis': 'Executable finite local repair search, complete bounded-catalog oracle, nonword-generable interval restoration, and Fin 3 instantiated repair/refinement',
        'RecursiveOperatorReentry': 'Finite child-generated novel operator catalogue, fresh patch construction, sound and complete bounded frontier, reentry monotonicity, conditional local viability, three-round saturation example',
        'RuleSelfModification': 'Mutable internal rule-edge table, bounded generation meta-compiler, reactivation requiring an actual rule edit, finite startup and saturation, conditional interval survival bridge',
        'MetaRuleSelfExtension': 'Mutable second-order meta-rule catalogue, fixed higher-order lift, soundness and preservation, controlled divergent future object-level rules with identical lower-level state, finite saturation and interval viability bridge',
        'HigherOrderLiftSelfRewriting': 'State-resident lift program updated by learned operators, exact lower-level trace reproduction, finite observation classes and saturation',
        'EWFSFenchel': 'Verified reversible E polynomial, x-only forgetting obstruction, positive-intensity WFS gauge and physical-versus-changed Fenchel pairing',
        'WFSCanonicalLift': 'Positive-intensity WFS p=2 cotangent lift and p=0 momentum identity under explicit domain conditions',
        'EWFSFutureBridge': 'Coordinate-conjugate future equivalence, E x-trace full-state reconstruction, WFS2 exp observation invariance and radial rotation quotient',
        'TemporalSampling': 'General observation schedules, exact stride-sampling iff one-step congruence, phase reconstruction, and E-rotation even-time aliasing with positive WFS gauge',
        'WFSMobiusFourier': 'WFS p=2 positive-intensity Möbius involution induced by two E rotation steps and exact four-phase first Fourier coefficient with even-sample aliasing',
        'EnergyWfsFenchel': 'Exact E-gradient/Fenchel pairing transport, p=0/p=2 WFS gauges, all-u probe obstruction for F0 retractions and double-well minorants',
        'ObservationRetractionPolarity': 'Exact decode/re-observe retraction on data, compatible fixed points, Stops semantics, and singleton closure with explicit properness hypotheses.',
        'F0FutureMinimality': 'F0 descent iff the current observation kernel equals complete future equivalence, plus the concrete one-step counterexample.',
        'WFSProjectiveSampling': 'Projective conjugacy, gcd sampling kernel and cyclic phase pseudometric; adapted original PR21 with repaired proof and unchanged assumptions.',
        'RepresentationBridges': 'Exact identities of retained F16 matrix representations and energy maps, with transfer of actual complementary reconstruction.',
        'HistoryNonpreservation': 'Historical preservation as a falsifiable property, missing observation and transition obstructions, impossibility of internal repair with fixed readout, global growth counterexamples, and tagged-state extension',
        'TemporalLocalExtinction': 'Time-and-state-dependent partial local availability, extinction-induced historical obstruction, exact if-and-only-if preservation boundary, interval failure, local replacement and domain reactivation counterexamples',
        'LocalCapacityIncompatibility': 'Finite local capacity versus global all-requirements demand, derived total extinction and historical nonpreservation, pairwise-compatible non-gluing triple and finite noncommutativity countermodel',
        'CooperativeGluingObstruction': 'Collective requirement reachability without joint sequential goal, destructive-operation invariant, cooperative versus noninterfering countermodels, joint-postcondition gated extinction and history nonpreservation',
        'RelationalOddCycleGluing': 'Strict hierarchy of individual, pairwise and global relational feasibility, Boolean odd-cycle obstruction, even-cycle control; pairwise SAT is not overlap agreement of fixed assignments',
        'JoinContextualEquivalence': 'Contextual equality under rewrites and binary attachment, compositional quotient, representation minimality, exact descent of old quotient attachment, and finite counterexample',
        'CurveLetterContextualEquivalence': 'Exact normalized A/B curve-letter composition, observational collision, left-context separation, and specialization of the attachment-descent criterion',
        'RadicalF0Bridge': 'Arithmetic radical as multiplicity-forgetting F0, exact prime-support kernel, squarefree fixed points, and successor failure of descent and predictive sufficiency',
        'PilotComparisonBridge': 'Choice-dependent reconstruction range cover, quotient factorization boundary, exact log-volume witness iff numerical cap, independent finite and ell=7 countermodels; not an IUT proof.',
        'PilotVolumeTransport': 'Exact choice-dependent log-volume shift criterion, neutral/limited-shift obstruction, and conditional local packet budget certificate; not an arithmetic IUT proof.',
        'PilotHullInflation': 'Volume-preserving coordinate swap with strictly larger hull of its orbit; abstract finite countermodel, not an IUT Ind2 calculation.',
        'PilotHullStability': 'Exact no-hull-inflation iff every image stays within the original closure, with identity choice, volume monotonicity and escape obstruction.',
        'ElasticaOperatorBridge': 'Constant-angle Elastica xCoord reconstruction applied to strict operator-quotient splitting (four directed straight segments).',
        'ObservableRigidPoint': 'Conditional common observable fixed point of projected idempotents, F0 range derivation, four-state hidden-order counterexample and disjoint-idempotent obstruction',
        'RimObservability': 'Exact one-channel four-phase decoder for a 4D rotation/reflection model, optimal three-versus-four horizon witness and signed 2x2 local gauges; no global F16 conjugacy claim.',
        'ViscousRewrite': 'Proximal parameter-shift closure for the original E polynomial, minimizer-derived viscous balance, energy descent, Fenchel-Young identities, a nonconvex two-branch example, and an F16 rotation/reflection dissipation test.',
        'GravityCocycle': 'Generic pair-interaction two-cocycle, exact coboundary of symmetric internal energy, Newton inverse-distance kernel, and oriented 1D inverse-square force; does not deduce Newton law from associativity.',
        'GravityObserver': 'F0 reflection quotient and mass-only counterexample for symmetric two-mass gravitational observation; exact probe kernel, injectivity, and quadrupole/remainder identities.',
        'GravityObservation': 'Idempotent F0 observational descent iff fiber invariance; exact three-moment exterior inverse-distance expansion with finite remainder; symmetric-pair quadrupole witness and failure of mass-only reduction.',
        'TernaryZeroCesaro': 'Zero insertion into ternary blocks, six-step Cesaro values, preserved nonzero sums, and exact dwell-time weighted sums.',
        'FiniteObservationSeparation': 'Probe refinement criteria, finite F0-style idempotent recovery, minimal permitted probe pair, six-state coordinates, and time-sensitive ternary observables.',
        'DecompositionIdentification': 'Terminating rewrite paths, uniqueness and common-ancestor criteria, terminal probe identification, monotone finite probe libraries, and commutative generator collisions.',
        'DecompositionF0Bridge': 'Actual positive F0 multiset merges as decreasing evaluation-preserving rewrites with a unique singleton terminal form.',
        'PrimeFactorIdentification': 'Mathlib positive integer factor-multiset equivalence, canonical prime product injectivity, zero extra probes, and contrast with composite generator collisions.',
        'PrimeSplitNormalForm': 'Actual nonunit factor splitting, product invariance, terminal-prime equivalence, exact step count, and terminal uniqueness with zero extra probes.',
        'AssociatesFactorIdentification': 'UFM atomic-factor uniqueness modulo units, explicit existence and cancellation converse, finite probe monotonicity and zero probes, and rewrite path invariance.',
        'GeneratedNonUniqueMonoid': 'Actual multiplicative submonoid generated by 4,6,9 with three relative atoms, two distinct atomic factorizations of 36, and failure of Euclid primality.',
        'HalfFactorialIdentification': 'Exponents at 2 and 3 of 4^r6^s9^t; half-factorial length across all generator words; one-count probe reconstructs every generator word; concrete G coverage.',
        'AtomicGeneratorClassification': 'Every atom in the actual 4-6-9 submonoid is one of 4, 6, 9; closure induction over arbitrary generator products.',
        'AtomicHalfFactorial': 'For every actual atomic multiset the sum of 2- and 3-valuations is twice its length, implying full half-factoriality of the generated submonoid.',
        'AtomicWordProbe': 'All actual atomic multisets admit explicit multiplicity triples; product plus count of factor 6 identifies any atomic decomposition, while product alone is insufficient.',
        'SingleSwapFiber': 'Complete rank-one collision lattice and oriented 4*9-to-6*6 swap; every equal-product pair is connected by finite swaps, with termination and unique oriented endpoint.',
        'F16RimRecovery': 'Lean-identifies the actual F16 relative action A^T C, proves a full 16D four-phase decoder, and exhibits collisions for one, two, and three phases.',
        'ParallelLocalGluing': 'Pairwise overlap agreement iff global gluing, canonical unique global state under coverage, exact global policy and operational reachability factorization, three independent finite failure modes',
        'OperatorContextualEquivalence': 'Contextual two-sided congruence of operator programs and predictive quotient replacement',
        'OperatorAdaptivePolicies': 'Quotient-safe feedback policies, adaptive iteration, and unsafe feedback counterexample',
        'OperatorProductSystems': 'Independent product systems, interleaved actions and observational product kernels',
        'OperatorReachability': 'Reachability closure, invariant predicates, and generated-language reachability preservation',
        'OperatorSensorFamilies': 'Arbitrary sensor bundles, kernel intersections, and joint separation',
        'OperatorF0SemanticBridge': 'Exact semantic-compatibility and F0-descent correspondence under fiber-respecting updates',
        'OperatorSemanticMonoid': 'Faithful semantic operator monoid, quotient congruence and constructive full transformation monoid on predictive states',
        'OperatorFiniteMapCounts': 'Finite three-state compatible-map cardinalities and non-generatable constant witness',
        'GravityObservations': 'Exact F0 observational descent and injectivity obstruction; monopole/dipole invariance, lost quadratic moment and exact exterior inverse-distance correction for symmetric two-body configurations.',
        'FiveDimLagrange': 'Five-coordinate constrained-energy lift, regular one-constraint multiplier existence from Elastica kernel annihilators, confirmed-observation Jacobian rank drop, and explicit original-E stationary input.',
        'ParallelWriteGluing': 'Finite-family partial-state update amalgamation iff overlap compatibility, constructive first-write gluing and written-coordinate uniqueness, conflicting/disjoint concurrent writes, explicit history gate and conditional nonpreservation (PR #71, renamed so it coexists with the different ParallelLocalGluing proof of PR #70)',
        'PrimeFactorObservation': 'Finite prime-factor observation kernels and the minimal probe count for 2, 3 and 5 (PR #50).',
        'PrimeFactorOrbits': 'Prime-factor orbit kernels (S2/S3) and exact three-factor observation counts (PR #51).',
        'PrimeFactorF0Adaptive': 'F0 sorting retraction, product-kernel quotient and adaptive observation lower bound (PR #52).',
        'PrimeFactorFiniteLength': 'General finite-length prime-factor observation minimum and unordered-state count (PR #53).',
        'PrimeFactorGeneralF0': 'Canonical F0 sorting for arbitrary finite prime lists and exact product kernels (PR #54).',
        'AutonomyCycle00001': 'Autonomously enumerated finite operator separation and strictly refined predictive quotient; five explicit Lean theorems',
        'AutonomyCycle00002': 'Autonomously enumerated finite operator separation and strictly refined predictive quotient; five explicit Lean theorems',
        'AutonomyCycle00003': 'Autonomously enumerated finite operator separation and strictly refined predictive quotient; five explicit Lean theorems',
        'AstraRiccati': 'Exact Riccati clock and derivative identities; branch and pole conditions remain explicit',
        'AstraFiniteEnergy': 'Pointwise and finite dimensional energy identities under explicitly given evolution equations',
        'AstraReconstruction': 'Fixed-energy smooth periodic family obstructs uniformly bounded encoding with continuous linear point reconstruction',
        'AstraKoopmanDescent': 'Koopman eigenfunction pullback under an explicit update intertwining hypothesis',
        'AstraConstitutive': 'Quartic constitutive law and scalar inverse bounds connected to the existing primitive potential',
        'AstraObservation': 'Two-input probe recovery, semiconjugate eigenfunction pullback, and observation obstruction',
        'AstraDynamicsBoundary': 'Static potential and critical points do not determine an evolution law',
        'AstraExplicitMaterial': 'Explicit nonlinear scalar constitutive inverse using hyperbolic functions',
        'AstraRelativeEnergy': 'Pointwise relative energy identities and bounds for the chosen constitutive law',
        'AstraExactShear': 'Exact finite dimensional split shear steps, reversibility, and preserved components',
        'AstraHilbertShear': 'Hilbert norm estimates for split shears and globally Lipschitz nonlinear vector fields',
        'AstraHilbertFlow': 'Global existence, uniqueness, flow composition and growth for globally Lipschitz fields on a complete space',
        'AstraHilbertError': 'Local second order Lie split-step error relative to the exact Lipschitz flow',
        'AstraIterationBound': 'Explicit recurrence and finite time inverse-step-count error bounds',
        'AstraHilbertIteration': 'Convergence of actual split iterates to the exact flow with an explicit O(1/n) bound',
        'AstraFiniteFlow': 'Actual finite matrix Maxwell flow with the scalar material inverse: global existence and uniqueness, old ExactShear identification, O(1/n) split convergence, physical reconstruction and skew-matrix energy conservation',
        'AstraFourierProjection': 'Actual normalized-circle Fourier orthogonal projections and strong L2 convergence',
        'AstraMaterialL2': 'Actual nonlinear scalar material inverse lifted to a Lipschitz L2 map',
        'AstraRealGalerkin': 'Real finite Fourier subspaces and actual orthogonal projection operators',
        'AstraFourierDerivative': 'Actual finite Fourier derivative operator and its skew-adjoint identity',
        'AstraRealFourierDerivative': 'Real Fourier differentiation, scalar compatibility and skew identities',
        'AstraFiniteRepresentatives': 'Continuous finite Fourier representatives of L2 states and finite dimensionality',
        'AstraFourierSupBounds': 'Explicit finite Fourier sup bounds with their cutoff dependence retained',
        'AstraFiniteRepresentativeCalculus': 'Spatial calculus of actual finite Fourier representatives',
        'AstraRelativeDynamics': 'Relative-energy evolution and residual identities for actual finite nonlinear dynamics',
        'AstraContinuumCalculus': 'Periodic continuum integration and differentiation identities under explicit regularity',
        'AstraIntervalFourier': 'Periodic interval Fourier functions and their normalized integral identities',
        'AstraContinuumRelative': 'Classical periodic Kerr-pair relative-energy calculus with explicit PDE hypotheses',
        'AstraIntegralTail': 'Integrated projection-tail inequalities for relative-energy estimates',
        'AstraContinuumGalerkin': 'Continuum relative-energy estimates for actual projected classical fields',
        'AstraIntervalFourierProjection': 'Finite interval Fourier projection and its integral identities',
        'AstraCircleProjection': 'Agreement between actual circle and interval Fourier projections',
        'AstraGalerkinFlow': 'Actual finite Fourier Galerkin flow, split step and decoded fields',
        'AstraGalerkinClassical': 'Classical representatives and equations for the actual finite Galerkin flow',
        'AstraContinuumFourier': 'Continuum Fourier projection identities for classical periodic fields',
        'AstraGalerkinRelative': 'Relative-energy comparison of actual Galerkin and classical continuum fields',
        'AstraGalerkinRestoration': 'Physical-field restoration from actual Galerkin states',
        'AstraInitialRelativeEnergy': 'Initial relative-energy estimates from projected initial fields',
        'AstraStoppingCertificate': 'Explicit stopping argument for bounded continuous scalar errors',
        'AstraInteriorGronwall': 'Gronwall bounds from interior differential inequalities and endpoint continuity',
        'AstraGalerkinGronwall': 'Cutoff error bounds derived from relative-energy differential inequalities',
        'AstraGalerkinRegularity': 'Regularity and domination needed for the actual Galerkin relative-energy estimates',
        'AstraJointGalerkinLimit': 'Joint cutoff and split-step limit under supplied classical tail control; initial-norm step choice',
        'AstraUniformGalerkinLimit': 'Uniform-in-time joint approximation on the controlled classical interval T <= 1/5',
        'AstraPolynomialInverse': 'Actual local nonlinear polynomial inverse in a complete normed algebra',
        'AstraAnalyticFixedPoint': 'Analytic fixed-point construction with explicit norm and time bounds',
        'AstraAnalyticLpMap': 'Analytic sequence maps into the weighted Lp setting',
        'AstraAnalyticLift': 'Lift of the actual analytic fixed-point construction to weighted coefficient spaces',
        'AstraWeightedConvolution': 'Weighted convolution algebra estimates and actual coefficient identities',
        'AstraAnalyticKernel': 'Bounded analytic kernel operators in the weighted sequence space',
        'AstraAnalyticDuhamel': 'Actual analytic Duhamel operator and its norm bounds',
        'AstraAnalyticFourierDuhamel': 'Fourier-coordinate identity for the constructed Duhamel operator',
        'AstraAnalyticAssembly': 'Assembly of actual analytic fixed points from the selected weighted input data',
        'AstraWeightedDecoder': 'Weighted Fourier decoding and convergence of the decoded field',
        'AstraWeightedReality': 'Hermitian coefficient reality and preservation under actual weighted operations',
        'AstraAnalyticReality': 'Reality of the actual analytic fixed-point construction',
        'AstraWeightedDerivative': 'Spatial differentiation of weighted Fourier decoders',
        'AstraWeightedRealDecode': 'Real-valued decoding of Hermitian weighted Fourier coefficients',
        'AstraAnalyticModeODE': 'Actual mode ODE identities for the constructed analytic solution',
        'AstraAnalyticFields': 'Construction, constitutive identity, bounds and spatial derivatives of physical analytic fields',
        'AstraAnalyticPhysicalMode': 'Physical Fourier-mode identities derived from the analytic construction',
        'AstraAnalyticTransport': 'Time transport and derivative identities for the constructed analytic fields',
        'AstraAnalyticPDE': 'Actual classical nonlinear Maxwell PDE for the constructed local analytic fields',
        'AstraAnalyticClassical': 'Constructed analytic fields satisfy the required classical continuum regularity',
        'AstraRealFourierProjection': 'Real Fourier projection identities for continuous periodic fields',
        'AstraAnalyticTails': 'Explicit cutoff-tail estimates from the analytic weighted coefficient bounds',
        'AstraAnalyticTraceTails': 'Uniform Fourier-tail estimates for actual analytic traces',
        'AstraAnalyticFieldTails': 'Uniform spatial-tail estimates for the constructed physical fields',
        'AstraAnalyticInitial': 'Actual initial physical fields and constitutive compatibility',
        'AstraAnalyticInitialTails': 'Initial Fourier-tail bounds derived from the selected analytic input',
        'AstraAnalyticGalerkinCertificate': 'Constructed analytic data discharge classical tail control and yield uniform joint Galerkin/splitting convergence',
        'AstraExplicitAnalyticInput': 'Explicit analytic coefficient data satisfying the required smallness and reality bounds',
        'AstraAnalyticExample': 'Concrete sinusoidal analytic input and its actual continuum approximation certificate',
        'AstraContinuumLimit': 'Initial analytic data construct physical Maxwell PDE fields, scalar restoration, cutoff-uniform spatial estimates and a uniform joint split/cutoff limit on 0 <= T <= 1/5; includes a nonconstant mixed-wave datum, no arbitrary-data uniqueness claim',
    }
    supplemental_groups = {
        Path(group["source"]).stem: dict(
            theorem_count=group["theorem_count"], declaration_count=group["declaration_count"],
            path=group["source"], scope=supplemental_scopes[Path(group["source"]).stem])
        for group in supplement["supplemental_groups"]
    }
    result = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(), passed=passed,
        proof_layout="Existing Elastica and linear-input proofs retained; registered additions and theorem compositions audited together",
        entry_point="tools/verify.py", detailed_joint_report="linear_input/lean_results.json",
        supplemental_report="verification/main-result.json", supplemental_run=supplement_run,
        version=current["version"], clean_project_build=rebuild, dependency_cache_retained=True,
        run=run, build=current["parent_library_build"], baseline_audit=current["compile"], audit=supplement["compile"],
        declarations=declarations, theorem_count=current["theorem_count"] + current["parent_theorem_count"] + supplement["theorem_count"],
        declaration_count=len(declarations), axioms=axioms, joint_axiom_audit=supplement["joint_axiom_audit"],
        proof_groups=dict(Elastica=dict(theorem_count=current["parent_theorem_count"],
            declaration_count=current["parent_declaration_count"], path="lean/Elastica"),
            LinearInput=dict(theorem_count=current["theorem_count"], declaration_count=current["declaration_count"],
            path="linear_input/lean_check", scope="Unchanged original 36 proof parts"),
            **supplemental_groups),
        added_declarations=supplement["declarations"],
        dependencies=current["dependencies"], source_hashes=hashes,
        unexpected=current["unexpected"] + supplement["unexpected"] + supplement["errors"],
        forbidden_tokens=current["forbidden_tokens"] + supplement["forbidden_tokens"],
        warnings=warnings, changed_during_verification=changed,
        pre_unification_preservation=preservation,
        scope="The unchanged linear-input verifier builds Elastica, generates All.lean from the original 36 parts and audits the original 509 declarations. The additive checker then compiles the exact All.lean followed by every registered supplement with --trust=0 and audits all original and additional public declarations in one session. Supplements retain separate source groups and counts. Original proof files, names and configuration are preserved.",
        not_covered=[
            ("existence for arbitrary prescribed boundary/area data and regularity of weak "
             "area-constrained minimizers; the explicit circle comparison minimum is covered")
            if item == "existence and regularity of area-constrained minimizing curves" else item
            for item in current["not_covered"]])
    write_json(OUT / "lean.json", result)
    # Keep familiar top-level log links, copying actual outputs rather than relabelling old runs.
    shutil.copyfile(ROOT / "linear_input" / current["parent_library_build"]["log"], OUT / "lean-build.log")
    shutil.copyfile(OUT / "main-result.log", OUT / "lean-axioms.log")
    if rebuild and passed:
        shutil.copyfile(OUT / "lean-build.log", OUT / "clean-rebuild.log")
        write_json(OUT / "clean-rebuild.json", dict(timestamp_utc=result["timestamp_utc"],
            clean_project_build=True, dependency_cache_retained=True,
            build=current["parent_library_build"], cleaned_by="tools/verify.py --rebuild before the joint checker",
            build_log="verification/clean-rebuild.log", build_log_sha256=sha(OUT / "clean-rebuild.log"),
            source_hashes=hashes, dependencies=current["dependencies"]))
    return result


def refresh_manifest():
    files = {}
    for path in sorted(ROOT.rglob("*")):
        rel = path.relative_to(ROOT)
        if not path.is_file() or ".lake" in rel.parts or "__pycache__" in rel.parts or path.name == "manifest.json":
            continue
        files[rel.as_posix()] = sha(path)
    write_json(ROOT / "manifest.json", dict(algorithm="SHA256", files=files))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--lean-only", action="store_true")
    modes.add_argument("--proof-only", action="store_true")
    modes.add_argument("--two-wavelength-only", action="store_true", help="Verify the isolated PR #92 two-wavelength extension")
    modes.add_argument("--arc3-only", action="store_true", help="Check experimental ARC integration; does not run Lean")
    modes.add_argument("--integration-only", action="store_true", help="Check integrated PR sources, offline tests and Lean proofs")
    modes.add_argument("--elastica-boundary-only", action="store_true", help="Check the fixed-boundary Elastica operator bridge")
    args = parser.parse_args(argv)
    if args.two_wavelength_only:
        from verify_two_wavelength import run_two_wavelength
        result = run_two_wavelength(ROOT, args.rebuild)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0 if result["passed"] else 1
    if args.elastica_boundary_only:
        if args.rebuild:
            parser.error("--rebuild is not supported by --elastica-boundary-only")
        from verify_elastica_fixed_boundary import main as verify_boundary
        return verify_boundary([])
    if args.arc3_only:
        if args.rebuild:
            parser.error("--rebuild applies to Lean, not --arc3-only")
        from arc3_integration import run_arc3
        report = run_arc3(ROOT)
        print(json.dumps(report, ensure_ascii=False, indent=2))
        return 0 if report["passed"] else 1
    OUT.mkdir(exist_ok=True)
    if args.integration_only:
        from pr_integration import run_integration
        result = run_integration(ROOT, command, args.rebuild)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0 if result["passed"] else 1
    if args.proof_only:
        from proof_only import run_proof_only
        proof = run_proof_only(ROOT, command, args.rebuild)
        print(json.dumps(proof, ensure_ascii=False, indent=2))
        return 0 if proof["passed"] else 1
    lean = verify_lean(args.rebuild)
    summary = {k: lean[k] for k in ("passed", "proof_layout", "version", "clean_project_build",
        "theorem_count", "declaration_count", "proof_groups", "unexpected", "warnings", "forbidden_tokens")}
    if args.lean_only:
        print(json.dumps(summary, ensure_ascii=False, indent=2))
        return 0 if lean["passed"] else 1
    checks = {}
    for key, script in (("examples", "tools/check_examples.py"), ("scale_response", "tools/check_scale_response.py"),
                       ("combinations", "tools/check_combinations.py"), ("linear_input", "linear_input/verify.py"),
                       ("rendering", "tools/render.py")):
        checks[key] = command([sys.executable, "-X", "utf8", script], key.replace("_", "-") + "-run")
    write_json(OUT / "results.json", dict(passed=False, status="delivery validation pending"))
    write_json(ROOT / "manifest.json", dict(algorithm="SHA256", status="validation pending", files={}))
    delivery_run = command([sys.executable, "-X", "utf8", "tools/check_delivery.py"], "delivery-run")
    delivery = json.loads((OUT / "delivery.json").read_text("utf-8"))
    passed = lean["passed"] and all(check["exit_code"] == 0 for check in checks.values()) and delivery_run["exit_code"] == 0 and delivery["passed"]
    result = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(), passed=passed, lean_passed=lean["passed"],
        theorem_count=lean["theorem_count"], declaration_count=lean["declaration_count"],
        clean_project_build=args.rebuild, **checks, delivery_run=delivery_run, delivery=delivery,
        source_hashes=lean["source_hashes"])
    write_json(OUT / "results.json", result)
    refresh_manifest()
    print(json.dumps({**summary, "passed": passed, "checks": checks, "delivery_passed": delivery["passed"]}, ensure_ascii=False, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
