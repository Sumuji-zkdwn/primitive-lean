"""Check additive proof sources against the unchanged joint assembly.

Run linear_input/verify_lean.py first, or use tools/verify.py for both stages.
MainResult.lean prepends the additive Mathlib imports listed in EXTRA_IMPORTS, then the
byte-exact verified All.lean, the registered supplements and the all-declaration axiom audit.
Approved assembly contexts can add namespace aliases outside a source's exact byte span.
The recorded prelude lowers the generic LieAlgebra Module instance priority
after All.lean, preserving the existing analytic instances and proof bytes.
The original All.lean bytes are preserved without modification.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
OUT = ROOT / "verification"
PROOFS = ROOT / "linear_input/lean_check"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
# Additive Mathlib imports prepended to MainResult.lean (All.lean bytes stay unchanged).
EXTRA_IMPORTS = (
    "Mathlib.Topology.UnitInterval",
    "Mathlib.Topology.Constructions.SumProd",
    "Mathlib.Topology.Compactness.Compact",
    "Mathlib.Topology.ContinuousOn",
    "Mathlib.Data.Fintype.Card",
    "Mathlib.Data.Fintype.Prod",
    "Mathlib.Data.Fintype.Sum",
    "Mathlib.SetTheory.Cardinal.Finite",
    "Mathlib.Data.Fin.VecNotation",
    "Mathlib.Data.Setoid.Basic",
    "Mathlib.Algebra.BigOperators.Fin",
    "Mathlib.Data.Finset.Max",
    "Mathlib.Topology.Algebra.Order.Field",
    "Mathlib.Data.List.Dedup",
    "Mathlib.Data.Nat.Squarefree",
    "Mathlib.FieldTheory.RatFunc.IntermediateField",
    "Mathlib.Data.Nat.Factorization.Defs",
    "Mathlib.RingTheory.UniqueFactorizationDomain.Basic",
    "Mathlib.Data.PNat.Factors",
    "Mathlib.Tactic.NormNum.Prime",  # norm_num proves Nat.Prime (PR #50-#54)
    "Mathlib.Data.Sym.Card",  # Sym.card_sym_fin_eq_multichoose (PR #53)
    "Mathlib.Analysis.Calculus.Deriv.Inv",
    "Mathlib.Analysis.Calculus.Deriv.MeanValue",
    "Mathlib.Analysis.Calculus.Deriv.Pow",
    "Mathlib.Analysis.Calculus.MeanValue",
    "Mathlib.Analysis.Normed.Operator.Basic",
    "Mathlib.Analysis.SpecialFunctions.Arsinh",
    "Mathlib.Analysis.SpecialFunctions.Integrals.Basic",
    "Mathlib.Analysis.SpecialFunctions.Sqrt",
    "Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic",
    "Mathlib.Data.Real.Basic",
    "Mathlib.Tactic",
    "Mathlib.Tactic.FieldSimp",
    "Mathlib.Tactic.Linarith",
    "Mathlib.Tactic.NormNum",
    "Mathlib.Tactic.Positivity",
    "Mathlib.Tactic.Ring",
    "Mathlib.Topology.MetricSpace.Lipschitz",
    "Mathlib.Topology.Order.IntermediateValue",
    "Mathlib.Analysis.InnerProductSpace.ProdL2",
    "Mathlib.Analysis.ODE.Gronwall",
    "Mathlib.Analysis.ODE.PicardLindelof",
    "Mathlib.Analysis.SpecialFunctions.Exp",
    "Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp",
    "Mathlib.Analysis.SpecificLimits.Basic",
    "Lean.Util.CollectAxioms",
    "Mathlib.Algebra.QuadraticDiscriminant",
    "Mathlib.Analysis.Calculus.IteratedDeriv.Defs",
    "Mathlib.Analysis.Calculus.ParametricIntervalIntegral",
    "Mathlib.Analysis.Calculus.SmoothSeries",
    "Mathlib.Analysis.Complex.Basic",
    "Mathlib.Analysis.Complex.ExponentialBounds",
    "Mathlib.Analysis.Complex.Trigonometric",
    "Mathlib.Analysis.Fourier.AddCircle",
    "Mathlib.Analysis.InnerProductSpace.Adjoint",
    "Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional",
    "Mathlib.Analysis.Normed.Lp.lpSpace",
    "Mathlib.Analysis.Normed.Module.Basic",
    "Mathlib.Analysis.Normed.Operator.Bilinear",
    "Mathlib.Analysis.Normed.Operator.Prod",
    "Mathlib.Analysis.Normed.Ring.InfiniteSum",
    "Mathlib.Analysis.SpecialFunctions.ExpDeriv",
    "Mathlib.Analysis.SpecialFunctions.Log.Basic",
    "Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv",
    "Mathlib.Data.Real.Sqrt",
    "Mathlib.MeasureTheory.Integral.Bochner.Set",
    "Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus",
    "Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts",
    "Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic",
    "Mathlib.Order.Filter.AtTopBot.Finset",
    "Mathlib.Topology.Algebra.Module.FiniteDimension",
    "Mathlib.Topology.ContinuousMap.Algebra",
    "Mathlib.Topology.ContinuousMap.Compact",
    "Mathlib.Topology.ContinuousMap.Star",
    "Mathlib.Topology.MetricSpace.Contracting",
    "Mathlib.Topology.MetricSpace.Equicontinuity",
    "Mathlib.Topology.Order.ProjIcc",
    "Mathlib.Topology.UniformSpace.Ascoli",
    "Mathlib.Analysis.Calculus.Deriv.Shift",
    "Mathlib.Data.Fintype.Pigeonhole",
    "Mathlib.Probability.Moments.ComplexMGF",
    "Mathlib.Analysis.Normed.Algebra.GelfandFormula",
    "Mathlib.Analysis.Matrix.Normed",
    "Mathlib.LinearAlgebra.Matrix.Irreducible.Defs",
    "Mathlib.Algebra.BigOperators.Intervals",
    "Mathlib.Algebra.Lie.Free",
    "Mathlib.Topology.ContinuousMap.StoneWeierstrass",
    "Mathlib.Topology.UniformSpace.UniformApproximation",
    "Mathlib.Topology.EMetricSpace.BoundedVariation",
    "Mathlib.MeasureTheory.Measure.Stieltjes",
    "Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap",
    "Mathlib.MeasureTheory.Integral.DominatedConvergence",
    "Mathlib.MeasureTheory.Integral.Prod",
    "Mathlib.Topology.LocallyConstant.Basic",
    "Mathlib.RingTheory.PowerSeries.Log",
    "Mathlib.Analysis.Convex.Jensen",
    "Mathlib.Analysis.Convex.PathConnected",
    "Mathlib.Analysis.Convex.Topology",
    "Mathlib.Analysis.LocallyConvex.Separation",
    "Mathlib.LinearAlgebra.Matrix.Adjugate",
    "Mathlib.Data.Finset.Sort",
    "Mathlib.Combinatorics.SimpleGraph.Acyclic",
    "Mathlib.Algebra.MonoidAlgebra.Basic",
    "Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli",
    "Mathlib.Analysis.Normed.Module.FiniteDimension",
)

# Importing FreeLieAlgebra adds a generic LieAlgebra-to-Module instance.
# Prefer the pre-existing analytic Module instances without changing any
# historical proof bytes; the generic instance remains available as fallback.
ASSEMBLY_PRELUDE = "attribute [instance 90] LieAlgebra.toModule\n"

SUPPLEMENTS = (
    ('linear_input/lean_check/MainResult.inc', 'LinearInputMainResult'),
    ('linear_input/lean_check/GeneralMinimum.inc', 'LinearInputMinimum'),
    ('linear_input/lean_check/SupportComposition.inc', 'LinearInputSupportComposition'),
    ('linear_input/lean_check/QuarticClassification.inc', 'LinearInputQuarticClassification'),
    ('linear_input/lean_check/CurvatureRigidity.inc', 'LinearInputCurvatureRigidity'),
    ('linear_input/lean_check/HistorySignature.inc', 'LinearInputHistorySignature'),
    ('linear_input/lean_check/CurveWordAlgebra.inc', 'LinearInputCurveWordAlgebra'),
    ('linear_input/lean_check/CurveWordFinite.inc', 'LinearInputCurveWordFinite'),
    ('linear_input/lean_check/CurveWordArc.inc', 'LinearInputCurveWordArc'),
    ('linear_input/lean_check/CurveWordFiniteState.inc', 'LinearInputCurveWordFiniteState'),
    ('linear_input/lean_check/CurveWordCycleLimit.inc', 'LinearInputCurveWordCycleLimit'),
    ('linear_input/lean_check/CurveWordRealization.inc', 'LinearInputCurveWordRealization'),
    ('linear_input/lean_check/CurveWordThermodynamics.inc', 'LinearInputCurveWordThermodynamics'),
    ('linear_input/lean_check/CurveWordSignature.inc', 'LinearInputCurveWordSignature'),
    ('linear_input/lean_check/CurveWordCircularMoment.inc', 'LinearInputCurveWordCircularMoment'),
    ('linear_input/lean_check/BranchForgetting.inc', 'LinearInputBranchForgetting'),
    ('linear_input/lean_check/VariablePairObservations.inc', 'LinearInputVariablePairs'),
    ('linear_input/lean_check/BranchFibers.inc', 'LinearInputBranchFibers'),
    ('linear_input/lean_check/F0Retractions.inc', 'LinearInputF0'),
    ('linear_input/lean_check/F0Counting.inc', 'LinearInputF0Counting'),
    ('linear_input/lean_check/F0MergeChains.inc', 'LinearInputF0Merge'),
    ('linear_input/lean_check/FiniteBayes.inc', 'LinearInputBayes'),
    ('linear_input/lean_check/FourBayes.inc', 'LinearInputFourBayes'),
    ('linear_input/lean_check/GaloisChebyshev.inc', 'LinearInputGaloisChebyshev'),
    ('linear_input/lean_check/KummerDihedral.inc', 'LinearInputKummerDihedral'),
    ('linear_input/lean_check/VariablePairGaloisBridge.inc', 'LinearInputVariablePairGalois'),
    ('linear_input/lean_check/FoldCount.inc', 'LinearInputFoldCount'),
    ('linear_input/lean_check/FoldCountOriginal.inc', 'LinearInputFoldCountOriginal'),
    ('linear_input/lean_check/F16Holonomy.inc', 'LinearInputF16Holonomy'),
    ('linear_input/lean_check/F16RecoverySpectrum.inc', 'LinearInputF16Recovery'),
    ('linear_input/lean_check/F16RankCertificate.inc', 'LinearInputF16Rank'),
    ('linear_input/lean_check/F16RealDeterminant.inc', 'LinearInputF16Determinant'),
    ('linear_input/lean_check/F16CompleteRank.inc', 'LinearInputF16CompleteRank'),
    ('linear_input/lean_check/F16UnexpectedBridges.inc', 'LinearInputF16UnexpectedBridges'),
    ('linear_input/lean_check/ShearCommutator.inc', 'LinearInputShearCommutator'),
    ('linear_input/lean_check/ComplementaryPencilRecovery.inc', 'LinearInputComplementaryPencilRecovery'),
    ('linear_input/lean_check/F16ConstructiveRecovery.inc', 'LinearInputF16ConstructiveRecovery'),
    ('linear_input/lean_check/ComplementaryObservationExamples.inc', 'LinearInputComplementaryObservationExamples'),
    ('linear_input/lean_check/StrangeOperatorGalois.inc', 'LinearInputStrangeGalois'),
    ('linear_input/lean_check/StrangeOperatorConjugacy.inc', 'LinearInputStrangeConjugacy'),
    ('linear_input/lean_check/StrangeOperatorBoundary.inc', 'LinearInputStrangeBoundary'),
    ('linear_input/lean_check/StrangeOperatorFixedSets.inc', 'LinearInputStrangeFixedSets'),
    ('linear_input/lean_check/StrangeOperatorCounting.inc', 'LinearInputStrangeCounting'),
    ('linear_input/lean_check/F16SaddleCantor.inc', 'LinearInputF16SaddleCantor'),
    ('linear_input/lean_check/F16FullMatrix.inc', 'LinearInputF16FullMatrix'),
    ('linear_input/lean_check/F16FullRank.inc', 'LinearInputF16FullRank'),
    ('linear_input/lean_check/F0UpdateDescent.inc', 'LinearInputF0Descent'),
    ('linear_input/lean_check/Rule481Symmetry.inc', 'LinearInputRule481'),
    ('linear_input/lean_check/HannaJetCorrection.inc', 'LinearInputHannaJets'),
    ('linear_input/lean_check/FutureObservations.inc', 'LinearInputFutureObservation'),
    ('linear_input/lean_check/FutureFiniteHorizon.inc', 'LinearInputFutureHorizon'),
    ('linear_input/lean_check/OperatorWordObservations.inc', 'LinearInputOperatorWords'),
    ('linear_input/lean_check/MonoEyeComposition.inc', 'LinearInputMonoEyeComposition'),
    ('linear_input/lean_check/OperatorBisimulation.inc', 'LinearInputOperatorBisimulation'),
    ('linear_input/lean_check/OperatorVocabularyRefinement.inc', 'LinearInputOperatorRefinement'),
    ('linear_input/lean_check/OperatorFiniteHorizon.inc', 'LinearInputOperatorHorizon'),
    ('linear_input/lean_check/OperatorSemanticClosure.inc', 'LinearInputOperatorSemanticClosure'),
    ('linear_input/lean_check/CrossSystemObservation.inc', 'LinearInputCrossSystemObservation'),
    ('linear_input/lean_check/InverseTowerObservation.inc', 'LinearInputInverseTowerObservation'),
    ('linear_input/lean_check/LaaksoFiniteGraph.inc', 'LinearInputLaaksoFiniteGraph'),
    ('linear_input/lean_check/LaaksoNonlinearObstruction.inc', 'LinearInputLaaksoNonlinear'),
    ('linear_input/lean_check/LaaksoRealization.inc', 'LinearInputLaaksoRealization'),
    ('linear_input/lean_check/LaaksoGeometricProjection.inc', 'LinearInputLaaksoGeometricProjection'),
    ('linear_input/lean_check/LaaksoGeometricTower.inc', 'LinearInputLaaksoGeometricTower'),
    ('linear_input/lean_check/SemanticIntervalNecessity.inc', 'LinearInputSemanticIntervals'),
    ('linear_input/lean_check/FiniteSelfSynthesis.inc', 'LinearInputFiniteSelfSynthesis'),
    ('linear_input/lean_check/RecursiveOperatorReentry.inc', 'LinearInputRecursiveReentry'),
    ('linear_input/lean_check/RuleSelfModification.inc', 'LinearInputRuleSelfModification'),
    ('linear_input/lean_check/MetaRuleSelfExtension.inc', 'LinearInputMetaRuleExtension'),
    ('linear_input/lean_check/HigherOrderLiftSelfRewriting.inc', 'LinearInputHigherOrderLiftSelfRewriting'),
    ('linear_input/lean_check/EWFSFenchel.inc', 'LinearInputEWFSDual'),
    ('linear_input/lean_check/WFSCanonicalLift.inc', 'LinearInputWFSCanonical'),
    ('linear_input/lean_check/EWFSFutureBridge.inc', 'LinearInputEWFSFuture'),
    ('linear_input/lean_check/TemporalSampling.inc', 'LinearInputTemporalSampling'),
    ('linear_input/lean_check/WFSMobiusFourier.inc', 'LinearInputWFSMobiusFourier'),
    ('linear_input/lean_check/EnergyWfsFenchel.inc', 'LinearInputEnergyGaugeFenchel'),
    ('linear_input/lean_check/ObservationRetractionPolarity.inc', 'LinearInputObservationRetractionPolarity'),
    ('linear_input/lean_check/F0FutureMinimality.inc', 'LinearInputF0FutureMinimality'),
    ('linear_input/lean_check/WFSProjectiveSampling.inc', 'LinearInputWFSObservation'),
    ('linear_input/lean_check/RepresentationBridges.inc', 'LinearInputRepresentationBridges'),
    ('linear_input/lean_check/HistoryNonpreservation.inc', 'LinearInputHistoryNonpreservation'),
    ('linear_input/lean_check/TemporalLocalExtinction.inc', 'LinearInputTemporalExtinction'),
    ('linear_input/lean_check/LocalCapacityIncompatibility.inc', 'LinearInputCapacityExtinction'),
    ('linear_input/lean_check/CooperativeGluingObstruction.inc', 'LinearInputCooperativeGluing'),
    ('linear_input/lean_check/RelationalOddCycleGluing.inc', 'LinearInputRelationalGluing'),
    ('linear_input/lean_check/JoinContextualEquivalence.inc', 'LinearInputJoinContexts'),
    ('linear_input/lean_check/CurveLetterContextualEquivalence.inc', 'LinearInputCurveLetters'),
    ('linear_input/lean_check/RadicalF0Bridge.inc', 'LinearInputRadicalF0'),
    ('linear_input/lean_check/PilotComparisonBridge.inc', 'LinearInputPilotComparison'),
    ('linear_input/lean_check/PilotVolumeTransport.inc', 'LinearInputPilotTransport'),
    ('linear_input/lean_check/PilotHullInflation.inc', 'LinearInputPilotHullInflation'),
    ('linear_input/lean_check/PilotHullStability.inc', 'LinearInputPilotHullStability'),
    ('linear_input/lean_check/ElasticaOperatorBridge.inc', 'LinearInputElasticaOperatorBridge'),
    ('linear_input/lean_check/ObservableRigidPoint.inc', 'LinearInputRigidPoint'),
    ('linear_input/lean_check/ChebyshevDihedralDescent.inc', 'LinearInputChebyshevDescent'),
    ('linear_input/lean_check/ChebyshevRatFuncDegrees.inc', 'LinearInputChebyshevNext'),
    ('linear_input/lean_check/ChebyshevDegreeTower.inc', 'LinearInputChebyshevTower'),
    ('linear_input/lean_check/ChebyshevSplittingField.inc', 'LinearInputChebyshevSplitting'),
    ('linear_input/lean_check/ChebyshevGaloisAutomorphisms.inc', 'LinearInputChebyshevAutomorphisms'),
    ('linear_input/lean_check/RimObservability.inc', 'LinearInputRimObservability'),
    ('linear_input/lean_check/ViscousRewrite.inc', 'LinearInputViscousRewrite'),
    ('linear_input/lean_check/GravityCocycle.inc', 'LinearInputGravityCocycle'),
    ('linear_input/lean_check/GravityObserver.inc', 'LinearInputGravityObserver'),
    ('linear_input/lean_check/GravityObservation.inc', 'LinearInputGravityObservation'),
    ('linear_input/lean_check/TernaryZeroCesaro.inc', 'LinearInputTernaryZero'),
    ('linear_input/lean_check/FiniteObservationSeparation.inc', 'LinearInputFiniteObservation'),
    ('linear_input/lean_check/DecompositionIdentification.inc', 'LinearInputDecompositionIdentification'),
    ('linear_input/lean_check/DecompositionF0Bridge.inc', 'LinearInputDecompositionF0Bridge'),
    ('linear_input/lean_check/PrimeFactorIdentification.inc', 'LinearInputPrimeFactorIdentification'),
    ('linear_input/lean_check/PrimeSplitNormalForm.inc', 'LinearInputPrimeSplitNormalForm'),
    ('linear_input/lean_check/AssociatesFactorIdentification.inc', 'LinearInputAssociatesFactorIdentification'),
    ('linear_input/lean_check/GeneratedNonUniqueMonoid.inc', 'LinearInputGeneratedNonUnique'),
    ('linear_input/lean_check/HalfFactorialIdentification.inc', 'LinearInputHalfFactorial'),
    ('linear_input/lean_check/AtomicGeneratorClassification.inc', 'LinearInputAtomicGeneratorClassification'),
    ('linear_input/lean_check/AtomicHalfFactorial.inc', 'LinearInputAtomicHalfFactorial'),
    ('linear_input/lean_check/AtomicWordProbe.inc', 'LinearInputAtomicWordProbe'),
    ('linear_input/lean_check/SingleSwapFiber.inc', 'LinearInputSingleSwapFiber'),
    ('linear_input/lean_check/F16RimRecovery.inc', 'LinearInputF16RimRecovery'),
    ('linear_input/lean_check/ParallelLocalGluing.inc', 'LinearInputParallelGluing'),
    ('linear_input/lean_check/OperatorContextualEquivalence.inc', 'LinearInputOperatorContexts'),
    ('linear_input/lean_check/OperatorAdaptivePolicies.inc', 'LinearInputOperatorPolicies'),
    ('linear_input/lean_check/OperatorProductSystems.inc', 'LinearInputOperatorProducts'),
    ('linear_input/lean_check/OperatorReachability.inc', 'LinearInputOperatorReachability'),
    ('linear_input/lean_check/OperatorSensorFamilies.inc', 'LinearInputOperatorSensors'),
    ('linear_input/lean_check/OperatorF0SemanticBridge.inc', 'LinearInputOperatorF0Bridge'),
    ('linear_input/lean_check/OperatorSemanticMonoid.inc', 'LinearInputOperatorSemanticMonoid'),
    ('linear_input/lean_check/OperatorFiniteMapCounts.inc', 'LinearInputOperatorFiniteCounts'),
    ('linear_input/lean_check/GravityObservations.inc', 'LinearInputGravityObservations'),
    ('linear_input/lean_check/FiveDimLagrange.inc', 'LinearInputFiveDimLagrange'),
    ('linear_input/lean_check/ParallelWriteGluing.inc', 'LinearInputParallelWriteGluing'),
    ('linear_input/lean_check/PrimeFactorObservation.inc', 'LinearInputPrimeFactorObservation'),
    ('linear_input/lean_check/PrimeFactorOrbits.inc', 'LinearInputPrimeFactorOrbits'),
    ('linear_input/lean_check/PrimeFactorF0Adaptive.inc', 'LinearInputPrimeFactorF0'),
    ('linear_input/lean_check/PrimeFactorFiniteLength.inc', 'LinearInputPrimeFactorFiniteLength'),
    ('linear_input/lean_check/PrimeFactorGeneralF0.inc', 'LinearInputPrimeFactorGeneralF0'),
    ('linear_input/lean_check/AutonomyCycle00001.inc', 'LinearInputAutoCycle00001'),
    ('linear_input/lean_check/AutonomyCycle00002.inc', 'LinearInputAutoCycle00002'),
    ('linear_input/lean_check/AutonomyCycle00003.inc', 'LinearInputAutoCycle00003'),
    ('linear_input/lean_check/AstraRiccati.inc', 'KerrKoopman.Riccati'),
    ('linear_input/lean_check/AstraFiniteEnergy.inc', 'KerrKoopman.FiniteEnergy'),
    ('linear_input/lean_check/AstraReconstruction.inc', 'KerrKoopman.Reconstruction'),
    ('linear_input/lean_check/AstraKoopmanDescent.inc', 'LinearInputKoopmanDescent'),
    ('linear_input/lean_check/AstraConstitutive.inc', 'KerrKoopman.PrimitiveConstitutive'),
    ('linear_input/lean_check/AstraObservation.inc', 'KerrKoopman.PrimitiveObservation'),
    ('linear_input/lean_check/AstraDynamicsBoundary.inc', 'KerrKoopman.PrimitiveDynamicsBoundary'),
    ('linear_input/lean_check/AstraExplicitMaterial.inc', 'KerrKoopman.ExplicitMaterial'),
    ('linear_input/lean_check/AstraRelativeEnergy.inc', 'KerrKoopman.RelativeEnergy'),
    ('linear_input/lean_check/AstraExactShear.inc', 'KerrKoopman.ExactShear'),
    ('linear_input/lean_check/AstraHilbertShear.inc', 'KerrKoopman.HilbertShear'),
    ('linear_input/lean_check/AstraHilbertFlow.inc', 'KerrKoopman.HilbertFlow'),
    ('linear_input/lean_check/AstraHilbertError.inc', 'KerrKoopman.HilbertError'),
    ('linear_input/lean_check/AstraIterationBound.inc', 'KerrKoopman.IterationBound'),
    ('linear_input/lean_check/AstraHilbertIteration.inc', 'KerrKoopman.HilbertIteration'),
    ('linear_input/lean_check/AstraFourierProjection.inc', 'KerrKoopman.FourierProjection'),
    ('linear_input/lean_check/AstraMaterialL2.inc', 'KerrKoopman.MaterialL2'),
    ('linear_input/lean_check/AstraRealGalerkin.inc', 'KerrKoopman.RealGalerkin'),
    ('linear_input/lean_check/AstraFourierDerivative.inc', 'KerrKoopman.FourierProjection'),
    ('linear_input/lean_check/AstraRealFourierDerivative.inc', 'KerrKoopman.RealFourierDerivative'),
    ('linear_input/lean_check/AstraFiniteRepresentatives.inc', 'KerrKoopman.FiniteRepresentatives'),
    ('linear_input/lean_check/AstraFourierSupBounds.inc', 'KerrKoopman.FourierSupBounds'),
    ('linear_input/lean_check/AstraFiniteRepresentativeCalculus.inc', 'KerrKoopman.FiniteRepresentatives'),
    ('linear_input/lean_check/AstraRelativeDynamics.inc', 'KerrKoopman.RelativeDynamics'),
    ('linear_input/lean_check/AstraContinuumCalculus.inc', 'KerrKoopman.ContinuumCalculus'),
    ('linear_input/lean_check/AstraIntervalFourier.inc', 'KerrKoopman.IntervalFourier'),
    ('linear_input/lean_check/AstraContinuumRelative.inc', 'KerrKoopman.ContinuumRelative'),
    ('linear_input/lean_check/AstraIntegralTail.inc', 'KerrKoopman.IntegralTail'),
    ('linear_input/lean_check/AstraContinuumGalerkin.inc', 'KerrKoopman.ContinuumGalerkin'),
    ('linear_input/lean_check/AstraIntervalFourierProjection.inc', 'KerrKoopman.IntervalFourier'),
    ('linear_input/lean_check/AstraCircleProjection.inc', 'KerrKoopman.FiniteRepresentatives'),
    ('linear_input/lean_check/AstraGalerkinFlow.inc', 'KerrKoopman.GalerkinFlow'),
    ('linear_input/lean_check/AstraGalerkinClassical.inc', 'KerrKoopman.GalerkinClassical'),
    ('linear_input/lean_check/AstraContinuumFourier.inc', 'KerrKoopman.ContinuumFourier'),
    ('linear_input/lean_check/AstraGalerkinRelative.inc', 'KerrKoopman.GalerkinClassical'),
    ('linear_input/lean_check/AstraGalerkinRestoration.inc', 'KerrKoopman.GalerkinClassical'),
    ('linear_input/lean_check/AstraInitialRelativeEnergy.inc', 'KerrKoopman.GalerkinClassical'),
    ('linear_input/lean_check/AstraStoppingCertificate.inc', 'KerrKoopman.StoppingCertificate'),
    ('linear_input/lean_check/AstraInteriorGronwall.inc', 'KerrKoopman.InteriorGronwall'),
    ('linear_input/lean_check/AstraGalerkinGronwall.inc', 'KerrKoopman.GalerkinClassical'),
    ('linear_input/lean_check/AstraGalerkinRegularity.inc', 'KerrKoopman.GalerkinClassical'),
    ('linear_input/lean_check/AstraJointGalerkinLimit.inc', 'KerrKoopman.GalerkinClassical'),
    ('linear_input/lean_check/AstraUniformGalerkinLimit.inc', 'KerrKoopman.GalerkinClassical'),
    ('linear_input/lean_check/AstraPolynomialInverse.inc', 'KerrKoopman.Phase3PolynomialInverse'),
    ('linear_input/lean_check/AstraAnalyticFixedPoint.inc', 'KerrKoopman.AnalyticFixedPoint'),
    ('linear_input/lean_check/AstraAnalyticLpMap.inc', 'KerrKoopman.AnalyticLpMap'),
    ('linear_input/lean_check/AstraAnalyticLift.inc', 'KerrKoopman.AnalyticLift'),
    ('linear_input/lean_check/AstraWeightedConvolution.inc', 'KerrKoopman.Phase3WeightedConvolution'),
    ('linear_input/lean_check/AstraAnalyticKernel.inc', 'KerrKoopman.Phase3AnalyticKernel'),
    ('linear_input/lean_check/AstraAnalyticDuhamel.inc', 'KerrKoopman.AnalyticDuhamel'),
    ('linear_input/lean_check/AstraAnalyticFourierDuhamel.inc', 'KerrKoopman.AnalyticFourierDuhamel'),
    ('linear_input/lean_check/AstraAnalyticAssembly.inc', 'KerrKoopman.AnalyticAssembly'),
    ('linear_input/lean_check/AstraWeightedDecoder.inc', 'KerrKoopman.Phase3WeightedDecoder'),
    ('linear_input/lean_check/AstraWeightedReality.inc', 'KerrKoopman.Phase3WeightedReality'),
    ('linear_input/lean_check/AstraAnalyticReality.inc', 'KerrKoopman.AnalyticReality'),
    ('linear_input/lean_check/AstraWeightedDerivative.inc', 'KerrKoopman.Phase3WeightedDerivative'),
    ('linear_input/lean_check/AstraWeightedRealDecode.inc', 'KerrKoopman.Phase3WeightedRealDecode'),
    ('linear_input/lean_check/AstraAnalyticModeODE.inc', 'KerrKoopman.AnalyticModeODE'),
    ('linear_input/lean_check/AstraAnalyticFields.inc', 'KerrKoopman.AnalyticFields'),
    ('linear_input/lean_check/AstraAnalyticPhysicalMode.inc', 'KerrKoopman.AnalyticPhysicalMode'),
    ('linear_input/lean_check/AstraAnalyticTransport.inc', 'KerrKoopman.AnalyticTransport'),
    ('linear_input/lean_check/AstraAnalyticPDE.inc', 'KerrKoopman.AnalyticPDE'),
    ('linear_input/lean_check/AstraAnalyticClassical.inc', 'KerrKoopman.AnalyticClassical'),
    ('linear_input/lean_check/AstraRealFourierProjection.inc', 'KerrKoopman.RealFourierProjection'),
    ('linear_input/lean_check/AstraAnalyticTails.inc', 'KerrKoopman.AnalyticTails'),
    ('linear_input/lean_check/AstraAnalyticTraceTails.inc', 'KerrKoopman.AnalyticTraceTails'),
    ('linear_input/lean_check/AstraAnalyticFieldTails.inc', 'KerrKoopman.AnalyticFieldTails'),
    ('linear_input/lean_check/AstraAnalyticInitial.inc', 'KerrKoopman.AnalyticInitial'),
    ('linear_input/lean_check/AstraAnalyticInitialTails.inc', 'KerrKoopman.AnalyticInitialTails'),
    ('linear_input/lean_check/AstraAnalyticGalerkinCertificate.inc', 'KerrKoopman.AnalyticGalerkinCertificate'),
    ('linear_input/lean_check/AstraExplicitAnalyticInput.inc', 'KerrKoopman.ExplicitAnalyticInput'),
    ('linear_input/lean_check/AstraAnalyticExample.inc', 'KerrKoopman.AnalyticExample'),
    ('linear_input/lean_check/AstraFiniteFlow.inc', 'KerrKoopman.FiniteFlow'),
    ('linear_input/lean_check/AstraContinuumLimit.inc', 'KerrKoopman.ContinuumLimit'),
    ('linear_input/lean_check/CurveWordPiecewise.inc', 'LinearInputCurveWordPiecewise'),
    ('linear_input/lean_check/CurveWordCircleWords.inc', 'LinearInputCurveWordCircleWords'),
    ('linear_input/lean_check/CurveWordGraphLimit.inc', 'LinearInputCurveWordGraphLimit'),
    ('linear_input/lean_check/CurveWordDirectedGraph.inc', 'LinearInputCurveWordDirectedGraph'),
    ('linear_input/lean_check/CurveWordLaplace.inc', 'LinearInputCurveWordLaplace'),
    ('linear_input/lean_check/CurveWordSpectral.inc', 'LinearInputCurveWordSpectral'),
    ('linear_input/lean_check/CurveWordTransfer.inc', 'LinearInputCurveWordTransfer'),
    ('linear_input/lean_check/CurveWordChen.inc', 'LinearInputCurveWordChen'),
    ('linear_input/lean_check/CurveWordFormalSeries.inc', 'LinearInputCurveWordFormalSeries'),
    ('linear_input/lean_check/CurveWordCoproduct.inc', 'LinearInputCurveWordCoproduct'),
    ('linear_input/lean_check/CurveWordFriedrichs.inc', 'LinearInputCurveWordFriedrichs'),
    ('linear_input/lean_check/CurveWordTreeLike.inc', 'LinearInputCurveWordTreeLike'),
    ('linear_input/lean_check/CurveWordSignatureTopology.inc', 'LinearInputCurveWordSignatureTopology'),
    ('linear_input/lean_check/CurveWordReparametrization.inc', 'LinearInputCurveWordReparametrization'),
    ('linear_input/lean_check/CurveWordBoundedVariation.inc', 'LinearInputCurveWordBoundedVariation'),
    ('linear_input/lean_check/CurveWordStieltjes.inc', 'LinearInputCurveWordStieltjes'),
    ('linear_input/lean_check/CurveWordBVSignature.inc', 'LinearInputCurveWordBVSignature'),
    ('linear_input/lean_check/CurveWordBVReparam.inc', 'LinearInputCurveWordBVReparam'),
    ('linear_input/lean_check/CurveWordBVChen.inc', 'LinearInputCurveWordBVChen'),
    ('linear_input/lean_check/CurveWordBVShuffle.inc', 'LinearInputCurveWordBVShuffle'),
    ('linear_input/lean_check/CurveWordSignatureTree.inc', 'LinearInputCurveWordSignatureTree'),
    ('linear_input/lean_check/CurveWordHeightMetric.inc', 'LinearInputCurveWordHeightMetric'),
    ('linear_input/lean_check/CurveWordScalarLog.inc', 'LinearInputCurveWordScalarLog'),
    ('linear_input/lean_check/CurveWordLogFormula.inc', 'LinearInputCurveWordLogFormula'),
    ('linear_input/lean_check/CurveWordBVTopology.inc', 'LinearInputCurveWordBVTopology'),
    ('linear_input/lean_check/CurveWordBVAlgebra.inc', 'LinearInputCurveWordBVAlgebra'),
    ('linear_input/lean_check/CurveWordConvexObservation.inc', 'LinearInputCurveWordConvexObservation'),
    ('linear_input/lean_check/CurveWordSignatureBounds.inc', 'LinearInputCurveWordSignatureBounds'),
    ('linear_input/lean_check/CurveWordSignatureUniform.inc', 'LinearInputCurveWordSignatureUniform'),
    ('linear_input/lean_check/CurveWordConvexSeparation.inc', 'LinearInputCurveWordConvexSeparation'),
    ('linear_input/lean_check/CurveWordLinearAction.inc', 'LinearInputCurveWordLinearAction'),
    ('linear_input/lean_check/CurveWordBVCanonical.inc', 'LinearInputCurveWordBVCanonical'),
    ('linear_input/lean_check/CurveWordWordSignature.inc', 'LinearInputCurveWordWordSignature'),
    ('linear_input/lean_check/CurveWordGenerating.inc', 'LinearInputCurveWordGenerating'),
    ('linear_input/lean_check/CurveWordWordGenerating.inc', 'LinearInputCurveWordWordGenerating'),
    ('linear_input/lean_check/CurveWordSamplingOrder.inc', 'LinearInputCurveWordSamplingOrder'),
    ('linear_input/lean_check/CurveWordTreeSignature.inc', 'LinearInputCurveWordTreeSignature'),
    ('linear_input/lean_check/CurveWordPolygonal.inc', 'LinearInputCurveWordPolygonal'),
    ('linear_input/lean_check/CurveWordBVSubinterval.inc', 'LinearInputCurveWordBVSubinterval'),
    ('linear_input/lean_check/CurveWordTreeSampling.inc', 'LinearInputCurveWordTreeSampling'),
    ('linear_input/lean_check/CurveWordTreeSampleProduct.inc', 'LinearInputCurveWordTreeSampleProduct'),
    ('linear_input/lean_check/CurveWordTreeLimit.inc', 'LinearInputCurveWordTreeLimit'),
    ('linear_input/lean_check/CurveWordArcGenerating.inc', 'LinearInputCurveWordArcGenerating'),
    ('linear_input/lean_check/CurveWordBVPathOperations.inc', 'LinearInputCurveWordBVPathOperations'),
    ('linear_input/lean_check/CurveWordBVCompactness.inc', 'LinearInputCurveWordBVCompactness'),
    ('linear_input/lean_check/CurveWordBVLoopErase.inc', 'LinearInputCurveWordBVLoopErase'),
    ('linear_input/lean_check/CurveWordBVReduced.inc', 'LinearInputCurveWordBVReduced'),
    ('linear_input/lean_check/CurveWordBVArc.inc', 'LinearInputCurveWordBVArc'),
    ('linear_input/lean_check/CurveWordBVOrientation.inc', 'LinearInputCurveWordBVOrientation'),
    ('linear_input/lean_check/CurveWordGeodesicTree.inc', 'LinearInputCurveWordGeodesicTree'),
    ('linear_input/lean_check/CurveWordBVArcUnique.inc', 'LinearInputCurveWordBVArcUnique'),
    ('linear_input/lean_check/CurveWordBVIntrinsic.inc', 'LinearInputCurveWordBVIntrinsic'),
    ('linear_input/lean_check/CurveWordBVIntrinsicTree.inc', 'LinearInputCurveWordBVIntrinsicTree'),
    ('linear_input/lean_check/CurveWordBVHamblyLyons.inc', 'LinearInputCurveWordBVHamblyLyons'),
    ('linear_input/lean_check/CurveWordBVEquivalence.inc', 'LinearInputCurveWordBVEquivalence'),
    ('linear_input/lean_check/CurveWordBVCoordinates.inc', 'LinearInputCurveWordBVCoordinates'),
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", "utf-8")


def canonical_path(relative):
    return (ROOT / "linear_input" / relative).resolve().relative_to(ROOT).as_posix()


def dependency_revisions(expected):
    rows = []
    for package in expected:
        proc = subprocess.run(["git", "rev-parse", "HEAD"],
            cwd=LEAN / ".lake/packages" / package["name"],
            capture_output=True, encoding="utf-8", errors="replace")
        actual = proc.stdout.strip()
        rows.append(dict(name=package["name"], expected=package["expected"], actual=actual,
                         match=proc.returncode == 0 and actual == package["expected"]))
    return rows


def main():
    OUT.mkdir(exist_ok=True)
    report = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(), passed=False,
        baseline_report="linear_input/lean_results.json",
        supplemental_source="linear_input/lean_check/MainResult.inc",
        supplemental_sources=[source for source, _ in SUPPLEMENTS],
        supplemental_groups=[],
        assembled_source="linear_input/lean_check/MainResult.lean",
        assembly="EXTRA_IMPORTS, exact verified All.lean, the recorded instance-priority prelude and each supplemental source in registered order, with approved assembly contexts outside exact source bytes, followed by public axiom audits, direct proof references and the Astra namespace environment audit.",
        assembly_prelude=ASSEMBLY_PRELUDE,
        errors=[], declarations=[], theorem_count=0, declaration_count=0,
        all_declarations=[], total_theorem_count=0, total_declaration_count=0,
        axioms={}, unexpected=[], forbidden_tokens=[], warnings=[],
        source_hashes={}, changed_during_verification=[], dependencies=[],
        baseline_axioms_match=False, joint_axiom_audit=False, compile=None,
        astra_source_audit=None, astra_proof_dependencies=None, astra_environment_audit=None)
    log_path = OUT / "main-result.log"
    log_path.write_text("Supplemental verification has not yet compiled.\n", "utf-8")
    try:
        baseline_path = ROOT / report["baseline_report"]
        baseline = json.loads(baseline_path.read_text("utf-8"))
        if not baseline["passed"]:
            raise ValueError("The unchanged baseline verifier did not pass")
        if baseline["compile"]["exit_code"] != 0 or baseline["parent_library_build"]["exit_code"] != 0:
            raise ValueError("The baseline build or joint compile failed")
        original = [{**d, "file": canonical_path(d["file"])}
                    for d in baseline["parent_declarations"] + baseline["declarations"]]
        original_axioms = {**baseline["parent_axioms"], **baseline["axioms"]}
        hashes = {canonical_path(rel): digest for rel, digest in baseline["source_sha256"].items()}
        stale = [rel for rel, digest in hashes.items()
                 if not (ROOT / rel).is_file() or sha(ROOT / rel) != digest]
        if stale:
            raise ValueError("Stale baseline source hashes: " + ", ".join(stale))
        if len(original_axioms) != len(original) or set(original_axioms) != {d["name"] for d in original}:
            raise ValueError("The baseline axiom audit is incomplete")
        if not all(package["match"] for package in baseline["dependencies"]):
            raise ValueError("The baseline dependency revisions did not pass")
        report["dependencies"] = dependency_revisions(baseline["dependencies"])
        if not all(package["match"] for package in report["dependencies"]):
            raise ValueError("A pinned dependency revision changed after the baseline check")

        astra_spec = importlib.util.spec_from_file_location("astra_physics_audit", ROOT / "tools/check_astra_physics.py")
        astra = importlib.util.module_from_spec(astra_spec)
        astra_spec.loader.exec_module(astra)
        report["astra_source_audit"] = astra.audit(ROOT)
        if not report["astra_source_audit"]["passed"]:
            raise ValueError("Astra source/provenance audit failed: " + repr(report["astra_source_audit"]["errors"]))
        astra_manifest = json.loads((ROOT / "docs/astra/manifest.json").read_text("utf-8"))
        report["assembly_contexts"] = astra_manifest.get("assembly_contexts", [])
        astra_inputs = ["tools/check_astra_physics.py", "docs/astra/manifest.json",
                        astra_manifest["bridge_contract"]["preserved_copy"]]
        astra_inputs += [row["preserved_copy"] for row in astra_manifest["modules"]]
        astra_inputs += [astra.contract_path(row) for row in astra_manifest.get("additional_bridge_contracts", [])]
        for rel in astra_inputs:
            hashes[rel] = sha(ROOT / rel)

        spec = importlib.util.spec_from_file_location("common_verifier", ROOT / "tools/verify.py")
        common = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(common)
        supplement_bytes = []
        for source, namespace in SUPPLEMENTS:
            raw = (ROOT / source).read_bytes()
            supplement_bytes.append(astra.assembly_fragment(source, raw, report["assembly_contexts"]))
            hashes[source] = hashlib.sha256(raw).hexdigest()
            code = common.strip_comments_strings(raw.decode("utf-8"))
            if not Path(source).stem.startswith('Astra'):
                namespaces = re.findall(r"(?m)^namespace\s+([^\s]+)", code)
                if namespaces != [namespace]:
                    raise ValueError(source + " must use the sole namespace " + namespace)
            if re.search(r"(?m)^\s*import\b", code):
                raise ValueError(source + " must use the imports already present in All.lean")
            for found in re.finditer(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code):
                report["forbidden_tokens"].append(dict(file=source,
                    token=found.group(), line=code.count("\n", 0, found.start()) + 1))
            if Path(source).stem.startswith('Astra'):
                declarations = astra.source_declarations(raw.decode('utf-8'), namespace, source)
            else:
                declarations = []
                for found in re.finditer(
                        r"(?m)^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([^\s({:]+)",
                        code):
                    declarations.append(dict(name=namespace + "." + found.group(2),
                        kind=found.group(1), file=source,
                        line=code.count("\n", 0, found.start()) + 1))
            if not declarations:
                raise ValueError("No supplemental public declarations found in " + source)
            report["supplemental_groups"].append(dict(
                source=source, namespace=namespace, declarations=declarations,
                theorem_count=sum(d["kind"] in ("theorem", "lemma") for d in declarations),
                declaration_count=len(declarations), sha256=hashes[source]))
            report["declarations"].extend(declarations)
        all_declarations = original + report["declarations"]
        if len({d["name"] for d in all_declarations}) != len(all_declarations):
            raise ValueError("Duplicate declaration names in the combined audit")
        report.update(theorem_count=sum(d["kind"] in ("theorem", "lemma") for d in report["declarations"]),
            declaration_count=len(report["declarations"]), all_declarations=all_declarations,
            total_theorem_count=sum(d["kind"] in ("theorem", "lemma") for d in all_declarations),
            total_declaration_count=len(all_declarations),
            baseline_theorem_count=baseline["theorem_count"] + baseline["parent_theorem_count"],
            baseline_declaration_count=len(original), version=baseline["version"])
        if report["forbidden_tokens"]:
            raise ValueError("Forbidden proof tokens in the supplemental source")

        # Preserve every input byte for byte, including its original newlines.
        assembled = ("".join(f"import {m}\n" for m in EXTRA_IMPORTS).encode("utf-8") +
            b"\n".join([(PROOFS / "All.lean").read_bytes(),
                         ASSEMBLY_PRELUDE.encode("utf-8"), *supplement_bytes])
            + b"\n\n-- Audit the additive proof declarations.\n"
            + ("\n".join("#print axioms " + d["name"] for d in report["declarations"]) + "\n").encode("utf-8")
            + astra.proof_edge_commands(ROOT).encode("utf-8")
            + astra.environment_audit_commands(ROOT).encode("utf-8"))
        (ROOT / report["assembled_source"]).write_bytes(assembled)
        for rel in (report["baseline_report"], report["assembled_source"],
                    "tools/verify_main_result.py", "tools/verify.py", "tools/check_delivery.py"):
            hashes[rel] = sha(ROOT / rel)
        report["source_hashes"] = hashes
        started = time.monotonic()
        command = ["lake", "env", "lean", "--trust=0", "../linear_input/lean_check/MainResult.lean"]
        proc = subprocess.run(command, cwd=LEAN, capture_output=True,
                              encoding="utf-8", errors="replace")
        log = proc.stdout + proc.stderr
        log_path.write_text(log, "utf-8")
        report["compile"] = dict(command=command, working_directory=str(LEAN), exit_code=proc.returncode,
            seconds=round(time.monotonic() - started, 3), log="verification/main-result.log")
        report["warnings"] = [line for line in log.splitlines() if re.search(r"\bwarning:", line)]
        report["astra_proof_dependencies"] = astra.audit_proof_edges(ROOT, log)
        report["astra_environment_audit"] = astra.audit_environment(ROOT, log)
        for declaration in all_declarations:
            name = declaration["name"]
            matches = re.findall("'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]", log, re.S)
            no_axioms = log.count("'" + name + "' does not depend on any axioms")
            if len(matches) + no_axioms != 1:
                report["unexpected"].append(name + ": missing or duplicate audit result")
                continue
            axioms = [item.strip() for item in matches[0].split(",") if item.strip()] if matches else []
            report["axioms"][name] = axioms
            report["unexpected"].extend(name + ": " + ax for ax in axioms if ax not in ALLOWED)
        report["baseline_axioms_match"] = all(report["axioms"].get(name) == axioms
                                              for name, axioms in original_axioms.items())
        report["joint_axiom_audit"] = len(report["axioms"]) == len(all_declarations)
        report["changed_during_verification"] = [rel for rel, digest in hashes.items()
            if not (ROOT / rel).is_file() or sha(ROOT / rel) != digest]
        after_dependencies = dependency_revisions(baseline["dependencies"])
        report["dependencies_after_compile"] = after_dependencies
        if proc.returncode != 0:
            report["errors"].append("Supplemental joint compilation failed")
        if report["warnings"]:
            report["errors"].append("Lean emitted warnings")
        if not report["astra_proof_dependencies"]["passed"]:
            report["errors"].append("Astra elaborated proof dependency audit failed")
        if not report["astra_environment_audit"]["passed"]:
            report["errors"].append("Astra environment axiom audit failed")
        if report["unexpected"] or not report["joint_axiom_audit"] or not report["baseline_axioms_match"]:
            report["errors"].append("Supplemental joint axiom audit failed")
        if report["changed_during_verification"]:
            report["errors"].append("Verified inputs changed during compilation")
        if not all(package["match"] for package in after_dependencies):
            report["errors"].append("A dependency revision changed during compilation")
        report["passed"] = not report["errors"]
    except (OSError, ValueError, KeyError, TypeError) as error:
        report["errors"].append(str(error))
    report["log_sha256"] = sha(log_path)
    report["scope"] = ("The original checker and its 60 proof sources remain unchanged. "
        "This second --trust=0 compilation audits the original declarations, the additive main result "
        "and the general fixed-input minimum, support composition, quartic classification and curvature rigidity criteria "
        "in one assembled Lean session. It verifies proofs, not numerical simulations or browser rendering.")
    write_json(OUT / "main-result.json", report)
    print(json.dumps({key: report[key] for key in ("passed", "theorem_count", "declaration_count",
        "total_theorem_count", "total_declaration_count", "compile", "errors", "unexpected",
        "warnings", "forbidden_tokens", "changed_during_verification")}, ensure_ascii=False, indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
