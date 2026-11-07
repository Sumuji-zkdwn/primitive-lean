import ElasticaUnifiedOperatorAdapter
import ElasticaCurveDistinct
import ElasticaFixedBoundaryEnergy
import Lean.Util.FoldConsts

open Lean Elab Command

def projectProofPath (env : Environment) (start goal : Name) : Option (Array Name) := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut pending : Array (Name × Array Name) := #[(start, #[start])]
  let mut index := 0
  while index < pending.size do
    let (current, path) := pending[index]!
    index := index + 1
    if current == goal then return some path
    if !visited.contains current then
      visited := visited.insert current
      match env.find? current with
      | some (.thmInfo info) =>
        for child in info.value.getUsedConstants do
          let name := child.toString
          if name.startsWith "LinearInput" || name.startsWith "Elastica" ||
              name.startsWith "FixedBoundary" then
            if !visited.contains child then
              pending := pending.push (child, path.push child)
      | _ => pure ()
  return none

/- Inspect named constants in accepted proof bodies, not just axiom sets.
   Each check is direct; it is not a complete transitive dependency graph. -/
run_cmd do
  let env ← getEnv
  let checks : Array (Name × Name) := #[
    (⟨`LinearInputElasticaOperatorBridge.elastica_quotient_splits,
      `LinearInputOperatorRefinement.strict_refinement_splits_quotient⟩),
    (⟨`LinearInputElasticaOperatorBridge.observer_zero, `Elastica.xCoord_const⟩),
    (⟨`LinearInputElasticaOperatorBridge.observer_one, `Elastica.xCoord_const⟩),
    (⟨`LinearInputElasticaOperatorBridge.observer_two, `Elastica.xCoord_const⟩),
    (⟨`LinearInputElasticaOperatorBridge.observer_three, `Elastica.xCoord_const⟩),
    (⟨`LinearInputElasticaOperatorBridge.elastica_quotient_splits,
      `LinearInputElasticaOperatorBridge.old_indistinguishable⟩),
    (⟨`LinearInputElasticaOperatorBridge.elastica_quotient_splits,
      `LinearInputElasticaOperatorBridge.new_distinguishes⟩),
    (⟨`ElasticaObservationBridge.K_zero, `Elastica.curvature_const⟩),
    (⟨`ElasticaObservationBridge.K_one, `Elastica.curvature_const⟩),
    (⟨`ElasticaObservationBridge.K_two, `Elastica.curvature_affine⟩),
    (⟨`ElasticaObservationBridge.curve_split,
      `ElasticaObservationBridge.strict_refinement_splits_quotient⟩),
    (⟨`ElasticaObservationBridge.curve_split,
      `ElasticaObservationBridge.old_cannot_separate⟩),
    (⟨`ElasticaObservationBridge.curve_split,
      `ElasticaObservationBridge.fresh_separates⟩),
    (⟨`ElasticaObservationBridge.old_cannot_separate,
      `ElasticaObservationBridge.K_one⟩),
    (⟨`ElasticaObservationBridge.fresh_separates, `ElasticaObservationBridge.K_two⟩),
    (⟨`FixedBoundaryWitness.fixed_boundary_quotient_splits,
      `LinearInputOperatorRefinement.strict_refinement_splits_quotient⟩),
    (⟨`FixedBoundaryWitness.represented_curve_split,
      `LinearInputOperatorRefinement.strict_refinement_splits_quotient⟩),
    (⟨`FixedBoundaryWitness.unit_speed, `Elastica.unit_speed_squared⟩),
    (⟨`FixedBoundaryCurveDistinct.same_coordinates_same_curvature,
      `Elastica.signed_curvature_eq_deriv⟩),
    (⟨`FixedBoundaryExactEnergy.exact_represented_realization,
      `FixedBoundaryWitness.represented_curve_split⟩),
    (⟨`FixedBoundaryExactEnergy.exact_represented_realization,
      `FixedBoundaryExactEnergy.represented_curve_energy⟩)
  ]
  for (source, target) in checks do
    let some info := env.find? source | throwError "missing declaration {source}"
    let some val := info.value? (allowOpaque := true) |
      throwError "no proof body for {source}"
    unless val.getUsedConstants.contains target do
      throwError "missing direct proof edge {source} -> {target}"
    logInfo m!"proof edge: {source} -> {target}"

  let paths : Array (Name × Name) := #[
    (⟨`LinearInputElasticaOperatorBridge.elastica_quotient_splits,
      `Elastica.xCoord_const⟩),
    (⟨`ElasticaObservationBridge.curve_split, `Elastica.curvature_const⟩),
    (⟨`ElasticaObservationBridge.curve_split, `Elastica.curvature_affine⟩),
    (⟨`FixedBoundaryExactEnergy.exact_represented_realization,
      `Elastica.unit_speed_squared⟩),
    (⟨`FixedBoundaryExactEnergy.exact_represented_realization,
      `LinearInputOperatorRefinement.strict_refinement_splits_quotient⟩),
    (⟨`FixedBoundaryCurveDistinct.coordinates_injective,
      `Elastica.signed_curvature_eq_deriv⟩)
  ]
  for (source, target) in paths do
    let some path := projectProofPath env source target |
      throwError "missing theorem-body path {source} -> {target}"
    logInfo m!"proof path: {path.toList}"
