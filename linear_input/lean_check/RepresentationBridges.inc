/-!
Exact identifications between retained, independently developed PR models.

These equalities connect the actual definitions, not merely matching
determinants, ranks, Jacobian signs, or finite numerical examples.
The F16 block decomposition uses separate row and column permutations;
that matrix equivalence is not claimed to be conjugacy.
-/

namespace LinearInputRepresentationBridges

/-- The two real F16 families have exactly the same original table entries. -/
theorem leftMatrix_eq_realPencilAll (t : ℝ) :
    LinearInputF16FullMatrix.leftMatrix t =
      LinearInputF16Determinant.realPencilAll t := rfl

/-- The integer families also agree before any scalar extension. -/
theorem leftMatrixInt_eq_intPencil (t : ℤ) :
    LinearInputF16FullMatrix.leftMatrixInt t =
      LinearInputF16Rank.intPencil t := rfl

/-- The independently described row orderings are the same function. -/
theorem rowOrder_eq_rowCoord :
    LinearInputF16FullMatrix.rowOrder = LinearInputF16Determinant.rowCoord := rfl

/-- The independently described column orderings are the same function. -/
theorem colOrder_eq_colCoord :
    LinearInputF16FullMatrix.colOrder = LinearInputF16Determinant.colCoord := rfl

/-- Transfer the actual constructive decoder to the alternative matrix API. -/
theorem reconstruct_leftMatrix_observations (v : Fin 16 → ℝ) :
    LinearInputF16ConstructiveRecovery.reconstruct
      ((LinearInputF16FullMatrix.leftMatrix 1).mulVec v,
       (LinearInputF16FullMatrix.leftMatrix (-1)).mulVec v) = v := by
  exact LinearInputF16ConstructiveRecovery.reconstruct_observations v

/-- The two energy branches use the same sign-corrected gradient map. -/
theorem orientedGradient_eq_H (k lam c y : ℝ) :
    LinearInputEnergyGaugeFenchel.orientedGradient k lam c y =
      LinearInputEWFSDual.H k lam c y := rfl

/-- Their stated polynomial inverses are identical as well. -/
theorem orientedInverse_eq_HInv (k lam c y : ℝ) :
    LinearInputEnergyGaugeFenchel.orientedInverse k lam c y =
      LinearInputEWFSDual.HInv k lam c y := rfl

end LinearInputRepresentationBridges
