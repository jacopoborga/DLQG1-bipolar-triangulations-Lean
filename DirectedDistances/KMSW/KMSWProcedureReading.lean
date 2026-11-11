module

public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariantRotate
public import DirectedDistances.KMSW.KMSWPeanoPrefixInvariantClimb
public import DirectedDistances.KMSW.KMSWPeanoPrefixInduction
public import DirectedDistances.KMSW.KMSWProcedureBijection
public import DirectedDistances.PlanarMap.KMSWMapIsoClass

/-! # The KMSW procedure reading

This file proves the procedure-reading form of `thm-kmsw`
increments `(1,-1)`, `(-1,0)`, and `(0,1)` (`def-kmsw`,
paper result. The single-edge case `n = 1` (`m₀`) is included: the only size
hypothesis is `1 ≤ n`, which permits `n = 1`. No positivity hypotheses on
`ℓ` or `r` are needed by the imported prefix and class-bijection results. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- The final Peano prefix exists for every procedure-reading class.
paper result. -/
theorem kmswPeanoPrefixExistsFinal_holds (ℓ r n : ℕ) :
    KMSWPeanoPrefixExistsFinal ℓ r n := by
  apply kmswPeanoPrefixExistsFinal_of_steps
  · intro R
    exact kmswPeanoRotatePreserves R.B (kmswRepInverseWalkClass R)
  · intro R
    exact kmswPeanoClimbPreserves R.B (kmswRepInverseWalkClass R)

/-- The procedure-reading walk-to-map function is bijective for every
positive total edge count. Procedure reading of `thm-kmsw` -/
theorem thm_kmsw_procedureReading (ℓ r n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (@kmswToMapIsoClass ℓ r n hn) := by
  exact kmswToMapIsoClass_bijective_of_prefix
    (kmswPeanoPrefixExistsFinal_holds ℓ r n) hn

/-- The procedure-reading walk-class and unrooted map-class equivalence.
paper result. It is the same `Equiv.ofBijective` construction as
`kmswProcedureEquivOfPrefix`, applied using the unconditional bijectivity
proved above. -/
@[expose]
noncomputable def kmswProcedureEquiv (ℓ r n : ℕ) (hn : 1 ≤ n) :
    KMSWWalkClass ℓ r n ≃ KMSWMapIsoClass ℓ r n :=
  Equiv.ofBijective (@kmswToMapIsoClass ℓ r n hn)
    (thm_kmsw_procedureReading ℓ r n hn)

/-- The forward map of `kmswProcedureEquiv` is the procedure's walk-to-map
class function. Procedure reading of `thm-kmsw` -/
@[simp] theorem kmswProcedureEquiv_toFun (ℓ r n : ℕ) (hn : 1 ≤ n) :
    (kmswProcedureEquiv ℓ r n hn).toFun =
      @kmswToMapIsoClass ℓ r n hn := rfl

/-- The walk-class and unrooted map-class carriers have equal finite
cardinality in the procedure reading. Procedure reading of `thm-kmsw` -/
theorem kmswProcedure_natCard_eq (ℓ r n : ℕ) (hn : 1 ≤ n) :
    Nat.card (KMSWWalkClass ℓ r n) = Nat.card (KMSWMapIsoClass ℓ r n) := by
  exact kmswToMapIsoClass_natCard_eq_of_prefix
    (kmswPeanoPrefixExistsFinal_holds ℓ r n) hn

end DirectedDistances.KMSW
