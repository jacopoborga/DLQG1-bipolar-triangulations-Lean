module

public import DirectedDistances.PlanarMap.D39FacedBallClass
public import DirectedDistances.PaperProofs.Section3.D39DistanceZero

/-! Supporting lemmas for paper labels `def-bs-topology` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap
open scoped ENNReal






theorem d39RootedBallSystem_distance_eq_source_formula
    (M N : D39RootedMap) :
    RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem M N =
      ⨅ r : ℕ, ⨅ (_ : d39BallClass M (r + 1) (Nat.succ_pos r) =
        d39BallClass N (r + 1) (Nat.succ_pos r)),
        (2 : ℝ≥0∞)⁻¹ ^ (r + 1) := by
  rfl





theorem d39RootedBallSystem_distance_eq_zero_iff
    (M N : D39RootedMap) :
    RootedBallSystem.bsLocalDistanceGeneric d39RootedBallSystem M N = 0 ↔
      ∀ r : ℕ, d39BallClass M (r + 1) (Nat.succ_pos r) =
        d39BallClass N (r + 1) (Nat.succ_pos r) := by
  exact RootedBallSystem.bsLocalDistance_eq_zero_iffGeneric
    d39RootedBallSystem M N

end DirectedDistances.PaperProofs.Section3
