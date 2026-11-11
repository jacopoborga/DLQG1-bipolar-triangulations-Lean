/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.KMSWFiniteBoundaryPresentation2
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRepresentation3




public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: a finite-index successor is exactly a
one-step increase of its integer position. -/
private theorem kmswFiniteRun_step_position_iff {m : ℕ} (i j : Fin m) :
    (∃ h : i.val + 1 < m, (⟨i.val + 1, h⟩ : Fin m) = j) ↔
      (j.val : ℤ) = (i.val : ℤ) + 1 := by
  constructor
  · rintro ⟨_, heq⟩
    have hv := congrArg Fin.val heq
    exact_mod_cast hv.symm
  · intro h
    have hj := j.isLt
    have hlt : i.val + 1 < m := by omega
    refine ⟨hlt, ?_⟩
    apply Fin.ext
    exact_mod_cast h.symm

/-- Helper toward Definition 3.2: the four finite KMSW dart runs admit the
gapless integer order given by their concatenated outer-word offsets. -/
theorem kmswStage_finite_boundary_positionOrder3
    (w : ℕ → Fin 3) (n : ℕ)
    (M : DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex)
      (Fin (kmswStage w n).nextEdge))
    (J : FiniteBoundaryJunctions (Fin (kmswStage w n).nextVertex)) :
    BoundaryPositionOrder3 (kmswStageFiniteBoundaryPresentation w n M J) := by
  let P := kmswStageFiniteBoundaryPresentation w n M J
  let a := (kmswStageULDartRun w n).length
  let b := (kmswStageURDartRun w n).length
  let c := (kmswStageLRDartRun w n).length
  let d := (kmswStageLLDartRun w n).length
  let position := kmswStageFiniteBoundaryPosition w n M J
  refine ⟨position, ?_⟩
  unfold IsBoundaryPositionOrder3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    cases i <;> cases j <;>
      simp [position, kmswStageFiniteBoundaryPosition, a, b, c, d] at hij ⊢ <;>
      first | (apply Fin.ext; omega) | omega
  · intro i j htag
    cases i <;> cases j <;>
      simp [position, kmswStageFiniteBoundaryPresentation,
        kmswStageFiniteBoundaryPosition, kmswFiniteRunSide, kmswFiniteRunNext,
        sideNext, sideTag, a, b, c, d] at htag ⊢
    all_goals
      cases htag
    all_goals
      rename_i j i
      constructor
      · rintro ⟨hlt, heq⟩
        injection heq with hfin
        have hv := congrArg Fin.val hfin
        change j.val + 1 = i.val at hv
        omega
      · intro hpos
        have hval : j.val + 1 = i.val := by omega
        have hi := i.isLt
        refine ⟨by omega, ?_⟩
        apply congrArg _
        apply Fin.ext
        exact hval
  · intro i j z hiz hzj
    have hzlo : 0 ≤ z := by
      cases i <;>
        simp [position, kmswStageFiniteBoundaryPosition, a, b, c, d] at hiz <;>
        omega
    have hzhi : z < ((a + b + c + d : ℕ) : ℤ) := by
      cases j <;>
        simp [position, kmswStageFiniteBoundaryPosition, a, b, c, d] at hzj <;>
        omega
    by_cases ha : z < (a : ℤ)
    · refine ⟨.upperLeft ⟨z.toNat, ?_⟩, ?_⟩
      · exact_mod_cast (show (z.toNat : ℤ) < (a : ℤ) by
          rw [Int.toNat_of_nonneg hzlo]
          exact ha)
      · simp [position, kmswStageFiniteBoundaryPosition,
          Int.toNat_of_nonneg hzlo]
    · by_cases hab : z < ((a + b : ℕ) : ℤ)
      · have hq0 : 0 ≤ z - (a : ℤ) := by omega
        refine ⟨.upperRight ⟨(z - (a : ℤ)).toNat, ?_⟩, ?_⟩
        · exact_mod_cast (show ((z - (a : ℤ)).toNat : ℤ) < (b : ℤ) by
            rw [Int.toNat_of_nonneg hq0]
            omega)
        · simp [position, kmswStageFiniteBoundaryPosition,
            Int.toNat_of_nonneg hq0]
          omega
      · by_cases habc : z < ((a + b + c : ℕ) : ℤ)
        · have hq0 : 0 ≤ z - ((a + b : ℕ) : ℤ) := by omega
          refine ⟨.lowerRight ⟨(z - ((a + b : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩
          · exact_mod_cast (show ((z - ((a + b : ℕ) : ℤ)).toNat : ℤ) < (c : ℤ) by
              rw [Int.toNat_of_nonneg hq0]
              omega)
          · simp [position, kmswStageFiniteBoundaryPosition,
              Int.toNat_of_nonneg hq0]
            omega
        · have hq0 : 0 ≤ z - ((a + b + c : ℕ) : ℤ) := by omega
          refine ⟨.lowerLeft ⟨(z - ((a + b + c : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩
          · exact_mod_cast (show ((z - ((a + b + c : ℕ) : ℤ)).toNat : ℤ) < (d : ℤ) by
              rw [Int.toNat_of_nonneg hq0]
              omega)
          · simp [position, kmswStageFiniteBoundaryPosition,
              Int.toNat_of_nonneg hq0]
            omega
  · intro i j k hij hjk htag
    cases i <;> cases j <;> cases k <;>
      simp [P, position, kmswStageFiniteBoundaryPresentation,
        kmswStageFiniteBoundaryPosition, kmswFiniteRunSide, sideTag,
        a, b, c, d] at * <;>
      omega
  · intro i j k hij hjk htag₁ htag₂ htag₃
    cases i <;> cases j <;> cases k <;>
      simp [P, position, kmswStageFiniteBoundaryPresentation,
        kmswStageFiniteBoundaryPosition, kmswFiniteRunSide, sideTag,
        sideDistance, a, b, c, d] at * <;>
      omega

end DirectedDistances.PaperProofs.Section3
