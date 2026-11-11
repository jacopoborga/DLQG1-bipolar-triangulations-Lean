/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.WholePlanePastGlueData
public import DirectedDistances.PlanarMap.PLDrawingFaceTransfer

public section

namespace DirectedDistances.KMSW.WholePlanePastGlueData

open DirectedDistances.PlanarMap

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "wp" => kmswPastCode W
local notation "Pp" => monotoneFamilyDrawing wp (past_finiteIncidence W H)
  (monotone_family_all wp)
local notation "Pt" => pastDrawing W h0 hp H
local notation "T" => PastDrawingTransfer.transfer (shiftedStream W 0) wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)

/-- not a paper result. The face transfers, and its border predicate is the target wedge
pulled back by the inverse transfer. -/
theorem pastDrawing_dartBorders_inverseWedge (d : ℕ × Bool) (F : (Pp).Face) :
    ∃ Ft : (Pt).Face, Ft.val = T '' F.val ∧
      ((Pt).dartBorders d Ft ↔
        ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ, 0 < t → t < δ → 0 < ε → ε < δ →
          (T).symm (((Pt).arc d).start + (t : ℂ) *
            (((Pt).arc d).initialDirection + (ε : ℂ) * Complex.I *
              ((Pt).arc d).initialDirection)) ∈ F.val) := by
  obtain ⟨_, hfaces, _⟩ := PLDrawing.face_image_of_transfer Pp T Pt
    (pastDrawing_pos W h0 hp H)
    (fun e => (pastDrawing_arc W h0 hp H e).1)
  obtain ⟨Ft, hFt⟩ := hfaces F
  refine ⟨Ft, hFt, ?_⟩
  unfold PLDrawing.dartBorders
  rw [hFt]
  constructor
  · rintro ⟨δ, hδ, hw⟩
    refine ⟨δ, hδ, ?_⟩
    intro t ε ht htδ hε hεδ
    obtain ⟨x, hx, hxt⟩ := hw t ε ht htδ hε hεδ
    have hxt' := congrArg (T).symm hxt
    rw [(T).symm_apply_apply] at hxt'
    exact hxt' ▸ hx
  · rintro ⟨δ, hδ, hw⟩
    refine ⟨δ, hδ, ?_⟩
    intro t ε ht htδ hε hεδ
    let z := ((Pt).arc d).start + (t : ℂ) *
      (((Pt).arc d).initialDirection + (ε : ℂ) * Complex.I *
        ((Pt).arc d).initialDirection)
    refine ⟨(T).symm z, hw t ε ht htδ hε hεδ, ?_⟩
    exact (T).apply_symm_apply z

end DirectedDistances.KMSW.WholePlanePastGlueData
