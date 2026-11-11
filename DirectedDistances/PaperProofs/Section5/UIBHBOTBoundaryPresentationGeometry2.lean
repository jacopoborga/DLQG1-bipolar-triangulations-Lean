/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTBoundaryPresentationGeometry
public import DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceGeometry2

public section

namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.SourceResults

noncomputable section

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))
  (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
    (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
  (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0))
    (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) '' ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
      (monotone_family_all _)).arc d).image)
  (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)

local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "M" => uibhbotAssemblyDirectedPlaneMapWithMissing
  W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

/-- Helper toward Definition 3.2: the whole-plane assembly dart carrier is
equivalent to the geometric-edge dart carrier used by its presentation. The
quotient's edge coordinate is unchanged and the traversal bit is complemented. -/
@[expose] def uibhbotAssemblyBoundaryDartEquiv :
    WholePlaneDart W ≃ (G).GeometricEdge × Bool where
  toFun d := (Quotient.mk (G).edgeSetoid d, !d.2)
  invFun d := (d.1.out.1, !d.2)
  left_inv d := by
    rcases d with ⟨e, b⟩
    change ((Quotient.mk (G).edgeSetoid (e, b)).out.1, !!b) = (e, b)
    rcases (G).geometricEdge_out_mk (e, b) with h | h
    · rw [h]
      cases b <;> rfl
    · rw [h]
      cases b <;> rfl
  right_inv d := by
    rcases d with ⟨q, b⟩
    change (Quotient.mk (G).edgeSetoid (q.out.1, !b), !!b) = (q, b)
    have hqrep : Quotient.mk (G).edgeSetoid (q.out.1, !b) =
        Quotient.mk (G).edgeSetoid q.out := by
      rcases q.out with ⟨e, c⟩
      cases c <;> cases b
      · exact PLDrawing.geometricEdge_flip G (e, false)
      · rfl
      · rfl
      · exact PLDrawing.geometricEdge_flip G (e, true)
    have hq : Quotient.mk (G).edgeSetoid (q.out.1, !b) = q :=
      hqrep.trans (Quotient.out_eq q)
    apply Prod.ext
    · exact hq
    · cases b <;> rfl

/-- Helper toward Definition 3.2: the assembly dart equivalence commutes with
reversal on both carrier conventions. -/
theorem uibhbotAssemblyBoundaryDartEquiv_flip (d : WholePlaneDart W) :
    uibhbotAssemblyBoundaryDartEquiv W H h0 hL hR hfin P hp ha F hf hFim hFa
      (wholePlaneDartFlip W d) =
      ((uibhbotAssemblyBoundaryDartEquiv W H h0 hL hR hfin P hp ha F hf hFim hFa
        d).1,
        !((uibhbotAssemblyBoundaryDartEquiv W H h0 hL hR hfin P hp ha F hf hFim hFa
          d).2)) := by
  rcases d with ⟨e, b⟩
  simp only [uibhbotAssemblyBoundaryDartEquiv, wholePlaneDartFlip]
  exact Prod.ext (PLDrawing.geometricEdge_flip G (e, b)) rfl

/-- Helper toward Definition 3.2: transport the whole-plane rotation to the
presentation dart carrier by conjugation. -/
@[expose] def uibhbotAssemblyBoundaryDartRotation :
    Equiv.Perm ((G).GeometricEdge × Bool) :=
  uiqbotTransportRotation (uibhbotAssemblyBoundaryDartEquiv W H h0 hL hR hfin P hp ha
    F hf hFim hFa).symm (wholePlaneRotation W H)

/-- Helper toward Definition 3.2: the transported rotation commutes with the
assembly dart equivalence. -/
theorem uibhbotAssemblyBoundaryDartEquiv_rotation (d : WholePlaneDart W) :
    uibhbotAssemblyBoundaryDartRotation W H h0 hL hR hfin P hp ha F hf hFim hFa
      (uibhbotAssemblyBoundaryDartEquiv W H h0 hL hR hfin P hp ha F hf hFim hFa d) =
      uibhbotAssemblyBoundaryDartEquiv W H h0 hL hR hfin P hp ha F hf hFim hFa
        (wholePlaneRotation W H d) := by
  simp [uibhbotAssemblyBoundaryDartRotation, uiqbotTransportRotation]





























































end
end DirectedDistances.PaperProofs.Section5

end
