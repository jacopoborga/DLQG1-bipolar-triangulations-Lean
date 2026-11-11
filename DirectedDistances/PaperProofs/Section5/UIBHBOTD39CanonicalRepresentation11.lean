/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation9

/-! Helper toward Proposition 5.16.

This module identifies the assembly's PL border relation with its
face-successor orbits and transfers the frontier incidence characterization
to the canonical drawing representation. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults

/-- Helper toward Proposition 5.16. A dart borders the assembly face of `d`
exactly when it lies in the same face-successor cycle as `d`. -/
theorem uibhbotD39Assembly_dartBorders_iff_faceCycle
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (d e : WholePlaneDart W) :
    let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
    let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
    let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
    let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
    let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa
    let A := uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa D.pastRightPositive
    G.dartBorders e (A (Quotient.mk _ d)) ↔
      (wholePlaneFaceSucc W D.rotation).SameCycle d e := by
  let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
  let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
  let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
  let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa
  let A := uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa D.pastRightPositive
  change G.dartBorders e (A (Quotient.mk _ d)) ↔ _
  constructor
  · intro hborder
    have hface : A (Quotient.mk _ e) = A (Quotient.mk _ d) :=
      G.dartBorders_face_unique e _ _
        (uibhbotD39Assembly_faceOrbitEquiv_dartBorders W D e) hborder
    have hquot : Quotient.mk
        (Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W D.rotation)) e =
        Quotient.mk _ d := A.injective hface
    exact (Quotient.exact hquot).symm
  · intro hcycle
    have hquot : Quotient.mk
        (Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W D.rotation)) d =
        Quotient.mk _ e := Quotient.sound hcycle
    have hface : A (Quotient.mk _ d) = A (Quotient.mk _ e) := congrArg A hquot
    rw [hface]
    exact uibhbotD39Assembly_faceOrbitEquiv_dartBorders W D e

/-- Helper toward Proposition 5.16. A whole-plane vertex is on the frontier
of the assembly face of `d` exactly when it is the initial vertex of a dart
in `d`'s face-successor cycle. -/
theorem uibhbotD39Assembly_vertex_frontier_iff_faceCycle
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (d : WholePlaneDart W) (v : WholePlaneVertex W) :
    let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence
    let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
    let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
    let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
    let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
    let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa
    let A := uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
      D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
      P hp ha F hf hFim hFa D.pastRightPositive
    G.pos v ∈ frontier (A (Quotient.mk _ d)).val ↔
      ∃ e : WholePlaneDart W,
        (wholePlaneFaceSucc W D.rotation).SameCycle d e ∧
          wholePlaneDartVertex W e = v := by
  let P := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let F := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
  let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
  let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
  let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa
  let A := uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P hp ha F hf hFim hFa D.pastRightPositive
  have hvert : Function.Surjective (wholePlaneDartVertex W) :=
    uibhbot_faceOrbit_dartVertex_surjective W D.rotation
  constructor
  · intro hfront
    rw [G.frontier_face_eq_iUnion_dartBorders_arcs_of_locallyFinite hvert _] at hfront
    rcases Set.mem_iUnion.mp hfront with ⟨e, hfront⟩
    rcases Set.mem_iUnion.mp hfront with ⟨hborder, hpoint⟩
    have hcycle : (wholePlaneFaceSucc W D.rotation).SameCycle d e := by
      exact (uibhbotD39Assembly_dartBorders_iff_faceCycle W D d e).mp hborder
    have hend : G.pos v = (G.arc e).start ∨ G.pos v = (G.arc e).finish := by
      by_contra hnot
      have hstart : G.pos v ≠ (G.arc e).start := fun h => hnot (Or.inl h)
      have hfinish : G.pos v ≠ (G.arc e).finish := fun h => hnot (Or.inr h)
      have hinterior : G.pos v ∈ (G.arc e).interior := by
        refine ⟨hpoint, ?_⟩
        intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx
        · exact hstart hx
        · exact hfinish hx
      exact G.interior_avoids_vertices e v hinterior
    rcases hend with hstart | hfinish
    · have hv : wholePlaneDartVertex W e = v := by
        exact (G.pos_injective (hstart.trans (G.arc_start e))).symm
      exact ⟨e, hcycle, hv⟩
    · have hv : wholePlaneDartVertex W (wholePlaneDartFlip W e) = v := by
        exact (G.pos_injective (hfinish.trans (G.arc_finish e))).symm
      have hnext :
          wholePlaneDartVertex W (wholePlaneFaceSucc W D.rotation e) =
            wholePlaneDartVertex W (wholePlaneDartFlip W e) := by
        have hrot (x : WholePlaneDart W) :
            wholePlaneDartVertex W ((wholePlaneRotation W D.rotation).symm x) =
              wholePlaneDartVertex W x := by
          have h := wholePlaneRotation_preserves_dartVertex W D.rotation
            ((wholePlaneRotation W D.rotation).symm x)
          simpa using h.symm
        simp [wholePlaneFaceSucc, Equiv.Perm.mul_apply, hrot]
      refine ⟨wholePlaneFaceSucc W D.rotation e, ?_, hnext.trans hv⟩
      exact hcycle.trans (Equiv.Perm.SameCycle.rfl.apply_right)
  · rintro ⟨e, hcycle, hv⟩
    have hborder : G.dartBorders e (A (Quotient.mk _ d)) :=
      (uibhbotD39Assembly_dartBorders_iff_faceCycle W D d e).mpr hcycle
    have hsubset := G.dartBorders_arc_subset_frontier hvert e
      (A (Quotient.mk _ d)) hborder
    have hstart : (G.arc e).start = G.pos v := by
      calc
        (G.arc e).start = G.pos (wholePlaneDartVertex W e) := G.arc_start e
        _ = G.pos v := congrArg G.pos hv
    exact hsubset (Or.inl hstart.symm)






























































end DirectedDistances.PaperProofs.Section5

end
