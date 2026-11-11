/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59D39GeomMirrorCompat
public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation11

/-! Helper toward Proposition 5.9 (`prop-uihbot-sym`).

For the canonical whole-plane UIBHBOT map, the assembly drawing supplies the
actual complementary components, the face-orbit quotient, its frontier
incidences, the retained-face criterion, and its marked unbounded face. This
is only the face-correspondence helper; it does not prove Proposition 5.9. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.9. The assembly faces are precisely the
complementary components for the canonical UIBHBOT local topology map, with the exact
face-cycle, frontier-vertex, positive-radius retained-face, and unbounded
outer-face clauses of the face-correspondence predicate. -/
theorem uibhbotD39CanonicalAssembly_planeFaceCorrespondence
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0) :
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
    let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
    prop59D39PlaneFaceCorrespondenceOpen M G.image
      (fun v => G.pos (wholePlaneDartVertex W (Quotient.out v)))
      (fun d => (A (Quotient.mk _ d)).val) := by
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
  let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  let vertexPos : RootedLocallyFiniteVertex M.core.D M.core.rot → ℂ :=
    fun v => G.pos (wholePlaneDartVertex W (Quotient.out v))
  let leftFace : M.core.D → Set ℂ := fun d => (A (Quotient.mk _ d)).val
  have hvertexClass (d e : WholePlaneDart W) :
      d39VertexClass M d = d39VertexClass M e ↔
        wholePlaneDartVertex W d = wholePlaneDartVertex W e := by
    change rootedLocallyFiniteVertexClass (wholePlaneRotation W D.rotation) d =
        rootedLocallyFiniteVertexClass (wholePlaneRotation W D.rotation) e ↔ _
    constructor
    · intro h
      exact (wholePlaneRotation_sameCycle_dartVertex W D.rotation d e
        (Quotient.exact h)).symm
    · intro h
      exact Quotient.sound
        (wholePlaneRotation_sameVertex_sameCycle_proof W D.rotation d e h)
  have hvertexPos (d : WholePlaneDart W) :
      vertexPos (d39VertexClass M d) = G.pos (wholePlaneDartVertex W d) := by
    change G.pos (wholePlaneDartVertex W
      (Quotient.out (d39VertexClass M d))) = _
    have hclass : rootedLocallyFiniteVertexClass (wholePlaneRotation W D.rotation)
        (Quotient.out (d39VertexClass M d)) = d39VertexClass M d :=
      Quotient.out_eq' (d39VertexClass M d)
    have hcycle := Quotient.exact hclass
    exact congrArg G.pos
      (wholePlaneRotation_sameCycle_dartVertex W D.rotation
        (Quotient.out (d39VertexClass M d)) d hcycle).symm
  have hfrontier : ∀ d v,
      vertexPos v ∈ frontier (leftFace d) ↔
        ∃ e, Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e ∧
          d39VertexClass M e = v := by
    intro d v
    let e₀ : WholePlaneDart W := Quotient.out v
    have hv₀ : d39VertexClass M e₀ = v := Quotient.out_eq' v
    have hrep := uibhbotD39Assembly_vertex_frontier_iff_faceCycle
      W D d (wholePlaneDartVertex W e₀)
    change G.pos (wholePlaneDartVertex W e₀) ∈
        frontier (A (Quotient.mk _ d)).val ↔ _
    change (G.pos (wholePlaneDartVertex W e₀) ∈
      frontier (A (Quotient.mk _ d)).val ↔
      ∃ e, (wholePlaneFaceSucc W D.rotation).SameCycle d e ∧
        wholePlaneDartVertex W e = wholePlaneDartVertex W e₀) at hrep
    constructor
    · intro h
      obtain ⟨e, hecycle, hevertex⟩ := hrep.mp h
      refine ⟨e, ?_, ?_⟩
      · exact hecycle
      · exact (hvertexClass e e₀).2 hevertex |>.trans hv₀
    · rintro ⟨e, hecycle, heclass⟩
      apply hrep.mpr
      refine ⟨e, hecycle, ?_⟩
      apply (hvertexClass e e₀).1
      exact heclass.trans hv₀.symm
  dsimp only [prop59D39PlaneFaceCorrespondenceOpen]
  refine ⟨?_, ?_, ?_, hfrontier, ?_, ?_⟩
  · intro d
    exact (A (Quotient.mk _ d)).property
  · intro z hz
    let Fz : G.Face := ⟨connectedComponentIn G.imageᶜ z, z, hz, rfl⟩
    obtain ⟨q, hq⟩ := A.surjective Fz
    revert hq
    refine Quotient.inductionOn q ?_
    intro d hq
    refine ⟨d, ?_⟩
    change (A (Quotient.mk _ d)).val = connectedComponentIn G.imageᶜ z
    exact congrArg Subtype.val hq
  · intro d e
    change (A (Quotient.mk _ d)).val = (A (Quotient.mk _ e)).val ↔
      Equiv.Perm.SameCycle (wholePlaneFaceSucc W D.rotation) d e
    constructor
    · intro h
      have hface : A (Quotient.mk _ d) = A (Quotient.mk _ e) :=
        Subtype.ext h
      exact Quotient.exact (A.injective hface)
    · intro h
      have hq : Quotient.mk
          (Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W D.rotation)) d =
          Quotient.mk _ e := Quotient.sound h
      exact congrArg (fun q => (A q).val) hq
  · intro r hr d
    rw [d39BallContainsOriginalFace_iff]
    change (∀ e, Equiv.Perm.SameCycle (wholePlaneFaceSucc W D.rotation) d e →
        d39VertexClass M e ∈ d39BallVertices M r) ↔ _
    constructor
    · intro h v hv
      obtain ⟨e, hecycle, heclass⟩ := (hfrontier d v).mp hv
      exact heclass ▸ h e hecycle
    · intro h e hecycle
      apply h (d39VertexClass M e)
      exact (hfrontier d (d39VertexClass M e)).mpr ⟨e, hecycle, rfl⟩
  · intro R
    have houter : M.core.outer = uibhbotWholePlaneOuterDart W := by
      change (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).outer = _
      rfl
    rw [houter]
    have hborder : G.dartBorders (uibhbotWholePlaneOuterDart W)
        (A (Quotient.mk _ (uibhbotWholePlaneOuterDart W))) :=
      uibhbotD39Assembly_faceOrbitEquiv_dartBorders W D
        (uibhbotWholePlaneOuterDart W)
    have hunbounded : G.IsUnbounded
        (A (Quotient.mk _ (uibhbotWholePlaneOuterDart W))) :=
      (uibhbot_assembly_isUnbounded_iff_outer_dartBorders
        W D.rotation D.boundary D.pastLeftUnbounded D.pastRightNonnegative
        D.pastFiniteIncidence P hp ha F hf hFim hFa D.pastRightPositive _).2 hborder
    exact hunbounded R

end DirectedDistances.PaperProofs.Section5

end
