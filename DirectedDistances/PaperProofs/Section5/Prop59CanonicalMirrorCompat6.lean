/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59CanonicalMirrorCompat5

/-! Helper toward Proposition 5.9 (`prop-uihbot-sym`). This file transports
complementary faces across compatible PL drawing carriers and applies that
transport to the canonical assembly's rooted rotation-class carrier. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults

private theorem prop59_wholePlaneVertexClass_eq_iff
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d e : WholePlaneDart W) :
    rootedLocallyFiniteVertexClass (wholePlaneRotation W H) d =
        rootedLocallyFiniteVertexClass (wholePlaneRotation W H) e ↔
      wholePlaneDartVertex W d = wholePlaneDartVertex W e := by
  constructor
  · intro h
    exact (wholePlaneRotation_sameCycle_dartVertex W H d e
      (Quotient.exact h)).symm
  · intro h
    exact Quotient.sound
      (wholePlaneRotation_sameVertex_sameCycle_proof W H d e h)

/-- Helper toward Proposition 5.9. Compatible dart and vertex reindexings
identify the plane images of two PL drawings. Their complementary faces,
unboundedness predicates, and dart-border predicates therefore transport
without additional geometric assumptions. -/
theorem prop59_PLDrawing_transport_faces
    {D D' V V' : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V'}
    (P : PLDrawing D V flip rot vert)
    (Q : PLDrawing D' V' flip' rot' vert')
    (eD : D ≃ D') (eV : V ≃ V')
    (_hvert : ∀ d, eV (vert d) = vert' (eD d))
    (hpos : ∀ v, Q.pos (eV v) = P.pos v)
    (harc : ∀ d, Q.arc (eD d) = P.arc d) :
    (∀ F : P.Face, ∃ F' : Q.Face,
      F'.val = F.val ∧ (Q.IsUnbounded F' ↔ P.IsUnbounded F)) ∧
    (∀ F' : Q.Face, ∃ F : P.Face,
      F.val = F'.val ∧ (P.IsUnbounded F ↔ Q.IsUnbounded F')) ∧
    (∀ (d : D) (F : P.Face) (F' : Q.Face), F'.val = F.val →
      (Q.dartBorders (eD d) F' ↔ P.dartBorders d F)) := by
  have himage : P.image = Q.image := by
    ext z
    change (z ∈ Set.range P.pos ∨ ∃ d, z ∈ (P.arc d).image) ↔
      (z ∈ Set.range Q.pos ∨ ∃ d', z ∈ (Q.arc d').image)
    constructor
    · rintro (⟨v, rfl⟩ | ⟨d, hz⟩)
      · exact Or.inl ⟨eV v, hpos v⟩
      · exact Or.inr ⟨eD d, (harc d).symm ▸ hz⟩
    · rintro (⟨v', hv'⟩ | ⟨d', hz⟩)
      · refine Or.inl ⟨eV.symm v', ?_⟩
        calc
          P.pos (eV.symm v') = Q.pos (eV (eV.symm v')) := (hpos _).symm
          _ = Q.pos v' := congrArg Q.pos (eV.apply_symm_apply v')
          _ = z := hv'
      · refine Or.inr ⟨eD.symm d', ?_⟩
        have harc' := harc (eD.symm d')
        have hz' : z ∈ (Q.arc (eD (eD.symm d'))).image := by
          simpa only [Equiv.apply_symm_apply] using hz
        exact harc' ▸ hz'
  constructor
  · intro F
    obtain ⟨z, hz, hF⟩ := F.property
    have hzQ : z ∉ Q.image := by
      intro hzq
      apply hz
      rw [himage]
      exact hzq
    let F' : Q.Face := ⟨connectedComponentIn Q.imageᶜ z, z, hzQ, rfl⟩
    have hval : F'.val = F.val := by
      change connectedComponentIn Q.imageᶜ z = F.val
      rw [← himage, hF]
    refine ⟨F', hval, ?_⟩
    · change (∀ R : ℝ, ∃ z ∈ F'.val, R < ‖z‖) ↔
        ∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖
      rw [hval]
  constructor
  · intro F'
    obtain ⟨z, hz, hF'⟩ := F'.property
    have hzP : z ∉ P.image := by
      intro hzp
      apply hz
      rw [← himage]
      exact hzp
    let F : P.Face := ⟨connectedComponentIn P.imageᶜ z, z, hzP, rfl⟩
    have hval : F.val = F'.val := by
      change connectedComponentIn P.imageᶜ z = F'.val
      rw [himage, hF']
    refine ⟨F, hval, ?_⟩
    · change (∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖) ↔
        ∀ R : ℝ, ∃ z ∈ F'.val, R < ‖z‖
      rw [hval]
  · intro d F F' hF
    simp only [PLDrawing.dartBorders, harc d, hF]

/-- Helper toward Proposition 5.9. If two PL drawings have the same plane
image and corresponding arcs, their face sets, unbounded faces, and dart
borders agree. -/
theorem prop59_PLDrawing_transport_faces_of_image_eq
    {D D' V V' : Type*}
    {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V'}
    (P : PLDrawing D V flip rot vert)
    (Q : PLDrawing D' V' flip' rot' vert')
    (eD : D ≃ D')
    (harc : ∀ d, Q.arc (eD d) = P.arc d)
    (himage : P.image = Q.image) :
    (∀ F : P.Face, ∃ F' : Q.Face,
      F'.val = F.val ∧ (Q.IsUnbounded F' ↔ P.IsUnbounded F)) ∧
    (∀ F' : Q.Face, ∃ F : P.Face,
      F.val = F'.val ∧ (P.IsUnbounded F ↔ Q.IsUnbounded F')) ∧
    (∀ (d : D) (F : P.Face) (F' : Q.Face), F'.val = F.val →
      (Q.dartBorders (eD d) F' ↔ P.dartBorders d F)) := by
  constructor
  · intro F
    obtain ⟨z, hz, hF⟩ := F.property
    have hzQ : z ∉ Q.image := by
      intro hzq
      apply hz
      rw [himage]
      exact hzq
    let F' : Q.Face := ⟨connectedComponentIn Q.imageᶜ z, z, hzQ, rfl⟩
    have hval : F'.val = F.val := by
      change connectedComponentIn Q.imageᶜ z = F.val
      rw [← himage, hF]
    refine ⟨F', hval, ?_⟩
    change (∀ R : ℝ, ∃ z ∈ F'.val, R < ‖z‖) ↔
      ∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖
    rw [hval]
  constructor
  · intro F'
    obtain ⟨z, hz, hF'⟩ := F'.property
    have hzP : z ∉ P.image := by
      intro hzp
      apply hz
      rw [← himage]
      exact hzp
    let F : P.Face := ⟨connectedComponentIn P.imageᶜ z, z, hzP, rfl⟩
    have hval : F.val = F'.val := by
      change connectedComponentIn P.imageᶜ z = F'.val
      rw [himage, hF']
    refine ⟨F, hval, ?_⟩
    change (∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖) ↔
      ∀ R : ℝ, ∃ z ∈ F'.val, R < ‖z‖
    rw [hval]
  · intro d F F' hF
    simp only [PLDrawing.dartBorders, harc d, hF]

/-- Helper toward Proposition 5.9. The assembly drawing reindexed by the
whole-plane vertex/rotation-class equivalence has the canonical outer dart
as a PL drawing on the rooted rotation-class carrier. -/
noncomputable def prop59_canonicalAssembly_reindexedDrawing
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0) :
    PLDrawing
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.D
      (RootedLocallyFiniteVertex
        ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.D
        ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.rot)
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.edgeInv
      ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap).core.rot
      (d39VertexClass
        ((uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap)) := by
  let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  let P0 := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let F0 := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
  let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
  let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
  let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P0 hp ha F0 hf hFim hFa
  have hrep (v : RootedLocallyFiniteVertex M.core.D M.core.rot) :
      d39VertexClass M (Quotient.out v) = v := Quotient.out_eq' v
  have hvertex (d : M.core.D) :
      wholePlaneDartVertex W (Quotient.out (d39VertexClass M d)) =
        wholePlaneDartVertex W d :=
    (prop59_wholePlaneVertexClass_eq_iff W D.rotation _ _).mp (hrep _)
  have hclass {v w : RootedLocallyFiniteVertex M.core.D M.core.rot}
      (hv : wholePlaneDartVertex W (Quotient.out v) =
        wholePlaneDartVertex W (Quotient.out w)) : v = w := by
    calc
      v = d39VertexClass M (Quotient.out v) := (hrep v).symm
      _ = d39VertexClass M (Quotient.out w) :=
        (prop59_wholePlaneVertexClass_eq_iff W D.rotation _ _).mpr hv
      _ = w := hrep w
  refine
    { flip_involutive := M.core.edgeInv_invol
      flip_ne := M.core.edgeInv_ne
      vert_rotation := by
        intro d
        change rootedLocallyFiniteVertexClass M.core.rot (M.core.rot d) = _
        exact Quotient.sound ⟨-1, by simp⟩
      pos := fun v => G.pos (wholePlaneDartVertex W (Quotient.out v))
      pos_injective := by
        intro v w hvw
        apply hclass
        exact G.pos_injective hvw
      arc := G.arc
      arc_simple := G.arc_simple
      arc_length := G.arc_length
      arc_start := by
        intro d
        change (G.arc d).start =
          G.pos (wholePlaneDartVertex W (Quotient.out (d39VertexClass M d)))
        rw [hvertex d]
        exact G.arc_start d
      arc_finish := by
        intro d
        change (G.arc d).finish =
          G.pos (wholePlaneDartVertex W
            (Quotient.out (d39VertexClass M (M.core.edgeInv d))))
        rw [hvertex (M.core.edgeInv d)]
        exact G.arc_finish d
      arc_flip := by
        intro d
        change G.arc (wholePlaneDartFlip W d) = (G.arc d).reverse
        exact G.arc_flip d
      interior_disjoint := G.interior_disjoint
      interior_avoids_vertices := by
        intro d v
        exact G.interior_avoids_vertices d (wholePlaneDartVertex W (Quotient.out v))
      locally_finite := G.locally_finite
      initial_nonzero := G.initial_nonzero
      initial_arg_injective := by
        intro d e hv harg
        apply G.initial_arg_injective d e ?_ harg
        exact (prop59_wholePlaneVertexClass_eq_iff W D.rotation d e).mp hv
      rotation_agreement := by
        intro d
        have hstar :
            {e : M.core.D | d39VertexClass M e = d39VertexClass M d} =
            {e | wholePlaneDartVertex W e = wholePlaneDartVertex W d} := by
          ext e
          constructor
          · intro h
            change d39VertexClass M e = d39VertexClass M d at h
            exact (prop59_wholePlaneVertexClass_eq_iff W D.rotation e d).mp h
          · intro h
            change wholePlaneDartVertex W e = wholePlaneDartVertex W d at h
            exact (prop59_wholePlaneVertexClass_eq_iff W D.rotation e d).mpr h
        change CcwSuccessor
          {e | d39VertexClass M e = d39VertexClass M d}
          (fun e => (G.arc e).initialDirection) d
          (wholePlaneRotation W D.rotation d)
        rw [hstar]
        exact G.rotation_agreement d }

/-- Helper toward Proposition 5.9. The canonical outer dart belongs to the
restricted external orbit of the assembly drawing on every positive-radius
ball, after reindexing vertices by rotation classes. -/
theorem prop59_canonicalAssembly_outerDart_mem_restrictedExternalOrbit
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (r : ℕ) (hr : 0 < r) :
    let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
    let P := prop59_canonicalAssembly_reindexedDrawing W D hhit C₀
    ∃ d : (d39FacedBall M r hr).D,
      d.1 = uibhbotWholePlaneOuterDart W ∧
      d ∈ (d39FacedBallPLWithExternal M P r hr).externalOrbit.val := by
  let P0 := uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let hp := uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
    D.pastRightNonnegative D.pastFiniteIncidence
  let F0 := uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary
  let hf := uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary
  let hFim := uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary
  let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P0 hp ha F0 hf hFim hFa
  let M := (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).toD39RootedMap
  let P := prop59_canonicalAssembly_reindexedDrawing W D hhit C₀
  have hD : WholePlaneDart W = M.core.D := by
    dsimp [M, RootedLocallyFiniteMap.toD39RootedMap,
      uibhbotWholePlaneRootedLocallyFiniteMap]
  let eD : WholePlaneDart W ≃ M.core.D := Equiv.cast hD
  have harc (d : WholePlaneDart W) : P.arc (eD d) = G.arc d := by
    rfl
  have hPsurj : Function.Surjective (d39VertexClass M) := by
    intro v
    exact ⟨Quotient.out v, Quotient.out_eq' v⟩
  have hGsurj : Function.Surjective (wholePlaneDartVertex W) := by
    intro v
    obtain ⟨d, hd⟩ := WholePlanePastGlueData.vertex_incident W v
    exact ⟨d, hd⟩
  have himage : P.image = G.image := by
    rw [P.image_eq_union_arcs hPsurj, G.image_eq_union_arcs hGsurj]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨d', hz⟩
      obtain ⟨d, rfl⟩ := eD.surjective d'
      exact ⟨d, harc d ▸ hz⟩
    · rintro ⟨d, hz⟩
      exact ⟨eD d, (harc d).symm ▸ hz⟩
  have htransport := prop59_PLDrawing_transport_faces_of_image_eq
    G P eD harc himage.symm
  let A := uibhbot_assembly_faceOrbitEquiv W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    P0 hp ha F0 hf hFim hFa D.pastRightPositive
  let F := A (Quotient.mk _ (uibhbotWholePlaneOuterDart W))
  obtain ⟨F', hFval, hFbounded⟩ := htransport.1 F
  have hambient := prop59_canonicalAssembly_outerDart_borders_ambientUnboundedFace
    W D hhit C₀
  have hGborder : G.dartBorders (uibhbotWholePlaneOuterDart W) F := by
    exact hambient.1
  have hGunbounded : G.IsUnbounded F := hambient.2
  have hPborder : P.dartBorders (uibhbotWholePlaneOuterDart W) F' :=
    (htransport.2.2 _ F F' hFval).2 hGborder
  have houter : M.core.outer = uibhbotWholePlaneOuterDart W := by
    change (uibhbotWholePlaneRootedLocallyFiniteMap W D.rotation hhit C₀).outer = _
    rfl
  have hPborder' : P.dartBorders M.core.outer F' := by
    rw [houter]
    exact hPborder
  have hPunbounded : P.IsUnbounded F' := hFbounded.mpr hGunbounded
  have houterRoot : M.core.outer = M.core.edgeInv M.rootMark.dart := by rfl
  have houterBall : M.core.outer ∈ d39BallDarts M r := by
    rw [houterRoot]
    exact (d39BallDarts_root_mem M hr).2
  let d : (d39FacedBall M r hr).D := ⟨M.core.outer, houterBall⟩
  have hmem := prop59_ambientUnboundedDartSide_mem_restrictedExternalOrbit
    M P r hr d F' hPunbounded (by simpa [d] using hPborder')
  exact ⟨d, by simp [d, M, uibhbotWholePlaneRootedLocallyFiniteMap,
      RootedLocallyFiniteMap.toD39RootedMap], hmem⟩

end DirectedDistances.PaperProofs.Section5

end
