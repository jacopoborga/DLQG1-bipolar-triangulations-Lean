/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCutDescent2
public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization19

/-! # Geometric transport of internal cut faces

Run-zero recurrence implies recurrence in every earlier run. Geometric code
recovery then fixes chronological edge identities. Finite face frontiers and
the bounded cap characterization identify the actual open face regions.
The private topological lemmas reproduce the private frontier machinery of -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open Set Metric Topology
open scoped Classical

private theorem frontier_eq_border_arcs_of_finite
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (F : P.Face) (hfin : {d | P.dartBorders d F}.Finite) :
    frontier F.val = ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image := by
  let K := ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image
  have hc : IsClosed K := hfin.isClosed_biUnion fun d _ =>
    (P.arc d).isCompact_image.isClosed
  apply Subset.antisymm
  · intro q hq
    by_contra hn
    obtain ⟨s, hs, hsafe⟩ := Metric.mem_nhds_iff.mp (hc.isOpen_compl.mem_nhds hn)
    have hqi := (P.face_open_frontier_subset_image hv F).2 hq
    have ha : ∃ d, q ∈ (P.arc d).image := by
      rcases hqi with ⟨v, rfl⟩ | h
      · obtain ⟨d, rfl⟩ := hv v
        exact ⟨d, Or.inl (P.arc_start d).symm⟩
      · exact h
    obtain ⟨d, hd⟩ := ha
    have hseg : ∃ i, i + 1 < (P.arc d).points.length ∧
        q ∈ (P.arc d).segmentAt i := by
      rcases hd with hstart | ⟨i, hi, hqi⟩
      · refine ⟨0, by have := P.arc_length d; omega, ?_⟩
        rw [hstart, Polyline.segmentAt, Polyline.point_zero_eq_start]
        exact left_mem_segment ℝ _ _
      · exact ⟨i, hi, hqi⟩
    obtain ⟨i, hi, hqi⟩ := hseg
    by_cases he : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1)
    · obtain ⟨x, hxf, hxb, hx⟩ := P.face_endpoint_frontier_not_vertex_mem_ball
        hv F q d hi he (frontier_subset_closure hq) hs
      obtain ⟨e, hxe, heF⟩ := P.exists_mem_arc_dartBorders_of_frontier_not_vertex
        hv F hxf hx
      exact hsafe hxb (mem_iUnion₂.mpr ⟨e, heF, hxe⟩)
    · have hqo := mem_openSegment_of_ne_left_right
        (fun h => he (Or.inl h.symm)) (fun h => he (Or.inr h.symm)) hqi
      rcases (P.mem_closure_face_openSegment_iff_dartBorders hv d F hi hqo).mp
          (frontier_subset_closure hq) with hb | hb
      · exact hn (mem_iUnion₂.mpr ⟨d, hb, (P.arc d).segmentAt_subset_image hi hqi⟩)
      · apply hn
        apply mem_iUnion₂.mpr
        refine ⟨flip d, hb, ?_⟩
        rw [P.arc_image_flip]
        exact (P.arc d).segmentAt_subset_image hi hqi
  · rintro q hq
    obtain ⟨d, hd, hqd⟩ := mem_iUnion₂.mp hq
    exact P.dartBorders_arc_subset_frontier hv d F hd hqd


private theorem open_eq_of_subset_frontier_disjoint {F S : Set ℂ}
    (ho : IsOpen F) (hn : F.Nonempty) (hc : IsPreconnected S)
    (hs : F ⊆ S) (hd : Disjoint (frontier F) S) : F = S := by
  apply Subset.antisymm hs
  apply hc.subset_of_closure_inter_subset ho
  · obtain ⟨x, hx⟩ := hn
    exact ⟨x, hs hx, hx⟩
  · rintro x ⟨hx, hxs⟩
    by_contra hnF
    exact Set.disjoint_left.mp hd
      (by rw [frontier, ho.interior_eq]; exact ⟨hx, hnF⟩) hxs

private theorem bounded_open_eq_of_frontier {S T : Set ℂ}
    (hoS : IsOpen S) (hcS : IsConnected S)
    (hoT : IsOpen T) (hcT : IsConnected T) (hbT : Bornology.IsBounded T)
    (hcE : IsPreconnected (closure S)ᶜ) (hbE : ¬ Bornology.IsBounded (closure S)ᶜ)
    (hf : frontier S = frontier T) : S = T := by
  have hd : Disjoint S (closure S)ᶜ := Set.disjoint_left.mpr
    (fun _ hx hy => hy (subset_closure hx))
  have hs : T ⊆ S ∪ (closure S)ᶜ := by
    intro x hx
    by_cases hxs : x ∈ S
    · exact Or.inl hxs
    · right
      intro hxc
      have hxf : x ∈ frontier S := by
        rw [frontier, hoS.interior_eq]; exact ⟨hxc, hxs⟩
      rw [hf, frontier, hoT.interior_eq] at hxf
      exact hxf.2 hx
  rcases hcT.isPreconnected.subset_or_subset hoS isClosed_closure.isOpen_compl hd hs with hin | hout
  · symm
    apply open_eq_of_subset_frontier_disjoint hoT hcT.nonempty hcS.isPreconnected hin
    rw [← hf, frontier, hoS.interior_eq]
    exact Set.disjoint_left.mpr (fun _ hx hy => hx.2 hy)
  · have he := open_eq_of_subset_frontier_disjoint hoT hcT.nonempty hcE hout
      (Set.disjoint_left.mpr (fun _ hx hy => hy (frontier_subset_closure (hf.symm ▸ hx))))
    exact False.elim (hbE (he ▸ hbT))

private theorem cap_image_eq_of_frontier (C : DirectedDistances.KMSW.GraphCap)
    (g : ℂ ≃ₜ ℂ) (T : Set ℂ) (hoT : IsOpen T) (hcT : IsConnected T)
    (hbT : Bornology.IsBounded T) (hf : frontier (g '' C.region) = frontier T) :
    g '' C.region = T := by
  have hle : ∀ x ∈ Icc C.a C.b, C.low x ≤ C.high x := by
    intro x hx
    by_cases hxa : x = C.a
    · subst x; exact C.left_join.le
    by_cases hxb : x = C.b
    · subst x; exact C.right_join.le
    exact (C.separated x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩).le
  have hcl : closure C.region = closedGraphRegion C.a C.b C.low C.high :=
    closure_graphRegion_eq_closedGraphRegion C.ab C.low_continuous C.high_continuous
      C.separated C.left_join C.right_join
  have hext : (closure (g '' C.region))ᶜ = g '' (closure C.region)ᶜ := by
    rw [← g.image_closure, g.image_compl]
  apply bounded_open_eq_of_frontier
    (g.isOpenMap _ (isOpen_graphRegion C.low_continuous C.high_continuous))
    ((isPathConnected_graphRegion C.ab C.low_continuous C.high_continuous C.separated).isConnected.image
      g g.continuous.continuousOn) hoT hcT hbT
  · change IsPreconnected (closure (g '' C.region))ᶜ
    rw [hext, hcl]
    exact (isPathConnected_compl_closedGraphRegion C.ab.le C.low_continuous
      C.high_continuous hle).isConnected.isPreconnected.image g g.continuous.continuousOn
  · change ¬ Bornology.IsBounded (closure (g '' C.region))ᶜ
    rw [hext, hcl]
    intro hb
    have hback := (hb.isCompact_closure.image g.symm.continuous).isBounded.subset
      (Set.image_mono (subset_closure : g '' (closedGraphRegion C.a C.b C.low C.high)ᶜ ⊆ _))
    have hb0 : Bornology.IsBounded (closedGraphRegion C.a C.b C.low C.high)ᶜ := by
      simpa only [Set.image_image, g.symm_apply_apply, Set.image_id'] using hback
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb0
    obtain ⟨z, hz, hRz⟩ := exists_norm_gt_compl_closedGraphRegion
      C.low_continuous C.high_continuous hle R
    exact (not_le_of_gt hRz) (hR z hz)
  · exact hf


private theorem source_iso_fixes_arc_images
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (hh : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N))
    (J : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G))
    (d : WholePlaneDart W) :
    J.h '' (G.arc d).image = (G.arc d).image := by
  have he (e : WholePlaneEdge W) : J.edgeEquiv e = e :=
    (uibotCut_geometric_iso_fixes_ids hh J).1 e
  have hrange (e : WholePlaneEdge W) :
      Set.range ((uibotWholePlaneSourceMap W H G hp).arc e) =
        (G.arc (e, false)).image := G.toPlaneGraphDrawing_arc_range (e, false)
  have hzero (e : WholePlaneEdge W) :
      J.h '' (G.arc (e, false)).image = (G.arc (e, false)).image := by
    rw [← hrange]
    ext z
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      refine ⟨J.edgeParam e t, ?_⟩
      have ha := J.arc_map e t
      rw [he e] at ha
      exact ha.symm
    · rintro ⟨t, rfl⟩
      refine ⟨(uibotWholePlaneSourceMap W H G hp).arc e ((J.edgeParam e).symm t),
        ⟨(J.edgeParam e).symm t, rfl⟩, ?_⟩
      have ha := J.arc_map e ((J.edgeParam e).symm t)
      rw [he e, Homeomorph.apply_symm_apply] at ha
      exact ha
  rcases d with ⟨e, b⟩
  cases b
  · exact hzero e
  · have hf := G.arc_image_flip (e, false)
    change (G.arc (e, true)).image = (G.arc (e, false)).image at hf
    rw [hf]
    exact hzero e

/-- Helper toward Proposition 3.9: every rooted geometric automorphism
of a glued realization fixes each actual internal cut-face region. No extra
recurrence or face-preservation hypothesis is required. -/
theorem uibotCut_source_iso_internal_face_fixed
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (J : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H))
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H)))
    (q : FutureMapInternalFaceOrbit W H) :
    J.h '' (futureMapInternalGluedFace W H h0 hpast q).val =
      (futureMapInternalGluedFace W H h0 hpast q).val := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
  let F := futureMapInternalGluedFace W H h0 hpast q
  let F0 := futureMapInternalFaceEquiv W H h0 q
  have hh (N : ℕ) : BoundaryHitWitnesses (shiftedStream W N) :=
    boundaryHitWitnesses_of_le W (Nat.zero_le N) h0
  have ha := source_iso_fixes_arc_images W H G hp hh J
  have hfinite : {d | G.dartBorders d F}.Finite := by
    obtain ⟨j, hj, _⟩ := futureMap_internal_glued_triangle W H h0 hpast q
    rw [hj]
    exact (stageTriangleDartList (shiftedStream W 0) j).finite_toSet.image _
  have hfront : J.h '' frontier F.val = frontier F.val := by
    rw [frontier_eq_border_arcs_of_finite G
      (uibhbot_faceOrbit_dartVertex_surjective W H) F hfinite]
    simp only [Set.image_iUnion, ha]
  have hval : F.val = F0.val.val := futureMap_internal_glued_face_val W H h0 hpast q
  obtain ⟨n, i, hcap⟩ := limitDrawing_boundedFace_eq_capRegion_twoSided
    (shiftedStream W 0) (H.1 0) h0 F0.val F0.property
  let C := (familyG (shiftedStream W 0) (monotone_family_all _) n).cap i
  have hFC : F.val = C.region := hval.trans hcap
  have hopen : IsOpen F.val :=
    (G.face_open_frontier_subset_image (uibhbot_faceOrbit_dartVertex_surjective W H) F).1
  have hconn : IsConnected F.val := by
    obtain ⟨z, hz, he⟩ := F.property
    rw [he]
    exact isConnected_connectedComponentIn_iff.mpr hz
  have hbounded : Bornology.IsBounded F.val := by
    obtain ⟨j, hj⟩ := (boundedFace_iff_creation_orbit
      (shiftedStream W 0) (H.1 0) h0 F0.val).1 F0.property
    rw [hval, hj]
    exact capFace_bounded (shiftedStream W 0) (H.1 0) j
  change J.h '' F.val = F.val
  rw [hFC] at ⊢
  apply cap_image_eq_of_frontier C J.h C.region
    (hFC ▸ hopen) (hFC ▸ hconn) (hFC ▸ hbounded)
  rw [← J.h.image_frontier, ← hFC]
  exact hfront

/-- Helper toward Proposition 3.9: an arbitrary rooted geometric
isomorphism of two glued whole-plane realizations transports the internal
cut-face orbits bijectively, with equality of their open planar regions. -/
theorem uibotCut_geometric_internal_face_transport
    (W W' : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis W')
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (h0' : BoundaryHitWitnesses (shiftedStream W' 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hpast' : BoundaryHitWitnesses (kmswPastCode W'))
    (hp : ∀ a : WholePlaneEdge W, wholePlaneEdgePresent W a)
    (hp' : ∀ a : WholePlaneEdge W', wholePlaneEdgePresent W' a) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let G' := WholePlanePastGlueDrawing.glueDrawing W' h0' hpast' H'
    ∀ I : D39GeomRootedMapIsoV2
      (uibotWholePlaneGeometricMap W H G hp) (uibotWholePlaneGeometricRoot W H G)
      (uibotWholePlaneGeometricMap W' H' G' hp') (uibotWholePlaneGeometricRoot W' H' G'),
      ∃ f : FutureMapInternalFaceOrbit W H ≃ FutureMapInternalFaceOrbit W' H',
        ∀ q : FutureMapInternalFaceOrbit W H,
          I.h '' (futureMapInternalGluedFace W H h0 hpast q).val =
            (futureMapInternalGluedFace W' H' h0' hpast' (f q)).val := by
  intro G G' I
  let J := ((uibotWholePlaneSourceIso W H G hp).trans I).trans
    (uibotWholePlaneSourceIso W' H' G' hp').symm
  have hh (N : ℕ) : BoundaryHitWitnesses (shiftedStream W N) :=
    boundaryHitWitnesses_of_le W (Nat.zero_le N) h0
  have hh' (N : ℕ) : BoundaryHitWitnesses (shiftedStream W' N) :=
    boundaryHitWitnesses_of_le W' (Nat.zero_le N) h0'
  have hW : W = W' := uibotCut_code_eq_of_geometric_iso hh hh' J
  subst W'
  refine ⟨Equiv.refl _, fun q => ?_⟩
  exact uibotCut_source_iso_internal_face_fixed W H h0 hpast hp J q

end DirectedDistances.PaperProofs.Section3
end
