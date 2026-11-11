/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTClassSeparation3







public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap DirectedDistances.KMSW DirectedDistances.RandomWalk
open Set Topology
open scoped Topology

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

private theorem cap_image_eq_of_frontier (C : GraphCap)
    (g : ℂ ≃ₜ ℂ) (T : Set ℂ) (hoT : IsOpen T) (hcT : IsConnected T)
    (hbT : Bornology.IsBounded T) (hf : frontier (g '' C.region) = frontier T) :
    g '' C.region = T := by
  have hle : ∀ x ∈ Icc C.a C.b, C.low x ≤ C.high x := by
    intro x hx
    by_cases hxa : x = C.a
    · subst x; exact C.left_join.le
    by_cases hxb : x = C.b
    · subst x; exact C.right_join.le
    exact (C.separated x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa),
      lt_of_le_of_ne hx.2 hxb⟩).le
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

/-- Helper toward Proposition 3.9: every source face is an ambient image
of one of the graph caps in the past or future construction. -/
theorem uibotClassSeparation4_source_face_cap
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    ∀ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      ∃ (C : GraphCap) (T : ℂ ≃ₜ ℂ), F.val = T '' C.region := by
  intro G M F
  let I := uibotWholePlaneSourceIso W H G hp
  let Fg := I.faceEquiv F
  have hval : Fg.val = F.val := by
    rw [show Fg.val = I.h '' F.val from I.faceEquiv_val F]
    exact Set.image_id _
  rcases WholePlanePastGlueDrawing.glueDrawing_faces W h0 hpast H
    (G.toPlaneGraphDrawingFaceEquiv Fg) with ⟨F0, hb, he⟩ | ⟨Fp, hb, he⟩
  · obtain ⟨n, i, hi⟩ := limitDrawing_boundedFace_eq_capRegion_twoSided
      (shiftedStream W 0) (H.1 0) h0 F0 hb
    refine ⟨(familyG (shiftedStream W 0) (monotone_family_all _) n).cap i,
      Homeomorph.refl ℂ, ?_⟩
    change F.val = id '' _
    rw [Set.image_id]
    exact hval.symm.trans (he.trans hi)
  · obtain ⟨n, i, hi⟩ := limitDrawing_boundedFace_eq_capRegion_twoSided
      (kmswPastCode W) (WholePlanePastGlueData.past_finiteIncidence W H) hpast Fp hb
    refine ⟨(familyG (kmswPastCode W) (monotone_family_all _) n).cap i,
      PastDrawingTransfer.transfer (shiftedStream W 0) (kmswPastCode W)
        h0 hpast (H.1 0) (WholePlanePastGlueData.past_finiteIncidence W H), ?_⟩
    exact hval.symm.trans (he.trans (congrArg (fun s => _ '' s) hi))

/-- Helper toward Proposition 3.9: two ambient images of a source face
with the same frontier are the same bounded open region. This excludes
selecting the unbounded side of the mapped boundary. -/
theorem uibotClassSeparation4_source_face_image_eq_of_frontier
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    ∀ (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) (g k : ℂ ≃ₜ ℂ),
      g '' frontier F.val = k '' frontier F.val → g '' F.val = k '' F.val := by
  intro G M F g k hf
  obtain ⟨C, T, hF⟩ := uibotClassSeparation4_source_face_cap W H h0 hpast hp F
  have ho : IsOpen F.val := by
    rw [hF]
    exact T.isOpenMap _ (isOpen_graphRegion C.low_continuous C.high_continuous)
  have hc : IsConnected F.val := by
    rw [hF]
    exact (isPathConnected_graphRegion C.ab C.low_continuous C.high_continuous
      C.separated).isConnected.image T T.continuous.continuousOn
  have hb : Bornology.IsBounded (k '' F.val) :=
    ((uibotClassSeparation2_source_face_compact_finite_boundary W H h0 hpast hp F).1.image
      k.continuous).isBounded.subset (Set.image_mono subset_closure)
  have hcomp : (T.trans g) '' C.region = g '' F.val := by
    rw [hF, Set.image_image]
    rfl
  rw [← hcomp]
  apply cap_image_eq_of_frontier C (T.trans g) (k '' F.val)
    (k.isOpenMap _ ho) (hc.image k k.continuous.continuousOn) hb
  rw [hcomp, ← g.image_frontier, ← k.image_frontier]
  exact hf

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

/-- Helper toward Proposition 3.9: each source frontier point lies on a
whole geometric edge contained in that frontier, with its original edge ID. -/
theorem uibotClassSeparation4_source_frontier_covered_by_edges
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    ∀ (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) (x : ℂ),
      x ∈ frontier F.val → ∃ e : WholePlaneEdge W,
        Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val ∧
        x ∈ Set.range (M.toPlaneMapWithMissing.arc e) := by
  intro G M F x hx
  let I := uibotWholePlaneSourceIso W H G hp
  let Fg := I.faceEquiv F
  let Fp := G.toPlaneGraphDrawingFaceEquiv Fg
  have hval : Fp.val = F.val := by
    change Fg.val = F.val
    rw [show Fg.val = I.h '' F.val from I.faceEquiv_val F]
    exact Set.image_id _
  have hcompact :=
    (uibotClassSeparation2_source_face_compact_finite_boundary W H h0 hpast hp F).1
  have hfin : {d | G.dartBorders d Fp}.Finite := by
    apply (G.locally_finite (closure F.val) hcompact.isBounded).subset
    intro d hd
    refine ⟨(G.arc d).start, ?_, Or.inl rfl⟩
    rw [← hval]
    exact G.dartBorders_arc_subset_closure
      (uibhbot_faceOrbit_dartVertex_surjective W H) d Fp hd (Or.inl rfl)
  have hx' : x ∈ frontier Fp.val := hval.symm ▸ hx
  rw [frontier_eq_border_arcs_of_finite G
    (uibhbot_faceOrbit_dartVertex_surjective W H) Fp hfin] at hx'
  obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hx'
  have harc : Set.range (M.toPlaneMapWithMissing.arc d.1) = (G.arc d).image := by
    rcases d with ⟨e, b⟩
    cases b
    · exact G.toPlaneGraphDrawing_arc_range (e, false)
    · exact (G.toPlaneGraphDrawing_arc_range (e, false)).trans
        (G.arc_image_flip (e, false)).symm
  refine ⟨d.1, ?_, harc.symm ▸ hxd⟩
  rw [harc, ← hval]
  exact G.dartBorders_arc_subset_frontier
    (uibhbot_faceOrbit_dartVertex_surjective W H) d Fp hd

/-- Helper toward Proposition 3.9: compatible ball witnesses at any two
radii select the same target face once the source face is retained at both.
Only equality of the individual boundary-edge images is needed here. -/
theorem uibotClassSeparation4_retained_face_image_eq
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0}) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    let ρ := uibotWholePlaneSourceRoot W H G
    ∀ (I : D39CombDartIso M ρ A.map A.root) (r s : ℕ)
      (J : D39GeomBallIsoV2 r M ρ A.map A.root)
      (K : D39GeomBallIsoV2 s M ρ A.map A.root)
      (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
      (hr : F ∈ d39GeomRetainedFaces M ρ r)
      (hs : F ∈ d39GeomRetainedFaces M ρ s),
      (∀ e : {e // e ∈ d39GeomBallEdges M ρ r},
        I.edgeEquiv e.val = (J.edgeEquiv e).val) →
      (∀ e : {e // e ∈ d39GeomBallEdges M ρ s},
        I.edgeEquiv e.val = (K.edgeEquiv e).val) →
      (J.faceEquiv ⟨F, hr⟩).val = (K.faceEquiv ⟨F, hs⟩).val := by
  intro G M ρ I r s J K F hr hs hJ hK
  apply Subtype.ext
  rw [← J.face_image_map ⟨F, hr⟩, ← K.face_image_map ⟨F, hs⟩]
  apply uibotClassSeparation4_source_face_image_eq_of_frontier W H h0 hpast hp F
  have hboundary : ∀ e : WholePlaneEdge W,
      Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val →
      J.h '' Set.range (M.toPlaneMapWithMissing.arc e) =
        K.h '' Set.range (M.toPlaneMapWithMissing.arc e) := by
    intro e he
    have hsrc : M.toPlaneMapWithMissing.pos (M.toPlaneMapWithMissing.src e) ∈ closure F.val :=
      frontier_subset_closure (he ⟨0, (M.toPlaneMapWithMissing.arc e).source⟩)
    have htgt : M.toPlaneMapWithMissing.pos (M.toPlaneMapWithMissing.tgt e) ∈ closure F.val :=
      frontier_subset_closure (he ⟨1, (M.toPlaneMapWithMissing.arc e).target⟩)
    let er : {e // e ∈ d39GeomBallEdges M ρ r} := ⟨e, hr _ hsrc, hr _ htgt⟩
    let es : {e // e ∈ d39GeomBallEdges M ρ s} := ⟨e, hs _ hsrc, hs _ htgt⟩
    rw [J.arc_range_map er, K.arc_range_map es, ← hJ er, ← hK es]
  have hsub (g k : ℂ ≃ₜ ℂ)
      (hk : ∀ e : WholePlaneEdge W,
        Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val →
        g '' Set.range (M.toPlaneMapWithMissing.arc e) =
          k '' Set.range (M.toPlaneMapWithMissing.arc e)) :
      g '' frontier F.val ⊆ k '' frontier F.val := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨e, he, hxe⟩ :=
      uibotClassSeparation4_source_frontier_covered_by_edges W H h0 hpast hp F x hx
    have hmem : g x ∈ k '' Set.range (M.toPlaneMapWithMissing.arc e) :=
      hk e he ▸ Set.mem_image_of_mem g hxe
    exact Set.image_mono he hmem
  exact Subset.antisymm (hsub J.h K.h hboundary)
    (hsub K.h J.h (fun e he => (hboundary e he).symm))

/-- Helper toward Proposition 3.9: compatible finite traces determine one
injective assignment of source faces to target faces. Every larger-radius
witness retaining the face selects exactly this same target component. -/
theorem uibotClassSeparation4_target_face_assignment
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0}) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    let ρ := uibotWholePlaneSourceRoot W H G
    ∀ I : D39CombDartIso M ρ A.map A.root,
      (∀ n : ℕ, ∃ J : D39GeomBallIsoV2 (n + 1) M ρ A.map A.root,
        (∀ v : uibotSeparationBallV (uibotWholePlaneSourceDomain W H G hp) n,
          I.vertexEquiv v.val = (J.vertexEquiv v).val) ∧
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
          I.edgeEquiv e.val = (J.edgeEquiv e).val) ∧
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
          I.flip e.val = J.edgeFlip e)) →
      ∃ τ : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face →
          A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
        Function.Injective τ ∧
        ∀ (n : ℕ) (J : D39GeomBallIsoV2 (n + 1) M ρ A.map A.root),
          (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
            I.edgeEquiv e.val = (J.edgeEquiv e).val) →
          ∀ (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
            (hF : F ∈ d39GeomRetainedFaces M ρ (n + 1)),
            (J.faceEquiv ⟨F, hF⟩).val = τ F := by
  classical
  intro G M ρ I hlocal
  have hex : ∀ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      ∃ (T : A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
        (n : ℕ) (J : D39GeomBallIsoV2 (n + 1) M ρ A.map A.root)
        (hF : F ∈ d39GeomRetainedFaces M ρ (n + 1)),
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
          I.edgeEquiv e.val = (J.edgeEquiv e).val) ∧
        (J.faceEquiv ⟨F, hF⟩).val = T := by
    intro F
    obtain ⟨r, _, hr⟩ :=
      uibotClassSeparation2_source_face_eventually_retained W H h0 hpast hp F
    obtain ⟨J, _, he, _⟩ := hlocal r
    have hF : F ∈ d39GeomRetainedFaces M ρ (r + 1) := fun v hv =>
      D39GeomBallIsoV2.vertexBall_mono (Nat.le_succ r) (hr v hv)
    exact ⟨(J.faceEquiv ⟨F, hF⟩).val, r, J, hF, he, rfl⟩
  choose τ n J hret he hτ using hex
  have hcoh (m : ℕ) (K : D39GeomBallIsoV2 (m + 1) M ρ A.map A.root)
      (hK : ∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) m,
        I.edgeEquiv e.val = (K.edgeEquiv e).val)
      (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
      (hF : F ∈ d39GeomRetainedFaces M ρ (m + 1)) :
      (K.faceEquiv ⟨F, hF⟩).val = τ F :=
    (uibotClassSeparation4_retained_face_image_eq W H h0 hpast hp A I
      (m + 1) (n F + 1) K (J F) F hF (hret F) hK (he F)).trans (hτ F)
  refine ⟨τ, ?_, hcoh⟩
  intro F F' hsame
  let r := max (n F) (n F')
  obtain ⟨K, _, hK, _⟩ := hlocal r
  have hF : F ∈ d39GeomRetainedFaces M ρ (r + 1) := fun v hv =>
    D39GeomBallIsoV2.vertexBall_mono (Nat.add_le_add_right (le_max_left _ _) 1)
      (hret F v hv)
  have hF' : F' ∈ d39GeomRetainedFaces M ρ (r + 1) := fun v hv =>
    D39GeomBallIsoV2.vertexBall_mono (Nat.add_le_add_right (le_max_right _ _) 1)
      (hret F' v hv)
  have hsame' : (K.faceEquiv ⟨F, hF⟩).val = (K.faceEquiv ⟨F', hF'⟩).val :=
    (hcoh r K hK F hF).trans (hsame.trans (hcoh r K hK F' hF').symm)
  exact congrArg Subtype.val (K.faceEquiv.injective (Subtype.ext hsame'))

private theorem face_nonempty {V E : Type*} (D : PlaneGraphDrawing V E) (F : D.Face) :
    F.val.Nonempty := by
  obtain ⟨x, hx, hF⟩ := F.property
  exact ⟨x, hF.symm ▸ mem_connectedComponentIn hx⟩

private theorem faces_eq_of_mem {V E : Type*} (D : PlaneGraphDrawing V E)
    (F F' : D.Face) {x : ℂ} (hx : x ∈ F.val) (hx' : x ∈ F'.val) : F = F' := by
  apply Subtype.ext
  obtain ⟨a, _, hF⟩ := F.property
  obtain ⟨b, _, hF'⟩ := F'.property
  exact hF.trans ((connectedComponentIn_eq (hF ▸ hx)).trans
    ((connectedComponentIn_eq (hF' ▸ hx')).symm.trans hF'.symm))

/-- Helper toward Proposition 3.9: each individual source edge belongs
to one complete closed source face, including both stored endpoints. -/
theorem uibotClassSeparation4_source_edge_in_closed_face
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    ∀ e : WholePlaneEdge W,
      ∃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
        Set.range (M.toPlaneMapWithMissing.arc e) ⊆ closure F.val := by
  intro G M e
  obtain ⟨F, hF⟩ :=
    WholePlaneGlueFaceCorrespondenceFull.dart_borders_exists W h0 hpast H (e, false)
  let I := uibotWholePlaneSourceIso W H G hp
  let Fg := G.toPlaneGraphDrawingFaceEquiv.symm F
  let Fs := I.faceEquiv.symm Fg
  have hval : Fs.val = F.val := by
    have h := I.faceEquiv_val Fs
    rw [show I.faceEquiv Fs = Fg from I.faceEquiv.apply_symm_apply Fg] at h
    exact (Set.image_id _).symm.trans h.symm
  refine ⟨Fs, ?_⟩
  rw [hval, show Set.range (M.toPlaneMapWithMissing.arc e) = (G.arc (e, false)).image
    from G.toPlaneGraphDrawing_arc_range (e, false)]
  exact G.dartBorders_arc_subset_closure
    (uibhbot_faceOrbit_dartVertex_surjective W H) (e, false) F hF

/-- Helper toward Proposition 3.9: the coherent face assignment exhausts
all target faces. Compact source neighborhoods give an open union of target
closed faces; retained-face saturation then excludes a residual component.
The same neighborhoods prove local finiteness of the target closed cells.
No properness condition on the target is imposed. -/
theorem uibotClassSeparation4_target_face_equiv
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0}) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    let ρ := uibotWholePlaneSourceRoot W H G
    ∀ I : D39CombDartIso M ρ A.map A.root,
      (∀ n : ℕ, ∃ J : D39GeomBallIsoV2 (n + 1) M ρ A.map A.root,
        (∀ v : uibotSeparationBallV (uibotWholePlaneSourceDomain W H G hp) n,
          I.vertexEquiv v.val = (J.vertexEquiv v).val) ∧
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
          I.edgeEquiv e.val = (J.edgeEquiv e).val) ∧
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
          I.flip e.val = J.edgeFlip e)) →
      ∃ τ : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face ≃
          A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
        LocallyFinite (fun F => closure (τ F).val) ∧
        (⋃ F, closure (τ F).val) = Set.univ ∧
        ∀ (n : ℕ) (J : D39GeomBallIsoV2 (n + 1) M ρ A.map A.root),
          (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
            I.edgeEquiv e.val = (J.edgeEquiv e).val) →
          ∀ (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
            (hF : F ∈ d39GeomRetainedFaces M ρ (n + 1)),
            (J.faceEquiv ⟨F, hF⟩).val = τ F := by
  classical
  intro G M ρ I hlocal
  obtain ⟨τ, hinj, hcoh⟩ :=
    uibotClassSeparation4_target_face_assignment W H h0 hpast hp A I hlocal
  let U : Set ℂ := ⋃ F, closure (τ F).val
  have hcover := uibotClassSeparation3_source_closed_faces_cover W H h0 hpast hp
  have hpoint (x : ℂ) : ∃ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      x ∈ closure F.val := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  have hseen (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
      ∃ (n : ℕ) (J : D39GeomBallIsoV2 (n + 1) M ρ A.map A.root)
        (hF : F ∈ d39GeomRetainedFaces M ρ (n + 1)),
        (∀ v : uibotSeparationBallV (uibotWholePlaneSourceDomain W H G hp) n,
          I.vertexEquiv v.val = (J.vertexEquiv v).val) ∧
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
          I.edgeEquiv e.val = (J.edgeEquiv e).val) ∧
        J.h '' F.val = (τ F).val := by
    obtain ⟨r, _, hr⟩ :=
      uibotClassSeparation2_source_face_eventually_retained W H h0 hpast hp F
    obtain ⟨J, hv, he, _⟩ := hlocal r
    have hF : F ∈ d39GeomRetainedFaces M ρ (r + 1) := fun v hv =>
      D39GeomBallIsoV2.vertexBall_mono (Nat.le_succ r) (hr v hv)
    exact ⟨r, J, hF, hv, he,
      (J.face_image_map ⟨F, hF⟩).trans (congrArg Subtype.val (hcoh r J he F hF))⟩
  have hopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨F, hzF⟩ := mem_iUnion.mp hz
    obtain ⟨R, hR⟩ :=
      (uibotClassSeparation2_source_face_compact_finite_boundary W H h0 hpast hp F).1.isBounded.subset_ball (0 : ℂ)
    obtain ⟨r, _, hr⟩ :=
      uibotClassSeparation3_source_compact_faces_eventually_retained W H h0 hpast hp
        (Metric.closedBall (0 : ℂ) R) (isCompact_closedBall _ _)
    obtain ⟨J, _, he, _⟩ := hlocal r
    have hmap (F' : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
        (hF' : (closure F'.val ∩ Metric.closedBall (0 : ℂ) R).Nonempty) :
        J.h '' F'.val = (τ F').val := by
      have hret : F' ∈ d39GeomRetainedFaces M ρ (r + 1) := fun v hv =>
        D39GeomBallIsoV2.vertexBall_mono (Nat.le_succ r) (hr F' hF' v hv)
      exact (J.face_image_map ⟨F', hret⟩).trans
        (congrArg Subtype.val (hcoh r J he F' hret))
    have hsub : J.h '' Metric.ball (0 : ℂ) R ⊆ U := by
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨F', hxF⟩ := hpoint x
      apply mem_iUnion.mpr
      refine ⟨F', ?_⟩
      rw [← hmap F' ⟨x, hxF, Metric.ball_subset_closedBall hx⟩, ← J.h.image_closure]
      exact Set.mem_image_of_mem J.h hxF
    have hzball : z ∈ J.h '' Metric.ball (0 : ℂ) R := by
      obtain ⟨x, hx⟩ := face_nonempty M.toPlaneMapWithMissing.toPlaneGraphDrawing F
      have hm := hmap F ⟨x, subset_closure hx,
        Metric.ball_subset_closedBall (hR (subset_closure hx))⟩
      rw [← hm, ← J.h.image_closure] at hzF
      exact Set.image_mono hR hzF
    exact Filter.mem_of_superset
      ((J.h.isOpenMap _ Metric.isOpen_ball).mem_nhds hzball) hsub
  have hvertices : ∀ v, A.map.toPlaneMapWithMissing.pos v ∈ U := by
    intro v
    let v' := I.vertexEquiv.symm v
    obtain ⟨F, hvF⟩ := hpoint (M.toPlaneMapWithMissing.pos v')
    obtain ⟨n, J, hF, hv, _, hm⟩ := hseen F
    let vb : uibotSeparationBallV (uibotWholePlaneSourceDomain W H G hp) n :=
      ⟨v', hF v' hvF⟩
    have hpos : J.h (M.toPlaneMapWithMissing.pos v') = A.map.toPlaneMapWithMissing.pos v := by
      rw [J.pos_map vb, ← hv vb]
      exact congrArg A.map.toPlaneMapWithMissing.pos (I.vertexEquiv.apply_symm_apply v)
    rw [← hpos]
    apply mem_iUnion.mpr
    refine ⟨F, ?_⟩
    rw [← hm, ← J.h.image_closure]
    exact Set.mem_image_of_mem J.h hvF
  have hedges : ∀ e, Set.range (A.map.toPlaneMapWithMissing.arc e) ⊆ U := by
    intro e
    let e' := I.edgeEquiv.symm e
    obtain ⟨F, heF⟩ := uibotClassSeparation4_source_edge_in_closed_face W H h0 hpast hp e'
    obtain ⟨n, J, hF, _, he, hm⟩ := hseen F
    let eb : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n :=
      ⟨e', hF _ (heF ⟨0, (M.toPlaneMapWithMissing.arc e').source⟩),
        hF _ (heF ⟨1, (M.toPlaneMapWithMissing.arc e').target⟩)⟩
    have harc : J.h '' Set.range (M.toPlaneMapWithMissing.arc e') =
        Set.range (A.map.toPlaneMapWithMissing.arc e) := by
      rw [J.arc_range_map eb, ← he eb]
      exact congrArg (fun a => Set.range (A.map.toPlaneMapWithMissing.arc a))
        (I.edgeEquiv.apply_symm_apply e)
    rw [← harc]
    intro z hz
    apply mem_iUnion.mpr
    refine ⟨F, ?_⟩
    rw [← hm, ← J.h.image_closure]
    exact Set.image_mono heF hz
  have hfront (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
      frontier (τ F).val ⊆ A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.image := by
    obtain ⟨n, J, hF, _, he, hm⟩ := hseen F
    rw [← hm, ← J.h.image_frontier]
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨e, heF, hxe⟩ :=
      uibotClassSeparation4_source_frontier_covered_by_edges W H h0 hpast hp F x hx
    let eb : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n :=
      ⟨e, hF _ (frontier_subset_closure (heF ⟨0, (M.toPlaneMapWithMissing.arc e).source⟩)),
        hF _ (frontier_subset_closure (heF ⟨1, (M.toPlaneMapWithMissing.arc e).target⟩))⟩
    have hmem : J.h x ∈ Set.range (A.map.toPlaneMapWithMissing.arc (J.edgeEquiv eb).val) :=
      J.arc_range_map eb ▸ Set.mem_image_of_mem J.h hxe
    exact Or.inr (mem_iUnion.mpr ⟨(J.edgeEquiv eb).val, hmem⟩)
  have hidentify (F : A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
      (x : ℂ) (hx : x ∈ F.val) (hxU : x ∈ U) : ∃ F', τ F' = F := by
    obtain ⟨F', hxF'⟩ := mem_iUnion.mp hxU
    rw [closure_eq_self_union_frontier] at hxF'
    rcases hxF' with hxF' | hxF'
    · exact ⟨F', faces_eq_of_mem A.map.toPlaneMapWithMissing.toPlaneGraphDrawing
        (τ F') F hxF' hx⟩
    · exact (A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.face_subset_compl_image F hx
        (hfront F' hxF')).elim
  have hfaces : ∀ F : A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      (F.val ∩ U).Nonempty → F.val ⊆ U := by
    rintro F ⟨x, hx, hxU⟩
    obtain ⟨F', hF'⟩ := hidentify F x hx hxU
    intro y hy
    apply mem_iUnion.mpr
    exact ⟨F', subset_closure (hF'.symm ▸ hy)⟩
  obtain ⟨J0, _, _, _⟩ := hlocal 0
  have hU : U = Set.univ := uibotClassSeparation2_open_image_eq_univ A.map U hopen
    hvertices hedges hfaces (uibotClassSeparation2_face_has_boundary_vertex J0
      (uibotClassSeparation2_source_face_has_boundary_vertex W H h0 hpast hp))
  have hsurj : Function.Surjective τ := by
    intro F
    obtain ⟨x, hx⟩ := face_nonempty A.map.toPlaneMapWithMissing.toPlaneGraphDrawing F
    exact hidentify F x hx (hU.symm ▸ mem_univ x)
  have hfinite : LocallyFinite (fun F => closure (τ F).val) := by
    intro z
    obtain ⟨F, hzF⟩ := mem_iUnion.mp (show z ∈ U from hU.symm ▸ mem_univ z)
    obtain ⟨R, hR⟩ :=
      (uibotClassSeparation2_source_face_compact_finite_boundary W H h0 hpast hp F).1.isBounded.subset_ball (0 : ℂ)
    obtain ⟨r, _, hr⟩ :=
      uibotClassSeparation3_source_compact_faces_eventually_retained W H h0 hpast hp
        (Metric.closedBall (0 : ℂ) R) (isCompact_closedBall _ _)
    obtain ⟨J, _, he, _⟩ := hlocal r
    have hmap (F' : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
        (hF' : (closure F'.val ∩ Metric.closedBall (0 : ℂ) R).Nonempty) :
        J.h '' F'.val = (τ F').val := by
      have hret : F' ∈ d39GeomRetainedFaces M ρ (r + 1) := fun v hv =>
        D39GeomBallIsoV2.vertexBall_mono (Nat.le_succ r) (hr F' hF' v hv)
      exact (J.face_image_map ⟨F', hret⟩).trans
        (congrArg Subtype.val (hcoh r J he F' hret))
    have hzball : z ∈ J.h '' Metric.ball (0 : ℂ) R := by
      obtain ⟨x, hx⟩ := face_nonempty M.toPlaneMapWithMissing.toPlaneGraphDrawing F
      have hm := hmap F ⟨x, subset_closure hx,
        Metric.ball_subset_closedBall (hR (subset_closure hx))⟩
      rw [← hm, ← J.h.image_closure] at hzF
      exact Set.image_mono hR hzF
    have hballopen : IsOpen (J.h '' Metric.ball (0 : ℂ) R) :=
      J.h.isOpenMap _ Metric.isOpen_ball
    refine ⟨J.h '' Metric.ball (0 : ℂ) R, hballopen.mem_nhds hzball, ?_⟩
    have hloc := uibotClassSeparation3_source_closed_faces_locallyFinite W H h0 hpast hp
    apply (hloc.finite_nonempty_inter_compact (isCompact_closedBall (0 : ℂ) R)).subset
    rintro F' ⟨y, hy, hyball⟩
    obtain ⟨t, htball, htF'⟩ :=
      mem_closure_iff_nhds.mp hy _ (hballopen.mem_nhds hyball)
    obtain ⟨x, hxball, hxt⟩ := htball
    obtain ⟨F'', hxF''⟩ := hpoint x
    have hmeet : (closure F''.val ∩ Metric.closedBall (0 : ℂ) R).Nonempty :=
      ⟨x, hxF'', Metric.ball_subset_closedBall hxball⟩
    have htF'' : t ∈ closure (τ F'').val := by
      rw [← hmap F'' hmeet, ← J.h.image_closure]
      exact ⟨x, hxF'', hxt⟩
    have heq : F' = F'' := by
      rw [closure_eq_self_union_frontier] at htF''
      rcases htF'' with htF'' | htF''
      · exact hinj (faces_eq_of_mem A.map.toPlaneMapWithMissing.toPlaneGraphDrawing
          (τ F') (τ F'') htF' htF'')
      · exact (A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.face_subset_compl_image
          (τ F') htF' (hfront F'' htF'')).elim
    exact heq.symm ▸ hmeet
  exact ⟨Equiv.ofBijective τ ⟨hinj, hsurj⟩, hfinite, hU, hcoh⟩

/- REMAINING OBLIGATIONS. These are comments, not premises or declarations.

The target-face selection, independence of retaining ball witnesses, bijectivity,
and local finiteness of the target closed-face cover are proved above. The
open saturated union used in that proof is a union of closed target cells;
it is not yet the image of a constructed cellular map. The next missing step
is assembling the global edge parameters into boundary homeomorphisms, then
extending them and proving overlap compatibility. Pasting, injectivity,
finite target cover supplies a possible inverse-pasting route once compatible
cell maps and exact overlap correspondence have actually been constructed.

The exact remaining cellular-extension target, with its original binders, is:

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
  let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
  let M := uibotWholePlaneSourceMap W H G hp
  let ρ := uibotWholePlaneSourceRoot W H G
  ∀ I : D39CombDartIso M ρ A.map A.root,
    (∀ n : ℕ, ∃ J : D39GeomBallIsoV2 (n + 1) M ρ A.map A.root,
      (∀ v : uibotSeparationBallV (uibotWholePlaneSourceDomain W H G hp) n,
        I.vertexEquiv v.val = (J.vertexEquiv v).val) ∧
      (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
        I.edgeEquiv e.val = (J.edgeEquiv e).val) ∧
      (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
        I.flip e.val = J.edgeFlip e)) →
    ∃ (U : Set ℂ) (g : ℂ ≃ₜ U)
      (p : ∀ e : WholePlaneEdge W, unitInterval ≃ₜ unitInterval),
      IsOpen U ∧
      (∀ v, (g (M.toPlaneMapWithMissing.pos v) : ℂ) =
        A.map.toPlaneMapWithMissing.pos (I.vertexEquiv v)) ∧
      (∀ e t, (g (M.toPlaneMapWithMissing.arc e t) : ℂ) =
        A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e) (p e t)) ∧
      (∀ e, I.flip e = false → StrictMono (p e)) ∧
      (∀ e, I.flip e = true → StrictAnti (p e)) ∧
      (∀ F : A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
        (F.val ∩ U).Nonempty → F.val ⊆ U) ∧
      (∀ {z : ℂ} (L : Path z z) (w : ℂ), w ∉ Set.range L → ∀ n : ℤ,
        HasWinding L w n ↔
          HasWinding (L.map (continuous_subtype_val.comp g.continuous)) (g w : ℂ) n)

The remaining geometric-isomorphism target is:

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
  let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
  let M := uibotWholePlaneSourceMap W H G hp
  let ρ := uibotWholePlaneSourceRoot W H G
  (∀ r : ℕ, 0 < r → Nonempty (D39GeomBallIsoV2 r M ρ A.map A.root)) →
  Nonempty (D39GeomRootedMapIsoV2 M ρ A.map A.root)

The remaining almost-everywhere reconstruction target is:

letI uibotClassSeparation4ReconstructionMeasurable :
  MeasurableSpace D39GeomRootedMapClass.{0} :=
    borel D39GeomRootedMapClass.{0}
letI uibotClassSeparation4ReconstructionBorel :
  BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩
let F := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
let mu := (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
  MeasureTheory.Measure D39GeomRootedMapClass.{0})
∀ᵐ z ∂mu, F (uibotRecoveredCode z) = z

Use UIBOTClassReconstruction's measurable conull set and recovered-code law;
measurability of the class-equality event has not been assumed. No properness
assumption on A, geometric-class separation, qualifier removal, independent -/

end DirectedDistances.PaperProofs.Section3
end
