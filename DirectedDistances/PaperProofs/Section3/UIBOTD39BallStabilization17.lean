/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization16

/-! # Exterior certificates and ambient comparisons for whole-plane stage restrictions -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Set Metric Topology

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

private theorem bounded_face_of_finite_border_of_infinite
    {D V : Type*} [Infinite D] {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (F : P.Face) (hfin : {d | P.dartBorders d F}.Finite) :
    Bornology.IsBounded F.val := by
  have hcompact : IsCompact (frontier F.val) := by
    rw [frontier_eq_border_arcs_of_finite P hv F hfin]
    exact hfin.isCompact_biUnion fun d _ => (P.arc d).isCompact_image
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
    hcompact.isBounded
  by_contra hn
  have hunb := (P.isUnbounded_iff_not_isBounded F).mpr hn
  obtain ⟨z, hz, hzR⟩ := hunb R
  have hzout : z ∈ (closedBall (0 : ℂ) R)ᶜ := by
    simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hzR
  have hout : (closedBall (0 : ℂ) R)ᶜ ⊆ F.val := by
    apply (isConnected_compl_closedBall_complex R).isPreconnected.subset_of_closure_inter_subset
      (P.face_open_frontier_subset_image hv F).1 ⟨z, hzout, hz⟩
    rintro x ⟨hxcl, hxout⟩
    by_contra hxF
    have hxf : x ∈ frontier F.val := by
      rw [frontier, (P.face_open_frontier_subset_image hv F).1.interior_eq]
      exact ⟨hxcl, hxF⟩
    exact hxout (hR hxf)
  have hi : P.image ⊆ closedBall (0 : ℂ) R := by
    intro x hx
    by_contra hxb
    exact P.face_subset_compl F (hout hxb) hx
  have hall : (Set.univ : Set D).Finite :=
    (P.locally_finite (closedBall (0 : ℂ) R) isBounded_closedBall).subset (by
      intro d _
      exact ⟨(P.arc d).start, hi (Or.inr ⟨d, Or.inl rfl⟩), Or.inl rfl⟩)
  exact Set.infinite_univ hall

/-- Helper toward Proposition 3.9: the finite stage restriction contains
only original whole-plane geometric points. -/
theorem uibotWholePlaneStageDrawing_image_subset
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N m : ℕ) :
    (uibotWholePlaneStageDrawing W H G N m).image ⊆ G.image := by
  intro z hz
  rcases hz with ⟨v, rfl⟩ | ⟨d, hd⟩
  · exact Or.inl ⟨wholePlaneVertexι W N v.val, rfl⟩
  · exact Or.inr ⟨wholePlaneDartι W N (d.1.val, d.2), hd⟩

/-- Helper toward Proposition 3.9: every original triangle face remains
exactly the same bounded open set in a finite stage containing its creation.
The complete oriented bordering-dart characterization is retained. -/
theorem uibotWholePlaneStageDrawing_triangleFace
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N m : ℕ)
    (q : TriangleCreationTime (shiftedStream W N)) (hq : q.val < m) :
    let Q := uibotWholePlaneStageDrawing W H G N m
    ∃ F : Q.Face,
      F.val = (uibotWholePlaneWindowTriangleFace W H G N q).val ∧
      Bornology.IsBounded F.val ∧
      ∀ d, Q.dartBorders d F ↔
        (d.1.val, d.2) ∈ stageTriangleDartList (shiftedStream W N) q := by
  let Q := uibotWholePlaneStageDrawing W H G N m
  let F := G.toPlaneGraphDrawingFaceEquiv (uibotWholePlaneWindowTriangleFace W H G N q)
  have hv := uibhbot_faceOrbit_dartVertex_surjective W H
  have hfin : {d | G.dartBorders d F}.Finite := by
    apply ((stageTriangleDartList (shiftedStream W N) q).toFinset.finite_toSet.image
      (wholePlaneDartι W N)).subset
    intro d hd
    obtain ⟨a, ha, he⟩ := (uibotWholePlaneWindowTriangleFace_border W H G N q d).mp hd
    exact ⟨a, List.mem_toFinset.mpr ha, he⟩
  have hfront : frontier F.val ⊆ Q.image := by
    rw [frontier_eq_border_arcs_of_finite G hv F hfin]
    intro z hz
    obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp hz
    obtain ⟨a, ha, rfl⟩ := (uibotWholePlaneWindowTriangleFace_border W H G N q d).mp hd
    let b : StageDart (kmswStage (shiftedStream W N) m).nextEdge :=
      (⟨a.1, stageTriangleDartList_lt _ m q hq a ha⟩, a.2)
    exact Or.inr ⟨b, hzd⟩
  obtain ⟨FQ, heq⟩ := G.face_of_agree Q hv (A := F.val)
    (by
      rintro z ⟨hzG, hzcl⟩
      apply hfront
      rw [frontier, (G.face_open_frontier_subset_image hv F).1.interior_eq]
      exact ⟨hzcl, fun hzF => G.face_subset_compl F hzF hzG⟩)
    (by rintro z ⟨hzQ, _⟩; exact uibotWholePlaneStageDrawing_image_subset W H G N m hzQ)
    F (Subset.refl _)
  have hinj : Function.Injective (fun n : ℕ => wholePlaneDartι W 0 (n, false)) := by
    intro a b h
    exact congrArg Prod.fst (wholePlaneDartι_injective W 0 h)
  let uibotBallStab17InfiniteDarts : Infinite (WholePlaneDart W) := Infinite.of_injective _ hinj
  have hb := bounded_face_of_finite_border_of_infinite G hv F hfin
  refine ⟨FQ, heq, heq.symm ▸ hb, ?_⟩
  intro d
  rw [G.dartBorders_congr Q F FQ (uibotWholePlaneStageDrawing_arc W H G N m d) heq]
  change G.dartBorders _ (G.toPlaneGraphDrawingFaceEquiv
    (uibotWholePlaneWindowTriangleFace W H G N q)) ↔ _
  apply (uibotWholePlaneWindowTriangleFace_border W H G N q _).trans
  constructor
  · rintro ⟨a, ha, he⟩
    exact wholePlaneDartι_injective W N he ▸ ha
  · intro hd
    exact ⟨_, hd, rfl⟩

/-- Helper toward Proposition 3.9: the restriction of an arbitrary
whole-plane drawing has exactly the manuscript's finite exterior orbit. -/
theorem uibotWholePlaneStageDrawing_exterior
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N m : ℕ) :
    let Q := uibotWholePlaneStageDrawing W H G N m
    ∃ U : Q.Face, Q.IsUnbounded U ∧
      ∀ d, Q.dartBorders d U ↔ (kmswStageDirectedMap (shiftedStream W N) m).IsOuter d := by
  let u := shiftedStream W N
  let Q := uibotWholePlaneStageDrawing W H G N m
  obtain ⟨U, hU, _⟩ := Q.existsUnique_unbounded_face
  have hb (d) (hd : Q.dartBorders d U) : (kmswStageDirectedMap u m).IsOuter d := by
    rcases stage_dart_partition u m d with ho | ⟨q, ⟨hq, hdq⟩, _⟩
    · rw [kmswStage_isOuter_iff_boundary]
      have h := (stageOuterWord_mem_iff u m d).mp ho
      simpa only [List.mem_append, or_comm] using h
    · obtain ⟨F, _, hF, hchar⟩ := uibotWholePlaneStageDrawing_triangleFace W H G N m q hq
      have he : U = F := Q.dartBorders_face_unique d U F hd ((hchar d).mpr hdq)
      exact False.elim ((Q.isUnbounded_iff_not_isBounded U).mp hU (he.symm ▸ hF))
  refine ⟨U, hU, fun d => ⟨hb d, ?_⟩⟩
  intro hd
  obtain ⟨a, ha⟩ := Q.face_has_bordering_dart (kmswStageDrawing_vertex_surjective u m)
    (kmswRootedStage u m).root U
  have hcycle : (kmswMap u m).faceSucc.SameCycle a d := (hb a ha).symm.trans hd
  apply (kmswStageDrawing_leftFace_eq_iff Q d U).mp
  exact (kmswStageDrawing_leftFace_eq_of_sameCycle Q a d hcycle).symm.trans
    ((kmswStageDrawing_leftFace_eq_iff Q a U).mpr ha)

/-- Helper toward Proposition 3.9: one orientation-preserving ambient
homeomorphism compares any exterior-certified drawing of a finite stage to
its actual embedding in an arbitrary whole-plane drawing. It simultaneously
transports every labeled vertex and every ordered parameterized dart arc. -/
theorem uibotWholePlaneStageDrawing_ambient_homeomorph
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N m : ℕ)
    (P : StageDrawing (shiftedStream W N) m)
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap (shiftedStream W N) m).IsOuter d) :
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ v, h (P.pos v) = G.pos (wholePlaneVertexι W N v.val)) ∧
      ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
        ∀ t, h ((P.arc d).toPath t) =
          (G.arc (wholePlaneDartι W N (d.1.val, d.2))).toPath (φ t) := by
  obtain ⟨V, hV, hb⟩ := uibotWholePlaneStageDrawing_exterior W H G N m
  exact uibotFiniteStageDrawing_ambient_homeomorph P
    (uibotWholePlaneStageDrawing W H G N m) U V hU hV hborder hb

/-- Helper toward Proposition 3.9: arbitrary whole-plane drawings have
one compatible orientation-preserving ambient map on every finite stage.
This assertion requires neither recurrence nor a glued canonical drawing. -/
theorem uibotWholePlaneDrawings_stage_ambient_homeomorph
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G G' : WholePlaneDrawing W H) (N m : ℕ) :
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ v : Fin (kmswStage (shiftedStream W N) m).nextVertex,
        h (G.pos (wholePlaneVertexι W N v.val)) = G'.pos (wholePlaneVertexι W N v.val)) ∧
      ∀ d : StageDart (kmswStage (shiftedStream W N) m).nextEdge,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ t, h ((G.arc (wholePlaneDartι W N (d.1.val, d.2))).toPath t) =
            (G'.arc (wholePlaneDartι W N (d.1.val, d.2))).toPath (φ t) := by
  obtain ⟨U, hU, hb⟩ := uibotWholePlaneStageDrawing_exterior W H G N m
  exact uibotWholePlaneStageDrawing_ambient_homeomorph W H G' N m
    (uibotWholePlaneStageDrawing W H G N m) U hU hb

private def finiteStageBall (w : ℕ → Fin 3) (n : ℕ) : D39FiniteBall where
  D := StageDart (kmswStage w n).nextEdge
  map := kmswMap w n
  missing := (kmswStageDirectedMap w n).missing
  tail := (kmswStageDirectedMap w n).tail
  rootDart := (kmswRootedStage w n).root
  original := Set.univ
  original_closed := fun _ => Iff.rfl

private theorem finiteStageBall_connected (w : ℕ → Fin 3) (n : ℕ) :
    ∀ d e : (finiteStageBall w n).D, Relation.EqvGen
      (fun x y => (finiteStageBall w n).map.rot x = y ∨
        (finiteStageBall w n).map.edgeInv x = y) d e := by
  intro d e
  have h := kmswMap_isConnected w n d e
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | @tail b c _ hbc ih =>
    apply ih.trans
    rcases hbc with h | h | h | h
    · exact Relation.EqvGen.rel _ _ (Or.inl h.symm)
    · apply Relation.EqvGen.symm
      apply Relation.EqvGen.rel
      left
      exact (congrArg (kmswMap w n).rot h).trans
        ((kmswMap w n).rot.apply_symm_apply _)
    · exact Relation.EqvGen.rel _ _ (Or.inr h.symm)
    · apply Relation.EqvGen.symm
      apply Relation.EqvGen.rel
      right
      exact (congrArg (kmswMap w n).edgeInv h).trans
        ((kmswMap w n).edgeInv.apply_symm_apply _)

/-- Helper toward Proposition 3.9: a single ambient homeomorphism between
arbitrary whole-plane drawings transports the entire finite stage and all its
original triangle faces, with increasing parameters for every ordered dart. -/
theorem uibotWholePlaneDrawings_stage_geometry
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G G' : WholePlaneDrawing W H) (N m : ℕ) :
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ v : Fin (kmswStage (shiftedStream W N) m).nextVertex,
        h (G.pos (wholePlaneVertexι W N v.val)) = G'.pos (wholePlaneVertexι W N v.val)) ∧
      (∀ d : StageDart (kmswStage (shiftedStream W N) m).nextEdge,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ t, h ((G.arc (wholePlaneDartι W N (d.1.val, d.2))).toPath t) =
            (G'.arc (wholePlaneDartι W N (d.1.val, d.2))).toPath (φ t)) ∧
      ∀ q : TriangleCreationTime (shiftedStream W N), q.val < m →
        h '' (uibotWholePlaneWindowTriangleFace W H G N q).val =
          (uibotWholePlaneWindowTriangleFace W H G' N q).val := by
  let u := shiftedStream W N
  let P := uibotWholePlaneStageDrawing W H G N m
  let P' := uibotWholePlaneStageDrawing W H G' N m
  obtain ⟨U, hU, hb⟩ := uibotWholePlaneStageDrawing_exterior W H G N m
  obtain ⟨U', hU', hb'⟩ := uibotWholePlaneStageDrawing_exterior W H G' N m
  let B := finiteStageBall u m
  have hv := kmswStageDrawing_vertex_surjective u m
  obtain ⟨O, hO⟩ := B.plOrbitFace_surjective (stageVertex u m) P hv U
  obtain ⟨d, hd⟩ := O.property
  have hdO : d ∈ O.val := hd.symm ▸ Equiv.Perm.SameCycle.rfl
  have hdU := (B.plOrbitFace_eq_iff (stageVertex u m) P hv O d hdO U).mp hO
  have hO' : B.plOrbitFace (stageVertex u m) P' hv O = U' :=
    (B.plOrbitFace_eq_iff (stageVertex u m) P' hv O d hdO U').mpr
      ((hb' d).mpr ((hb d).mp hdU))
  obtain ⟨h, ho, hp, ha, hf⟩ := ReverseComparison2.exists_plDrawing_homeomorph
    B (stageVertex u m) P P' hv (finiteStageBall_connected u m) O
    ⟨hO.symm ▸ (P.isUnbounded_iff_not_isBounded U).mp hU,
      hO'.symm ▸ (P'.isUnbounded_iff_not_isBounded U').mp hU'⟩
  refine ⟨h, ho, hp, ha, ?_⟩
  intro q hq
  obtain ⟨F, hF, _, hchar⟩ := uibotWholePlaneStageDrawing_triangleFace W H G N m q hq
  obtain ⟨F', hF', _, hchar'⟩ := uibotWholePlaneStageDrawing_triangleFace W H G' N m q hq
  let a := stageTriangleDart₁ u m q hq
  have ham : (a.1.val, a.2) ∈ stageTriangleDartList u q := by
    simp only [a, stageTriangleDart₁, stageTriangleDartAt, stageTriangleDartList,
      List.mem_cons, List.not_mem_nil, or_false, true_or]
  let T : D39BallFaceCycleOrbit B := ⟨{e | B.map.faceSucc.SameCycle a e}, a, rfl⟩
  have haT : a ∈ T.val := Equiv.Perm.SameCycle.rfl
  have he : B.plOrbitFace (stageVertex u m) P hv T = F :=
    (B.plOrbitFace_eq_iff (stageVertex u m) P hv T a haT F).mpr ((hchar a).mpr ham)
  have he' : B.plOrbitFace (stageVertex u m) P' hv T = F' :=
    (B.plOrbitFace_eq_iff (stageVertex u m) P' hv T a haT F').mpr ((hchar' a).mpr ham)
  have hm := hf T
  rw [he, he', hF, hF'] at hm
  exact hm

/-- Helper toward Proposition 3.9: whole-plane drawing independence holds
on every captured ball. One ambient orientation-preserving homeomorphism
realizes positions, parameterized arcs and the full original retained faces. -/
theorem uibotWholePlaneDrawings_captured_ballIso
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G G' : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hr : 0 < r)
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    Nonempty (D39GeomBallIsoV2 r
      (uibotWholePlaneGeometricMap W H G hp) (uibotWholePlaneGeometricRoot W H G)
      (uibotWholePlaneGeometricMap W H G' hp) (uibotWholePlaneGeometricRoot W H G')) := by
  classical
  obtain ⟨h, ho, hpos, harc, hface⟩ :=
    uibotWholePlaneDrawings_stage_geometry W H G G' N (2 * N)
  let M := uibotWholePlaneGeometricMap W H G hp
  let M' := uibotWholePlaneGeometricMap W H G' hp
  let rho := uibotWholePlaneGeometricRoot W H G
  let rho' := uibotWholePlaneGeometricRoot W H G'
  let A := {F // F ∈ d39GeomRetainedFaces M rho r}
  let B := {F // F ∈ d39GeomRetainedFaces M' rho' r}
  have hex (F : A) : ∃ q : TriangleCreationTime (shiftedStream W N),
      q.val < 2 * N ∧ F.val = uibotWholePlaneWindowTriangleFace W H G N q :=
    (uibotWholePlane_retainedFace_windowTriangle W H G hp N r hcap F.val F.property).exists
  choose q hq hF using hex
  have hret (p : TriangleCreationTime (shiftedStream W N)) :
      uibotWholePlaneWindowTriangleFace W H G N p ∈ d39GeomRetainedFaces M rho r ↔
      uibotWholePlaneWindowTriangleFace W H G' N p ∈ d39GeomRetainedFaces M' rho' r :=
    (uibotWholePlaneWindowTriangleFace_retained_iff W H G hp N r hcap p).trans
      (uibotWholePlaneWindowTriangleFace_retained_iff W H G' hp N r hcap p).symm
  let f : A → B := fun F => ⟨uibotWholePlaneWindowTriangleFace W H G' N (q F),
    (hret (q F)).mp (hF F ▸ F.property)⟩
  have hfi : Function.Injective f := by
    intro F K he
    have heq : q F = q K := uibotWholePlaneWindowTriangleFace_injective W H G' N
      (congrArg Subtype.val he)
    apply Subtype.ext
    exact (hF F).trans ((congrArg (uibotWholePlaneWindowTriangleFace W H G N) heq).trans (hF K).symm)
  have hfs : Function.Surjective f := by
    intro K
    obtain ⟨p, ⟨hp', hK⟩, _⟩ :=
      uibotWholePlane_retainedFace_windowTriangle W H G' hp N r hcap K.val K.property
    let F : A := ⟨uibotWholePlaneWindowTriangleFace W H G N p,
      (hret p).mpr (hK ▸ K.property)⟩
    have heq : p = q F := uibotWholePlaneWindowTriangleFace_injective W H G N (hF F)
    refine ⟨F, Subtype.ext ?_⟩
    change uibotWholePlaneWindowTriangleFace W H G' N (q F) = K.val
    rw [← heq]
    exact hK.symm
  let E := Equiv.ofBijective f ⟨hfi, hfs⟩
  have himage (F : A) : h '' F.val.val = (E F).val.val := by
    change h '' F.val.val = (uibotWholePlaneWindowTriangleFace W H G' N (q F)).val
    rw [hF F]
    exact hface (q F) (hq F)
  have hvmap (v : {v // v ∈ d39GeomBallVertices M rho r}) :
      h (G.pos v.val) = G'.pos v.val := by
    have hv := Eq.mp (congrArg (fun S : Set (WholePlaneVertex W) => v.val ∈ S)
      (uibotWholePlaneGeometricBallVertices_eq_window W H G hp N r hcap)) v.property
    obtain ⟨a, ha, he⟩ := hv
    have hal : a < (kmswStage (shiftedStream W N) (2 * N)).nextVertex := by
      exact (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
    exact he ▸ hpos ⟨a, hal⟩
  have ha (e : {e // e ∈ d39GeomBallEdges M rho r}) :
      ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
        ∀ t, h (M.arc e.val t) = M'.arc e.val (φ t) := by
    have he := (uibotWholePlaneGeometricBallEdge_iff W H G hp r e.val).mp e.property
    obtain ⟨a, _, hae⟩ := (uibotWholePlane_rootBallEdges_bijOn W N r hcap).surjOn he
    let d : StageDart (kmswStage (shiftedStream W N) (2 * N)).nextEdge := (a, e.val.out.2)
    have hd : wholePlaneDartι W N (d.1.val, d.2) = e.val.out := Prod.ext hae rfl
    obtain ⟨φ, hφ, hpath⟩ := harc d
    refine ⟨φ, hφ, ?_⟩
    intro t
    change h ((G.arc e.val.out).toPath t) = (G'.arc e.val.out).toPath (φ t)
    rw [← hd]
    exact hpath t
  choose φ hφ hpath using ha
  exact ⟨{
    radius_pos := hr
    h := h
    orientationPreserving := ho
    vertexEquiv := Equiv.refl _
    edgeEquiv := Equiv.refl _
    faceEquiv := E
    edgeFlip := fun _ => false
    pos_map := hvmap
    edgeParam := φ
    edgeParam_mono := fun e _ => hφ e
    edgeParam_anti := by intro e he; cases he
    arc_map := hpath
    src_map := fun _ => rfl
    tgt_map := fun _ => rfl
    missing_map := fun _ => Iff.rfl
    orientation_map := by intro e he; exact (Bool.xor_false _).symm
    root_edge_map := rfl
    root_bool_map := (Bool.xor_false _).symm
    face_image_map := himage }⟩

private theorem finite_triangle_face {w : ℕ → Fin 3} {n : ℕ}
    (P : StageDrawing w n) (U : P.Face)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d)
    (q : TriangleCreationTime w) (hq : q.val < n) :
    ∃ F : P.toPlaneGraphDrawing.Face,
      ∀ d : StageDart (kmswStage w n).nextEdge,
        P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
          (d.1.val, d.2) ∈ stageTriangleDartList w q := by
  let d := stageTriangleDart₁ w n q hq
  have hdq : (d.1.val, d.2) ∈ stageTriangleDartList w q := by
    simp only [d, stageTriangleDart₁, stageTriangleDartAt, stageTriangleDartList,
      List.mem_cons, List.not_mem_nil, or_false, true_or]
  let F := kmswStageDrawing_leftFace P d
  have hd : P.dartBorders d F := (kmswStageDrawing_leftFace_eq_iff P d F).mp rfl
  have hFU : F ≠ U := by
    intro he
    have ho := (hborder d).mp (he ▸ hd)
    have hon : d ∈ stageOuterWord w n := by
      rw [kmswStage_isOuter_iff_boundary] at ho
      apply (stageOuterWord_mem_iff w n d).mpr
      simpa only [List.mem_append, or_comm] using ho
    exact stageTriangleDart_not_outer w n q hq d hdq hon
  obtain ⟨k, ⟨hk, hchar⟩, _⟩ :=
    uibotFiniteStage_nonexteriorFace_triangle P U hborder F hFU
  have hkq : k = q := by
    by_contra hne
    exact (List.disjoint_left.mp (stageTriangleDartLists_disjoint w n k q hk hq hne))
      ((hchar d).mp hd) hdq
  exact ⟨P.toPlaneGraphDrawingFaceEquiv.symm F, by
    intro e
    rw [Equiv.apply_symm_apply]
    exact hkq ▸ hchar e⟩

private theorem window_triangle_mem (w u : ℕ → Fin 3) (s m : ℕ)
    (hcode : ∀ i < m, w (s + i) = u i)
    (q : TriangleCreationTime u) (hq : q.val < m)
    (hc : w (s + q.val) = 0 ∨ w (s + q.val) = 1) (d : ℕ × Bool) :
    d ∈ stageTriangleDartList w ⟨s + q.val, hc⟩ ↔
      ∃ a, a ∈ stageTriangleDartList u q ∧
        (kmswWindowEdgeMapInf w s a.1, a.2) = d := by
  have hs : kmswStage (fun i => w (s + i)) q.val = kmswStage u q.val :=
    kmswStage_congr (fun i hi => hcode i (hi.trans hq))
  have hsfull : kmswStage (fun i => w (s + i)) m = kmswStage u m :=
    kmswStage_congr hcode
  have hl : stageTriangleDartList (fun i => w (s + i)) ⟨q.val, hc⟩ =
      stageTriangleDartList u q := by
    simp only [stageTriangleDartList, stageTriangleDartTriple, hs, hcode q.val hq]
  have hr := kmswWindowPatchData_triangle_rotated w s m q.val hq hc
  rw [hl] at hr
  have hm (a : ℕ × Bool) (ha : a ∈ stageTriangleDartList u q) :
      ((kmswWindowPatchData w s m).φ a.1, a.2) =
        (kmswWindowEdgeMapInf w s a.1, a.2) := by
    apply Prod.ext
    · symm
      apply kmswWindowEdgeMapInf_eq_stage
      rw [hsfull]
      exact stageTriangleDartList_lt u m q hq a ha
    · rfl
  constructor
  · intro hd
    obtain ⟨a, ha, he⟩ := List.mem_map.mp (hr.mem_iff.mpr hd)
    exact ⟨a, ha, (hm a ha).symm.trans he⟩
  · rintro ⟨a, ha, he⟩
    exact hr.mem_iff.mp (List.mem_map.mpr ⟨a, ha, (hm a ha).trans he⟩)

/-- Helper toward Proposition 3.9: a triangle created in a finite window
is the same bounded original face in the global and restricted drawings,
with its complete local bordering-dart characterization. -/
theorem uibotFiniteWindowStageDrawing_triangleFace
    (w : ℕ → Fin 3) (s m : ℕ) (P : StageDrawing w (s + m))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w (s + m)).IsOuter d)
    (q : TriangleCreationTime (fun i => w (s + i))) (hq : q.val < m) :
    let Q := uibotFiniteWindowStageDrawing w s m P
    ∃ (F : P.Face) (FQ : Q.Face), FQ.val = F.val ∧ Bornology.IsBounded F.val ∧
      (∀ d, P.dartBorders d F ↔
        (d.1.val, d.2) ∈ stageTriangleDartList w ⟨s + q.val, q.property⟩) ∧
      ∀ d, Q.dartBorders d FQ ↔
        (d.1.val, d.2) ∈ stageTriangleDartList (fun i => w (s + i)) q := by
  let u := fun i => w (s + i)
  let Q := uibotFiniteWindowStageDrawing w s m P
  let q0 : TriangleCreationTime w := ⟨s + q.val, q.property⟩
  have hq0 : q0.val < s + m := Nat.add_lt_add_left hq s
  obtain ⟨F, hchar⟩ := finite_triangle_face P U hborder q0 hq0
  let F0 := P.toPlaneGraphDrawingFaceEquiv F
  have hFU : F0 ≠ U := by
    intro he
    let d := stageTriangleDart₁ w (s + m) q0 hq0
    have hdm : (d.1.val, d.2) ∈ stageTriangleDartList w q0 := by
      simp only [d, stageTriangleDart₁, stageTriangleDartAt, stageTriangleDartList,
        List.mem_cons, List.not_mem_nil, or_false, true_or]
    have hb := (hborder d).mp (he ▸ (hchar d).mpr hdm)
    have ho : d ∈ stageOuterWord w (s + m) := by
      rw [kmswStage_isOuter_iff_boundary] at hb
      apply (stageOuterWord_mem_iff w (s + m) d).mpr
      rcases hb with ⟨hd, hm⟩ | ⟨hd, hm⟩
      · exact Or.inl ⟨hd, List.mem_append.mp hm⟩
      · exact Or.inr ⟨hd, (List.mem_append.mp hm).symm⟩
    exact stageTriangleDart_not_outer w (s + m) q0 hq0 d hdm ho
  have hbound : Bornology.IsBounded F0.val := by
    by_contra hn
    obtain ⟨U0, _, hu⟩ := P.existsUnique_unbounded_face
    exact hFU ((hu F0 ((P.isUnbounded_iff_not_isBounded F0).mpr hn)).trans (hu U hU).symm)
  have hlocal (d : StageDart (kmswStage u m).nextEdge) :
      P.dartBorders (kmswWindowDartMap w s m d) F0 ↔
        (d.1.val, d.2) ∈ stageTriangleDartList u q := by
    apply (hchar _).trans
    apply (window_triangle_mem w u s m (fun _ _ => rfl) q hq q.property _).trans
    have hmap : kmswWindowEdgeMapInf w s d.1.val = (kmswWindowPatchData w s m).φ d.1.val :=
      kmswWindowEdgeMapInf_eq_stage w s m d.1.val d.1.isLt
    constructor
    · rintro ⟨a, ha, he⟩
      have he' : a = (d.1.val, d.2) := by
        apply Prod.ext
        · apply kmswWindowEdgeMapInf_injective w s
          exact (congrArg Prod.fst he).trans hmap.symm
        · have hb := congrArg (fun z : ℕ × Bool => z.2) he
          exact hb
      exact he' ▸ ha
    · intro hd
      exact ⟨_, hd, Prod.ext hmap rfl⟩
  have hfront : frontier F0.val ⊆ Q.image := by
    rw [frontier_eq_border_arcs_of_finite P (kmswStageDrawing_vertex_surjective w (s + m)) F0 (Set.toFinite _)]
    intro z hz
    obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp hz
    obtain ⟨a, ha, he⟩ := (window_triangle_mem w u s m (fun _ _ => rfl)
      q hq q.property _).mp ((hchar d).mp hd)
    let b : StageDart (kmswStage u m).nextEdge :=
      (⟨a.1, stageTriangleDartList_lt u m q hq a ha⟩, a.2)
    have hbd : kmswWindowDartMap w s m b = d := by
      apply Prod.ext
      · apply Fin.ext
        exact (kmswWindowEdgeMapInf_eq_stage w s m a.1 b.1.isLt).symm.trans (congrArg Prod.fst he)
      · exact congrArg (fun z : ℕ × Bool => z.2) he
    exact Or.inr ⟨b, by change z ∈ (P.arc (kmswWindowDartMap w s m b)).image; rw [hbd]; exact hzd⟩
  have hsub : Q.image ⊆ P.image := by
    rintro z (⟨v, rfl⟩ | ⟨d, hd⟩)
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨kmswWindowDartMap w s m d, hd⟩
  have hv := kmswStageDrawing_vertex_surjective w (s + m)
  obtain ⟨FQ, heq⟩ := P.face_of_agree Q hv (A := F0.val)
    (by
      rintro z ⟨hzP, hzcl⟩
      apply hfront
      rw [frontier, (P.face_open_frontier_subset_image hv F0).1.interior_eq]
      exact ⟨hzcl, fun hzF => P.face_subset_compl F0 hzF hzP⟩)
    (by rintro z ⟨hzQ, _⟩; exact hsub hzQ) F0 (Subset.refl _)
  refine ⟨F0, FQ, heq, hbound, hchar, ?_⟩
  intro d
  exact (P.dartBorders_congr Q F0 FQ (uibotFiniteWindowStageDrawing_arc w s m P d) heq).trans (hlocal d)

/-- Helper toward Proposition 3.9: a finite shifted-window restriction
has the source exterior orbit whenever the original finite drawing does. -/
theorem uibotFiniteWindowStageDrawing_exterior
    (w : ℕ → Fin 3) (s m : ℕ) (P : StageDrawing w (s + m))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w (s + m)).IsOuter d) :
    let Q := uibotFiniteWindowStageDrawing w s m P
    ∃ V : Q.Face, Q.IsUnbounded V ∧
      ∀ d, Q.dartBorders d V ↔ (kmswStageDirectedMap (fun i => w (s + i)) m).IsOuter d := by
  let u := fun i => w (s + i)
  let Q := uibotFiniteWindowStageDrawing w s m P
  obtain ⟨V, hV, _⟩ := Q.existsUnique_unbounded_face
  have hb (d) (hd : Q.dartBorders d V) : (kmswStageDirectedMap u m).IsOuter d := by
    rcases stage_dart_partition u m d with ho | ⟨q, ⟨hq, hdq⟩, _⟩
    · rw [kmswStage_isOuter_iff_boundary]
      have h := (stageOuterWord_mem_iff u m d).mp ho
      simpa only [List.mem_append, or_comm] using h
    · obtain ⟨F, FQ, heq, hF, _, hchar⟩ :=
        uibotFiniteWindowStageDrawing_triangleFace w s m P U hU hborder q hq
      have he : V = FQ := Q.dartBorders_face_unique d V FQ hd ((hchar d).mpr hdq)
      exact False.elim ((Q.isUnbounded_iff_not_isBounded V).mp hV
        ((congrArg Subtype.val he).trans heq |>.symm ▸ hF))
  refine ⟨V, hV, fun d => ⟨hb d, ?_⟩⟩
  intro hd
  obtain ⟨a, ha⟩ := Q.face_has_bordering_dart (kmswStageDrawing_vertex_surjective u m)
    (kmswRootedStage u m).root V
  have hcycle : (kmswMap u m).faceSucc.SameCycle a d := (hb a ha).symm.trans hd
  apply (kmswStageDrawing_leftFace_eq_iff Q d V).mp
  exact (kmswStageDrawing_leftFace_eq_of_sameCycle Q a d hcycle).symm.trans
    ((kmswStageDrawing_leftFace_eq_iff Q a V).mpr ha)

/-- Helper toward Proposition 3.9: one orientation-preserving ambient
homeomorphism transports the actual finite-window patch to its canonical
finite-stage drawing, preserving positions and all parameterized dart arcs. -/
theorem uibotFiniteWindowStageDrawing_ambient_canonical
    (w : ℕ → Fin 3) (s m : ℕ) (P : StageDrawing w (s + m))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w (s + m)).IsOuter d) :
    let C := familyQ (fun i => w (s + i)) (monotone_family_all (fun i => w (s + i))) m
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ v : Fin (kmswStage (fun i => w (s + i)) m).nextVertex,
        h (P.pos ⟨kmswWindowPatchVertexMap w s m v.val,
          (kmswWindowPatchVertexMap_rel w s m).vertex_bound v.val v.isLt⟩) = C.pos v) ∧
      ∀ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ t, h ((P.arc (kmswWindowDartMap w s m d)).toPath t) = (C.arc d).toPath (φ t) := by
  obtain ⟨V, hV, hb⟩ := uibotFiniteWindowStageDrawing_exterior w s m P U hU hborder
  obtain ⟨Vc, hVc, _, hbc⟩ := uibotCanonicalStage_exterior (fun i => w (s + i)) m
  exact uibotFiniteStageDrawing_ambient_homeomorph
    (uibotFiniteWindowStageDrawing w s m P) _ V Vc hV hVc hb hbc





























end DirectedDistances.PaperProofs.Section3
end
