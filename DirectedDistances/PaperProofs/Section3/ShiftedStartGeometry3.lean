/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry2
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumer52FaceOrbits
public import DirectedDistances.PaperProofs.Section3.UIBOTClassSeparation6

/-! Helper toward Proposition 3.9: bounded complementary cells at shifted starts. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open Set Topology

private theorem window_triangle_image (w : ℕ → Fin 3) (s : ℕ)
    (j : TriangleCreationTime (fun i => w (s + i))) :
    (fun d : ℕ × Bool => (kmswWindowEdgeMapInf w s d.1, d.2)) ''
        {d | d ∈ stageTriangleDartList (fun i => w (s + i)) j} =
      {d | d ∈ stageTriangleDartList w ⟨s + j.val, j.property⟩} := by
  have hr := kmswWindowPatchData_triangle_rotated w s (j.val + 1) j.val
    (Nat.lt_succ_self _) j.property
  have he (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList (fun i => w (s + i)) j) :
      kmswWindowEdgeMapInf w s d.1 = (kmswWindowPatchData w s (j.val + 1)).φ d.1 :=
    kmswWindowEdgeMapInf_eq_stage w s (j.val + 1) d.1
      (stageTriangleDartList_lt _ _ j (Nat.lt_succ_self _) d hd)
  ext d
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact hr.mem_iff.mp (List.mem_map.mpr
      ⟨a, ha, congrArg (fun e => (e, a.2)) (he a ha).symm⟩)
  · intro hd
    obtain ⟨a, ha, had⟩ := List.mem_map.mp (hr.mem_iff.mpr hd)
    exact ⟨a, ha, (congrArg (fun e => (e, a.2)) (he a ha)).trans had⟩

private theorem start_dart_eq (W : ℤ → Fin 3) (n : ℤ)
    (J : WholePlaneStartIso W n) (d : ℕ × Bool) :
    J.dart (wholePlaneDartι (shiftWordInt W n) 0 d) =
      (lemma38StartEdgeι W n d.1, d.2) := by
  erw [J.dart_apply, J.iota_edge]
  rfl

/-- Helper toward Proposition 3.9: each shifted creation triangle is the
same three geometric darts as a triangle in a nonpositive-start run. -/
theorem start_triangle_image (W : ℤ → Fin 3) (n : ℤ)
    (J : WholePlaneStartIso W n)
    (j : TriangleCreationTime (shiftedStream (shiftWordInt W n) 0)) :
    ∃ (N : ℕ) (k : TriangleCreationTime (shiftedStream W N)),
      (fun d => J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)) ''
          {d | d ∈ stageTriangleDartList (shiftedStream (shiftWordInt W n) 0) j} =
        wholePlaneDartι W N '' {d | d ∈ stageTriangleDartList (shiftedStream W N) k} := by
  have hd : (fun d => J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)) =
      fun d : ℕ × Bool => (lemma38StartEdgeι W n d.1, d.2) :=
    funext (start_dart_eq W n J)
  rw [hd]
  have ht (u v : ℕ → Fin 3) (he : u = v) (a : TriangleCreationTime u) :
      stageTriangleDartList u a = stageTriangleDartList v (he ▸ a) := by
    subst v
    rfl
  by_cases hn : n ≤ 0
  · have hu : shiftedStream (shiftWordInt W n) 0 = shiftedStream W n.natAbs := by
      funext i
      simp only [shiftedStream, shiftWordInt, Int.ofNat_zero, sub_zero]
      congr 1
      have hh := Int.ofNat_natAbs_of_nonpos hn
      omega
    simp only [lemma38StartEdgeι, ite_eq_left hn]
    refine ⟨n.natAbs, hu ▸ j, ?_⟩
    rw [ht _ _ hu j]
    rfl
  · have hu : shiftedStream (shiftWordInt W n) 0 =
        fun i => shiftedStream W 0 (n.toNat + i) := by
      funext i
      simp only [shiftedStream, shiftWordInt, Int.ofNat_zero, sub_zero, Nat.cast_add]
      congr 1
      have hh := Int.toNat_of_nonneg (show 0 ≤ n by omega)
      omega
    simp only [lemma38StartEdgeι, ite_eq_right hn]
    let k : TriangleCreationTime (fun i => shiftedStream W 0 (n.toNat + i)) := hu ▸ j
    refine ⟨0, ⟨n.toNat + k.val, k.property⟩, ?_⟩
    have hi := congrArg (fun s => wholePlaneDartι W 0 '' s)
      (window_triangle_image (shiftedStream W 0) n.toNat k)
    rw [Set.image_image] at hi
    rw [ht _ _ hu j]
    exact hi

/-- Helper toward Proposition 3.9: each shifted creation triangle borders
exactly one actual glued face, with precisely its three transported darts. -/
theorem start_triangle_glued_face (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (j : TriangleCreationTime (shiftedStream (shiftWordInt W n) 0)) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    ∃ F : G.Face, {d | G.dartBorders d F} =
      (fun d => J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)) ''
        {d | d ∈ stageTriangleDartList (shiftedStream (shiftWordInt W n) 0) j} := by
  intro G
  obtain ⟨N, k, hk⟩ := start_triangle_image W n J j
  let a := wholePlaneDartι W N (stageTriangleDartTriple (shiftedStream W N) k).1
  obtain ⟨F, ha⟩ := WholePlaneGlueFaceCorrespondenceFull.dart_borders_exists W h hpast H a
  refine ⟨F, ?_⟩
  rw [hk]
  ext d
  constructor
  · intro hd
    exact (futureMaps_triangle_orbit W H N k d).mp
      ((WholePlaneGlueFaceCorrespondenceFull.faceOrbit_iff_common_face
        W h hpast H a d).mpr ⟨F, ha, hd⟩)
  · intro hd
    obtain ⟨F', ha', hd'⟩ :=
      (WholePlaneGlueFaceCorrespondenceFull.faceOrbit_iff_common_face
        W h hpast H a d).mp ((futureMaps_triangle_orbit W H N k d).mpr hd)
    have he := WholePlaneGlueSeamFaces.glueSeamFaces_dartBorders_unique
      W h hpast H a F' F ha' ha
    exact he ▸ hd'

private theorem finite_face_frontier
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

/-- Helper toward Proposition 3.9: every shifted creation cell has a disk
chart with its entire frontier exactly the image of the unit circle. -/
theorem creation_face_disk_chart (u : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence u) (j : TriangleCreationTime u) :
    ∃ c : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure (capFace u hfin j).val,
      ∀ z, ((c z : ℂ) ∈ frontier (capFace u hfin j).val ↔ ‖(z : ℂ)‖ = 1) := by
  rw [(capFace_spec u hfin j).1]
  exact uibotClassSeparation3_graphCap_disk_chart _

/-- Helper toward Proposition 3.9: every actual glued face has a disk
chart, on the dart-based face carrier used by the inherited drawing. -/
theorem glued_face_disk_chart (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hpast H).Face) :
    ∃ c : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure F.val,
      ∀ z, ((c z : ℂ) ∈ frontier F.val ↔ ‖(z : ℂ)‖ = 1) := by
  have hcap : ∃ (C : GraphCap) (T : ℂ ≃ₜ ℂ), F.val = T '' C.region := by
    rcases WholePlanePastGlueDrawing.glueDrawing_faces W h hpast H F with
      ⟨F0, hb, he⟩ | ⟨Fp, hb, he⟩
    · obtain ⟨m, i, hi⟩ := limitDrawing_boundedFace_eq_capRegion_twoSided
        (shiftedStream W 0) (H.1 0) h F0 hb
      refine ⟨(familyG (shiftedStream W 0) (monotone_family_all _) m).cap i,
        Homeomorph.refl ℂ, ?_⟩
      change F.val = id '' _
      rw [Set.image_id]
      exact he.trans hi
    · obtain ⟨m, i, hi⟩ := limitDrawing_boundedFace_eq_capRegion_twoSided
        (kmswPastCode W) (WholePlanePastGlueData.past_finiteIncidence W H) hpast Fp hb
      refine ⟨(familyG (kmswPastCode W) (monotone_family_all _) m).cap i,
        PastDrawingTransfer.transfer (shiftedStream W 0) (kmswPastCode W)
          h hpast (H.1 0) (WholePlanePastGlueData.past_finiteIncidence W H), ?_⟩
      exact he.trans (congrArg (fun s => _ '' s) hi)
  obtain ⟨C, T, hF⟩ := hcap
  obtain ⟨c, hc⟩ := uibotClassSeparation3_graphCap_disk_chart C
  have hcl : T '' closure C.region = closure F.val := by rw [T.image_closure, ← hF]
  let E : closure C.region ≃ₜ closure F.val :=
    (T.image _).trans (Homeomorph.setCongr hcl)
  refine ⟨c.trans E, ?_⟩
  intro z
  change T (c z : ℂ) ∈ frontier F.val ↔ _
  rw [hF, ← T.image_frontier, T.injective.mem_set_image]
  exact hc z

/-- Helper toward Proposition 3.9: a shifted creation triangle is an
actual complementary face of the inherited restriction. Its entire region
equals a glued face, and its dart incidence is exactly the transported triple. -/
theorem start_triangle_inherited_face (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (j : TriangleCreationTime (shiftedStream (shiftWordInt W n) 0)) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    ∃ (F : Q.Face) (B : G.Face), F.val = B.val ∧
      {d | G.dartBorders d B} =
        (fun d => J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)) ''
          {d | d ∈ stageTriangleDartList (shiftedStream (shiftWordInt W n) 0) j} ∧
      ∀ d : retainedDarts W n univ, Q.dartBorders d F ↔ G.dartBorders d.val B := by
  intro G Q
  obtain ⟨B, hB⟩ := start_triangle_glued_face W H h hpast n J j
  have hfinite : {d | G.dartBorders d B}.Finite := by
    rw [hB]
    exact (List.finite_toSet _).image _
  have hfront := finite_face_frontier G (WholePlanePastGlueData.vertex_incident W) B hfinite
  have hret (d : WholePlaneDart W) (hd : G.dartBorders d B) :
      d ∈ retainedDarts W n univ := by
    have hd' : d ∈ {d | G.dartBorders d B} := hd
    rw [hB] at hd'
    obtain ⟨a, _, rfl⟩ := hd'
    rw [retained_darts_eq_image W n J univ]
    exact ⟨a, mem_univ _, rfl⟩
  have hXY : G.image ∩ closure B.val ⊆ Q.image := by
    intro z hz
    have hzf : z ∈ frontier B.val := by
      rw [frontier, (G.face_open_frontier_subset_image
        (WholePlanePastGlueData.vertex_incident W) B).1.interior_eq]
      exact ⟨hz.2, fun hb => G.face_subset_compl B hb hz.1⟩
    rw [hfront] at hzf
    obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp hzf
    exact Or.inr ⟨⟨d, hret d hd⟩, hzd⟩
  have hYX : Q.image ∩ B.val ⊆ G.image := fun _ hz =>
    inherited_image_subset W H G n univ hz.1
  obtain ⟨F, hF⟩ := G.face_of_agree Q (WholePlanePastGlueData.vertex_incident W)
    hXY hYX B Subset.rfl
  exact ⟨F, B, hF, hB, fun d =>
    G.dartBorders_congr Q B F (inherited_arc W H G n univ d) hF⟩

private theorem restricted_boundary_homeomorph
    (S T A B : Set ℂ) (hA : A ⊆ S) (hB : B ⊆ T)
    (Φ : S ≃ₜ T) (hΦ : ∀ x : S, (Φ x : ℂ) ∈ B ↔ (x : ℂ) ∈ A) :
    ∃ b : A ≃ₜ B, ∀ x : A, (b x : ℂ) = (Φ ⟨x, hA x.property⟩ : ℂ) := by
  let f (x : A) : B := ⟨Φ ⟨x, hA x.property⟩, (hΦ _).mpr x.property⟩
  let g (y : B) : A := ⟨Φ.symm ⟨y, hB y.property⟩, (hΦ _).mp (by
    rw [Φ.apply_symm_apply]
    exact y.property)⟩
  refine ⟨{
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_
  }, fun _ => rfl⟩
  · intro x
    apply Subtype.ext
    change (Φ.symm (Φ ⟨x, hA x.property⟩) : ℂ) = (x : ℂ)
    exact congrArg Subtype.val (Φ.symm_apply_apply ⟨x, hA x.property⟩)
  · intro y
    apply Subtype.ext
    change (Φ (Φ.symm ⟨y, hB y.property⟩) : ℂ) = (y : ℂ)
    exact congrArg Subtype.val (Φ.apply_symm_apply ⟨y, hB y.property⟩)
  · exact (continuous_subtype_val.comp
      (Φ.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _
  · exact (continuous_subtype_val.comp
      (Φ.symm.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _

private theorem extension_frontier_iff (S T : Set ℂ)
    (b : frontier S ≃ₜ frontier T) (E : closure S ≃ₜ closure T)
    (he : ∀ x : frontier S,
      (E ⟨x, frontier_subset_closure x.property⟩ : ℂ) = (b x : ℂ))
    (x : closure S) : (E x : ℂ) ∈ frontier T ↔ (x : ℂ) ∈ frontier S := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := b.surjective ⟨E x, hx⟩
    have hE : E ⟨y, frontier_subset_closure y.property⟩ = E x :=
      Subtype.ext ((he y).trans (congrArg Subtype.val hy))
    exact congrArg Subtype.val (E.injective hE) ▸ y.property
  · intro hx
    exact (he ⟨x, hx⟩).symm ▸ (b ⟨x, hx⟩).property

/-- Helper toward Proposition 3.9: one drawing-image homeomorphism extends
over every shifted creation cell onto its actual inherited face. All extensions
agree with that same map on their frontiers and preserve frontier membership. -/
theorem exists_creation_face_extensions (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    ∃ Φ : P.image ≃ₜ Q.image,
      (∀ v, (Φ ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩ : ℂ) =
        G.pos (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))) ∧
      (∀ d : ℕ × Bool, ∃ φ : unitInterval ≃ₜ unitInterval,
        StrictMono φ ∧ ∀ t,
          (Φ ⟨(P.arc d).toPath t,
            Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩⟩ : ℂ) =
            (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d))).toPath (φ t)) ∧
      ∀ j : TriangleCreationTime u, ∃ (F : Q.Face)
        (E : closure (capFace u hfin j).val ≃ₜ closure F.val),
        (∀ (x : P.image) (hx : (x : ℂ) ∈ frontier (capFace u hfin j).val),
          (E ⟨x, frontier_subset_closure hx⟩ : ℂ) = (Φ x : ℂ)) ∧
        (∀ x : closure (capFace u hfin j).val,
          (E x : ℂ) ∈ frontier F.val ↔ (x : ℂ) ∈ frontier (capFace u hfin j).val) ∧
        ∀ d : retainedDarts W n univ, Q.dartBorders d F ↔
          d.val ∈ (fun a => J.dart (wholePlaneDartι (shiftWordInt W n) 0 a)) ''
            {a | a ∈ stageTriangleDartList u j} := by
  intro u P G Q
  obtain ⟨Φ, hv, ha⟩ := exists_drawing_image_homeomorph W H G n J hfin
  refine ⟨Φ, hv, ha, ?_⟩
  intro j
  obtain ⟨F, B, hFB, hB, hinc⟩ := start_triangle_inherited_face W H h hpast n J j
  let A := capFace u hfin j
  let D := fun d => J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)
  have hfiniteA : {d | P.dartBorders d A}.Finite := by
    have he : {d | P.dartBorders d A} = {d | d ∈ stageTriangleDartList u j} :=
      Set.ext (fun d => cap_border_iff u hfin j d)
    rw [he]
    exact List.finite_toSet _
  have hfiniteB : {d | G.dartBorders d B}.Finite := by
    rw [hB]
    exact (List.finite_toSet _).image _
  have hfrontA := finite_face_frontier P (kmswLimitDartVertex_surjective u hfin) A hfiniteA
  have hfrontB := finite_face_frontier G (WholePlanePastGlueData.vertex_incident W) B hfiniteB
  have hA : frontier A.val ⊆ P.image :=
    (P.face_open_frontier_subset_image (kmswLimitDartVertex_surjective u hfin) A).2
  have hQ : Function.Surjective (restrictedVertex G (retainedDarts W n univ)) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  have hF : frontier F.val ⊆ Q.image := (Q.face_open_frontier_subset_image hQ F).2
  have harc (d : ℕ × Bool) (x : P.image) :
      (Φ x : ℂ) ∈ (G.arc (D d)).image ↔ (x : ℂ) ∈ (P.arc d).image := by
    obtain ⟨φ, _, hφ⟩ := ha d
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := (Polyline.range_toPath _).symm ▸ hx
      have he : Φ ⟨(P.arc d).toPath (φ.symm t),
          Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨_, rfl⟩⟩⟩ = Φ x := by
        apply Subtype.ext
        exact (hφ (φ.symm t)).trans
          ((congrArg (G.arc (D d)).toPath (φ.apply_symm_apply t)).trans ht)
      have hex := congrArg Subtype.val (Φ.injective he)
      exact (Polyline.range_toPath _).symm ▸ ⟨φ.symm t, hex⟩
    · intro hx
      obtain ⟨t, ht⟩ := (Polyline.range_toPath _).symm ▸ hx
      have hex : (⟨(P.arc d).toPath t,
          Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩⟩ : P.image) = x :=
        Subtype.ext ht
      rw [← hex, hφ]
      exact (Polyline.range_toPath _).symm ▸ ⟨φ t, rfl⟩
  have hfront (x : P.image) : (Φ x : ℂ) ∈ frontier F.val ↔ (x : ℂ) ∈ frontier A.val := by
    rw [hFB, hfrontB, hfrontA]
    constructor
    · intro hx
      obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hx
      have hd' : d ∈ {d | G.dartBorders d B} := hd
      rw [hB] at hd'
      obtain ⟨a, ha', rfl⟩ := hd'
      exact mem_iUnion₂.mpr ⟨a, (cap_border_iff u hfin j a).mpr ha', (harc a x).mp hxd⟩
    · intro hx
      obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp hx
      have hb : G.dartBorders (D d) B := by
        have hm : D d ∈ {d | G.dartBorders d B} := by
          rw [hB]
          exact ⟨d, (cap_border_iff u hfin j d).mp hd, rfl⟩
        exact hm
      exact mem_iUnion₂.mpr ⟨D d, hb, (harc d x).mpr hxd⟩
  obtain ⟨b, hb⟩ := restricted_boundary_homeomorph P.image Q.image
    (frontier A.val) (frontier F.val) hA hF Φ hfront
  obtain ⟨c, hc⟩ := creation_face_disk_chart u hfin j
  have hchart : ∃ k : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure F.val,
      ∀ z, ((k z : ℂ) ∈ frontier F.val ↔ ‖(z : ℂ)‖ = 1) := by
    rw [hFB]
    exact glued_face_disk_chart W H h hpast B
  obtain ⟨k, hk⟩ := hchart
  obtain ⟨E, hE⟩ := exists_disk_homeomorph_extending_boundary
    (closure A.val) (frontier A.val) (closure F.val) (frontier F.val)
    frontier_subset_closure frontier_subset_closure c k hc hk b
  refine ⟨F, E, ?_, extension_frontier_iff A.val F.val b E hE, ?_⟩
  · intro x hx
    exact (hE ⟨x, hx⟩).trans (hb ⟨x, hx⟩)
  · intro d
    exact (hinc d).trans (Set.ext_iff.mp hB d.val)

private theorem coordinate_hits_after (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    (hhit : ∀ a : ℤ, a < 0 → ∃ n, f n = a) (s : ℕ)
    (a : ℤ) (ha : a < 0) : ∃ m, f (s + m) - f s = a := by
  have hlower (n : ℕ) : -(n : ℤ) ≤ f n := by
    induction n with
    | zero => rw [hzero]; omega
    | succ n ih => have hs := hstep n; omega
  let b := min (-(s : ℤ) - 1) (f s + a)
  have hb0 : b < 0 := lt_of_le_of_lt (min_le_left _ _) (by omega)
  obtain ⟨t, ht⟩ := hhit b hb0
  have hst : s ≤ t := by
    have htlow := hlower t
    have hb := min_le_left (-(s : ℤ) - 1) (f s + a)
    change b ≤ -(s : ℤ) - 1 at hb
    omega
  have ht' : f (s + (t - s)) - f s ≤ a := by
    rw [Nat.add_sub_of_le hst, ht]
    have hb := min_le_right (-(s : ℤ) - 1) (f s + a)
    change b ≤ f s + a at hb
    omega
  let p := fun m => f (s + m) - f s
  have hex : ∃ m, p m ≤ a := ⟨t - s, ht'⟩
  let m := Nat.find hex
  have hm : p m ≤ a := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro he
    change f (s + m) - f s ≤ a at hm
    rw [he, Nat.add_zero, sub_self] at hm
    omega
  have hprev : a < p (m - 1) := by
    exact lt_of_not_ge (Nat.find_min hex (by omega : m - 1 < m))
  have hs := hstep (s + (m - 1))
  have he : s + (m - 1) + 1 = s + m := by omega
  rw [he] at hs
  refine ⟨m, ?_⟩
  dsimp only [p] at hm hprev
  omega

private theorem boundary_hits_tail (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (s : ℕ) : BoundaryHitWitnesses (fun i => w (s + i)) := by
  have hR (n : ℕ) : R w n - 1 ≤ R w (n + 1) := by
    have he : R w (n + 1) = R w n +
        (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w n)).2 :=
      Finset.sum_range_succ _ _
    have hs : -1 ≤ (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w n)).2 := by
      unfold DirectedDistances.RandomWalk.lazyTwoDimensionalStep
      split_ifs <;> omega
    omega
  have hL (n : ℕ) : L w n - 1 ≤ L w (n + 1) := by
    have he : L w (n + 1) = L w n +
        (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w n)).1 :=
      Finset.sum_range_succ _ _
    have hs : -1 ≤ (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
      unfold DirectedDistances.RandomWalk.lazyTwoDimensionalStep
      split_ifs <;> omega
    omega
  constructor
  · intro k hk
    have hh (a : ℤ) (ha : a < 0) : ∃ n, R w n = a := by
      simpa only [neg_neg] using h.rightHit (-a) (by omega)
    obtain ⟨m, hm⟩ := coordinate_hits_after (R w) hR (by simp only [R, Finset.range_zero,
      Finset.sum_empty]) hh s (-k) (by omega)
    have he : R w (s + m) = R w s + R (fun i => w (s + i)) m :=
      Finset.sum_range_add _ s m
    exact ⟨m, by omega⟩
  · intro k hk
    obtain ⟨m, hm⟩ := coordinate_hits_after (L w) hL (by simp only [L, Finset.range_zero,
      Finset.sum_empty]) (fun a ha => h.leftHit a (by omega)) s k (by omega)
    have he : L w (s + m) = L w s + L (fun i => w (s + i)) m :=
      Finset.sum_range_add _ s m
    exact ⟨m, by omega⟩

/-- Helper toward Proposition 3.9: the original boundary-hit witnesses
imply the two-sided face-classification hypotheses at every integer start. -/
theorem start_boundary_hits (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (n : ℤ) :
    BoundaryHitWitnesses (shiftedStream (shiftWordInt W n) 0) := by
  by_cases hn : n ≤ 0
  · have hu : shiftedStream (shiftWordInt W n) 0 = shiftedStream W n.natAbs := by
      funext i
      simp only [shiftedStream, shiftWordInt, Int.ofNat_zero, sub_zero]
      congr 1
      have hh := Int.ofNat_natAbs_of_nonpos hn
      omega
    rw [hu]
    exact boundaryHitWitnesses_of_le W (Nat.zero_le _) h
  · have hu : shiftedStream (shiftWordInt W n) 0 =
        fun i => shiftedStream W 0 (n.toNat + i) := by
      funext i
      simp only [shiftedStream, shiftWordInt, Int.ofNat_zero, sub_zero, Nat.cast_add]
      congr 1
      have hh := Int.toNat_of_nonneg (show 0 ≤ n by omega)
      omega
    rw [hu]
    exact boundary_hits_tail (shiftedStream W 0) h n.toNat

/-- Helper toward Proposition 3.9: the same drawing-image homeomorphism
extends over every bounded complementary face at every integer start, with
the exact inherited dart incidence and the same boundary values on overlaps. -/
theorem exists_bounded_face_extensions (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    ∃ Φ : P.image ≃ₜ Q.image,
      (∀ v, (Φ ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩ : ℂ) =
        G.pos (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))) ∧
      (∀ d : ℕ × Bool, ∃ φ : unitInterval ≃ₜ unitInterval,
        StrictMono φ ∧ ∀ t,
          (Φ ⟨(P.arc d).toPath t,
            Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩⟩ : ℂ) =
            (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d))).toPath (φ t)) ∧
      ∀ (F : P.Face), ¬ P.IsUnbounded F → ∃ (F' : Q.Face)
        (E : closure F.val ≃ₜ closure F'.val),
        (∀ (x : P.image) (hx : (x : ℂ) ∈ frontier F.val),
          (E ⟨x, frontier_subset_closure hx⟩ : ℂ) = (Φ x : ℂ)) ∧
        (∀ x : closure F.val,
          (E x : ℂ) ∈ frontier F'.val ↔ (x : ℂ) ∈ frontier F.val) ∧
        ∀ d : retainedDarts W n univ, Q.dartBorders d F' ↔
          ∃ a : ℕ × Bool, P.dartBorders a F ∧
            J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val := by
  intro u P G Q
  obtain ⟨Φ, hv, ha, hext⟩ := exists_creation_face_extensions W H h hpast n J hfin
  refine ⟨Φ, hv, ha, ?_⟩
  intro F hF
  obtain ⟨j, rfl⟩ := (boundedFace_iff_creation_orbit u hfin (start_boundary_hits W h n) F).mp hF
  obtain ⟨F', E, hE, hb, hd⟩ := hext j
  refine ⟨F', E, hE, hb, ?_⟩
  intro d
  exact (hd d).trans (by
    constructor
    · rintro ⟨a, ha, had⟩
      exact ⟨a, (cap_border_iff u hfin j a).mpr ha, had⟩
    · rintro ⟨a, ha, had⟩
      exact ⟨a, (cap_border_iff u hfin j a).mp ha, had⟩)

private theorem face_closure_inter_frontier
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (F K : P.Face) (hne : F ≠ K) :
    closure F.val ∩ closure K.val ⊆ frontier F.val := by
  have ho := (P.face_open_frontier_subset_image hv F).1
  intro x hx
  rw [frontier, ho.interior_eq]
  exact ⟨hx.1, fun hf => Set.disjoint_left.mp
    ((P.faces_disjoint hne).closure_right ho) hf hx.2⟩

/-- Helper toward Proposition 3.9: the bounded-cell extensions can be
chosen simultaneously with an injective face assignment. They identify two
points, even on different closed cells, exactly when the source points agree. -/
theorem exists_compatible_bounded_face_extensions (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    let B := {F : P.Face // ¬ P.IsUnbounded F}
    ∃ (Φ : P.image ≃ₜ Q.image) (τ : B ↪ Q.Face)
      (E : ∀ F : B, closure F.val.val ≃ₜ closure (τ F).val),
      (∀ v, (Φ ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩ : ℂ) =
        G.pos (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))) ∧
      (∀ d : ℕ × Bool, ∃ φ : unitInterval ≃ₜ unitInterval,
        StrictMono φ ∧ ∀ t,
          (Φ ⟨(P.arc d).toPath t,
            Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩⟩ : ℂ) =
            (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d))).toPath (φ t)) ∧
      (∀ (F : B) (x : P.image) (hx : (x : ℂ) ∈ frontier F.val.val),
        (E F ⟨x, frontier_subset_closure hx⟩ : ℂ) = (Φ x : ℂ)) ∧
      (∀ (F : B) (x : closure F.val.val),
        (E F x : ℂ) ∈ frontier (τ F).val ↔ (x : ℂ) ∈ frontier F.val.val) ∧
      (∀ (F : B) (d : retainedDarts W n univ), Q.dartBorders d (τ F) ↔
        ∃ a : ℕ × Bool, P.dartBorders a F.val ∧
          J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val) ∧
      ∀ (F K : B) (x : closure F.val.val) (y : closure K.val.val),
        (E F x : ℂ) = (E K y : ℂ) ↔ (x : ℂ) = (y : ℂ) := by
  classical
  intro u P G Q B
  obtain ⟨Φ, hv, ha, hcell⟩ := exists_bounded_face_extensions W H h hpast n J hfin
  choose τ E he hb hd using fun F : B => hcell F.val F.property
  let D := fun a => J.dart (wholePlaneDartι (shiftWordInt W n) 0 a)
  have hD : Function.Injective D := by
    intro a b hab
    have hh := J.dart.injective hab
    exact Prod.ext (wholePlaneEdgeι_injective _ 0 (congrArg Prod.fst hh))
      (congrArg (fun q : WholePlaneDart (shiftWordInt W n) => q.2) hh)
  have hret (a : ℕ × Bool) : D a ∈ retainedDarts W n univ := by
    rw [retained_darts_eq_image W n J univ]
    exact ⟨a, mem_univ _, rfl⟩
  have hτ : Function.Injective τ := by
    intro F K hFK
    obtain ⟨a, ha⟩ := face_bordered u hfin (start_boundary_hits W h n) F.val
    have hf := (hd F ⟨D a, hret a⟩).mpr ⟨a, ha, rfl⟩
    rw [hFK] at hf
    obtain ⟨b, hb, hba⟩ := (hd K ⟨D a, hret a⟩).mp hf
    have hba' := hD hba
    subst b
    exact Subtype.ext (dart_border_face_unique u hfin a F.val K.val ha hb)
  refine ⟨Φ, ⟨τ, hτ⟩, E, hv, ha, he, hb, hd, ?_⟩
  have hP := kmswLimitDartVertex_surjective u hfin
  have hQ : Function.Surjective (restrictedVertex G (retainedDarts W n univ)) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  intro F K x y
  by_cases hFK : F = K
  · subst K
    exact ⟨fun hxy => congrArg Subtype.val ((E F).injective (Subtype.ext hxy)),
      fun hxy => congrArg (fun z => (E F z : ℂ)) (Subtype.ext hxy)⟩
  have hFval : F.val ≠ K.val := fun heq => hFK (Subtype.ext heq)
  have hτne : τ F ≠ τ K := fun heq => hFK (hτ heq)
  constructor
  · intro hxy
    have hx' : (E F x : ℂ) ∈ frontier (τ F).val :=
      face_closure_inter_frontier Q hQ (τ F) (τ K) hτne
        ⟨(E F x).property, hxy.symm ▸ (E K y).property⟩
    have hy' : (E K y : ℂ) ∈ frontier (τ K).val :=
      face_closure_inter_frontier Q hQ (τ K) (τ F) (Ne.symm hτne)
        ⟨(E K y).property, hxy ▸ (E F x).property⟩
    have hx := (hb F x).mp hx'
    have hy := (hb K y).mp hy'
    let x' : P.image := ⟨x, (P.face_open_frontier_subset_image hP F.val).2 hx⟩
    let y' : P.image := ⟨y, (P.face_open_frontier_subset_image hP K.val).2 hy⟩
    exact congrArg Subtype.val (Φ.injective (Subtype.ext
      ((he F x' hx).symm.trans (hxy.trans (he K y' hy)))))
  · intro hxy
    have hx : (x : ℂ) ∈ frontier F.val.val :=
      face_closure_inter_frontier P hP F.val K.val hFval
        ⟨x.property, hxy.symm ▸ y.property⟩
    have hy : (y : ℂ) ∈ frontier K.val.val :=
      face_closure_inter_frontier P hP K.val F.val (Ne.symm hFval)
        ⟨y.property, hxy ▸ x.property⟩
    let x' : P.image := ⟨x, (P.face_open_frontier_subset_image hP F.val).2 hx⟩
    let y' : P.image := ⟨y, (P.face_open_frontier_subset_image hP K.val).2 hy⟩
    exact (he F x' hx).trans ((congrArg (fun z => (Φ z : ℂ))
      (show x' = y' from Subtype.ext hxy)).trans (he K y' hy).symm)

private theorem paste_face_charts {ι : Type*} (S T : ι → Set ℂ)
    (hS : LocallyFinite S) (hT : LocallyFinite T)
    (hclS : ∀ i, IsClosed (S i)) (hclT : ∀ i, IsClosed (T i))
    (E : ∀ i, S i ≃ₜ T i)
    (heq : ∀ i j (x : S i) (y : S j),
      (E i x : ℂ) = (E j y : ℂ) ↔ (x : ℂ) = (y : ℂ)) :
    ∃ g : (⋃ i, S i) ≃ₜ (⋃ i, T i),
      ∀ i (x : S i),
        (g ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ : ℂ) = (E i x : ℂ) := by
  classical
  let A := ⋃ i, S i
  let B := ⋃ i, T i
  have hmem (x : A) : ∃ i, (x : ℂ) ∈ S i := mem_iUnion.mp x.property
  let idx (x : A) := (hmem x).choose
  have hx (x : A) : (x : ℂ) ∈ S (idx x) := (hmem x).choose_spec
  let f (x : A) : B :=
    ⟨E (idx x) ⟨x, hx x⟩, mem_iUnion.mpr ⟨idx x, (E (idx x) _).property⟩⟩
  have hf (i : ι) (x : S i) :
      (f ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ : ℂ) = (E i x : ℂ) :=
    (heq _ _ _ _).mpr rfl
  have hfi : Function.Injective f := by
    intro x y h
    have hh : (E (idx x) ⟨x, hx x⟩ : ℂ) = (E (idx y) ⟨y, hx y⟩ : ℂ) :=
      congrArg Subtype.val h
    exact Subtype.ext ((heq _ _ _ _).mp hh)
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨i, hi⟩ := mem_iUnion.mp y.property
    refine ⟨⟨(E i).symm ⟨y, hi⟩, mem_iUnion.mpr
      ⟨i, ((E i).symm ⟨y, hi⟩).property⟩⟩, ?_⟩
    exact Subtype.ext ((hf i _).trans
      (congrArg Subtype.val ((E i).apply_symm_apply _)))
  let a : ι → Set A := fun i => Subtype.val ⁻¹' S i
  let b : ι → Set B := fun i => Subtype.val ⁻¹' T i
  have ha : LocallyFinite a := hS.preimage_continuous continuous_subtype_val
  have hb : LocallyFinite b := hT.preimage_continuous continuous_subtype_val
  have hac : ⋃ i, a i = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hbc : ⋃ i, b i = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hfc : Continuous f := ha.continuous hac
      (fun i => (hclS i).preimage continuous_subtype_val) (fun i => by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply Continuous.subtype_mk
    have he : (fun x : a i => (f x.val : ℂ)) =
        fun x => (E i ⟨x.val.val, x.property⟩ : ℂ) :=
      funext fun x => hf i ⟨x.val.val, x.property⟩
    rw [he]
    exact continuous_subtype_val.comp ((E i).continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)))
  let e := Equiv.ofBijective f ⟨hfi, hfs⟩
  have hinv (i : ι) (y : T i) :
      (e.symm ⟨y, mem_iUnion.mpr ⟨i, y.property⟩⟩ : ℂ) =
        ((E i).symm y : ℂ) := by
    have hh : e ⟨(E i).symm y,
        mem_iUnion.mpr ⟨i, ((E i).symm y).property⟩⟩ =
        ⟨y, mem_iUnion.mpr ⟨i, y.property⟩⟩ :=
      Subtype.ext ((hf i _).trans (congrArg Subtype.val ((E i).apply_symm_apply y)))
    exact congrArg Subtype.val ((congrArg e.symm hh).symm.trans (e.symm_apply_apply _))
  have hic : Continuous e.symm := hb.continuous hbc
      (fun i => (hclT i).preimage continuous_subtype_val) (fun i => by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply Continuous.subtype_mk
    have he : (fun y : b i => (e.symm y.val : ℂ)) =
        fun y => ((E i).symm ⟨y.val.val, y.property⟩ : ℂ) :=
      funext fun y => hinv i ⟨y.val.val, y.property⟩
    change Continuous (fun y : b i => (e.symm y.val : ℂ))
    erw [he]
    exact continuous_subtype_val.comp ((E i).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)))
  exact ⟨{ toEquiv := e, continuous_toFun := hfc, continuous_invFun := hic }, hf⟩

private theorem nearby_face_arc
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d₀ : D) (F : P.Face) (z : ℂ) (hz : z ∈ F.val) :
    ∃ (d : D) (x : ℂ), x ∈ (P.arc d).image ∧ P.dartBorders d F ∧
      dist x z < dist z (P.pos (vert d₀)) + 1 := by
  obtain ⟨q, d, i, hi, hqi, hqfront, _, _, hmin⟩ :=
    P.face_nearest_segment_contact hvert d₀ F z hz
  have hdist := hmin (P.pos (vert d₀)) (Or.inl ⟨vert d₀, rfl⟩)
  by_cases hend : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1)
  · obtain ⟨x, hx, hxball, hnot⟩ := P.face_endpoint_frontier_not_vertex_mem_ball
      hvert F q d hi hend (frontier_subset_closure hqfront) zero_lt_one
    obtain ⟨e, hxe, he⟩ := P.exists_mem_arc_dartBorders_of_frontier_not_vertex hvert F hx hnot
    refine ⟨e, x, hxe, he, ?_⟩
    have hnear : dist x q < 1 := Metric.mem_ball.mp hxball
    have htri := dist_triangle x q z
    rw [dist_comm q z] at htri
    linarith only [hnear, htri, hdist]
  · have hopen := mem_openSegment_of_ne_left_right
      (fun he => hend (Or.inl he.symm)) (fun he => hend (Or.inr he.symm)) hqi
    have hqnear : dist q z < dist z (P.pos (vert d₀)) + 1 := by
      rw [dist_comm]
      linarith only [hdist]
    rcases (P.mem_closure_face_openSegment_iff_dartBorders hvert d F hi hopen).mp
      (frontier_subset_closure hqfront) with hd | hd
    · exact ⟨d, q, (P.arc d).segmentAt_subset_image hi hqi, hd, hqnear⟩
    · refine ⟨flip d, q, ?_, hd, hqnear⟩
      rw [P.arc_image_flip]
      exact (P.arc d).segmentAt_subset_image hi hqi

private theorem closed_faces_locallyFinite
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert) (d₀ : D) :
    LocallyFinite (fun F : P.Face => closure F.val) := by
  classical
  have hu := P.dartBorders_existsUnique_of_locallyFiniteVertexImage32
    (LeftSideHalfDisk.locallyFiniteVertexImage_of_surjective P hv)
  let f := fun d => (hu d).choose
  have hf (d : D) (F : P.Face) (hd : P.dartBorders d F) : f d = F :=
    ((hu d).choose_spec.2 F hd).symm
  intro z
  let p₀ := P.pos (vert d₀)
  let R := dist z p₀ + 5
  have hdarts := P.locally_finite (Metric.ball z R) Metric.isBounded_ball
  have hfinite := hdarts.image f
  refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, hfinite.subset ?_⟩
  rintro F ⟨y, hyF, hyz⟩
  obtain ⟨w, hwF, hyw⟩ := Metric.mem_closure_iff.mp hyF 1 zero_lt_one
  have hwz : dist w z < 2 := by
    have ht := dist_triangle w y z
    rw [dist_comm w y] at ht
    have hyz' := Metric.mem_ball.mp hyz
    linarith only [ht, hyw, hyz']
  obtain ⟨d, x, hxd, hdF, hxw⟩ := nearby_face_arc P hv d₀ F w hwF
  have hxz : x ∈ Metric.ball z R := by
    have ht := dist_triangle x w z
    have ht' := dist_triangle w z p₀
    change dist x w < dist w p₀ + 1 at hxw
    change dist x z < dist z p₀ + 5
    linarith only [ht, ht', hxw, hwz]
  exact ⟨d, ⟨x, hxz, hxd⟩, hf d F hdF⟩

/-- Helper toward Proposition 3.9: the compatible bounded cells paste to a
homeomorphism of their closed unions. Its inverse is continuous by local
finiteness of the actual target faces. The exterior is not included here. -/
theorem exists_bounded_union_homeomorph (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    let B := {F : P.Face // ¬ P.IsUnbounded F}
    ∃ (Φ : P.image ≃ₜ Q.image) (τ : B ↪ Q.Face)
      (g : (⋃ F : B, closure F.val.val) ≃ₜ (⋃ F : B, closure (τ F).val)),
      (∀ v, (Φ ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩ : ℂ) =
        G.pos (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))) ∧
      (∀ d : ℕ × Bool, ∃ φ : unitInterval ≃ₜ unitInterval,
        StrictMono φ ∧ ∀ t,
          (Φ ⟨(P.arc d).toPath t,
            Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩⟩ : ℂ) =
            (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d))).toPath (φ t)) ∧
      (∀ F : B,
        g '' {x : (⋃ i : B, closure i.val.val) | (x : ℂ) ∈ closure F.val.val} =
          {y : (⋃ i : B, closure (τ i).val) | (y : ℂ) ∈ closure (τ F).val}) ∧
      ∀ (F : B) (x : P.image) (hx : (x : ℂ) ∈ frontier F.val.val),
        (g ⟨x, mem_iUnion.mpr ⟨F, frontier_subset_closure hx⟩⟩ : ℂ) = (Φ x : ℂ) := by
  intro u P G Q B
  obtain ⟨Φ, τ, E, hv, ha, he, _hb, _hd, hcollision⟩ :=
    exists_compatible_bounded_face_extensions W H h hpast n J hfin
  have hP := kmswLimitDartVertex_surjective u hfin
  have hQ : Function.Surjective (restrictedVertex G (retainedDarts W n univ)) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  let a := J.dart (wholePlaneDartι (shiftWordInt W n) 0 (0, false))
  have haret : a ∈ retainedDarts W n univ := by
    rw [retained_darts_eq_image W n J univ]
    exact ⟨(0, false), mem_univ _, rfl⟩
  have hs := (closed_faces_locallyFinite P hP (0, false)).comp_injective
    (show Function.Injective (fun F : B => F.val) from Subtype.val_injective)
  have ht := (closed_faces_locallyFinite Q hQ ⟨a, haret⟩).comp_injective τ.injective
  obtain ⟨g, hg⟩ := paste_face_charts (fun F : B => closure F.val.val)
    (fun F : B => closure (τ F).val) hs ht
    (fun _ => isClosed_closure) (fun _ => isClosed_closure) E hcollision
  refine ⟨Φ, τ, g, hv, ha, ?_, ?_⟩
  · intro F
    apply Set.ext
    intro y
    change (∃ x : (⋃ i : B, closure i.val.val),
      (x : ℂ) ∈ closure F.val.val ∧ g x = y) ↔ (y : ℂ) ∈ closure (τ F).val
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hh := hg F ⟨x, hx⟩
      change (g x : ℂ) ∈ closure (τ F).val
      rw [hh]
      exact (E F ⟨x, hx⟩).property
    · intro hy
      let x := (E F).symm ⟨y, hy⟩
      refine ⟨⟨x, mem_iUnion.mpr ⟨F, x.property⟩⟩, x.property, ?_⟩
      apply Subtype.ext
      exact (hg F x).trans (congrArg Subtype.val ((E F).apply_symm_apply ⟨y, hy⟩))
  · intro F x hx
    exact (hg F ⟨x, frontier_subset_closure hx⟩).trans (he F x hx)


















































































































































































































end DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry
