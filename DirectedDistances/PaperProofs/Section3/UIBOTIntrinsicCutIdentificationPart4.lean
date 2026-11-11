/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart3

/-! # Transport of the intrinsic future-cut characterization

transport the complete characterization. Source satisfaction and the iid
the sole coordinator. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section1
open scoped Topology

variable {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)

/-- Helper toward Proposition 3.9: the other endpoint of each dart is
transported with the same storage reversal as its initial endpoint. -/
theorem intrinsicFutureDartEquiv_other_vertex (d : A.E × Bool) :
    d39GeomRootOtherVertex B.map (intrinsicFutureDartEquiv I d) =
      I.vertexEquiv (d39GeomRootOtherVertex A.map d) := by
  have hh := intrinsicFutureDartEquiv_vertex I (d.1, !d.2)
  rw [intrinsicFutureDartEquiv_flip] at hh
  cases hd : d.2 <;> cases hb : (intrinsicFutureDartEquiv I d).2 <;>
    simpa only [d39GeomRootVertex, d39GeomRootOtherVertex, hd, hb,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] using hh

private theorem dart_open_image (A : D39DomainRootedMap.{0}) (d : A.E × Bool) :
    intrinsicFutureDartArc A d '' openParams = A.map.toPlaneGraphDrawing.openArc d.1 := by
  rcases d with ⟨e, b⟩
  cases b
  · exact path_symm_openParams_image (A.map.arc e)
  · rfl

/-- Helper toward Proposition 3.9: open edge images are preserved even
when the geometric isomorphism reverses the stored parameter. -/
theorem intrinsicFuture_openArc_map (e : A.E) :
    I.h '' A.map.toPlaneGraphDrawing.openArc e =
      B.map.toPlaneGraphDrawing.openArc (I.edgeEquiv e) := by
  let d : A.E × Bool := (e, true)
  let φ := intrinsicFutureDartParam I d
  have hend := d39StrictMonoIntervalEndpoints φ (intrinsicFutureDartParam_strictMono I d)
  rw [← dart_open_image A d]
  change _ = B.map.toPlaneGraphDrawing.openArc (intrinsicFutureDartEquiv I d).1
  rw [← dart_open_image B (intrinsicFutureDartEquiv I d)]
  ext z
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨φ t, (mem_openParams_homeomorph_iff φ hend.1 hend.2 t).mpr ht,
      (intrinsicFutureDartArc_map I d t).symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨intrinsicFutureDartArc A d (φ.symm t),
      ⟨φ.symm t, ?_, rfl⟩, ?_⟩
    · apply (mem_openParams_homeomorph_iff φ hend.1 hend.2 (φ.symm t)).mp
      simpa only [Homeomorph.apply_symm_apply] using ht
    · simpa only [← show intrinsicFutureDartParam I d = φ from rfl,
        Homeomorph.apply_symm_apply] using
        intrinsicFutureDartArc_map I d (φ.symm t)

/-- Helper toward Proposition 3.9: each geometric face multiplicity is
preserved, including a face incident to both sides of an edge. -/
theorem intrinsicFuture_faceMult_map
    (e : A.E) (F : A.map.toPlaneGraphDrawing.Face) :
    A.map.toPlaneGraphDrawing.faceMult e F =
      B.map.toPlaneGraphDrawing.faceMult (I.edgeEquiv e) (I.faceEquiv F) := by
  classical
  have hn (x : ℂ) (S : Set ℂ) : S ∈ 𝓝 x ↔ I.h '' S ∈ 𝓝 (I.h x) := by
    rw [← I.h.map_nhds_eq x]
    exact (Filter.image_mem_map_iff I.h.injective).symm
  have hu : I.h '' (F.val ∪ Set.range (A.map.arc e)) =
      (I.faceEquiv F).val ∪ Set.range (B.map.arc (I.edgeEquiv e)) := by
    rw [Set.image_union, I.faceEquiv_val, I.arc_range_map]
  have hfirst :
      (∀ x ∈ A.map.toPlaneGraphDrawing.openArc e,
        F.val ∪ Set.range (A.map.arc e) ∈ 𝓝 x) ↔
      (∀ y ∈ B.map.toPlaneGraphDrawing.openArc (I.edgeEquiv e),
        (I.faceEquiv F).val ∪ Set.range (B.map.arc (I.edgeEquiv e)) ∈ 𝓝 y) := by
    rw [← intrinsicFuture_openArc_map I e]
    constructor
    · rintro h y ⟨x, hx, rfl⟩
      rw [← hu]
      exact (hn x _).mp (h x hx)
    · intro h x hx
      apply (hn x _).mpr
      rw [hu]
      exact h (I.h x) ⟨x, hx, rfl⟩
  have hsecond : A.map.toPlaneGraphDrawing.openArc e ⊆ closure F.val ↔
      B.map.toPlaneGraphDrawing.openArc (I.edgeEquiv e) ⊆
        closure (I.faceEquiv F).val := by
    rw [← intrinsicFuture_openArc_map I e, I.faceEquiv_val, ← I.h.image_closure]
    exact (Set.image_subset_image_iff I.h.injective).symm
  unfold PlaneGraphDrawing.faceMult
  rw [propext hfirst, propext hsecond]

/-- Helper toward Proposition 3.9: ambient face degree is invariant under
the actual geometric face equivalence, with edge multiplicities retained. -/
theorem intrinsicFuture_faceDegree_map (F : A.map.toPlaneGraphDrawing.Face) :
    A.map.toPlaneGraphDrawing.faceDegree F =
      B.map.toPlaneGraphDrawing.faceDegree (I.faceEquiv F) := by
  classical
  unfold PlaneGraphDrawing.faceDegree
  apply (Equiv.finsetCongr I.edgeEquiv).iSup_congr
  intro s
  rw [Equiv.finsetCongr_apply]
  symm
  apply Finset.sum_bij (fun e _ => I.edgeEquiv e)
  · intro e he
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩
  · intro e _ f _ hh
    exact I.edgeEquiv.injective hh
  · intro f hf
    obtain ⟨e, he, hh⟩ := Finset.mem_map.mp hf
    exact ⟨e, he, hh⟩
  · intro e _
    exact intrinsicFuture_faceMult_map I e F

/-- Helper toward Proposition 3.9: the unordered pair of stored endpoints
is preserved even if the storage orientation changes. -/
theorem intrinsicFuture_endpoints_map (e : A.E) (v : A.V) :
    (B.map.src (I.edgeEquiv e) = I.vertexEquiv v ∨
      B.map.tgt (I.edgeEquiv e) = I.vertexEquiv v) ↔
    (A.map.src e = v ∨ A.map.tgt e = v) := by
  have hs := I.src_map e
  have ht := I.tgt_map e
  cases hf : I.edgeFlip e <;> simp only [hf, Bool.false_eq_true, ite_false, ite_true] at hs ht
  · rw [← hs, ← ht, I.vertexEquiv.injective.eq_iff, I.vertexEquiv.injective.eq_iff]
  · rw [← ht, ← hs, I.vertexEquiv.injective.eq_iff, I.vertexEquiv.injective.eq_iff]
    exact or_comm

/-- Helper toward Proposition 3.9: push forward every field of an intrinsic
future cut along a rooted geometric isomorphism, including its missing edges,
boundary enumeration, acyclicity, and triangular ambient faces. -/
@[expose] def intrinsicFutureCutPushforward (C : IntrinsicFutureCut A) :
    IntrinsicFutureCut B := by
  let E := intrinsicFutureDartEquiv I
  have hroot : E A.root = B.root := intrinsicFutureDartEquiv_root I
  have hgeom := intrinsicFutureCut_geometry_map I C
  have hm (e : A.E) : C.missing (I.edgeEquiv.symm (I.edgeEquiv e)) = C.missing e := by
    rw [I.edgeEquiv.symm_apply_apply]
  have ht (d : B.E × Bool) : C.tail (E.symm d) ↔
      d.1 ∈ I.edgeEquiv '' C.edges ∧ intrinsicFutureAmbientTail B d ∧
        ¬ C.missing (I.edgeEquiv.symm d.1) := by
    obtain ⟨d, rfl⟩ := E.surjective d
    rw [E.symm_apply_apply, C.tail_iff]
    change (_ ∧ _ ∧ _) ↔ (I.edgeEquiv d.1 ∈ I.edgeEquiv '' C.edges ∧
      intrinsicFutureAmbientTail B (intrinsicFutureDartEquiv I d) ∧
      ¬ C.missing (I.edgeEquiv.symm (I.edgeEquiv d.1)))
    rw [I.edgeEquiv.injective.mem_set_image, hm,
      intrinsicFutureAmbientTail_map I d]
  refine {
    vertices := I.vertexEquiv '' C.vertices
    edges := I.edgeEquiv '' C.edges
    faces := I.faceEquiv '' C.faces
    seam := fun e => C.seam (I.edgeEquiv.symm e)
    missing := fun e => C.missing (I.edgeEquiv.symm e)
    tail := fun d => C.tail (E.symm d)
    rotation := fun d a => C.rotation (E.symm d) (E.symm a)
    x := fun k => I.vertexEquiv (C.x k)
    betaRVertex := fun n => I.vertexEquiv (C.betaRVertex n)
    betaLVertex := fun n => I.vertexEquiv (C.betaLVertex n)
    betaREdge := fun n => I.edgeEquiv (C.betaREdge n)
    betaLEdge := fun n => I.edgeEquiv (C.betaLEdge n)
    root_initial := (congrArg I.vertexEquiv C.root_initial).trans I.rootVertex_map
    root_terminal := ?_
    root_tail := ?_
    betaR_start := congrArg I.vertexEquiv C.betaR_start
    betaR_extremal := fun n => intrinsicFutureRightmostOutgoingAt_map I _ _ (C.betaR_extremal n)
    betaR_step := ?_
    betaL_start := congrArg I.vertexEquiv C.betaL_start
    betaL_extremal := fun n => intrinsicFutureLeftmostIncomingAt_map I _ _ (C.betaL_extremal n)
    betaL_step := ?_
    seam_iff := ?_
    vertices_iff := hgeom.1
    edges_iff := hgeom.2.1
    faces_iff := hgeom.2.2
    seam_mem := ?_
    ambient_present := ?_
    missing_iff := ?_
    present_iff := ?_
    tail_iff := ht
    missing_unoriented := ?_
    root_not_missing := ?_
    cut_root_tail := ?_
    rotation_iff := ?_
    x_injective := I.vertexEquiv.injective.comp C.x_injective
    x_range := ?_
    x_mem := fun k => ⟨C.x k, C.x_mem k, rfl⟩
    x_right := fun n => congrArg I.vertexEquiv (C.x_right n)
    x_left := fun n => congrArg I.vertexEquiv (C.x_left n)
    acyclic := ?_
    internal_triangles := ?_ }
  · rw [C.root_terminal]
    exact (intrinsicFutureDartEquiv_other_vertex I A.root).symm.trans
      (congrArg (d39GeomRootOtherVertex B.map) hroot)
  · rw [← hroot]
    exact (intrinsicFutureAmbientTail_map I A.root).mpr C.root_tail
  · intro n
    obtain ⟨he, htail, hhead⟩ := C.betaR_step n
    refine ⟨fun h => he ((I.missing_map _).mp h), ?_, ?_⟩
    · exact (intrinsicFuture_tail_map I ⟨_, he⟩).symm.trans (congrArg I.vertexEquiv htail)
    · exact (intrinsicFuture_head_map I ⟨_, he⟩).symm.trans (congrArg I.vertexEquiv hhead)
  · intro n
    obtain ⟨he, hhead, htail⟩ := C.betaL_step n
    refine ⟨fun h => he ((I.missing_map _).mp h), ?_, ?_⟩
    · exact (intrinsicFuture_head_map I ⟨_, he⟩).symm.trans (congrArg I.vertexEquiv hhead)
    · exact (intrinsicFuture_tail_map I ⟨_, he⟩).symm.trans (congrArg I.vertexEquiv htail)
  · intro e
    obtain ⟨e, rfl⟩ := I.edgeEquiv.surjective e
    rw [I.edgeEquiv.symm_apply_apply, C.seam_iff, ← I.root_edge_map]
    simp only [Set.mem_range, I.edgeEquiv.injective.eq_iff]
  · intro e he
    exact ⟨I.edgeEquiv.symm e, C.seam_mem _ he, I.edgeEquiv.apply_symm_apply e⟩
  · rintro e ⟨e, he, rfl⟩ hmiss
    exact C.ambient_present e he ((I.missing_map e).mp hmiss)
  · intro e
    obtain ⟨e, rfl⟩ := I.edgeEquiv.surjective e
    rw [I.edgeEquiv.symm_apply_apply, C.missing_iff]
    simp only [Set.mem_range, I.edgeEquiv.injective.eq_iff]
  · intro e
    obtain ⟨e, rfl⟩ := I.edgeEquiv.surjective e
    rw [I.edgeEquiv.symm_apply_apply, I.edgeEquiv.injective.mem_set_image,
      ← I.root_edge_map]
    simp only [Set.mem_range, I.edgeEquiv.injective.eq_iff]
    exact C.present_iff e
  · intro e he
    exact ⟨fun h => ((ht (e, false)).mp h).2.2 he,
      fun h => ((ht (e, true)).mp h).2.2 he⟩
  · rw [← I.root_edge_map, I.edgeEquiv.symm_apply_apply]
    exact C.root_not_missing
  · rw [← hroot, E.symm_apply_apply]
    exact C.cut_root_tail
  · intro d a
    obtain ⟨d, rfl⟩ := E.surjective d
    obtain ⟨a, rfl⟩ := E.surjective a
    rw [E.symm_apply_apply, E.symm_apply_apply, C.rotation_iff]
    exact (intrinsicFutureRotation_map_iff I C.edges d a).symm
  · ext v
    obtain ⟨v, rfl⟩ := I.vertexEquiv.surjective v
    have hx : I.vertexEquiv v ∈ Set.range (fun k => I.vertexEquiv (C.x k)) ↔
        v ∈ Set.range C.x := by
      simp only [Set.mem_range, I.vertexEquiv.injective.eq_iff]
    rw [hx, C.x_range]
    change (∃ e, C.seam e ∧ (A.map.src e = v ∨ A.map.tgt e = v)) ↔ _
    constructor
    · rintro ⟨e, he, hv⟩
      refine ⟨I.edgeEquiv e, ?_, (intrinsicFuture_endpoints_map I e v).mpr hv⟩
      simpa only [I.edgeEquiv.symm_apply_apply] using he
    · rintro ⟨e, he, hv⟩
      obtain ⟨e, rfl⟩ := I.edgeEquiv.surjective e
      exact ⟨e, by simpa only [I.edgeEquiv.symm_apply_apply] using he,
        (intrinsicFuture_endpoints_map I e v).mp hv⟩
  · intro v hcycle
    apply C.acyclic (I.vertexEquiv.symm v)
    apply Relation.TransGen.lift I.vertexEquiv.symm ?_ v v hcycle
    rintro u w ⟨d, hd, hu, hw⟩
    refine ⟨E.symm d, hd, ?_, ?_⟩
    · apply I.vertexEquiv.injective
      rw [I.vertexEquiv.apply_symm_apply]
      exact (intrinsicFutureDartEquiv_vertex I (E.symm d)).symm.trans
        (by change d39GeomRootVertex B.map (E (E.symm d)) = u
            rw [E.apply_symm_apply]; exact hu)
    · apply I.vertexEquiv.injective
      rw [I.vertexEquiv.apply_symm_apply]
      exact (intrinsicFutureDartEquiv_other_vertex I (E.symm d)).symm.trans
        (by change d39GeomRootOtherVertex B.map (E (E.symm d)) = w
            rw [E.apply_symm_apply]; exact hw)
  · rintro F ⟨F, hF, rfl⟩
    rw [← intrinsicFuture_faceDegree_map I F]
    exact C.internal_triangles F hF

/-- Helper toward Proposition 3.9: the pushforward has exactly the image
carriers, rays and labels and the transported seam, missing tags, orientation
and rotation. The existence statement includes every field of the cut. -/
theorem intrinsicFutureCut_pushforward (C : IntrinsicFutureCut A) :
    ∃ C' : IntrinsicFutureCut B,
      C'.vertices = I.vertexEquiv '' C.vertices ∧
      C'.edges = I.edgeEquiv '' C.edges ∧
      C'.faces = I.faceEquiv '' C.faces ∧
      (∀ e, C'.seam (I.edgeEquiv e) ↔ C.seam e) ∧
      (∀ e, C'.missing (I.edgeEquiv e) ↔ C.missing e) ∧
      (∀ d, C'.tail (intrinsicFutureDartEquiv I d) ↔ C.tail d) ∧
      (∀ d a, C'.rotation (intrinsicFutureDartEquiv I d)
        (intrinsicFutureDartEquiv I a) ↔ C.rotation d a) ∧
      (∀ k, C'.x k = I.vertexEquiv (C.x k)) ∧
      (∀ n, C'.betaRVertex n = I.vertexEquiv (C.betaRVertex n) ∧
        C'.betaLVertex n = I.vertexEquiv (C.betaLVertex n) ∧
        C'.betaREdge n = I.edgeEquiv (C.betaREdge n) ∧
        C'.betaLEdge n = I.edgeEquiv (C.betaLEdge n)) := by
  refine ⟨intrinsicFutureCutPushforward I C, rfl, rfl, rfl, ?_, ?_, ?_, ?_,
    fun _ => rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  · intro e
    change C.seam (I.edgeEquiv.symm (I.edgeEquiv e)) ↔ C.seam e
    rw [I.edgeEquiv.symm_apply_apply]
  · intro e
    change C.missing (I.edgeEquiv.symm (I.edgeEquiv e)) ↔ C.missing e
    rw [I.edgeEquiv.symm_apply_apply]
  · intro d
    change C.tail ((intrinsicFutureDartEquiv I).symm (intrinsicFutureDartEquiv I d)) ↔ _
    rw [(intrinsicFutureDartEquiv I).symm_apply_apply]
  · intro d a
    change C.rotation ((intrinsicFutureDartEquiv I).symm (intrinsicFutureDartEquiv I d))
      ((intrinsicFutureDartEquiv I).symm (intrinsicFutureDartEquiv I a)) ↔ _
    rw [(intrinsicFutureDartEquiv I).symm_apply_apply,
      (intrinsicFutureDartEquiv I).symm_apply_apply]

section SourceIndependence

open DirectedDistances.KMSW

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H

/-- Helper toward Proposition 3.9: any two rooted geometric source
isomorphisms into the same representative agree on every individual edge,
vertex and dart. Run-zero recurrence supplies every required earlier witness. -/
theorem uibotCut_representative_iso_agree
    (A : D39DomainRootedMap.{0})
    (I J : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root) :
    I.edgeEquiv = J.edgeEquiv ∧ I.vertexEquiv = J.vertexEquiv ∧
      intrinsicFutureDartEquiv (A := uibotWholePlaneSourceDomain W H G hp) I =
        intrinsicFutureDartEquiv (A := uibotWholePlaneSourceDomain W H G hp) J := by
  have hh (N : ℕ) : BoundaryHitWitnesses (shiftedStream W N) :=
    boundaryHitWitnesses_of_le W (Nat.zero_le N) h
  obtain ⟨he, hv⟩ := uibotCut_geometric_iso_fixes_ids hh (I.trans J.symm)
  have heq : I.edgeEquiv = J.edgeEquiv := by
    ext e
    have hee := congrArg J.edgeEquiv (he e)
    change J.edgeEquiv (J.edgeEquiv.symm (I.edgeEquiv e)) = J.edgeEquiv e at hee
    simpa only [J.edgeEquiv.apply_symm_apply] using hee
  have hvq : I.vertexEquiv = J.vertexEquiv := by
    ext v
    have hvv := congrArg J.vertexEquiv (hv v)
    change J.vertexEquiv (J.vertexEquiv.symm (I.vertexEquiv v)) = J.vertexEquiv v at hvv
    simpa only [J.vertexEquiv.apply_symm_apply] using hvv
  refine ⟨heq, hvq, ?_⟩
  have hflip (e : WholePlaneEdge W) : I.edgeFlip e = J.edgeFlip e := by
    have he0 : ¬ (uibotWholePlaneSourceMap W H G hp).missing e := fun hn => hn (hp e)
    have hi := I.orientation_map e he0
    have hj := J.orientation_map e he0
    have hx := hi.symm.trans ((congrArg A.map.forward
      (Subtype.ext (congrArg (fun E => E e) heq))).trans hj)
    cases hf : (uibotWholePlaneSourceMap W H G hp).forward ⟨e, he0⟩
    · simpa only [hf, Bool.false_xor] using hx
    · have hc := congrArg Bool.not hx
      simpa only [hf, Bool.true_xor, Bool.not_not] using hc
  ext d : 1
  exact Prod.ext (congrArg (fun E => E d.1) heq)
    (congrArg (Bool.xor d.2) (hflip d.1))

/-- Helper toward Proposition 3.9: the image of every individual internal
cut face is independent of the chosen rooted geometric source isomorphism.
Equality is of actual complementary components in the target plane. -/
theorem uibotCut_representative_internal_face_agree
    (A : D39DomainRootedMap.{0})
    (I J : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root)
    (q : FutureMapInternalFaceOrbit W H) :
    uibotCutFaceInRepresentative W H h hpast hp A I q =
      uibotCutFaceInRepresentative W H h hpast hp A J q := by
  apply Subtype.ext
  rw [uibotCutFaceInRepresentative_val, uibotCutFaceInRepresentative_val]
  have hfixed := uibotCut_source_iso_internal_face_fixed W H h hpast hp (I.trans J.symm) q
  have himage := congrArg (fun S : Set ℂ => J.h '' S) hfixed
  change J.h '' ((fun z => J.h.symm (I.h z)) ''
    (futureMapInternalGluedFace W H h hpast q).val) =
      J.h '' (futureMapInternalGluedFace W H h hpast q).val at himage
  simpa only [Set.image_image, Homeomorph.apply_symm_apply] using himage

end SourceIndependence













































































































end DirectedDistances.PaperProofs.Section3
end
