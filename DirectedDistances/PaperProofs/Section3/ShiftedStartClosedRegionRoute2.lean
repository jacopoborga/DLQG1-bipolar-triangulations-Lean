/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.ShiftedStartClosedRegionRoute
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers51And52Final

/-! Helper toward Proposition 3.9: relative complementary components after deletion.

All regions below are actual connected components. Deleted edge interiors remain
present in relative complements; only the explicitly displayed difference with
belong to the sole coordinator. No intrinsic qualifier is removed. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.ShiftedStartClosedRegionRoute2

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open ShiftedStartGeometry ShiftedStartClosedRegionRoute Set Topology

private theorem bounded_region_diff_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert) :
    (⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val) \ P.image =
      ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, F.val.val := by
  classical
  ext z
  constructor
  · rintro ⟨hz, hzP⟩
    obtain ⟨F, hzF⟩ := mem_iUnion.mp hz
    obtain ⟨B, hzB⟩ := (P.faces_cover_compl z).mpr hzP
    have he : B = F.val := by
      by_contra hn
      exact Set.disjoint_left.mp
        ((P.faces_disjoint hn).closure_right (P.face_open_frontier_subset_image hv B).1)
        hzB hzF
    exact mem_iUnion.mpr ⟨F, he ▸ hzB⟩
  · intro hz
    obtain ⟨F, hzF⟩ := mem_iUnion.mp hz
    exact ⟨mem_iUnion.mpr ⟨F, subset_closure hzF⟩, P.face_subset_compl F.val hzF⟩

/-- Helper toward Proposition 3.9: after deleting geometric edges, the part
of a relative component off the original drawing is exactly the union of the
bounded full faces contained in that component. Deleted edge points are not
discarded from the component itself. -/
theorem relative_component_diff_image_eq_iUnion
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (R : Set ℂ) (hR : R ⊆ P.image) (z : ℂ) :
    let X := ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val
    let C := connectedComponentIn (X \ R) z
    C \ P.image =
      ⋃ (F : {F : P.Face // ¬ P.IsUnbounded F}) (_ : F.val.val ⊆ C), F.val.val := by
  intro X C
  ext y
  constructor
  · rintro ⟨hyC, hyP⟩
    have hyX := (connectedComponentIn_subset (X \ R) z hyC).1
    have hyfaces : y ∈ ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, F.val.val := by
      rw [← bounded_region_diff_image P hv]
      exact ⟨hyX, hyP⟩
    obtain ⟨F, hyF⟩ := mem_iUnion.mp hyfaces
    have hFsub : F.val.val ⊆ X \ R := by
      intro x hx
      exact ⟨mem_iUnion.mpr ⟨F, subset_closure hx⟩,
        fun hxR => P.face_subset_compl F.val hx (hR hxR)⟩
    have hFC : F.val.val ⊆ C := by
      change F.val.val ⊆ connectedComponentIn (X \ R) z
      rw [connectedComponentIn_eq hyC]
      exact (P.face_isPathConnected hv F.val).isConnected.isPreconnected
        |>.subset_connectedComponentIn hyF hFsub
    exact mem_iUnion₂.mpr ⟨F, hFC, hyF⟩
  · intro hy
    obtain ⟨F, hFC, hyF⟩ := mem_iUnion₂.mp hy
    exact ⟨hFC hyF, P.face_subset_compl F.val hyF⟩

/-- Helper toward Proposition 3.9: every relative component lies in the
actual full-plane complementary component of the retained drawing through its
base point. This inclusion does not assert equality after adjoining the exterior. -/
theorem relative_component_subset_plane_component (X R : Set ℂ) (z : ℂ) :
    connectedComponentIn (X \ R) z ⊆ connectedComponentIn Rᶜ z :=
  connectedComponentIn_mono z (fun _ hx => hx.2)

private theorem subtype_component_image (X R : Set ℂ) (x : X)
    (hx : (x : ℂ) ∉ R) :
    Subtype.val '' connectedComponentIn {a : X | (a : ℂ) ∉ R} x =
      connectedComponentIn (X \ R) (x : ℂ) := by
  let A : Set X := {a | (a : ℂ) ∉ R}
  have hset : Subtype.val '' A = X \ R := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, ha⟩
    · rintro ⟨hzX, hzR⟩
      exact ⟨⟨z, hzX⟩, hzR, rfl⟩
  apply Subset.antisymm
  · rw [← hset]
    exact continuous_subtype_val.continuousOn.image_connectedComponentIn_subset hx
  · have hsub : connectedComponentIn (X \ R) (x : ℂ) ⊆ X :=
      (connectedComponentIn_subset _ _).trans sdiff_subset
    have hconn : IsPreconnected
        (Subtype.val ⁻¹' connectedComponentIn (X \ R) (x : ℂ) : Set X) := by
      apply IsInducing.subtypeVal.isPreconnected_image.mp
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsub]
      exact isPreconnected_connectedComponentIn
    have hxC : x ∈ (Subtype.val ⁻¹' connectedComponentIn (X \ R) (x : ℂ) : Set X) :=
      mem_connectedComponentIn ⟨x.property, hx⟩
    have hCA : (Subtype.val ⁻¹' connectedComponentIn (X \ R) (x : ℂ) : Set X) ⊆ A :=
      fun _ ha => (connectedComponentIn_subset _ _ ha).2
    intro y hy
    exact ⟨⟨y, hsub hy⟩, hconn.subset_connectedComponentIn hxC hCA hy, rfl⟩

/-- Helper toward Proposition 3.9: the same closed-region map transports
the actual relative connected components for every retained edge set. The
component formula is in the ambient plane, with all deleted-edge points kept. -/
theorem exists_relative_component_transport (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    let X := ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val
    let Y := ⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val
    ∃ g : X ≃ₜ Y, ∀ K : Set ℕ,
      let P' := restrictDrawing P {d : ℕ × Bool | d.1 ∈ K} (fun _ => Iff.rfl)
      let Q' := inheritedDrawing W H G n K
      (∀ x : X, (g x : ℂ) ∈ Q'.image ↔ (x : ℂ) ∈ P'.image) ∧
      ∀ (x : X), (x : ℂ) ∉ P'.image →
        (fun a : X => (g a : ℂ)) ''
            {a : X | (a : ℂ) ∈ connectedComponentIn (X \ P'.image) (x : ℂ)} =
          connectedComponentIn (Y \ Q'.image) (g x : ℂ) := by
  intro u P G Q X Y
  obtain ⟨g, hg⟩ := exists_closed_region_restriction_homeomorphs W H h hpast n J hfin
  refine ⟨g, fun K => ?_⟩
  intro P' Q'
  obtain ⟨hi, _⟩ := hg K
  refine ⟨hi, fun x hx => ?_⟩
  let A : Set X := {a | (a : ℂ) ∉ P'.image}
  let B : Set Y := {b | (b : ℂ) ∉ Q'.image}
  have hAB : g '' A = B := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact fun hb => ha ((hi a).mp hb)
    · intro hb
      refine ⟨g.symm b, ?_, g.apply_symm_apply b⟩
      intro ha
      exact hb (by simpa only [g.apply_symm_apply] using (hi (g.symm b)).mpr ha)
  have hc : {a : X | (a : ℂ) ∈ connectedComponentIn (X \ P'.image) (x : ℂ)} =
      connectedComponentIn A x := by
    rw [← subtype_component_image X P'.image x hx]
    exact preimage_image_eq _ Subtype.val_injective
  have hgx : (g x : ℂ) ∉ Q'.image := fun hh => hx ((hi x).mp hh)
  rw [hc]
  change (Subtype.val ∘ g) '' connectedComponentIn A x = _
  rw [image_comp, g.image_connectedComponentIn hx, hAB]
  exact subtype_component_image Y Q'.image (g x) hgx

private theorem finite_incidence_suffix (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (s : ℕ) :
    KMSWFiniteIncidence (fun i => w (s + i)) := by
  intro v
  apply Set.Finite.subset
    (Set.Finite.preimage (kmswWindowEdgeMapInf_injective w s).injOn
      (hfin (kmswWindowVertexMapInf w s v)))
  rintro e ⟨n, he, hw | ht⟩
  · refine ⟨s + n, ?_, Or.inl ?_⟩
    · rw [kmswWindowEdgeMapInf_eq_stage w s n e he]
      exact (kmswWindowPatchData_rel w s n).edge_bound e he
    · rw [kmswWindowEdgeMapInf_west w s n e he, hw]
  · refine ⟨s + n, ?_, Or.inr ?_⟩
    · rw [kmswWindowEdgeMapInf_eq_stage w s n e he]
      exact (kmswWindowPatchData_rel w s n).edge_bound e he
    · rw [kmswWindowEdgeMapInf_east w s n e he, ht]

private theorem rotation_hypothesis_shift_nat (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (n : ℕ) :
    WholePlaneRotationHypothesis (shiftWord W n) := by
  constructor
  · intro N
    have hs : shiftedStream (shiftWord W n) N =
        (fun i => shiftedStream W N (n + i)) := by
      funext i
      unfold shiftedStream shiftWord
      congr 1
      omega
    rw [hs]
    exact finite_incidence_suffix _ (H.1 N) n
  · intro N v
    let hN : N ≤ N + n := Nat.le_add_right N n
    let v' := wholePlaneVertexTrans (shiftWord W n) N (N + n) hN v
    obtain ⟨M, hNM, hf⟩ := H.2 N v'
    have hNM' : N ≤ M + n := by omega
    refine ⟨M + n, hNM', ?_⟩
    intro L hML
    obtain ⟨K, rfl⟩ : ∃ K, L = K + n := ⟨L - n, by omega⟩
    have he : wholePlaneVertexTrans (shiftWord W n) N (M + n) hNM' v =
        wholePlaneVertexTrans W N M hNM v' := by
      have hc := congrFun (wholePlaneVertexTrans_comp (shiftWord W n)
        N (N + n) (M + n) hN (Nat.add_le_add_right hNM n)) v
      rw [Function.comp_apply, wholePlaneVertexTrans_shiftWord] at hc
      exact hc.symm
    rw [he]
    exact (wholePlaneFresh_shiftWord W n M K (by omega) _).mpr (hf K (by omega))

/-- Helper toward Proposition 3.9: the existing deterministic rotation
hypothesis is invariant under every integer change of start. No extra shifted
rotation assumption or almost-sure event is needed for the geometric comparison. -/
theorem rotation_hypothesis_shift (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (n : ℤ) :
    WholePlaneRotationHypothesis (shiftWordInt W n) := by
  cases n with
  | ofNat m =>
    change WholePlaneRotationHypothesis (shiftWordInt W (m : ℤ))
    rw [shiftWordInt_nat]
    exact rotation_hypothesis_shift_nat W H m
  | negSucc m =>
    have he : shiftWord (shiftWordInt W (Int.negSucc m)) (m + 1) = W := by
      funext i
      unfold shiftWord shiftWordInt
      congr 1
      omega
    exact wholePlaneRotationHypothesis_of_shiftWord _ (m + 1) (he.symm ▸ H)


private theorem route2_locally_finite_vertex_segments
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert) (v : V) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball (P.pos v) r,
      (y ∈ P.image ↔ ∃ d : D, vert d = v ∧ y ∈ (P.arc d).segmentAt 0) := by
  classical
  let S (d : D) (i : Fin ((P.arc d).points.length - 1)) : Set ℂ :=
    if P.pos v ∈ (P.arc d).segmentAt i.val then ∅ else (P.arc d).segmentAt i.val
  let B (d : D) := ⋃ i, S d i
  have hsub (d : D) : B d ⊆ (P.arc d).image := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    dsimp only [S] at hi
    split_ifs at hi
    · exact hi.elim
    · exact (P.arc d).segmentAt_subset_image (by have := i.isLt; omega) hi
  have hlf : LocallyFinite (fun d => (P.arc d).image) := by
    intro z
    refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, ?_⟩
    simpa only [inter_comm] using P.locally_finite (Metric.ball z 1) Metric.isBounded_ball
  have hclosed : IsClosed (⋃ d, B d) := (hlf.subset hsub).isClosed_iUnion (by
    intro d
    apply isClosed_iUnion_of_finite
    intro i
    dsimp only [S]
    split_ifs
    · exact isClosed_empty
    · change IsClosed (segment ℝ _ _)
      rw [segment_eq_image']
      exact (isCompact_Icc.image (by fun_prop)).isClosed)
  have hnot : P.pos v ∉ ⋃ d, B d := by
    intro hmem
    obtain ⟨d, hd⟩ := mem_iUnion.mp hmem
    obtain ⟨i, hi⟩ := mem_iUnion.mp hd
    dsimp only [S] at hi
    split_ifs at hi with h
    · exact hi
    · exact h hi
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hnot)
  refine ⟨r, hr, ?_⟩
  intro y hyr
  constructor
  · intro hy
    have harc : ∃ d, y ∈ (P.arc d).image := by
      rcases hy with ⟨w, rfl⟩ | ⟨d, hd⟩
      · obtain ⟨d, rfl⟩ := hv w
        exact ⟨d, Or.inl (P.arc_start d).symm⟩
      · exact ⟨d, hd⟩
    obtain ⟨d, hd⟩ := harc
    have hseg : ∃ i, i + 1 < (P.arc d).points.length ∧
        y ∈ (P.arc d).segmentAt i := by
      rcases hd with hd | ⟨i, hi, hd⟩
      · refine ⟨0, by have := P.arc_length d; omega, ?_⟩
        rw [mem_singleton_iff] at hd
        rw [hd, Polyline.segmentAt, Polyline.point_zero_eq_start]
        exact left_mem_segment ℝ _ _
      · exact ⟨i, hi, hd⟩
    obtain ⟨i, hi, hyi⟩ := hseg
    have hvi : P.pos v ∈ (P.arc d).segmentAt i := by
      by_contra hn
      apply hball hyr
      exact mem_iUnion.mpr ⟨d, mem_iUnion.mpr
        ⟨⟨i, by omega⟩, by simpa only [S, ite_eq_right hn] using hyi⟩⟩
    have him := (P.arc d).segmentAt_subset_image hi hvi
    have hend : P.pos v = (P.arc d).start ∨ P.pos v = (P.arc d).finish := by
      by_contra hn
      exact P.interior_avoids_vertices d v ⟨him, by
        simpa only [mem_insert_iff, mem_singleton_iff] using hn⟩
    rcases hend with hs | ht
    · have hi0 := (P.arc d).segmentAt_index_eq_zero_of_start_mem
        (P.arc_simple d) (P.arc_length d) hi (hs ▸ hvi)
      exact ⟨d, P.pos_injective (hs.trans (P.arc_start d)).symm, hi0 ▸ hyi⟩
    · have hilast := (P.arc d).segmentAt_index_last_of_finish_mem
        (P.arc_simple d) (P.arc_length d) hi (ht ▸ hvi)
      refine ⟨flip d, P.pos_injective (ht.trans (P.arc_finish d)).symm, ?_⟩
      rw [P.arc_flip, Polyline.segmentAt_reverse_transfer _ (by
        have := P.arc_length d; omega)]
      have hind : (P.arc d).points.length - 2 - 0 = i := by omega
      simpa only [hind] using hyi
  · rintro ⟨d, _, hd⟩
    exact Or.inr ⟨d, (P.arc d).segmentAt_subset_image (by
      have := P.arc_length d; omega) hd⟩

private theorem route2_locally_finite_border_predecessor
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (d : D) (F : P.Face) (hd : P.dartBorders d F) :
    P.dartBorders (flip (rot d)) F := by
  obtain ⟨r, hr, hlocal⟩ := route2_locally_finite_vertex_segments P hv (vert d)
  have hsafe : P.initialSector d r ⊆ P.imageᶜ := by
    intro z hz hzim
    obtain ⟨e, he, hze⟩ := (hlocal z (P.initialSector_subset_ball d r hz)).mp hzim
    exact Set.disjoint_left.mp (P.initialSector_disjoint_initial_segment d e r he) hz hze
  have hc := P.isConnected_initialSector d hr
  obtain ⟨z, hz⟩ := hc.nonempty
  obtain ⟨K, hzK⟩ := (P.faces_cover_compl z).mpr (hsafe hz)
  have hsub : P.initialSector d r ⊆ K.val := by
    obtain ⟨w, _, hK⟩ := K.property
    rw [hK] at hzK ⊢
    rw [connectedComponentIn_eq hzK]
    exact hc.isPreconnected.subset_connectedComponentIn hz hsafe
  have hKF := P.dartBorders_face_unique d K F
    (P.dartBorders_of_initialSector_subset hv d hr K hsub) hd
  exact hKF ▸ P.dartBorders_flip_rot_of_initialSector_subset hv d hr K hsub

private theorem route2_firstReturn_of_inverse_scan
    {D E V : Type*} {flip : E → E} {rot : Equiv.Perm E} {vert : E → V}
    (P : PLDrawing E V flip rot vert) (σ : Equiv.Perm D) (i : D → E)
    (hscan : ∀ d, ∃ k : ℕ, 0 < k ∧
      (rot.symm : E → E)^[k] (i d) = i (σ.symm d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (rot.symm : E → E)^[j] (i d) ∉ range i) (d : D) :
    (drawingFirstReturnPerm P (range i) ⟨i d, ⟨d, rfl⟩⟩).val = i (σ d) := by
  classical
  obtain ⟨k, hk, he, hg⟩ := hscan (σ d)
  rw [Equiv.symm_apply_apply] at he
  have hpow : (rot.symm ^ k) (i (σ d)) = i d := by
    simpa only [permIterateEqPow] using he
  have hfwd : (rot ^ k) (i d) = i (σ d) := by
    rw [← hpow, ← Equiv.Perm.mul_apply, show rot.symm ^ k = (rot ^ k).symm from inv_pow rot k,
      Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
  have hgap (j : ℕ) (hj : 0 < j) (hjk : j < k) :
      (rot ^ j) (i d) ∉ range i := by
    have hs : (rot ^ j) (i d) = (rot.symm ^ (k - j)) (i (σ d)) := by
      apply (rot ^ (k - j)).injective
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hjk.le, hfwd,
        show rot.symm ^ (k - j) = (rot ^ (k - j)).symm from inv_pow rot (k - j),
        Equiv.apply_symm_apply]
    rw [hs]
    simpa only [permIterateEqPow] using hg (k - j) (by omega) (by omega)
  let x : range i := ⟨i d, ⟨d, rfl⟩⟩
  have htime : subsetFirstReturnTime rot (range i) (drawingPositiveReturn P (range i)) x = k := by
    apply Nat.le_antisymm
    · apply Nat.find_min'
      exact ⟨hk, by rw [permIterateEqPow, hfwd]; exact ⟨σ d, rfl⟩⟩
    · have ht := subsetFirstReturnTime_spec rot (range i) (drawingPositiveReturn P (range i)) x
      by_contra hn
      exact hgap _ ht.1 (Nat.lt_of_not_ge hn)
        (by simpa only [permIterateEqPow] using ht.2.1)
  change (rot : E → E)^[subsetFirstReturnTime rot (range i)
    (drawingPositiveReturn P (range i)) x] (i d) = _
  rw [htime, permIterateEqPow]
  exact hfwd

private theorem route2_start_rotation (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (J : WholePlaneStartIso W n)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W n))
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0))
    (a : ℕ × Bool) (d : retainedDarts W n univ)
    (ha : J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val) :
    (drawingFirstReturnPerm G (retainedDarts W n univ) d).val =
      J.dart (wholePlaneDartι (shiftWordInt W n) 0
        (kmswInfRot (shiftedStream (shiftWordInt W n) 0) hfin a)) := by
  let U := shiftWordInt W n
  let i := fun a => J.dart (wholePlaneDartι U 0 a)
  have hstep (x : WholePlaneDart U) :
      J.dart ((wholePlaneRotation U H').symm x) =
        (wholePlaneRotation W H).symm (J.dart x) := by
    apply (wholePlaneRotation W H).injective
    rw [← J.rot H H', Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hiter (k : ℕ) (x : WholePlaneDart U) :
      J.dart (((wholePlaneRotation U H').symm ^ k) x) =
        ((wholePlaneRotation W H).symm ^ k) (J.dart x) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, hstep, ih,
        pow_succ', Equiv.Perm.mul_apply]
  have hscan (b : ℕ × Bool) : ∃ k : ℕ, 0 < k ∧
      ((wholePlaneRotation W H).symm : _ → _)^[k] (i b) =
        i ((kmswInfRot (shiftedStream U 0) hfin).symm b) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((wholePlaneRotation W H).symm : _ → _)^[j] (i b) ∉ range i := by
    obtain ⟨k, hk, he, hg⟩ := wholePlaneRotation_symm_firstReturn_run U H' 0 b
    refine ⟨k, hk, ?_, ?_⟩
    · rw [permIterateEqPow]
      exact (hiter k (wholePlaneDartι U 0 b)).symm.trans (congrArg J.dart he)
    · intro j hj hjk hmem
      obtain ⟨c, hc⟩ := hmem
      apply hg j hj hjk
      refine ⟨c, J.dart.injective ?_⟩
      exact hc.trans (by
        rw [permIterateEqPow]
        exact (hiter j (wholePlaneDartι U 0 b)).symm)
  have hS : retainedDarts W n univ = range i := by
    rw [retained_darts_eq_image W n J univ]
    exact image_univ
  revert d
  rw [hS]
  intro d ha
  have hd : d = (⟨i a, mem_range_self a⟩ : range i) := Subtype.ext ha.symm
  subst d
  exact route2_firstReturn_of_inverse_scan G (kmswInfRot (shiftedStream U 0) hfin)
    i hscan a

private theorem route2_inherited_border_sameCycle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (J : WholePlaneStartIso W n)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W n))
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let Q := inheritedDrawing W H G n univ
    ∀ (a b : ℕ × Bool) (d e : retainedDarts W n univ),
      J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val →
      J.dart (wholePlaneDartι (shiftWordInt W n) 0 b) = e.val →
      (kmswInfFaceSucc u hfin).SameCycle a b →
      ∀ F : Q.Face, Q.dartBorders d F ↔ Q.dartBorders e F := by
  intro u Q a b d e ha hb hab F
  let i := fun a => J.dart (wholePlaneDartι (shiftWordInt W n) 0 a)
  let D (a : ℕ × Bool) : retainedDarts W n univ := ⟨i a, by
    rw [retained_darts_eq_image W n J univ]
    exact ⟨a, mem_univ _, rfl⟩⟩
  have hvert : Function.Surjective (restrictedVertex G (retainedDarts W n univ)) := by
    rintro ⟨v, c, hc, hcv⟩
    exact ⟨⟨c, hc⟩, Subtype.ext hcv⟩
  let σ := kmswInfFaceSucc u hfin
  have hpred (a : ℕ × Bool) :
      restrictedFlip G (retainedDarts W n univ) (fun _ => Iff.rfl)
          (drawingFirstReturnPerm G (retainedDarts W n univ) (D a)) = D (σ.symm a) := by
    apply Subtype.ext
    change wholePlaneDartFlip W
      (drawingFirstReturnPerm G (retainedDarts W n univ) (D a)).val = i (σ.symm a)
    rw [route2_start_rotation W H G n J H' hfin a (D a) rfl]
    change wholePlaneDartFlip W (J.dart (wholePlaneDartι (shiftWordInt W n) 0
      (kmswInfRot u hfin a))) =
      J.dart (wholePlaneDartι (shiftWordInt W n) 0
        ((kmswInfRot u hfin a).1, !(kmswInfRot u hfin a).2))
    erw [J.dart_apply, J.dart_apply]
    rfl
  have hinv (c : ℕ × Bool) : Q.dartBorders (D c) F → Q.dartBorders (D (σ.symm c)) F := by
    intro hc
    have hh := route2_locally_finite_border_predecessor Q hvert (D c) F hc
    rwa [hpred] at hh
  have hfwd (c : ℕ × Bool) : Q.dartBorders (D c) F → Q.dartBorders (D (σ c)) F := by
    intro hc
    obtain ⟨K, hK, _⟩ := Q.dartBorders_existsUnique_of_locallyFiniteVertexImage32
      (LeftSideHalfDisk.locallyFiniteVertexImage_of_surjective Q hvert) (D (σ c))
    have hK' := route2_locally_finite_border_predecessor Q hvert (D (σ c)) K hK
    rw [hpred, Equiv.symm_apply_apply] at hK'
    exact Q.dartBorders_face_unique (D c) K F hK' hc ▸ hK
  have hp (τ : Equiv.Perm (ℕ × Bool))
      (ht : ∀ c, Q.dartBorders (D c) F → Q.dartBorders (D (τ c)) F)
      (m : ℕ) (c : ℕ × Bool) (hc : Q.dartBorders (D c) F) :
      Q.dartBorders (D ((τ ^ m) c)) F := by
    induction m with
    | zero => exact hc
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ht _ ih
  have htransfer (c c' : ℕ × Bool) (hcc : σ.SameCycle c c')
      (hc : Q.dartBorders (D c) F) : Q.dartBorders (D c') F := by
    obtain ⟨k, rfl⟩ := hcc
    cases k with
    | ofNat m => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hp σ hfwd m c hc
    | negSucc m =>
      simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.inv_def] using hp σ.symm hinv (m + 1) c hc
  have hd : D a = d := Subtype.ext ha
  have he : D b = e := Subtype.ext hb
  rw [← hd, ← he]
  exact ⟨htransfer a b hab, htransfer b a hab.symm⟩

private theorem route2_inherited_exterior (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W n))
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    ∃ U : Q.Face, Q.IsUnbounded U ∧
      (∀ F : Q.Face, Q.IsUnbounded F → F = U) ∧
      (∀ (a : ℕ × Bool) (d : retainedDarts W n univ),
        J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val →
        (Q.dartBorders d U ↔ (kmswInfFaceSucc u hfin).SameCycle futureMapOuterDart a)) ∧
      (⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val) = U.valᶜ := by
  intro u G Q
  let d₀ : retainedDarts W n univ :=
    ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 futureMapOuterDart), by
      rw [retained_darts_eq_image W n J univ]
      exact ⟨futureMapOuterDart, mem_univ _, rfl⟩⟩
  obtain ⟨U, ⟨hU, hdU⟩, _⟩ := inherited_external_dart_existsUnique W H h hpast n J hfin
    futureMapOuterDart d₀ rfl (Equiv.Perm.SameCycle.refl _ _)
  have hvert : Function.Surjective (restrictedVertex G (retainedDarts W n univ)) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  have hinc (a : ℕ × Bool) (d : retainedDarts W n univ)
      (ha : J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val) :
      Q.dartBorders d U ↔ (kmswInfFaceSucc u hfin).SameCycle futureMapOuterDart a := by
    constructor
    · intro hd
      exact (inherited_dart_unbounded_iff W H h hpast n J hfin a d ha U hd).mp hU
    · intro haU
      exact (route2_inherited_border_sameCycle W H G n J H' hfin
        futureMapOuterDart a d₀ d rfl ha haU U).mp hdU
  have huniq (F : Q.Face) (hF : Q.IsUnbounded F) : F = U := by
    obtain ⟨d, hdF⟩ := Q.face_has_bordering_dart hvert d₀ F
    have hd := (Set.ext_iff.mp (retained_darts_eq_image W n J univ) d.val).mp d.property
    obtain ⟨a, _, ha⟩ := hd
    have houter := (inherited_dart_unbounded_iff W H h hpast n J hfin a d ha F hdF).mp hF
    exact Q.dartBorders_face_unique d F U hdF ((hinc a d ha).mpr houter)
  refine ⟨U, hU, huniq, hinc, ?_⟩
  obtain ⟨_, hgraph, _⟩ := exists_closed_region_homeomorph W H h hpast n J hfin
  apply Set.ext
  intro z
  constructor
  · intro hz hzU
    obtain ⟨F, hzF⟩ := mem_iUnion.mp hz
    have hne : U ≠ F.val := fun he => F.property (he ▸ hU)
    exact Set.disjoint_left.mp
      ((Q.faces_disjoint hne).closure_right (inherited_face_isOpen W H G n univ U)) hzU hzF
  · intro hz
    by_cases hzQ : z ∈ Q.image
    · exact hgraph hzQ
    obtain ⟨F, hzF⟩ := (Q.faces_cover_compl z).mpr hzQ
    have hF : ¬ Q.IsUnbounded F := fun hF => hz (huniq F hF ▸ hzF)
    exact mem_iUnion.mpr ⟨⟨F, hF⟩, subset_closure hzF⟩

/-- Helper toward Proposition 3.9: the target unbounded complementary region
is unique at every integer start under precisely the original deterministic
hypotheses. Its complement is the union of the bounded closed faces. -/
theorem inherited_exterior_unique (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    ∃ U : Q.Face, Q.IsUnbounded U ∧
      (∀ F : Q.Face, Q.IsUnbounded F → F = U) ∧
      (⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val)ᶜ = U.val := by
  intro G Q
  obtain ⟨U, hU, hu, _, hcl⟩ := route2_inherited_exterior W H h hpast n J
    (rotation_hypothesis_shift W H n) hfin
  exact ⟨U, hU, hu, by rw [hcl, compl_compl]⟩

private theorem face_subset_of_restriction_meeting
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (T : Set D)
    (hT : ∀ d, d ∈ T ↔ flip d ∈ T)
    (F : P.Face) (B : (restrictDrawing P T hT).Face)
    (z : ℂ) (hzF : z ∈ F.val) (hzB : z ∈ B.val) : F.val ⊆ B.val := by
  obtain ⟨x, _, hF⟩ := F.property
  obtain ⟨y, _, hB⟩ := B.property
  have hFz := hF.trans (connectedComponentIn_eq (hF ▸ hzF))
  have hBz := hB.trans (connectedComponentIn_eq (hB ▸ hzB))
  rw [hFz, hBz]
  exact connectedComponentIn_mono z
    (compl_subset_compl.mpr (restrictDrawing_image_subset P T hT))

/-- Helper toward Proposition 3.9: every face after deleting edges is,
off the original drawing, precisely the union of the full-plane faces it
contains. Its incidence at each retained oriented dart is equivalent to
containing the unique original face on that dart's left. -/
theorem restriction_faces_eq_iUnion_and_incidence
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (T : Set D) (hT : ∀ d, d ∈ T ↔ flip d ∈ T) :
    let Q := restrictDrawing P T hT
    (∀ B : Q.Face,
      B.val \ P.image = ⋃ (F : P.Face) (_ : F.val ⊆ B.val), F.val) ∧
    (∀ (d : T) (B : Q.Face), Q.dartBorders d B ↔
      ∃ F : P.Face, P.dartBorders d.val F ∧ F.val ⊆ B.val) := by
  intro Q
  constructor
  · intro B
    ext z
    constructor
    · rintro ⟨hzB, hzP⟩
      obtain ⟨F, hzF⟩ := (P.faces_cover_compl z).mpr hzP
      exact mem_iUnion₂.mpr
        ⟨F, face_subset_of_restriction_meeting P T hT F B z hzF hzB, hzF⟩
    · intro hz
      obtain ⟨F, hFB, hzF⟩ := mem_iUnion₂.mp hz
      exact ⟨hFB hzF, P.face_subset_compl F hzF⟩
  · intro d B
    constructor
    · intro hdB
      obtain ⟨F, hdF, _⟩ := P.dartBorders_existsUnique_of_locallyFiniteVertexImage32
        (LeftSideHalfDisk.locallyFiniteVertexImage_of_surjective P hv) d.val
      refine ⟨F, hdF, ?_⟩
      obtain ⟨r, hr, hF⟩ := hdF
      obtain ⟨s, hs, hB⟩ := hdB
      let t := min r s / 2
      have ht : 0 < t := half_pos (lt_min hr hs)
      have htr : t < r := (half_lt_self (lt_min hr hs)).trans_le (min_le_left _ _)
      have hts : t < s := (half_lt_self (lt_min hr hs)).trans_le (min_le_right _ _)
      let z := (P.arc d.val).start + (t : ℂ) *
        ((P.arc d.val).initialDirection + (t : ℂ) * Complex.I *
          (P.arc d.val).initialDirection)
      have hzF : z ∈ F.val := hF t t ht htr ht htr
      have hzB : z ∈ B.val := by
        have hh := hB t t ht hts ht hts
        change ((restrictDrawing P T hT).arc d).start + (t : ℂ) *
          (((restrictDrawing P T hT).arc d).initialDirection +
            (t : ℂ) * Complex.I * ((restrictDrawing P T hT).arc d).initialDirection)
            ∈ B.val at hh
        simpa only [restrictDrawing_arc] using hh
      exact face_subset_of_restriction_meeting P T hT F B z hzF hzB
    · rintro ⟨F, ⟨r, hr, hF⟩, hFB⟩
      refine ⟨r, hr, fun t ε ht htr hε hεr => ?_⟩
      change ((restrictDrawing P T hT).arc d).start + (t : ℂ) *
        (((restrictDrawing P T hT).arc d).initialDirection +
          (ε : ℂ) * Complex.I * ((restrictDrawing P T hT).arc d).initialDirection) ∈ B.val
      rw [restrictDrawing_arc]
      exact hFB (hF t ε ht htr hε hεr)

/-- Helper toward Proposition 3.9: every non-exterior face of an edge-deleted
drawing is already a single relative component of the closed region. Only the
face containing the original exterior can merge different relative components. -/
theorem plane_component_eq_relative_of_ne_exterior
    (X R : Set ℂ) (hR : R ⊆ X) (hext : IsPreconnected Xᶜ)
    (q z : ℂ) (hq : q ∉ X) (hz : z ∉ R)
    (hne : connectedComponentIn Rᶜ z ≠ connectedComponentIn Rᶜ q) :
    connectedComponentIn Rᶜ z = connectedComponentIn (X \ R) z := by
  have hsub : connectedComponentIn Rᶜ z ⊆ X := by
    intro y hy
    by_contra hyX
    have hE : Xᶜ ⊆ connectedComponentIn Rᶜ y :=
      hext.subset_connectedComponentIn hyX (compl_subset_compl.mpr hR)
    have hqC : q ∈ connectedComponentIn Rᶜ z := by
      rw [connectedComponentIn_eq hy]
      exact hE hq
    exact hne (connectedComponentIn_eq hqC)
  apply Subset.antisymm
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hz) (fun _ hy =>
        ⟨hsub hy, connectedComponentIn_subset _ _ hy⟩)
  · exact relative_component_subset_plane_component X R z

/-- Helper toward Proposition 3.9: the unique inherited exterior is the
unique actual unbounded complementary region in every representative, at every
integer start, under the original deterministic hypotheses. -/
theorem representative_exterior_existsUnique (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root)
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))
    let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι (shiftWordInt W n) 0 e))
    ∃! U : Set ℂ,
      U ∈ intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (V '' intrinsicConsumer51RunVertices u univ) (E '' univ)) ∧
      ¬ Bornology.IsBounded U := by
  intro u V E
  obtain ⟨U, hU, hu, _⟩ := inherited_exterior_unique W H h hpast n J hfin
  have hr := representative_faceRegions W H h hpast hp A I n J univ
  refine ⟨I.h '' U.val, ⟨?_, ?_⟩, ?_⟩
  · rw [hr]
    exact ⟨U, rfl⟩
  · exact (representative_external W H h hpast hp A I n univ U).mpr hU
  · rintro B ⟨hB, hb⟩
    rw [hr] at hB
    obtain ⟨F, rfl⟩ := hB
    rw [hu F ((representative_external W H h hpast hp A I n univ F).mp hb)]

/-- Helper toward Proposition 3.9: after identifying both exteriors
uniquely, one homeomorphism of their complements transports every relative
component for every retained edge set. No ambient extension is assumed. -/
theorem exists_exterior_relative_component_transport (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    ∃ (U : P.Face) (V : Q.Face),
      P.IsUnbounded U ∧ (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      Q.IsUnbounded V ∧ (∀ F : Q.Face, Q.IsUnbounded F → F = V) ∧
      ∃ g : (U.valᶜ : Set ℂ) ≃ₜ (V.valᶜ : Set ℂ), ∀ K : Set ℕ,
        let P' := restrictDrawing P {d : ℕ × Bool | d.1 ∈ K} (fun _ => Iff.rfl)
        let Q' := inheritedDrawing W H G n K
        (∀ x : ↥(U.valᶜ), (g x : ℂ) ∈ Q'.image ↔ (x : ℂ) ∈ P'.image) ∧
        ∀ x : ↥(U.valᶜ), (x : ℂ) ∉ P'.image →
          (fun a : ↥(U.valᶜ) => (g a : ℂ)) ''
              {a : ↥(U.valᶜ) | (a : ℂ) ∈ connectedComponentIn
                (U.valᶜ \ P'.image) (x : ℂ)} =
            connectedComponentIn (V.valᶜ \ Q'.image) (g x : ℂ) := by
  intro u P G Q
  obtain ⟨U, hU, hu, hX⟩ :=
    closed_region_eq_compl_exterior u hfin (start_boundary_hits W h n)
  obtain ⟨V, hV, hv, _, hY⟩ := route2_inherited_exterior W H h hpast n J
    (rotation_hypothesis_shift W H n) hfin
  refine ⟨U, V, hU, hu, hV, hv, ?_⟩
  have hg := exists_relative_component_transport W H h hpast n J hfin
  dsimp only at hg
  rw [hX, hY] at hg
  exact hg

private theorem relative_component_closed_in_complement
    (X R : Set ℂ) (hX : IsClosed X) (z : ℂ) (hz : z ∈ X \ R) :
    IsClosed (Subtype.val ⁻¹' connectedComponentIn (X \ R) z : Set ↥(Rᶜ)) := by
  let hAO : X \ R ⊆ Rᶜ := fun _ hx => hx.2
  have hA : IsClosed (Subtype.val ⁻¹' (X \ R) : Set ↥(Rᶜ)) := by
    have he : (Subtype.val ⁻¹' (X \ R) : Set ↥(Rᶜ)) =
        Subtype.val ⁻¹' X := by
      ext x
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.property⟩⟩
    rw [he]
    exact hX.preimage continuous_subtype_val
  have hi := Topology.IsClosedEmbedding.inclusion hAO hA
  have he : (Subtype.val ⁻¹' connectedComponentIn (X \ R) z : Set ↥(Rᶜ)) =
      inclusion hAO '' connectedComponent (⟨z, hz⟩ : ↥(X \ R)) := by
    rw [connectedComponentIn_eq_image hz]
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, Subtype.ext he⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [he]
  exact hi.isClosedMap _ isClosed_connectedComponent

/-- Helper toward Proposition 3.9: a relative component joins the exterior
after the exterior is adjoined exactly when it meets the closed region's
boundary away from retained edges. This is a characterization of the actual
components, with no assumed face correspondence. -/
theorem relative_component_joins_exterior_iff
    (X R : Set ℂ) (hX : IsClosed X) (hR : IsClosed R)
    (hRX : R ⊆ X) (hext : IsPreconnected Xᶜ)
    (q z : ℂ) (hq : q ∉ X) (hz : z ∈ X \ R) :
    connectedComponentIn Rᶜ z = connectedComponentIn Rᶜ q ↔
      (connectedComponentIn (X \ R) z ∩ frontier X).Nonempty := by
  let C := connectedComponentIn (X \ R) z
  let E := connectedComponentIn Rᶜ z
  have hzC : z ∈ C := mem_connectedComponentIn hz
  have hCE : C ⊆ E := relative_component_subset_plane_component X R z
  have hCX : C ⊆ X := (connectedComponentIn_subset _ _).trans sdiff_subset
  constructor
  · intro hEq
    by_contra hn
    have hCI : C ⊆ interior X \ R := by
      intro y hy
      refine ⟨(mem_interior_iff_notMem_frontier (hCX hy)).mpr ?_,
        (connectedComponentIn_subset _ _ hy).2⟩
      intro hyf
      exact hn ⟨y, hy, hyf⟩
    have hCeq : C = connectedComponentIn (interior X \ R) z := by
      apply Subset.antisymm
      · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hzC hCI
      · exact connectedComponentIn_mono z
          (fun _ hy => ⟨interior_subset hy.1, hy.2⟩)
    have hCo : IsOpen C := by
      rw [hCeq]
      exact (isOpen_interior.sdiff hR).connectedComponentIn
    have hCc := relative_component_closed_in_complement X R hX z hz
    have hcl : closure C ∩ E ⊆ C := by
      have hc := isClosed_preimage_val.mp hCc
      have hCO : C ⊆ Rᶜ := (connectedComponentIn_subset _ _).trans
        (fun _ hy => hy.2)
      rw [inter_eq_right.mpr hCO] at hc
      intro y hy
      exact hc ⟨connectedComponentIn_subset _ _ hy.2, hy.1⟩
    have hEC : E ⊆ C := isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      hCo ⟨z, mem_connectedComponentIn hz.2, hzC⟩ hcl
    have hqE : q ∈ E := by
      change q ∈ connectedComponentIn Rᶜ z
      rw [hEq]
      exact mem_connectedComponentIn (fun hqR => hq (hRX hqR))
    exact hq (hCX (hEC hqE))
  · rintro ⟨y, hyC, hyf⟩
    have hycl : y ∈ closure Xᶜ := by
      rw [frontier_eq_closure_inter_closure] at hyf
      exact hyf.2
    have hEo : IsOpen E := hR.isOpen_compl.connectedComponentIn
    obtain ⟨w, hwE, hwX⟩ := mem_closure_iff.mp hycl E hEo (hCE hyC)
    have hQE : Xᶜ ⊆ connectedComponentIn Rᶜ w :=
      hext.subset_connectedComponentIn hwX (compl_subset_compl.mpr hRX)
    have hqE : q ∈ E := by
      change q ∈ connectedComponentIn Rᶜ z
      rw [connectedComponentIn_eq hwE]
      exact hQE hq
    exact connectedComponentIn_eq hqE

/-- Helper toward Proposition 3.9: adjoining the omitted exterior merges
exactly the relative components that meet the closed region's boundary. The
formula includes the exterior itself and every deleted-edge point. -/
theorem exterior_component_eq_union_relative_components
    (X R : Set ℂ) (hX : IsClosed X) (hR : IsClosed R)
    (hRX : R ⊆ X) (hext : IsPreconnected Xᶜ)
    (q : ℂ) (hq : q ∉ X) :
    connectedComponentIn Rᶜ q = Xᶜ ∪
      ⋃ (z : ℂ) (_ : z ∈ X \ R)
        (_ : (connectedComponentIn (X \ R) z ∩ frontier X).Nonempty),
        connectedComponentIn (X \ R) z := by
  have hQE : Xᶜ ⊆ connectedComponentIn Rᶜ q :=
    hext.subset_connectedComponentIn hq (compl_subset_compl.mpr hRX)
  ext y
  constructor
  · intro hy
    by_cases hyX : y ∈ X
    · right
      have hyR : y ∈ X \ R := ⟨hyX, connectedComponentIn_subset _ _ hy⟩
      have hjoin := (relative_component_joins_exterior_iff X R hX hR hRX hext
        q y hq hyR).mp (connectedComponentIn_eq hy).symm
      exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hyR,
        mem_iUnion.mpr ⟨hjoin, mem_connectedComponentIn hyR⟩⟩⟩
    · exact Or.inl hyX
  · rintro (hy | hy)
    · exact hQE hy
    · obtain ⟨z, hy⟩ := mem_iUnion.mp hy
      obtain ⟨hz, hy⟩ := mem_iUnion.mp hy
      obtain ⟨hjoin, hy⟩ := mem_iUnion.mp hy
      rw [← (relative_component_joins_exterior_iff X R hX hR hRX hext q z hq hz).mpr hjoin]
      exact relative_component_subset_plane_component X R z hy

private theorem route2_frontier_eq_arcs
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert)
    (hvert : Function.Surjective vert) (F : P.Face) :
    frontier F.val = ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image := by
  let K := ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image
  have hlf : LocallyFinite (fun d => (P.arc d).image) := by
    intro z
    refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, ?_⟩
    simpa only [inter_comm] using P.locally_finite (Metric.ball z 1) Metric.isBounded_ball
  have hsub (d : D) : (⋃ (_ : P.dartBorders d F), (P.arc d).image) ⊆ (P.arc d).image :=
    iUnion_subset fun _ => Subset.rfl
  have hclosed : IsClosed K := (hlf.subset hsub).isClosed_iUnion fun d =>
    isClosed_iUnion_of_finite fun _ => (P.arc d).isCompact_image.isClosed
  apply Subset.antisymm
  · intro q hqfront
    by_contra hqK
    obtain ⟨s, hs, hsafe⟩ := Metric.mem_nhds_iff.mp
      (hclosed.isOpen_compl.mem_nhds hqK)
    have hqimage := (P.face_open_frontier_subset_image hvert F).2 hqfront
    have harc : ∃ d, q ∈ (P.arc d).image := by
      rcases hqimage with ⟨v, rfl⟩ | h
      · obtain ⟨d, rfl⟩ := hvert v
        exact ⟨d, Or.inl (P.arc_start d).symm⟩
      · exact h
    obtain ⟨d, hd⟩ := harc
    have hseg : ∃ i, i + 1 < (P.arc d).points.length ∧
        q ∈ (P.arc d).segmentAt i := by
      rcases hd with hstart | ⟨i, hi, hqi⟩
      · refine ⟨0, by have := P.arc_length d; omega, ?_⟩
        rw [hstart, Polyline.segmentAt, Polyline.point_zero_eq_start]
        exact left_mem_segment ℝ _ _
      · exact ⟨i, hi, hqi⟩
    obtain ⟨i, hi, hqi⟩ := hseg
    by_cases hqend : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1)
    · obtain ⟨x, hx, hxball, hnot⟩ := P.face_endpoint_frontier_not_vertex_mem_ball
        hvert F q d hi hqend (frontier_subset_closure hqfront) hs
      obtain ⟨e, hxe, heF⟩ :=
        P.exists_mem_arc_dartBorders_of_frontier_not_vertex hvert F hx hnot
      exact hsafe hxball (mem_iUnion₂.mpr ⟨e, heF, hxe⟩)
    · have hqopen := mem_openSegment_of_ne_left_right
        (fun he => hqend (Or.inl he.symm)) (fun he => hqend (Or.inr he.symm)) hqi
      rcases (P.mem_closure_face_openSegment_iff_dartBorders hvert d F hi hqopen).mp
          (frontier_subset_closure hqfront) with hF | hF
      · exact hqK (mem_iUnion₂.mpr
          ⟨d, hF, (P.arc d).segmentAt_subset_image hi hqi⟩)
      · apply hqK
        apply mem_iUnion₂.mpr
        refine ⟨flip d, hF, ?_⟩
        rw [P.arc_image_flip]
        exact (P.arc d).segmentAt_subset_image hi hqi
  · intro q hq
    obtain ⟨d, hd, hqd⟩ := mem_iUnion₂.mp hq
    exact P.dartBorders_arc_subset_frontier hvert d F hd hqd

private theorem route2_restricted_boundary_homeomorph
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

/-- Helper toward Proposition 3.9: at every integer start, the complete
closed-region map has the prescribed boundary homeomorphism between the unique
source and target exteriors. The two closed regions are exactly the respective
exterior complements, and the original vertex and edge formulas persist. -/
theorem exists_exterior_boundary_homeomorph (W : ℤ → Fin 3) :
      ∀ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (n : ℤ) (J : WholePlaneStartIso W n)
        (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)),
      let u := shiftedStream (shiftWordInt W n) 0
      let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      let Q := inheritedDrawing W H G n univ
      let X := ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val
      let Y := ⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val
      ∃ (U : P.Face) (V : Q.Face) (hP : P.image ⊆ X) (_hQ : Q.image ⊆ Y)
        (g : X ≃ₜ Y) (b : frontier U.val ≃ₜ frontier V.val),
        P.IsUnbounded U ∧ (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
        Q.IsUnbounded V ∧ (∀ F : Q.Face, Q.IsUnbounded F → F = V) ∧
        X = U.valᶜ ∧ Y = V.valᶜ ∧
        (∀ v, (g ⟨P.pos v, hP (Or.inl ⟨v, rfl⟩)⟩ : ℂ) =
          G.pos (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))) ∧
        (∀ d : ℕ × Bool, ∃ φ : unitInterval ≃ₜ unitInterval,
          StrictMono φ ∧ ∀ t,
            (g ⟨(P.arc d).toPath t,
              hP (Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩)⟩ : ℂ) =
              (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d))).toPath (φ t)) ∧
        (∀ x : X, (g x : ℂ) ∈ frontier V.val ↔ (x : ℂ) ∈ frontier U.val) ∧
        (∀ (x : X) (hx : (x : ℂ) ∈ frontier U.val),
          (g x : ℂ) = (b ⟨x, hx⟩ : ℂ)) := by
  intro H h hpast n J hfin u P G Q X Y
  obtain ⟨U, hU, huniqU, hX⟩ := closed_region_eq_compl_exterior u hfin
    (start_boundary_hits W h n)
  obtain ⟨V, hV, huniqV, hborderV, hY⟩ := route2_inherited_exterior W H h hpast n J
    (rotation_hypothesis_shift W H n) hfin
  obtain ⟨hP, hQ, g, τ, hv, ha, _, _, _, _, _⟩ :=
    exists_closed_region_homeomorph W H h hpast n J hfin
  have hPv := kmswLimitDartVertex_surjective u hfin
  have hQv : Function.Surjective (restrictedVertex G (retainedDarts W n univ)) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  have hborderU (a : ℕ × Bool) : P.dartBorders a U ↔
      (kmswInfFaceSucc u hfin).SameCycle futureMapOuterDart a := by
    obtain ⟨U', hU', _, hborder, _⟩ :=
      monotoneFamilyDrawing_realized_boundary_twoSided u hfin (start_boundary_hits W h n)
    exact huniqU U' hU' ▸ hborder a
  let D (a : ℕ × Bool) : retainedDarts W n univ :=
    ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 a), by
      rw [retained_darts_eq_image W n J univ]
      exact ⟨a, mem_univ _, rfl⟩⟩
  have hD (a : ℕ × Bool) : Q.dartBorders (D a) V ↔ P.dartBorders a U :=
    (hborderV a (D a) rfl).trans (hborderU a).symm
  have hfront (x : X) : (g x : ℂ) ∈ frontier V.val ↔ (x : ℂ) ∈ frontier U.val := by
    constructor
    · intro hx
      rw [route2_frontier_eq_arcs Q hQv V] at hx
      obtain ⟨d, hdV, hxd⟩ := mem_iUnion₂.mp hx
      have hd := (Set.ext_iff.mp (retained_darts_eq_image W n J univ) d.val).mp d.property
      obtain ⟨a, _, ha'⟩ := hd
      have hDa : D a = d := Subtype.ext ha'
      have haU : P.dartBorders a U := (hD a).mp (hDa.symm ▸ hdV)
      rw [← Polyline.range_toPath] at hxd
      obtain ⟨s, hs⟩ := hxd
      obtain ⟨φ, _, hφ⟩ := ha a
      let t := φ.symm s
      let y : X := ⟨(P.arc a).toPath t,
        hP (Or.inr ⟨a, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩)⟩
      have hgy : (g y : ℂ) = (g x : ℂ) := by
        rw [hφ]
        change (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 a))).toPath
          (φ (φ.symm s)) = _
        rw [φ.apply_symm_apply]
        exact (congrArg (fun c : WholePlaneDart W => (G.arc c).toPath s) ha').trans hs
      have hyx : y = x := g.injective (Subtype.ext hgy)
      have hyU : (y : ℂ) ∈ frontier U.val := P.dartBorders_arc_subset_frontier hPv a U haU
        ((Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩)
      exact hyx ▸ hyU
    · intro hx
      rw [route2_frontier_eq_arcs P hPv U] at hx
      obtain ⟨a, haU, hxa⟩ := mem_iUnion₂.mp hx
      rw [← Polyline.range_toPath] at hxa
      obtain ⟨t, ht⟩ := hxa
      obtain ⟨φ, _, hφ⟩ := ha a
      have hx' : (⟨(P.arc a).toPath t,
          hP (Or.inr ⟨a, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩)⟩ : X) = x :=
        Subtype.ext ht
      rw [← hx', hφ]
      exact Q.dartBorders_arc_subset_frontier hQv (D a) V ((hD a).mpr haU)
        ((Polyline.range_toPath _).symm ▸ ⟨φ t, rfl⟩)
  obtain ⟨b, hb⟩ := route2_restricted_boundary_homeomorph X Y (frontier U.val) (frontier V.val)
    (fun _ hx => hP ((P.face_open_frontier_subset_image hPv U).2 hx))
    (fun _ hx => hQ ((Q.face_open_frontier_subset_image hQv V).2 hx)) g hfront
  refine ⟨U, V, hP, hQ, g, b, hU, huniqU, hV, huniqV, hX, hY, hv, ha, hfront, ?_⟩
  intro x hx
  exact (hb ⟨x, hx⟩).symm


private theorem route2_restricted_image_iff_arc
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (T : Set D)
    (hT : ∀ d, d ∈ T ↔ flip d ∈ T) (z : ℂ) :
    z ∈ (restrictDrawing P T hT).image ↔ ∃ d ∈ T, z ∈ (P.arc d).image := by
  have hv : Function.Surjective (restrictedVertex P T) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  rw [(restrictDrawing P T hT).image_eq_union_arcs hv]
  constructor
  · intro hz
    obtain ⟨d, hd⟩ := mem_iUnion.mp hz
    exact ⟨d.val, d.property, hd⟩
  · rintro ⟨d, hd, hz⟩
    exact mem_iUnion.mpr ⟨⟨d, hd⟩, hz⟩

/-- Helper toward Proposition 3.9: one closed-region homeomorphism matches
every retained geometric edge set, including all its incident vertices. It
therefore restricts to a homeomorphism of the relative complements for every
edge set. Relative complements are not asserted to be full plane faces. -/
theorem exists_boundary_restriction_homeomorphs (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    let X := ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val
    let Y := ⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val
    ∃ g : X ≃ₜ Y,
      (∀ x : X, (g x : ℂ) ∈ frontier Y ↔ (x : ℂ) ∈ frontier X) ∧
      ∀ K : Set ℕ,
      let P' := restrictDrawing P {d : ℕ × Bool | d.1 ∈ K} (fun _ => Iff.rfl)
      let Q' := inheritedDrawing W H G n K
      (∀ x : X, (g x : ℂ) ∈ Q'.image ↔ (x : ℂ) ∈ P'.image) ∧
      Nonempty ({x : X // (x : ℂ) ∉ P'.image} ≃ₜ {y : Y // (y : ℂ) ∉ Q'.image}) := by
  intro u P G Q X Y
  obtain ⟨U, V, hP, _, g, _, _, _, _, _, hX, hY, _, ha, hfront, _⟩ :=
    exists_exterior_boundary_homeomorph W H h hpast n J hfin
  have hbdy : ∀ x : X, (g x : ℂ) ∈ frontier Y ↔ (x : ℂ) ∈ frontier X := by
    have hfX : frontier X = frontier U.val :=
      (congrArg frontier hX).trans (frontier_compl _)
    have hfY : frontier Y = frontier V.val :=
      (congrArg frontier hY).trans (frontier_compl _)
    simpa only [hfX, hfY] using hfront
  refine ⟨g, hbdy, fun K => ?_⟩
  intro P' Q'
  have himage (x : X) : (g x : ℂ) ∈ Q'.image ↔ (x : ℂ) ∈ P'.image := by
    constructor
    · intro hx
      obtain ⟨d, hd, hxd⟩ := (route2_restricted_image_iff_arc G
        (retainedDarts W n K) (fun _ => Iff.rfl) _).mp hx
      rw [retained_darts_eq_image W n J K] at hd
      obtain ⟨a, haK, rfl⟩ := hd
      obtain ⟨φ, _, hφ⟩ := ha a
      have ht : (g x : ℂ) ∈ range
          (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 a))).toPath := by
        rw [Polyline.range_toPath]
        exact hxd
      obtain ⟨t, ht⟩ := ht
      let z : X := ⟨(P.arc a).toPath (φ.symm t), hP (Or.inr ⟨a, by
        rw [← Polyline.range_toPath]
        exact ⟨φ.symm t, rfl⟩⟩)⟩
      have hz : g z = g x := by
        apply Subtype.ext
        exact (hφ (φ.symm t)).trans (by rw [φ.apply_symm_apply]; exact ht)
      have hzx : (z : ℂ) = (x : ℂ) := congrArg Subtype.val (g.injective hz)
      apply (route2_restricted_image_iff_arc P {d : ℕ × Bool | d.1 ∈ K}
        (fun _ => Iff.rfl) _).mpr
      refine ⟨a, haK, ?_⟩
      rw [← hzx, ← Polyline.range_toPath]
      exact ⟨φ.symm t, rfl⟩
    · intro hx
      obtain ⟨a, haK, hxa⟩ := (route2_restricted_image_iff_arc P
        {d : ℕ × Bool | d.1 ∈ K} (fun _ => Iff.rfl) _).mp hx
      have ht : (x : ℂ) ∈ range (P.arc a).toPath := by
        rw [Polyline.range_toPath]
        exact hxa
      obtain ⟨t, ht⟩ := ht
      obtain ⟨φ, _, hφ⟩ := ha a
      apply (route2_restricted_image_iff_arc G (retainedDarts W n K)
        (fun _ => Iff.rfl) _).mpr
      refine ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 a), ?_, ?_⟩
      · rw [retained_darts_eq_image W n J K]
        exact ⟨a, haK, rfl⟩
      · have he : (g x : ℂ) =
            (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 a))).toPath (φ t) := by
          have hz : (⟨(P.arc a).toPath t,
              hP (Or.inr ⟨a, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩)⟩ : X) = x :=
            Subtype.ext ht
          exact hz ▸ hφ t
        rw [he, ← Polyline.range_toPath]
        exact ⟨φ t, rfl⟩
  exact ⟨himage, ⟨g.subtype (fun x => not_congr (himage x).symm)⟩⟩

private theorem relative_boundary_nonempty_iff
    (X Y R S : Set ℂ) (g : X ≃ₜ Y)
    (hRS : ∀ x : X, (g x : ℂ) ∈ S ↔ (x : ℂ) ∈ R)
    (hfront : ∀ x : X, (g x : ℂ) ∈ frontier Y ↔ (x : ℂ) ∈ frontier X)
    (x : X) (hx : (x : ℂ) ∉ R) :
    (connectedComponentIn (X \ R) (x : ℂ) ∩ frontier X).Nonempty ↔
      (connectedComponentIn (Y \ S) (g x : ℂ) ∩ frontier Y).Nonempty := by
  let A : Set X := {a | (a : ℂ) ∉ R}
  let B : Set Y := {b | (b : ℂ) ∉ S}
  have hAB : g '' A = B := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact fun hb => ha ((hRS a).mp hb)
    · intro hb
      refine ⟨g.symm b, ?_, g.apply_symm_apply b⟩
      intro ha
      exact hb (by simpa only [g.apply_symm_apply] using (hRS (g.symm b)).mpr ha)
  have hc : g '' connectedComponentIn A x = connectedComponentIn B (g x) := by
    rw [g.image_connectedComponentIn hx, hAB]
  have hgx : (g x : ℂ) ∉ S := fun hh => hx ((hRS x).mp hh)
  rw [← subtype_component_image X R x hx, ← subtype_component_image Y S (g x) hgx]
  constructor
  · rintro ⟨z, ⟨a, ha, rfl⟩, hza⟩
    refine ⟨(g a : ℂ), ⟨g a, ?_, rfl⟩, (hfront a).mpr hza⟩
    rw [← hc]
    exact ⟨a, ha, rfl⟩
  · rintro ⟨z, ⟨b, hb, rfl⟩, hzb⟩
    rw [← hc] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨(a : ℂ), ⟨a, ha, rfl⟩, (hfront a).mp hzb⟩

/-- Helper toward Proposition 3.9: one boundary-preserving closed-region
map matches every retained edge set and precisely the relative components
which merge with the exterior. The comparison holds at every integer start. -/
theorem exists_exterior_merger_transport (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    let X := ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val
    let Y := ⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val
    ∃ g : X ≃ₜ Y,
      (∀ x : X, (g x : ℂ) ∈ frontier Y ↔ (x : ℂ) ∈ frontier X) ∧
      ∀ K : Set ℕ,
        let P' := restrictDrawing P {d : ℕ × Bool | d.1 ∈ K} (fun _ => Iff.rfl)
        let Q' := inheritedDrawing W H G n K
        (∀ x : X, (g x : ℂ) ∈ Q'.image ↔ (x : ℂ) ∈ P'.image) ∧
        ∀ x : X, (x : ℂ) ∉ P'.image →
          ((connectedComponentIn (X \ P'.image) (x : ℂ) ∩ frontier X).Nonempty ↔
            (connectedComponentIn (Y \ Q'.image) (g x : ℂ) ∩ frontier Y).Nonempty) := by
  intro u P G Q X Y
  obtain ⟨g, hbdy, hg⟩ := exists_boundary_restriction_homeomorphs W H h hpast n J hfin
  refine ⟨g, hbdy, fun K => ?_⟩
  intro P' Q'
  obtain ⟨hPQ, _⟩ := hg K
  exact ⟨hPQ, relative_boundary_nonempty_iff X Y P'.image Q'.image g hPQ hbdy⟩


/- EXACT REMAINING OBLIGATIONS (comments, not premises or declarations).

The deterministic exterior-uniqueness target is proved above. The relative
component decomposition, oriented incidence within each restriction, and the
exterior-merging criterion are proved. The following simultaneous source-to-target
face equivalence after deletion still has to be assembled; boundedness and the
oriented incidence equivalence must be checked for the same correspondence.

1. Complete deletion comparison for arbitrary retained geometric edge sets.

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (n : ℤ) (J : WholePlaneStartIso W n)
  (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0))
  (K : Set ℕ),
  let u := shiftedStream (shiftWordInt W n) 0
  let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let T := {d : ℕ × Bool | d.1 ∈ K}
  let P' := restrictDrawing P T (fun _ => Iff.rfl)
  let Q' := inheritedDrawing W H G n K
  ∃ τ : P'.Face ≃ Q'.Face,
    (∀ F : P'.Face, Q'.IsUnbounded (τ F) ↔ P'.IsUnbounded F) ∧
    (∀ (a : T) (d : retainedDarts W n K),
      J.dart (wholePlaneDartι (shiftWordInt W n) 0 a.val) = d.val →
      ∀ F : P'.Face, Q'.dartBorders d (τ F) ↔ P'.dartBorders a F)

The complete numbered targets below retain every original binder and clause.
They are not proved by the separate helper exports in this file.

2. Exact Proposition 5.1 comparison (ShiftedStartGeometry.lean:425).

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∀ (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
    (uibotWholePlaneSourceRoot W H G) A.map A.root)
  (n : ℤ) (J : WholePlaneStartIso W n),
  let u := fun i => futureMapShiftedCodePath n W (i + 1)
  ∀ (hflow : HasFlowLineHits u)
    (hhat : hatLimitFiniteIncidence u)
    (hprime : primedLimitFiniteIncidence u)
    (hb : BoundaryHitWitnesses u),
  ∀ K : Set ℕ,
    K = {e | MhatGeometricEdge u e} ∨ K = {e | primeGeomEdge u hprime hb e} →
    let U := shiftWordInt W n
    let S := uibotWholePlaneSourceDomain W H G hp
    let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι U 0 v))
    let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι U 0 e))
    let D := fun d => intrinsicFutureDartEquiv (A := S) I
      (uibotCut2SourceDartEquiv W H h hpast hp (J.dart (wholePlaneDartι U 0 d)))
    let P := monotoneFamilyDrawing u hhat (monotone_family_all u)
    let T := {d : ℕ × Bool | d.1 ∈ K}
    let Q := restrictDrawing P T (fun _ => Iff.rfl)
    ∃ R : Q.Face → Set ℂ,
      Function.Injective R ∧
      Set.range R = intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (V '' intrinsicConsumer51RunVertices u K) (E '' K)) ∧
      (∀ F, IsOpen (R F)) ∧
      (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
      (∀ d : T, intrinsicFutureRotation A (E '' K)
        (D (drawingFirstReturnPerm P T d).val) (D d.val)) ∧
      (∀ (d : T) (F : Q.Face),
        (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F)

3. Exact Lemma 5.2 analogue (ShiftedStartGeometry.lean:463).

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∀ (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
    (uibotWholePlaneSourceRoot W H G) A.map A.root)
    (k : ℤ),
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := fun i => w (t + i)
  ∀ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
  let S := uibotWholePlaneSourceDomain W H G hp
  let V := intrinsicConsumer52HatVertex W H G hp A I t hτ
  let E := intrinsicConsumer52HatEdge W H G hp A I t hτ
  let D := fun d : ℕ × Bool => intrinsicFutureDartEquiv (A := S) I
    (uibotCut2SourceDartEquiv W H h hpast hp
      (wholePlaneDartι W 0 (kmswWindowEdgeMapInf w t d.1, d.2)))
  let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
  let T := {d : ℕ × Bool | MhatGeometricEdge u d.1}
  let Q := hatRealizedDrawing u hfin
  ∃ R : Q.Face → Set ℂ,
    Function.Injective R ∧
    Set.range R = intrinsicConsumer51FaceRegions
      (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
    (∀ F, IsOpen (R F)) ∧
    (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
    (∀ d : T, intrinsicFutureRotation A (Set.range E)
      (D (drawingFirstReturnPerm P T d).val) (D d.val)) ∧
    (∀ (d : T) (F : Q.Face),
      (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F)


4. Exact nonzero-stopping-time face-orbit comparison
(IntrinsicConsumer52FaceOrbits.lean:376). Every binder is retained.

  ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
  ∀ (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root)
    (k : ℤ),
    let t := boundaryHitTime (shiftedStream W 0) h k
    let u := fun i => shiftedStream W 0 (t + i)
    ∀ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let V := intrinsicConsumer52HatVertex W H G hp A I t hτ
    let E := intrinsicConsumer52HatEdge W H G hp A I t hτ
    let D := intrinsicConsumer52HatDart W H h hpast hp A I t hτ
    ∃ R : HatFaceOrbit u hτ hfin → Set ℂ,
      Function.Injective R ∧
      Set.range R = intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
      (∀ q, IsOpen (R q)) ∧
      (∀ d q, (∀ s, LeftAtOn (R q) (intrinsicFutureDartArc A (D d)) s) ↔
        Quotient.mk _ d = q) ∧
      (∀ q, (¬ Bornology.IsBounded (R q)) ↔
        q = Quotient.mk _ futureMapOuterDart) ∧
      (∀ d, (∀ s, LeftAtOn (R (Quotient.mk _ futureMapOuterDart))
        (intrinsicFutureDartArc A (D d)) s) ↔ limitExternalDart (hatCodes u hτ) d)


5. Exact Lemma 5.2 assembly (IntrinsicConsumer52FaceOrbits.lean:419).

  ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
    let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W
    ∃ (H : WholePlaneRotationHypothesis W)
      (h : BoundaryHitWitnesses (shiftedStream W 0))
      (hpast : BoundaryHitWitnesses (kmswPastCode W))
      (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
    let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
      Nonempty (D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
        (uibotWholePlaneSourceRoot W H G) A.map A.root) ∧
      ∃! C : IntrinsicFutureCut2 A,
        (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
        ∀ I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root,
        let t := intrinsicStageBoundaryTime W H h hLL G hp A I
        t 0 = 0 ∧
        ∀ k : ℤ,
          IsLeast {n : ℕ | C.x k = intrinsicStageActiveInitial A
            (intrinsicStageActiveEdges W H G hp A I) n} (t k) ∧
          t k = boundaryHitTime (shiftedStream W 0) h k ∧
          boundaryCodeStoppingTime k (shiftedCodePath W 0) = (t k : ℕ∞) ∧
          wholePlaneIIDCodeMeasure.map (boundaryFutureCode k) =
            wholePlaneIIDCodeMeasure.map (boundaryFutureCode 0) ∧
          wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ boundaryFutureCode k) =
            iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) ∧
          (fun i => boundaryFutureCode k W (i + 1)) =
            (fun i => shiftedStream W 0 (t k + i)) ∧
          (∃ hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t k + i)),
            hatLawCodes (boundaryFutureCode k W) =
              hatCodes (fun i => shiftedStream W 0 (t k + i)) hτ) ∧
          M0CutShiftContainment W H h hLL k ∧
          boundaryFutureRootedMapClause W h k ∧
          IntrinsicStageShiftContainment W A
            (fun j => I.vertexEquiv (wholePlaneVertexι W 0 j))
            (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j))
            C.edges C.missing (C.x k) (t k) ∧
          ∃ (hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t k + i)))
            (hfin : hatLimitFiniteIncidence (fun i => shiftedStream W 0 (t k + i))),
          let u := fun i => shiftedStream W 0 (t k + i)
          let V := intrinsicConsumer52HatVertex W H G hp A I (t k) hτ
          let E := intrinsicConsumer52HatEdge W H G hp A I (t k) hτ
          let D := intrinsicConsumer52HatDart W H h hpast hp A I (t k) hτ
          hatLawCodes (boundaryFutureCode k W) = hatCodes u hτ ∧
          hatRootedMapClause u hτ hfin ∧
          Function.Injective E ∧
          E 0 = (intrinsicStageActiveEdges W H G hp A I (t k)).val ∧
          (∀ e : ℕ, ∃ he : ¬ A.map.missing (E e),
            A.map.tail ⟨E e, he⟩ = V (edgeWest (hatCodes u hτ) e) ∧
            A.map.head ⟨E e, he⟩ = V (edgeEast (hatCodes u hτ) e)) ∧
          (∀ d, intrinsicFutureRotation A (Set.range E)
            (D (kmswInfRot (hatCodes u hτ) (hatCodes_finiteIncidence u hτ hfin) d))
            (D d)) ∧
          ∃ R : HatFaceOrbit u hτ hfin → Set ℂ,
            Function.Injective R ∧
            Set.range R = intrinsicConsumer51FaceRegions
              (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
            (∀ q, IsOpen (R q)) ∧
            (∀ d q, (∀ s, LeftAtOn (R q) (intrinsicFutureDartArc A (D d)) s) ↔
              Quotient.mk _ d = q) ∧
            (∀ q, (¬ Bornology.IsBounded (R q)) ↔
              q = Quotient.mk _ futureMapOuterDart) ∧
            (∀ d, (∀ s, LeftAtOn (R (Quotient.mk _ futureMapOuterDart))
              (intrinsicFutureDartArc A (D d)) s) ↔ limitExternalDart (hatCodes u hτ) d) -/

end DirectedDistances.PaperProofs.Section3.ShiftedStartClosedRegionRoute2
