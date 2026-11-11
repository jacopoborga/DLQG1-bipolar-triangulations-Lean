/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry4
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers51And52Complete
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumer52FaceOrbits
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumersMuAE

/-! Helper toward Proposition 3.9: exterior incidence at arbitrary integer starts.

This continues the exterior obligation of `ShiftedStartGeometry4`. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open Set Topology

private theorem final_start_dart_injective (W : ℤ → Fin 3) (n : ℤ)
    (J : WholePlaneStartIso W n) :
    Function.Injective (fun d => J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)) :=
  J.dart.injective.comp (wholePlaneDartι_injective _ _)

/-- Helper toward Proposition 3.9: a retained dart borders an unbounded
inherited region exactly when its source dart is in the external face orbit.
This identifies exterior incidence without assuming an ambient extension. -/
theorem inherited_dart_unbounded_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    ∀ (a : ℕ × Bool) (d : retainedDarts W n univ),
      J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val →
      ∀ F : Q.Face, Q.dartBorders d F →
        (Q.IsUnbounded F ↔ (kmswInfFaceSucc u hfin).SameCycle futureMapOuterDart a) := by
  intro u G Q a d ha F hdF
  let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
  obtain ⟨Φ, τ, E, hv, harc, he, hb, hd, hcollision⟩ :=
    exists_bounded_face_equiv W H h hpast n J hfin
  have hu := start_boundary_hits W h n
  obtain ⟨U, hU, huniq, hborder, _⟩ :=
    monotoneFamilyDrawing_realized_boundary_twoSided u hfin hu
  constructor
  · intro hF
    obtain ⟨B, hB⟩ := dart_borders_exists u hfin hu a
    have hBU : P.IsUnbounded B := by
      by_contra hn
      let b : {B : P.Face // ¬ P.IsUnbounded B} := ⟨B, hn⟩
      have hdτ := (hd b d).mpr ⟨a, hB, ha⟩
      have hEq := Q.dartBorders_face_unique d F (τ b).val hdF hdτ
      exact (τ b).property (hEq ▸ hF)
    exact (hborder a).mp (huniq B hBU ▸ hB)
  · intro haU
    by_contra hn
    let f : {F : Q.Face // ¬ Q.IsUnbounded F} := ⟨F, hn⟩
    obtain ⟨b, hb⟩ := τ.surjective f
    have hdτ : Q.dartBorders d (τ b).val := by rw [hb]; exact hdF
    obtain ⟨a', ha', ha'd⟩ := (hd b d).mp hdτ
    have haa : a' = a := final_start_dart_injective W n J (ha'd.trans ha.symm)
    subst a'
    have hEq := P.dartBorders_face_unique a b.val U ha' ((hborder a).mpr haU)
    exact b.property (hEq.symm ▸ hU)

/-- Helper toward Proposition 3.9: every external source dart has exactly
one unbounded inherited region on its left. The uniqueness here is for that
dart; global uniqueness of the exterior is a separate assertion. -/
theorem inherited_external_dart_existsUnique (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    ∀ (a : ℕ × Bool) (d : retainedDarts W n univ),
      J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val →
      (kmswInfFaceSucc u hfin).SameCycle futureMapOuterDart a →
      ∃! F : Q.Face, Q.IsUnbounded F ∧ Q.dartBorders d F := by
  intro u G Q a d ha hext
  have hvert : Function.Surjective (restrictedVertex G (retainedDarts W n univ)) := by
    rintro ⟨v, b, hb, hbv⟩
    exact ⟨⟨b, hb⟩, Subtype.ext hbv⟩
  obtain ⟨F, hdF, huniq⟩ := Q.dartBorders_existsUnique_of_locallyFiniteVertexImage32
    (LeftSideHalfDisk.locallyFiniteVertexImage_of_surjective Q hvert) d
  exact ⟨F, ⟨(inherited_dart_unbounded_iff W H h hpast n J hfin a d ha F hdF).mpr
    hext, hdF⟩, fun F' hF' => huniq F' hF'.2⟩

/-- Helper toward Proposition 3.9: the inherited drawing at every integer
start has an actual unbounded complementary region, containing the left side
of the transported external root dart. -/
theorem inherited_unbounded_face_exists (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    ∃ U : Q.Face, Q.IsUnbounded U := by
  intro G Q
  let a := futureMapOuterDart
  let d : retainedDarts W n univ :=
    ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 a), by
      rw [retained_darts_eq_image W n J univ]
      exact ⟨a, mem_univ _, rfl⟩⟩
  obtain ⟨U, hU, _⟩ := inherited_external_dart_existsUnique W H h hpast n J hfin
    a d rfl (Equiv.Perm.SameCycle.refl _ _)
  exact ⟨U, hU.1⟩

private theorem final_locally_finite_vertex_segments
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

private theorem final_locally_finite_border_predecessor
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert)
    (d : D) (F : P.Face) (hd : P.dartBorders d F) :
    P.dartBorders (flip (rot d)) F := by
  obtain ⟨r, hr, hlocal⟩ := final_locally_finite_vertex_segments P hv (vert d)
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

private theorem final_firstReturn_of_inverse_scan
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

private theorem final_start_rotation (W : ℤ → Fin 3)
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
  exact final_firstReturn_of_inverse_scan G (kmswInfRot (shiftedStream U 0) hfin)
    i hscan a

private theorem final_inherited_border_sameCycle (W : ℤ → Fin 3)
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
    rw [final_start_rotation W H G n J H' hfin a (D a) rfl]
    change wholePlaneDartFlip W (J.dart (wholePlaneDartι (shiftWordInt W n) 0
      (kmswInfRot u hfin a))) =
      J.dart (wholePlaneDartι (shiftWordInt W n) 0
        ((kmswInfRot u hfin a).1, !(kmswInfRot u hfin a).2))
    erw [J.dart_apply, J.dart_apply]
    rfl
  have hinv (c : ℕ × Bool) : Q.dartBorders (D c) F → Q.dartBorders (D (σ.symm c)) F := by
    intro hc
    have hh := final_locally_finite_border_predecessor Q hvert (D c) F hc
    rwa [hpred] at hh
  have hfwd (c : ℕ × Bool) : Q.dartBorders (D c) F → Q.dartBorders (D (σ c)) F := by
    intro hc
    obtain ⟨K, hK, _⟩ := Q.dartBorders_existsUnique_of_locallyFiniteVertexImage32
      (LeftSideHalfDisk.locallyFiniteVertexImage_of_surjective Q hvert) (D (σ c))
    have hK' := final_locally_finite_border_predecessor Q hvert (D (σ c)) K hK
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

private theorem final_inherited_exterior (W : ℤ → Fin 3)
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
      exact (final_inherited_border_sameCycle W H G n J H' hfin
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

open MeasureTheory DirectedDistances.RandomWalk

private theorem final_ae_shift_rotation :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ n : ℤ, WholePlaneRotationHypothesis (shiftWordInt W n) := by
  apply ae_all_iff.mpr
  intro n
  exact (measurePreserving_futureMapCodeShift n).quasiMeasurePreserving.ae
    wholePlaneIID_ae_rotationHypothesis

/-- Helper toward Proposition 3.9: on one common iid event, every integer
start has exactly one inherited exterior, with its complete external-dart
incidence. The closed bounded region is exactly that exterior's complement.
No ambient homeomorphism or exterior extension is assumed. -/
theorem ae_inherited_exterior :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (n : ℤ) (J : WholePlaneStartIso W n)
        (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)),
      let u := shiftedStream (shiftWordInt W n) 0
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      let Q := inheritedDrawing W H G n univ
      ∃ U : Q.Face, Q.IsUnbounded U ∧
        (∀ F : Q.Face, Q.IsUnbounded F → F = U) ∧
        (∀ (a : ℕ × Bool) (d : retainedDarts W n univ),
          J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val →
          (Q.dartBorders d U ↔ (kmswInfFaceSucc u hfin).SameCycle futureMapOuterDart a)) ∧
        (⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val) = U.valᶜ := by
  filter_upwards [final_ae_shift_rotation] with W hW
  intro H h hpast n J hfin
  exact final_inherited_exterior W H h hpast n J (hW n) hfin

private theorem final_frontier_eq_arcs
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

private theorem final_restricted_boundary_homeomorph
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

/-- Helper toward Proposition 3.9: on the common iid event, the complete
closed-region map has the prescribed boundary homeomorphism between the unique
source and target exteriors. The two closed regions are exactly the respective
exterior complements, and the original vertex and edge formulas persist. -/
theorem ae_exists_exterior_boundary_homeomorph :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
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
  filter_upwards [ae_inherited_exterior] with W hW
  intro H h hpast n J hfin u P G Q X Y
  obtain ⟨U, hU, huniqU, hX⟩ := closed_region_eq_compl_exterior u hfin
    (start_boundary_hits W h n)
  obtain ⟨V, hV, huniqV, hborderV, hY⟩ := hW H h hpast n J hfin
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
      rw [final_frontier_eq_arcs Q hQv V] at hx
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
      rw [final_frontier_eq_arcs P hPv U] at hx
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
  obtain ⟨b, hb⟩ := final_restricted_boundary_homeomorph X Y (frontier U.val) (frontier V.val)
    (fun _ hx => hP ((P.face_open_frontier_subset_image hPv U).2 hx))
    (fun _ hx => hQ ((Q.face_open_frontier_subset_image hQv V).2 hx)) g hfront
  refine ⟨U, V, hP, hQ, g, b, hU, huniqU, hV, huniqV, hX, hY, hv, ha, hfront, ?_⟩
  intro x hx
  exact (hb ⟨x, hx⟩).symm

/-- Helper toward Proposition 3.9: all shifted source faces, including
the exterior, correspond bijectively to all inherited complementary regions
on one common iid event. Every dart incidence and unboundedness is preserved.
This is a region correspondence, not an ambient plane extension. -/
theorem ae_exists_face_equiv :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (n : ℤ) (J : WholePlaneStartIso W n)
        (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)),
      let u := shiftedStream (shiftWordInt W n) 0
      let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      let Q := inheritedDrawing W H G n univ
      ∃ τ : P.Face ≃ Q.Face,
        (∀ F : P.Face, Q.IsUnbounded (τ F) ↔ P.IsUnbounded F) ∧
        (∀ (a : ℕ × Bool) (d : retainedDarts W n univ),
          J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val →
          ∀ F : P.Face, Q.dartBorders d (τ F) ↔ P.dartBorders a F) := by
  classical
  filter_upwards [ae_inherited_exterior] with W hW
  intro H h hpast n J hfin u P G Q
  obtain ⟨U, hU, huniqU, hborderU, _⟩ :=
    monotoneFamilyDrawing_realized_boundary_twoSided u hfin (start_boundary_hits W h n)
  obtain ⟨V, hV, huniqV, hborderV, _⟩ := hW H h hpast n J hfin
  obtain ⟨_, τ, _, _, _, _, _, hd, _⟩ := exists_bounded_face_equiv W H h hpast n J hfin
  let f (F : P.Face) : Q.Face := if hF : P.IsUnbounded F then V else (τ ⟨F, hF⟩).val
  have hbound (F : P.Face) : Q.IsUnbounded (f F) ↔ P.IsUnbounded F := by
    dsimp only [f]
    split_ifs with hF
    · exact iff_of_true hV hF
    · exact iff_of_false (τ ⟨F, hF⟩).property hF
  have hinc (a : ℕ × Bool) (d : retainedDarts W n univ)
      (ha : J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val) (F : P.Face) :
      Q.dartBorders d (f F) ↔ P.dartBorders a F := by
    dsimp only [f]
    split_ifs with hF
    · have hFU := huniqU F hF
      rw [hFU]
      exact (hborderV a d ha).trans (hborderU a).symm
    · rw [hd ⟨F, hF⟩ d]
      constructor
      · rintro ⟨a', ha', hmap⟩
        have he : a' = a := final_start_dart_injective W n J (hmap.trans ha.symm)
        exact he ▸ ha'
      · intro haF
        exact ⟨a, haF, ha⟩
  have hfi : Function.Injective f := by
    intro F K hFK
    obtain ⟨a, haF⟩ := P.face_has_bordering_dart (kmswLimitDartVertex_surjective u hfin)
      (0, false) F
    let d : retainedDarts W n univ :=
      ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 a), by
        rw [retained_darts_eq_image W n J univ]
        exact ⟨a, mem_univ _, rfl⟩⟩
    have hdF := (hinc a d rfl F).mpr haF
    rw [hFK] at hdF
    exact P.dartBorders_face_unique a F K haF ((hinc a d rfl K).mp hdF)
  have hfs : Function.Surjective f := by
    intro F
    by_cases hF : Q.IsUnbounded F
    · refine ⟨U, ?_⟩
      dsimp only [f]
      rw [dite_eq_left hU]
      exact (huniqV F hF).symm
    · obtain ⟨B, hB⟩ := τ.surjective ⟨F, hF⟩
      refine ⟨B.val, ?_⟩
      dsimp only [f]
      rw [dite_eq_right B.property]
      exact congrArg Subtype.val hB
  exact ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, hbound, hinc⟩


























































































































































































































end DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry
