/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSide4CrossWitness4

/-! Creation-time transport for equal aligned nonnegative left presentation codes. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: future creation triangles embed into the
run-zero creation triangle at the shifted creation time, with cyclic order. -/
theorem lPlus_window_creationTriangle_rotated
    (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ)
    (j : TriangleCreationTime (boundaryGluingFutureStream W h k)) :
    List.IsRotated
      ((stageTriangleDartList (boundaryGluingFutureStream W h k) j).map
        (fun d => (boundaryGluingEdgeMap W h k d.1, d.2)))
      (stageTriangleDartList (shiftedStream W 0)
        ⟨boundaryHitTime (shiftedStream W 0) h k + j.val, j.property⟩) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let U := boundaryGluingFutureStream W h k
  have hr := kmswWindowPatchData_triangle_rotated w t (j.val + 1) j.val
    (Nat.lt_succ_self _) j.property
  have hm : (stageTriangleDartList U j).map
      (fun d => (boundaryGluingEdgeMap W h k d.1, d.2)) =
      (stageTriangleDartList U j).map
        (fun d => ((kmswWindowPatchData w t (j.val + 1)).φ d.1, d.2)) := by
    apply List.map_congr_left
    intro d hd
    have hdlt := stageTriangleDartList_lt U (j.val + 1) j
      (Nat.lt_succ_self _) d hd
    exact Prod.ext (kmswWindowEdgeMapInf_eq_stage w t (j.val + 1) d.1 hdlt) rfl
  rw [hm]
  exact hr

/-- Helper toward Lemma 5.5: every run-zero creation dart is either before
the stopping stage or has an oriented creation-dart representative in one of
the two future blocks. This includes positive boundary indices. -/
theorem LPlusSidePresentationSourceWitness.creationDart_prefix_or_future_block
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r)
    (J : TriangleCreationTime (shiftedStream s.W 0))
    (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList (shiftedStream s.W 0) J) :
    J.val < boundaryHitTime (shiftedStream s.W 0) s.h k ∨
      (∃ a : ℕ × Bool, ∃ j : TriangleCreationTime
          (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ),
        lMinusPrimedDartImage s.hτ a = d ∧ a ∈ stageTriangleDartList _ j) ∨
      (∃ a : ℕ × Bool, ∃ j : TriangleCreationTime
          (hatCodes (boundaryGluingFutureStream s.W s.h k) s.hτ),
        (boundaryGluingHatEdgeMap s.W s.h k s.hτ a.1, a.2) = d ∧
          a ∈ stageTriangleDartList _ j) := by
  let w := shiftedStream s.W 0
  let t := boundaryHitTime w s.h k
  let U := boundaryGluingFutureStream s.W s.h k
  by_cases hJ : J.val < t
  · exact Or.inl hJ
  · right
    let j : TriangleCreationTime U := ⟨J.val - t, by
      change w (t + (J.val - t)) = 0 ∨ w (t + (J.val - t)) = 1
      rw [Nat.add_sub_of_le (by omega : t ≤ J.val)]
      exact J.property⟩
    have hj : (⟨t + j.val, j.property⟩ : TriangleCreationTime w) = J := by
      apply Subtype.ext
      dsimp [j]
      omega
    have hrot := lPlus_window_creationTriangle_rotated s.W s.h k j
    rw [hj] at hrot
    obtain ⟨a, ha, had⟩ := List.mem_map.mp (hrot.mem_iff.mpr hd)
    let I : (ℕ × Bool) → ℕ × Bool :=
      fun b => (boundaryGluingEdgeMap s.W s.h k b.1, b.2)
    rcases lMinusFutureCreationDart_in_block s.hτ s.hfin j a ha with
      ⟨b, jb, hb, hjb⟩ | ⟨b, jb, hb, hjb⟩
    · exact Or.inl ⟨b, jb, (congrArg I hb).trans had, hjb⟩
    · exact Or.inr ⟨b, jb, (congrArg I hb).trans had, hjb⟩

/-- Helper toward Lemma 5.5: a retained face has a prefix creation time or
an oriented primed/hatted creation-dart seed. No triangle correspondence is
assumed and no sign condition is needed for this classification. -/
theorem LPlusSidePresentationSourceWitness.faceNext_prefix_or_future_block
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r)
    (d e : ℕ × Bool) (hde : (m0GeodesicSide s.hp s.P .left).faceNext d e) :
    (∃ J : TriangleCreationTime (shiftedStream s.W 0),
      J.val < boundaryHitTime (shiftedStream s.W 0) s.h k ∧
        d ∈ stageTriangleDartList _ J ∧
        ∀ a ∈ stageTriangleDartList _ J,
          a.1 ∈ (m0GeodesicSide s.hp s.P .left).edges) ∨
      (∃ a : ℕ × Bool, ∃ j : TriangleCreationTime
          (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ),
        lMinusPrimedDartImage s.hτ a = d ∧ a ∈ stageTriangleDartList _ j) ∨
      (∃ a : ℕ × Bool, ∃ j : TriangleCreationTime
          (hatCodes (boundaryGluingFutureStream s.W s.h k) s.hτ),
        (boundaryGluingHatEdgeMap s.W s.h k s.hτ a.1, a.2) = d ∧
          a ∈ stageTriangleDartList _ j) := by
  obtain ⟨J, hd, hall⟩ := lMinusActualFaceNext_triangle s.hp s.P d e hde
  rcases s.creationDart_prefix_or_future_block x k r J d hd with hJ | hblock
  · exact Or.inl ⟨J, hJ, hd, hall⟩
  · exact Or.inr hblock

/-- Helper toward Lemma 5.5: equal stopped-prefix codes preserve the
creation time and all three oriented darts of each earlier triangle. -/
theorem lPlusSourceWitnessAligned_prefix_creationTriangle_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code)
    (J : TriangleCreationTime (shiftedStream s.W 0))
    (hJ : J.val < boundaryHitTime (shiftedStream s.W 0) s.h k) :
    ∃ J' : TriangleCreationTime (shiftedStream s'.W 0),
      J'.val = J.val ∧
      J'.val < boundaryHitTime (shiftedStream s'.W 0) s'.h k ∧
      stageTriangleDartList (shiftedStream s.W 0) J =
        stageTriangleDartList (shiftedStream s'.W 0) J' := by
  have hc := (lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq
    x k r r' s.toLPlusSidePresentationSourceWitness
      s'.toLPlusSidePresentationSourceWitness hr).1
  have ht := lPlusBoundaryHitTime_eq_of_boundaryPrefixCode_eq s.W s'.W s.h s'.h k hc
  have heq (i : ℕ) (hi : i < boundaryHitTime (shiftedStream s.W 0) s.h k) :
      shiftedStream s.W 0 i = shiftedStream s'.W 0 i := by
    have hi' : i < boundaryHitTime (shiftedStream s'.W 0) s'.h k := by omega
    exact (lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt s.W s.h k hi).symm.trans
      ((congrFun hc i).trans
        (lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt s'.W s'.h k hi'))
  let J' : TriangleCreationTime (shiftedStream s'.W 0) :=
    ⟨J.val, by rw [← heq J.val hJ]; exact J.property⟩
  refine ⟨J', rfl, ?_, ?_⟩
  · change J.val < _
    omega
  · have hstage := kmswStage_eq_of_prefix (shiftedStream s.W 0)
      (shiftedStream s'.W 0) J.val (fun i hi => heq i (hi.trans hJ))
    simp only [stageTriangleDartList, stageTriangleDartTriple, J', hstage, heq J.val hJ]

/-- Helper toward Lemma 5.5: a triangle before a nonnegative stopping
stage is already present before the final, triangle-free down step. -/
theorem lPlus_prefix_creationTime_lt_previous
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (k : ℤ) (hk : 0 ≤ k)
    (J : TriangleCreationTime w) (hJ : J.val < boundaryHitTime w h k) :
    J.val < boundaryHitTime w h k - 1 := by
  by_cases hk0 : k = 0
  · subst k
    rw [boundaryHitTime_zero] at hJ
    omega
  · obtain ⟨m, ht, hm, _⟩ := lPlus_positive_hit_fresh w h (by omega : 0 < k)
    have hne : J.val ≠ m := by
      intro he
      have hc := J.property
      rw [he, hm] at hc
      rcases hc with hc | hc <;> contradiction
    omega

/-- Helper toward Lemma 5.5: each creation triangle before the nonnegative
hit is wholly retained in the actual left side, including missing edges. -/
theorem LPlusSidePresentationSourceWitness.prefix_creationTriangle_retained
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k)
    (J : TriangleCreationTime (shiftedStream s.W 0))
    (hJ : J.val < boundaryHitTime (shiftedStream s.W 0) s.h k) :
    ∀ d ∈ stageTriangleDartList (shiftedStream s.W 0) J,
      d.1 ∈ (m0GeodesicSide s.hp s.P .left).edges := by
  have hprev := lPlus_prefix_creationTime_lt_previous _ s.h k hk J hJ
  have hkpos : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    subst k
    rw [boundaryHitTime_zero] at hJ
    omega
  intro d hd
  apply boundaryGluingPrefixMinusEdges_subset_left s.W s.h k s.longest s.hp s.P hk
  rw [lPlusPrefixMinusEdges_eq_previousStage hkpos]
  exact stageTriangleDartList_lt _ _ J hprev d hd

/-- Helper toward Lemma 5.5: equal aligned codes transport every prefix
creation triangle with its exact time, oriented darts and full retention. -/
theorem lPlusSourceWitnessAligned_prefix_retained_creationTriangle_transport
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code)
    (J : TriangleCreationTime (shiftedStream s.W 0))
    (hJ : J.val < boundaryHitTime (shiftedStream s.W 0) s.h k) :
    ∃ J' : TriangleCreationTime (shiftedStream s'.W 0),
      J'.val = J.val ∧
      stageTriangleDartList (shiftedStream s.W 0) J =
        stageTriangleDartList (shiftedStream s'.W 0) J' ∧
      (∀ d ∈ stageTriangleDartList (shiftedStream s.W 0) J,
        d.1 ∈ (m0GeodesicSide s.hp s.P .left).edges) ∧
      (∀ d ∈ stageTriangleDartList (shiftedStream s'.W 0) J',
        d.1 ∈ (m0GeodesicSide s'.hp s'.P .left).edges) := by
  obtain ⟨J', hj, hJ', hlist⟩ :=
    lPlusSourceWitnessAligned_prefix_creationTriangle_eq x k r r' s s' hr J hJ
  exact ⟨J', hj, hlist,
    s.toLPlusSidePresentationSourceWitness.prefix_creationTriangle_retained x k r hk J hJ,
    s'.toLPlusSidePresentationSourceWitness.prefix_creationTriangle_retained x k r' hk J' hJ'⟩

/-- Helper toward Lemma 5.5: an injective map sending a creation triangle
into a creation triangle exhausts the latter's three oriented darts. -/
theorem lPlus_creationTriangle_image_eq
    (u v : ℕ → Fin 3) (j : TriangleCreationTime u) (J : TriangleCreationTime v)
    (I : (ℕ × Bool) → ℕ × Bool) (hinj : Function.Injective I)
    (hmap : ∀ a ∈ stageTriangleDartList u j, I a ∈ stageTriangleDartList v J) :
    ∀ b, b ∈ stageTriangleDartList v J ↔
      ∃ a ∈ stageTriangleDartList u j, I a = b := by
  have hs : ((stageTriangleDartList u j).toFinset.image I) =
      (stageTriangleDartList v J).toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact List.mem_toFinset.mpr (hmap a (List.mem_toFinset.mp ha))
    · rw [Finset.card_image_of_injective _ hinj,
        List.toFinset_card_of_nodup (stageTriangleDartList_nodup u j),
        List.toFinset_card_of_nodup (stageTriangleDartList_nodup v J)]
      simp only [stageTriangleDartList, List.length_cons, List.length_nil]
      exact le_rfl
  intro b
  have hh := Finset.ext_iff.mp hs b
  simpa only [Finset.mem_image, List.mem_toFinset] using hh.symm

/-- Helper toward Lemma 5.5: every primed creation triangle maps onto one
retained run-zero creation triangle at every boundary index. -/
theorem LPlusSidePresentationSourceWitness.primed_creationTriangle_retained
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r)
    (j : TriangleCreationTime
      (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ)) :
    ∃ J : TriangleCreationTime (shiftedStream s.W 0),
      (∀ d, d ∈ stageTriangleDartList (shiftedStream s.W 0) J ↔
        ∃ a ∈ stageTriangleDartList _ j, lMinusPrimedDartImage s.hτ a = d) ∧
      (∀ d ∈ stageTriangleDartList (shiftedStream s.W 0) J,
        d.1 ∈ (m0GeodesicSide s.hp s.P .left).edges) := by
  let U := boundaryGluingFutureStream s.W s.h k
  let p := primedCode (primedSimInput U) s.hτ
  obtain ⟨J₀, hmap₀⟩ := lMinusPrimedCreationTriangle_future_stageTriangle s.hτ s.hfin j
  have hmap (a : ℕ × Bool) (ha : a ∈ stageTriangleDartList p j) :
      primedLimitDartMap U s.hτ a ∈ stageTriangleDartList U J₀ := hmap₀ a ha
  have heq := lPlus_creationTriangle_image_eq p U j J₀ _
    (primedLimitDartMap_injective U s.hτ) hmap
  let J : TriangleCreationTime (shiftedStream s.W 0) :=
    ⟨boundaryHitTime (shiftedStream s.W 0) s.h k + J₀.val, J₀.property⟩
  have hrot := lPlus_window_creationTriangle_rotated s.W s.h k J₀
  have hmem (d : ℕ × Bool) : d ∈ stageTriangleDartList (shiftedStream s.W 0) J ↔
      ∃ a ∈ stageTriangleDartList p j, lMinusPrimedDartImage s.hτ a = d := by
    constructor
    · intro hd
      obtain ⟨b, hb, hbd⟩ := List.mem_map.mp (hrot.mem_iff.mpr hd)
      obtain ⟨a, ha, hab⟩ := (heq b).mp hb
      exact ⟨a, ha, (congrArg
        (fun b : ℕ × Bool => (boundaryGluingEdgeMap s.W s.h k b.1, b.2)) hab).trans hbd⟩
    · rintro ⟨a, ha, rfl⟩
      exact hrot.mem_iff.mp (List.mem_map.mpr ⟨_, hmap a ha, rfl⟩)
  refine ⟨J, hmem, ?_⟩
  intro d hd
  obtain ⟨a, _, rfl⟩ := (hmem d).mp hd
  exact boundaryGluingPrimedEdges_subset_left s.W s.h k s.hτ s.longest s.hp s.P
    s.hqMode s.Tpath s.hfin s.hleft ⟨a.1, rfl⟩

/-- Helper toward Lemma 5.5: the finite prefix adds no hatted edge to the
left side; hatted membership reflects exactly, also for positive indices. -/
theorem LPlusSidePresentationSourceWitness.hattedEdge_mem_actual_iff
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k) (e : ℕ) :
    boundaryGluingHatEdgeMap s.W s.h k s.hτ e ∈
        (m0GeodesicSide s.hp s.P .left).edges ↔
      e ∈ (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode).edges := by
  rw [(boundaryGluing_nonneg_side_identities s.W s.h k s.hτ s.longest s.hp s.P
    s.hqMode s.Tpath s.hfin s.hleft hk).2]
  have reflect (he : boundaryGluingHatEdgeMap s.W s.h k s.hτ e ∈
      boundaryGluingLeftHatEdges s.W s.h k s.hτ
        (if s.longest then XDP.ldp else XDP.sdp) s.hqMode) :
      e ∈ (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode).edges := by
    obtain ⟨a, ha, hae⟩ := he
    exact boundaryGluingHatEdgeMap_injective s.W s.h k s.hτ hae ▸ ha
  constructor
  · rintro ((hp | hh) | hp)
    · have hm : boundaryGluingHatEdgeMap s.W s.h k s.hτ e ∈
          boundaryGluingPrefixMinusEdges s.W s.h k ∩
            Set.range (boundaryGluingHatEdgeMap s.W s.h k s.hτ) := ⟨hp, e, rfl⟩
      rw [boundaryGluingPrefixMinusEdges_inter_hatRange s.W s.h k s.hτ hk] at hm
      exact hm.elim
    · exact reflect hh
    · have hb : boundaryGluingHatEdgeMap s.W s.h k s.hτ e ∈
          boundaryGluingBetaEdges s.W s.h k s.hτ := by
        rw [← boundaryGluingPrimedEdges_inter_hatRange s.W s.h k s.hτ s.hfin]
        exact ⟨hp, e, rfl⟩
      exact reflect (boundaryGluingBetaEdges_subset_leftHatEdges s.W s.h k s.hτ
        (if s.longest then XDP.ldp else XDP.sdp) s.hqMode hb)
  · intro he
    exact Or.inl (Or.inr ⟨e, he, rfl⟩)

/-- Helper toward Lemma 5.5: a hatted creation-dart seed bordering an
actual retained face forces the entire hatted triangle to be retained. -/
theorem LPlusSidePresentationSourceWitness.hattedTriangle_retained_of_actual_faceNext
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k)
    (j : TriangleCreationTime (hatCodes (boundaryGluingFutureStream s.W s.h k) s.hτ))
    (a e : ℕ × Bool)
    (ha : a ∈ stageTriangleDartList _ j)
    (hde : (m0GeodesicSide s.hp s.P .left).faceNext
      (boundaryGluingHatEdgeMap s.W s.h k s.hτ a.1, a.2) e) :
    ∀ c ∈ stageTriangleDartList _ j,
      c.1 ∈ (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode).edges := by
  let U := boundaryGluingFutureStream s.W s.h k
  let z := hatCodes U s.hτ
  let EH := boundaryGluingHatEdgeMap s.W s.h k s.hτ
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index z j
  let T : HatLocalTri U s.hτ :=
    ⟨stageTriangleRecord z j, j.val + 1, hi ▸ List.get_mem _ i⟩
  obtain ⟨F, hFR, hb⟩ :=
    boundaryGluing_hatTriangle_gluedFace s.W s.h k s.hτ s.H s.hp s.hfin T
  have border (c : ℕ × Bool) (hc : c ∈ stageTriangleDartList z j) :
      (WholePlanePastGlueDrawing.glueDrawing s.W s.h s.hp s.H).dartBorders
        (wholePlaneDartι s.W 0 (EH c.1, c.2)) F :=
    hb c ((rMinusWhole_creation_oriented_mem z j c).mpr hc)
  obtain ⟨⟨G, haG, hG⟩, _⟩ := hde
  have hFG : F = G := by
    obtain ⟨δ₁, hδ₁, hw₁⟩ := border a ha
    obtain ⟨δ₂, hδ₂, hw₂⟩ := haG
    let t := min δ₁ δ₂ / 2
    have ht : 0 < t := half_pos (lt_min hδ₁ hδ₂)
    have ht₁ : t < δ₁ :=
      (half_lt_self (lt_min hδ₁ hδ₂)).trans_le (min_le_left _ _)
    have ht₂ : t < δ₂ :=
      (half_lt_self (lt_min hδ₁ hδ₂)).trans_le (min_le_right _ _)
    exact (WholePlanePastGlueDrawing.glueDrawing s.W s.h s.hp s.H).faces_eq_of_mem
      (hw₁ t t ht ht₁ ht ht₁) (hw₂ t t ht ht₂ ht ht₂)
  have hF : F.val ⊆ m0GeodesicSideOpenRegion s.hp s.P .left := by
    rw [hFG]
    exact hG
  intro c hc
  apply (s.hattedEdge_mem_actual_iff x k r hk c.1).mp
  by_cases hs : EH c.1 ∈ m0GeodesicEdges s.P
  · exact (m0GeodesicEdges_subset_both s.hp s.P hs).1
  · exact (boundaryGluing_sideEdges_iff_borderingFace s.W s.h k s.longest s.hp s.P hs
      c.2 F hFR (border c hc) .left).mpr hF

/-- Helper toward Lemma 5.5: a retained hatted face supplies a retained
run-zero creation triangle at its embedded first dart, for every index. -/
theorem LPlusSidePresentationSourceWitness.hatted_faceNext_actual_triangle
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r)
    (a b : LPlusHattedDart
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode))
    (hab : (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode).faceNext
      a.val b.val) :
    ∃ J : TriangleCreationTime (shiftedStream s.W 0),
      (boundaryGluingHatEdgeMap s.W s.h k s.hτ a.val.1, a.val.2) ∈
        stageTriangleDartList _ J ∧
      ∀ d ∈ stageTriangleDartList _ J,
        d.1 ∈ (m0GeodesicSide s.hp s.P .left).edges := by
  let U := boundaryGluingFutureStream s.W s.h k
  let z := hatCodes U s.hτ
  let EH := boundaryGluingHatEdgeMap s.W s.h k s.hτ
  have hc := boundaryGluing_decoded_stream s.W s.h k s.hτ
  change boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s.W)) = z at hc
  obtain ⟨⟨j, ha, hall⟩, _⟩ := hab
  let j' : TriangleCreationTime z := ⟨j.val, by rw [← hc]; exact j.property⟩
  have hlist : stageTriangleDartList _ j = stageTriangleDartList z j' := by
    simp only [stageTriangleDartList, stageTriangleDartTriple, j', hc]
  have ha' : a.val ∈ stageTriangleDartList z j' := hlist ▸ ha
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index z j'
  let T : HatLocalTri U s.hτ :=
    ⟨stageTriangleRecord z j', j'.val + 1, hi ▸ List.get_mem _ i⟩
  obtain ⟨G, hGR, hborder⟩ :=
    boundaryGluing_hatTriangle_gluedFace s.W s.h k s.hτ s.H s.hp s.hfin T
  have hb (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList z j') :
      (WholePlanePastGlueDrawing.glueDrawing s.W s.h s.hp s.H).dartBorders
        (wholePlaneDartι s.W 0 (EH d.1, d.2)) G :=
    hborder d ((rMinusWhole_creation_oriented_mem z j' d).mpr hd)
  let R := sourceAncestorPath (if s.longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩
  obtain ⟨d, hd, hoff⟩ := rMinusWhole_triangle_off_path _
    (sourceAncestor_finite_incidence (if s.longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime
      ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩) R j
  have hdz : d ∈ stageTriangleDartList z j' := hlist ▸ hd
  have hid := boundaryGluing_geodesicIdentification s.W s.h k s.hτ s.longest s.hqMode
    s.hp s.Tpath s.P s.hfin s.hleft
  have hoff' : EH d.1 ∉ m0GeodesicEdges s.P := by
    rintro ⟨n, hn⟩
    exact hoff ⟨n, boundaryGluingHatEdgeMap_injective s.W s.h k s.hτ ((hid n).symm.trans hn)⟩
  have heL : EH d.1 ∈ (m0GeodesicSide s.hp s.P .left).edges :=
    boundaryGluingLeftHatEdges_subset_left s.W s.h k s.hτ s.longest s.hp s.P s.hqMode
      s.Tpath s.hfin s.hleft ⟨d.1, hall d hd, rfl⟩
  have hG := (boundaryGluing_sideEdges_iff_borderingFace s.W s.h k s.longest s.hp s.P
    hoff' d.2 G hGR (hb d hdz) .left).mp heL
  exact lMinusActualFaceNext_triangle s.hp s.P _ _ ⟨⟨G, hb a.val ha', hG⟩, rfl⟩

/-- Helper toward Lemma 5.5: one common cell equivalence preserves all
relations, including retained triangles and every indexed exterior mark. -/
theorem lPlusSourceWitnessAligned_codeBlockCellEquiv4_all_relations
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let B := lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    let B' := lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
    ∃ F : GeometricSideCell B ≃ GeometricSideCell B',
      (∀ t ∈ ({TruncationRelation.vertex, .root, .incident, .opposite, .rotation, .target, .faceNext} ∪
          Set.range TruncationRelation.seam ∪ Set.range TruncationRelation.boundary : Set TruncationRelation),
        ∀ u v, geometricSideRelation B t u v ↔ geometricSideRelation B' t (F u) (F v)) ∧
      (∀ u v, geometricSideRelation B .oriented u v ↔
        geometricSideRelation B' .oriented (F u) (F v)) ∧
      ∃ qD : LPlusGluedDart s.longest s.hqMode s.hτ ≃
          LPlusGluedDart s'.longest s'.hqMode s'.hτ,
        (∀ a, F (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inr a)) =
          s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r' hk (.inr (qD a))) ∧
        (∀ a,
          (∃ J : TriangleCreationTime (shiftedStream s.W 0),
            (lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk a).val ∈
              stageTriangleDartList _ J ∧ ∀ d ∈ stageTriangleDartList _ J,
                d.1 ∈ (m0GeodesicSide s.hp s.P .left).edges) ↔
          (∃ J : TriangleCreationTime (shiftedStream s'.W 0),
            (lPlusGluedDartEquivNonneg s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
              (qD a)).val ∈ stageTriangleDartList _ J ∧ ∀ d ∈ stageTriangleDartList _ J,
                d.1 ∈ (m0GeodesicSide s'.hp s'.P .left).edges)) := by
  obtain ⟨fD, qV, qD, hqD, hroot, he, hop, hrot, hseam, hPD, hTD, ⟨phi, hHD⟩⟩ :=
    lPlusSourceWitnessAligned_endpointQuotient_rotation4_transport x k r r' s s' hk hr
  let E := s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk
  let E' := s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r' hk
  let Q := Equiv.sumCongr qV qD
  let F := E.symm.trans (Q.trans E')
  have hF (a) : F (E a) = E' (Q a) := by
    change E' (Q (E.symm (E a))) = E' (Q a)
    rw [E.symm_apply_apply]
  have go
      (r₁ r₂ : LPlusSidePresentation x)
      (s₁ : LPlusSourceWitnessAligned x k r₁)
      (s₂ : LPlusSourceWitnessAligned x k r₂) (hc : r₁.code = r₂.code)
      (q : LPlusGluedDart s₁.longest s₁.hqMode s₁.hτ ≃
        LPlusGluedDart s₂.longest s₂.hqMode s₂.hτ)
      (hP : ∀ p : LPlusPrefixDart s₁.W s₁.h k,
        ∃ p' : LPlusPrefixDart s₂.W s₂.h k,
          q ⟦Sum.inl p⟧ = ⟦Sum.inl p'⟧ ∧ p'.val = p.val)
      (hT : ∀ a : LPlusPrimedDart,
        q ⟦Sum.inr (Sum.inl a)⟧ = ⟦Sum.inr (Sum.inl a)⟧)
      (φ : GeometricSideMarkedIso
        (lPlusHattedSide (W := s₁.W) (h := s₁.h) (k := k) s₁.longest s₁.hqMode)
        (lPlusHattedSide (W := s₂.W) (h := s₂.h) (k := k) s₂.longest s₂.hqMode))
      (hH : ∀ a, q ⟦Sum.inr (Sum.inr a)⟧ =
        ⟦Sum.inr (Sum.inr (lMinusMarkedDartMap φ a))⟧)
      (a : LPlusGluedDart s₁.longest s₁.hqMode s₁.hτ)
      (htri : ∃ J : TriangleCreationTime (shiftedStream s₁.W 0),
        (lPlusGluedDartEquivNonneg s₁.hτ s₁.hp s₁.P s₁.hqMode s₁.Tpath
          s₁.hfin s₁.hleft hk a).val ∈ stageTriangleDartList _ J ∧
        ∀ d ∈ stageTriangleDartList _ J,
          d.1 ∈ (m0GeodesicSide s₁.hp s₁.P .left).edges) :
      ∃ J : TriangleCreationTime (shiftedStream s₂.W 0),
        (lPlusGluedDartEquivNonneg s₂.hτ s₂.hp s₂.P s₂.hqMode s₂.Tpath
          s₂.hfin s₂.hleft hk (q a)).val ∈ stageTriangleDartList _ J ∧
        ∀ d ∈ stageTriangleDartList _ J,
          d.1 ∈ (m0GeodesicSide s₂.hp s₂.P .left).edges := by
    let D₁ := lPlusGluedDartEquivNonneg s₁.hτ s₁.hp s₁.P s₁.hqMode s₁.Tpath
      s₁.hfin s₁.hleft hk
    let D₂ := lPlusGluedDartEquivNonneg s₂.hτ s₂.hp s₂.P s₂.hqMode s₂.Tpath
      s₂.hfin s₂.hleft hk
    obtain ⟨J, ha, hall⟩ := htri
    have hface : (m0GeodesicSide s₁.hp s₁.P .left).faceNext (D₁ a).val
        (kmswInfFaceSucc (shiftedStream s₁.W 0) (s₁.H.1 0) (D₁ a).val) := by
      obtain ⟨G, hG, hb⟩ := lMinusRunZeroCreationTriangle_retained s₁.hp s₁.P J hall
      exact ⟨⟨G, hb _ ha, hG⟩, rfl⟩
    rcases s₁.toLPlusSidePresentationSourceWitness.creationDart_prefix_or_future_block
        x k r₁ J (D₁ a).val ha with hJ | ⟨b, j, hb, hj⟩ | ⟨b, j, hb, hj⟩
    · have hprev := lPlus_prefix_creationTime_lt_previous _ s₁.h k hk J hJ
      have hkpos : 0 < k := by
        by_contra hn
        have hk0 : k = 0 := by omega
        subst k
        rw [boundaryHitTime_zero] at hJ
        omega
      let p : LPlusPrefixDart s₁.W s₁.h k := ⟨(D₁ a).val, by
        rw [lPlusPrefixMinusEdges_eq_previousStage hkpos]
        exact stageTriangleDartList_lt _ _ J hprev _ ha⟩
      have hap : a = ⟦Sum.inl p⟧ := D₁.injective (Subtype.ext rfl)
      obtain ⟨p', hp', hpval⟩ := hP p
      obtain ⟨J', _, hlist, _, hret⟩ :=
        lPlusSourceWitnessAligned_prefix_retained_creationTriangle_transport
          x k r₁ r₂ s₁ s₂ hk hc J hJ
      refine ⟨J', ?_, hret⟩
      rw [hap, hp']
      change p'.val ∈ _
      rw [hpval, ← hlist]
      exact ha
    · have hab : a = ⟦Sum.inr (Sum.inl b)⟧ := D₁.injective (Subtype.ext hb.symm)
      have hcode := lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq
        x k r₁ r₂ s₁ s₂ hc
      let j' : TriangleCreationTime
          (primedCode (primedSimInput (boundaryGluingFutureStream s₂.W s₂.h k)) s₂.hτ) :=
        ⟨j.val, by rw [← hcode]; exact j.property⟩
      have hlist : stageTriangleDartList _ j = stageTriangleDartList _ j' := by
        simp only [stageTriangleDartList, stageTriangleDartTriple, j', hcode]
      obtain ⟨J', hm, hret⟩ :=
        s₂.toLPlusSidePresentationSourceWitness.primed_creationTriangle_retained x k r₂ j'
      refine ⟨J', ?_, hret⟩
      rw [hab, hT]
      exact (hm _).mpr ⟨b, hlist ▸ hj, rfl⟩
    · have hactual : (m0GeodesicSide s₁.hp s₁.P .left).faceNext
          (boundaryGluingHatEdgeMap s₁.W s₁.h k s₁.hτ b.1, b.2)
          (kmswInfFaceSucc (shiftedStream s₁.W 0) (s₁.H.1 0) (D₁ a).val) := hb ▸ hface
      have hret :=
        s₁.toLPlusSidePresentationSourceWitness.hattedTriangle_retained_of_actual_faceNext
          x k r₁ hk j b _ hj hactual
      let z := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s₁.W))
      have hstream := boundaryGluing_decoded_stream s₁.W s₁.h k s₁.hτ
      let j' : TriangleCreationTime z := ⟨j.val, by
        change boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s₁.W)) j.val = 0 ∨
          boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s₁.W)) j.val = 1
        rw [hstream]
        exact j.property⟩
      have hlist : stageTriangleDartList _ j = stageTriangleDartList z j' := by
        simp only [stageTriangleDartList, stageTriangleDartTriple, j', z, hstream]
      let M := lPlusHattedSide (W := s₁.W) (h := s₁.h) (k := k) s₁.longest s₁.hqMode
      let bM : LPlusHattedDart M := ⟨b, hret b hj⟩
      let c := kmswInfFaceSucc z (sourceAncestor_finite_incidence
        (if s₁.longest then XDP.ldp else XDP.sdp) renewalTime
        renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k s₁.W, s₁.hqMode⟩) b
      have hcj : c ∈ stageTriangleDartList z j' :=
        rMinusWhole_triangle_succ_mem z _ j' b (hlist ▸ hj)
      let cM : LPlusHattedDart M := ⟨c, hret c (hlist.symm ▸ hcj)⟩
      have hbc : M.faceNext bM.val cM.val :=
        ⟨⟨j', hlist ▸ hj, fun d hd => hret d (hlist.symm ▸ hd)⟩, rfl⟩
      have hbc' := (φ.relation_iff .faceNext (.inr bM) (.inr cM)).mp hbc
      rw [lMinusMarkedDartMap_cell, lMinusMarkedDartMap_cell] at hbc'
      obtain ⟨J', hb', hret'⟩ :=
        s₂.toLPlusSidePresentationSourceWitness.hatted_faceNext_actual_triangle x k r₂ _ _ hbc'
      have hab : a = ⟦Sum.inr (Sum.inr bM)⟧ := D₁.injective (Subtype.ext hb.symm)
      refine ⟨J', ?_, hret'⟩
      rw [hab, hH]
      exact hb'
  have hP (p : LPlusPrefixDart s.W s.h k) :
      ∃ p' : LPlusPrefixDart s'.W s'.h k,
        qD ⟦Sum.inl p⟧ = ⟦Sum.inl p'⟧ ∧ p'.val = p.val := by
    obtain ⟨p', hp', hv⟩ := hPD p
    exact ⟨p', (hqD _).trans (congrArg Quotient.mk'' hp'), hv⟩
  have hT (a : LPlusPrimedDart) :
      qD ⟦Sum.inr (Sum.inl a)⟧ = ⟦Sum.inr (Sum.inl a)⟧ := by rw [hqD, hTD]
  have hH (a) : qD ⟦Sum.inr (Sum.inr a)⟧ =
      ⟦Sum.inr (Sum.inr (lMinusMarkedDartMap phi a))⟧ := by
    obtain ⟨a', ha', hv⟩ := hHD a
    have hv' : a' = lMinusMarkedDartMap phi a :=
      Sum.inr.inj (hv.symm.trans (lMinusMarkedDartMap_cell phi a))
    rw [hqD, ha', hv']
  have hPinv (p' : LPlusPrefixDart s'.W s'.h k) :
      ∃ p : LPlusPrefixDart s.W s.h k,
        qD.symm ⟦Sum.inl p'⟧ = ⟦Sum.inl p⟧ ∧ p.val = p'.val := by
    have hpref := lPlusSourceWitnessAligned_prefixEdges_eq_of_presentation_codes_eq
      x k r r' s s' hk hr
    let p : LPlusPrefixDart s.W s.h k := ⟨p'.val, by rw [hpref]; exact p'.property⟩
    obtain ⟨p'', hp'', hv⟩ := hP p
    have hpp : p'' = p' := Subtype.ext hv
    refine ⟨p, ?_, rfl⟩
    rw [← hpp, ← hp'', Equiv.symm_apply_apply]
  have hTinv (a : LPlusPrimedDart) :
      qD.symm ⟦Sum.inr (Sum.inl a)⟧ = ⟦Sum.inr (Sum.inl a)⟧ := by
    rw [← hT a, Equiv.symm_apply_apply]
  have hHinv (a) : qD.symm ⟦Sum.inr (Sum.inr a)⟧ =
      ⟦Sum.inr (Sum.inr (lMinusMarkedDartMap (GeometricSideMarkedIso.symm phi) a))⟧ := by
    have ha : lMinusMarkedDartMap phi (lMinusMarkedDartMap (GeometricSideMarkedIso.symm phi) a) = a :=
      lMinusMarkedDartMap_symm (GeometricSideMarkedIso.symm phi) a
    apply qD.injective
    rw [Equiv.apply_symm_apply, hH, ha]
  have htri (a) :
      (∃ J : TriangleCreationTime (shiftedStream s.W 0),
        (lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk a).val ∈
          stageTriangleDartList _ J ∧ ∀ d ∈ stageTriangleDartList _ J,
            d.1 ∈ (m0GeodesicSide s.hp s.P .left).edges) ↔
      (∃ J : TriangleCreationTime (shiftedStream s'.W 0),
        (lPlusGluedDartEquivNonneg s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
          (qD a)).val ∈ stageTriangleDartList _ J ∧ ∀ d ∈ stageTriangleDartList _ J,
            d.1 ∈ (m0GeodesicSide s'.hp s'.P .left).edges) := by
    constructor
    · exact go r r' s s' hr qD hP hT phi hH a
    · intro ha
      have hh := go r' r s' s hr.symm qD.symm hPinv hTinv (GeometricSideMarkedIso.symm phi) hHinv (qD a) ha
      simpa only [Equiv.symm_apply_apply] using hh
  have hface (a b) : geometricSideRelation _ .faceNext (E (.inr a)) (E (.inr b)) ↔
      geometricSideRelation _ .faceNext (E' (.inr (qD a))) (E' (.inr (qD b))) := by
    have h₁ := s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_faceNext_iff_triangle
      x k r hk a b
    have h₂ := s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_faceNext_iff_triangle
      x k r' hk (qD a) (qD b)
    dsimp only at h₁ h₂
    rw [h₁, h₂, htri a, ← hrot, ← hop, qD.injective.eq_iff]
  refine ⟨F, ?_, ?_, qD, ?_, htri⟩
  · intro t ht u v
    obtain ⟨a, rfl⟩ := E.surjective u
    obtain ⟨b, rfl⟩ := E.surjective v
    rw [hF, hF]
    rcases ht with (ht | ⟨i, rfl⟩) | ⟨i, rfl⟩
    · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_vertex_iff,
          s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_vertex_iff]
        cases a <;> rfl
      · rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_root_iff,
          s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_root_iff]
        have hQ : Q (.inl ⟦Sum.inr (Sum.inl 1)⟧) = .inl ⟦Sum.inr (Sum.inl 1)⟧ :=
          congrArg Sum.inl hroot
        rw [← hQ, Q.injective.eq_iff]
      · cases a with
        | inl a => rfl
        | inr a =>
          cases b with
          | inr b => rfl
          | inl b =>
            induction a using Quotient.inductionOn with
            | h a =>
              change geometricSideRelation _ .incident (E (.inr ⟦a⟧)) (E (.inl b)) ↔
                geometricSideRelation _ .incident (E' (.inr (qD ⟦a⟧))) (E' (.inl (qV b)))
              rw [hqD,
                s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_incident_mk_iff,
                s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_incident_mk_iff,
                ← he, qV.injective.eq_iff]
      · cases a with
        | inl a => rfl
        | inr a =>
          cases b with
          | inl b => rfl
          | inr b =>
            change geometricSideRelation _ .opposite (E (.inr a)) (E (.inr b)) ↔
              geometricSideRelation _ .opposite (E' (.inr (qD a))) (E' (.inr (qD b)))
            rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_opposite_iff,
              s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_opposite_iff,
              ← hop, qD.injective.eq_iff]
    
      · cases a with
        | inl a => rfl
        | inr a =>
          cases b with
          | inl b => rfl
          | inr b =>
            change geometricSideRelation _ .rotation (E (.inr a)) (E (.inr b)) ↔
              geometricSideRelation _ .rotation (E' (.inr (qD a))) (E' (.inr (qD b)))
            rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_rotation_iff,
              s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_rotation_iff,
              ← hrot, qD.injective.eq_iff]
      · cases a <;> cases b <;> rfl
      · cases a with
        | inl a => rfl
        | inr a =>
          cases b with
          | inl b => rfl
          | inr b => exact hface a b
    · cases a with
      | inl a => rfl
      | inr a =>
        change geometricSideRelation _ (.seam i) (E (.inr a)) (E b) ↔
          geometricSideRelation _ (.seam i) (E' (.inr (qD a))) (E' (Q b))
        rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_seam_iff,
          s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_seam_iff,
          ← hseam, qD.injective.eq_iff]
    · cases a with
      | inl a => rfl
      | inr a =>
        let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
        let D' := lPlusGluedDartEquivNonneg s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
        have htransport (dB : LPlusGluedDart s.longest s.hqMode s.hτ)
            (dB' : LPlusGluedDart s'.longest s'.hqMode s'.hτ)
            (hq : qD dB = dB')
            (hb : (D dB).val = m0GeodesicBoundaryDart (shiftedStream s.W 0) s.h k .left i)
            (hb' : (D' dB').val = m0GeodesicBoundaryDart (shiftedStream s'.W 0) s'.h k .left i) :
            geometricSideRelation _ (.boundary i) (E (.inr a)) (E b) ↔
              geometricSideRelation _ (.boundary i) (E' (.inr (qD a))) (E' (Q b)) := by
          change m0GeodesicBoundaryDart (shiftedStream s.W 0) s.h k .left i = (D a).val ↔
            m0GeodesicBoundaryDart (shiftedStream s'.W 0) s'.h k .left i = (D' (qD a)).val
          rw [← hb, ← hb']
          constructor
          · intro hh
            have hd : dB = a := D.injective (Subtype.ext hh)
            exact congrArg (fun d => (D' d).val) (hq.symm.trans (congrArg qD hd))
          · intro hh
            have hd : dB' = qD a := D'.injective (Subtype.ext hh)
            exact congrArg (fun d => (D d).val) (qD.injective (hq.trans hd))
        rcases lPlusSourceWitnessAligned_boundary_representatives x k r r' s s' hk hr i with
          ⟨p, p', hval, hp, hp'⟩ | ⟨p, hp, hp'⟩
        · obtain ⟨p'', hpp, hppval⟩ := hPD p
          have hpp' : p'' = p' := Subtype.ext (hppval.trans hval)
          apply htransport ⟦Sum.inl p⟧ ⟦Sum.inl p'⟧
          · rw [hqD, hpp, hpp']
          · exact hp
          · exact hp'
        · apply htransport ⟦Sum.inr (Sum.inl p)⟧ ⟦Sum.inr (Sum.inl p)⟧
          · rw [hqD, hTD]
          · exact hp
          · exact hp'
  · intro u v
    obtain ⟨a, rfl⟩ := E.surjective u
    obtain ⟨b, rfl⟩ := E.surjective v
    rw [hF, hF]
    cases a with
    | inl a => rfl
    | inr a =>
      induction a using Quotient.inductionOn with
      | h a =>
        change geometricSideRelation _ .oriented (E (.inr ⟦a⟧)) (E b) ↔
          geometricSideRelation _ .oriented (E' (.inr (qD ⟦a⟧))) (E' (Q b))
        rw [hqD]
        rcases a with a | (a | a)
        · obtain ⟨a', ha, hval⟩ := hPD a
          rw [ha]
          change (EdgePresent (shiftedStream s.W 0) a.val.1 ∧ a.val.2 = false) ↔
            (EdgePresent (shiftedStream s'.W 0) a'.val.1 ∧ a'.val.2 = false)
          rw [hval]
          exact and_congr
            (lPlusSourceWitnessAligned_prefixEdgePresent_iff x k r r' s s' hk hr a) Iff.rfl
        · rw [hTD]
          exact lPlusSourceWitnessAligned_codeBlockCellEquiv4_primed_oriented_iff
            x k r r' s s' hk hr a b (Q b)
        · obtain ⟨a', ha, hphi⟩ := hHD a
          rw [ha,
            s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_hatted_oriented_iff,
            s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_hatted_oriented_iff]
          have ho := phi.relation_iff .oriented (.inr a) (.inr a)
          rw [hphi] at ho
          have hp : a.val.1 ∈
              (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode).present := by
            change EdgePresent (boltzmannKMSWStream
              (pathCode (boundaryFutureHattedPath k s.W))) _
            rw [boundaryGluing_decoded_stream s.W s.h k s.hτ]
            exact hatCodes_edge_present _ s.hτ _
          have hp' : a'.val.1 ∈
              (lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode).present := by
            change EdgePresent (boltzmannKMSWStream
              (pathCode (boundaryFutureHattedPath k s'.W))) _
            rw [boundaryGluing_decoded_stream s'.W s'.h k s'.hτ]
            exact hatCodes_edge_present _ s'.hτ _
          change (_ ∧ a.val.2 = false) ↔ (_ ∧ a'.val.2 = false) at ho
          simpa only [hp, hp', true_and] using ho
  · intro a
    exact hF (.inr a)

/-- Helper toward Lemma 5.5: equal aligned presentation codes give one
cell equivalence preserving all marked whole-side relations. -/
theorem lPlusCodeBlockSide4_relationEquiv_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let B := lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    let B' := lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
    ∃ F : GeometricSideCell B ≃ GeometricSideCell B',
      ∀ (t : TruncationRelation) (u v : GeometricSideCell B),
        geometricSideRelation B t u v ↔ geometricSideRelation B' t (F u) (F v) := by
  obtain ⟨F, htags, horiented, _⟩ :=
    lPlusSourceWitnessAligned_codeBlockCellEquiv4_all_relations x k r r' s s' hk hr
  refine ⟨F, ?_⟩
  intro t u v
  cases t <;> first
    | exact horiented u v
    | exact htags _ (by simp) u v

/-- Helper toward Lemma 5.5: the full aligned marked comparison, including
the finite prefix and retained face succession at every nonnegative index. -/
theorem lPlusCodeBlockSide4_markedIso_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    Nonempty (GeometricSideMarkedIso
      (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
      (lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk)) := by
  obtain ⟨F, hF⟩ :=
    lPlusCodeBlockSide4_relationEquiv_of_presentation_codes_eq x k r r' s s' hk hr
  exact ⟨⟨F, hF⟩⟩



theorem lPlusCodeBlockSide4_class_eq_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    geometricSideClass
      (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) =
    geometricSideClass
      (lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk) := by
  exact (geometricSideClass_eq_iff _ _).mpr
    (lPlusCodeBlockSide4_markedIso_of_presentation_codes_eq x k r r' s s' hk hr)

/-- Helper toward Lemma 5.5: the common marked cell equivalence maps all
three oriented darts of every retained creation triangle into one retained
creation triangle of the other witness. The same map preserves every tag. -/
theorem lPlusSourceWitnessAligned_retained_creationTriangle_transport
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let B := lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    let B' := lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
    let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    let D' := lPlusGluedDartEquivNonneg s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
    ∃ (F : GeometricSideCell B ≃ GeometricSideCell B')
      (qD : LPlusGluedDart s.longest s.hqMode s.hτ ≃
        LPlusGluedDart s'.longest s'.hqMode s'.hτ),
      (∀ t u v, geometricSideRelation B t u v ↔ geometricSideRelation B' t (F u) (F v)) ∧
      (∀ a, F (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inr a)) =
        s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r' hk (.inr (qD a))) ∧
      (∀ J : TriangleCreationTime (shiftedStream s.W 0),
        (∀ d ∈ stageTriangleDartList _ J, d.1 ∈ (m0GeodesicSide s.hp s.P .left).edges) →
        ∃ J' : TriangleCreationTime (shiftedStream s'.W 0),
          (∀ d ∈ stageTriangleDartList _ J',
            d.1 ∈ (m0GeodesicSide s'.hp s'.P .left).edges) ∧
          ∀ a, (D a).val ∈ stageTriangleDartList _ J →
            (D' (qD a)).val ∈ stageTriangleDartList _ J') := by
  let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  let D' := lPlusGluedDartEquivNonneg s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
  let E := s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk
  let E' := s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r' hk
  obtain ⟨F, htags, horiented, qD, hF, _⟩ :=
    lPlusSourceWitnessAligned_codeBlockCellEquiv4_all_relations x k r r' s s' hk hr
  have hrel : ∀ t u v, geometricSideRelation _ t u v ↔
      geometricSideRelation _ t (F u) (F v) := by
    intro t u v
    cases t <;> first
      | exact horiented u v
      | exact htags _ (by simp) u v
  refine ⟨F, qD, hrel, hF, ?_⟩
  intro J hall
  let t := stageTriangleDartTriple (shiftedStream s.W 0) J
  have ht₀ : t.1 ∈ stageTriangleDartList (shiftedStream s.W 0) J := by
    simp only [stageTriangleDartList, t, List.mem_cons, true_or]
  have ht₁ : t.2.1 ∈ stageTriangleDartList (shiftedStream s.W 0) J := by
    simp only [stageTriangleDartList, t, List.mem_cons, true_or, or_true]
  have ht₂ : t.2.2 ∈ stageTriangleDartList (shiftedStream s.W 0) J := by
    simp only [stageTriangleDartList, t, List.mem_cons, true_or, or_true]
  let a₀ := D.symm ⟨t.1, hall _ ht₀⟩
  let a₁ := D.symm ⟨t.2.1, hall _ ht₁⟩
  let a₂ := D.symm ⟨t.2.2, hall _ ht₂⟩
  have ha₀ : (D a₀).val = t.1 := congrArg Subtype.val (D.apply_symm_apply _)
  have ha₁ : (D a₁).val = t.2.1 := congrArg Subtype.val (D.apply_symm_apply _)
  have ha₂ : (D a₂).val = t.2.2 := congrArg Subtype.val (D.apply_symm_apply _)
  obtain ⟨G, hG, hb⟩ := lMinusRunZeroCreationTriangle_retained s.hp s.P J hall
  have hcycle := kmswInfFaceSucc_stageTriangle_cycle (shiftedStream s.W 0) (s.H.1 0) J
  have mapped (a b : LPlusGluedDart s.longest s.hqMode s.hτ)
      (hab : (m0GeodesicSide s.hp s.P .left).faceNext (D a).val (D b).val) :
      (m0GeodesicSide s'.hp s'.P .left).faceNext (D' (qD a)).val (D' (qD b)).val := by
    have hh := (hrel .faceNext (E (.inr a)) (E (.inr b))).mp hab
    rw [hF, hF] at hh
    exact hh
  have h₀₁ := mapped a₀ a₁ (by
    rw [ha₀, ha₁]
    exact ⟨⟨G, hb _ ht₀, hG⟩, hcycle.1⟩)
  have h₁₂ := mapped a₁ a₂ (by
    rw [ha₁, ha₂]
    exact ⟨⟨G, hb _ ht₁, hG⟩, hcycle.2.1⟩)
  obtain ⟨J', h₀, hret⟩ := lMinusActualFaceNext_triangle s'.hp s'.P _ _ h₀₁
  have h₁ : (D' (qD a₁)).val ∈ stageTriangleDartList (shiftedStream s'.W 0) J' := by
    rw [← h₀₁.2]
    exact rMinusWhole_triangle_succ_mem _ (s'.H.1 0) J' _ h₀
  have h₂ : (D' (qD a₂)).val ∈ stageTriangleDartList (shiftedStream s'.W 0) J' := by
    rw [← h₁₂.2]
    exact rMinusWhole_triangle_succ_mem _ (s'.H.1 0) J' _ h₁
  refine ⟨J', hret, ?_⟩
  intro a ha
  change (D a).val ∈ [t.1, t.2.1, t.2.2] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with ha | ha | ha
  · have he : a = a₀ := D.injective (Subtype.ext (ha.trans ha₀.symm))
    exact he ▸ h₀
  · have he : a = a₁ := D.injective (Subtype.ext (ha.trans ha₁.symm))
    exact he ▸ h₁
  · have he : a = a₂ := D.injective (Subtype.ext (ha.trans ha₂.symm))
    exact he ▸ h₂














end DirectedDistances.PaperProofs.Section5

