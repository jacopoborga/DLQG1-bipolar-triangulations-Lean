/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceRightSliceUpdates2

/-! and integration remain with the sole coordinator. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open Set Metric
open scoped Classical Topology

/-- Helper toward Lemma 5.6: the two finite seed families are forward
next-prefix left faces and reverse preceding-prefix right faces. -/
@[expose] def rightSliceSeed3 (M : GeometricSideSubmap)
    (d ds : ℕ → GeometricSideCell M) (a b : ℕ) (c : GeometricSideCell M) : Prop :=
  ((∃ n, n < b ∧ c = d n) ∨
    ∃ n, n < a ∧ geometricSideRelation M .opposite (ds n) c) ∧
    ∃ e, geometricSideRelation M .faceNext c e

/-- Helper toward Lemma 5.6: both seed families transport using only
indexed prefix cells and the complete marked relations. -/
theorem rightSliceSeed3_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (d ds : ℕ → GeometricSideCell M)
    (a b : ℕ) (c : GeometricSideCell M) :
    rightSliceSeed3 M d ds a b c ↔
      rightSliceSeed3 N (I.equiv ∘ d) (I.equiv ∘ ds) a b (I.equiv c) := by
  apply and_congr
  · exact or_congr (exists_congr fun n => and_congr Iff.rfl
      ⟨congrArg I.equiv, fun h => I.equiv.injective h⟩)
      (exists_congr fun n => and_congr Iff.rfl (I.relation_iff _ _ _))
  · constructor
    · rintro ⟨e, he⟩
      exact ⟨I.equiv e, (I.relation_iff _ _ _).1 he⟩
    · rintro ⟨e, he⟩
      exact ⟨I.equiv.symm e, (I.relation_iff _ _ _).2
        (by simpa only [Equiv.apply_symm_apply] using he)⟩

/-- Helper toward Lemma 5.6: both finite prefixes and finite slit chains
from either seed family, with strict vertex and weak edge tails removed. -/
@[expose] def rightSliceKeep3 (M : GeometricSideSubmap)
    (v d vs ds : ℕ → GeometricSideCell M) (a b : ℕ) : Set (GeometricSideCell M) :=
  {c | (c ∈ rightSlicePrecedingSegment M vs ds a ∨
      c ∈ rightSlicePrecedingSegment M v d b ∨
      ∃ q, rightSliceSeed3 M d ds a b q ∧
        Relation.ReflTransGen (geometricSide_slit_step M v d) q c) ∧
    c ∉ geometricSideRayDeletedTailCells M vs ds a ∪
      geometricSideRayDeletedTailCells M v d b}

/-- Helper toward Lemma 5.6: the entire two-prefix candidate transports
unconditionally under a marked isomorphism mapping the four streams. -/
theorem rightSliceKeep3_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d vs ds : ℕ → GeometricSideCell M)
    (a b : ℕ) (c : GeometricSideCell M) :
    c ∈ rightSliceKeep3 M v d vs ds a b ↔
      I.equiv c ∈ rightSliceKeep3 N (I.equiv ∘ v) (I.equiv ∘ d)
        (I.equiv ∘ vs) (I.equiv ∘ ds) a b := by
  apply and_congr
  · apply or_congr (rightSlicePrecedingSegment_map_iff I vs ds a c)
    apply or_congr (rightSlicePrecedingSegment_map_iff I v d b c)
    constructor
    · rintro ⟨q, hq, hqc⟩
      exact ⟨I.equiv q, (rightSliceSeed3_map_iff I d ds a b q).1 hq,
        (geometricSide_slit_reaches_map_iff I v d q c).1 hqc⟩
    · rintro ⟨q, hq, hqc⟩
      refine ⟨I.equiv.symm q, ?_, ?_⟩
      · apply (rightSliceSeed3_map_iff I d ds a b _).2
        simpa only [Equiv.apply_symm_apply] using hq
      · apply (geometricSide_slit_reaches_map_iff I v d _ c).2
        simpa only [Equiv.apply_symm_apply] using hqc
  · exact not_congr (or_congr
      (geometricSideRayDeletedTailCells_map_iff I vs ds a c)
      (geometricSideRayDeletedTailCells_map_iff I v d b c))

/-- Helper toward Lemma 5.6: realization of the corrected restriction at
its jointly least aligned old-seam and next-ray offsets. The old offset is
a and the next offset is b, reversing the intrinsic agreement API's order. -/
@[expose] def rightSliceRealizes3 (x : XDP) (M N : GeometricSideSubmap) : Prop :=
  ∃ v d vs ds a b, rightReconstructionRay2 (geoSliceRightLongest x) M v d ∧
    rightReconstructionSeam2 M vs ds ∧ geometricSideRaySeamAgreement M d b a ∧
    (∀ a' b', geometricSideRaySeamAgreement M d b' a' → a ≤ a' ∧ b ≤ b') ∧
    rightRestrictionRealizes2 M (rightSliceKeep3 M v d vs ds a b)
      (rightSliceRelation2 M v d (rightSliceKeep3 M v d vs ds a b)) N

/-- Helper toward Lemma 5.6: corrected slice realization transports with
no exhaustion or source-realization premise. -/
theorem rightSliceRealizes3_map {M M' N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M M') (x : XDP)
    (h : rightSliceRealizes3 x M N) : rightSliceRealizes3 x M' N := by
  obtain ⟨v, d, vs, ds, a, b, hr, hs, ht, hm, hN⟩ := h
  refine ⟨I.equiv ∘ v, I.equiv ∘ d, I.equiv ∘ vs, I.equiv ∘ ds, a, b,
    rightReconstructionRay2_map I _ hr, rightReconstructionSeam2_map I hs,
    (geometricSideRaySeamAgreement_iff I d b a).1 ht,
    fun a' b' ht' => hm a' b' ((geometricSideRaySeamAgreement_iff I d b' a').2 ht'), ?_⟩
  exact rightRestrictionRealizes2_transport I (rightSliceKeep3_map_iff I v d vs ds a b)
    (rightSliceRelation2_map_iff I v d _ _ (rightSliceKeep3_map_iff I v d vs ds a b)) hN

/-- Helper toward Lemma 5.6: corrected realizations have a unique marked
class; uniqueness precedes the choice in the optional reader. -/
theorem rightSliceRealizes3_class_unique {x : XDP} {M N N' : GeometricSideSubmap}
    (h : rightSliceRealizes3 x M N) (h' : rightSliceRealizes3 x M N') :
    geometricSideClass N = geometricSideClass N' := by
  obtain ⟨v, d, vs, ds, a, b, hr, hs, ht, hm, hN⟩ := h
  obtain ⟨v', d', vs', ds', a', b', hr', hs', ht', hm', hN'⟩ := h'
  obtain ⟨rfl, rfl⟩ := hr.2 v' d' hr'.1
  obtain ⟨rfl, rfl⟩ := rightReconstructionSeam2_unique hs' hs
  have ha : a' = a := Nat.le_antisymm (hm' a b ht).1 (hm a' b' ht').1
  have hb : b' = b := Nat.le_antisymm (hm' a b ht).2 (hm a' b' ht').2
  subst a'
  subst b'
  exact rightRestrictionRealizes2_class_unique hN hN'

/-- Helper toward Lemma 5.6: the corrected optional reader chooses the
unique marked class of the complete intrinsic restriction. Nonrealizable
restrictions return none; source realizability is not asserted here. -/
@[expose] noncomputable def rightOneSlice3 (x : XDP) (M : GeometricSideSubmap) :
    Option GeometricSideClass :=
  if h : ∃ N, rightSliceRealizes3 x M N then some (geometricSideClass h.choose) else none

/-- Helper toward Lemma 5.6: the corrected reader returns the class of
every complete realization of its intrinsic restriction. -/
theorem rightOneSlice3_eq_of_realizes {x : XDP} {M N : GeometricSideSubmap}
    (h : rightSliceRealizes3 x M N) :
    rightOneSlice3 x M = some (geometricSideClass N) := by
  have hex : ∃ N, rightSliceRealizes3 x M N := ⟨N, h⟩
  rw [rightOneSlice3, dite_eq_left hex]
  exact congrArg some (rightSliceRealizes3_class_unique hex.choose_spec h)

/-- Helper toward Lemma 5.6: the corrected reader is absent precisely
when its complete intrinsic restriction has no numbered realization. -/
theorem rightOneSlice3_eq_none_iff (x : XDP) (M : GeometricSideSubmap) :
    rightOneSlice3 x M = none ↔ ¬ ∃ N, rightSliceRealizes3 x M N := by
  unfold rightOneSlice3
  split_ifs with h <;> simp only [not_true_eq_false,
    not_false_eq_true, h]

/-- Helper toward Lemma 5.6: the corrected optional reader is invariant
under every marked-side isomorphism, including outside its realization domain. -/
theorem rightOneSlice3_markedIso {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (x : XDP) :
    rightOneSlice3 x M = rightOneSlice3 x N := by
  by_cases h : ∃ K, rightSliceRealizes3 x M K
  · obtain ⟨K, hK⟩ := h
    exact (rightOneSlice3_eq_of_realizes hK).trans
      (rightOneSlice3_eq_of_realizes (rightSliceRealizes3_map I x hK)).symm
  · have hn : ¬ ∃ K, rightSliceRealizes3 x N K := by
      rintro ⟨K, hK⟩
      exact h ⟨K, rightSliceRealizes3_map (GeometricSideMarkedIso.symm I) x hK⟩
    rw [(rightOneSlice3_eq_none_iff x M).2 h, (rightOneSlice3_eq_none_iff x N).2 hn]

/-- Helper toward Lemma 5.6: the corrected slice reader descends to
marked-isomorphism classes without an exhaustion assumption. -/
@[expose] noncomputable def oneR3 (x : XDP) :
    GeometricSideClass → Option GeometricSideClass :=
  Quotient.lift (rightOneSlice3 x)
    (fun _ _ h => h.elim fun I => rightOneSlice3_markedIso I x)

/-- Helper toward Lemma 5.6: the quotient reader evaluates on every
representative by the corrected intrinsic one-slice operation. -/
theorem oneR3_geometricSideClass (x : XDP) (M : GeometricSideSubmap) :
    oneR3 x (geometricSideClass M) = rightOneSlice3 x M := rfl

/-- Helper toward Lemma 5.6: the full graph of the corrected reader
characterizes its value by a realization of the specified intrinsic restriction. -/
theorem rightOneSlice3_eq_some_iff (x : XDP) (M : GeometricSideSubmap)
    (C : GeometricSideClass) :
    rightOneSlice3 x M = some C ↔
      ∃ N, rightSliceRealizes3 x M N ∧ geometricSideClass N = C := by
  constructor
  · intro h
    by_cases hex : ∃ N, rightSliceRealizes3 x M N
    · refine ⟨hex.choose, hex.choose_spec, ?_⟩
      rw [rightOneSlice3, dite_eq_left hex] at h
      exact Option.some.inj h
    · rw [(rightOneSlice3_eq_none_iff x M).2 hex] at h
      cases h
  · rintro ⟨N, hN, rfl⟩
    exact rightOneSlice3_eq_of_realizes hN


variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

section Source
variable (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hc : ∀ m : ℤ, ∃ a b : ℕ,
    M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
  (k : ℤ)
include T hleft

/-- Helper toward Lemma 5.6: an old prefix edge cannot belong to the
next ray, since a meeting of leftmost rays forces equality of their tails. -/
theorem m0GeodesicRightSide_old_prefix_off_next3 (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (n : ℕ) (hn : n < a) :
    (P (k - 1)).codePath.edge n ∉ m0GeodesicEdges (P k) := by
  rintro ⟨m, hm⟩
  have hi : ((P (k - 1)).codePath.initial n).1 = ((P k).codePath.initial m).1 := by
    apply (show Function.Injective (PresentVertex.id (w := shiftedStream W 0)) from
      fun ⟨i⟩ ⟨j⟩ hij => by cases hij; rfl)
    rw [← ((P (k - 1)).codePath.edge_outgoing_at_initial (shiftedStream W 0) n).2,
      ← ((P k).codePath.edge_outgoing_at_initial (shiftedStream W 0) m).2, hm]
  have hco := m0CutEdgeTailsCoalesce_of_meeting_of_leftmost hp
    (P (k - 1)) (P k) (T (k - 1)) (T k) (hleft (k - 1)) (hleft k)
    a b hab.1 n m hi
  exact (Nat.not_lt_of_ge (hab.2 n m hco).1) hn

/-- Helper toward Lemma 5.6: a reverse old-prefix face seed satisfies
the next-left oriented invariant, including when the next prefix is empty. -/
theorem m0GeodesicRightSide_old_seed_invariant3 (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (n : ℕ) (hn : n < a)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right))
    (hop : geometricSideRelation _ .opposite
      (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right n) c)
    (hsucc : ∃ e, geometricSideRelation _ .faceNext c e) :
    m0GeodesicRightSlitInvariant hp (P k) (P (k - 1)) .left c := by
  cases c with
  | inl c => exact False.elim hop
  | inr c =>
    obtain ⟨e, he⟩ := hsucc
    cases e with
    | inl e => exact False.elim he
    | inr e =>
      obtain ⟨⟨F, hb, hFR⟩, _⟩ := he
      have hFA : F.val ⊆ m0GeodesicAmbientRegion W H h := fun z hz => (hFR hz).1
      have hval : c.val = ((P (k - 1)).codePath.edge n, true) := hop.symm
      have hoff := m0GeodesicRightSide_old_prefix_off_next3 hp P T hleft k a b hab n hn
      have hmem := (m0CutGeodesicSlice_boundary_segments_mem
        (hp := hp) P T hleft k a b hab).2.1 n hn
      have hnext : c.val.1 ∈ m0GeodesicSideEdges hp (P k) .left := by
        rw [hval]
        exact hmem.1.2
      exact m0GeodesicRightSide_face_dart_invariant hp (P k) (P (k - 1)) .left c F hb
        ((boundaryGluing_sideEdges_iff_borderingFace W h k longest hp (P k)
          hoff true F hFA (by simpa only [hval] using hb) .left).mp (by
            change (P (k - 1)).codePath.edge n ∈ m0GeodesicSideEdges hp (P k) .left
            simpa only [hval] using hnext))


/-- Helper toward Lemma 5.6: dual steps between overlap faces transfer
to next-ray slit chains in the preceding right side, for either dart orientation. -/
theorem m0GeodesicRightSide_adjacent_overlap_slit_reaches3
    (F G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFL : F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right)
    (hGL : G.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left)
    (hGR : G.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges})
    (hd : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F)
    (he : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 e.val) G)
    (q : ℕ) (u v : Bool)
    (hu : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (q, u)) F)
    (hv : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 (q, v)) G) :
    Relation.ReflTransGen (geometricSide_slit_step _
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k)) (.inr d) (.inr e) := by
  by_cases huv : u = v
  · have hFG := (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders_face_unique
      (wholePlaneDartι W 0 (q, u)) F G hu (huv.symm ▸ hv)
    subst G
    exact m0GeodesicSide_common_face_slit_reaches hp (P (k - 1)) .right _ _ d e F hFR hd he
  · have hvu : v = !u := by cases u <;> cases v <;> simp_all only [Bool.not_false,
      Bool.not_true, not_true_eq_false]
    let qa : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges} :=
      ⟨(q, u), m0Geodesic_side_edge_of_bordering_face hp (P (k - 1)) .right
        (q, u) F hFR hu⟩
    have hoff : q ∉ m0GeodesicEdges (P k) := by
      rintro ⟨n, hn⟩
      have hFi := m0GeodesicRightSide_face_dart_invariant hp (P k) (P (k - 1)) .left
        qa F hu hFL
      let qb : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges} :=
        ⟨(q, v), qa.property⟩
      have hGi := m0GeodesicRightSide_face_dart_invariant hp (P k) (P (k - 1)) .left
        qb G hv hGL
      cases hb : u with
      | true => exact hFi.2 n (Prod.ext hn.symm hb)
      | false => exact hGi.2 n (Prod.ext hn.symm (hvu.trans (by rw [hb]; rfl)))
    exact m0GeodesicSide_adjacent_faces_slit_reaches hp (P (k - 1)) .right _ _ d e qa
      F G hFR hGR hd he hu (by simpa only [hvu] using hv)
      (fun hr => hoff ((m0GeodesicRightSide_ray_dart_iff hp P k
        (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k) qa).mp hr))

/-- Helper toward Lemma 5.6: any overlap-face dart is reached from one
of the finite seed families. The imported overlap chain uses the generic
open-preconnected clopen bridge; no connectivity premise is supplied here. -/
theorem m0GeodesicRightSide_overlap_face_reached3 (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFL : F.val ⊆ m0GeodesicSideOpenRegion hp (P k) .left)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp (P (k - 1)) .right)
    (d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges})
    (hd : (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
      (wholePlaneDartι W 0 d.val) F) :
    ∃ q, rightSliceSeed3 _ (m0GeodesicRightSideNextDarts hp P T hleft hc k)
        (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a b q ∧
      Relation.ReflTransGen (geometricSide_slit_step _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k)) q (.inr d) := by
  have hsub := m0CutGeodesicLeftSide_subset_of_adjacentCoalescence
    P T hleft hc (k - 1) k (by omega)
  have hcontain (n : ℕ) :
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈ (m0GeodesicSide hp (P k) .left).vertices := by
    constructor
    · exact fun z hz => hsub ((m0GeodesicEdges_subset_both hp (P (k - 1)) ⟨n, rfl⟩).1 hz)
    · have ht := m0Geodesic_initial_pos_mem_trace hp (P (k - 1)) n
      rw [← m0GeodesicSideRegion_inter hp (P (k - 1))] at ht
      exact hsub ht.1
  obtain ⟨G, n, hGL, hGR, hbG, hchain⟩ :=
    m0GeodesicLeftSide_overlap_face_chain_to_ray hp P T hleft k hcontain F hFL hFR
  have hn : n < a := by
    by_contra hna
    have han : a ≤ n := Nat.le_of_not_gt hna
    have hsame := wholePlaneEdgeι_injective W 0 (hab.1 (n - a))
    rw [Nat.add_sub_of_le han] at hsame
    have hnextR := m0Geodesic_reverse_seam_face_right hp (P k) (b + (n - a)) G
      (fun z hz => (hGR hz).1) (by simpa only [hsame] using hbG)
    obtain ⟨z, hz, heq⟩ := G.property
    have hzG : z ∈ G.val := heq ▸ mem_connectedComponentIn hz
    exact disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp (P k)) (hGL hzG) (hnextR hzG)
  revert d hd
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro d hd
    let q : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges} :=
      ⟨((P (k - 1)).codePath.edge n, true),
        (m0GeodesicEdges_subset_both hp (P (k - 1)) ⟨n, rfl⟩).2⟩
    exact ⟨.inr q, ⟨Or.inr ⟨n, hn, rfl⟩,
      m0GeodesicSide_bordering_face_has_successor hp (P (k - 1)) .right q G hGR hbG⟩,
      m0GeodesicSide_common_face_slit_reaches hp (P (k - 1)) .right _ _ q d G hGR hbG hd⟩
  | @head A B hAB _ ih =>
    intro d hd
    obtain ⟨hAL, hAR, hBL, hBR, e, _, u, v, hu, hv⟩ := hAB
    let db : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges} :=
      ⟨(e, v), m0Geodesic_side_edge_of_bordering_face hp (P (k - 1)) .right (e, v) B hBR hv⟩
    obtain ⟨q, hq, hqdb⟩ := ih hBL hBR db hv
    have hddb := m0GeodesicRightSide_adjacent_overlap_slit_reaches3 hp P T hleft hc k
      A B hAL hAR hBL hBR d db hd hv e u v hu hv
    exact ⟨q, hq, hqdb.trans (geometricSide_slit_reaches_reverse _ _ _ hddb)⟩


/-- Helper toward Lemma 5.6: every surviving overlap cell is in a finite
prefix or reached from a finite seed. Zero next offset is included. -/
theorem m0GeodesicRightSide_survivor_exhaustion3 (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right))
    (hmem : match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .left
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .left)
    (htail : c ∉ m0GeodesicRightSideDeletedTailCells hp P k a b) :
    c ∈ rightSliceKeep3 _
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k)
      (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
      (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a b := by
  have htail' := htail
  rw [m0GeodesicRightSideDeletedTailCells_eq hp P k
    (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k) a b] at htail'
  refine ⟨?_, htail'⟩
  by_cases hs : c ∈ rightSlicePrecedingSegment _
    (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
    (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a
  · exact Or.inl hs
  · apply Or.inr
    by_cases hv : geometricSide_ray_vertex _
      (m0GeodesicRightSideNextVertices hp P T hleft hc k) c
    · obtain ⟨n, hn⟩ := hv
      have hnle : n ≤ b := by
        by_contra hnb
        exact htail' (Or.inr (Or.inl ⟨n, Nat.lt_of_not_ge hnb, hn⟩))
      exact Or.inl (Or.inl ⟨n, hnle, hn⟩)
    · by_cases hd : geometricSide_ray_dart _
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) c
      · obtain ⟨n, hn⟩ := hd
        have hnlt : n < b := by
          by_contra hnb
          exact htail' (Or.inr (Or.inr ⟨n, Nat.le_of_not_gt hnb, hn⟩))
        exact Or.inl (Or.inr ⟨n, hnlt, hn⟩)
      · obtain ⟨F, d, hbF, hFL, hFR, hdc⟩ :=
          m0GeodesicRightSide_survivor_has_overlap_face hp P T hleft hc k a b
            c hmem htail hs hv hd
        obtain ⟨q, hq, hqd⟩ :=
          m0GeodesicRightSide_overlap_face_reached3 hp P T hleft hc k a b hab F hFL hFR d hbF
        exact Or.inr ⟨q, hq, hqd.trans hdc⟩

/-- Helper toward Lemma 5.6: every cell admitted by the two-seed
candidate belongs to the next closed left side. -/
theorem m0GeodesicRightSide_keep3_sound (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right))
    (hkeep : c ∈ rightSliceKeep3 _
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k)
      (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
      (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a b) :
    match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P k) .left
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P k) .left := by
  rcases hkeep.1 with hs | hs | ⟨q, hq, hqc⟩
  · have hm := rightSlicePrecedingSegment_source_mem_slice hp P T hleft k a b hab c hs
    cases c with
    | inl c => exact hm.1.2
    | inr c => exact hm.1.2
  · have hl : geometricSide_intrinsic_left _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) c := by
      rcases hs with ⟨n, _, hn⟩ | ⟨n, _, hn⟩
      · exact Or.inl ⟨n, hn⟩
      · exact Or.inr (Or.inl ⟨n, hn⟩)
    have hh := m0GeodesicRightSide_intrinsic_left_sound hp P k
      (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k) c hl
    cases c <;> exact hh
  · have hqi : m0GeodesicRightSlitInvariant hp (P k) (P (k - 1)) .left q := by
      rcases hq with ⟨⟨n, _, hn⟩ | ⟨n, hn, hop⟩, hsucc⟩
      · exact m0GeodesicRightSide_left_face_seed_invariant hp P k
          (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k) q ⟨n, hn, hsucc⟩
      · exact m0GeodesicRightSide_old_seed_invariant3 hp P T hleft k a b hab n hn q hop hsucc
    have hci := m0GeodesicRightSide_slit_reaches_invariant hp P k
      (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k) .left hqi hqc
    cases c with
    | inl c => exact hci
    | inr c => exact hci.1

/-- Helper toward Lemma 5.6: the two-seed candidate is precisely the
literal source slice image, with both vertex and dart endpoint conventions. -/
theorem m0CutGeodesicSlice_range_eq_keep3 (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    Set.range (m0CutGeodesicSliceRightCell hp P k a b hab) = rightSliceKeep3 _
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k)
      (m0GeodesicSideSeamVertexCell hp (P (k - 1)) .right)
      (m0GeodesicSideSeamDartCell hp (P (k - 1)) .right) a b := by
  ext c
  apply (m0CutGeodesicSliceRightCell_mem_range_iff hp P k a b hab c).trans
  apply (m0CutGeodesicSlice_mem_cell_iff_nextLeft_and_not_deletedTail hp P k a b hab c).trans
  constructor
  · rintro ⟨hm, ht⟩
    exact m0GeodesicRightSide_survivor_exhaustion3 hp P T hleft hc k a b hab c hm ht
  · intro hk
    have hm := m0GeodesicRightSide_keep3_sound hp P T hleft hc k a b hab c hk
    refine ⟨?_, ?_⟩
    · cases c <;> exact hm
    ·
      rw [m0GeodesicRightSideDeletedTailCells_eq hp P k
        (m0GeodesicRightSide_nextRay_contained hp P T hleft hc k) a b]
      exact hk.2

include hc

/-- Helper toward Lemma 5.6: the actual source slice realizes the
complete intrinsic two-prefix restriction, including first-return rotation. -/
theorem m0CutGeodesicSlice_rightSliceRealizes3 (x : XDP)
    (hx : longest = geoSliceRightLongest x) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    rightSliceRealizes3 x (m0GeodesicSide hp (P (k - 1)) .right)
      (m0CutGeodesicSlice (hp := hp) P k a b hab) := by
  subst longest
  have hoff := (m0GeodesicRightSide_leastCoalescence_iff_intrinsicSeam2 hp P T hleft hc k a b).1 hab
  refine ⟨_, _, _, _, a, b,
    m0GeodesicRightSide_rightReconstructionRay2 hp P T hleft hc k,
    m0GeodesicRightSide_rightReconstructionSeam2 hp (P (k - 1)), hoff.1, hoff.2, ?_⟩
  have hreal := m0CutGeodesicSlice_rightRestrictionRealizes2_literal_range hp P T hleft hc k a b hab
  rw [m0CutGeodesicSlice_range_eq_keep3 hp P T hleft hc k a b hab] at hreal
  exact hreal

/-- Helper toward Lemma 5.6: the two-seed reader returns the literal
source slice class without an exhaustion or characterization premise. -/
theorem rightOneSlice3_source (x : XDP)
    (hx : longest = geoSliceRightLongest x) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    rightOneSlice3 x (m0GeodesicSide hp (P (k - 1)) .right) =
      some (geometricSideClass (m0CutGeodesicSlice (hp := hp) P k a b hab)) :=
  rightOneSlice3_eq_of_realizes
    (m0CutGeodesicSlice_rightSliceRealizes3 hp P T hleft hc k x hx a b hab)

end Source

/-- Helper toward Lemma 5.6: next-side relations use typed first return,
the new root and seam, and the shifted exterior boundary. -/
@[expose] def rightNextRelation3 (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) (keep : Set (GeometricSideCell M))
    (t : TruncationRelation) (c e : GeometricSideCell M) : Prop :=
  match t with
  | .boundary i => geometricSideRelation M (.boundary (i + 1)) c e
  | .seam i => c = d i
  | _ => geometricSide_enclosed_relation M v d keep t c e

/-- Helper toward Lemma 5.6: the full typed next-side relation transports
through every marked isomorphism preserving the retained cells. -/
theorem rightNextRelation3_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d : ℕ → GeometricSideCell M)
    (keep : Set (GeometricSideCell M)) (keep' : Set (GeometricSideCell N))
    (hk : ∀ c, c ∈ keep ↔ I.equiv c ∈ keep')
    (t : TruncationRelation) (c e : GeometricSideCell M) :
    rightNextRelation3 M v d keep t c e ↔
      rightNextRelation3 N (I.equiv ∘ v) (I.equiv ∘ d) keep' t (I.equiv c) (I.equiv e) := by
  have hh := geometricSide_enclosed_relation_map_iff I v d keep keep' hk t c e
  cases t with
  | boundary i => exact I.relation_iff (.boundary (i + 1)) c e
  | seam i => exact ⟨congrArg I.equiv, fun h => I.equiv.injective h⟩
  | vertex | root | target | incident | opposite | oriented | rotation | faceNext =>
    exact hh

/-- Helper toward Lemma 5.6: full realization of the intrinsic next-right
restriction; the unique corner ray is read from the marked input. -/
@[expose] def rightNextRealizes3 (x : XDP) (M N : GeometricSideSubmap) : Prop :=
  ∃ v d, rightReconstructionRay2 (geoSliceRightLongest x) M v d ∧
    rightRestrictionRealizes2 M {c | geometricSide_intrinsic_right M v d c}
      (rightNextRelation3 M v d {c | geometricSide_intrinsic_right M v d c}) N

/-- Helper toward Lemma 5.6: next-right realizations transport without
any geometric exhaustion assumption. -/
theorem rightNextRealizes3_map {M M' N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M M') (x : XDP)
    (h : rightNextRealizes3 x M N) : rightNextRealizes3 x M' N := by
  obtain ⟨v, d, hr, hN⟩ := h
  exact ⟨I.equiv ∘ v, I.equiv ∘ d, rightReconstructionRay2_map I _ hr,
    rightRestrictionRealizes2_transport I (geometricSide_intrinsic_right_map_iff I v d)
      (rightNextRelation3_map_iff I v d _ _ (geometricSide_intrinsic_right_map_iff I v d)) hN⟩

/-- Helper toward Lemma 5.6: next-side realization determines a unique
marked class before choosing a numbered representative. -/
theorem rightNextRealizes3_class_unique {x : XDP} {M N N' : GeometricSideSubmap}
    (h : rightNextRealizes3 x M N) (h' : rightNextRealizes3 x M N') :
    geometricSideClass N = geometricSideClass N' := by
  obtain ⟨v, d, hr, hN⟩ := h
  obtain ⟨v', d', hr', hN'⟩ := h'
  obtain ⟨rfl, rfl⟩ := hr.2 v' d' hr'.1
  exact rightRestrictionRealizes2_class_unique hN hN'

/-- Helper toward Lemma 5.6: select the full typed next-side restriction
when realizable, retaining the input side outside that domain. -/
@[expose] noncomputable def rightNextSide3 (x : XDP) (M : GeometricSideSubmap) :
    GeometricSideSubmap :=
  if h : ∃ N, rightNextRealizes3 x M N then h.choose else M

/-- Helper toward Lemma 5.6: every full next-side realization identifies
the chosen next-side class. -/
theorem rightNextSide3_class_eq_of_realizes {x : XDP} {M N : GeometricSideSubmap}
    (h : rightNextRealizes3 x M N) :
    geometricSideClass (rightNextSide3 x M) = geometricSideClass N := by
  have hex : ∃ N, rightNextRealizes3 x M N := ⟨N, h⟩
  rw [rightNextSide3, dite_eq_left hex]
  exact rightNextRealizes3_class_unique hex.choose_spec h

/-- Helper toward Lemma 5.6: next-side marked classes are unconditionally
invariant, including inputs outside the realization domain. -/
theorem rightNextSide3_markedIso {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (x : XDP) :
    geometricSideClass (rightNextSide3 x M) = geometricSideClass (rightNextSide3 x N) := by
  by_cases h : ∃ K, rightNextRealizes3 x M K
  · obtain ⟨K, hK⟩ := h
    exact (rightNextSide3_class_eq_of_realizes hK).trans
      (rightNextSide3_class_eq_of_realizes (rightNextRealizes3_map I x hK)).symm
  · have hn : ¬ ∃ K, rightNextRealizes3 x N K := by
      rintro ⟨K, hK⟩
      exact h ⟨K, rightNextRealizes3_map (GeometricSideMarkedIso.symm I) x hK⟩
    rw [rightNextSide3, dite_eq_right h, rightNextSide3, dite_eq_right hn]
    exact (geometricSideClass_eq_iff _ _).2 ⟨I⟩

/-- Helper toward Lemma 5.6: the typed next-side operation descends to
marked-isomorphism classes without source or exhaustion premises. -/
@[expose] noncomputable def nextR3 (x : XDP) : GeometricSideClass → GeometricSideClass :=
  Quotient.lift (fun M => geometricSideClass (rightNextSide3 x M))
    (fun _ _ h => h.elim fun I => rightNextSide3_markedIso I x)

/-- Helper toward Lemma 5.6: evaluation of the quotient next-side reader
agrees with the class of its numbered representative. -/
theorem nextR3_geometricSideClass (x : XDP) (M : GeometricSideSubmap) :
    nextR3 x (geometricSideClass M) = geometricSideClass (rightNextSide3 x M) := rfl


section NextSource
variable (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hc : ∀ m : ℤ, ∃ a b : ℕ,
    M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b)
  (k : ℤ)

/-- Helper toward Lemma 5.6: the source next-right cell inclusion retains
literal vertex and edge identities and both dart orientations. -/
@[expose] def m0GeodesicNextRightCell3 :
    GeometricSideCell (m0GeodesicSide hp (P k) .right) →
      GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)
  | .inl v => .inl ⟨v.val, m0CutGeodesicRightSide_subset_of_le_index_of_adjacentCoalescence
      P T hleft hc (k - 1) k (by omega) v.property⟩
  | .inr d => .inr ⟨d.val, d.property.trans
      (m0CutGeodesicRightSide_subset_of_le_index_of_adjacentCoalescence
        P T hleft hc (k - 1) k (by omega))⟩

/-- Helper toward Lemma 5.6: the next-side inclusion is injective on
both sorts of individual cells. -/
theorem m0GeodesicNextRightCell3_injective :
    Function.Injective (m0GeodesicNextRightCell3 hp P T hleft hc k) := by
  intro c e hce
  cases c <;> cases e
  all_goals dsimp only [m0GeodesicNextRightCell3] at hce
  · have hv := congrArg Subtype.val (Sum.inl.inj hce)
    exact congrArg Sum.inl (Subtype.ext hv)
  · exact False.elim (Sum.inl_ne_inr hce)
  · exact False.elim (Sum.inr_ne_inl hce)
  · have hv := congrArg Subtype.val (Sum.inr.inj hce)
    exact congrArg Sum.inr (Subtype.ext hv)

/-- Helper toward Lemma 5.6: the image of the next-side inclusion is
exactly the unconditionally proved intrinsic right candidate. -/
theorem m0GeodesicNextRightCell3_mem_range_iff
    (c : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .right)) :
    c ∈ Set.range (m0GeodesicNextRightCell3 hp P T hleft hc k) ↔
      geometricSide_intrinsic_right _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) c := by
  rw [m0GeodesicRightSide_intrinsic_right_iff_nextRight hp P T hleft hc k c]
  cases c with
  | inl v =>
    constructor
    · rintro ⟨c, he⟩
      cases c with
      | inl c =>
        change v.val ∈ m0GeodesicSideVertices hp (P k) .right
        exact (congrArg Subtype.val (Sum.inl.inj he)) ▸ c.property
      | inr c => exact False.elim (Sum.inr_ne_inl he)
    · intro hv
      exact ⟨.inl ⟨v.val, hv⟩, rfl⟩
  | inr d =>
    constructor
    · rintro ⟨c, he⟩
      cases c with
      | inl c => exact False.elim (Sum.inl_ne_inr he)
      | inr c =>
        change d.val.1 ∈ m0GeodesicSideEdges hp (P k) .right
        exact (congrArg Prod.fst (congrArg Subtype.val (Sum.inr.inj he))) ▸ c.property
    · intro hd
      exact ⟨.inr ⟨d.val, hd⟩, rfl⟩

/-- Helper toward Lemma 5.6: source next-right rotation is the typed
positive first-return chain through the preceding right side. -/
theorem m0GeodesicNextRight_rotation_iff_chain3
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .right).edges}) :
    (m0GeodesicSide hp (P k) .right).rotation d.val e.val ↔
      EnclosedSliceRotationChain
        (geometricSideRelation (m0GeodesicSide hp (P (k - 1)) .right) .rotation)
        (Set.range (m0GeodesicNextRightCell3 hp P T hleft hc k))
        (m0GeodesicNextRightCell3 hp P T hleft hc k (.inr d))
        (m0GeodesicNextRightCell3 hp P T hleft hc k (.inr e)) := by
  let M := m0GeodesicSide hp (P (k - 1)) .right
  let S : Set (ℕ × Bool) := {d | d.1 ∈ M.edges}
  let U : Set (ℕ × Bool) := {d | d.1 ∈ (m0GeodesicSide hp (P k) .right).edges}
  let f := (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)
  let inc : S → GeometricSideCell M := fun d => .inr d
  have hUS : U ⊆ S := fun _ hd => hd.trans
    (m0CutGeodesicRightSide_subset_of_le_index_of_adjacentCoalescence P T hleft hc
      (k - 1) k (by omega))
  let dS : S := ⟨d.val, hUS d.property⟩
  let eS : S := ⟨e.val, hUS e.property⟩
  have hsub := enclosedSliceRotationChain_injective_iff
    (fun x : S => x.val) Subtype.val_injective
    (R := fun x y : S => enclosedSliceFirstReturn f S x.val y.val)
    (R' := fun x y => y ∈ S ∧ enclosedSliceFirstReturn f S x y)
    (S := {x : S | x.val ∈ U}) (S' := U)
    (fun x y => ⟨fun h => ⟨y.property, h⟩, fun h => h.2⟩)
    (fun _ => Iff.rfl) (fun _ y hy => ⟨⟨y, hy.1⟩, rfl⟩) dS eS
  have hcell := enclosedSliceRotationChain_injective_iff inc
    (fun _ _ hh => Sum.inr.inj hh)
    (R := fun x y : S => enclosedSliceFirstReturn f S x.val y.val)
    (R' := geometricSideRelation M .rotation)
    (S := {x : S | x.val ∈ U})
    (S' := Set.range (m0GeodesicNextRightCell3 hp P T hleft hc k))
    (fun _ _ => Iff.rfl)
    (fun x => by
      rw [m0GeodesicNextRightCell3_mem_range_iff,
        m0GeodesicRightSide_intrinsic_right_iff_nextRight hp P T hleft hc k]
      rfl)
    (by
      intro x y hxy
      cases y with
      | inl y => exact False.elim hxy
      | inr y => exact ⟨y, rfl⟩) dS eS
  exact (enclosedSliceFirstReturn_nested f S U hUS e.property).trans
    (hsub.symm.trans hcell)

/-- Helper toward Lemma 5.6: source next-right face retention is exactly
intrinsic right membership with forward next-ray darts excluded. -/
theorem m0GeodesicNextRight_faceNext_iff3
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .right).edges}) :
    (m0GeodesicSide hp (P k) .right).faceNext d.val e.val ↔
      rightNextRelation3 _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k)
        (Set.range (m0GeodesicNextRightCell3 hp P T hleft hc k)) .faceNext
        (m0GeodesicNextRightCell3 hp P T hleft hc k (.inr d))
        (m0GeodesicNextRightCell3 hp P T hleft hc k (.inr e)) := by
  let d' : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .right).edges} :=
    (m0GeodesicNextRightCell3 hp P T hleft hc k (.inr d)).getRight rfl
  have hi : geometricSide_intrinsic_right _
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) (.inr d') :=
    (m0GeodesicNextRightCell3_mem_range_iff hp P T hleft hc k _).1 ⟨.inr d, rfl⟩
  constructor
  · rintro ⟨⟨F, hb, hFR⟩, hsucc⟩
    have hnest := m0CutGeodesicRightSide_subset_of_le_index_of_adjacentCoalescence
      P T hleft hc (k - 1) k (by omega)
    have hprev := m0Geodesic_right_face_subset_of_rightSide_subset hp (P k) (P (k - 1)) hnest F hFR
    refine ⟨⟨⟨F, hb, hprev⟩, hsucc⟩, hi, ?_⟩
    intro n hn
    have hval : d.val = ((P k).codePath.edge n, false) :=
      congrArg Subtype.val (Sum.inr.inj hn)
    have hinv := m0GeodesicRightSide_face_dart_invariant hp (P k) (P (k - 1)) .right
      d' F hb hFR
    exact hinv.2 n hval
  · rintro ⟨⟨⟨F, hb, hprev⟩, hsucc⟩, _, hnot⟩
    refine ⟨⟨F, hb, ?_⟩, hsucc⟩
    apply m0GeodesicRightSide_invariant_dart_face hp (P k) (P (k - 1)) .right d' ?_ F
      (fun z hz => (hprev hz).1) hb
    refine ⟨d.property, ?_⟩
    intro n hn
    apply hnot n
    exact congrArg Sum.inr (Subtype.ext hn)


/-- Helper toward Lemma 5.6: every typed next-side relation agrees with
the complete source restriction, preserving all indexed boundary marks. -/
theorem m0GeodesicNextRight_relation_iff3 (t : TruncationRelation)
    (c e : GeometricSideCell (m0GeodesicSide hp (P k) .right)) :
    geometricSideRelation (m0GeodesicSide hp (P k) .right) t c e ↔
      rightNextRelation3 _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k)
        (Set.range (m0GeodesicNextRightCell3 hp P T hleft hc k)) t
        (m0GeodesicNextRightCell3 hp P T hleft hc k c)
        (m0GeodesicNextRightCell3 hp P T hleft hc k e) := by
  cases t with
  | root =>
    cases c with
    | inl c =>
      change c.val = boundaryVertex (shiftedStream W 0) h k ↔ Sum.inl _ = Sum.inl _
      rw [Sum.inl.injEq, Subtype.ext_iff]
      exact (congrArg (fun n => c.val = n) (m0Geodesic_initial_zero (P k))).symm ▸ Iff.rfl
    | inr c => exact ⟨False.elim, fun hh => (Sum.inr_ne_inl hh).elim⟩
  | seam i =>
    cases c with
    | inl c => exact ⟨False.elim, fun hh => (Sum.inl_ne_inr hh).elim⟩
    | inr c =>
      change ((P k).codePath.edge i, false) = c.val ↔ Sum.inr _ = Sum.inr _
      rw [Sum.inr.injEq, Subtype.ext_iff]
      exact eq_comm
  | boundary i =>
    cases c with
    | inl c => rfl
    | inr c =>
      change (boundaryOuterEdge (shiftedStream W 0) h (k + (i : ℤ)), false) = c.val ↔
        (boundaryOuterEdge (shiftedStream W 0) h (k - 1 + ((i + 1 : ℕ) : ℤ)), false) = c.val
      rw [show k - 1 + ((i + 1 : ℕ) : ℤ) = k + (i : ℤ) by omega]
  | rotation =>
    cases c with
    | inl c =>
      cases e <;> refine ⟨False.elim, ?_⟩ <;> intro hh <;>
        cases hh with
        | single hh => exact False.elim hh
        | cons hh _ _ => exact False.elim hh
    | inr c =>
      cases e with
      | inl e =>
        refine ⟨False.elim, ?_⟩
        intro hh
        obtain ⟨d, hd⟩ := enclosedSliceRotationChain_last hh
        cases d <;> exact False.elim hd
      | inr e => exact m0GeodesicNextRight_rotation_iff_chain3 hp P T hleft hc k c e
  | faceNext =>
    cases c with
    | inl c => cases e <;> exact ⟨False.elim, fun hh => hh.1.elim⟩
    | inr c =>
      cases e with
      | inl e => exact ⟨False.elim, fun hh => hh.1.elim⟩
      | inr e => exact m0GeodesicNextRight_faceNext_iff3 hp P T hleft hc k c e
  | vertex => cases c <;> cases e <;> rfl
  | target => cases c <;> cases e <;> rfl
  | incident => cases c <;> cases e <;> rfl
  | opposite => cases c <;> cases e <;> rfl
  | oriented => cases c <;> cases e <;> rfl

include T hleft hc

/-- Helper toward Lemma 5.6: the next source side is a full realization
of the intrinsic typed next-right restriction. -/
theorem m0GeodesicNextRight_rightNextRealizes3 (x : XDP)
    (hx : longest = geoSliceRightLongest x) :
    rightNextRealizes3 x (m0GeodesicSide hp (P (k - 1)) .right)
      (m0GeodesicSide hp (P k) .right) := by
  subst longest
  refine ⟨_, _, m0GeodesicRightSide_rightReconstructionRay2 hp P T hleft hc k, ?_⟩
  let f := m0GeodesicNextRightCell3 hp P T hleft hc k
  have hrange : Set.range f = {c | geometricSide_intrinsic_right _
      (m0GeodesicRightSideNextVertices hp P T hleft hc k)
      (m0GeodesicRightSideNextDarts hp P T hleft hc k) c} :=
    Set.ext (m0GeodesicNextRightCell3_mem_range_iff hp P T hleft hc k)
  have hreal : rightRestrictionRealizes2 _ (Set.range f)
      (rightNextRelation3 _
        (m0GeodesicRightSideNextVertices hp P T hleft hc k)
        (m0GeodesicRightSideNextDarts hp P T hleft hc k) (Set.range f))
      (m0GeodesicSide hp (P k) .right) := by
    let g : GeometricSideCell (m0GeodesicSide hp (P k) .right) → Set.range f :=
      fun c => ⟨f c, Set.mem_range_self c⟩
    have hg : Function.Bijective g := by
      constructor
      · intro c e hce
        exact m0GeodesicNextRightCell3_injective hp P T hleft hc k (congrArg Subtype.val hce)
      · rintro ⟨_, c, rfl⟩
        exact ⟨c, rfl⟩
    exact ⟨Equiv.ofBijective g hg, m0GeodesicNextRight_relation_iff3 hp P T hleft hc k⟩
  rw [hrange] at hreal
  exact hreal

/-- Helper toward Lemma 5.6: the typed next-side reader has the exact
next source-side marked class, without an extra source hypothesis. -/
theorem rightNextSide3_source (x : XDP)
    (hx : longest = geoSliceRightLongest x) :
    geometricSideClass (rightNextSide3 x (m0GeodesicSide hp (P (k - 1)) .right)) =
      geometricSideClass (m0GeodesicSide hp (P k) .right) :=
  rightNextSide3_class_eq_of_realizes
    (m0GeodesicNextRight_rightNextRealizes3 hp P T hleft hc k x hx)

end NextSource

open MeasureTheory DirectedDistances.RandomWalk
open DirectedDistances.Paper.Section4

/-- Helper toward Lemma 5.6: both right-side updates hold simultaneously
at every integer on one full-measure event, for the same source witness.
There is no additional geometric, connectivity, or exhaustion hypothesis. -/
theorem m0Cut_ae_rightSideUpdates (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : M0CutGeodesicSliceWitness W x, ∀ j : ℤ,
        oneR3 x (geometricSideClass (m0GeodesicSide s.hp (s.P j) .right)) =
          m0CutGeodesicSliceClassOption x (j + 1) W ∧
        nextR3 x (geometricSideClass (m0GeodesicSide s.hp (s.P j) .right)) =
          geometricSideClass (m0GeodesicSide s.hp (s.P (j + 1)) .right) := by
  filter_upwards [ae_m0CutGeodesicSliceWitness x] with W hW
  let s := Classical.choice hW
  have hc (m : ℤ) : ∃ a b : ℕ,
      M0CutLeastEdgeCoalescence (s.P m) (s.P (m + 1)) a b := by
    refine ⟨s.thetaMinus (m + 1), s.theta (m + 1), ?_⟩
    have hab := s.least (m + 1)
    rw [show m + 1 - 1 = m by omega] at hab
    exact hab
  refine ⟨s, fun j => ?_⟩
  constructor
  · rw [oneR3_geometricSideClass]
    have hs := rightOneSlice3_source s.hp s.P s.T s.hleft hc (j + 1) x rfl
      (s.thetaMinus (j + 1)) (s.theta (j + 1)) (s.least (j + 1))
    rw [show j + 1 - 1 = j by omega] at hs
    simpa only [m0CutGeodesicSliceClassOption, dite_eq_left hW] using hs
  · rw [nextR3_geometricSideClass]
    have hs := rightNextSide3_source s.hp s.P s.T s.hleft hc (j + 1) x rfl
    rw [show j + 1 - 1 = j by omega] at hs
    exact hs

/-- Helper toward Lemma 5.6: the one-slice quotient reader has the
source identity at k, on the same simultaneous event for every k. -/
theorem m0Cut_ae_oneR3_source (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : M0CutGeodesicSliceWitness W x, ∀ k : ℤ,
        oneR3 x (geometricSideClass (m0GeodesicSide s.hp (s.P (k - 1)) .right)) =
          m0CutGeodesicSliceClassOption x k W := by
  filter_upwards [m0Cut_ae_rightSideUpdates x] with W hW
  obtain ⟨s, hs⟩ := hW
  refine ⟨s, fun k => ?_⟩
  simpa only [show k - 1 + 1 = k by omega] using (hs (k - 1)).1

end DirectedDistances.PaperProofs.Section5
