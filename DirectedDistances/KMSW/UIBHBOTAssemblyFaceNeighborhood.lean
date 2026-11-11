/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTAssemblyFaceMultiplicity
import DirectedDistances.PlanarMap.FaceDegreeFiniteSupport

/-! # Neighborhoods along assembly edges

Helpers toward Definition 5.8. Local face contacts identify the geometric
neighborhood multiplicity with bordering-dart counts. The existing
almost-sure triangle classification then gives internal face degree three. -/

public section

namespace DirectedDistances.PlanarMap.PLDrawing

open Set Metric
open scoped Topology Classical

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
variable (P : PLDrawing D V flip rot vert)

/-- Helper toward Definition 5.8: near an interior point of a dart, every
drawing point lies on that geometric dart. Local finiteness closes the union
of all other compact dart images, including at polyline bends. -/
theorem interior_contact_local_arc_image (hvert : Function.Surjective vert)
    (d : D) {q : ℂ} (hq : q ∈ (P.arc d).interior) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball q r, y ∈ P.image → y ∈ (P.arc d).image := by
  classical
  have hqpos (v : V) : q ≠ P.pos v := by
    intro he
    exact P.interior_avoids_vertices d v (he ▸ hq)
  have hqother (e : D) (hed : e ≠ d) (heflip : e ≠ flip d) :
      q ∉ (P.arc e).image := by
    intro hqe
    have hqeint : q ∈ (P.arc e).interior := by
      refine ⟨hqe, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun he => hqpos (vert e) (he.trans (P.arc_start e)),
        fun he => hqpos (vert (flip e)) (he.trans (P.arc_finish e))⟩
    exact (Set.disjoint_left.mp (P.interior_disjoint d e hed heflip)) hq hqeint
  let B : D → Set ℂ := fun e =>
    if e = d ∨ e = flip d then ∅ else (P.arc e).image
  have hBsub (e : D) : B e ⊆ (P.arc e).image := by
    dsimp [B]
    split_ifs <;> simp only [empty_subset, subset_refl]
  have hlocal : LocallyFinite (fun e => (P.arc e).image) := by
    intro z
    refine ⟨ball z 1, ball_mem_nhds z zero_lt_one, ?_⟩
    simpa only [inter_comm] using P.locally_finite (ball z 1) isBounded_ball
  have hBclosed : IsClosed (⋃ e, B e) := by
    apply (hlocal.subset hBsub).isClosed_iUnion
    intro e
    dsimp [B]
    split_ifs
    · exact isClosed_empty
    · exact (P.arc e).isCompact_image.isClosed
  have hqB : q ∉ ⋃ e, B e := by
    intro h
    obtain ⟨e, he⟩ := mem_iUnion.mp h
    dsimp [B] at he
    split_ifs at he with heq
    · exact notMem_empty q he
    · exact hqother e (fun h => heq (Or.inl h)) (fun h => heq (Or.inr h)) he
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhds_iff.mp (hBclosed.isOpen_compl.mem_nhds hqB)
  refine ⟨r, hr, ?_⟩
  intro y hyr hy
  have hyB : y ∉ ⋃ e, B e := hball hyr
  rw [P.image_eq_union_arcs hvert] at hy
  obtain ⟨e, he⟩ := mem_iUnion.mp hy
  by_cases hed : e = d
  · simpa only [hed] using he
  by_cases heflip : e = flip d
  · rw [heflip, P.arc_flip d, Polyline.image_reverse_transfer] at he
    exact he
  · have hyeB : y ∈ B e := by
      simpa only [B, ite_eq_right (not_or.mpr ⟨hed, heflip⟩)] using he
    exact (hyB (mem_iUnion.mpr ⟨e, hyeB⟩)).elim

/-- Helper toward Definition 5.8: every face meeting a sufficiently small
ball about an interior point borders one of the two darts of that edge.
A punctured disk supplies a frontier contact away from polyline vertices;
the existing nearest-contact transport then returns to the original dart. -/
theorem interior_contact_local_bordering_dart (hvert : Function.Surjective vert)
    (d : D) {q : ℂ} (hq : q ∈ (P.arc d).interior) :
    ∃ r : ℝ, 0 < r ∧ ∀ (K : P.Face) (z : ℂ),
      z ∈ ball q r → z ∈ K.val →
      P.dartBorders d K ∨ P.dartBorders (flip d) K := by
  obtain ⟨ra, hra, harc⟩ := P.interior_contact_local_arc_image hvert d hq
  obtain ⟨rv, hrv, hvertices⟩ := P.polyline_vertices_locally_isolated q
  let r := min ra rv
  have hr : 0 < r := lt_min hra hrv
  have hqi : q ∈ P.image := Or.inr ⟨d, hq.1⟩
  have hnearby : ∃ y ∈ P.image, y ∈ ball q (r / 2) ∧ y ≠ q := by
    obtain ⟨i, hi, hseg⟩ : ∃ i, i + 1 < (P.arc d).points.length ∧
        q ∈ (P.arc d).segmentAt i := by
      rcases hq.1 with hs | hs
      · exact (hq.2 (Or.inl hs)).elim
      · exact hs
    let a := (P.arc d).point i
    let b := (P.arc d).point (i + 1)
    obtain ⟨b', hne, hsub⟩ : ∃ b' : ℂ, q ≠ b' ∧
        segment ℝ q b' ⊆ (P.arc d).segmentAt i := by
      by_cases hb : q = b
      · refine ⟨a, ?_, ?_⟩
        · exact hb ▸ ((P.arc_simple d).1 i hi).symm
        · exact (convex_segment a b).segment_subset hseg (left_mem_segment ℝ a b)
      · exact ⟨b, hb,
          (convex_segment a b).segment_subset hseg (right_mem_segment ℝ a b)⟩
    obtain ⟨y, hy, hyball, hyne⟩ := segment_endpoint_nearby q b' q hne
      (Or.inl rfl) (r / 2) (by positivity)
    exact ⟨y, Or.inr ⟨d, (P.arc d).segmentAt_subset_image hi (hsub hy)⟩,
      hyball, hyne⟩
  refine ⟨r / 4, by positivity, ?_⟩
  intro K z hz hzK
  have hzU : z ∈ ball q (r / 2) \ {q} := by
    refine ⟨?_, ?_⟩
    · exact (mem_ball.mp hz).trans (by linarith only [hr])
    · intro he
      exact P.face_subset_compl K hzK (he ▸ hqi)
  obtain ⟨hopen, _⟩ := P.face_open_frontier_subset_image hvert K
  have hfront : ∃ x ∈ ball q (r / 2) \ {q}, x ∈ frontier K.val := by
    by_contra hnone
    have hsub : ball q (r / 2) \ {q} ⊆ K.val := by
      apply (punctured_ball_isPreconnected q (r / 2) (by positivity)).subset_of_closure_inter_subset
        hopen ⟨z, hzU, hzK⟩
      intro x hx
      by_contra hxK
      apply hnone
      refine ⟨x, hx.2, hx.1, ?_⟩
      rw [hopen.interior_eq]
      exact hxK
    obtain ⟨y, hyim, hyball, hyne⟩ := hnearby
    exact P.face_subset_compl K (hsub ⟨hyball, hyne⟩) hyim
  obtain ⟨x, hxU, hxfront⟩ := hfront
  have hxq : 0 < dist x q := dist_pos.mpr hxU.2
  let s := min (r / 8) (dist x q / 8)
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  obtain ⟨w, hwK, hwx⟩ := Metric.mem_closure_iff.mp
    (frontier_subset_closure hxfront) s hs
  obtain ⟨q', e, j, hj, hqseg, _, hdist, hball, hmin⟩ :=
    P.face_nearest_segment_contact hvert d K w hwK
  have hxim : x ∈ P.image := (P.face_open_frontier_subset_image hvert K).2 hxfront
  have hnear : dist q' x < 2 * s := by
    calc
      dist q' x ≤ dist q' w + dist w x := dist_triangle _ _ _
      _ ≤ dist w x + dist w x := by
        rw [dist_comm q' w]
        exact add_le_add (hmin x hxim) le_rfl
      _ < 2 * s := by rw [dist_comm w x]; linarith only [hwx]
  have hqr : q' ∈ ball q r := by
    have hx := mem_ball.mp hxU.1
    have hsle : s ≤ r / 8 := min_le_left _ _
    have ht := dist_triangle q' x q
    rw [mem_ball]
    linarith only [ht, hnear, hsle, hx, hr]
  have hqne : q' ≠ q := by
    intro he
    have hsle : s ≤ dist x q / 8 := min_le_right _ _
    rw [he, dist_comm q x] at hnear
    linarith only [hnear, hsle, hxq]
  have hnotvertex (a : D) (k : ℕ) (hk : k < (P.arc a).points.length) :
      q' ≠ (P.arc a).point k := by
    intro he
    apply hqne
    rw [he]
    exact hvertices a k hk (he ▸ (mem_ball.mp hqr).trans_le (min_le_right ra rv))
  have hqopen : q' ∈ openSegment ℝ ((P.arc e).point j) ((P.arc e).point (j + 1)) :=
    mem_openSegment_of_ne_left_right (hnotvertex e j (by omega)).symm
      (hnotvertex e (j + 1) hj).symm hqseg
  have hqe : q' ∈ (P.arc e).interior :=
    openSegment_contact_mem_interior _ (P.arc_simple e) hj hqopen
  have hqd : q' ∈ (P.arc d).interior := by
    refine ⟨harc q' ((mem_ball.mp hqr).trans_le (min_le_left ra rv))
      (Or.inr ⟨e, hqe.1⟩), ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun he => P.interior_avoids_vertices e (vert d)
        ((he.trans (P.arc_start d)) ▸ hqe),
      fun he => P.interior_avoids_vertices e (vert (flip d))
        ((he.trans (P.arc_finish d)) ▸ hqe)⟩
  have he : e = d ∨ e = flip d := by
    by_contra hn
    exact (Set.disjoint_left.mp (P.interior_disjoint d e
      (fun he => hn (Or.inl he)) (fun he => hn (Or.inr he)))) hqd hqe
  have hb := P.face_nearest_openSegment_bordering_dart hvert K w q' e hj hqopen
    (dist_pos.mp hdist) hball hmin
  rcases he with rfl | rfl
  · exact hb
  · rw [P.flip_involutive d] at hb
    exact hb.symm

/-- Helper toward Definition 5.8: if both original darts border a face,
the face together with the closed edge arc is a neighborhood of every open
arc point, including bends. All nearby complementary faces are identified
by nearest-contact transport and uniqueness of the face bordering a dart. -/
theorem both_darts_border_implies_openArc_neighborhood
    (hvert : Function.Surjective vert) (e : P.GeometricEdge)
    (K : P.toPlaneGraphDrawing.Face)
    (hborder : P.dartBorders e.out (P.toPlaneGraphDrawingFaceEquiv K) ∧
      P.dartBorders (flip e.out) (P.toPlaneGraphDrawingFaceEquiv K)) :
    ∀ x ∈ P.toPlaneGraphDrawing.openArc e,
      K.val ∪ Set.range (P.toPlaneGraphDrawing.arc e) ∈ 𝓝 x := by
  intro x hx
  have hxint : x ∈ (P.arc e.out).interior := by
    change x ∈ (P.arc e.out).toPath '' openParams at hx
    rwa [Polyline.toPath_image_openParams _ (P.arc_length _) (P.arc_simple _)] at hx
  obtain ⟨ra, hra, harc⟩ := P.interior_contact_local_arc_image hvert e.out hxint
  obtain ⟨rf, hrf, hfaces⟩ := P.interior_contact_local_bordering_dart hvert e.out hxint
  apply Metric.mem_nhds_iff.mpr
  refine ⟨min ra rf, lt_min hra hrf, ?_⟩
  intro y hy
  by_cases hyim : y ∈ P.image
  · right
    change y ∈ Set.range (P.arc e.out).toPath
    rw [Polyline.range_toPath]
    exact harc y ((mem_ball.mp hy).trans_le (min_le_left ra rf)) hyim
  · left
    obtain ⟨L, hyL⟩ := (P.faces_cover_compl y).mpr hyim
    have hb := hfaces L y ((mem_ball.mp hy).trans_le (min_le_right ra rf)) hyL
    have heq : L = P.toPlaneGraphDrawingFaceEquiv K := by
      rcases hb with hb | hb
      · exact P.dartBorders_face_unique _ _ _ hb hborder.1
      · exact P.dartBorders_face_unique _ _ _ hb hborder.2
    have hyK : y ∈ (P.toPlaneGraphDrawingFaceEquiv K).val := heq ▸ hyL
    exact hyK

/-- Helper toward Definition 5.8: the geometric neighborhood multiplicity
is exactly the number of the edge's two original darts bordering the face. -/
theorem faceMult_eq_bordering_dart_count (hvert : Function.Surjective vert)
    (e : P.GeometricEdge) (K : P.toPlaneGraphDrawing.Face) :
    P.toPlaneGraphDrawing.faceMult e K =
      (if P.dartBorders e.out (P.toPlaneGraphDrawingFaceEquiv K) then (1 : ℕ∞) else 0) +
      (if P.dartBorders (flip e.out) (P.toPlaneGraphDrawingFaceEquiv K)
        then (1 : ℕ∞) else 0) :=
  (P.faceMult_eq_bordering_dart_count_iff hvert e K).mpr
    (P.both_darts_border_implies_openArc_neighborhood hvert e K)

end DirectedDistances.PlanarMap.PLDrawing

namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open scoped Topology Classical

section Assembly

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))
  (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
  (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
    (uibhbotPastMonotoneDrawing W hfin).pos)
  (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
    ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
  (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot (shiftedStream W 0) (H.1 0))
    (kmswLimitDartVertex (shiftedStream W 0)))
  (hf : F.pos = uibhbotSeparationFuturePos W H h0)
  (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
  (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer (shiftedStream W 0)
    h0 (H.1 0) ''
      ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all _)).arc d).image)
  (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)

local notation "G" => uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
local notation "M" => uibhbotAssemblyDirectedPlaneMapWithMissing
  W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

/-- Helper toward Definition 5.8: the exact assembly carrier satisfies the
two-sided neighborhood implication, including at internal polyline bends. -/
theorem uibhbotAssembly_both_darts_border_implies_openArc_neighborhood
    (K : (M).toPlaneGraphDrawing.Face)
    (_hK : (M).toPlaneGraphDrawing.IsInternal K) (e : (G).GeometricEdge)
    (hborder : (G).dartBorders e.out ((G).toPlaneGraphDrawingFaceEquiv K) ∧
      (G).dartBorders (wholePlaneDartFlip W e.out)
        ((G).toPlaneGraphDrawingFaceEquiv K)) :
    ∀ x ∈ (M).toPlaneGraphDrawing.openArc e,
      K.val ∪ Set.range ((M).toPlaneGraphDrawing.arc e) ∈ 𝓝 x :=
  (G).both_darts_border_implies_openArc_neighborhood
    (uibhbot_faceOrbit_dartVertex_surjective W H) e K hborder

/-- Helper toward Definition 5.8: for the exact assembly drawing, geometric
edge multiplicity agrees with its bordering-dart count. -/
theorem uibhbotAssembly_faceMult_eq_bordering_dart_count
    (K : (M).toPlaneGraphDrawing.Face) (e : (G).GeometricEdge) :
    (M).toPlaneGraphDrawing.faceMult e K =
      (if (G).dartBorders e.out ((G).toPlaneGraphDrawingFaceEquiv K)
        then (1 : ℕ∞) else 0) +
      (if (G).dartBorders (wholePlaneDartFlip W e.out)
        ((G).toPlaneGraphDrawingFaceEquiv K) then (1 : ℕ∞) else 0) :=
  (G).faceMult_eq_bordering_dart_count
    (uibhbot_faceOrbit_dartVertex_surjective W H) e K

end Assembly

open MeasureTheory DirectedDistances.PaperProofs.Section5

/-- Helper toward Definition 5.8: almost surely every internal face of
the assembled drawing has geometric face degree three. The count uses the
actual neighborhood multiplicities, including missing geometric edges. -/
theorem uibhbotCodeLawRel_ae_assembly_internal_faceDegree :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
        (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
        (hfin : KMSWFiniteIncidence (kmswPastCode W))
        (_hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
        (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot (kmswPastCode W) hfin) (kmswLimitDartVertex (kmswPastCode W)))
        (hp : P.pos = uibhbotPastStraightTransfer W hL hR ∘
          (uibhbotPastMonotoneDrawing W hfin).pos)
        (ha : ∀ d, (P.arc d).image = uibhbotPastStraightTransfer W hL hR ''
          ((uibhbotPastMonotoneDrawing W hfin).arc d).image)
        (F : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot (shiftedStream W 0) (H.1 0))
          (kmswLimitDartVertex (shiftedStream W 0)))
        (hf : F.pos = uibhbotSeparationFuturePos W H h0)
        (hFim : F.image ⊆ {z : ℂ | z.im ≤ 0})
        (hFa : ∀ d, (F.arc d).image = uibhbotGlueFutureTransfer
          (shiftedStream W 0) h0 (H.1 0) ''
            ((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
              (monotone_family_all _)).arc d).image)
        (G : WholePlaneDrawing W H),
        G = uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa ∧
        ∀ K : G.toPlaneGraphDrawing.Face,
          G.toPlaneGraphDrawing.IsInternal K → G.toPlaneGraphDrawing.faceDegree K = 3 := by
  filter_upwards [uibhbotCodeLawRel_ae_assembly_internal_face_triangle_edges] with W hW
  obtain ⟨H, h0, hL, hR, hfin, hRpos, P, hp, ha, F, hf, hFim, hFa,
    G, faceOfOrbit, hG, hbij, hchar, htri⟩ := hW
  refine ⟨H, h0, hL, hR, hfin, hRpos, P, hp, ha, F, hf, hFim, hFa, G, hG, ?_⟩
  intro K hK
  obtain ⟨q, hq, N, j, hdarts, hcard⟩ := htri K hK
  let t := stageTriangleDartTriple (shiftedStream W N) j
  let raw : Fin 3 → ℕ × Bool := fun i =>
    if i.val = 0 then t.1 else if i.val = 1 then t.2.1 else t.2.2
  let darts : Fin 3 → WholePlaneDart W := fun i => wholePlaneDartι W N (raw i)
  let edges : Fin 3 → G.GeometricEdge := fun i => Quotient.mk G.edgeSetoid (darts i)
  have hinj : Function.Injective edges := by
    have hc : (Finset.univ.image edges).card = (Finset.univ : Finset (Fin 3)).card := by
      simpa only [edges, darts, raw, t, Finset.card_univ, Fintype.card_fin] using hcard
    have hi := Finset.card_image_iff.mp hc
    intro i k hik
    exact hi (Finset.mem_univ i) (Finset.mem_univ k) hik
  let K' := G.toPlaneGraphDrawingFaceEquiv K
  have hb (a : WholePlaneDart W) : G.dartBorders a K' ↔ ∃ i : Fin 3, darts i = a := by
    have ho : G.dartBorders a K' ↔ Quotient.mk _ a = q := by
      constructor
      · intro ha
        exact hbij.1 (((hchar a K').mpr ha).trans hq.symm)
      · intro ha
        exact (hchar a K').mp ((congrArg faceOfOrbit ha).trans hq)
    rw [ho]
    change a ∈ {a : WholePlaneDart W | Quotient.mk _ a = q} ↔ _
    rw [hdarts]
    constructor
    · rintro ⟨b, hb, rfl⟩
      change b ∈ [t.1, t.2.1, t.2.2] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨raw i, ?_, rfl⟩
      fin_cases i <;> simp [raw, t, stageTriangleDartList]
  have hmult (e : G.GeometricEdge) : G.toPlaneGraphDrawing.faceMult e K =
      if ∃ i : Fin 3, edges i = e then (1 : ℕ∞) else 0 := by
    have hc : (∃ i : Fin 3, edges i = e) ↔
        G.dartBorders e.out K' ∨ G.dartBorders (wholePlaneDartFlip W e.out) K' := by
      constructor
      · rintro ⟨i, hie⟩
        have hrel : darts i = e.out ∨ darts i = wholePlaneDartFlip W e.out :=
          Quotient.exact (hie.trans (Quotient.out_eq e).symm)
        have hbi := (hb (darts i)).mpr ⟨i, rfl⟩
        rcases hrel with he | he
        · exact Or.inl (he ▸ hbi)
        · exact Or.inr (he ▸ hbi)
      · rintro (he | he)
        · obtain ⟨i, hi⟩ := (hb e.out).mp he
          exact ⟨i, (congrArg (Quotient.mk G.edgeSetoid) hi).trans (Quotient.out_eq e)⟩
        · obtain ⟨i, hi⟩ := (hb (wholePlaneDartFlip W e.out)).mp he
          exact ⟨i, (congrArg (Quotient.mk G.edgeSetoid) hi).trans
            ((G.geometricEdge_flip e.out).trans (Quotient.out_eq e))⟩
    have hn : ¬ (G.dartBorders e.out K' ∧
        G.dartBorders (wholePlaneDartFlip W e.out) K') := by
      rintro ⟨hl, hr⟩
      obtain ⟨i, hi⟩ := (hb e.out).mp hl
      obtain ⟨k, hk⟩ := (hb (wholePlaneDartFlip W e.out)).mp hr
      have heq : edges i = edges k := by
        change Quotient.mk G.edgeSetoid (darts i) = Quotient.mk G.edgeSetoid (darts k)
        rw [hi, hk, G.geometricEdge_flip]
      have hik := hinj heq
      have hd : e.out = wholePlaneDartFlip W e.out := hi.symm.trans (hik ▸ hk)
      exact G.flip_ne e.out hd.symm
    rw [G.faceMult_eq_bordering_dart_count (uibhbot_faceOrbit_dartVertex_surjective W H)]
    change (if G.dartBorders e.out K' then (1 : ℕ∞) else 0) +
      (if G.dartBorders (wholePlaneDartFlip W e.out) K' then (1 : ℕ∞) else 0) = _
    by_cases hl : G.dartBorders e.out K'
    · have hr : ¬ G.dartBorders (wholePlaneDartFlip W e.out) K' := fun hr => hn ⟨hl, hr⟩
      have he := hc.mpr (Or.inl hl)
      simp only [hl, hr, he, ite_true, ite_false, add_zero]
    · by_cases hr : G.dartBorders (wholePlaneDartFlip W e.out) K'
      · have he := hc.mpr (Or.inr hr)
        simp only [hl, hr, he, ite_true, ite_false, zero_add]
      · have he : ¬ ∃ i : Fin 3, edges i = e := fun he => (hc.mp he).elim hl hr
        simp only [hl, hr, he, ite_false, zero_add]
  exact G.toPlaneGraphDrawing.faceDegree_eq_three_of_injective K edges hinj hmult

end DirectedDistances.KMSW
