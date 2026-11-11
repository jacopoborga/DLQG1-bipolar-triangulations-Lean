/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTAssemblyFaceDegree

/-! # Geometric multiplicity for the assembly carrier

The carrier uses actual complementary components and its neighborhood test,
including polyline bends; no winding-side substitute is used here. -/

public section

namespace DirectedDistances.PlanarMap.PLDrawing

open Set Metric
open scoped Topology Classical

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
variable (P : PLDrawing D V flip rot vert)

/-- Helper toward Definition 5.8: either oriented representative bordering a
face puts the entire geometric open arc in its closure. -/
theorem openArc_subset_closure_of_bordering_dart (hvert : Function.Surjective vert)
    (e : P.GeometricEdge) (K : P.toPlaneGraphDrawing.Face)
    (h : P.dartBorders e.out (P.toPlaneGraphDrawingFaceEquiv K) ∨
      P.dartBorders (flip e.out) (P.toPlaneGraphDrawingFaceEquiv K)) :
    P.toPlaneGraphDrawing.openArc e ⊆ closure K.val := by
  have he : P.toPlaneGraphDrawing.openArc e = (P.arc e.out).interior := by
    change (P.arc e.out).toPath '' openParams = _
    exact Polyline.toPath_image_openParams _ (P.arc_length _) (P.arc_simple _)
  rw [he]
  rcases h with h | h
  · exact Set.Subset.trans (fun _ hz => hz.1) (P.dartBorders_arc_subset_closure hvert _ _ h)
  · have hc := P.dartBorders_arc_subset_closure hvert _ _ h
    rw [P.arc_image_flip] at hc
    exact Set.Subset.trans (fun _ hz => hz.1) hc

/-- Helper toward Definition 5.8: closure incidence with an open geometric
edge forces incidence with one of its two original darts. A nearby nearest
contact is confined to a single open segment; the established transport
handles all earlier bends, including straight and reflex sectors. -/
theorem bordering_dart_of_openArc_subset_closure (hvert : Function.Surjective vert)
    (e : P.GeometricEdge) (K : P.toPlaneGraphDrawing.Face)
    (h : P.toPlaneGraphDrawing.openArc e ⊆ closure K.val) :
    P.dartBorders e.out (P.toPlaneGraphDrawingFaceEquiv K) ∨
      P.dartBorders (flip e.out) (P.toPlaneGraphDrawingFaceEquiv K) := by
  let d := e.out
  let a := (P.arc d).point 0
  let b := (P.arc d).point 1
  let q := midpoint ℝ a b
  have hi : 0 + 1 < (P.arc d).points.length := P.arc_length d
  have hab : a ≠ b := (P.arc_simple d).1 0 hi
  have hqa : q ≠ a := fun he => hab ((midpoint_eq_left_iff ℝ).mp he)
  have hqb : q ≠ b := fun he => hab ((midpoint_eq_right_iff ℝ).mp he)
  have hqo : q ∈ openSegment ℝ a b := midpoint_mem_openSegment a b
  have hqint : q ∈ (P.arc d).interior :=
    openSegment_contact_mem_interior _ (P.arc_simple d) hi hqo
  have hqcl : q ∈ closure K.val := by
    apply h
    change q ∈ (P.arc d).toPath '' openParams
    rw [Polyline.toPath_image_openParams _ (P.arc_length _) (P.arc_simple _)]
    exact hqint
  obtain ⟨r, hr, hlocal⟩ := P.openSegment_contact_local_image hvert d hi hqo
  let s := min r (min (dist q a) (dist q b))
  have hs : 0 < s := lt_min hr (lt_min (dist_pos.mpr hqa) (dist_pos.mpr hqb))
  obtain ⟨w, hwK, hwq⟩ := Metric.mem_closure_iff.mp hqcl (s / 4) (by positivity)
  let K' := P.toPlaneGraphDrawingFaceEquiv K
  obtain ⟨q', d', i', hi', hq', _, hdist, hball, hmin⟩ :=
    P.face_nearest_segment_contact hvert d K' w hwK
  have hqimage : q ∈ P.image := Or.inr ⟨d, hqint.1⟩
  have hq'image : q' ∈ P.image :=
    Or.inr ⟨d', (P.arc d').segmentAt_subset_image hi' hq'⟩
  have hnear : dist q' q < s := by
    calc
      dist q' q ≤ dist q' w + dist w q := dist_triangle _ _ _
      _ ≤ dist w q + dist w q := by
        rw [dist_comm q' w]
        exact add_le_add (hmin q hqimage) le_rfl
      _ < s := by rw [dist_comm w q]; linarith only [hwq, hs]
  have hs_r : s ≤ r := min_le_left _ _
  have hs_a : s ≤ dist q a := (min_le_right _ _).trans (min_le_left _ _)
  have hs_b : s ≤ dist q b := (min_le_right _ _).trans (min_le_right _ _)
  have hseg : q' ∈ segment ℝ a b :=
    hlocal q' (hnear.trans_le hs_r) hq'image
  have hna : a ≠ q' := by
    intro he
    have ht : dist q' q < dist q a := hnear.trans_le hs_a
    rw [← he, dist_comm a q] at ht
    exact (lt_irrefl _ ht)
  have hnb : b ≠ q' := by
    intro he
    have ht : dist q' q < dist q b := hnear.trans_le hs_b
    rw [← he, dist_comm b q] at ht
    exact (lt_irrefl _ ht)
  exact P.face_nearest_openSegment_bordering_dart hvert K' w q' d hi
    (mem_openSegment_of_ne_left_right hna hnb hseg)
    (dist_pos.mp hdist) hball hmin

/-- Helper toward Definition 5.8: the carrier's closure branch agrees exactly
with incidence with either dart, retaining the two orientations separately. -/
theorem openArc_subset_closure_iff_bordering_dart (hvert : Function.Surjective vert)
    (e : P.GeometricEdge) (K : P.toPlaneGraphDrawing.Face) :
    P.toPlaneGraphDrawing.openArc e ⊆ closure K.val ↔
      P.dartBorders e.out (P.toPlaneGraphDrawingFaceEquiv K) ∨
        P.dartBorders (flip e.out) (P.toPlaneGraphDrawingFaceEquiv K) :=
  ⟨P.bordering_dart_of_openArc_subset_closure hvert e K,
    P.openArc_subset_closure_of_bordering_dart hvert e K⟩

/-- Helper toward Definition 5.8: the actual neighborhood branch forces
both oriented representatives to border the face. This uses closure contact
with each neighboring face and disjointness from the entire geometric arc. -/
theorem both_darts_border_of_openArc_neighborhood (hvert : Function.Surjective vert)
    (e : P.GeometricEdge) (K : P.toPlaneGraphDrawing.Face)
    (hN : ∀ x ∈ P.toPlaneGraphDrawing.openArc e,
      K.val ∪ Set.range (P.toPlaneGraphDrawing.arc e) ∈ 𝓝 x) :
    P.dartBorders e.out (P.toPlaneGraphDrawingFaceEquiv K) ∧
      P.dartBorders (flip e.out) (P.toPlaneGraphDrawingFaceEquiv K) := by
  let d := e.out
  let q := midpoint ℝ ((P.arc d).point 0) ((P.arc d).point 1)
  have hi : 0 + 1 < (P.arc d).points.length := P.arc_length d
  have hqint : q ∈ (P.arc d).interior :=
    openSegment_contact_mem_interior _ (P.arc_simple d) hi
      (midpoint_mem_openSegment _ _)
  have hqopen : q ∈ P.toPlaneGraphDrawing.openArc e := by
    change q ∈ (P.arc d).toPath '' openParams
    rw [Polyline.toPath_image_openParams _ (P.arc_length _) (P.arc_simple _)]
    exact hqint
  have hforce (a : D) (ha : (P.arc a).image = (P.arc d).image) :
      P.dartBorders a (P.toPlaneGraphDrawingFaceEquiv K) := by
    obtain ⟨K', hK'⟩ := P.dartBorders_exists_of_wedge_compl a
      (P.wedgeIn_compl_image hvert _ _ (P.initial_nonzero a))
    have hcl : q ∈ closure K'.val :=
      P.dartBorders_arc_subset_closure hvert a K' hK' (ha.symm ▸ hqint.1)
    obtain ⟨y, hyU, hyK'⟩ := mem_closure_iff_nhds.mp hcl _ (hN q hqopen)
    have hyK : y ∈ K.val := by
      rcases hyU with hyK | hyArc
      · exact hyK
      · have hyim : y ∈ P.image := by
          right
          refine ⟨d, ?_⟩
          change y ∈ Set.range (P.arc d).toPath at hyArc
          rwa [Polyline.range_toPath] at hyArc
        exact False.elim (P.face_subset_compl K' hyK' hyim)
    have heq : K' = P.toPlaneGraphDrawingFaceEquiv K := P.faces_eq_of_mem hyK' hyK
    exact heq ▸ hK'
  exact ⟨hforce d rfl, hforce (flip d) (P.arc_image_flip d)⟩

/-- Helper toward Definition 5.8: geometric multiplicity cannot exceed
the number of bordering oriented representatives. -/
theorem faceMult_le_bordering_dart_count (hvert : Function.Surjective vert)
    (e : P.GeometricEdge) (K : P.toPlaneGraphDrawing.Face) :
    P.toPlaneGraphDrawing.faceMult e K ≤
      (if P.dartBorders e.out (P.toPlaneGraphDrawingFaceEquiv K) then (1 : ℕ∞) else 0) +
      (if P.dartBorders (flip e.out) (P.toPlaneGraphDrawingFaceEquiv K)
        then (1 : ℕ∞) else 0) := by
  classical
  have hc := P.openArc_subset_closure_iff_bordering_dart hvert e K
  have hn := P.both_darts_border_of_openArc_neighborhood hvert e K
  by_cases hl : P.dartBorders e.out (P.toPlaneGraphDrawingFaceEquiv K) <;>
    by_cases hr : P.dartBorders (flip e.out) (P.toPlaneGraphDrawingFaceEquiv K) <;>
    by_cases hN : ∀ x ∈ P.toPlaneGraphDrawing.openArc e,
      K.val ∪ Set.range (P.toPlaneGraphDrawing.arc e) ∈ 𝓝 x <;>
    simp_all [PlaneGraphDrawing.faceMult, -not_forall]; norm_num

/-- Helper toward Definition 5.8: the multiplicity bridge is reduced exactly
to the remaining two-sided neighborhood implication. This is an equivalence,
not an assumption of that implication or a completed multiplicity bridge. -/
theorem faceMult_eq_bordering_dart_count_iff (hvert : Function.Surjective vert)
    (e : P.GeometricEdge) (K : P.toPlaneGraphDrawing.Face) :
    (P.toPlaneGraphDrawing.faceMult e K =
      (if P.dartBorders e.out (P.toPlaneGraphDrawingFaceEquiv K) then (1 : ℕ∞) else 0) +
      (if P.dartBorders (flip e.out) (P.toPlaneGraphDrawingFaceEquiv K)
        then (1 : ℕ∞) else 0)) ↔
    (P.dartBorders e.out (P.toPlaneGraphDrawingFaceEquiv K) ∧
      P.dartBorders (flip e.out) (P.toPlaneGraphDrawingFaceEquiv K) →
      ∀ x ∈ P.toPlaneGraphDrawing.openArc e,
        K.val ∪ Set.range (P.toPlaneGraphDrawing.arc e) ∈ 𝓝 x) := by
  classical
  have hc := P.openArc_subset_closure_iff_bordering_dart hvert e K
  have hn := P.both_darts_border_of_openArc_neighborhood hvert e K
  by_cases hl : P.dartBorders e.out (P.toPlaneGraphDrawingFaceEquiv K) <;>
    by_cases hr : P.dartBorders (flip e.out) (P.toPlaneGraphDrawingFaceEquiv K) <;>
    by_cases hN : ∀ x ∈ P.toPlaneGraphDrawing.openArc e,
      K.val ∪ Set.range (P.toPlaneGraphDrawing.arc e) ∈ 𝓝 x <;>
    simp_all [PlaneGraphDrawing.faceMult, -not_forall] <;> norm_num

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



theorem uibhbotAssembly_faceMult_eq_bordering_dart_count_iff
    (K : (M).toPlaneGraphDrawing.Face)
    (_hK : (M).toPlaneGraphDrawing.IsInternal K) (e : (G).GeometricEdge) :
    ((M).toPlaneGraphDrawing.faceMult e K =
      (if (G).dartBorders e.out ((G).toPlaneGraphDrawingFaceEquiv K)
        then (1 : ℕ∞) else 0) +
      (if (G).dartBorders (wholePlaneDartFlip W e.out)
        ((G).toPlaneGraphDrawingFaceEquiv K) then (1 : ℕ∞) else 0)) ↔
    ((G).dartBorders e.out ((G).toPlaneGraphDrawingFaceEquiv K) ∧
      (G).dartBorders (wholePlaneDartFlip W e.out)
        ((G).toPlaneGraphDrawingFaceEquiv K) →
      ∀ x ∈ (M).toPlaneGraphDrawing.openArc e,
        K.val ∪ Set.range ((M).toPlaneGraphDrawing.arc e) ∈ 𝓝 x) :=
  (G).faceMult_eq_bordering_dart_count_iff
    (uibhbot_faceOrbit_dartVertex_surjective W H) e K

end Assembly
end DirectedDistances.KMSW

