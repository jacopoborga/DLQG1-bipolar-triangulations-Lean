/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTAssemblyFaceBorders
import DirectedDistances.KMSW.WholePlaneLeftBoundaryTerminal
import DirectedDistances.PlanarMap.PLDrawingFaceTransfer
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-! # Geometric contact toward UIBHBOT face coverage

Helpers toward Definition 5.8

This file proves nearest-segment contact and its nonzero oriented side at an
interior contact. Signed half-disks transport along segments and across every
preceding bend. Local finiteness supplies a uniform wedge at the original
dart tail, and reversal handles the negative side: an open-segment contact
therefore supplies a bordering original dart. Local isolation of polyline
vertices and preconnected punctured disks reduce every endpoint contact to
an open-segment contact, proving geometric face coverage. The existing
assembly bordering theorems then give the face-orbit equivalence, exact
creation-cap classification, uniqueness of the unbounded face, and its
bordering characterization by the east darts of globally missing edges.
they do not assert completion of that definition or of the paper. -/

public section

namespace DirectedDistances.PlanarMap.PLDrawing

open Set Metric
open scoped Topology

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
variable (P : PLDrawing D V flip rot vert)

/-- Helper toward Definition 5.8: each point of a face has a nearest point
of the geometric image, with the entire intervening open ball in that face.
The nearest point lies on a nondegenerate segment of an actual geometric dart;
no assumption about face coverage by darts is used. -/
theorem face_nearest_segment_contact (hvert : Function.Surjective vert) (d₀ : D)
    (K : P.Face) (z : ℂ) (hz : z ∈ K.val) :
    ∃ (q : ℂ) (d : D) (i : ℕ),
      i + 1 < (P.arc d).points.length ∧
      q ∈ (P.arc d).segmentAt i ∧
      q ∈ frontier K.val ∧
      0 < dist z q ∧
      ball z (dist z q) ⊆ K.val ∧
      ∀ y ∈ P.image, dist z q ≤ dist z y := by
  have hne : P.image.Nonempty :=
    ⟨P.pos (vert d₀), Or.inl ⟨vert d₀, rfl⟩⟩
  obtain ⟨q, hq, hdist⟩ :=
    (P.image_isClosed hvert).exists_infDist_eq_dist hne z
  have hznot := P.face_subset_compl K hz
  have hzq : z ≠ q := by
    rintro rfl
    exact hznot hq
  have hr : 0 < dist z q := dist_pos.mpr hzq
  have hbcompl : ball z (dist z q) ⊆ P.imageᶜ := by
    rw [← hdist]
    exact ball_infDist_subset_compl
  have hbK : ball z (dist z q) ⊆ K.val := by
    obtain ⟨x, hx, hK⟩ := K.property
    rw [hK] at hz ⊢
    rw [connectedComponentIn_eq hz]
    intro y hy
    have hs : IsPreconnected (segment ℝ z y) := by
      rw [segment_eq_image']
      exact isPreconnected_Icc.image _ (by fun_prop)
    have hsball : segment ℝ z y ⊆ ball z (dist z q) :=
      (convex_ball z (dist z q)).segment_subset (mem_ball_self hr) hy
    exact hs.subset_connectedComponentIn (left_mem_segment ℝ z y)
      (hsball.trans hbcompl) (right_mem_segment ℝ z y)
  have hqcl : q ∈ closure K.val := by
    apply closure_mono hbK
    rw [closure_ball z (ne_of_gt hr)]
    exact mem_closedBall.mpr (le_of_eq (dist_comm q z))
  have hqfront : q ∈ frontier K.val := by
    rw [← closure_sdiff_interior]
    refine ⟨hqcl, ?_⟩
    intro hqint
    exact P.face_subset_compl K (interior_subset hqint) hq
  have hqarc : ∃ d, q ∈ (P.arc d).image := by
    rw [P.image_eq_union_arcs hvert] at hq
    exact mem_iUnion.mp hq
  obtain ⟨d, hd⟩ := hqarc
  have hseg : ∃ i, i + 1 < (P.arc d).points.length ∧
      q ∈ (P.arc d).segmentAt i := by
    rcases hd with hstart | ⟨i, hi, hqi⟩
    · refine ⟨0, by have := P.arc_length d; omega, ?_⟩
      rw [hstart]
      change (P.arc d).start ∈ segment ℝ ((P.arc d).point 0) ((P.arc d).point 1)
      rw [Polyline.point_zero_eq_start]
      exact left_mem_segment ℝ _ _
    · exact ⟨i, hi, hqi⟩
  obtain ⟨i, hi, hqi⟩ := hseg
  refine ⟨q, d, i, hi, hqi, hqfront, hr, hbK, ?_⟩
  intro y hy
  rw [← hdist]
  exact infDist_le_dist_of_mem hy

/-- Helper toward Definition 5.8: a nearest point in the open part of a
segment is the orthogonal foot. The minimization premise is only over that
segment, so it applies to the global nearest contact above. -/
theorem segment_nearest_orthogonal (a b z q : ℂ)
    (hq : q ∈ openSegment ℝ a b)
    (hmin : ∀ y ∈ segment ℝ a b, dist z q ≤ dist z y) :
    (star (b - a) * (z - q)).re = 0 := by
  have hqseg : q ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hq
  let : Nonempty (segment ℝ a b) := ⟨⟨q, hqseg⟩⟩
  have hbelow : BddBelow (Set.range (fun y : segment ℝ a b => ‖z - y‖)) :=
    ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
  have hnorm : ‖z - q‖ = ⨅ y : segment ℝ a b, ‖z - y‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro y
      simpa only [dist_eq_norm] using hmin y y.property
    · exact ciInf_le hbelow ⟨q, hqseg⟩
  have hinner := (norm_eq_iInf_iff_real_inner_le_zero
    (convex_segment a b) hqseg).mp hnorm
  rw [openSegment_eq_image'] at hq
  obtain ⟨s, hs, hsq⟩ := hq
  have ha : a - q = (-s) • (b - a) := by
    rw [← hsq]
    module
  have hb : b - q = (1 - s) • (b - a) := by
    rw [← hsq]
    module
  have hleft := hinner a (left_mem_segment ℝ a b)
  have hright := hinner b (right_mem_segment ℝ a b)
  rw [ha, real_inner_smul_right] at hleft
  rw [hb, real_inner_smul_right] at hright
  have hzero : inner ℝ (z - q) (b - a) = 0 := by
    nlinarith only [hs.1, hs.2, hleft, hright]
  rw [real_inner_comm] at hzero
  simpa only [Complex.inner, starRingEnd_apply, mul_comm] using hzero

/-- Helper toward Definition 5.8: an interior nearest contact has a
nonzero oriented side. This excludes the collinear case without choosing a
side or assuming any dart borders the face. -/
theorem segment_nearest_side_ne_zero (a b z q : ℂ) (hab : a ≠ b) (hzq : z ≠ q)
    (hq : q ∈ openSegment ℝ a b)
    (hmin : ∀ y ∈ segment ℝ a b, dist z q ≤ dist z y) :
    (star (b - a) * (z - q)).im ≠ 0 := by
  have hreal := segment_nearest_orthogonal a b z q hq hmin
  intro him
  have heq : star (b - a) * (z - q) = 0 := Complex.ext hreal him
  exact (mul_ne_zero (star_ne_zero.mpr (sub_ne_zero.mpr hab.symm))
    (sub_ne_zero.mpr hzq)) heq

/-- Helper toward Definition 5.8: a point in the open part of a segment
of a simple polyline belongs to no other segment of that polyline. -/
theorem openSegment_contact_index_unique (p : Polyline) (hp : p.IsSimple)
    {i j : ℕ} (hi : i + 1 < p.points.length) (hj : j + 1 < p.points.length)
    {q : ℂ} (hq : q ∈ openSegment ℝ (p.point i) (p.point (i + 1)))
    (hqj : q ∈ p.segmentAt j) : j = i := by
  have hqi : q ∈ p.segmentAt i := openSegment_subset_segment ℝ _ _ hq
  have hqa : q ≠ p.point i := by
    intro he
    rw [he, left_mem_openSegment_iff] at hq
    exact hp.1 i hi hq
  have hqb : q ≠ p.point (i + 1) := by
    intro he
    rw [he, right_mem_openSegment_iff] at hq
    exact hp.1 i hi hq
  by_cases heq : j = i
  · exact heq
  by_cases hji : j + 1 = i
  · have hmeet := hp.2.1 j (by omega)
    have hqpoint : q ∈ ({p.point (j + 1)} : Set ℂ) := by
      rw [← hmeet]
      exact ⟨hqj, hji ▸ hqi⟩
    exact (hqa (hji ▸ Set.mem_singleton_iff.mp hqpoint)).elim
  by_cases hij : i + 1 = j
  · have hmeet := hp.2.1 i (by omega)
    have hqpoint : q ∈ ({p.point (i + 1)} : Set ℂ) := by
      rw [← hmeet]
      exact ⟨hqi, hij ▸ hqj⟩
    exact (hqb (Set.mem_singleton_iff.mp hqpoint)).elim
  rcases lt_or_gt_of_ne heq with hlt | hgt
  · exact ((Set.disjoint_left.mp (hp.2.2 j i hj hi (by omega))) hqj hqi).elim
  · exact ((Set.disjoint_left.mp (hp.2.2 i j hi hj (by omega))) hqi hqj).elim

/-- Helper toward Definition 5.8: an open-segment contact is in the
polyline interior, including when the chosen segment is first or last. -/
theorem openSegment_contact_mem_interior (p : Polyline) (hp : p.IsSimple)
    {i : ℕ} (hi : i + 1 < p.points.length) {q : ℂ}
    (hq : q ∈ openSegment ℝ (p.point i) (p.point (i + 1))) :
    q ∈ p.interior := by
  have hqi : q ∈ p.segmentAt i := openSegment_subset_segment ℝ _ _ hq
  have hstart : q ≠ p.start := by
    intro he
    have hs : q ∈ p.segmentAt 0 := by
      rw [he]
      change p.start ∈ segment ℝ (p.point 0) (p.point 1)
      rw [p.point_zero_eq_start]
      exact left_mem_segment ℝ _ _
    have hidx := openSegment_contact_index_unique p hp hi (by omega) hq hs
    subst i
    rw [he, ← p.point_zero_eq_start, left_mem_openSegment_iff] at hq
    exact hp.1 0 hi hq
  have hfinish : q ≠ p.finish := by
    intro he
    let j := p.points.length - 2
    have hj : j + 1 < p.points.length := by dsimp [j]; omega
    have hlast : j + 1 = p.points.length - 1 := by dsimp [j]; omega
    have hf : q ∈ p.segmentAt j := by
      rw [he]
      change p.finish ∈ segment ℝ (p.point j) (p.point (j + 1))
      rw [hlast, p.point_last_eq_finish]
      exact right_mem_segment ℝ _ _
    have hidx := openSegment_contact_index_unique p hp hi hj hq hf
    have hqend : q = p.point (i + 1) := by
      rw [← hidx, hlast, p.point_last_eq_finish]
      exact he
    rw [hqend, right_mem_openSegment_iff] at hq
    exact hp.1 i hi hq
  exact ⟨p.segmentAt_subset_image hi hqi, by
    simpa only [mem_insert_iff, mem_singleton_iff, not_or] using And.intro hstart hfinish⟩

/-- Helper toward Definition 5.8: near an open-segment contact, the entire
drawing consists only of that segment. Local finiteness excludes distant arcs;
simple traces and disjoint edge interiors exclude all other local segments. -/
theorem openSegment_contact_local_image (hvert : Function.Surjective vert)
    (d : D) {i : ℕ} (hi : i + 1 < (P.arc d).points.length) {q : ℂ}
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball q r, y ∈ P.image → y ∈ (P.arc d).segmentAt i := by
  classical
  let p := P.arc d
  have hqint : q ∈ p.interior :=
    openSegment_contact_mem_interior p (P.arc_simple d) hi hq
  have hqpos (v : V) : q ≠ P.pos v := by
    intro he
    exact P.interior_avoids_vertices d v (he ▸ hqint)
  have hqother (e : D) (hed : e ≠ d) (heflip : e ≠ flip d) :
      q ∉ (P.arc e).image := by
    intro hqe
    have hqeint : q ∈ (P.arc e).interior := by
      refine ⟨hqe, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun he => hqpos (vert e) (he.trans (P.arc_start e)),
        fun he => hqpos (vert (flip e)) (he.trans (P.arc_finish e))⟩
    exact (Set.disjoint_left.mp (P.interior_disjoint d e hed heflip)) hqint hqeint
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
  let J := Fin (p.points.length - 1)
  let S : J → Set ℂ := fun j => if j.val = i then ∅ else p.segmentAt j.val
  have hSclosed : IsClosed (⋃ j, S j) := by
    apply (locallyFinite_of_finite S).isClosed_iUnion
    intro j
    dsimp [S]
    split_ifs
    · exact isClosed_empty
    · change IsClosed (segment ℝ _ _)
      rw [segment_eq_image']
      exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hqS : q ∉ ⋃ j, S j := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    dsimp [S] at hj
    split_ifs at hj with heq
    · exact notMem_empty q hj
    · exact heq (openSegment_contact_index_unique p (P.arc_simple d) hi
        (by have := j.isLt; omega) hq hj)
  have hqstart : q ≠ p.start := by
    intro he
    exact hqint.2 (Or.inl he)
  let E : Set ℂ := (⋃ e, B e) ∪ (⋃ j, S j) ∪ {p.start}
  have hEclosed : IsClosed E := (hBclosed.union hSclosed).union isClosed_singleton
  have hqE : q ∉ E := by
    rintro ((he | hj) | hs)
    · exact hqB he
    · exact hqS hj
    · exact hqstart hs
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hEclosed.isOpen_compl.mem_nhds hqE)
  refine ⟨r, hr, ?_⟩
  intro y hyr hy
  have hyE : y ∉ E := hball hyr
  rw [P.image_eq_union_arcs hvert] at hy
  obtain ⟨e, he⟩ := mem_iUnion.mp hy
  have hyp : y ∈ p.image := by
    by_cases hed : e = d
    · simpa only [hed] using he
    by_cases heflip : e = flip d
    · rw [heflip, P.arc_flip d, Polyline.image_reverse_transfer] at he
      exact he
    · exact (hyE (Or.inl (Or.inl (mem_iUnion.mpr
        ⟨e, by simpa only [B, ite_eq_right (not_or.mpr ⟨hed, heflip⟩)] using he⟩)))).elim
  rcases hyp with hs | ⟨j, hj, hyj⟩
  · exact (hyE (Or.inr hs)).elim
  · by_cases hji : j = i
    · simpa only [hji] using hyj
    · exact (hyE (Or.inl (Or.inr (mem_iUnion.mpr
        ⟨⟨j, by omega⟩, by simpa only [S, ite_eq_right hji] using hyj⟩)))).elim

/-- Helper toward Definition 5.8: the oriented side vanishes on the
supporting line of a segment, with any point of the segment as origin. -/
theorem segment_contact_side_eq_zero (a b q y : ℂ)
    (hq : q ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b) :
    (star (b - a) * (y - q)).im = 0 := by
  rw [segment_eq_image'] at hq hy
  obtain ⟨s, _, hs⟩ := hq
  obtain ⟨t, _, ht⟩ := hy
  have hyq : y - q = (t - s) • (b - a) := by
    rw [← hs, ← ht]
    module
  rw [hyq, mul_smul_comm, Complex.smul_im]
  have hzero : (star (b - a) * (b - a)).im = 0 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    exact Complex.ofReal_im _
  rw [hzero, smul_zero]

/-- Helper toward Definition 5.8: on the side selected by a nearest
interior contact, an entire sufficiently small open half-disk belongs to the
contacted face. This is a local statement at the contact, not yet transport to
the initial segment of a dart. -/
theorem face_nearest_openSegment_halfDisk (hvert : Function.Surjective vert)
    (K : P.Face) (z q : ℂ) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hzq : z ≠ q) (hball : ball z (dist z q) ⊆ K.val)
    (hmin : ∀ y ∈ P.image, dist z q ≤ dist z y) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball q r,
      0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (z - q)).im *
        (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (y - q)).im →
      y ∈ K.val := by
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let u := b - a
  let c : ℂ → ℝ := fun y => (star u * (y - q)).im
  have hc : c z ≠ 0 := segment_nearest_side_ne_zero a b z q
    ((P.arc_simple d).1 i hi) hzq hq (fun y hy =>
      hmin y (Or.inr ⟨d, (P.arc d).segmentAt_subset_image hi hy⟩))
  obtain ⟨r, hr, hlocal⟩ := P.openSegment_contact_local_image hvert d hi hq
  let N := ‖z - q‖
  have hN : 0 < N := norm_pos_iff.mpr (sub_ne_zero.mpr hzq)
  let t := min (1 / 2 : ℝ) (r / (2 * (N + 1)))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hr (by positivity))
  have ht1 : t < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have htr : t * (2 * (N + 1)) ≤ r :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have htN : t * N < r := by nlinarith only [htr, ht, hN]
  let w := q + t • (z - q)
  have hwq : w - q = t • (z - q) := by dsimp [w]; abel
  have hwz : w - z = (t - 1) • (z - q) := by
    rw [sub_smul, one_smul]
    dsimp only [w]
    abel
  have hwball : w ∈ ball q r := by
    rw [mem_ball, dist_eq_norm, hwq, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact htN
  have hwK : w ∈ K.val := by
    apply hball
    rw [mem_ball, dist_eq_norm, hwz, norm_smul, Real.norm_eq_abs,
      abs_of_neg (sub_neg.mpr ht1), dist_eq_norm]
    change -(t - 1) * N < N
    nlinarith only [ht, hN]
  have hcw : c w = t * c z := by
    dsimp [c]
    rw [hwq, mul_smul_comm, Complex.smul_im]
    rfl
  have hwside : 0 < c z * c w := by
    rw [hcw]
    nlinarith only [sq_pos_of_ne_zero hc, ht]
  refine ⟨r, hr, ?_⟩
  intro y hyr hyc
  have hsegball : segment ℝ w y ⊆ ball q r :=
    (convex_ball q r).segment_subset hwball hyr
  have hsegcompl : segment ℝ w y ⊆ P.imageᶜ := by
    intro x hx hximage
    have hxseg := hlocal x (hsegball hx) hximage
    have hcx : c x = 0 := segment_contact_side_eq_zero a b q x
      (openSegment_subset_segment ℝ a b hq) hxseg
    rw [segment_eq_image'] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    have hcombo : c (w + s • (y - w)) = (1 - s) * c w + s * c y := by
      change (star u * (w + s • (y - w) - q)).im =
        (1 - s) * (star u * (w - q)).im + s * (star u * (y - q)).im
      have heq : w + s • (y - w) - q =
          (1 - s) • (w - q) + s • (y - q) := by module
      rw [heq, mul_add, mul_smul_comm, mul_smul_comm, Complex.add_im,
        Complex.smul_im, Complex.smul_im]
      rfl
    have hpos : 0 < c z * c (w + s • (y - w)) := by
      rw [hcombo]
      by_cases hs0 : s = 0
      · simpa only [hs0, sub_zero, one_mul, zero_mul, add_zero] using hwside
      · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
        have hsum := add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr hs.2) hwside.le) (mul_pos hspos hyc)
        nlinarith only [hsum]
    rw [hcx, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hpre : IsPreconnected (segment ℝ w y) := by
    rw [segment_eq_image']
    exact isPreconnected_Icc.image _ (by fun_prop)
  obtain ⟨x, _, hK⟩ := K.property
  rw [hK] at hwK ⊢
  rw [connectedComponentIn_eq hwK]
  exact hpre.subset_connectedComponentIn (left_mem_segment ℝ w y)
    hsegcompl (right_mem_segment ℝ w y)

/-- Helper toward Definition 5.8: a left open half-disk contains a uniform
left wedge. The independent wedge parameters are controlled by continuity at
their common zero, rather than by a radius depending on their ratio. -/
theorem wedgeIn_of_left_halfDisk (q u : ℂ) (hu : u ≠ 0) (S : Set ℂ)
    (r : ℝ) (hr : 0 < r)
    (hS : ∀ y ∈ ball q r, 0 < (star u * (y - q)).im → y ∈ S) :
    WedgeIn q u S := by
  let f : ℝ × ℝ → ℂ := fun x => wedgePoint q u x.1 x.2
  have hf : Continuous f := by dsimp [f, wedgePoint]; fun_prop
  have hf0 : f (0, 0) = q := by simp only [f, wedgePoint, Complex.ofReal_zero, zero_mul, add_zero]
  have hnhds : f ⁻¹' ball q r ∈ 𝓝 (0, 0) := by
    apply hf.continuousAt.preimage_mem_nhds
    rw [hf0]
    exact ball_mem_nhds q hr
  obtain ⟨δ, hδ, hfball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ, hδ, ?_⟩
  intro t eps ht htd he hed
  apply hS
  · change (t, eps) ∈ f ⁻¹' ball q r
    apply hfball
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ht, abs_of_pos he] using And.intro htd hed
  · have hcross : (star u * (wedgePoint q u t eps - q)).im =
        t * eps * Complex.normSq u := by
      simp only [wedgePoint, add_sub_cancel_left, Complex.star_def,
        Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.add_re, Complex.add_im, Complex.normSq_apply]
      ring
    rw [hcross]
    exact mul_pos (mul_pos ht he) (Complex.normSq_pos.mpr hu)

/-- Helper toward Definition 5.8: an interior nearest contact selects the
left wedge of the segment direction or its negative, according to its nonzero
oriented side. These wedges are based at the contact point. -/
theorem face_nearest_openSegment_wedge (hvert : Function.Surjective vert)
    (K : P.Face) (z q : ℂ) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hzq : z ≠ q) (hball : ball z (dist z q) ⊆ K.val)
    (hmin : ∀ y ∈ P.image, dist z q ≤ dist z y) :
    let u := (P.arc d).point (i + 1) - (P.arc d).point i
    (0 < (star u * (z - q)).im ∧ WedgeIn q u K.val) ∨
      ((star u * (z - q)).im < 0 ∧ WedgeIn q (-u) K.val) := by
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let u := b - a
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  have hc : (star u * (z - q)).im ≠ 0 :=
    segment_nearest_side_ne_zero a b z q ((P.arc_simple d).1 i hi) hzq hq
      (fun y hy => hmin y (Or.inr ⟨d, (P.arc d).segmentAt_subset_image hi hy⟩))
  obtain ⟨r, hr, hside⟩ := P.face_nearest_openSegment_halfDisk hvert K z q d hi hq hzq hball hmin
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · refine Or.inr ⟨hneg, wedgeIn_of_left_halfDisk q (-u) (neg_ne_zero.mpr hu) K.val r hr ?_⟩
    intro y hyr hy
    apply hside y hyr
    have hcy : (star u * (y - q)).im < 0 := by
      simpa only [star_neg, neg_mul, Complex.neg_im, neg_pos] using hy
    exact mul_pos_of_neg_of_neg hneg hcy
  · refine Or.inl ⟨hpos, wedgeIn_of_left_halfDisk q u hu K.val r hr ?_⟩
    intro y hyr hy
    exact hside y hyr (mul_pos hpos hy)

/-- Helper toward Definition 5.8: every face has a nearest segment contact
which is either a segment endpoint or supports a uniform left wedge of one of
the two segment orientations. All original nearest-contact conclusions are
retained; no coverage or bordering premise is added. -/
theorem face_nearest_segment_contact_or_wedge (hvert : Function.Surjective vert)
    (d₀ : D) (K : P.Face) (z : ℂ) (hz : z ∈ K.val) :
    ∃ (q : ℂ) (d : D) (i : ℕ),
      i + 1 < (P.arc d).points.length ∧
      q ∈ (P.arc d).segmentAt i ∧ q ∈ frontier K.val ∧
      0 < dist z q ∧ ball z (dist z q) ⊆ K.val ∧
      (∀ y ∈ P.image, dist z q ≤ dist z y) ∧
      (q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1) ∨
        let u := (P.arc d).point (i + 1) - (P.arc d).point i
        (0 < (star u * (z - q)).im ∧ WedgeIn q u K.val) ∨
          ((star u * (z - q)).im < 0 ∧ WedgeIn q (-u) K.val)) := by
  classical
  obtain ⟨q, d, i, hi, hqi, hqfront, hr, hball, hmin⟩ :=
    P.face_nearest_segment_contact hvert d₀ K z hz
  refine ⟨q, d, i, hi, hqi, hqfront, hr, hball, hmin, ?_⟩
  by_cases hleft : q = (P.arc d).point i
  · exact Or.inl hleft
  by_cases hright : q = (P.arc d).point (i + 1)
  · exact Or.inr (Or.inl hright)
  have hqopen := mem_openSegment_of_ne_left_right (Ne.symm hleft) (Ne.symm hright) hqi
  exact Or.inr (Or.inr (P.face_nearest_openSegment_wedge hvert K z q d hi hqopen
    (dist_pos.mp hr) hball hmin))

/-- Helper toward Definition 5.8: a compact subsegment of an open drawing
segment has one uniform neighborhood in which no other drawing segment occurs.
The radius is proved from compactness and the local isolation theorem. -/
theorem openSegment_contact_uniform_local_image (hvert : Function.Surjective vert)
    (d : D) {i : ℕ} (hi : i + 1 < (P.arc d).points.length) (q₁ q₂ : ℂ)
    (hq₁ : q₁ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hq₂ : q₂ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ segment ℝ q₁ q₂,
      ∀ y ∈ ball q r, y ∈ P.image → y ∈ (P.arc d).segmentAt i := by
  let U := interior (P.imageᶜ ∪ (P.arc d).segmentAt i)
  have hsub : segment ℝ q₁ q₂ ⊆ U := by
    intro q hq
    have hqo := (convex_openSegment _ _).segment_subset hq₁ hq₂ hq
    obtain ⟨r, hr, hlocal⟩ := P.openSegment_contact_local_image hvert d hi hqo
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (ball_mem_nhds q hr)
    intro y hy
    by_cases hyP : y ∈ P.image
    · exact Or.inr (hlocal y hy hyP)
    · exact Or.inl hyP
  have hcompact : IsCompact (segment ℝ q₁ q₂) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  have hdisj : Disjoint (segment ℝ q₁ q₂) Uᶜ :=
    disjoint_compl_right.mono_left hsub
  obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist
    hcompact isOpen_interior.isClosed_compl hdisj
  refine ⟨r, by exact_mod_cast hr, ?_⟩
  intro q hq y hy hyP
  have hyU : y ∈ U := by
    by_contra hyU
    have hlt : edist q y < (r : ENNReal) := by
      rw [edist_lt_coe, ← dist_lt_coe, dist_comm]
      exact hy
    exact (not_lt_of_gt (hsep q hq y hyU)) hlt
  exact (interior_subset hyU).resolve_left (fun h => h hyP)

/-- Helper toward Definition 5.8: within a ball meeting the drawing only
on one supporting segment, one point on a chosen side determines the face of
the entire open half-disk on that side. No nearest-point premise is needed. -/
theorem face_halfDisk_of_local_image (K : P.Face) (a b q w : ℂ) (r s : ℝ)
    (hq : q ∈ segment ℝ a b) (hw : w ∈ K.val) (hwr : w ∈ ball q r)
    (hwside : 0 < s * (star (b - a) * (w - q)).im)
    (hlocal : ∀ y ∈ ball q r, y ∈ P.image → y ∈ segment ℝ a b) :
    ∀ y ∈ ball q r, 0 < s * (star (b - a) * (y - q)).im → y ∈ K.val := by
  intro y hyr hyside
  let c : ℂ → ℝ := fun x => s * (star (b - a) * (x - q)).im
  have hsegball : segment ℝ w y ⊆ ball q r :=
    (convex_ball q r).segment_subset hwr hyr
  have hsafe : segment ℝ w y ⊆ P.imageᶜ := by
    intro x hx hxP
    have hcx : c x = 0 := by
      dsimp only [c]
      rw [segment_contact_side_eq_zero a b q x hq (hlocal x (hsegball hx) hxP),
        mul_zero]
    rw [segment_eq_image'] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have heq : c (w + t • (y - w)) = (1 - t) * c w + t * c y := by
      have heq : w + t • (y - w) - q =
          (1 - t) • (w - q) + t • (y - q) := by module
      dsimp only [c]
      rw [heq, mul_add, mul_smul_comm, mul_smul_comm, Complex.add_im,
        Complex.smul_im, Complex.smul_im]
      ring
    have hpos : 0 < c (w + t • (y - w)) := by
      rw [heq]
      by_cases ht0 : t = 0
      · simpa only [ht0, sub_zero, one_mul, zero_mul, add_zero] using hwside
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr ht.2) hwside.le)
          (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hyside)
    exact (ne_of_gt hpos) hcx
  have hpre : IsPreconnected (segment ℝ w y) := by
    rw [segment_eq_image']
    exact isPreconnected_Icc.image _ (by fun_prop)
  obtain ⟨x, _, hK⟩ := K.property
  rw [hK] at hw ⊢
  rw [connectedComponentIn_eq hw]
  exact hpre.subset_connectedComponentIn (left_mem_segment ℝ w y)
    hsafe (right_mem_segment ℝ w y)

/-- Helper toward Definition 5.8: normal translation from any point on a
segment has the expected signed cross product, independently of the base
point chosen on that segment. -/
theorem segment_normal_offset_side (a b q x : ℂ) (t : ℝ)
    (hq : q ∈ segment ℝ a b) (hx : x ∈ segment ℝ a b) :
    (star (b - a) * (x + t • (Complex.I * (b - a)) - q)).im =
      t * Complex.normSq (b - a) := by
  have heq : x + t • (Complex.I * (b - a)) - q =
      (x - q) + t • (Complex.I * (b - a)) := by module
  rw [heq, mul_add, mul_smul_comm, Complex.add_im, Complex.smul_im,
    segment_contact_side_eq_zero a b q x hq hx, zero_add]
  congr 1
  simp only [Complex.star_def, Complex.mul_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.normSq_apply]
  ring

/-- Helper toward Definition 5.8: a compact part of an open drawing
segment admits uniform thin normal strips on both sides, entirely avoiding
the drawing. The strip width is proved, rather than supplied as a premise. -/
theorem openSegment_normal_strip_compl (hvert : Function.Surjective vert)
    (d : D) {i : ℕ} (hi : i + 1 < (P.arc d).points.length) (q₁ q₂ : ℂ)
    (hq₁ : q₁ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hq₂ : q₂ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ segment ℝ q₁ q₂, ∀ t : ℝ,
      0 < |t| → |t| < δ →
      q + t • (Complex.I * ((P.arc d).point (i + 1) - (P.arc d).point i)) ∉ P.image := by
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let u := b - a
  let v := Complex.I * u
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  obtain ⟨r, hr, hlocal⟩ :=
    P.openSegment_contact_uniform_local_image hvert d hi q₁ q₂ hq₁ hq₂
  let δ := r / (2 * (‖v‖ + 1))
  have hden : 0 < 2 * (‖v‖ + 1) := by positivity
  refine ⟨δ, div_pos hr hden, ?_⟩
  intro q hq t ht htd hP
  have hprod : |t| * (2 * (‖v‖ + 1)) < r := (lt_div_iff₀ hden).mp htd
  have hball : q + t • v ∈ ball q r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    nlinarith only [hprod, ht, norm_nonneg v]
  have hseg : q + t • v ∈ segment ℝ a b := hlocal q hq _ hball hP
  have hqseg : q ∈ segment ℝ a b := openSegment_subset_segment ℝ a b
    ((convex_openSegment a b).segment_subset hq₁ hq₂ hq)
  have hzero := segment_contact_side_eq_zero a b q (q + t • v) hqseg hseg
  have hnormal := segment_normal_offset_side a b q q t hqseg hqseg
  have hnonzero : t * Complex.normSq u ≠ 0 :=
    mul_ne_zero (abs_pos.mp ht) (ne_of_gt (Complex.normSq_pos.mpr hu))
  exact hnonzero (hnormal.symm.trans hzero)

/-- Helper toward Definition 5.8: the normal side selected by an interior
nearest contact remains in the same face along every compact subsegment of
that open segment. The normal direction includes the signed contact test. -/
theorem face_nearest_openSegment_normal_strip (hvert : Function.Surjective vert)
    (K : P.Face) (z q₁ q₂ : ℂ) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hq₁ : q₁ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hq₂ : q₂ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hzq : z ≠ q₁) (hball : ball z (dist z q₁) ⊆ K.val)
    (hmin : ∀ y ∈ P.image, dist z q₁ ≤ dist z y) :
    let u := (P.arc d).point (i + 1) - (P.arc d).point i
    let c := (star u * (z - q₁)).im
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ segment ℝ q₁ q₂, ∀ t : ℝ,
      0 < t → t < δ → q + t • (c • (Complex.I * u)) ∈ K.val := by
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let u := b - a
  let c := (star u * (z - q₁)).im
  let v := c • (Complex.I * u)
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  have hc : c ≠ 0 := segment_nearest_side_ne_zero a b z q₁
    ((P.arc_simple d).1 i hi) hzq hq₁ (fun y hy =>
      hmin y (Or.inr ⟨d, (P.arc d).segmentAt_subset_image hi hy⟩))
  obtain ⟨r, hr, hhalf⟩ :=
    P.face_nearest_openSegment_halfDisk hvert K z q₁ d hi hq₁ hzq hball hmin
  obtain ⟨δ₀, hδ₀, hstrip⟩ :=
    P.openSegment_normal_strip_compl hvert d hi q₁ q₂ hq₁ hq₂
  let δ := min (δ₀ / (|c| + 1)) (r / (2 * (‖v‖ + 1)))
  have hδ : 0 < δ := lt_min (div_pos hδ₀ (by positivity)) (div_pos hr (by positivity))
  have hscaled (t : ℝ) (ht : 0 < t) (htd : t < δ) : |t * c| < δ₀ := by
    have hprod : t * (|c| + 1) < δ₀ :=
      (lt_div_iff₀ (by positivity)).mp (htd.trans_le (min_le_left _ _))
    rw [abs_mul, abs_of_pos ht]
    linarith only [hprod, ht]
  have hbase (t : ℝ) (ht : 0 < t) (htd : t < δ) : q₁ + t • v ∈ K.val := by
    apply hhalf
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht]
      have hprod : t * (2 * (‖v‖ + 1)) < r :=
        (lt_div_iff₀ (by positivity)).mp (htd.trans_le (min_le_right _ _))
      nlinarith only [hprod, ht, norm_nonneg v]
    · have hqseg := openSegment_subset_segment ℝ a b hq₁
      change 0 < c * (star u * (q₁ + t • v - q₁)).im
      dsimp only [v]
      rw [smul_smul, segment_normal_offset_side a b q₁ q₁ (t * c) hqseg hqseg]
      have hpos := mul_pos (mul_pos ht (sq_pos_of_ne_zero hc))
        (Complex.normSq_pos.mpr hu)
      nlinarith only [hpos]
  let f : ℂ × ℝ → ℂ := fun p => p.1 + p.2 • v
  let S := f '' (segment ℝ q₁ q₂ ×ˢ Ioo 0 δ)
  have hsegpre : IsPreconnected (segment ℝ q₁ q₂) := by
    rw [segment_eq_image']
    exact isPreconnected_Icc.image _ (by fun_prop)
  have hpre : IsPreconnected S :=
    (hsegpre.prod isPreconnected_Ioo).image f (by dsimp [f]; fun_prop)
  have hsafe : S ⊆ P.imageᶜ := by
    rintro y ⟨⟨q, t⟩, ⟨hq, ht⟩, rfl⟩
    change q + t • v ∉ P.image
    dsimp only [v]
    rw [smul_smul]
    exact hstrip q hq (t * c) (abs_pos.mpr (mul_ne_zero ht.1.ne' hc))
      (hscaled t ht.1 ht.2)
  let w := q₁ + (δ / 2) • v
  have hwS : w ∈ S := ⟨(q₁, δ / 2),
    ⟨left_mem_segment ℝ q₁ q₂, half_pos hδ, half_lt_self hδ⟩, rfl⟩
  have hwK : w ∈ K.val := hbase (δ / 2) (half_pos hδ) (half_lt_self hδ)
  have hSK : S ⊆ K.val := by
    obtain ⟨x, _, hK⟩ := K.property
    rw [hK] at hwK ⊢
    rw [connectedComponentIn_eq hwK]
    exact hpre.subset_connectedComponentIn hwS hsafe
  refine ⟨δ, hδ, ?_⟩
  intro q hq t ht htd
  exact hSK ⟨(q, t), ⟨hq, ht, htd⟩, rfl⟩

/-- Helper toward Definition 5.8: the half-disk side of an interior nearest
contact transports to every other open point of that same drawing segment.
Both contact-side signs are retained in the conclusion. -/
theorem face_nearest_openSegment_halfDisk_transport (hvert : Function.Surjective vert)
    (K : P.Face) (z q₁ q₂ : ℂ) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hq₁ : q₁ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hq₂ : q₂ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hzq : z ≠ q₁) (hball : ball z (dist z q₁) ⊆ K.val)
    (hmin : ∀ y ∈ P.image, dist z q₁ ≤ dist z y) :
    let u := (P.arc d).point (i + 1) - (P.arc d).point i
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball q₂ r,
      0 < (star u * (z - q₁)).im * (star u * (y - q₂)).im → y ∈ K.val := by
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let u := b - a
  let c := (star u * (z - q₁)).im
  let v := c • (Complex.I * u)
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  have hc : c ≠ 0 := segment_nearest_side_ne_zero a b z q₁
    ((P.arc_simple d).1 i hi) hzq hq₁ (fun y hy =>
      hmin y (Or.inr ⟨d, (P.arc d).segmentAt_subset_image hi hy⟩))
  obtain ⟨δ, hδ, hstrip⟩ := P.face_nearest_openSegment_normal_strip
    hvert K z q₁ q₂ d hi hq₁ hq₂ hzq hball hmin
  obtain ⟨r, hr, hlocal⟩ := P.openSegment_contact_local_image hvert d hi hq₂
  let t := min (δ / 2) (r / (2 * (‖v‖ + 1)))
  have ht : 0 < t := lt_min (half_pos hδ) (div_pos hr (by positivity))
  have htd : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  let w := q₂ + t • v
  have hwK : w ∈ K.val := hstrip q₂ (right_mem_segment ℝ q₁ q₂) t ht htd
  have hwr : w ∈ ball q₂ r := by
    rw [mem_ball, dist_eq_norm]
    change ‖q₂ + t • v - q₂‖ < r
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hprod : t * (2 * (‖v‖ + 1)) ≤ r :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith only [hprod, ht, norm_nonneg v]
  have hqseg := openSegment_subset_segment ℝ a b hq₂
  have hwside : 0 < c * (star u * (w - q₂)).im := by
    change 0 < c * (star u * (q₂ + t • (c • (Complex.I * u)) - q₂)).im
    rw [smul_smul, segment_normal_offset_side a b q₂ q₂ (t * c) hqseg hqseg]
    have hpos := mul_pos (mul_pos ht (sq_pos_of_ne_zero hc))
      (Complex.normSq_pos.mpr hu)
    nlinarith only [hpos]
  exact ⟨r, hr, P.face_halfDisk_of_local_image K a b q₂ w r c
    hqseg hwK hwr hwside hlocal⟩

/-- Helper toward Definition 5.8: the selected left wedge transports
between all open points of one drawing segment, without a new minimization
assumption at the destination point. -/
theorem face_nearest_openSegment_wedge_transport (hvert : Function.Surjective vert)
    (K : P.Face) (z q₁ q₂ : ℂ) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hq₁ : q₁ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hq₂ : q₂ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hzq : z ≠ q₁) (hball : ball z (dist z q₁) ⊆ K.val)
    (hmin : ∀ y ∈ P.image, dist z q₁ ≤ dist z y) :
    let u := (P.arc d).point (i + 1) - (P.arc d).point i
    (0 < (star u * (z - q₁)).im ∧ WedgeIn q₂ u K.val) ∨
      ((star u * (z - q₁)).im < 0 ∧ WedgeIn q₂ (-u) K.val) := by
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let u := b - a
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  have hc : (star u * (z - q₁)).im ≠ 0 :=
    segment_nearest_side_ne_zero a b z q₁ ((P.arc_simple d).1 i hi) hzq hq₁
      (fun y hy => hmin y (Or.inr ⟨d, (P.arc d).segmentAt_subset_image hi hy⟩))
  obtain ⟨r, hr, hhalf⟩ := P.face_nearest_openSegment_halfDisk_transport
    hvert K z q₁ q₂ d hi hq₁ hq₂ hzq hball hmin
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · refine Or.inr ⟨hneg, wedgeIn_of_left_halfDisk q₂ (-u) (neg_ne_zero.mpr hu) K.val r hr ?_⟩
    intro y hyr hy
    have hcy : (star u * (y - q₂)).im < 0 := by
      simpa only [star_neg, neg_mul, Complex.neg_im, neg_pos] using hy
    exact hhalf y hyr (mul_pos_of_neg_of_neg hneg hcy)
  · refine Or.inl ⟨hpos, wedgeIn_of_left_halfDisk q₂ u hu K.val r hr ?_⟩
    intro y hyr hy
    exact hhalf y hyr (mul_pos hpos hy)

/-- Helper toward Definition 5.8: an internal vertex of a simple polyline
belongs only to its two incident segments. Collinear subdivisions are allowed. -/
theorem bend_contact_index (p : Polyline) (hp : p.IsSimple)
    {i j : ℕ} (hi : i + 2 < p.points.length) (hj : j + 1 < p.points.length)
    (hq : p.point (i + 1) ∈ p.segmentAt j) : j = i ∨ j = i + 1 := by
  have hleft : p.point (i + 1) ∈ p.segmentAt i := right_mem_segment ℝ _ _
  have hright : p.point (i + 1) ∈ p.segmentAt (i + 1) := left_mem_segment ℝ _ _
  by_cases hji : j < i
  · exact ((Set.disjoint_left.mp (hp.2.2 j (i + 1) hj (by omega) (by omega)))
      hq hright).elim
  by_cases hij : i + 1 < j
  · exact ((Set.disjoint_left.mp (hp.2.2 i j (by omega) hj hij)) hleft hq).elim
  omega

/-- Helper toward Definition 5.8: an internal polyline vertex is an
interior point of the edge trace, rather than a graph endpoint. -/
theorem bend_contact_mem_interior (p : Polyline) (hp : p.IsSimple)
    {i : ℕ} (hi : i + 2 < p.points.length) : p.point (i + 1) ∈ p.interior := by
  have hleft : p.point (i + 1) ∈ p.segmentAt i := right_mem_segment ℝ _ _
  have hright : p.point (i + 1) ∈ p.segmentAt (i + 1) := left_mem_segment ℝ _ _
  have hstart : p.point (i + 1) ≠ p.start := by
    intro he
    have hzero : p.point (i + 1) ∈ p.segmentAt 0 := by
      rw [he]
      change p.start ∈ segment ℝ (p.point 0) (p.point 1)
      rw [p.point_zero_eq_start]
      exact left_mem_segment ℝ _ _
    have hidx := bend_contact_index p hp hi (by omega) hzero
    have hi0 : i = 0 := by omega
    subst i
    exact (hp.1 0 (by omega)) (by simpa only [p.point_zero_eq_start] using he.symm)
  have hfinish : p.point (i + 1) ≠ p.finish := by
    intro he
    let j := p.points.length - 2
    have hj : j + 1 < p.points.length := by dsimp [j]; omega
    have hlast : j + 1 = p.points.length - 1 := by dsimp [j]; omega
    have hseg : p.point (i + 1) ∈ p.segmentAt j := by
      rw [he]
      change p.finish ∈ segment ℝ (p.point j) (p.point (j + 1))
      rw [hlast, p.point_last_eq_finish]
      exact right_mem_segment ℝ _ _
    have hidx := bend_contact_index p hp hi hj hseg
    have hji : j = i + 1 := by dsimp [j] at *; omega
    have he' : p.point (i + 1) = p.point (i + 1 + 1) := by
      calc
        p.point (i + 1) = p.finish := he
        _ = p.point (i + 1 + 1) := by rw [← hji, hlast, p.point_last_eq_finish]
    exact hp.1 (i + 1) (by omega) he'
  exact ⟨p.segmentAt_subset_image (by omega) hleft, by
    simpa only [mem_insert_iff, mem_singleton_iff, not_or] using And.intro hstart hfinish⟩

/-- Helper toward Definition 5.8: a sufficiently small ball at any
internal polyline vertex meets the whole drawing precisely on its two
incident segments. This includes straight subdivisions and excludes every
other arc using local finiteness and disjoint edge interiors. -/
theorem bend_contact_local_image (hvert : Function.Surjective vert)
    (d : D) {i : ℕ} (hi : i + 2 < (P.arc d).points.length) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball ((P.arc d).point (i + 1)) r,
      y ∈ P.image ↔ y ∈ (P.arc d).segmentAt i ∪ (P.arc d).segmentAt (i + 1) := by
  classical
  let p := P.arc d
  let q := p.point (i + 1)
  have hqint : q ∈ p.interior := bend_contact_mem_interior p (P.arc_simple d) hi
  have hqpos (v : V) : q ≠ P.pos v := by
    intro he
    exact P.interior_avoids_vertices d v (he ▸ hqint)
  have hqother (e : D) (hed : e ≠ d) (heflip : e ≠ flip d) :
      q ∉ (P.arc e).image := by
    intro hqe
    have hqeint : q ∈ (P.arc e).interior := by
      refine ⟨hqe, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun he => hqpos (vert e) (he.trans (P.arc_start e)),
        fun he => hqpos (vert (flip e)) (he.trans (P.arc_finish e))⟩
    exact (Set.disjoint_left.mp (P.interior_disjoint d e hed heflip)) hqint hqeint
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
  let J := Fin (p.points.length - 1)
  let S : J → Set ℂ := fun j =>
    if j.val = i ∨ j.val = i + 1 then ∅ else p.segmentAt j.val
  have hSclosed : IsClosed (⋃ j, S j) := by
    apply (locallyFinite_of_finite S).isClosed_iUnion
    intro j
    dsimp [S]
    split_ifs
    · exact isClosed_empty
    · change IsClosed (segment ℝ _ _)
      rw [segment_eq_image']
      exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hqS : q ∉ ⋃ j, S j := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    dsimp [S] at hj
    split_ifs at hj with heq
    · exact notMem_empty q hj
    · exact heq (bend_contact_index p (P.arc_simple d) hi
        (by have := j.isLt; omega) hj)
  let E : Set ℂ := (⋃ e, B e) ∪ (⋃ j, S j) ∪ {p.start}
  have hEclosed : IsClosed E := (hBclosed.union hSclosed).union isClosed_singleton
  have hqE : q ∉ E := by
    rintro ((he | hj) | hs)
    · exact hqB he
    · exact hqS hj
    · exact hqint.2 (Or.inl hs)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hEclosed.isOpen_compl.mem_nhds hqE)
  refine ⟨r, hr, ?_⟩
  intro y hyr
  constructor
  · intro hy
    have hyE : y ∉ E := hball hyr
    rw [P.image_eq_union_arcs hvert] at hy
    obtain ⟨e, he⟩ := mem_iUnion.mp hy
    have hyp : y ∈ p.image := by
      by_cases hed : e = d
      · simpa only [hed] using he
      by_cases heflip : e = flip d
      · rw [heflip, P.arc_flip d, Polyline.image_reverse_transfer] at he
        exact he
      · exact (hyE (Or.inl (Or.inl (mem_iUnion.mpr
          ⟨e, by simpa only [B, ite_eq_right (not_or.mpr ⟨hed, heflip⟩)] using he⟩)))).elim
    rcases hyp with hs | ⟨j, hj, hyj⟩
    · exact (hyE (Or.inr hs)).elim
    · by_cases hji : j = i ∨ j = i + 1
      · rcases hji with rfl | rfl
        · exact Or.inl hyj
        · exact Or.inr hyj
      · exact (hyE (Or.inl (Or.inr (mem_iUnion.mpr
          ⟨⟨j, by omega⟩, by simpa only [S, ite_eq_right hji] using hyj⟩)))).elim
  · rintro (hy | hy)
    · exact Or.inr ⟨d, p.segmentAt_subset_image (by dsimp [p]; omega) hy⟩
    · exact Or.inr ⟨d, p.segmentAt_subset_image (by dsimp [p]; omega) hy⟩

/-- Helper toward Definition 5.8: consecutive collinear segments of a
simple polyline point in the same direction. Reversal would overlap the two
closed segments away from their common vertex. -/
theorem bend_collinear_inner_pos (p : Polyline) (hp : p.IsSimple)
    {i : ℕ} (hi : i + 2 < p.points.length)
    (hcross : (star (p.point (i + 1) - p.point i) *
      (p.point (i + 2) - p.point (i + 1))).im = 0) :
    0 < (star (p.point (i + 1) - p.point i) *
      (p.point (i + 2) - p.point (i + 1))).re := by
  let a := p.point i
  let b := p.point (i + 1)
  let c := p.point (i + 2)
  let u := b - a
  let v := c - b
  let k := (star u * v).re
  have hu : u ≠ 0 := sub_ne_zero.mpr (hp.1 i (by omega)).symm
  have hv : v ≠ 0 := sub_ne_zero.mpr (hp.1 (i + 1) (by omega)).symm
  have hn : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  have hprod : star u * v = (k : ℂ) := Complex.ext rfl hcross
  have hk : k ≠ 0 := by
    intro hk
    rw [hk, Complex.ofReal_zero] at hprod
    exact mul_ne_zero (star_ne_zero.mpr hu) hv hprod
  by_contra hpos
  have hkneg : k < 0 := lt_of_le_of_ne (not_lt.mp hpos) hk
  let α := k / Complex.normSq u
  have hα : α < 0 := div_neg_of_neg_of_pos hkneg hn
  have hvu : v = α • u := by
    apply mul_left_cancel₀ (star_ne_zero.mpr hu)
    rw [hprod, mul_smul_comm, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self]
    apply Complex.ext <;>
      simp only [Complex.smul_re, Complex.smul_im, Complex.ofReal_re,
        Complex.ofReal_im, smul_eq_mul, mul_zero]
    dsimp [α]
    exact (div_mul_cancel₀ k hn.ne').symm
  let t := 1 / (1 - α)
  have ht : 0 < t := div_pos zero_lt_one (by linarith only [hα])
  have ht1 : t < 1 := (div_lt_one (by linarith only [hα])).mpr (by linarith only [hα])
  have htα : 1 + t * α = t := by
    have hd : 1 - α ≠ 0 := ne_of_gt (by linarith only [hα])
    dsimp [t]
    field_simp [hd]
    ring
  have heq : b + t • v = a + t • u := by
    rw [hvu, smul_smul]
    have hba : b = a + u := by dsimp [u]; abel
    calc
      b + (t * α) • u = a + (1 + t * α) • u := by rw [hba]; module
      _ = a + t • u := by rw [htα]
  have hleft : b + t • v ∈ p.segmentAt i := by
    change b + t • v ∈ segment ℝ a b
    rw [heq, segment_eq_image']
    exact ⟨t, ⟨ht.le, ht1.le⟩, rfl⟩
  have hright : b + t • v ∈ p.segmentAt (i + 1) := by
    change b + t • v ∈ segment ℝ b c
    rw [segment_eq_image']
    exact ⟨t, ⟨ht.le, ht1.le⟩, rfl⟩
  have hmeet : b + t • v = b := by
    have hm : b + t • v ∈ p.segmentAt i ∩ p.segmentAt (i + 1) := ⟨hleft, hright⟩
    rw [hp.2.1 i hi] at hm
    exact hm
  have hz : t • v = 0 := by simpa only [add_eq_left] using hmeet
  exact (smul_ne_zero ht.ne' hv) hz

/-- Helper toward Definition 5.8: a signed open half-disk is convex. -/
theorem signed_halfDisk_convex (q u : ℂ) (r s : ℝ) :
    Convex ℝ {y : ℂ | y ∈ ball q r ∧ 0 < s * (star u * (y - q)).im} := by
  have hlinear : IsLinearMap ℝ (fun y : ℂ => s * (star u * y).im) := by
    constructor
    · intro x y
      simp only [mul_add, Complex.add_im]
    · intro t y
      rw [mul_smul_comm, Complex.smul_im]
      change s * (t * (star u * y).im) = t * (s * (star u * y).im)
      ring
  have hc := (convex_halfSpace_gt hlinear 0).translate_preimage_left (-q)
  change Convex ℝ (ball q r ∩
    (fun x : ℂ => x + -q) ⁻¹' {w | 0 < s * (star u * w).im})
  exact (convex_ball q r).inter hc

/-- Helper toward Definition 5.8: signed offsets on the two incident rays
have matching cross products, including the straight subdivision case. -/
theorem bend_offset_sides (u v : ℂ) (s t ε : ℝ) :
    s * (star u * (t • (-u + ε • (s • (Complex.I * u))))).im =
        t * ε * s ^ 2 * Complex.normSq u ∧
    s * (star v * (t • (v + ε • (s • (Complex.I * v))))).im =
        t * ε * s ^ 2 * Complex.normSq v ∧
    s * (star v * (t • (-u + ε • (s • (Complex.I * u))))).im =
        t * (s * (star u * v).im + ε * s ^ 2 * (star u * v).re) ∧
    s * (star u * (t • (v + ε • (s • (Complex.I * v))))).im =
        t * (s * (star u * v).im + ε * s ^ 2 * (star u * v).re) := by
  simp only [Complex.star_def, Complex.mul_im, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
    Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.normSq_apply]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Helper toward Definition 5.8: on either signed side of an internal
polyline vertex there is a preconnected subset of the drawing complement
containing uniform small offsets of both incident rays. The sign is arbitrary
and nonzero, so the same statement gives both left and right transport. -/
theorem bend_contact_side_sector (hvert : Function.Surjective vert)
    (d : D) {i : ℕ} (hi : i + 2 < (P.arc d).points.length)
    (s : ℝ) (hs : s ≠ 0) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ S : Set ℂ, IsPreconnected S ∧ S ⊆ P.imageᶜ ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ,
        0 < t → t < δ → 0 < ε → ε < δ →
        b + t • (-u + ε • (s • (Complex.I * u))) ∈ S ∧
        b + t • (v + ε • (s • (Complex.I * v))) ∈ S := by
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let c := (P.arc d).point (i + 2)
  let u := b - a
  let v := c - b
  let k := s * (star u * v).im
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i (by omega)).symm
  have hv : v ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 (i + 1) (by omega)).symm
  obtain ⟨r, hr, hlocal⟩ := P.bend_contact_local_image hvert d hi
  let A := {y : ℂ | y ∈ ball b r ∧ 0 < s * (star u * (y - b)).im}
  let B := {y : ℂ | y ∈ ball b r ∧ 0 < s * (star v * (y - b)).im}
  have hAc : Convex ℝ A := signed_halfDisk_convex b u r s
  have hBc : Convex ℝ B := signed_halfDisk_convex b v r s
  let f : ℝ × ℝ → ℂ × ℂ := fun x =>
    (b + x.1 • (-u + x.2 • (s • (Complex.I * u))),
      b + x.1 • (v + x.2 • (s • (Complex.I * v))))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hf0 : f (0, 0) = (b, b) := by simp only [f, zero_smul, add_zero]
  have hnh : f ⁻¹' (ball b r ×ˢ ball b r) ∈ 𝓝 (0, 0) := by
    apply hf.continuousAt.preimage_mem_nhds
    rw [hf0]
    exact (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hr, mem_ball_self hr⟩
  obtain ⟨δ₀, hδ₀, hfball⟩ := Metric.mem_nhds_iff.mp hnh
  have hballs (t ε : ℝ) (ht : 0 < t) (htd : t < δ₀)
      (he : 0 < ε) (hed : ε < δ₀) :
      (f (t, ε)).1 ∈ ball b r ∧ (f (t, ε)).2 ∈ ball b r := by
    apply hfball
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ht, abs_of_pos he] using And.intro htd hed
  have hown (t ε : ℝ) (ht : 0 < t) (he : 0 < ε) :
      0 < s * (star u * ((f (t, ε)).1 - b)).im ∧
        0 < s * (star v * ((f (t, ε)).2 - b)).im := by
    dsimp only [f]
    rw [add_sub_cancel_left, add_sub_cancel_left,
      (bend_offset_sides u v s t ε).1, (bend_offset_sides u v s t ε).2.1]
    exact ⟨mul_pos (mul_pos (mul_pos ht he) (sq_pos_of_ne_zero hs))
        (Complex.normSq_pos.mpr hu),
      mul_pos (mul_pos (mul_pos ht he) (sq_pos_of_ne_zero hs))
        (Complex.normSq_pos.mpr hv)⟩
  by_cases hk : 0 ≤ k
  · have hη : ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
        0 < k + ε * s ^ 2 * (star u * v).re := by
      by_cases hk0 : k = 0
      · have hc0 : (star u * v).im = 0 := (mul_eq_zero.mp hk0).resolve_left hs
        have hdot : 0 < (star u * v).re :=
          bend_collinear_inner_pos (P.arc d) (P.arc_simple d) hi hc0
        refine ⟨1, zero_lt_one, ?_⟩
        intro ε he _
        rw [hk0, zero_add]
        exact mul_pos (mul_pos he (sq_pos_of_ne_zero hs)) hdot
      · have hkp : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
        have hcont : Continuous (fun ε : ℝ => k + ε * s ^ 2 * (star u * v).re) := by
          fun_prop
        have hpre : (fun ε : ℝ => k + ε * s ^ 2 * (star u * v).re) ⁻¹' Ioi 0 ∈ 𝓝 0 :=
          hcont.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by simpa using hkp))
        obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp hpre
        refine ⟨η, hη, ?_⟩
        intro ε he heη
        apply hsub
        simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos he] using heη
    obtain ⟨η, hη, hother⟩ := hη
    refine ⟨A ∩ B, (hAc.inter hBc).isPreconnected, ?_, min δ₀ η,
      lt_min hδ₀ hη, ?_⟩
    · intro y hy hyP
      rcases (hlocal y hy.1.1).mp hyP with hleft | hright
      · have hz := segment_contact_side_eq_zero a b b y (right_mem_segment ℝ a b) hleft
        have hp := hy.1.2
        rw [hz, mul_zero] at hp
        exact (lt_irrefl 0) hp
      · have hz := segment_contact_side_eq_zero b c b y (left_mem_segment ℝ b c) hright
        have hp := hy.2.2
        rw [hz, mul_zero] at hp
        exact (lt_irrefl 0) hp
    · intro t ε ht htd he hed
      have hb := hballs t ε ht (htd.trans_le (min_le_left _ _))
        he (hed.trans_le (min_le_left _ _))
      have ho := hown t ε ht he
      have hw := mul_pos ht (hother ε he (hed.trans_le (min_le_right _ _)))
      have hother' :
          0 < s * (star v * ((f (t, ε)).1 - b)).im ∧
            0 < s * (star u * ((f (t, ε)).2 - b)).im := by
        dsimp only [f]
        rw [add_sub_cancel_left, add_sub_cancel_left,
          (bend_offset_sides u v s t ε).2.2.1, (bend_offset_sides u v s t ε).2.2.2]
        exact ⟨hw, hw⟩
      exact ⟨⟨⟨hb.1, ho.1⟩, ⟨hb.1, hother'.1⟩⟩,
        ⟨⟨hb.2, hother'.2⟩, ⟨hb.2, ho.2⟩⟩⟩
  · have hkneg : k < 0 := lt_of_not_ge hk
    let τ := r / (2 * (‖u - v‖ + 1))
    have hτ : 0 < τ := div_pos hr (by positivity)
    let w := b + τ • (u - v)
    have hwr : w ∈ ball b r := by
      rw [mem_ball, dist_eq_norm]
      change ‖b + τ • (u - v) - b‖ < r
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
      have hprod : τ * (2 * (‖u - v‖ + 1)) = r :=
        div_mul_cancel₀ r (by positivity)
      nlinarith only [hprod, hτ, norm_nonneg (u - v)]
    have hwu : s * (star u * (w - b)).im = -τ * k := by
      change s * (star u * (b + τ • (u - v) - b)).im =
        -τ * (s * (star u * v).im)
      simp only [add_sub_cancel_left, Complex.star_def, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.smul_re,
        Complex.smul_im, smul_eq_mul, Complex.sub_re, Complex.sub_im]
      ring
    have hwv : s * (star v * (w - b)).im = -τ * k := by
      change s * (star v * (b + τ • (u - v) - b)).im =
        -τ * (s * (star u * v).im)
      simp only [add_sub_cancel_left, Complex.star_def, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.smul_re,
        Complex.smul_im, smul_eq_mul, Complex.sub_re, Complex.sub_im]
      ring
    have hwpos : 0 < -τ * k := mul_pos_of_neg_of_neg (neg_neg_of_pos hτ) hkneg
    have hwA : w ∈ A := ⟨hwr, hwu.symm ▸ hwpos⟩
    have hwB : w ∈ B := ⟨hwr, hwv.symm ▸ hwpos⟩
    refine ⟨A ∪ B, hAc.isPreconnected.union w hwA hwB hBc.isPreconnected, ?_,
      δ₀, hδ₀, ?_⟩
    · intro y hy hyP
      have hyr : y ∈ ball b r := hy.elim And.left And.left
      rcases (hlocal y hyr).mp hyP with hleft | hright
      · have hzu := segment_contact_side_eq_zero a b b y (right_mem_segment ℝ a b) hleft
        have hzv : s * (star v * (y - b)).im ≤ 0 := by
          change y ∈ segment ℝ a b at hleft
          rw [segment_eq_image'] at hleft
          obtain ⟨t, ht, rfl⟩ := hleft
          have heq : a + t • (b - a) - b = (1 - t) • (-u) := by
            change a + t • (b - a) - b = (1 - t) • (-(b - a))
            module
          rw [heq]
          have hval := (bend_offset_sides u v s (1 - t) 0).2.2.1
          simp only [zero_smul, add_zero, zero_mul] at hval
          rw [hval]
          exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hkneg.le
        rcases hy with hy | hy
        · exact (ne_of_gt hy.2) (by rw [hzu, mul_zero])
        · exact (not_lt_of_ge hzv) hy.2
      · have hzv := segment_contact_side_eq_zero b c b y (left_mem_segment ℝ b c) hright
        have hzu : s * (star u * (y - b)).im ≤ 0 := by
          change y ∈ segment ℝ b c at hright
          rw [segment_eq_image'] at hright
          obtain ⟨t, ht, rfl⟩ := hright
          have hval := (bend_offset_sides u v s t 0).2.2.2
          simp only [zero_smul, add_zero, zero_mul] at hval
          rw [add_sub_cancel_left, hval]
          exact mul_nonpos_of_nonneg_of_nonpos ht.1 hkneg.le
        rcases hy with hy | hy
        · exact (not_lt_of_ge hzu) hy.2
        · exact (ne_of_gt hy.2) (by rw [hzv, mul_zero])
    · intro t ε ht htd he hed
      have hb := hballs t ε ht htd he hed
      have ho := hown t ε ht he
      exact ⟨Or.inl ⟨hb.1, ho.1⟩, Or.inr ⟨hb.2, ho.2⟩⟩

/-- Helper toward Definition 5.8: the signed side of a nearest contact on
the outgoing segment propagates across its preceding bend. Both incident
ray offsets lie in the original face, uniformly in the two positive
parameters; no bordering or sector premise is assumed. -/
theorem face_nearest_openSegment_bend_transport (hvert : Function.Surjective vert)
    (K : P.Face) (z q : ℂ) (d : D) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hq : q ∈ openSegment ℝ ((P.arc d).point (i + 1)) ((P.arc d).point (i + 2)))
    (hzq : z ≠ q) (hball : ball z (dist z q) ⊆ K.val)
    (hmin : ∀ y ∈ P.image, dist z q ≤ dist z y) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    let s := (star v * (z - q)).im
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ,
      0 < t → t < δ → 0 < ε → ε < δ →
      b + t • (-u + ε • (s • (Complex.I * u))) ∈ K.val ∧
      b + t • (v + ε • (s • (Complex.I * v))) ∈ K.val := by
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let c := (P.arc d).point (i + 2)
  let u := b - a
  let v := c - b
  let s := (star v * (z - q)).im
  have hv : v ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 (i + 1) (by omega)).symm
  have hs : s ≠ 0 := segment_nearest_side_ne_zero b c z q
    ((P.arc_simple d).1 (i + 1) (by omega)) hzq hq (fun y hy =>
      hmin y (Or.inr ⟨d, (P.arc d).segmentAt_subset_image (by omega) hy⟩))
  obtain ⟨S, hSpre, hSsafe, δ, hδ, hcorners⟩ :=
    P.bend_contact_side_sector hvert d hi s hs
  let t := min (δ / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
  have htd : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let x := b + t • v
  have hx : x ∈ openSegment ℝ b c := by
    rw [openSegment_eq_image']
    exact ⟨t, ⟨ht, ht1⟩, rfl⟩
  obtain ⟨r, hr, hhalf⟩ := P.face_nearest_openSegment_halfDisk_transport
    hvert K z q x d (by omega) hq hx hzq hball hmin
  let n := t • (s • (Complex.I * v))
  let ε := min (δ / 2) (r / (2 * (‖n‖ + 1)))
  have he : 0 < ε := lt_min (half_pos hδ) (div_pos hr (by positivity))
  have hed : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  let y := b + t • (v + ε • (s • (Complex.I * v)))
  have hyx : y - x = ε • n := by
    change b + t • (v + ε • (s • (Complex.I * v))) - (b + t • v) =
      ε • (t • (s • (Complex.I * v)))
    module
  have hyr : y ∈ ball x r := by
    rw [mem_ball, dist_eq_norm, hyx, norm_smul, Real.norm_eq_abs, abs_of_pos he]
    have hprod : ε * (2 * (‖n‖ + 1)) ≤ r :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith only [hprod, he, norm_nonneg n]
  have hyrepr : y = x + (t * ε * s) • (Complex.I * v) := by
    change b + t • (v + ε • (s • (Complex.I * v))) =
      (b + t • v) + (t * ε * s) • (Complex.I * v)
    module
  have hyside : 0 < s * (star v * (y - x)).im := by
    have hxseg := openSegment_subset_segment ℝ b c hx
    rw [hyrepr, segment_normal_offset_side b c x x (t * ε * s) hxseg hxseg]
    have hpos := mul_pos (mul_pos (mul_pos ht he) (sq_pos_of_ne_zero hs))
      (Complex.normSq_pos.mpr hv)
    nlinarith only [hpos]
  have hyK : y ∈ K.val := hhalf y hyr hyside
  have hyS : y ∈ S := (hcorners t ε ht htd he hed).2
  have hSK : S ⊆ K.val := by
    obtain ⟨x₀, _, hK⟩ := K.property
    rw [hK] at hyK ⊢
    rw [connectedComponentIn_eq hyK]
    exact hSpre.subset_connectedComponentIn hyS hSsafe
  refine ⟨δ, hδ, ?_⟩
  intro t' ε' ht' htd' he' hed'
  have hc := hcorners t' ε' ht' htd' he' hed'
  exact ⟨hSK hc.1, hSK hc.2⟩

/-- Helper toward Definition 5.8: the signed half-disk selected by a
nearest interior contact transports across every preceding bend to every
open point of every earlier segment. The original signed test is retained
throughout the induction, without any additional contact or sector premise. -/
theorem face_nearest_openSegment_earlier_halfDisk (hvert : Function.Surjective vert)
    (K : P.Face) (z q : ℂ) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hzq : z ≠ q) (hball : ball z (dist z q) ⊆ K.val)
    (hmin : ∀ y ∈ P.image, dist z q ≤ dist z y) :
    let s := (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (z - q)).im
    ∀ j : ℕ, j ≤ i → ∀ x : ℂ,
      x ∈ openSegment ℝ ((P.arc d).point j) ((P.arc d).point (j + 1)) →
      ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x r,
        0 < s * (star ((P.arc d).point (j + 1) - (P.arc d).point j) * (y - x)).im →
          y ∈ K.val := by
  let s := (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (z - q)).im
  have hs : s ≠ 0 := segment_nearest_side_ne_zero _ _ z q
    ((P.arc_simple d).1 i hi) hzq hq (fun y hy =>
      hmin y (Or.inr ⟨d, (P.arc d).segmentAt_subset_image hi hy⟩))
  let H := fun j : ℕ => ∀ x : ℂ,
    x ∈ openSegment ℝ ((P.arc d).point j) ((P.arc d).point (j + 1)) →
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x r,
      0 < s * (star ((P.arc d).point (j + 1) - (P.arc d).point j) * (y - x)).im →
        y ∈ K.val
  have htransport (j : ℕ) (hj : j + 1 < (P.arc d).points.length) (x₁ x₂ : ℂ)
      (hx₁ : x₁ ∈ openSegment ℝ ((P.arc d).point j) ((P.arc d).point (j + 1)))
      (hx₂ : x₂ ∈ openSegment ℝ ((P.arc d).point j) ((P.arc d).point (j + 1)))
      (hbase : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x₁ r,
        0 < s * (star ((P.arc d).point (j + 1) - (P.arc d).point j) * (y - x₁)).im →
          y ∈ K.val) :
      ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x₂ r,
        0 < s * (star ((P.arc d).point (j + 1) - (P.arc d).point j) * (y - x₂)).im →
          y ∈ K.val := by
    let a := (P.arc d).point j
    let b := (P.arc d).point (j + 1)
    let u := b - a
    let v := s • (Complex.I * u)
    have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 j hj).symm
    obtain ⟨r₀, hr₀, hhalf⟩ := hbase
    obtain ⟨δ₀, hδ₀, hstrip⟩ := P.openSegment_normal_strip_compl hvert d hj x₁ x₂ hx₁ hx₂
    let δ := min (δ₀ / (|s| + 1)) (r₀ / (2 * (‖v‖ + 1)))
    have hδ : 0 < δ := lt_min (div_pos hδ₀ (by positivity)) (div_pos hr₀ (by positivity))
    have hscaled (t : ℝ) (ht : 0 < t) (htd : t < δ) : |t * s| < δ₀ := by
      have hprod : t * (|s| + 1) < δ₀ :=
        (lt_div_iff₀ (by positivity)).mp (htd.trans_le (min_le_left _ _))
      rw [abs_mul, abs_of_pos ht]
      linarith only [hprod, ht]
    have hside (x : ℂ) (hx : x ∈ segment ℝ a b) (t : ℝ) (ht : 0 < t) :
        0 < s * (star u * (x + t • v - x)).im := by
      change 0 < s * (star u * (x + t • (s • (Complex.I * u)) - x)).im
      rw [smul_smul, segment_normal_offset_side a b x x (t * s) hx hx]
      have hp := mul_pos (mul_pos ht (sq_pos_of_ne_zero hs)) (Complex.normSq_pos.mpr hu)
      nlinarith only [hp]
    have hbase' (t : ℝ) (ht : 0 < t) (htd : t < δ) : x₁ + t • v ∈ K.val := by
      apply hhalf
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_pos ht]
        have hprod : t * (2 * (‖v‖ + 1)) < r₀ :=
          (lt_div_iff₀ (by positivity)).mp (htd.trans_le (min_le_right _ _))
        nlinarith only [hprod, ht, norm_nonneg v]
      · exact hside x₁ (openSegment_subset_segment ℝ a b hx₁) t ht
    let f : ℂ × ℝ → ℂ := fun p => p.1 + p.2 • v
    let S := f '' (segment ℝ x₁ x₂ ×ˢ Ioo 0 δ)
    have hsegpre : IsPreconnected (segment ℝ x₁ x₂) := by
      rw [segment_eq_image']
      exact isPreconnected_Icc.image _ (by fun_prop)
    have hpre : IsPreconnected S :=
      (hsegpre.prod isPreconnected_Ioo).image f (by dsimp [f]; fun_prop)
    have hsafe : S ⊆ P.imageᶜ := by
      rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      change x + t • v ∉ P.image
      change x + t • (s • (Complex.I * u)) ∉ P.image
      rw [smul_smul]
      exact hstrip x hx (t * s) (abs_pos.mpr (mul_ne_zero ht.1.ne' hs))
        (hscaled t ht.1 ht.2)
    have hwS : x₁ + (δ / 2) • v ∈ S := ⟨(x₁, δ / 2),
      ⟨left_mem_segment ℝ x₁ x₂, half_pos hδ, half_lt_self hδ⟩, rfl⟩
    have hwK := hbase' (δ / 2) (half_pos hδ) (half_lt_self hδ)
    have hSK : S ⊆ K.val := by
      obtain ⟨x₀, _, hK⟩ := K.property
      rw [hK] at hwK ⊢
      rw [connectedComponentIn_eq hwK]
      exact hpre.subset_connectedComponentIn hwS hsafe
    obtain ⟨r, hr, hlocal⟩ := P.openSegment_contact_local_image hvert d hj hx₂
    let t := min (δ / 2) (r / (2 * (‖v‖ + 1)))
    have ht : 0 < t := lt_min (half_pos hδ) (div_pos hr (by positivity))
    have htd : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hw₂ : x₂ + t • v ∈ K.val :=
      hSK ⟨(x₂, t), ⟨right_mem_segment ℝ x₁ x₂, ht, htd⟩, rfl⟩
    have hwr : x₂ + t • v ∈ ball x₂ r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have hprod : t * (2 * (‖v‖ + 1)) ≤ r :=
        (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
      nlinarith only [hprod, ht, norm_nonneg v]
    exact ⟨r, hr, P.face_halfDisk_of_local_image K a b x₂ (x₂ + t • v) r s
      (openSegment_subset_segment ℝ a b hx₂) hw₂ hwr
      (hside x₂ (openSegment_subset_segment ℝ a b hx₂) t ht) hlocal⟩
  have hstep (j : ℕ) (hj : j < i) (hnext : H (j + 1)) : H j := by
    let a := (P.arc d).point j
    let b := (P.arc d).point (j + 1)
    let c := (P.arc d).point (j + 2)
    let u := b - a
    let v := c - b
    have hlen : j + 2 < (P.arc d).points.length := by omega
    have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 j (by omega)).symm
    have hv : v ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 (j + 1) (by omega)).symm
    obtain ⟨S, hSpre, hSsafe, δ, hδ, hcorners⟩ := P.bend_contact_side_sector hvert d hlen s hs
    let t := min (δ / 2) (1 / 2 : ℝ)
    have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
    have htd : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
    let x₁ := b + t • (-u)
    let x₂ := b + t • v
    have hx₁ : x₁ ∈ openSegment ℝ a b := by
      rw [openSegment_symm, openSegment_eq_image']
      refine ⟨t, ⟨ht, ht1⟩, ?_⟩
      change b + t • (a - b) = b + t • (-(b - a))
      module
    have hx₂ : x₂ ∈ openSegment ℝ b c := by
      rw [openSegment_eq_image']
      exact ⟨t, ⟨ht, ht1⟩, rfl⟩
    obtain ⟨r₁, hr₁, hlocal⟩ := P.openSegment_contact_local_image hvert d (by omega) hx₁
    obtain ⟨r₂, hr₂, hhalf₂⟩ := hnext x₂ hx₂
    let n₁ := t • (s • (Complex.I * u))
    let n₂ := t • (s • (Complex.I * v))
    let ε := min (δ / 2) (min r₁ r₂ / (2 * (‖n₁‖ + ‖n₂‖ + 1)))
    have he : 0 < ε := lt_min (half_pos hδ) (div_pos (lt_min hr₁ hr₂) (by positivity))
    have hed : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hprod : ε * (2 * (‖n₁‖ + ‖n₂‖ + 1)) ≤ min r₁ r₂ :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    let y₁ := b + t • (-u + ε • (s • (Complex.I * u)))
    let y₂ := b + t • (v + ε • (s • (Complex.I * v)))
    have hydiff₁ : y₁ - x₁ = ε • n₁ := by
      change b + t • (-u + ε • (s • (Complex.I * u))) - (b + t • (-u)) =
        ε • (t • (s • (Complex.I * u)))
      module
    have hydiff₂ : y₂ - x₂ = ε • n₂ := by
      change b + t • (v + ε • (s • (Complex.I * v))) - (b + t • v) =
        ε • (t • (s • (Complex.I * v)))
      module
    have hyr₁ : y₁ ∈ ball x₁ r₁ := by
      rw [mem_ball, dist_eq_norm, hydiff₁, norm_smul, Real.norm_eq_abs, abs_of_pos he]
      have hbound := hprod.trans (min_le_left _ _)
      nlinarith only [hbound, he, norm_nonneg n₁, norm_nonneg n₂]
    have hyr₂ : y₂ ∈ ball x₂ r₂ := by
      rw [mem_ball, dist_eq_norm, hydiff₂, norm_smul, Real.norm_eq_abs, abs_of_pos he]
      have hbound := hprod.trans (min_le_right _ _)
      nlinarith only [hbound, he, norm_nonneg n₁, norm_nonneg n₂]
    have hside₁ : 0 < s * (star u * (y₁ - x₁)).im := by
      have heq : y₁ = x₁ + (t * ε * s) • (Complex.I * u) := by
        change b + t • (-u + ε • (s • (Complex.I * u))) =
          (b + t • (-u)) + (t * ε * s) • (Complex.I * u)
        module
      have hxseg := openSegment_subset_segment ℝ a b hx₁
      rw [heq, segment_normal_offset_side a b x₁ x₁ (t * ε * s) hxseg hxseg]
      have hp := mul_pos (mul_pos (mul_pos ht he) (sq_pos_of_ne_zero hs))
        (Complex.normSq_pos.mpr hu)
      nlinarith only [hp]
    have hside₂ : 0 < s * (star v * (y₂ - x₂)).im := by
      have heq : y₂ = x₂ + (t * ε * s) • (Complex.I * v) := by
        change b + t • (v + ε • (s • (Complex.I * v))) =
          (b + t • v) + (t * ε * s) • (Complex.I * v)
        module
      have hxseg := openSegment_subset_segment ℝ b c hx₂
      rw [heq, segment_normal_offset_side b c x₂ x₂ (t * ε * s) hxseg hxseg]
      have hp := mul_pos (mul_pos (mul_pos ht he) (sq_pos_of_ne_zero hs))
        (Complex.normSq_pos.mpr hv)
      nlinarith only [hp]
    have hy₂K : y₂ ∈ K.val := hhalf₂ y₂ hyr₂ hside₂
    have hc := hcorners t ε ht htd he hed
    have hSK : S ⊆ K.val := by
      obtain ⟨x₀, _, hK⟩ := K.property
      rw [hK] at hy₂K ⊢
      rw [connectedComponentIn_eq hy₂K]
      exact hSpre.subset_connectedComponentIn hc.2 hSsafe
    have hbase : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x₁ r,
        0 < s * (star u * (y - x₁)).im → y ∈ K.val :=
      ⟨r₁, hr₁, P.face_halfDisk_of_local_image K a b x₁ y₁ r₁ s
        (openSegment_subset_segment ℝ a b hx₁) (hSK hc.1) hyr₁ hside₁ hlocal⟩
    intro x hx
    exact htransport j (by omega) x₁ x hx₁ hx hbase
  have htop : H i := by
    intro x hx
    exact P.face_nearest_openSegment_halfDisk_transport hvert K z q x d hi hq hx hzq hball hmin
  change ∀ j : ℕ, j ≤ i → H j
  intro j hji
  exact Nat.decreasingInduction (motive := fun j _ => H j) hstep htop hji

/-- Helper toward Definition 5.8: a neighborhood of the wedge base contains
a uniform wedge with independently bounded positive parameters. -/
theorem wedgeIn_of_mem_nhds (a u : ℂ) {S : Set ℂ} (hS : S ∈ 𝓝 a) :
    WedgeIn a u S := by
  let f : ℝ × ℝ → ℂ := fun x => wedgePoint a u x.1 x.2
  have hf : Continuous f := by dsimp [f, wedgePoint]; fun_prop
  have hf0 : f (0, 0) = a := by simp only [f, wedgePoint, Complex.ofReal_zero, zero_mul, add_zero]
  have hpre : f ⁻¹' S ∈ 𝓝 (0, 0) := by
    apply hf.continuousAt.preimage_mem_nhds
    rwa [hf0]
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htd he hed
  change (t, ε) ∈ f ⁻¹' S
  apply hsub
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  simpa only [Real.dist_eq, sub_zero, abs_of_pos ht, abs_of_pos he] using And.intro htd hed

/-- Helper toward Definition 5.8: a nondegenerate closed segment misses
a sufficiently narrow left wedge at any base and any nonzero direction.
If the base lies on the segment, the nonzero normal perturbation handles
the collinear case explicitly. -/
theorem wedgeIn_compl_segment (a u x y : ℂ) (hu : u ≠ 0) (hxy : x ≠ y) :
    WedgeIn a u (segment ℝ x y)ᶜ := by
  by_cases ha : a ∈ segment ℝ x y
  · let w := y - x
    let A := (star w * u).im
    let B := (star w * u).re
    have hw : w ≠ 0 := sub_ne_zero.mpr hxy.symm
    have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → A + ε * B ≠ 0 := by
      by_cases hA : A = 0
      · have hB : B ≠ 0 := by
          intro hB
          exact mul_ne_zero (star_ne_zero.mpr hw) hu (Complex.ext hB hA)
        refine ⟨1, zero_lt_one, ?_⟩
        intro ε he _
        rw [hA, zero_add]
        exact mul_ne_zero he.ne' hB
      · have hf : Continuous (fun ε : ℝ => A + ε * B) := by fun_prop
        have hpre : (fun ε : ℝ => A + ε * B) ⁻¹' ({0}ᶜ : Set ℝ) ∈ 𝓝 0 :=
          hf.continuousAt.preimage_mem_nhds
            (isClosed_singleton.isOpen_compl.mem_nhds (by
              simpa only [zero_mul, add_zero, mem_compl_iff, mem_singleton_iff] using hA))
        obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hpre
        refine ⟨δ, hδ, ?_⟩
        intro ε he hed
        apply hsub
        simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos he] using hed
    obtain ⟨δ, hδ, hnonzero⟩ := hδ
    refine ⟨δ, hδ, ?_⟩
    intro t ε ht _ he hed hz
    have hzero := segment_contact_side_eq_zero x y a (wedgePoint a u t ε) ha hz
    have hformula : (star w * (wedgePoint a u t ε - a)).im = t * (A + ε * B) := by
      change (star w * (wedgePoint a u t ε - a)).im =
        t * ((star w * u).im + ε * (star w * u).re)
      simp only [wedgePoint, add_sub_cancel_left, Complex.star_def,
        Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.add_re, Complex.add_im]
      ring
    exact (mul_ne_zero ht.ne' (hnonzero ε he hed)) (hformula.symm.trans hzero)
  · have hclosed : IsClosed (segment ℝ x y) := by
      rw [segment_eq_image']
      exact (isCompact_Icc.image (by fun_prop)).isClosed
    exact wedgeIn_of_mem_nhds a u (hclosed.isOpen_compl.mem_nhds ha)

/-- Helper toward Definition 5.8: a finite simple polyline misses a
sufficiently narrow left wedge, at any base and any nonzero direction. -/
theorem wedgeIn_compl_polyline (a u : ℂ) (hu : u ≠ 0)
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length) :
    WedgeIn a u p.imageᶜ := by
  classical
  let J := Fin (p.points.length - 1)
  have hfinite (F : Finset J) : WedgeIn a u (⋃ j ∈ F, p.segmentAt j.val)ᶜ := by
    induction F using Finset.induction_on with
    | empty =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro t ε _ _ _ _
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, compl_empty, mem_univ]
    | @insert j F _ ih =>
      obtain ⟨δ₁, hδ₁, hw₁⟩ := wedgeIn_compl_segment a u (p.point j.val)
        (p.point (j.val + 1)) hu (hp.1 j.val (by have := j.isLt; omega))
      obtain ⟨δ₂, hδ₂, hw₂⟩ := ih
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro t ε ht htd he hed
      have h₁ := hw₁ t ε ht (htd.trans_le (min_le_left _ _)) he (hed.trans_le (min_le_left _ _))
      have h₂ := hw₂ t ε ht (htd.trans_le (min_le_right _ _)) he (hed.trans_le (min_le_right _ _))
      change wedgePoint a u t ε ∉ p.segmentAt j.val at h₁
      simpa only [Finset.set_biUnion_insert, mem_compl_iff, mem_union, not_or] using And.intro h₁ h₂
  obtain ⟨δ, hδ, hw⟩ := hfinite Finset.univ
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htd he hed hz
  apply hw t ε ht htd he hed
  rcases hz with hs | ⟨j, hj, hzj⟩
  · refine mem_iUnion.mpr ⟨⟨0, by omega⟩, mem_iUnion.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hs]
    change p.start ∈ segment ℝ (p.point 0) (p.point 1)
    rw [p.point_zero_eq_start]
    exact left_mem_segment ℝ _ _
  · exact mem_iUnion.mpr ⟨⟨j, by omega⟩, mem_iUnion.mpr ⟨Finset.mem_univ _, hzj⟩⟩

/-- Helper toward Definition 5.8: local finiteness of the drawing upgrades
finite-segment wedge avoidance to avoidance of the entire image. -/
theorem wedgeIn_compl_image (hvert : Function.Surjective vert)
    (a u : ℂ) (hu : u ≠ 0) : WedgeIn a u P.imageᶜ := by
  classical
  let E := {e : D | (ball a 1 ∩ (P.arc e).image).Nonempty}
  have hE : E.Finite := P.locally_finite (ball a 1) isBounded_ball
  have hfinite (F : Finset D) : WedgeIn a u (⋃ e ∈ F, (P.arc e).image)ᶜ := by
    induction F using Finset.induction_on with
    | empty =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro t ε _ _ _ _
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, compl_empty, mem_univ]
    | @insert e F _ ih =>
      obtain ⟨δ₁, hδ₁, hw₁⟩ := wedgeIn_compl_polyline a u hu (P.arc e) (P.arc_simple e) (P.arc_length e)
      obtain ⟨δ₂, hδ₂, hw₂⟩ := ih
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro t ε ht htd he hed
      have h₁ := hw₁ t ε ht (htd.trans_le (min_le_left _ _)) he (hed.trans_le (min_le_left _ _))
      have h₂ := hw₂ t ε ht (htd.trans_le (min_le_right _ _)) he (hed.trans_le (min_le_right _ _))
      simpa only [Finset.set_biUnion_insert, mem_compl_iff, mem_union, not_or] using And.intro h₁ h₂
  obtain ⟨δ₁, hδ₁, hw₁⟩ := hfinite hE.toFinset
  obtain ⟨δ₂, hδ₂, hw₂⟩ := wedgeIn_of_mem_nhds a u (ball_mem_nhds a zero_lt_one)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro t ε ht htd he hed hz
  have hball := hw₂ t ε ht (htd.trans_le (min_le_right _ _)) he (hed.trans_le (min_le_right _ _))
  have hnot := hw₁ t ε ht (htd.trans_le (min_le_left _ _)) he (hed.trans_le (min_le_left _ _))
  rw [P.image_eq_union_arcs hvert] at hz
  obtain ⟨e, hze⟩ := mem_iUnion.mp hz
  have heE : e ∈ hE.toFinset := hE.mem_toFinset.mpr ⟨_, hball, hze⟩
  exact hnot (mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨heE, hze⟩⟩)

/-- Helper toward Definition 5.8: a positive nearest-contact side reaches
the original dart tail. The tail wedge is proved to avoid the drawing and
its complementary face is identified using the transported first-segment
half-disk. -/
theorem face_nearest_openSegment_dartBorders_of_pos (hvert : Function.Surjective vert)
    (K : P.Face) (z q : ℂ) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hzq : z ≠ q) (hball : ball z (dist z q) ⊆ K.val)
    (hmin : ∀ y ∈ P.image, dist z q ≤ dist z y)
    (hpos : 0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (z - q)).im) :
    P.dartBorders d K := by
  let a := (P.arc d).start
  let b := (P.arc d).point 1
  let u := b - a
  let s := (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (z - q)).im
  have hu : u ≠ 0 := P.initial_nonzero d
  obtain ⟨F, hF⟩ := P.dartBorders_exists_of_wedge_compl d
    (P.wedgeIn_compl_image hvert a u hu)
  have hFcopy := hF
  obtain ⟨δ, hδ, hwF⟩ := hFcopy
  let t := min (δ / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
  have htd : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let x := a + t • u
  have hx : x ∈ openSegment ℝ ((P.arc d).point 0) ((P.arc d).point 1) := by
    rw [Polyline.point_zero_eq_start, openSegment_eq_image']
    exact ⟨t, ⟨ht, ht1⟩, rfl⟩
  obtain ⟨r, hr, hhalf⟩ := P.face_nearest_openSegment_earlier_halfDisk
    hvert K z q d hi hq hzq hball hmin 0 (Nat.zero_le _) x hx
  let n := t • (Complex.I * u)
  let ε := min (δ / 2) (r / (2 * (‖n‖ + 1)))
  have he : 0 < ε := lt_min (half_pos hδ) (div_pos hr (by positivity))
  have hed : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  let y := wedgePoint a u t ε
  have hyrepr : y = x + (t * ε) • (Complex.I * u) := by
    change wedgePoint a u t ε = (a + t • u) + (t * ε) • (Complex.I * u)
    simp only [wedgePoint, Complex.real_smul, Complex.ofReal_mul]
    ring
  have hyx : y - x = ε • n := by
    rw [hyrepr, add_sub_cancel_left]
    change (t * ε) • (Complex.I * u) = ε • (t • (Complex.I * u))
    module
  have hyr : y ∈ ball x r := by
    rw [mem_ball, dist_eq_norm, hyx, norm_smul, Real.norm_eq_abs, abs_of_pos he]
    have hprod : ε * (2 * (‖n‖ + 1)) ≤ r :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith only [hprod, he, norm_nonneg n]
  have hyK : y ∈ K.val := by
    apply hhalf y hyr
    have hxseg : x ∈ segment ℝ a b := by
      simpa only [Polyline.point_zero_eq_start] using openSegment_subset_segment ℝ _ _ hx
    rw [Polyline.point_zero_eq_start]
    change 0 < s * (star u * (y - x)).im
    rw [hyrepr, segment_normal_offset_side a b x x (t * ε) hxseg hxseg]
    exact mul_pos hpos (mul_pos (mul_pos ht he) (Complex.normSq_pos.mpr hu))
  have hyF : y ∈ F.val := hwF t ε ht htd he hed
  have hFK : F = K := P.faces_eq_of_mem hyF hyK
  exact hFK ▸ hF

/-- Helper toward Definition 5.8: a nearest open-segment contact belongs
to a face bordering one of the two original darts of that geometric edge.
The negative-side case uses the reversed polyline, retaining edge identity. -/
theorem face_nearest_openSegment_bordering_dart (hvert : Function.Surjective vert)
    (K : P.Face) (z q : ℂ) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hzq : z ≠ q) (hball : ball z (dist z q) ⊆ K.val)
    (hmin : ∀ y ∈ P.image, dist z q ≤ dist z y) :
    P.dartBorders d K ∨ P.dartBorders (flip d) K := by
  have hs := segment_nearest_side_ne_zero _ _ z q
    ((P.arc_simple d).1 i hi) hzq hq (fun y hy =>
      hmin y (Or.inr ⟨d, (P.arc d).segmentAt_subset_image hi hy⟩))
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · let j := (P.arc d).points.length - 2 - i
    have hj : j + 1 < (P.arc d).points.length := by dsimp [j]; omega
    have hlen : (P.arc (flip d)).points.length = (P.arc d).points.length := by
      rw [P.arc_flip d]
      exact List.length_reverse
    have hj' : j + 1 < (P.arc (flip d)).points.length := by omega
    have hfirst : (P.arc (flip d)).point j = (P.arc d).point (i + 1) := by
      rw [P.arc_flip d, Polyline.point_reverse_transfer _ (by omega)]
      congr 1
      dsimp [j]
      omega
    have hlast : (P.arc (flip d)).point (j + 1) = (P.arc d).point i := by
      rw [P.arc_flip d, Polyline.point_reverse_transfer _ hj]
      congr 1
      dsimp [j]
      omega
    have hq' : q ∈ openSegment ℝ ((P.arc (flip d)).point j)
        ((P.arc (flip d)).point (j + 1)) := by
      rw [hfirst, hlast, openSegment_symm]
      exact hq
    have hpos' : 0 < (star ((P.arc (flip d)).point (j + 1) -
        (P.arc (flip d)).point j) * (z - q)).im := by
      rw [hfirst, hlast, ← neg_sub ((P.arc d).point (i + 1)) ((P.arc d).point i),
        star_neg, neg_mul, Complex.neg_im]
      exact neg_pos.mpr hneg
    exact Or.inr (P.face_nearest_openSegment_dartBorders_of_pos
      hvert K z q (flip d) hj' hq' hzq hball hmin hpos')
  · exact Or.inl (P.face_nearest_openSegment_dartBorders_of_pos
      hvert K z q d hi hq hzq hball hmin hpos)

/-- Helper toward Definition 5.8: a punctured complex disk is preconnected.
Four convex signed half-disks, with consecutive nonempty intersections,
give a proof which does not require a choice of angular coordinates. -/
theorem punctured_ball_isPreconnected (q : ℂ) (r : ℝ) (hr : 0 < r) :
    IsPreconnected (ball q r \ {q}) := by
  let H (u : ℂ) (s : ℝ) :=
    {y : ℂ | y ∈ ball q r ∧ 0 < s * (star u * (y - q)).im}
  have hc (u : ℂ) (s : ℝ) : IsPreconnected (H u s) :=
    (signed_halfDisk_convex q u r s).isPreconnected
  let t := r / 4
  have ht : 0 < t := div_pos hr (by norm_num)
  have hball (w : ℂ) (hw : ‖w‖ ≤ 2) : q + t • w ∈ ball q r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    have := mul_le_mul_of_nonneg_left hw ht.le
    dsimp [t] at *
    linarith only [this, hr]
  have hn (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
      ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ≤ 2 := by
    calc
      ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ≤
          ‖(a : ℂ)‖ + ‖(b : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |a| + |b| := by rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 := by linarith only [ha, hb]
  have hab : (H 1 1 ∩ H Complex.I (-1)).Nonempty := by
    refine ⟨q + t • ((1 : ℂ) + Complex.I), ?_, ?_⟩
    · refine ⟨hball _ (by simpa [sub_eq_add_neg] using hn 1 1 (by norm_num) (by norm_num)), ?_⟩
      simp [ht]
    · refine ⟨hball _ (by simpa [sub_eq_add_neg] using hn 1 1 (by norm_num) (by norm_num)), ?_⟩
      simpa [H, Complex.smul_im, Complex.smul_re] using ht
  have hbc : ((H 1 1 ∪ H Complex.I (-1)) ∩ H 1 (-1)).Nonempty := by
    refine ⟨q + t • ((1 : ℂ) - Complex.I), Or.inr ?_, ?_⟩
    · refine ⟨hball _ (by simpa [sub_eq_add_neg] using hn 1 (-1) (by norm_num) (by norm_num)), ?_⟩
      simpa [H, Complex.smul_im, Complex.smul_re] using ht
    · refine ⟨hball _ (by simpa [sub_eq_add_neg] using hn 1 (-1) (by norm_num) (by norm_num)), ?_⟩
      simpa [H, Complex.smul_im] using ht
  have hcd : (((H 1 1 ∪ H Complex.I (-1)) ∪ H 1 (-1)) ∩
      H Complex.I 1).Nonempty := by
    refine ⟨q + t • ((-1 : ℂ) - Complex.I), Or.inr ?_, ?_⟩
    · refine ⟨hball _ (by simpa [sub_eq_add_neg] using hn (-1) (-1) (by norm_num) (by norm_num)), ?_⟩
      simpa [H, Complex.smul_im] using ht
    · refine ⟨hball _ (by simpa [sub_eq_add_neg] using hn (-1) (-1) (by norm_num) (by norm_num)), ?_⟩
      simpa [H, Complex.smul_im, Complex.smul_re] using ht
  have heq : ((H 1 1 ∪ H Complex.I (-1)) ∪ H 1 (-1)) ∪ H Complex.I 1 =
      ball q r \ {q} := by
    ext y
    simp only [H, mem_union, mem_ofPred_eq, mem_sdiff, mem_singleton_iff]
    have hz : y ≠ q ↔ (y - q).re ≠ 0 ∨ (y - q).im ≠ 0 := by
      rw [← sub_ne_zero]
      constructor
      · intro h
        by_contra hn
        push Not at hn
        exact h (Complex.ext hn.1 hn.2)
      · rintro (h | h) he
        · exact h (congrArg Complex.re he)
        · exact h (congrArg Complex.im he)
    simp only [star_one, one_mul, Complex.star_def, Complex.conj_I,
      neg_mul, Complex.neg_im, Complex.I_mul_im, neg_neg,
      neg_pos] at *
    constructor
    · rintro (((⟨hy, hs⟩ | ⟨hy, hs⟩) | ⟨hy, hs⟩) | ⟨hy, hs⟩)
      all_goals refine ⟨hy, hz.mpr ?_⟩
      · exact Or.inr hs.ne'
      · exact Or.inl hs.ne'
      · exact Or.inr hs.ne
      · exact Or.inl hs.ne
    · rintro ⟨hy, hne⟩
      rcases hz.mp hne with h | h
      · rcases lt_or_gt_of_ne h with h | h
        · exact Or.inr ⟨hy, h⟩
        · exact Or.inl (Or.inl (Or.inr ⟨hy, h⟩))
      · rcases lt_or_gt_of_ne h with h | h
        · exact Or.inl (Or.inr ⟨hy, h⟩)
        · exact Or.inl (Or.inl (Or.inl ⟨hy, h⟩))
  rw [← heq]
  exact IsPreconnected.union' hcd
    (IsPreconnected.union' hbc (IsPreconnected.union' hab (hc _ _) (hc _ _)) (hc _ _))
    (hc _ _)

/-- Helper toward Definition 5.8: around any point, local finiteness
isolates all polyline vertices other than that point. This includes internal
bends as well as graph vertices and retains all incident edge identities. -/
theorem polyline_vertices_locally_isolated (q : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ (e : D) (j : ℕ), j < (P.arc e).points.length →
      (P.arc e).point j ∈ ball q r → (P.arc e).point j = q := by
  classical
  let E (e : D) : Set ℂ :=
    (Set.range (fun j : Fin (P.arc e).points.length => (P.arc e).point j.val)) \ {q}
  have hsub (e : D) : E e ⊆ (P.arc e).image := by
    rintro x ⟨⟨j, rfl⟩, _⟩
    exact (P.arc e).point_mem_image j.isLt
  have hlocal : LocallyFinite (fun e => (P.arc e).image) := by
    intro z
    refine ⟨ball z 1, ball_mem_nhds z zero_lt_one, ?_⟩
    simpa only [inter_comm] using P.locally_finite (ball z 1) isBounded_ball
  have hclosed : IsClosed (⋃ e, E e) := by
    apply (hlocal.subset hsub).isClosed_iUnion
    intro e
    exact ((finite_range _).sdiff).isClosed
  have hq : q ∉ ⋃ e, E e := by
    rintro h
    obtain ⟨e, he⟩ := mem_iUnion.mp h
    exact he.2 rfl
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hq)
  refine ⟨r, hr, ?_⟩
  intro e j hj hjball
  by_contra hne
  exact hb hjball (mem_iUnion.mpr ⟨e, ⟨⟨⟨j, hj⟩, rfl⟩, hne⟩⟩)

/-- Helper toward Definition 5.8: complementary faces are open, and their
frontier is contained in the geometric drawing. -/
theorem face_open_frontier_subset_image (hvert : Function.Surjective vert)
    (K : P.Face) : IsOpen K.val ∧ frontier K.val ⊆ P.image := by
  have hopen : IsOpen K.val := by
    obtain ⟨x, _, hK⟩ := K.property
    rw [hK]
    exact (P.image_isClosed hvert).isOpen_compl.connectedComponentIn
  refine ⟨hopen, ?_⟩
  intro x hx
  by_contra hxi
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp
    ((P.image_isClosed hvert).isOpen_compl.mem_nhds hxi)
  obtain ⟨w, hwK, hw⟩ := Metric.mem_closure_iff.mp (frontier_subset_closure hx) r hr
  have hwball : w ∈ ball x r := by rwa [mem_ball, dist_comm]
  have hxK : x ∈ K.val := by
    obtain ⟨a, _, hK⟩ := K.property
    rw [hK] at hwK ⊢
    rw [connectedComponentIn_eq hwK]
    exact (convex_ball x r).isPreconnected.subset_connectedComponentIn hwball hb
      (mem_ball_self hr)
  exact hx.2 (hopen.mem_nhds hxK |> mem_interior_iff_mem_nhds.mpr)

/-- Helper toward Definition 5.8: a nondegenerate segment has points
arbitrarily close to either endpoint, distinct from that endpoint. -/
theorem segment_endpoint_nearby (a b q : ℂ) (hab : a ≠ b)
    (hq : q = a ∨ q = b) (r : ℝ) (hr : 0 < r) :
    ∃ y ∈ segment ℝ a b, y ∈ ball q r ∧ y ≠ q := by
  suffices h : ∀ (a b : ℂ), a ≠ b →
      ∃ y ∈ segment ℝ a b, y ∈ ball a r ∧ y ≠ a by
    rcases hq with rfl | rfl
    · exact h _ _ hab
    · simpa only [segment_symm] using h _ _ hab.symm
  intro a b hab
  let u := b - a
  let t := min (1 / 2 : ℝ) (r / (2 * (‖u‖ + 1)))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hr (by positivity))
  have ht1 : t < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have htr : t * (2 * (‖u‖ + 1)) ≤ r :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨a + t • u, ?_, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨t, ⟨ht.le, ht1.le⟩, rfl⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    nlinarith only [htr, ht, norm_nonneg u]
  · intro he
    have hzero : t • u = 0 := by simpa only [add_eq_left] using he
    exact smul_ne_zero ht.ne' (sub_ne_zero.mpr hab.symm) hzero

/-- Helper toward Definition 5.8: a face accumulating at a segment
endpoint has a frontier point which is not any polyline vertex. A punctured
disk cannot be separated by its center, and local finiteness removes every
other polyline vertex from that disk. -/
theorem face_endpoint_frontier_not_vertex (hvert : Function.Surjective vert)
    (K : P.Face) (q : ℂ) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hq : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1))
    (hqcl : q ∈ closure K.val) :
    ∃ x ∈ frontier K.val, ∀ (e : D) (j : ℕ),
      j < (P.arc e).points.length → x ≠ (P.arc e).point j := by
  obtain ⟨r, hr, hisolate⟩ := P.polyline_vertices_locally_isolated q
  obtain ⟨hopen, _⟩ := P.face_open_frontier_subset_image hvert K
  have hqimage : q ∈ P.image := by
    rcases hq with rfl | rfl
    · exact Or.inr ⟨d, (P.arc d).point_mem_image (by omega)⟩
    · exact Or.inr ⟨d, (P.arc d).point_mem_image hi⟩
  obtain ⟨w, hwK, hwr⟩ := Metric.mem_closure_iff.mp hqcl r hr
  have hwU : w ∈ ball q r \ {q} := by
    refine ⟨?_, ?_⟩
    · rwa [mem_ball, dist_comm]
    · intro he
      exact P.face_subset_compl K hwK (he ▸ hqimage)
  obtain ⟨y, hyseg, hyball, hyne⟩ := segment_endpoint_nearby _ _ q
    ((P.arc_simple d).1 i hi) hq r hr
  have hyimage : y ∈ P.image :=
    Or.inr ⟨d, (P.arc d).segmentAt_subset_image hi hyseg⟩
  have hfront : ∃ x ∈ ball q r \ {q}, x ∈ frontier K.val := by
    by_contra hnone
    have hsubset : ball q r \ {q} ⊆ K.val := by
      apply (punctured_ball_isPreconnected q r hr).subset_of_closure_inter_subset
        hopen ⟨w, hwU, hwK⟩
      intro x hx
      by_contra hxK
      apply hnone
      refine ⟨x, hx.2, hx.1, ?_⟩
      rw [hopen.interior_eq]
      exact hxK
    exact P.face_subset_compl K (hsubset ⟨hyball, hyne⟩) hyimage
  obtain ⟨x, hxU, hxfront⟩ := hfront
  refine ⟨x, hxfront, ?_⟩
  intro e j hj he
  have hxq : x = q := by
    rw [he]
    exact hisolate e j hj (he ▸ hxU.1)
  exact hxU.2 hxq

/-- Helper toward Definition 5.8: a frontier point away from every
polyline vertex yields a nearest open-segment contact in that same face.
The new nearest point stays in a disk containing no polyline vertices. -/
theorem face_frontier_not_vertex_openSegment_contact (hvert : Function.Surjective vert)
    (d₀ : D) (K : P.Face) (x : ℂ) (hx : x ∈ frontier K.val)
    (hnot : ∀ (e : D) (j : ℕ), j < (P.arc e).points.length →
      x ≠ (P.arc e).point j) :
    ∃ (z' q' : ℂ) (e : D) (j : ℕ),
      j + 1 < (P.arc e).points.length ∧
      q' ∈ openSegment ℝ ((P.arc e).point j) ((P.arc e).point (j + 1)) ∧
      z' ≠ q' ∧ ball z' (dist z' q') ⊆ K.val ∧
      ∀ y ∈ P.image, dist z' q' ≤ dist z' y := by
  obtain ⟨r, hr, hisolate⟩ := P.polyline_vertices_locally_isolated x
  obtain ⟨w, hwK, hwx⟩ := Metric.mem_closure_iff.mp (frontier_subset_closure hx)
    (r / 4) (by positivity)
  obtain ⟨q', e, j, hj, hqseg, _, hdist, hb, hmin⟩ :=
    P.face_nearest_segment_contact hvert d₀ K w hwK
  have hximage : x ∈ P.image := (P.face_open_frontier_subset_image hvert K).2 hx
  have hnear : q' ∈ ball x r := by
    rw [mem_ball]
    calc
      dist q' x ≤ dist q' w + dist w x := dist_triangle _ _ _
      _ ≤ dist w x + dist w x := by
        rw [dist_comm q' w]
        exact add_le_add (hmin x hximage) le_rfl
      _ < r := by rw [dist_comm w x]; linarith only [hwx, hr]
  have hqnot (d : D) (k : ℕ) (hk : k < (P.arc d).points.length) :
      q' ≠ (P.arc d).point k := by
    intro he
    have heq : (P.arc d).point k = x := hisolate d k hk (he ▸ hnear)
    exact hnot d k hk heq.symm
  refine ⟨w, q', e, j, hj, ?_, dist_pos.mp hdist, hb, hmin⟩
  exact mem_openSegment_of_ne_left_right (hqnot e j (by omega)).symm
    (hqnot e (j + 1) hj).symm hqseg

/-- Helper toward Definition 5.8: a nearest contact at a polyline
endpoint can be replaced by a nearest open-segment contact in the same face.
The punctured-disk argument treats internal bends and graph vertices uniformly. -/
theorem face_nearest_endpoint_openSegment_contact
    (hvert : Function.Surjective vert)
    (K : P.Face) (z q : ℂ) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length)
    (hq : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1))
    (hzq : z ≠ q) (hball : ball z (dist z q) ⊆ K.val)
    (hmin : ∀ y ∈ P.image, dist z q ≤ dist z y) :
    ∃ (z' q' : ℂ) (e : D) (j : ℕ),
      j + 1 < (P.arc e).points.length ∧
      q' ∈ openSegment ℝ ((P.arc e).point j) ((P.arc e).point (j + 1)) ∧
      z' ≠ q' ∧ ball z' (dist z' q') ⊆ K.val ∧
      ∀ y ∈ P.image, dist z' q' ≤ dist z' y := by
  have hqcl : q ∈ closure K.val := by
    apply closure_mono hball
    rw [closure_ball z (ne_of_gt (dist_pos.mpr hzq))]
    exact mem_closedBall.mpr (le_of_eq (dist_comm q z))
  obtain ⟨x, hx, hnot⟩ := P.face_endpoint_frontier_not_vertex hvert K q d hi hq hqcl
  exact P.face_frontier_not_vertex_openSegment_contact hvert d K x hx hnot

/-- Helper toward Definition 5.8: every geometric face borders an
original dart. Closedness gives a nearest segment contact; endpoint reduction
and the open-segment transport theorem cover all contact cases. -/
theorem face_has_bordering_dart (hvert : Function.Surjective vert)
    (d₀ : D) (K : P.Face) : ∃ d : D, P.dartBorders d K := by
  obtain ⟨z, hz, hK⟩ := K.property
  have hzK : z ∈ K.val := hK ▸ mem_connectedComponentIn hz
  obtain ⟨q, d, i, hi, hqseg, _, hr, hb, hm⟩ :=
    P.face_nearest_segment_contact hvert d₀ K z hzK
  by_cases hqend : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1)
  · obtain ⟨z', q', e, j, hj, hq', hne, hb', hm'⟩ :=
      P.face_nearest_endpoint_openSegment_contact hvert K z q d hi hqend
        (dist_pos.mp hr) hb hm
    rcases P.face_nearest_openSegment_bordering_dart hvert K z' q' e hj hq' hne hb' hm'
      with he | he
    · exact ⟨e, he⟩
    · exact ⟨flip e, he⟩
  · have hqopen := mem_openSegment_of_ne_left_right
      (fun he => hqend (Or.inl he.symm)) (fun he => hqend (Or.inr he.symm)) hqseg
    rcases P.face_nearest_openSegment_bordering_dart hvert K z q d hi hqopen
      (dist_pos.mp hr) hb hm with hd | hd
    · exact ⟨d, hd⟩
    · exact ⟨flip d, hd⟩

end DirectedDistances.PlanarMap.PLDrawing

namespace DirectedDistances.KMSW

open Set DirectedDistances.PlanarMap

/-- Helper toward Definition 5.8: every whole-plane colimit vertex is
incident to an actual geometric dart, including missing edges. -/
theorem uibhbot_faceOrbit_dartVertex_surjective (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : Function.Surjective (wholePlaneDartVertex W) := by
  intro v
  obtain ⟨⟨N, k⟩, rfl⟩ := Quotient.exists_rep v
  change ∃ d, wholePlaneDartVertex W d = wholePlaneVertexι W N k
  obtain ⟨n, hn⟩ := kmsw_vertex_allocated_of_finite_incidence (shiftedStream W N) (H.1 N) k
  obtain ⟨d, hd⟩ := stageEndpoint_exists (shiftedStream W N) n k hn
  refine ⟨wholePlaneDartι W N (d.1.val, d.2), ?_⟩
  rw [wholePlaneDartVertex_ι]
  congr 1
  have he := edge_endpoints_eq (shiftedStream W N) d.1.isLt
  cases hb : d.2 <;>
    simpa only [kmswLimitDartVertex, stageEndpoint, hb, Bool.false_eq_true,
      ite_false, ite_true, he.1, he.2] using hd

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

include hp ha hf hFim hFa in
/-- Helper toward Definition 5.8: every geometric assembly face borders
a whole-plane dart. This is geometric coverage, proved without a coverage premise. -/
theorem uibhbot_assembly_face_has_bordering_dart (K : (G).Face) :
    ∃ d : WholePlaneDart W, (G).dartBorders d K :=
  (G).face_has_bordering_dart (uibhbot_faceOrbit_dartVertex_surjective W H)
    (uibhbotWholePlaneOuterDart W) K

/-- Helper toward Definition 5.8: the uniquely bordered geometric face
of an assembly dart, chosen only after existence and uniqueness are proved. -/
noncomputable def uibhbot_assembly_faceOfDart (d : WholePlaneDart W) : (G).Face :=
  (uibhbot_assembly_dartBorders_existsUnique
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d).exists.choose

local notation "faceD" =>
  uibhbot_assembly_faceOfDart W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: the complete bordering characterization
of the chosen face of an assembly dart. -/
theorem uibhbot_assembly_faceOfDart_eq_iff (d : WholePlaneDart W) (K : (G).Face) :
    faceD d = K ↔ (G).dartBorders d K := by
  have hs : (G).dartBorders d (faceD d) :=
    (uibhbot_assembly_dartBorders_existsUnique
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d).exists.choose_spec
  constructor
  · intro he
    exact he ▸ hs
  · intro hd
    exact (G).dartBorders_face_unique d _ _ hs hd

include hp ha hf hFim hFa hRpos in


theorem uibhbot_assembly_faceOfDart_successor (d : WholePlaneDart W) :
    faceD (wholePlaneFaceSucc W H d) = faceD d := by
  apply (uibhbot_assembly_faceOfDart_eq_iff
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos _ _).mpr
  apply uibhbot_assembly_faceSucc_dartBorders
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  exact (uibhbot_assembly_faceOfDart_eq_iff
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos _ _).mp rfl

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: all darts of a whole-plane face orbit
border the same geometric assembly face. -/
theorem uibhbot_assembly_faceOfDart_sameCycle (d e : WholePlaneDart W)
    (h : (wholePlaneFaceSucc W H).SameCycle d e) : faceD d = faceD e := by
  let f := wholePlaneFaceSucc W H
  have hforward (a : WholePlaneDart W) : faceD (f a) = faceD a :=
    uibhbot_assembly_faceOfDart_successor W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos a
  have hbackward (a : WholePlaneDart W) : faceD (f.symm a) = faceD a := by
    simpa only [Equiv.apply_symm_apply] using (hforward (f.symm a)).symm
  obtain ⟨i, hi⟩ := h
  have hpow (i : ℤ) : faceD ((f ^ i) d) = faceD d := by
    refine Int.induction_on i ?_ ?_ ?_
    · simp only [zpow_zero, Equiv.Perm.one_apply]
    · intro i ih
      rw [add_comm (i : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply, hforward, ih]
    · intro i ih
      rw [show (-(i : ℤ) - 1) = -1 + -(i : ℤ) by ring,
        zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      exact (hbackward _).trans ih
  exact (hpow i).symm.trans (congrArg faceD hi)

/-- Helper toward Definition 5.8: the geometric face corresponding to
a whole-plane face-successor orbit. The construction descends the uniquely
bordered dart face using the proved orbit invariance. -/
noncomputable def uibhbot_assembly_faceOfOrbit :
    Quotient (Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W H)) → (G).Face :=
  Quotient.lift faceD (fun d e h => uibhbot_assembly_faceOfDart_sameCycle
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d e h)

local notation "faceO" =>
  uibhbot_assembly_faceOfOrbit W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: the geometric face of an orbit is
characterized by bordering any representative dart. -/
theorem uibhbot_assembly_faceOfOrbit_mk_eq_iff (d : WholePlaneDart W) (K : (G).Face) :
    faceO (Quotient.mk _ d) = K ↔ (G).dartBorders d K :=
  uibhbot_assembly_faceOfDart_eq_iff W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d K

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: whole-plane face-successor orbits
and geometric assembly faces correspond bijectively. Surjectivity uses
the proved geometric contact theorem, and injectivity uses K02's common-face theorem. -/
theorem uibhbot_assembly_faceOfOrbit_bijective : Function.Bijective faceO := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h d =>
      induction b using Quotient.inductionOn with
      | h e =>
        change faceD d = faceD e at hab
        apply Quotient.sound
        apply uibhbot_assembly_common_face_sameCycle
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d e
        refine ⟨faceD d, ?_, ?_⟩
        · exact (uibhbot_assembly_faceOfDart_eq_iff
            W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d _).mp rfl
        · apply (uibhbot_assembly_faceOfDart_eq_iff
            W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e _).mp
          exact hab.symm
  · intro K
    obtain ⟨d, hd⟩ := uibhbot_assembly_face_has_bordering_dart
      W H h0 hL hR hfin P hp ha F hf hFim hFa K
    exact ⟨Quotient.mk _ d, (uibhbot_assembly_faceOfOrbit_mk_eq_iff
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d K).mpr hd⟩

/-- Helper toward Definition 5.8: the equivalence between whole-plane
combinatorial face orbits and geometric assembly faces. -/
noncomputable def uibhbot_assembly_faceOrbitEquiv :
    Quotient (Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W H)) ≃ (G).Face :=
  Equiv.ofBijective faceO (uibhbot_assembly_faceOfOrbit_bijective
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos)

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: the face-orbit equivalence has the
complete geometric bordering characterization. -/
theorem uibhbot_assembly_faceOrbitEquiv_mk_eq_iff (d : WholePlaneDart W) (K : (G).Face) :
    uibhbot_assembly_faceOrbitEquiv W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
      (Quotient.mk _ d) = K ↔ (G).dartBorders d K :=
  uibhbot_assembly_faceOfOrbit_mk_eq_iff W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d K

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: every geometric assembly face is
the unbounded quadrant face or an exact transported future or past creation cap. -/
theorem uibhbot_assembly_face_classification :
    ∃ U : (G).Face, (G).IsUnbounded U ∧
      (G).dartBorders (uibhbotWholePlaneOuterDart W) U ∧
      ∀ K : (G).Face, K = U ∨
        (∃ j : TriangleCreationTime (shiftedStream W 0),
          K.val = uibhbotGlueFutureTransfer (shiftedStream W 0) h0 (H.1 0) ''
            (capFace (shiftedStream W 0) (H.1 0) j).val) ∨
        (∃ j : TriangleCreationTime (kmswPastCode W),
          K.val = uibhbotAssemblyHalfTurn ''
            (uibhbotPastStraightTransfer W hL hR ''
              (capFace (kmswPastCode W) hfin j).val)) := by
  obtain ⟨U, hroot, hclass⟩ := uibhbot_assembly_dartBorders_classification
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  obtain ⟨V, hV, _⟩ := uibhbot_assembly_quadrant_face_outer_existsUnique
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  have hVU : V = U := (G).dartBorders_face_unique _ _ _ hV.2.2 hroot
  refine ⟨U, hVU ▸ hV.2.1, hroot, ?_⟩
  intro K
  obtain ⟨d, hd⟩ := uibhbot_assembly_face_has_bordering_dart
    W H h0 hL hR hfin P hp ha F hf hFim hFa K
  rcases hclass d with hdU | ⟨j, K', hv, hd'⟩ | ⟨j, K', hv, hd'⟩
  · exact Or.inl ((G).dartBorders_face_unique d K U hd hdU)
  · have heq : K = K' := (G).dartBorders_face_unique d K K' hd hd'
    exact Or.inr (Or.inl ⟨j, heq ▸ hv⟩)
  · have heq : K = K' := (G).dartBorders_face_unique d K K' hd hd'
    exact Or.inr (Or.inr ⟨j, heq ▸ hv⟩)

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: the assembly has exactly one
unbounded complementary face. No unbounded-face coverage premise is assumed. -/
theorem uibhbot_assembly_unbounded_face_existsUnique :
    ∃! U : (G).Face, (G).IsUnbounded U := by
  obtain ⟨U, hu, _, hclass⟩ := uibhbot_assembly_face_classification
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  have hnot (K : (G).Face) (hb : Bornology.IsBounded K.val) : ¬ (G).IsUnbounded K := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hb
    intro hk
    obtain ⟨z, hz, hnorm⟩ := hk R
    have hzR := hR hz
    rw [Metric.mem_closedBall, dist_zero_right] at hzR
    exact (not_le_of_gt hnorm) hzR
  refine ⟨U, hu, ?_⟩
  intro K hk
  rcases hclass K with heq | ⟨j, hv⟩ | ⟨j, hv⟩
  · exact heq
  · exact (hnot K (hv ▸ uibhbot_future_transported_cap_bounded W H h0 j) hk).elim
  · exact (hnot K (hv ▸ uibhbot_past_transported_cap_bounded W hL hR hfin j) hk).elim

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: an assembly face is unbounded exactly
when the designated outer dart borders it. -/
theorem uibhbot_assembly_isUnbounded_iff_outer_dartBorders (K : (G).Face) :
    (G).IsUnbounded K ↔ (G).dartBorders (uibhbotWholePlaneOuterDart W) K := by
  obtain ⟨U, hu, hroot, _⟩ := uibhbot_assembly_face_classification
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  obtain ⟨V, hv, huniq⟩ := uibhbot_assembly_unbounded_face_existsUnique
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  constructor
  · intro hk
    have hKU : K = U := (huniq K hk).trans (huniq U hu).symm
    exact hKU ▸ hroot
  · intro hrootK
    have hKU : K = U := (G).dartBorders_face_unique _ _ _ hrootK hroot
    exact hKU ▸ hu

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: a face orbit has unbounded geometric
image exactly when it is the orbit of the designated outer dart. -/
theorem uibhbot_assembly_faceOfOrbit_isUnbounded_iff
    (q : Quotient (Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W H))) :
    (G).IsUnbounded (faceO q) ↔
      q = Quotient.mk _ (uibhbotWholePlaneOuterDart W) := by
  rw [uibhbot_assembly_isUnbounded_iff_outer_dartBorders
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos]
  rw [← uibhbot_assembly_faceOfOrbit_mk_eq_iff
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos]
  exact ⟨fun h => ((uibhbot_assembly_faceOfOrbit_bijective
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos).1 h).symm,
    fun h => congrArg faceO h.symm⟩

include hp ha hf hFim hFa hRpos in
/-- Helper toward Definition 5.8: precisely the east darts of globally
missing geometric edges border the unique unbounded assembly face. -/
theorem uibhbot_assembly_unbounded_dartBorders_iff (K : (G).Face)
    (hK : (G).IsUnbounded K) (d : WholePlaneDart W) :
    (G).dartBorders d K ↔ d.2 = true ∧ ¬ wholePlaneEdgePresent W d.1 := by
  have hnot (hb : Bornology.IsBounded K.val) : False := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hb
    obtain ⟨z, hz, hnorm⟩ := hK R
    have hzR := hR hz
    rw [Metric.mem_closedBall, dist_zero_right] at hzR
    exact (not_le_of_gt hnorm) hzR
  have hmissing (e : WholePlaneDart W) (he : (G).dartBorders e K) :
      e.2 = true ∧ ¬ wholePlaneEdgePresent W e.1 := by
    rcases uibhbot_assembly_bordered_face_cases
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos e K he with
      hm | ⟨a, j, _, _, hv⟩ | ⟨a, j, _, _, hv⟩
    · exact hm.2
    · exact (hnot (hv ▸ uibhbot_future_transported_cap_bounded W H h0 j)).elim
    · exact (hnot (hv ▸ uibhbot_past_transported_cap_bounded W hL hR hfin j)).elim
  constructor
  · exact hmissing d
  · intro hd
    have ho : (G).dartBorders (uibhbotWholePlaneOuterDart W) K :=
      (uibhbot_assembly_isUnbounded_iff_outer_dartBorders
        W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos K).mp hK
    have hom := hmissing _ ho
    have hc := wholePlane_missing_east_sameCycle W H
      (fun N => boundaryHitWitnesses_of_le W (Nat.zero_le N) h0)
      d.1 (uibhbotWholePlaneOuterDart W).1 hd.2 hom.2
    have hdEq : d = (d.1, true) := Prod.ext rfl hd.1
    have hoEq : uibhbotWholePlaneOuterDart W =
        ((uibhbotWholePlaneOuterDart W).1, true) := Prod.ext rfl hom.1
    rw [← hdEq, ← hoEq] at hc
    apply (uibhbot_assembly_faceOfDart_eq_iff
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d K).mp
    exact (uibhbot_assembly_faceOfDart_sameCycle
      W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos d _ hc).trans
        ((uibhbot_assembly_faceOfDart_eq_iff
          W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos _ K).mpr ho)

end Assembly
end DirectedDistances.KMSW

