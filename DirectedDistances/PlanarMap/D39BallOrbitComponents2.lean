/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents
public import DirectedDistances.PlanarMap.D39RadialOrder2

/-! # Finite drawing stars toward face-orbit identification

Helpers toward Proposition 5.16. The local statements retain all dart -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set Metric Topology

namespace Polyline

/-- Helper toward Proposition 5.16: a segment containing the start of a
simple nonconstant polyline is its initial segment. -/
theorem segmentAt_index_eq_zero_of_start_mem (p : Polyline) (hp : p.IsSimple)
    (hlen : 2 ≤ p.points.length) {i : ℕ} (hi : i + 1 < p.points.length)
    (hmem : p.start ∈ p.segmentAt i) : i = 0 := by
  by_contra hi0
  have hvalid : 0 + 1 < p.points.length := by omega
  have hzero : p.start ∈ p.segmentAt 0 := by
    rw [← p.point_zero_eq_start]
    exact left_mem_segment ℝ _ _
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hi0) with heq | hlt
  · subst i
    have hmeet := hp.2.1 0 (by omega)
    have hpoint : p.start = p.point 1 := by
      have hm : p.start ∈ ({p.point 1} : Set ℂ) := by
        rw [← hmeet]
        exact ⟨hzero, hmem⟩
      exact hm
    exact (hp.1 0 hvalid) (by simpa only [p.point_zero_eq_start] using hpoint)
  · exact (Set.disjoint_left.mp (hp.2.2 0 i hvalid hi (by omega))) hzero hmem

/-- Helper toward Proposition 5.16: a segment containing the finish of a
simple nonconstant polyline is its terminal segment. -/
theorem segmentAt_index_last_of_finish_mem (p : Polyline) (hp : p.IsSimple)
    (hlen : 2 ≤ p.points.length) {i : ℕ} (hi : i + 1 < p.points.length)
    (hmem : p.finish ∈ p.segmentAt i) : i + 2 = p.points.length := by
  let j := p.points.length - 2
  have hj : j + 1 < p.points.length := by dsimp [j]; omega
  have hjlast : j + 1 = p.points.length - 1 := by dsimp [j]; omega
  have hlast : p.finish ∈ p.segmentAt j := by
    change p.finish ∈ segment ℝ (p.point j) (p.point (j + 1))
    rw [hjlast, p.point_last_eq_finish]
    exact right_mem_segment ℝ _ _
  by_contra hnot
  have hle : i + 1 ≤ j := by dsimp [j]; omega
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact (Set.disjoint_left.mp (hp.2.2 i j hi hj hlt)) hmem hlast
  · have hmeet := hp.2.1 i (by dsimp [j] at heq; omega)
    have hpoint : p.finish = p.point (i + 1) := by
      have hm : p.finish ∈ ({p.point (i + 1)} : Set ℂ) := by
        rw [← hmeet]
        exact ⟨hmem, by simpa only [heq] using hlast⟩
      exact hm
    apply hp.1 j hj
    calc
      p.point j = p.finish := by simpa only [heq] using hpoint.symm
      _ = p.point (j + 1) := by rw [hjlast, p.point_last_eq_finish]

end Polyline

namespace PLDrawing

variable {D V : Type*} {flip : D → D}
  {rot : Equiv.Perm D} {vert : D → V}
  (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16: in a sufficiently small vertex ball,
the full drawing consists exactly of the initial segments of its outgoing
darts. Reversed terminal segments and all multiedge identities are retained. -/
theorem exists_ball_image_eq_initial_segments [Finite D] (hvert : Function.Surjective vert)
    (v : V) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball (P.pos v) r,
      (y ∈ P.image ↔ ∃ d : D, vert d = v ∧ y ∈ (P.arc d).segmentAt 0) := by
  classical
  let J := (d : D) × Fin ((P.arc d).points.length - 1)
  let S : J → Set ℂ := fun j =>
    if P.pos v ∈ (P.arc j.1).segmentAt j.2.val then ∅
    else (P.arc j.1).segmentAt j.2.val
  have hclosed : IsClosed (⋃ j, S j) := by
    apply isClosed_iUnion_of_finite
    intro j
    dsimp [S]
    split_ifs
    · exact isClosed_empty
    · change IsClosed (segment ℝ _ _)
      rw [segment_eq_image']
      exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hv : P.pos v ∉ ⋃ j, S j := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    dsimp [S] at hj
    split_ifs at hj with hmem
    · exact notMem_empty _ hj
    · exact hmem hj
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hv)
  refine ⟨r, hr, ?_⟩
  intro y hyr
  constructor
  · intro hy
    have harc : ∃ d, y ∈ (P.arc d).image := by
      rcases hy with ⟨w, rfl⟩ | ⟨d, hd⟩
      · obtain ⟨d, rfl⟩ := hvert w
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
      by_contra hnot
      apply hball hyr
      apply mem_iUnion.mpr
      refine ⟨⟨d, ⟨i, by omega⟩⟩, ?_⟩
      simpa only [S, ite_eq_right hnot] using hyi
    have hvimage := (P.arc d).segmentAt_subset_image hi hvi
    have hends : P.pos v = (P.arc d).start ∨ P.pos v = (P.arc d).finish := by
      by_contra h
      exact P.interior_avoids_vertices d v ⟨hvimage, by
        simpa only [mem_insert_iff, mem_singleton_iff] using h⟩
    rcases hends with hstart | hfinish
    · have hi0 := (P.arc d).segmentAt_index_eq_zero_of_start_mem
        (P.arc_simple d) (P.arc_length d) hi (hstart ▸ hvi)
      refine ⟨d, P.pos_injective (hstart.trans (P.arc_start d)).symm, ?_⟩
      simpa only [hi0] using hyi
    · have hilast := (P.arc d).segmentAt_index_last_of_finish_mem
        (P.arc_simple d) (P.arc_length d) hi (hfinish ▸ hvi)
      refine ⟨flip d, P.pos_injective (hfinish.trans (P.arc_finish d)).symm, ?_⟩
      rw [P.arc_flip, Polyline.segmentAt_reverse_transfer _ (by
        have := P.arc_length d; omega)]
      have hind : (P.arc d).points.length - 2 - 0 = i := by omega
      simpa only [hind] using hyi
  · rintro ⟨d, _, hy⟩
    exact Or.inr ⟨d, (P.arc d).segmentAt_subset_image (by
      have := P.arc_length d; omega) hy⟩

/-- Helper toward Proposition 5.16: the angular gap after an outgoing dart
has no intervening outgoing ray, including at singleton stars. -/
theorem rotation_turn_le (d e : D) (he : vert e = vert d) :
    ccwTurn (P.arc d).initialDirection (P.arc (rot d)).initialDirection ≤
      ccwTurn (P.arc d).initialDirection (P.arc e).initialDirection := by
  rcases P.rotation_agreement d with ⟨_, _, _, hs | ⟨_, hmin⟩⟩
  · have hed : e = d := Set.mem_singleton_iff.mp (hs.2 ▸ he)
    rw [hs.1, hed]
  · by_cases hed : e = d
    · rw [hed]
      have hfull : ccwTurn (P.arc d).initialDirection (P.arc d).initialDirection =
          2 * Real.pi := (ccwTurn_eq_two_pi_iff _ _).mpr rfl
      rw [hfull]
      exact ccwTurn_le_two_pi _ _
    · exact hmin e he hed

/-- Helper toward Proposition 5.16: the open angular sector between a dart
and its counterclockwise successor, truncated at a positive metric radius.
A singleton star gives the full punctured slit ball. -/
@[expose] def initialSector (d : D) (r : ℝ) : Set ℂ :=
  (fun p : ℝ × ℝ => P.pos (vert d) + (p.1 : ℂ) *
    Complex.exp ((((P.arc d).initialDirection.arg + p.2 : ℝ) : ℂ) * Complex.I)) ''
      (Ioo 0 r ×ˢ Ioo 0
        (ccwTurn (P.arc d).initialDirection (P.arc (rot d)).initialDirection))

/-- Helper toward Proposition 5.16: each truncated initial sector is
connected and nonempty, with no restriction on its angle being convex. -/
theorem isConnected_initialSector (d : D) {r : ℝ} (hr : 0 < r) :
    IsConnected (P.initialSector d r) := by
  apply ((isConnected_Ioo hr).prod (isConnected_Ioo (ccwTurn_pos _ _))).image
  exact (by fun_prop : Continuous (fun p : ℝ × ℝ => P.pos (vert d) + (p.1 : ℂ) *
    Complex.exp ((((P.arc d).initialDirection.arg + p.2 : ℝ) : ℂ) *
      Complex.I))).continuousOn

/-- Helper toward Proposition 5.16: a point in the initial sector is inside
the specified vertex ball. -/
theorem initialSector_subset_ball (d : D) (r : ℝ) :
    P.initialSector d r ⊆ ball (P.pos (vert d)) r := by
  rintro z ⟨⟨ρ, θ⟩, ⟨hρ, _⟩, rfl⟩
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ.1]
  exact hρ.2

/-- Helper toward Proposition 5.16: an initial sector avoids every initial
segment at its vertex. This is the strict angular exclusion supplied by the
counterclockwise rotation convention. -/
theorem initialSector_disjoint_initial_segment (d e : D) (r : ℝ)
    (he : vert e = vert d) :
    Disjoint (P.initialSector d r) ((P.arc e).segmentAt 0) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨⟨ρ, θ⟩, ⟨hρ, hθ⟩, rfl⟩ hseg
  rw [Polyline.segmentAt, Polyline.point_zero_eq_start, P.arc_start e, he,
    segment_eq_image'] at hseg
  obtain ⟨t, ht, htEq⟩ := hseg
  have hEq : (ρ : ℂ) *
      Complex.exp ((((P.arc d).initialDirection.arg + θ : ℝ) : ℂ) * Complex.I) =
      (t : ℂ) * (P.arc e).initialDirection := by
    change P.pos (vert d) + t • ((P.arc e).point 1 - P.pos (vert d)) = _ at htEq
    have hdir : (P.arc e).point 1 - P.pos (vert d) =
        (P.arc e).initialDirection := by
      rw [Polyline.initialDirection, P.arc_start e, he]
    rw [hdir, Complex.real_smul] at htEq
    exact add_left_cancel htEq.symm
  have htpos : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro ht0
    have hz : (ρ : ℂ) *
        Complex.exp ((((P.arc d).initialDirection.arg + θ : ℝ) : ℂ) * Complex.I) = 0 := by
      rw [← ht0, Complex.ofReal_zero, zero_mul] at hEq
      exact hEq
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ.1.ne') (Complex.exp_ne_zero _)) hz
  have harg := congrArg Complex.arg hEq
  rw [Complex.arg_real_mul _ hρ.1, Complex.arg_real_mul _ htpos] at harg
  have hturn : ccwTurn (P.arc d).initialDirection (P.arc e).initialDirection = θ := by
    rw [ccwTurn, ← harg]
    change ccwTurn (P.arc d).initialDirection
      (Complex.exp ((((P.arc d).initialDirection.arg + θ : ℝ) : ℂ) * Complex.I)) = θ
    exact d39_ccwTurn_polar _ _ hθ.1 (hθ.2.trans_le (ccwTurn_le_two_pi _ _))
  exact (not_lt_of_ge (P.rotation_turn_le d e he)) (hturn ▸ hθ.2)

/-- Helper toward Proposition 5.16: a whole truncated angular sector lies
in one unique geometric complementary face, for a sufficiently small radius.
This does not yet identify the face across an arriving dart. -/
theorem exists_ball_initialSector_subset_unique_face [Finite D]
    (hvert : Function.Surjective vert) (d : D) :
    ∃ r : ℝ, 0 < r ∧ ∃! F : P.Face, P.initialSector d r ⊆ F.val := by
  obtain ⟨r, hr, hlocal⟩ := P.exists_ball_image_eq_initial_segments hvert (vert d)
  have hsafe : P.initialSector d r ⊆ P.imageᶜ := by
    intro z hz hzimage
    obtain ⟨e, he, hze⟩ := (hlocal z (P.initialSector_subset_ball d r hz)).mp hzimage
    exact (Set.disjoint_left.mp (P.initialSector_disjoint_initial_segment d e r he)) hz hze
  have hc := P.isConnected_initialSector d hr
  obtain ⟨z, hz⟩ := hc.nonempty
  obtain ⟨F, hzF⟩ := (P.faces_cover_compl z).mpr (hsafe hz)
  have hsub : P.initialSector d r ⊆ F.val := by
    obtain ⟨w, _, hF⟩ := F.property
    rw [hF] at hzF ⊢
    rw [connectedComponentIn_eq hzF]
    exact hc.isPreconnected.subset_connectedComponentIn hz hsafe
  exact ⟨r, hr, F, hsub, fun G hG => P.faces_eq_of_mem (hG hz) (hsub hz)⟩

/-- Helper toward Proposition 5.16: the left face of a dart contains a
whole sufficiently small left half-ball at every open point of every one
of its segments, including its terminal segment. -/
theorem exists_ball_left_subset_of_dartBorders (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hF : P.dartBorders d F) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) {q : ℂ}
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball q r,
      0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (y - q)).im →
        y ∈ F.val := by
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let u := b - a
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  obtain ⟨r, hr, hlocal⟩ := P.openSegment_contact_local_image hvert d hi hq
  let t := r / (4 * (‖u‖ + 1))
  have ht : 0 < t := div_pos hr (by positivity)
  have htprod : t * (4 * (‖u‖ + 1)) = r := div_mul_cancel₀ r (by positivity)
  have hsmall : t * ‖u‖ < r / 2 := by nlinarith only [htprod, ht, hnu]
  let z := q + t • (Complex.I * u)
  have hzq : dist z q = t * ‖u‖ := by
    rw [dist_eq_norm]
    change ‖q + t • (Complex.I * u) - q‖ = _
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      norm_mul, Complex.norm_I, one_mul]
  have hzqpos : 0 < dist z q := hzq ▸ mul_pos ht hnu
  have hmin : ∀ y ∈ P.image, dist z q ≤ dist z y := by
    intro y hy
    by_cases hyr : y ∈ ball q r
    · have hyseg := hlocal y hyr hy
      have hside := segment_contact_side_eq_zero a b q y
        (openSegment_subset_segment ℝ a b hq) hyseg
      have him : (star u * (z - y)).im = t * Complex.normSq u := by
        have he : z - y = t • (Complex.I * u) - (y - q) := by dsimp [z]; module
        rw [he, mul_sub, Complex.sub_im, mul_smul_comm, Complex.smul_im]
        have hn : (star u * (Complex.I * u)).im = Complex.normSq u := by
          rw [show star u * (Complex.I * u) = Complex.I * (star u * u) by ring,
            Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
          simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
        change t * (star u * (Complex.I * u)).im - (star u * (y - q)).im = _
        rw [hn, hside, sub_zero]
      have hb := Complex.im_le_norm (star u * (z - y))
      rw [him, norm_mul, norm_star, Complex.normSq_eq_norm_sq] at hb
      rw [hzq, dist_eq_norm]
      nlinarith only [hb, hnu]
    · have hry : r ≤ dist q y := by
        simpa only [mem_ball, dist_comm, not_lt] using hyr
      have htri := dist_triangle q z y
      rw [dist_comm q z, hzq] at htri
      rw [hzq]
      linarith only [hry, htri, hsmall]
  have hznot : z ∉ P.image := by
    intro hz
    have hm := hmin z hz
    rw [dist_self] at hm
    exact (not_le_of_gt hzqpos) hm
  obtain ⟨K, hzK⟩ := (P.faces_cover_compl z).mpr hznot
  have hball : ball z (dist z q) ⊆ K.val := by
    have hsafe : ball z (dist z q) ⊆ P.imageᶜ := by
      intro y hy hym
      exact (not_lt_of_ge (hmin y hym)) (by
        simpa only [mem_ball, dist_comm] using hy)
    obtain ⟨x, _, hK⟩ := K.property
    rw [hK] at hzK ⊢
    rw [connectedComponentIn_eq hzK]
    exact (convex_ball z (dist z q)).isPreconnected.subset_connectedComponentIn
      (Metric.mem_ball_self hzqpos) hsafe
  have hpos : 0 < (star u * (z - q)).im := by
    have he : z - q = t • (Complex.I * u) := by dsimp [z]; abel
    rw [he, mul_smul_comm, Complex.smul_im]
    have hn : (star u * (Complex.I * u)).im = Complex.normSq u := by
      rw [show star u * (Complex.I * u) = Complex.I * (star u * u) by ring,
        Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
    rw [hn]
    exact mul_pos ht (Complex.normSq_pos.mpr hu)
  have hdK := P.face_nearest_openSegment_dartBorders_of_pos hvert K z q d hi hq
    (dist_pos.mp hzqpos) hball hmin hpos
  have hKF : K = F := P.dartBorders_face_unique d K F hdK hF
  refine ⟨r, hr, ?_⟩
  intro y hyr hypos
  rw [← hKF]
  apply P.face_halfDisk_of_local_image K a b q z r 1
    (openSegment_subset_segment ℝ a b hq) hzK
    (by rw [mem_ball, hzq]; linarith only [hsmall, hr])
    (by simpa only [one_mul] using hpos) hlocal y hyr
  simpa only [one_mul] using hypos

/-- Helper toward Proposition 5.16: the left face of the reversed dart
contains the right half-ball along the original dart's segments. -/
theorem exists_ball_right_subset_of_dartBorders_flip
    (hvert : Function.Surjective vert) (d : D) (F : P.Face)
    (hF : P.dartBorders (flip d) F) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) {q : ℂ}
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball q r,
      (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (y - q)).im < 0 →
        y ∈ F.val := by
  let j := (P.arc d).points.length - 2 - i
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
  obtain ⟨r, hr, hhalf⟩ := P.exists_ball_left_subset_of_dartBorders
    hvert (flip d) F hF hj' hq'
  refine ⟨r, hr, ?_⟩
  intro y hyr hyneg
  apply hhalf y hyr
  rw [hfirst, hlast, ← neg_sub ((P.arc d).point (i + 1)) ((P.arc d).point i),
    star_neg, neg_mul, Complex.neg_im]
  exact neg_pos.mpr hyneg

/-- Helper toward Proposition 5.16: the initial boundary ray of a sector
can be approached from within that sector on its strict left side. -/
theorem initialSector_left_approach (d : D) {r ρ s : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hs : 0 < s) :
    ∃ y ∈ P.initialSector d r,
      y ∈ ball (P.pos (vert d) + (ρ : ℂ) *
        Complex.exp (((P.arc d).initialDirection.arg : ℂ) * Complex.I)) s ∧
      0 < (star (P.arc d).initialDirection * (y - P.pos (vert d))).im := by
  let u := (P.arc d).initialDirection
  let α := ccwTurn u (P.arc (rot d)).initialDirection
  let f : ℝ → ℂ := fun θ => P.pos (vert d) + (ρ : ℂ) *
    Complex.exp ((((u.arg + θ : ℝ) : ℂ)) * Complex.I)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hnhds : f ⁻¹' ball (f 0) s ∈ 𝓝 (0 : ℝ) :=
    hf.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hs)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hnhds
  let θ := min δ (min α Real.pi) / 2
  have hθ : 0 < θ := half_pos (lt_min hδ (lt_min (ccwTurn_pos _ _) Real.pi_pos))
  have hθδ : θ < δ :=
    (half_lt_self (lt_min hδ (lt_min (ccwTurn_pos _ _) Real.pi_pos))).trans_le
      (min_le_left _ _)
  have hθα : θ < α :=
    (half_lt_self (lt_min hδ (lt_min (ccwTurn_pos _ _) Real.pi_pos))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hθpi : θ < Real.pi :=
    (half_lt_self (lt_min hδ (lt_min (ccwTurn_pos _ _) Real.pi_pos))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨f θ, ⟨(ρ, θ), ⟨⟨hρ, hρr⟩, hθ, hθα⟩, rfl⟩, ?_, ?_⟩
  · have hmem := hsub (show θ ∈ ball (0 : ℝ) δ by
      simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ] using hθδ)
    simpa only [mem_preimage, f, add_zero] using hmem
  · change 0 < (star u * ((P.pos (vert d) + (ρ : ℂ) *
      Complex.exp ((((u.arg + θ : ℝ) : ℂ)) * Complex.I)) - P.pos (vert d))).im
    rw [add_sub_cancel_left, Complex.star_def, d39_det_polar]
    have hangle : u.arg + θ - u.arg = θ := by ring
    rw [hangle]
    exact mul_pos (mul_pos (norm_pos_iff.mpr (P.initial_nonzero d)) hρ)
      (Real.sin_pos_of_pos_of_lt_pi hθ hθpi)

/-- Helper toward Proposition 5.16: the terminal boundary ray of a sector
can be approached from within that sector on the strict right of its
counterclockwise successor ray. -/
theorem initialSector_right_approach (d : D) {r ρ s : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hs : 0 < s) :
    ∃ y ∈ P.initialSector d r,
      y ∈ ball (P.pos (vert d) + (ρ : ℂ) *
        Complex.exp (((P.arc (rot d)).initialDirection.arg : ℂ) * Complex.I)) s ∧
      (star (P.arc (rot d)).initialDirection * (y - P.pos (vert d))).im < 0 := by
  let u := (P.arc d).initialDirection
  let v := (P.arc (rot d)).initialDirection
  let α := ccwTurn u v
  let f : ℝ → ℂ := fun θ => P.pos (vert d) + (ρ : ℂ) *
    Complex.exp ((((u.arg + θ : ℝ) : ℂ)) * Complex.I)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hnhds : f ⁻¹' ball (f α) s ∈ 𝓝 α :=
    hf.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hs)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hnhds
  let ε := min δ (min α Real.pi) / 2
  have hε : 0 < ε := half_pos (lt_min hδ (lt_min (ccwTurn_pos _ _) Real.pi_pos))
  have hεδ : ε < δ :=
    (half_lt_self (lt_min hδ (lt_min (ccwTurn_pos _ _) Real.pi_pos))).trans_le
      (min_le_left _ _)
  have hεα : ε < α :=
    (half_lt_self (lt_min hδ (lt_min (ccwTurn_pos _ _) Real.pi_pos))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hεpi : ε < Real.pi :=
    (half_lt_self (lt_min hδ (lt_min (ccwTurn_pos _ _) Real.pi_pos))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨f (α - ε), ⟨(ρ, α - ε), ⟨⟨hρ, hρr⟩,
    sub_pos.mpr hεα, sub_lt_self _ hε⟩, rfl⟩, ?_, ?_⟩
  · have hmem := hsub (show α - ε ∈ ball α δ by
      rw [mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hε]
      exact hεδ)
    simpa only [mem_preimage, f, α, d39_exp_arg_add_ccwTurn] using hmem
  · change (star v * ((P.pos (vert d) + (ρ : ℂ) *
      Complex.exp ((((u.arg + (α - ε) : ℝ) : ℂ)) * Complex.I)) -
        P.pos (vert d))).im < 0
    rw [add_sub_cancel_left, Complex.star_def, d39_det_polar]
    have hsin : Real.sin (u.arg + (α - ε) - v.arg) = -Real.sin ε := by
      dsimp [α, ccwTurn]
      split_ifs with huv
      · rw [show u.arg + (v.arg - u.arg - ε) - v.arg = -ε by ring,
          Real.sin_neg]
      · rw [show u.arg + (v.arg - u.arg + 2 * Real.pi - ε) - v.arg =
          -ε + 2 * Real.pi by ring, Real.sin_add_two_pi, Real.sin_neg]
    rw [hsin]
    exact mul_neg_of_pos_of_neg
      (mul_pos (norm_pos_iff.mpr (P.initial_nonzero (rot d))) hρ)
      (neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi hε hεpi))

/-- Helper toward Proposition 5.16: every sufficiently short positive
radius along an initial ray represents an open point of its initial segment. -/
theorem polar_mem_initial_openSegment (d : D) {ρ : ℝ}
    (hρ : 0 < ρ) (hρu : ρ < ‖(P.arc d).initialDirection‖) :
    P.pos (vert d) + (ρ : ℂ) *
        Complex.exp (((P.arc d).initialDirection.arg : ℂ) * Complex.I) ∈
      openSegment ℝ ((P.arc d).point 0) ((P.arc d).point 1) := by
  let u := (P.arc d).initialDirection
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr (P.initial_nonzero d)
  rw [Polyline.point_zero_eq_start, P.arc_start d, openSegment_eq_image']
  refine ⟨ρ / ‖u‖, ⟨div_pos hρ hnu, (div_lt_one hnu).mpr hρu⟩, ?_⟩
  have hdir : (P.arc d).point 1 - P.pos (vert d) = u := by
    rw [← P.arc_start d]
    rfl
  rw [hdir]
  change P.pos (vert d) + (ρ / ‖u‖) • u = _
  rw [Complex.real_smul]
  congr 1
  calc
    (↑(ρ / ‖u‖) : ℂ) * u = ↑(ρ / ‖u‖) *
        ((‖u‖ : ℂ) * Complex.exp ((u.arg : ℂ) * Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
    _ = (ρ : ℂ) * Complex.exp ((u.arg : ℂ) * Complex.I) := by
      rw [Complex.ofReal_div]
      field_simp [Complex.ofReal_ne_zero.mpr hnu.ne']

/-- Helper toward Proposition 5.16: any complementary face containing an
entire initial sector is the face immediately left of its first ray. -/
theorem dartBorders_of_initialSector_subset (hvert : Function.Surjective vert)
    (d : D) {r : ℝ} (hr : 0 < r) (F : P.Face)
    (hsector : P.initialSector d r ⊆ F.val) : P.dartBorders d F := by
  obtain ⟨G, hG⟩ := P.dartBorders_exists_of_wedge_compl d
    (P.wedgeIn_compl_image hvert (P.arc d).start
      (P.arc d).initialDirection (P.initial_nonzero d))
  let u := (P.arc d).initialDirection
  let ρ := min r ‖u‖ / 2
  have hminpos : 0 < min r ‖u‖ := lt_min hr (norm_pos_iff.mpr (P.initial_nonzero d))
  have hρ : 0 < ρ := half_pos hminpos
  have hρr : ρ < r := (half_lt_self hminpos).trans_le (min_le_left _ _)
  have hρu : ρ < ‖u‖ := (half_lt_self hminpos).trans_le (min_le_right _ _)
  let q := P.pos (vert d) + (ρ : ℂ) * Complex.exp ((u.arg : ℂ) * Complex.I)
  have hq : q ∈ openSegment ℝ ((P.arc d).point 0) ((P.arc d).point 1) :=
    P.polar_mem_initial_openSegment d hρ hρu
  obtain ⟨s, hs, hhalf⟩ := P.exists_ball_left_subset_of_dartBorders hvert d G hG
    (by have := P.arc_length d; omega) hq
  obtain ⟨y, hy, hys, hypos⟩ := P.initialSector_left_approach d hρ hρr hs
  have hzero : (star u * (q - P.pos (vert d))).im = 0 := by
    have hqseg := openSegment_subset_segment ℝ _ _ hq
    have h := segment_contact_side_eq_zero ((P.arc d).point 0)
      ((P.arc d).point 1) (P.pos (vert d)) q
      (by rw [Polyline.point_zero_eq_start, P.arc_start d]; exact left_mem_segment ℝ _ _)
      hqseg
    simpa only [u, Polyline.point_zero_eq_start, Polyline.initialDirection, P.arc_start d] using h
  have hyG : y ∈ G.val := by
    apply hhalf y hys
    have heq : y - q = (y - P.pos (vert d)) - (q - P.pos (vert d)) := by abel
    rw [Polyline.point_zero_eq_start, ← Polyline.initialDirection,
      heq, mul_sub, Complex.sub_im]
    change 0 < (star u * (y - P.pos (vert d))).im - (star u * (q - P.pos (vert d))).im
    rw [hzero, sub_zero]
    exact hypos
  have hGF : G = F := P.faces_eq_of_mem hyG (hsector hy)
  exact hGF ▸ hG

/-- Helper toward Proposition 5.16: the same sector is to the left of the
arriving dart obtained by reversing its counterclockwise successor ray. -/
theorem dartBorders_flip_rot_of_initialSector_subset
    (hvert : Function.Surjective vert) (d : D) {r : ℝ} (hr : 0 < r)
    (F : P.Face) (hsector : P.initialSector d r ⊆ F.val) :
    P.dartBorders (flip (rot d)) F := by
  obtain ⟨G, hG⟩ := P.dartBorders_exists_of_wedge_compl (flip (rot d))
    (P.wedgeIn_compl_image hvert (P.arc (flip (rot d))).start
      (P.arc (flip (rot d))).initialDirection (P.initial_nonzero (flip (rot d))))
  let v := (P.arc (rot d)).initialDirection
  let ρ := min r ‖v‖ / 2
  have hminpos : 0 < min r ‖v‖ :=
    lt_min hr (norm_pos_iff.mpr (P.initial_nonzero (rot d)))
  have hρ : 0 < ρ := half_pos hminpos
  have hρr : ρ < r := (half_lt_self hminpos).trans_le (min_le_left _ _)
  have hρv : ρ < ‖v‖ := (half_lt_self hminpos).trans_le (min_le_right _ _)
  let q := P.pos (vert d) + (ρ : ℂ) * Complex.exp ((v.arg : ℂ) * Complex.I)
  have hq : q ∈ openSegment ℝ ((P.arc (rot d)).point 0) ((P.arc (rot d)).point 1) := by
    have h := P.polar_mem_initial_openSegment (rot d) hρ hρv
    simpa only [P.vert_rotation] using h
  obtain ⟨s, hs, hhalf⟩ := P.exists_ball_right_subset_of_dartBorders_flip
    hvert (rot d) G hG (by have := P.arc_length (rot d); omega) hq
  obtain ⟨y, hy, hys, hyneg⟩ := P.initialSector_right_approach d hρ hρr hs
  have hzero : (star v * (q - P.pos (vert d))).im = 0 := by
    have hqseg := openSegment_subset_segment ℝ _ _ hq
    have h := segment_contact_side_eq_zero ((P.arc (rot d)).point 0)
      ((P.arc (rot d)).point 1) (P.pos (vert d)) q
      (by rw [Polyline.point_zero_eq_start, P.arc_start (rot d), P.vert_rotation]
          exact left_mem_segment ℝ _ _)
      hqseg
    simpa only [v, Polyline.point_zero_eq_start, Polyline.initialDirection,
      P.arc_start (rot d), P.vert_rotation] using h
  have hyG : y ∈ G.val := by
    apply hhalf y hys
    have heq : y - q = (y - P.pos (vert d)) - (q - P.pos (vert d)) := by abel
    rw [Polyline.point_zero_eq_start, ← Polyline.initialDirection,
      heq, mul_sub, Complex.sub_im]
    change (star v * (y - P.pos (vert d))).im - (star v * (q - P.pos (vert d))).im < 0
    rw [hzero, sub_zero]
    exact hyneg
  have hGF : G = F := P.faces_eq_of_mem hyG (hsector hy)
  exact hGF ▸ hG

/-- Helper toward Proposition 5.16: turning from a departing dart to the
reverse of its counterclockwise successor preserves its geometric left
face, by the common intervening sector. -/
theorem dartBorders_flip_rot [Finite D] (hvert : Function.Surjective vert)
    (d : D) (F : P.Face) (hF : P.dartBorders d F) :
    P.dartBorders (flip (rot d)) F := by
  obtain ⟨r, hr, G, hsector, _⟩ := P.exists_ball_initialSector_subset_unique_face hvert d
  have hdG := P.dartBorders_of_initialSector_subset hvert d hr G hsector
  have hGF : G = F := P.dartBorders_face_unique d G F hdG hF
  exact hGF ▸ P.dartBorders_flip_rot_of_initialSector_subset hvert d hr G hsector

end PLDrawing

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
  (hvert : Function.Surjective vert)

/-- Helper toward Proposition 5.16: face succession preserves the uniquely
chosen geometric left face. The proof uses the sector between the departing
dart and the reversal of the arriving dart at their shared vertex. -/
theorem plDartFace_faceSucc (d : B.D) :
    B.plDartFace vert P hvert (B.map.faceSucc d) = B.plDartFace vert P hvert d := by
  have hborder : P.dartBorders (B.map.faceSucc d)
      (B.plDartFace vert P hvert (B.map.faceSucc d)) :=
    (B.plDartFace_eq_iff vert P hvert _ _).mp rfl
  have hstep := P.dartBorders_flip_rot hvert _ _ hborder
  have hrev : B.map.edgeInv (B.map.rot (B.map.faceSucc d)) = d := by
    change B.map.edgeInv (B.map.rot (B.map.rot.symm (B.map.edgeInv d))) = d
    rw [Equiv.apply_symm_apply, B.map.edgeInv_invol]
  rw [hrev] at hstep
  exact (B.plDartFace_eq_iff vert P hvert d _).mpr hstep |>.symm

/-- Helper toward Proposition 5.16: all darts in a face-successor orbit
have the same geometric left face. -/
theorem plDartFace_eq_of_sameCycle (d e : B.D)
    (h : B.map.faceSucc.SameCycle d e) :
    B.plDartFace vert P hvert d = B.plDartFace vert P hvert e := by
  let f := B.map.faceSucc
  let face := B.plDartFace vert P hvert
  have hforward (a : B.D) : face (f a) = face a :=
    B.plDartFace_faceSucc vert P hvert a
  have hbackward (a : B.D) : face (f.symm a) = face a := by
    simpa only [Equiv.apply_symm_apply] using (hforward (f.symm a)).symm
  obtain ⟨i, hi⟩ := h
  have hpow (i : ℤ) : face ((f ^ i) d) = face d := by
    refine Int.induction_on i ?_ ?_ ?_
    · simp only [zpow_zero, Equiv.Perm.one_apply]
    · intro i ih
      rw [add_comm (i : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply, hforward, ih]
    · intro i ih
      rw [show (-(i : ℤ) - 1) = -1 + -(i : ℤ) by ring,
        zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      exact (hbackward _).trans ih
  exact (hpow i).symm.trans (congrArg face hi)

/-- Helper toward Proposition 5.16: the geometric face of an actual
face-successor orbit, well-defined by the proved same-cycle invariance.
Injectivity is a separate global geometric obligation. -/
@[expose] def plOrbitFace (O : D39BallFaceCycleOrbit B) : P.Face :=
  B.plDartFace vert P hvert O.property.choose



theorem plOrbitFace_eq_plDartFace_of_mem (O : D39BallFaceCycleOrbit B)
    (d : B.D) (hd : d ∈ O.val) :
    B.plOrbitFace vert P hvert O = B.plDartFace vert P hvert d := by
  apply B.plDartFace_eq_of_sameCycle vert P hvert O.property.choose d
  have hset := O.property.choose_spec
  rw [hset] at hd
  exact hd




theorem plOrbitFace_eq_iff (O : D39BallFaceCycleOrbit B) (d : B.D)
    (hd : d ∈ O.val) (F : P.Face) :
    B.plOrbitFace vert P hvert O = F ↔ P.dartBorders d F := by
  rw [B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O d hd]
  exact B.plDartFace_eq_iff vert P hvert d F

/-- Helper toward Proposition 5.16: every geometric complementary face is
the face of at least one actual face-successor orbit. -/
theorem plOrbitFace_surjective :
    Function.Surjective (B.plOrbitFace vert P hvert) := by
  intro F
  obtain ⟨d, hd⟩ := B.plDartFace_surjective vert P hvert F
  let O : D39BallFaceCycleOrbit B :=
    ⟨{e | B.map.faceSucc.SameCycle d e}, d, rfl⟩
  exact ⟨O, (B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O d
    Equiv.Perm.SameCycle.rfl).trans hd⟩



theorem plOrbitFace_arc_subset_closure (O : D39BallFaceCycleOrbit B)
    (d : B.D) (hd : d ∈ O.val) :
    (P.arc d).image ⊆ closure (B.plOrbitFace vert P hvert O).val := by
  rw [B.plOrbitFace_eq_plDartFace_of_mem vert P hvert O d hd]
  exact B.plDartFace_arc_subset_closure vert P hvert d




theorem exists_closed_plOrbitFace_boundary (O : D39BallFaceCycleOrbit B) :
    ∃ c : Polyline, c.start = c.finish ∧
      c.image = ⋃ d ∈ O.val, (P.arc d).image ∧
      c.image ⊆ closure (B.plOrbitFace vert P hvert O).val := by
  obtain ⟨d, hO⟩ := O.property
  obtain ⟨c, hc, himage⟩ := exists_closed_faceCyclePolyline B vert P d
  refine ⟨c, hc, himage.trans ?_, ?_⟩
  · rw [hO]
  · rw [himage]
    intro z hz
    obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.mp hz
    exact B.plOrbitFace_arc_subset_closure vert P hvert O e (by
      rw [hO]; exact he) hze

end D39FiniteBall

/- Remaining global obligations, not declarations and not assumptions.

U1. Common-face orbit uniqueness (D39BallOrbitComponents.lean:240).

  D39FiniteBall.plDartFace_sameCycle_of_eq
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (d e : B.D)
    (hface : B.plDartFace vert P hvert d = B.plDartFace vert P hvert e) :
    B.map.faceSucc.SameCycle d e

Three approaches investigated after proving local sector propagation:

1. Euler counting. `plOrbitFace_surjective` is now available. Equal finite
   cardinalities would give injectivity. The inspected
   `CombinatorialMapEulerBound.eulerChar_le_two_of_isConnected` bounds
   combinatorial orbit counts; its equality characterization concerns a
   combinatorial cycle space. Neither statement counts complementary
   components. A geometric Euler equality (or the corresponding lower
   installed Mathlib Topology and Combinatorics sources below 1 MiB did
   not locate a geometric plane-graph Euler theorem under these hypotheses.

2. Edge insertion and polygonal separation. The proved polygonal theorem in
   `D39PolygonalConnected2` gives exactly two components for a cyclically
   simple polygon. The drawing is connected by `B.plImage_isConnected`
   using hconn, and closed orbit polylines are now in their face closures.
   However, an orbit polyline may repeat a bridge or a vertex, so that
   theorem cannot be applied directly to it. An insertion proof still
   requires the exact component change for an arc inside a preexisting
   face, both when it joins graph components and when it closes a cycle.
   Separation by a simple polygon alone does not provide that relative
   component-change statement.

3. Propagation along a path in a face. The small vertex sectors and open
   segment half-balls now give the local transitions with the correct
   orientation. The missing global step is a checked passage from an
   arbitrary complementary path between two dart neighborhoods to a chain
   of boundary transitions. Nearest-contact choices used by the existing
   face contact theorem need not vary continuously along such a path.
   Connectedness of the drawing image does not by itself supply this
   boundary-tracing proof. Searches for frontier-connectedness results in
   installed Mathlib Topology did not locate the needed plane continuum
   theorem. The inspected assembly common-face theorem is specific to its
   cap/exterior classification, which arbitrary finite balls do not carry.

U2. Face-orbit equivalence (D39BallOrbitComponents.lean:255).

  D39FiniteBall.plFaceOrbitEquiv
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e) :
    D39BallFaceCycleOrbit B ≃ P.toPlaneGraphDrawing.Face

Three constructions were examined: the now-defined map on actual orbit
sets, a quotient lift using `plDartFace_eq_of_sameCycle`, and selecting a
bordering dart for each geometric face. The first two need injectivity
(U1); the last has a geometric right inverse from coverage but needs U1
for its orbit-valued left inverse. None justifies an equivalence yet.
No face-orbit correspondence, relative Jordan theorem, Euler equality,
coordinator; these compiled helpers do not close Proposition 5.16. -/

end DirectedDistances.PlanarMap

end
