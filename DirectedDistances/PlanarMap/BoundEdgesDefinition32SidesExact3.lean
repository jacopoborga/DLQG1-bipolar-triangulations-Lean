/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact2
public import DirectedDistances.PlanarMap.BoundEdgesMapDrawingBridge32









public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}

/-- Helper toward Definition 3.2: discard only vertices with no incident dart,
retaining the exact polylines and their oriented dart identities. This does
not assert any correspondence of faces. -/
@[expose] def incidentVertexDrawing32 (P : PLDrawing D V flip rot vert) :
    PLDrawing D (Set.range vert) flip rot (fun d => ⟨vert d, ⟨d, rfl⟩⟩) where
  flip_involutive := P.flip_involutive
  flip_ne := P.flip_ne
  vert_rotation := fun d => Subtype.ext (P.vert_rotation d)
  pos := fun v => P.pos v.val
  pos_injective := fun _ _ h => Subtype.ext (P.pos_injective h)
  arc := P.arc
  arc_simple := P.arc_simple
  arc_length := P.arc_length
  arc_start := P.arc_start
  arc_finish := P.arc_finish
  arc_flip := P.arc_flip
  interior_disjoint := P.interior_disjoint
  interior_avoids_vertices := fun d v => P.interior_avoids_vertices d v.val
  locally_finite := P.locally_finite
  initial_nonzero := P.initial_nonzero
  initial_arg_injective := fun d e h =>
    P.initial_arg_injective d e (congrArg Subtype.val h)
  rotation_agreement := by
    intro d
    have hset : {e : D | (⟨vert e, ⟨e, rfl⟩⟩ : Set.range vert) =
        ⟨vert d, ⟨d, rfl⟩⟩} = {e : D | vert e = vert d} := by
      ext e
      exact Subtype.ext_iff
    rw [hset]
    exact P.rotation_agreement d

/-- Helper toward Definition 3.2: the incident-vertex drawing has surjective
dart incidence by construction. -/
theorem incidentVertexDrawing32_surjective (_P : PLDrawing D V flip rot vert) :
    Function.Surjective (fun d : D => (⟨vert d, ⟨d, rfl⟩⟩ : Set.range vert)) := by
  rintro ⟨v, d, rfl⟩
  exact ⟨d, rfl⟩

/-- Helper toward Definition 3.2: deleting nonincident vertices leaves
precisely the union of all arc images. -/
theorem incidentVertexDrawing32_image (P : PLDrawing D V flip rot vert) :
    P.incidentVertexDrawing32.image = ⋃ e, (P.arc e).image := by
  ext z
  constructor
  · rintro (⟨⟨v, d, rfl⟩, rfl⟩ | ⟨d, hd⟩)
    · apply Set.mem_iUnion.mpr
      refine ⟨d, ?_⟩
      change P.pos (vert d) ∈ (P.arc d).image
      rw [← P.arc_start d]
      exact Or.inl rfl
    · exact Set.mem_iUnion.mpr ⟨d, hd⟩
  · intro hz
    exact Or.inr (Set.mem_iUnion.mp hz)

/-- Helper toward Definition 3.2: a locally covered original image has the
same membership as the incident-vertex image on the specified neighborhood.
No component or face equality is asserted. -/
theorem image_mem_iff_incidentVertexDrawing32_of_local_image
    (P : PLDrawing D V flip rot vert) (N : Set ℂ)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image)
    {z : ℂ} (hzN : z ∈ N) :
    z ∈ P.image ↔ z ∈ P.incidentVertexDrawing32.image := by
  rw [P.incidentVertexDrawing32_image]
  constructor
  · intro hz
    exact hlocal z hz hzN
  · intro hz
    exact Or.inr (Set.mem_iUnion.mp hz)

/-- Helper toward Definition 3.2: local arc coverage suffices to isolate a
strict segment contact in the original drawing, including its vertices. -/
theorem openSegment_contact_local_image_of_local_image
    (P : PLDrawing D V flip rot vert) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) {q : ℂ}
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (N : Set ℂ) (hopen : IsOpen N) (hqN : q ∈ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ N ∧
      ∀ y ∈ ball q r, y ∈ P.image → y ∈ (P.arc d).segmentAt i := by
  obtain ⟨r, hr, hcontact⟩ := P.incidentVertexDrawing32.openSegment_contact_local_image
    (P.incidentVertexDrawing32_surjective) d hi hq
  obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp hopen q hqN
  refine ⟨min r s, lt_min hr hs, ?_, ?_⟩
  · exact (ball_subset_ball (min_le_right r s)).trans hball
  · intro y hy hyP
    exact hcontact y (ball_subset_ball (min_le_left r s) hy)
      ((P.image_mem_iff_incidentVertexDrawing32_of_local_image N hlocal
        (hball (ball_subset_ball (min_le_right r s) hy))).mp hyP)

/-- Helper toward Definition 3.2: local arc coverage identifies the original
drawing near an interior bend with exactly its two incident segments. -/
theorem bend_contact_local_image_of_local_image
    (P : PLDrawing D V flip rot vert) (d : D) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (N : Set ℂ) (hopen : IsOpen N) (hqN : (P.arc d).point (i + 1) ∈ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∃ r : ℝ, 0 < r ∧ ball ((P.arc d).point (i + 1)) r ⊆ N ∧
      ∀ y ∈ ball ((P.arc d).point (i + 1)) r,
        y ∈ P.image ↔ y ∈ (P.arc d).segmentAt i ∪ (P.arc d).segmentAt (i + 1) := by
  obtain ⟨r, hr, hcontact⟩ := P.incidentVertexDrawing32.bend_contact_local_image
    (P.incidentVertexDrawing32_surjective) d hi
  obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp hopen _ hqN
  refine ⟨min r s, lt_min hr hs, ?_, ?_⟩
  · exact (ball_subset_ball (min_le_right r s)).trans hball
  · intro y hy
    exact (P.image_mem_iff_incidentVertexDrawing32_of_local_image N hlocal
      (hball (ball_subset_ball (min_le_right r s) hy))).trans
      (hcontact y (ball_subset_ball (min_le_left r s) hy))

/-- Helper toward Definition 3.2: local arc coverage gives a uniform
isolation radius along a compact subsegment of one open drawing segment. -/
theorem openSegment_uniform_local_image_of_local_image
    (P : PLDrawing D V flip rot vert) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) (q₁ q₂ : ℂ)
    (hq₁ : q₁ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hq₂ : q₂ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (N : Set ℂ) (hopen : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ segment ℝ q₁ q₂,
      ∀ y ∈ ball q r, y ∈ P.image → y ∈ (P.arc d).segmentAt i := by
  let W := interior (P.imageᶜ ∪ (P.arc d).segmentAt i)
  have hsub : segment ℝ q₁ q₂ ⊆ W := by
    intro q hq
    have hqo := (convex_openSegment _ _).segment_subset hq₁ hq₂ hq
    have hqN : q ∈ N := by
      apply harc
      rw [Polyline.range_toPath]
      exact (P.arc d).segmentAt_subset_image hi
        (openSegment_subset_segment ℝ _ _ hqo)
    obtain ⟨r, hr, _, hcontact⟩ :=
      P.openSegment_contact_local_image_of_local_image d hi hqo N hopen hqN hlocal
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (ball_mem_nhds q hr)
    intro y hy
    by_cases hyP : y ∈ P.image
    · exact Or.inr (hcontact y hy hyP)
    · exact Or.inl hyP
  have hcompact : IsCompact (segment ℝ q₁ q₂) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist hcompact
    isOpen_interior.isClosed_compl (disjoint_compl_right.mono_left hsub)
  refine ⟨r, by exact_mod_cast hr, ?_⟩
  intro q hq y hy hyP
  have hyW : y ∈ W := by
    by_contra hyW
    have hlt : edist q y < (r : ENNReal) := by
      rw [edist_lt_coe, ← dist_lt_coe, dist_comm]
      exact hy
    exact (not_lt_of_gt (hsep q hq y hyW)) hlt
  exact (interior_subset hyW).resolve_left (fun h => h hyP)

/-- Helper toward Definition 3.2: a sufficiently thin punctured normal
strip along a compact open subsegment avoids the original drawing image. -/
theorem openSegment_normal_strip_compl_of_local_image
    (P : PLDrawing D V flip rot vert) (d : D) {i : ℕ}
    (hi : i + 1 < (P.arc d).points.length) (q₁ q₂ : ℂ)
    (hq₁ : q₁ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (hq₂ : q₂ ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (N : Set ℂ) (hopen : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ segment ℝ q₁ q₂, ∀ t : ℝ,
      0 < |t| → |t| < δ →
      q + t • (Complex.I * ((P.arc d).point (i + 1) - (P.arc d).point i)) ∉ P.image := by
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let u := b - a
  let v := Complex.I * u
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  obtain ⟨r, hr, hcontact⟩ := P.openSegment_uniform_local_image_of_local_image
    d hi q₁ q₂ hq₁ hq₂ N hopen harc hlocal
  let δ := r / (2 * (‖v‖ + 1))
  have hden : 0 < 2 * (‖v‖ + 1) := by positivity
  refine ⟨δ, div_pos hr hden, ?_⟩
  intro q hq t ht htd hP
  have hprod : |t| * (2 * (‖v‖ + 1)) < r := (lt_div_iff₀ hden).mp htd
  have hball : q + t • v ∈ ball q r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    nlinarith only [hprod, ht, norm_nonneg v]
  have hseg : q + t • v ∈ segment ℝ a b := hcontact q hq _ hball hP
  have hqseg : q ∈ segment ℝ a b := openSegment_subset_segment ℝ a b
    ((convex_openSegment a b).segment_subset hq₁ hq₂ hq)
  have hzero := segment_contact_side_eq_zero a b q (q + t • v) hqseg hseg
  have hnormal := segment_normal_offset_side a b q q t hqseg hqseg
  exact (mul_ne_zero (abs_pos.mp ht) (ne_of_gt (Complex.normSq_pos.mpr hu)))
    (hnormal.symm.trans hzero)

/-- Helper toward Definition 3.2: the bordering face contains a left
half-disk at every strict point of the first segment under local coverage. -/
theorem dartBorders_firstSegment_left_halfDisk_of_local_image
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (hborder : P.dartBorders d F) (q : ℂ)
    (hq : q ∈ openSegment ℝ ((P.arc d).point 0) ((P.arc d).point 1))
    (N : Set ℂ) (hopen : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball q r,
      0 < (star ((P.arc d).point 1 - (P.arc d).point 0) * (y - q)).im →
        y ∈ F.val := by
  let a := (P.arc d).point 0
  let b := (P.arc d).point 1
  let u := b - a
  have hi : 0 + 1 < (P.arc d).points.length := by have := P.arc_length d; omega
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 0 hi).symm
  obtain ⟨δ, hδ, hwedge⟩ := hborder
  let t₀ := min (δ / 2) (1 / 2 : ℝ)
  have ht₀ : 0 < t₀ := lt_min (half_pos hδ) (by norm_num)
  have ht₀δ : t₀ < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have ht₀1 : t₀ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let q₀ := a + t₀ • u
  have hq₀ : q₀ ∈ openSegment ℝ a b := by
    rw [openSegment_eq_image']
    exact ⟨t₀, ⟨ht₀, ht₀1⟩, rfl⟩
  obtain ⟨ρ, hρ, hstrip⟩ := P.openSegment_normal_strip_compl_of_local_image
    d hi q₀ q hq₀ hq N hopen harc hlocal
  have hqN : q ∈ N := by
    apply harc
    rw [Polyline.range_toPath]
    exact (P.arc d).segmentAt_subset_image hi (openSegment_subset_segment ℝ a b hq)
  obtain ⟨r, hr, _, hcontact⟩ :=
    P.openSegment_contact_local_image_of_local_image d hi hq N hopen hqN hlocal
  let t := min (ρ / 2) (min (t₀ * δ / 2) (r / (2 * (‖Complex.I * u‖ + 1))))
  have ht : 0 < t := lt_min (half_pos hρ)
    (lt_min (half_pos (mul_pos ht₀ hδ)) (div_pos hr (by positivity)))
  have htρ : t < ρ := (min_le_left _ _).trans_lt (half_lt_self hρ)
  have htδ : t / t₀ < δ := by
    apply (div_lt_iff₀ ht₀).mpr
    have hle := (min_le_right (ρ / 2)
      (min (t₀ * δ / 2) (r / (2 * (‖Complex.I * u‖ + 1))))).trans (min_le_left _ _)
    dsimp only [t] at *
    nlinarith only [hle, mul_pos ht₀ hδ]
  let w₀ := q₀ + t • (Complex.I * u)
  have hw₀ : w₀ ∈ F.val := by
    have hw := hwedge t₀ (t / t₀) ht₀ ht₀δ (div_pos ht ht₀) htδ
    convert hw using 1
    have huinit : (P.arc d).initialDirection = u := by
      simp only [u, b, a, Polyline.initialDirection, Polyline.point_zero_eq_start]
    have ht₀C : (t₀ : ℂ) ≠ 0 := by exact_mod_cast ht₀.ne'
    dsimp only [w₀, q₀]
    rw [show a = (P.arc d).start from Polyline.point_zero_eq_start _, huinit]
    simp only [Complex.real_smul, Complex.ofReal_div]
    field_simp [ht₀C]
    ring
  let f : ℂ → ℂ := fun x => x + t • (Complex.I * u)
  have hpre : IsPreconnected (f '' segment ℝ q₀ q) :=
    (convex_segment q₀ q).isPreconnected.image f (by dsimp [f]; fun_prop)
  have hsafe : f '' segment ℝ q₀ q ⊆ P.imageᶜ := by
    rintro y ⟨x, hx, rfl⟩
    exact hstrip x hx t (abs_pos.mpr ht.ne') (by rw [abs_of_pos ht]; exact htρ)
  have hsub : f '' segment ℝ q₀ q ⊆ F.val := by
    obtain ⟨z, _, hF⟩ := F.property
    rw [hF] at hw₀ ⊢
    rw [connectedComponentIn_eq hw₀]
    exact hpre.subset_connectedComponentIn
      ⟨q₀, left_mem_segment ℝ q₀ q, rfl⟩ hsafe
  have hw : q + t • (Complex.I * u) ∈ F.val :=
    hsub ⟨q, right_mem_segment ℝ q₀ q, rfl⟩
  have hwr : q + t • (Complex.I * u) ∈ ball q r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    have hle := (min_le_right (ρ / 2)
      (min (t₀ * δ / 2) (r / (2 * (‖Complex.I * u‖ + 1))))).trans (min_le_right _ _)
    have hprod := (le_div_iff₀ (by positivity : 0 < 2 * (‖Complex.I * u‖ + 1))).mp hle
    nlinarith only [hprod, ht, norm_nonneg (Complex.I * u)]
  have hside : 0 < (1 : ℝ) *
      (star u * (q + t • (Complex.I * u) - q)).im := by
    rw [segment_normal_offset_side a b q q t
      (openSegment_subset_segment ℝ a b hq) (openSegment_subset_segment ℝ a b hq), one_mul]
    exact mul_pos ht (Complex.normSq_pos.mpr hu)
  refine ⟨r, hr, ?_⟩
  intro y hy hys
  exact P.face_halfDisk_of_local_image F a b q (q + t • (Complex.I * u)) r 1
    (openSegment_subset_segment ℝ a b hq) hw hwr hside hcontact y hy
    (by simpa only [one_mul] using hys)

/-- Helper toward Definition 3.2: local coverage provides small semicircular
return paths through the bordering face along the first segment. -/
theorem dartBorders_firstSegment_leftSemicircle_of_local_image
    (P : PLDrawing D V flip rot vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) (x : ℂ)
    (hx : x ∈ openSegment ℝ ((P.arc d).point 0) ((P.arc d).point (0 + 1)))
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      (x - ε • ((P.arc d).point (0 + 1) - (P.arc d).point 0) ∈
        openSegment ℝ ((P.arc d).point 0) ((P.arc d).point (0 + 1))) ∧
      (x + ε • ((P.arc d).point (0 + 1) - (P.arc d).point 0) ∈
        openSegment ℝ ((P.arc d).point 0) ((P.arc d).point (0 + 1))) ∧
      Function.Injective
        (leftSemicircle x (ε • ((P.arc d).point (0 + 1) - (P.arc d).point 0))) ∧
      ∀ t : I, t ∈ openParams →
        leftSemicircle x (ε • ((P.arc d).point (0 + 1) - (P.arc d).point 0)) t ∈
          F.val := by
  have hi : 0 + 1 < (P.arc d).points.length := by have := P.arc_length d; omega
  let u := (P.arc d).point (0 + 1) - (P.arc d).point 0
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 0 hi).symm
  obtain ⟨r, hr, hhalf⟩ :=
    P.dartBorders_firstSegment_left_halfDisk_of_local_image d F hborder x hx N hN harc hlocal
  obtain ⟨δseg, hδseg, hend⟩ := openSegment_small_symmetric_endpoints
    ((P.arc d).point 0) ((P.arc d).point (0 + 1)) x hx
  let δ := min δseg (r / (‖u‖ + 1))
  have hδ : 0 < δ := lt_min hδseg (div_pos hr (by positivity))
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hεu : ε • u ≠ 0 := smul_ne_zero hε.ne' hu
  obtain ⟨hleft, hright⟩ := hend ε hε (hεδ.trans_le (min_le_left _ _))
  refine ⟨hleft, hright, leftSemicircle_injective x (ε • u) hεu, ?_⟩
  intro t ht
  apply hhalf _
  · rw [Metric.mem_ball, leftSemicircle_dist, norm_smul, Real.norm_eq_abs,
      abs_of_pos hε]
    have he : ε * (‖u‖ + 1) < r :=
      (lt_div_iff₀ (by positivity)).mp (hεδ.trans_le (min_le_right _ _))
    nlinarith only [he, hε]
  · have hp := leftSemicircle_side_pos x (ε • u) hεu t ht
    have he : (star (ε • u) *
        (leftSemicircle x (ε • u) t - x)).im =
        ε * (star u * (leftSemicircle x (ε • u) t - x)).im := by
      rw [star_smul, star_trivial, smul_mul_assoc, Complex.smul_im, smul_eq_mul]
    rw [he] at hp
    exact ((mul_pos_iff.mp hp).resolve_right
      (fun h => (not_lt_of_gt hε) h.1)).2

/-- Helper toward Definition 3.2: at an open-segment
contact, a semicircular return path lies in the bordering face, and points
of that face with winding number one accumulate at the contact. This is
the geometric local loop, before identifying it with `edgeSubarc`. -/
theorem dartBorders_firstSegment_semicircleLoop_of_local_image
    (P : PLDrawing D V flip rot vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F) (x : ℂ)
    (hx : x ∈ openSegment ℝ ((P.arc d).point 0) ((P.arc d).point (0 + 1)))
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∃ ε : ℝ, 0 < ε ∧
      (x - ε • ((P.arc d).point (0 + 1) - (P.arc d).point 0) ∈
        openSegment ℝ ((P.arc d).point 0) ((P.arc d).point (0 + 1))) ∧
      (x + ε • ((P.arc d).point (0 + 1) - (P.arc d).point 0) ∈
        openSegment ℝ ((P.arc d).point 0) ((P.arc d).point (0 + 1))) ∧
      Function.Injective
        (leftSemicircle x (ε • ((P.arc d).point (0 + 1) - (P.arc d).point 0))) ∧
      (∀ t : I, t ∈ openParams →
        leftSemicircle x (ε • ((P.arc d).point (0 + 1) - (P.arc d).point 0)) t ∈
          F.val) ∧
      x ∈ closure {w : ℂ | w ∈ F.val ∧
        HasWinding
          (semicircleLoop x (ε • ((P.arc d).point (0 + 1) - (P.arc d).point 0)))
          w 1} := by
  have hi : 0 + 1 < (P.arc d).points.length := by have := P.arc_length d; omega
  let u := (P.arc d).point (0 + 1) - (P.arc d).point 0
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 0 hi).symm
  obtain ⟨δ, hδ, hreturn⟩ :=
    P.dartBorders_firstSegment_leftSemicircle_of_local_image d F hborder x hx N hN harc hlocal
  obtain ⟨r, hr, hhalf⟩ :=
    P.dartBorders_firstSegment_left_halfDisk_of_local_image d F hborder x hx N hN harc hlocal
  let ε := min (δ / 2) (r / (2 * (‖u‖ + 1)))
  have hε : 0 < ε := lt_min (by positivity) (div_pos hr (by positivity))
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith only [hδ])
  have hεr : ε * (2 * (‖u‖ + 1)) ≤ r :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let v := ε • u
  have hv : v ≠ 0 := smul_ne_zero hε.ne' hu
  have hvnorm : ‖v‖ = ε * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have hvr : ‖v‖ < r := by
    rw [hvnorm]
    exact (mul_lt_mul_of_pos_left (by linarith only [norm_nonneg u]) hε).trans_le hεr
  obtain ⟨hleft, hright, hinj, hopen⟩ := hreturn ε hε hεδ
  refine ⟨ε, hε, hleft, hright, hinj, hopen, Metric.mem_closure_iff.mpr ?_⟩
  intro η hη
  let τ := min (1 / 2) (η / (2 * (‖v‖ + 1)))
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hτ1 : τ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hτη : τ * (2 * (‖v‖ + 1)) ≤ η :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let w := x + v * (τ * Complex.I)
  have hwx : dist w x = τ * ‖v‖ := by
    rw [dist_eq_norm]
    change ‖x + v * (τ * Complex.I) - x‖ = _
    rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hτ, Complex.norm_I, mul_one, mul_comm]
  have hwF : w ∈ F.val := by
    apply hhalf _
    · rw [Metric.mem_ball, hwx]
      exact (mul_lt_of_lt_one_left (norm_pos_iff.mpr hv) hτ1).trans hvr
    · have he : star u * (w - x) =
          ((ε * τ : ℝ) : ℂ) * Complex.I * (star u * u) := by
        dsimp [w, v]
        push_cast
        ring
      rw [he, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        sub_zero, add_zero, mul_one, zero_add]
      exact mul_pos (mul_pos hε hτ) (Complex.normSq_pos.mpr hu)
  refine ⟨w, ⟨hwF, hasWinding_semicircleLoop x v hv τ hτ hτ1⟩, ?_⟩
  rw [dist_comm, hwx]
  exact (mul_lt_mul_of_pos_left (by linarith only [norm_nonneg v]) hτ).trans_le hτη

/-- Helper toward Definition 3.2: an open segment point has a unique
strictly interior affine coordinate. -/
private theorem openSegment_affine_coordinate (a b x : ℂ)
    (hx : x ∈ openSegment ℝ a b) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ x = a + (r : ℂ) * (b - a) := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨r, hr, hx⟩ := hx
  refine ⟨r, hr.1, hr.2, ?_⟩
  rw [AffineMap.lineMap_apply_module] at hx
  rw [Complex.real_smul] at hx
  calc
    x = ((1 - r : ℝ) : ℂ) * a + (r : ℂ) * b := hx.symm
    _ = a + (r : ℂ) * (b - a) := by push_cast; ring

/-- Helper toward Definition 3.2: affine coordinates on a nondegenerate
segment are unique. -/
private theorem affine_coordinate_unique {a u : ℂ} (hu : u ≠ 0)
    {r t : ℝ} (h : a + (r : ℂ) * u = a + (t : ℂ) * u) : r = t := by
  have hmul : ((r : ℂ) - (t : ℂ)) * u = 0 := by
    have hc := congrArg (fun z : ℂ => z - a) h
    simp only [add_sub_cancel_left] at hc
    rw [sub_mul, hc, sub_self]
  rcases mul_eq_zero.mp hmul with hrt | hzero
  · exact_mod_cast sub_eq_zero.mp hrt
  · exact (hu hzero).elim

/-- Helper toward Definition 3.2: each strict interior affine coordinate
selects a parameter in the corresponding recursively halved PL segment. -/
private def parameterAtSegmentFraction (p : Polyline) (i : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hr' : r ≤ 1) : I :=
  ⟨Polyline.segmentParameterStart i + r *
      (Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i), by
    have hs := Polyline.segmentParameterStart_mem_Icc i
    have he := Polyline.segmentParameterEnd_mem_Icc p.points.length i
    have hlen := Polyline.segmentParameterStart_le_end p.points.length i
    constructor
    · have hprod : 0 ≤ r *
          (Polyline.segmentParameterEnd p.points.length i -
            Polyline.segmentParameterStart i) :=
        mul_nonneg hr (sub_nonneg.mpr hlen)
      linarith
    · have hprod : 0 ≤ (1 - r) *
          (1 - Polyline.segmentParameterStart i) :=
        mul_nonneg (sub_nonneg.mpr hr') (sub_nonneg.mpr hs.2)
      have hprod' : 0 ≤ r *
          (1 - Polyline.segmentParameterEnd p.points.length i) :=
        mul_nonneg hr (sub_nonneg.mpr he.2)
      change Polyline.segmentParameterStart i + r *
          (Polyline.segmentParameterEnd p.points.length i -
            Polyline.segmentParameterStart i) ≤ 1
      nlinarith [hprod, hprod']⟩

/-- Helper toward Definition 3.2: the parameter selected by an affine
coordinate evaluates to that same point on the PL segment. -/
private theorem toPath_parameterAtSegmentFraction (p : Polyline) {i : ℕ}
    (hi : i + 1 < p.points.length) (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1) :
    p.toPath (parameterAtSegmentFraction p i r hr hr') =
      p.point i + (r : ℂ) * (p.point (i + 1) - p.point i) := by
  have hparam := Polyline.toPath_segment_affine_apply p hi
  have hstart : Polyline.segmentParameterStart i ≤
      (parameterAtSegmentFraction p i r hr hr' : ℝ) := by
    simp only [parameterAtSegmentFraction]
    have hlen := Polyline.segmentParameterStart_le_end p.points.length i
    nlinarith
  have hend : (parameterAtSegmentFraction p i r hr hr' : ℝ) ≤
      Polyline.segmentParameterEnd p.points.length i := by
    simp only [parameterAtSegmentFraction]
    have hlen := Polyline.segmentParameterStart_le_end p.points.length i
    nlinarith
  have h := hparam (parameterAtSegmentFraction p i r hr hr') hstart hend
  change p.toPath (parameterAtSegmentFraction p i r hr hr') = _
  rw [h]
  have hlen : 0 < Polyline.segmentParameterEnd p.points.length i -
      Polyline.segmentParameterStart i :=
    sub_pos.mpr (Polyline.segmentParameterStart_lt_end p.points.length i)
  have hratio :
      (((parameterAtSegmentFraction p i r hr hr' : ℝ) -
          Polyline.segmentParameterStart i) /
        (Polyline.segmentParameterEnd p.points.length i -
          Polyline.segmentParameterStart i)) = r := by
    simp only [parameterAtSegmentFraction]
    field_simp
    ring
  rw [hratio]

/-- Helper toward Definition 3.2: the localized winding-side bridge holds at
parameters strictly inside the first segment. Later segments and bends are
separate propagation obligations. -/
theorem dartBorders_toPath_leftAtOn_of_local_image_of_firstSegment
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (s : {t : I // t ∈ openParams})
    (hstart : Polyline.segmentParameterStart 0 < (s.1 : ℝ))
    (hend : (s.1 : ℝ) < Polyline.segmentParameterEnd (P.arc d).points.length 0)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    LeftAtOn F.val (P.arc d).toPath s := by
  have hi : 0 + 1 < (P.arc d).points.length := by have := P.arc_length d; omega
  let p := P.arc d
  let u := p.point (0 + 1) - p.point 0
  let x := p.toPath s.1
  have hx := Polyline.toPath_mem_openSegment_of_parameter p hi s.1 hstart hend
  obtain ⟨r, hr0, hr1, hxcoord⟩ :=
    openSegment_affine_coordinate (p.point 0) (p.point (0 + 1)) x hx
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 0 hi).symm
  have hform := Polyline.toPath_segment_affine_apply p hi
  dsimp only at hform
  have hform' := hform s.1 (le_of_lt hstart) (le_of_lt hend)
  let θ : ℝ := ((s.1 : ℝ) - Polyline.segmentParameterStart 0) /
    (Polyline.segmentParameterEnd p.points.length 0 -
      Polyline.segmentParameterStart 0)
  have hpath : p.toPath s.1 = p.point 0 + (θ : ℂ) * u := by
    simpa only [u, θ] using hform'
  have hratio : θ = r := by
    apply affine_coordinate_unique hu
    calc
      p.point 0 + (θ : ℂ) * u = p.toPath s.1 := hpath.symm
      _ = x := rfl
      _ = p.point 0 + (r : ℂ) * u := hxcoord
  have hratio' :
      (((s.1 : ℝ) - Polyline.segmentParameterStart 0) /
        (Polyline.segmentParameterEnd p.points.length 0 -
          Polyline.segmentParameterStart 0)) = r := hratio
  obtain ⟨ε, hε, hleft, hright, hinj, hopen, hcl⟩ :=
    P.dartBorders_firstSegment_semicircleLoop_of_local_image d F hborder x hx N hN harc hlocal
  obtain ⟨rl, hrl0, hrl1, hleftcoord⟩ :=
    openSegment_affine_coordinate (p.point 0) (p.point (0 + 1))
      (x - ε • u) hleft
  obtain ⟨rr, hrr0, hrr1, hrightcoord⟩ :=
    openSegment_affine_coordinate (p.point 0) (p.point (0 + 1))
      (x + ε • u) hright
  have hleftformula : x - ε • u =
      p.point 0 + ((r - ε : ℝ) : ℂ) * u := by
    rw [hxcoord, Complex.real_smul]
    push_cast
    ring
  have hrightformula : x + ε • u =
      p.point 0 + ((r + ε : ℝ) : ℂ) * u := by
    rw [hxcoord, Complex.real_smul]
    push_cast
    ring
  have hrl : rl = r - ε :=
    affine_coordinate_unique hu (hleftcoord.symm.trans hleftformula)
  have hrr : rr = r + ε :=
    affine_coordinate_unique hu (hrightcoord.symm.trans hrightformula)
  let a := parameterAtSegmentFraction p 0 (r - ε) (by linarith) (by linarith)
  let b := parameterAtSegmentFraction p 0 (r + ε) (by linarith) (by linarith)
  have haEval : p.toPath a = x - ε • u := by
    have h := toPath_parameterAtSegmentFraction p hi (r - ε) (by linarith) (by linarith)
    change p.toPath (parameterAtSegmentFraction p 0 (r - ε) _ _) = _
    rw [h, hleftformula]
  have hbEval : p.toPath b = x + ε • u := by
    have h := toPath_parameterAtSegmentFraction p hi (r + ε) (by linarith) (by linarith)
    change p.toPath (parameterAtSegmentFraction p 0 (r + ε) _ _) = _
    rw [h, hrightformula]
  have hlen : 0 < Polyline.segmentParameterEnd p.points.length 0 -
      Polyline.segmentParameterStart 0 :=
    sub_pos.mpr (Polyline.segmentParameterStart_lt_end p.points.length 0)
  have hsval : (s.1 : ℝ) = Polyline.segmentParameterStart 0 + r *
      (Polyline.segmentParameterEnd p.points.length 0 -
        Polyline.segmentParameterStart 0) := by
    have hratio'' := (div_eq_iff (ne_of_gt hlen)).mp hratio'
    linarith
  have hab : a < b := by
    change (a : ℝ) < (b : ℝ)
    dsimp [a, b, parameterAtSegmentFraction]
    nlinarith [mul_pos hε hlen]
  have has : a < s.1 := by
    change (a : ℝ) < (s.1 : ℝ)
    dsimp [a, parameterAtSegmentFraction]
    rw [hsval]
    nlinarith [mul_pos hε hlen]
  have hsb : s.1 < b := by
    change (s.1 : ℝ) < (b : ℝ)
    dsimp [b, parameterAtSegmentFraction]
    rw [hsval]
    nlinarith [mul_pos hε hlen]
  have hfracA : 0 < r - ε := by rw [← hrl]; exact hrl0
  have hfracB : r + ε < 1 := by rw [← hrr]; exact hrr1
  have ha : 0 < (a : ℝ) := by
    change 0 < Polyline.segmentParameterStart 0 + (r - ε) *
      (Polyline.segmentParameterEnd p.points.length 0 -
        Polyline.segmentParameterStart 0)
    exact lt_of_le_of_lt (Polyline.segmentParameterStart_mem_Icc 0).1
      (by nlinarith [mul_pos hfracA hlen])
  have hb : (b : ℝ) < 1 := by
    have hbend : (b : ℝ) < Polyline.segmentParameterEnd p.points.length 0 := by
      change Polyline.segmentParameterStart 0 + (r + ε) *
        (Polyline.segmentParameterEnd p.points.length 0 -
          Polyline.segmentParameterStart 0) < _
      exact (by nlinarith [mul_pos (sub_pos.mpr hfracB) hlen])
    exact lt_of_lt_of_le hbend (Polyline.segmentParameterEnd_mem_Icc
      p.points.length 0).2
  have hstartA : Polyline.segmentParameterStart 0 ≤ (a : ℝ) := by
    change Polyline.segmentParameterStart 0 ≤ Polyline.segmentParameterStart 0 +
      (r - ε) * (Polyline.segmentParameterEnd p.points.length 0 -
        Polyline.segmentParameterStart 0)
    exact le_add_of_nonneg_right (mul_nonneg (le_of_lt hfracA) hlen.le)
  have hBend : (b : ℝ) ≤ Polyline.segmentParameterEnd p.points.length 0 := by
    change Polyline.segmentParameterStart 0 + (r + ε) *
      (Polyline.segmentParameterEnd p.points.length 0 -
        Polyline.segmentParameterStart 0) ≤ _
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hfracB) hlen.le
    nlinarith [hmul]
  have hline : ∀ t : I, a ≤ t → t ≤ b →
      p.toPath t = p.toPath a +
        (((((t : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) : ℝ) : ℂ) *
          (p.toPath b - p.toPath a)) := by
    intro t hta htb
    have ht0 := hform t
      (le_trans hstartA (by exact_mod_cast hta))
      (le_trans (by exact_mod_cast htb) hBend)
    have hdenab : (b : ℝ) - (a : ℝ) = 2 * ε *
        (Polyline.segmentParameterEnd p.points.length 0 -
          Polyline.segmentParameterStart 0) := by
      dsimp [a, b, parameterAtSegmentFraction]
      ring
    have hratio_t :
        ((t : ℝ) - Polyline.segmentParameterStart 0) /
            (Polyline.segmentParameterEnd p.points.length 0 -
              Polyline.segmentParameterStart 0) =
          (r - ε) + (((t : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (2 * ε) := by
      rw [hdenab]
      dsimp [a, b, parameterAtSegmentFraction]
      field_simp [ne_of_gt hlen, hε.ne']
      ring
    have hratioC :
        (((((t : ℝ) - Polyline.segmentParameterStart 0) /
          (Polyline.segmentParameterEnd p.points.length 0 -
            Polyline.segmentParameterStart 0)) : ℝ) : ℂ) =
          (((r - ε) + (((t : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) *
            (2 * ε) : ℝ) : ℂ) := by
      exact congrArg (fun z : ℝ => (z : ℂ)) hratio_t
    rw [ht0, haEval, hbEval, hleftformula, hrightformula]
    rw [hratioC]
    dsimp [u]
    push_cast
    ring_nf
  let φ : I → I := fun t => ⟨
    (((min (max t a) b : I) : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)), by
      have hca : a ≤ min (max t a) b := le_min (le_max_right _ _) hab.le
      have hcb : min (max t a) b ≤ b := min_le_right _ _
      constructor
      · exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hca))
          (sub_nonneg.mpr (by exact_mod_cast hab.le))
      · rw [div_le_one (sub_pos.mpr (by exact_mod_cast hab))]
        exact sub_le_sub_right (by exact_mod_cast hcb) _⟩
  have hφc : Continuous φ := by
    dsimp [φ]
    fun_prop
  have hφ0 : φ 0 = 0 := by
    apply Subtype.ext
    simp [φ, min_eq_left hab.le]
  have hφ1 : φ 1 = 1 := by
    apply Subtype.ext
    have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    have hden : (b : ℝ) - (a : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hab')
    change (((min (max (1 : I) a) b : I) : ℝ) - (a : ℝ)) /
      ((b : ℝ) - (a : ℝ)) = 1
    rw [max_eq_left (show a ≤ (1 : I) from a.property.2)]
    have hmin : min (1 : I) b = b := min_eq_right b.property.2
    rw [hmin]
    exact div_self hden
  have hEdgeFun : ∀ t : I,
      (edgeSubarc p.toPath a b (le_of_lt hab)).cast
        haEval.symm hbEval.symm t =
          Path.segment (x - ε • u) (x + ε • u) (φ t) := by
    intro t
    change edgeSubarc p.toPath a b (le_of_lt hab) t = _
    rw [edgeSubarc_affine_apply p.toPath hab hline t]
    rw [Path.segment_apply, AffineMap.lineMap_apply_module']
    simp only [Complex.real_smul]
    rw [haEval, hbEval]
    dsimp [φ]
    push_cast
    ring_nf
  have hEdge :
      (edgeSubarc p.toPath a b (le_of_lt hab)).cast haEval.symm hbEval.symm =
        (Path.segment (x - ε • u) (x + ε • u)).reparam φ hφc hφ0 hφ1 := by
    apply Path.ext
    funext t
    exact hEdgeFun t
  let q : Path (p.toPath b) (p.toPath a) :=
    (leftSemicircle x (ε • u)).cast hbEval haEval
  have hqinj : Function.Injective q := by
    intro t t' htt'
    exact hinj htt'
  have hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val := by
    intro t ht
    exact hopen t ht
  let α : Path (x - ε • u) (x + ε • u) := Path.segment _ _
  let β : Path (x + ε • u) (x - ε • u) := leftSemicircle x (ε • u)
  let E : Path (x - ε • u) (x + ε • u) :=
    (edgeSubarc p.toPath a b (le_of_lt hab)).cast haEval.symm hbEval.symm
  let L : Path (p.toPath a) (p.toPath a) :=
    (edgeSubarc p.toPath a b (le_of_lt hab)).trans q
  let M : Path (x - ε • u) (x - ε • u) := E.trans β
  let N : Path (x - ε • u) (x - ε • u) :=
    ((Path.segment (x - ε • u) (x + ε • u)).reparam φ hφc hφ0 hφ1).trans β
  have hMN : M = N := by
    dsimp [M, N, E, α, β]
    exact congrArg (fun γ : Path _ _ => γ.trans (leftSemicircle x (ε • u))) hEdge
  have hLM : ∀ t : I, L t = M t := by
    intro t
    change ((edgeSubarc p.toPath a b (le_of_lt hab)).trans q) t =
      (((edgeSubarc p.toPath a b (le_of_lt hab)).cast
        haEval.symm hbEval.symm).trans β) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs <;> rfl
  have hwind : ∀ w : ℂ,
      HasWinding (semicircleLoop x (ε • u)) w 1 → HasWinding L w 1 := by
    intro w hw
    have hn : HasWinding N w 1 := by
      have h' := HasWinding.trans_reparam_left hw φ hφc hφ0 hφ1
      simpa [N, semicircleLoop, β] using h'
    have hm : HasWinding M w 1 :=
      (hasWinding_congr_fun M N w 1
        (fun t => congrArg (fun γ : Path _ _ => γ t) hMN)).mpr hn
    exact (hasWinding_congr_fun L M w 1 hLM).mpr hm
  have hsubset :
      {w : ℂ | w ∈ F.val ∧ HasWinding (semicircleLoop x (ε • u)) w 1} ⊆
        {w : ℂ | w ∈ F.val ∧ HasWinding L w 1} := by
    intro w hw
    exact ⟨hw.1, hwind w hw.2⟩
  have hcl' := closure_mono hsubset hcl
  refine ⟨a, b, ha, has, hsb, hb, q, hqinj, hqF, ?_⟩
  exact hcl'

/-- Helper toward Definition 3.2: for a single straight segment the localized
bridge holds at every open parameter, with no vertex-surjectivity premise. -/
theorem dartBorders_toPath_leftAtOn_of_local_image_of_two_points
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (hborder : P.dartBorders d F) (hlen : (P.arc d).points.length = 2)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∀ s : {t : I // t ∈ openParams}, LeftAtOn F.val (P.arc d).toPath s := by
  intro s
  apply P.dartBorders_toPath_leftAtOn_of_local_image_of_firstSegment
    d F hborder s _ _ N hN harc hlocal
  · simpa only [Polyline.segmentParameterStart_zero] using s.property.1
  · simpa only [hlen, Polyline.segmentParameterEnd, ite_true] using s.property.2

/-- Helper toward Definition 3.2: the reverse dart gives the complete
localized right-side bridge when its geometric arc is a single segment. -/
theorem dartBorders_flip_toPath_rightAtOn_of_local_image_of_two_points
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (hborder : P.dartBorders (flip d) F) (hlen : (P.arc d).points.length = 2)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∀ s : {t : I // t ∈ openParams}, RightAtOn F.val (P.arc d).toPath s := by
  apply (P.forall_leftAtOn_flip_toPath_iff_forall_rightAtOn d F.val).mp
  have hlen' : (P.arc (flip d)).points.length = 2 := by
    simpa only [P.arc_flip d, Polyline.reverse, List.length_reverse] using hlen
  have harc' : Set.range (P.arc (flip d)).toPath ⊆ N := by
    rw [Polyline.range_toPath, P.arc_flip d, Polyline.image_reverse_transfer,
      ← Polyline.range_toPath]
    exact harc
  exact P.dartBorders_toPath_leftAtOn_of_local_image_of_two_points
    (flip d) F hborder hlen' N hN harc' hlocal

/-- Helper toward Definition 3.2: the precise local-image obstruction is
accumulation of image points not covered by any arc, including accumulation
at an endpoint of the closed arc. -/
theorem exists_local_image_iff_disjoint_closure_uncovered
    (P : PLDrawing D V flip rot vert) (d : D) :
    (∃ N : Set ℂ, IsOpen N ∧ Set.range (P.arc d).toPath ⊆ N ∧
      ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) ↔
      Disjoint (Set.range (P.arc d).toPath)
        (closure (P.image \ ⋃ e, (P.arc e).image)) := by
  constructor
  · rintro ⟨N, hN, harc, hlocal⟩
    apply Set.disjoint_left.mpr
    intro z hz hcl
    obtain ⟨w, hwN, hwbad⟩ := mem_closure_iff.mp hcl N hN (harc hz)
    exact hwbad.2 (hlocal w hwbad.1 hwN)
  · intro hdisj
    refine ⟨(closure (P.image \ ⋃ e, (P.arc e).image))ᶜ,
      isClosed_closure.isOpen_compl, ?_, ?_⟩
    · intro z hz
      exact fun hcl => Set.disjoint_left.mp hdisj hz hcl
    · intro z hz hzN
      by_contra hn
      exact hzN (subset_closure ⟨hz, hn⟩)

end PLDrawing

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: the explicitly displayed local-image
condition for the supplied upper-left and lower-right side arcs. It is an
additional geometric premise, not a claimed consequence of `IsBoundEdges32`.
The neighborhoods contain the complete closed arcs, including endpoints. -/
@[expose] def IsLocallyArcCovered32
    {V : Type uV} {E : Type uE} (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)) : Prop :=
  (∀ i : B.presentation.upperLeft.Index,
    ∃ N : Set ℂ, IsOpen N ∧
      Set.range (G.arc (B.presentation.upperLeft.darts i)).toPath ⊆ N ∧
      ∀ z, z ∈ G.image → z ∈ N → z ∈ ⋃ d, (G.arc d).image) ∧
  (∀ i : B.presentation.lowerRight.Index,
    ∃ N : Set ℂ, IsOpen N ∧
      Set.range (G.arc (B.presentation.lowerRight.darts i)).toPath ⊆ N ∧
      ∀ z, z ∈ G.image → z ∈ N → z ∈ ⋃ d, (G.arc d).image)

/-- Helper toward Definition 3.2: the named local premise is exactly the
absence of uncovered-image accumulation on every supplied present-side arc. -/
theorem isLocallyArcCovered32_iff_disjoint_closure_uncovered
    {V : Type uV} {E : Type uE} (M : DirectedPlaneMapWithMissing V E)
    (B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M)
    {rot : Equiv.Perm (E × Bool)}
    (G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)) :
    IsLocallyArcCovered32 M B G ↔
      (∀ i : B.presentation.upperLeft.Index,
        Disjoint (Set.range (G.arc (B.presentation.upperLeft.darts i)).toPath)
          (closure (G.image \ ⋃ d, (G.arc d).image))) ∧
      (∀ i : B.presentation.lowerRight.Index,
        Disjoint (Set.range (G.arc (B.presentation.lowerRight.darts i)).toPath)
          (closure (G.image \ ⋃ d, (G.arc d).image))) := by
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_congr
    (forall_congr' (fun i => G.exists_local_image_iff_disjoint_closure_uncovered
      (B.presentation.upperLeft.darts i)))
    (forall_congr' (fun i => G.exists_local_image_iff_disjoint_closure_uncovered
      (B.presentation.lowerRight.darts i)))

/-- Helper toward Definition 3.2: the right winding-side test also implies
closure incidence, without any assumption on the vertex carrier. -/
theorem rightAtOn_mem_closure32 {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (s : {t : I // t ∈ openParams}) (hside : RightAtOn F γ s) :
    γ s.1 ∈ closure F := by
  rcases hside with ⟨a, b, ha, has, hsb, hb, q, hqi, hq, hcl⟩
  exact closure_mono (show
    {w : ℂ | w ∈ F ∧ HasWinding
      ((edgeSubarc γ a b (le_of_lt (lt_trans has hsb))).trans q) w (-1)} ⊆ F
    from fun _ hw => hw.1) hcl

/-- Helper toward Definition 3.2: `ULOkInf` supplies one external map face
whose closure contains every open point of each upper-left oriented edge.
This concerns the map drawing, and does not identify it with the PL face. -/
theorem IsBoundEdges32.upperLeft_mapFace_mem_closure
    {V : Type uV} {E : Type uE} {M : DirectedPlaneMapWithMissing V E}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (h : IsBoundEdges32 M B G U S) (i : B.presentation.upperLeft.Index) :
    ∃ hp : ¬ M.toPlaneMapWithMissing.missing (B.presentation.upperLeft.darts i).1,
      ∃ F : (Drawing M).Face, (Drawing M).IsExternal F ∧
        ∀ s : {t : I // t ∈ openParams},
          orientedArc M ⟨(B.presentation.upperLeft.darts i).1, hp⟩ s.val ∈ closure F.val := by
  obtain ⟨hp, _, F, hF, hleft⟩ :=
    ((ULOkInf_iff B.presentation).mp h.presentation_facts.2.1).1 i
  exact ⟨hp, F, hF, fun s => leftAtOn_mem_closure F.val _ s (hleft s)⟩

/-- Helper toward Definition 3.2: `LROkInf` supplies one external map face
whose closure contains every open point of each lower-right oriented edge.
It supplies closure incidence rather than exclusion of nearby isolated vertices. -/
theorem IsBoundEdges32.lowerRight_mapFace_mem_closure
    {V : Type uV} {E : Type uE} {M : DirectedPlaneMapWithMissing V E}
    {B : BoundaryPresentationWithJunctions.{uV, uE, uUL, uUR, uLR, uLL} M}
    {rot : Equiv.Perm (E × Bool)}
    {G : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial M)}
    {U : G.Face} {S : E × Bool → E × Bool}
    (h : IsBoundEdges32 M B G U S) (i : B.presentation.lowerRight.Index) :
    ∃ hp : ¬ M.toPlaneMapWithMissing.missing (B.presentation.lowerRight.darts i).1,
      ∃ F : (Drawing M).Face, (Drawing M).IsExternal F ∧
        ∀ s : {t : I // t ∈ openParams},
          orientedArc M ⟨(B.presentation.lowerRight.darts i).1, hp⟩ s.val ∈ closure F.val := by
  obtain ⟨hp, _, F, hF, hright⟩ :=
    ((LROkInf_iff B.presentation).mp h.presentation_facts.2.2.2.1).1 i
  exact ⟨hp, F, hF, fun s => rightAtOn_mem_closure32 F.val _ s (hright s)⟩

















































































































































end DirectedDistances.PlanarMap

end
