/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact3










public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}

/-- Helper toward Definition 3.2: local arc coverage supplies a connected
signed sector joining small offsets of the two rays at an interior bend.
The complement is that of the original drawing, including every vertex. -/
theorem bend_contact_side_sector_of_local_image
    (P : PLDrawing D V flip rot vert) (d : D) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (N : Set ℂ) (hN : IsOpen N) (hbN : (P.arc d).point (i + 1) ∈ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image)
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
  obtain ⟨r, hr, _, hlocal⟩ :=
    P.bend_contact_local_image_of_local_image d hi N hN hbN hcover
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


/-- Helper toward Definition 3.2: the initial left face propagates across
every bend to a left half-disk at every strict segment point, using local
arc coverage of the original drawing. -/
theorem dartBorders_openSegment_left_halfDisk_of_local_image
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image)
    {i : ℕ} (hi : i + 1 < (P.arc d).points.length) (q : ℂ)
    (hq : q ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball q r,
      0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) * (y - q)).im →
        y ∈ F.val := by
  have hmemN (x : ℂ) (hx : x ∈ (P.arc d).image) : x ∈ N := by
    apply harc
    rw [Polyline.range_toPath]
    exact hx
  have hcontact (j : ℕ) (hj : j + 1 < (P.arc d).points.length) (x : ℂ)
      (hx : x ∈ openSegment ℝ ((P.arc d).point j) ((P.arc d).point (j + 1))) :
      ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x r, y ∈ P.image →
        y ∈ (P.arc d).segmentAt j := by
    obtain ⟨r, hr, _, hc⟩ := P.openSegment_contact_local_image_of_local_image
      d hj hx N hN (hmemN x ((P.arc d).segmentAt_subset_image hj
        (openSegment_subset_segment ℝ _ _ hx))) hcover
    exact ⟨r, hr, hc⟩
  let s : ℝ := 1
  have hs : s ≠ 0 := one_ne_zero
  let H := fun j : ℕ => ∀ x : ℂ,
    x ∈ openSegment ℝ ((P.arc d).point j) ((P.arc d).point (j + 1)) →
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x r,
      0 < s * (star ((P.arc d).point (j + 1) - (P.arc d).point j) * (y - x)).im →
        y ∈ F.val
  have htransport (j : ℕ) (hj : j + 1 < (P.arc d).points.length) (x₁ x₂ : ℂ)
      (hx₁ : x₁ ∈ openSegment ℝ ((P.arc d).point j) ((P.arc d).point (j + 1)))
      (hx₂ : x₂ ∈ openSegment ℝ ((P.arc d).point j) ((P.arc d).point (j + 1)))
      (hbase : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x₁ r,
        0 < s * (star ((P.arc d).point (j + 1) - (P.arc d).point j) * (y - x₁)).im →
          y ∈ F.val) :
      ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x₂ r,
        0 < s * (star ((P.arc d).point (j + 1) - (P.arc d).point j) * (y - x₂)).im →
          y ∈ F.val := by
    let a := (P.arc d).point j
    let b := (P.arc d).point (j + 1)
    let u := b - a
    let v := s • (Complex.I * u)
    have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 j hj).symm
    obtain ⟨r₀, hr₀, hhalf⟩ := hbase
    obtain ⟨δ₀, hδ₀, hstrip⟩ := P.openSegment_normal_strip_compl_of_local_image d hj x₁ x₂ hx₁ hx₂ N hN harc hcover
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
    have hbase' (t : ℝ) (ht : 0 < t) (htd : t < δ) : x₁ + t • v ∈ F.val := by
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
    have hSK : S ⊆ F.val := by
      obtain ⟨x₀, _, hK⟩ := F.property
      rw [hK] at hwK ⊢
      rw [connectedComponentIn_eq hwK]
      exact hpre.subset_connectedComponentIn hwS hsafe
    obtain ⟨r, hr, hlocal⟩ := hcontact j hj x₂ hx₂
    let t := min (δ / 2) (r / (2 * (‖v‖ + 1)))
    have ht : 0 < t := lt_min (half_pos hδ) (div_pos hr (by positivity))
    have htd : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hw₂ : x₂ + t • v ∈ F.val :=
      hSK ⟨(x₂, t), ⟨right_mem_segment ℝ x₁ x₂, ht, htd⟩, rfl⟩
    have hwr : x₂ + t • v ∈ ball x₂ r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have hprod : t * (2 * (‖v‖ + 1)) ≤ r :=
        (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
      nlinarith only [hprod, ht, norm_nonneg v]
    exact ⟨r, hr, P.face_halfDisk_of_local_image F a b x₂ (x₂ + t • v) r s
      (openSegment_subset_segment ℝ a b hx₂) hw₂ hwr
      (hside x₂ (openSegment_subset_segment ℝ a b hx₂) t ht) hlocal⟩
  have hstep (j : ℕ) (hj : j + 2 < (P.arc d).points.length) (hprev : H j) : H (j + 1) := by
    let a := (P.arc d).point j
    let b := (P.arc d).point (j + 1)
    let c := (P.arc d).point (j + 2)
    let u := b - a
    let v := c - b
    have hlen : j + 2 < (P.arc d).points.length := by omega
    have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 j (by omega)).symm
    have hv : v ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 (j + 1) (by omega)).symm
    obtain ⟨S, hSpre, hSsafe, δ, hδ, hcorners⟩ := P.bend_contact_side_sector_of_local_image d hlen N hN
      (hmemN b ((P.arc d).segmentAt_subset_image (by omega)
        (right_mem_segment ℝ a b))) hcover s hs
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
    obtain ⟨r₁, hr₁, hhalf₁⟩ := hprev x₁ hx₁
    obtain ⟨r₂, hr₂, hlocal⟩ := hcontact (j + 1) (by omega) x₂ hx₂
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
    have hy₁F : y₁ ∈ F.val := hhalf₁ y₁ hyr₁ hside₁
    have hc := hcorners t ε ht htd he hed
    have hSK : S ⊆ F.val := by
      obtain ⟨x₀, _, hK⟩ := F.property
      rw [hK] at hy₁F ⊢
      rw [connectedComponentIn_eq hy₁F]
      exact hSpre.subset_connectedComponentIn hc.1 hSsafe
    have hbase : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x₂ r,
        0 < s * (star v * (y - x₂)).im → y ∈ F.val :=
      ⟨r₂, hr₂, P.face_halfDisk_of_local_image F b c x₂ y₂ r₂ s
        (openSegment_subset_segment ℝ b c hx₂) (hSK hc.2) hyr₂ hside₂ hlocal⟩
    intro x hx
    exact htransport (j + 1) (by omega) x₂ x hx₂ hx hbase
  have hzero : H 0 := by
    intro x hx
    simpa only [s, one_mul] using
      P.dartBorders_firstSegment_left_halfDisk_of_local_image d F hborder x hx N hN harc hcover
  have hall : ∀ j : ℕ, j + 1 < (P.arc d).points.length → H j := by
    intro j
    induction j with
    | zero => exact fun _ => hzero
    | succ j ih =>
      intro hj
      exact hstep j (by omega) (ih (by omega))
  simpa only [s, one_mul] using hall i hi q hq


/-- Helper toward Definition 3.2: local coverage provides small semicircular
return paths through the bordering face along any strict segment. -/
theorem dartBorders_openSegment_leftSemicircle_of_local_image
    (P : PLDrawing D V flip rot vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    {i : ℕ} (hi : i + 1 < (P.arc d).points.length) (x : ℂ)
    (hx : x ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      (x - ε • ((P.arc d).point (i + 1) - (P.arc d).point i) ∈
        openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) ∧
      (x + ε • ((P.arc d).point (i + 1) - (P.arc d).point i) ∈
        openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) ∧
      Function.Injective
        (leftSemicircle x (ε • ((P.arc d).point (i + 1) - (P.arc d).point i))) ∧
      ∀ t : I, t ∈ openParams →
        leftSemicircle x (ε • ((P.arc d).point (i + 1) - (P.arc d).point i)) t ∈
          F.val := by
  let u := (P.arc d).point (i + 1) - (P.arc d).point i
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  obtain ⟨r, hr, hhalf⟩ :=
    P.dartBorders_openSegment_left_halfDisk_of_local_image d F hborder N hN harc hlocal hi x hx
  obtain ⟨δseg, hδseg, hend⟩ := openSegment_small_symmetric_endpoints
    ((P.arc d).point i) ((P.arc d).point (i + 1)) x hx
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
theorem dartBorders_openSegment_semicircleLoop_of_local_image
    (P : PLDrawing D V flip rot vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    {i : ℕ} (hi : i + 1 < (P.arc d).points.length) (x : ℂ)
    (hx : x ∈ openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1)))
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∃ ε : ℝ, 0 < ε ∧
      (x - ε • ((P.arc d).point (i + 1) - (P.arc d).point i) ∈
        openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) ∧
      (x + ε • ((P.arc d).point (i + 1) - (P.arc d).point i) ∈
        openSegment ℝ ((P.arc d).point i) ((P.arc d).point (i + 1))) ∧
      Function.Injective
        (leftSemicircle x (ε • ((P.arc d).point (i + 1) - (P.arc d).point i))) ∧
      (∀ t : I, t ∈ openParams →
        leftSemicircle x (ε • ((P.arc d).point (i + 1) - (P.arc d).point i)) t ∈
          F.val) ∧
      x ∈ closure {w : ℂ | w ∈ F.val ∧
        HasWinding
          (semicircleLoop x (ε • ((P.arc d).point (i + 1) - (P.arc d).point i)))
          w 1} := by
  let u := (P.arc d).point (i + 1) - (P.arc d).point i
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  obtain ⟨δ, hδ, hreturn⟩ :=
    P.dartBorders_openSegment_leftSemicircle_of_local_image d F hborder hi x hx N hN harc hlocal
  obtain ⟨r, hr, hhalf⟩ :=
    P.dartBorders_openSegment_left_halfDisk_of_local_image d F hborder N hN harc hlocal hi x hx
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
parameters strictly inside any segment. Bend parameters are treated separately. -/
theorem dartBorders_toPath_leftAtOn_of_local_image_of_strictSegment
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert)
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    {i : ℕ} (hi : i + 1 < (P.arc d).points.length)
    (s : {t : I // t ∈ openParams})
    (hstart : Polyline.segmentParameterStart i < (s.1 : ℝ))
    (hend : (s.1 : ℝ) < Polyline.segmentParameterEnd (P.arc d).points.length i)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    LeftAtOn F.val (P.arc d).toPath s := by
  let p := P.arc d
  let u := p.point (i + 1) - p.point i
  let x := p.toPath s.1
  have hx := Polyline.toPath_mem_openSegment_of_parameter p hi s.1 hstart hend
  obtain ⟨r, hr0, hr1, hxcoord⟩ :=
    openSegment_affine_coordinate (p.point i) (p.point (i + 1)) x hx
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i hi).symm
  have hform := Polyline.toPath_segment_affine_apply p hi
  dsimp only at hform
  have hform' := hform s.1 (le_of_lt hstart) (le_of_lt hend)
  let θ : ℝ := ((s.1 : ℝ) - Polyline.segmentParameterStart i) /
    (Polyline.segmentParameterEnd p.points.length i -
      Polyline.segmentParameterStart i)
  have hpath : p.toPath s.1 = p.point i + (θ : ℂ) * u := by
    simpa only [u, θ] using hform'
  have hratio : θ = r := by
    apply affine_coordinate_unique hu
    calc
      p.point i + (θ : ℂ) * u = p.toPath s.1 := hpath.symm
      _ = x := rfl
      _ = p.point i + (r : ℂ) * u := hxcoord
  have hratio' :
      (((s.1 : ℝ) - Polyline.segmentParameterStart i) /
        (Polyline.segmentParameterEnd p.points.length i -
          Polyline.segmentParameterStart i)) = r := hratio
  obtain ⟨ε, hε, hleft, hright, hinj, hopen, hcl⟩ :=
    P.dartBorders_openSegment_semicircleLoop_of_local_image d F hborder hi x hx N hN harc hlocal
  obtain ⟨rl, hrl0, hrl1, hleftcoord⟩ :=
    openSegment_affine_coordinate (p.point i) (p.point (i + 1))
      (x - ε • u) hleft
  obtain ⟨rr, hrr0, hrr1, hrightcoord⟩ :=
    openSegment_affine_coordinate (p.point i) (p.point (i + 1))
      (x + ε • u) hright
  have hleftformula : x - ε • u =
      p.point i + ((r - ε : ℝ) : ℂ) * u := by
    rw [hxcoord, Complex.real_smul]
    push_cast
    ring
  have hrightformula : x + ε • u =
      p.point i + ((r + ε : ℝ) : ℂ) * u := by
    rw [hxcoord, Complex.real_smul]
    push_cast
    ring
  have hrl : rl = r - ε :=
    affine_coordinate_unique hu (hleftcoord.symm.trans hleftformula)
  have hrr : rr = r + ε :=
    affine_coordinate_unique hu (hrightcoord.symm.trans hrightformula)
  let a := parameterAtSegmentFraction p i (r - ε) (by linarith) (by linarith)
  let b := parameterAtSegmentFraction p i (r + ε) (by linarith) (by linarith)
  have haEval : p.toPath a = x - ε • u := by
    have h := toPath_parameterAtSegmentFraction p hi (r - ε) (by linarith) (by linarith)
    change p.toPath (parameterAtSegmentFraction p i (r - ε) _ _) = _
    rw [h, hleftformula]
  have hbEval : p.toPath b = x + ε • u := by
    have h := toPath_parameterAtSegmentFraction p hi (r + ε) (by linarith) (by linarith)
    change p.toPath (parameterAtSegmentFraction p i (r + ε) _ _) = _
    rw [h, hrightformula]
  have hlen : 0 < Polyline.segmentParameterEnd p.points.length i -
      Polyline.segmentParameterStart i :=
    sub_pos.mpr (Polyline.segmentParameterStart_lt_end p.points.length i)
  have hsval : (s.1 : ℝ) = Polyline.segmentParameterStart i + r *
      (Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i) := by
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
    change 0 < Polyline.segmentParameterStart i + (r - ε) *
      (Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i)
    exact lt_of_le_of_lt (Polyline.segmentParameterStart_mem_Icc i).1
      (by nlinarith [mul_pos hfracA hlen])
  have hb : (b : ℝ) < 1 := by
    have hbend : (b : ℝ) < Polyline.segmentParameterEnd p.points.length i := by
      change Polyline.segmentParameterStart i + (r + ε) *
        (Polyline.segmentParameterEnd p.points.length i -
          Polyline.segmentParameterStart i) < _
      exact (by nlinarith [mul_pos (sub_pos.mpr hfracB) hlen])
    exact lt_of_lt_of_le hbend (Polyline.segmentParameterEnd_mem_Icc
      p.points.length i).2
  have hstartA : Polyline.segmentParameterStart i ≤ (a : ℝ) := by
    change Polyline.segmentParameterStart i ≤ Polyline.segmentParameterStart i +
      (r - ε) * (Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i)
    exact le_add_of_nonneg_right (mul_nonneg (le_of_lt hfracA) hlen.le)
  have hBend : (b : ℝ) ≤ Polyline.segmentParameterEnd p.points.length i := by
    change Polyline.segmentParameterStart i + (r + ε) *
      (Polyline.segmentParameterEnd p.points.length i -
        Polyline.segmentParameterStart i) ≤ _
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
        (Polyline.segmentParameterEnd p.points.length i -
          Polyline.segmentParameterStart i) := by
      dsimp [a, b, parameterAtSegmentFraction]
      ring
    have hratio_t :
        ((t : ℝ) - Polyline.segmentParameterStart i) /
            (Polyline.segmentParameterEnd p.points.length i -
              Polyline.segmentParameterStart i) =
          (r - ε) + (((t : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))) * (2 * ε) := by
      rw [hdenab]
      dsimp [a, b, parameterAtSegmentFraction]
      field_simp [ne_of_gt hlen, hε.ne']
      ring
    have hratioC :
        (((((t : ℝ) - Polyline.segmentParameterStart i) /
          (Polyline.segmentParameterEnd p.points.length i -
            Polyline.segmentParameterStart i)) : ℝ) : ℂ) =
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


/-- Helper toward Definition 3.2: the left local sector at an internal
bend belongs to the face bordering the dart. -/
theorem dartBorders_bend_left_sector_subset_face_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ S : Set ℂ, IsPreconnected S ∧ S ⊆ F.val ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ,
        0 < t → t < δ → 0 < ε → ε < δ →
        b + t • (-u + ε • (Complex.I * u)) ∈ S ∧
        b + t • (v + ε • (Complex.I * v)) ∈ S := by
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨S, hSpre, hSsafe, δ, hδ, hcorners⟩ :=
    P.bend_contact_side_sector_of_local_image d hi N hN
      (by apply harc; rw [Polyline.range_toPath]
          exact (P.arc d).segmentAt_subset_image (by omega) (right_mem_segment ℝ _ _))
      hcover 1 one_ne_zero
  let t := min (δ / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (half_pos hδ) (by norm_num)
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let a := (P.arc d).point i
  let x := b - t • u
  have hx : x ∈ openSegment ℝ a b := by
    rw [openSegment_eq_image']
    refine ⟨1 - t, ⟨by linarith, by linarith⟩, ?_⟩
    dsimp [x, u, b, a]
    push_cast
    ring
  obtain ⟨r, hr, hhalf⟩ :=
    P.dartBorders_openSegment_left_halfDisk_of_local_image d F hborder N hN harc hcover (by omega) x hx
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i (by omega)).symm
  let ε := min (δ / 2) (r / (2 * (t * ‖u‖ + 1)))
  have hε : 0 < ε := lt_min (half_pos hδ) (div_pos hr (by positivity))
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  let y := b + t • (-u + ε • (Complex.I * u))
  have hyx : y - x = (t * ε) • (Complex.I * u) := by
    dsimp [y, x]
    push_cast
    ring
  have hyr : y ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm, hyx, norm_smul, Real.norm_eq_abs,
      abs_of_pos (mul_pos ht hε)]
    have hprod : ε * (2 * (t * ‖u‖ + 1)) ≤ r :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hnorm : ‖Complex.I * u‖ = ‖u‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [hnorm]
    nlinarith [norm_nonneg u]
  have hyside : 0 < (star u * (y - x)).im := by
    rw [hyx, mul_smul_comm, Complex.smul_im]
    have hn : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
    have hnormal : (star u * (Complex.I * u)).im = Complex.normSq u := by
      rw [show star u * (Complex.I * u) = Complex.I * (star u * u) by ring,
        Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      simp
    rw [hnormal]
    positivity
  have hyF : y ∈ F.val := hhalf y hyr hyside
  have hyS : y ∈ S := by
    simpa only [one_smul, y, u, b] using (hcorners t ε ht htδ hε hεδ).1
  have hSface : S ⊆ F.val := by
    obtain ⟨z, _, hF⟩ := F.property
    rw [hF] at hyF ⊢
    rw [connectedComponentIn_eq hyF]
    exact hSpre.subset_connectedComponentIn hyS hSsafe
  refine ⟨S, hSpre, hSface, δ, hδ, ?_⟩
  intro t' ε' ht' ht'δ hε' hε'δ
  simpa only [one_smul] using hcorners t' ε' ht' ht'δ hε' hε'δ

/-- Helper toward Definition 3.2: uniformly small left offsets on both
segments incident to a bend belong to the face bordering the dart. -/
theorem dartBorders_bend_left_offsets_mem_face_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ,
      0 < t → t < δ → 0 < ε → ε < δ →
      b + t • (-u + ε • (Complex.I * u)) ∈ F.val ∧
      b + t • (v + ε • (Complex.I * v)) ∈ F.val := by
  obtain ⟨S, hSpre, hSface, δ, hδ, hcorners⟩ :=
    P.dartBorders_bend_left_sector_subset_face_of_local_image d F hborder N hN harc hcover hi
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htδ hε hεδ
  exact ⟨hSface (hcorners t ε ht htδ hε hεδ).1,
    hSface (hcorners t ε ht htδ hε hεδ).2⟩


/-- Helper toward Definition 3.2: at a strict left turn, the small
intersection of the two left half-disks belongs to the bordering face. -/
theorem dartBorders_bend_left_wedge_subset_face_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : 0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ r : ℝ, 0 < r ∧ ∀ y : ℂ, y ∈ Metric.ball b r →
      0 < (star u * (y - b)).im → 0 < (star v * (y - b)).im → y ∈ F.val := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨r, hr, _, hlocal⟩ := P.bend_contact_local_image_of_local_image d hi N hN
    (by apply harc; rw [Polyline.range_toPath]
        exact (P.arc d).segmentAt_subset_image (by omega) (right_mem_segment ℝ _ _)) hcover
  let W := {y : ℂ | y ∈ Metric.ball b r ∧ 0 < (star u * (y - b)).im} ∩
    {y : ℂ | y ∈ Metric.ball b r ∧ 0 < (star v * (y - b)).im}
  have hWc : Convex ℝ W := by
    simpa only [one_mul] using
      (signed_halfDisk_convex b u r 1).inter (signed_halfDisk_convex b v r 1)
  have hWsafe : W ⊆ P.imageᶜ := by
    intro y hy hyP
    rcases (hlocal y hy.1.1).mp hyP with hleft | hright
    · have hz := segment_contact_side_eq_zero ((P.arc d).point i) b b y
        (right_mem_segment ℝ _ _) hleft
      exact (ne_of_gt hy.1.2) hz
    · have hz := segment_contact_side_eq_zero b ((P.arc d).point (i + 2)) b y
        (left_mem_segment ℝ _ _) hright
      exact (ne_of_gt hy.2.2) hz
  obtain ⟨δ, hδ, hface⟩ := P.dartBorders_bend_left_offsets_mem_face_of_local_image d F hborder N hN harc hcover hi
  have hc : Continuous (fun ε : ℝ => (star u * v).im + ε * (star u * v).re) := by
    fun_prop
  have hn : (fun ε : ℝ => (star u * v).im + ε * (star u * v).re) ⁻¹'
      Set.Ioi 0 ∈ 𝓝 0 := hc.continuousAt.preimage_mem_nhds
        (isOpen_Ioi.mem_nhds (by
          simpa only [Set.mem_Ioi, zero_mul, add_zero, u, v, b] using hturn))
  obtain ⟨e, he, hepos⟩ := Metric.mem_nhds_iff.mp hn
  let ε := min (δ / 2) (e / 2)
  have hε : 0 < ε := lt_min (half_pos hδ) (half_pos he)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hεe : ε < e := (min_le_right _ _).trans_lt (half_lt_self he)
  have hother : 0 < (star u * v).im + ε * (star u * v).re := by
    apply hepos
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε] using hεe
  let f : ℝ → ℂ := fun t => b + t • (-u + ε • (Complex.I * u))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfn : f ⁻¹' Metric.ball b r ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds
      (by simpa only [f, zero_smul, add_zero] using Metric.mem_ball_self hr))
  obtain ⟨e', he', hball⟩ := Metric.mem_nhds_iff.mp hfn
  let t := min (δ / 2) (e' / 2)
  have ht : 0 < t := lt_min (half_pos hδ) (half_pos he')
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hte : t < e' := (min_le_right _ _).trans_lt (half_lt_self he')
  have hfr : f t ∈ Metric.ball b r := by
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using hte
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i (by omega)).symm
  have hfu : 0 < (star u * (f t - b)).im := by
    have h := (bend_offset_sides u v 1 t ε).1
    simp only [one_smul, one_mul, one_pow, mul_one] at h
    dsimp only [f]
    rw [add_sub_cancel_left, h]
    exact mul_pos (mul_pos ht hε) (Complex.normSq_pos.mpr hu)
  have hfv : 0 < (star v * (f t - b)).im := by
    have h := (bend_offset_sides u v 1 t ε).2.2.1
    simp only [one_smul, one_mul, one_pow, mul_one] at h
    dsimp only [f]
    rw [add_sub_cancel_left, h]
    exact mul_pos ht hother
  have hfW : f t ∈ W := ⟨⟨hfr, hfu⟩, ⟨hfr, hfv⟩⟩
  have hfF : f t ∈ F.val := (hface t ε ht htδ hε hεδ).1
  have hWF : W ⊆ F.val := by
    obtain ⟨z, _, hF⟩ := F.property
    rw [hF] at hfF ⊢
    rw [connectedComponentIn_eq hfF]
    exact hWc.isPreconnected.subset_connectedComponentIn hfW hWsafe
  exact ⟨r, hr, fun y hyr hyu hyv => hWF ⟨⟨hyr, hyu⟩, ⟨hyr, hyv⟩⟩⟩

/-- Helper toward Definition 3.2: winding-one points of the bordering
face accumulate at a strict left bend for every positive triangle scale. -/
theorem dartBorders_bend_triangle_mem_closure_winding_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : 0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im)
    (r : ℝ) (hr : 0 < r) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    b ∈ closure {w : ℂ | w ∈ F.val ∧
      HasWinding (((Path.segment (b - r • u) b).trans
        (Path.segment b (b + r • v))).trans
        (Path.segment (b + r • v) (b - r • u))) w 1} := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨R, hR, hface⟩ :=
    P.dartBorders_bend_left_wedge_subset_face_of_local_image d F hborder N hN harc hcover hi hturn
  rw [Metric.mem_closure_iff]
  intro η hη
  let τ := min (r / 4) (min (R / (2 * (‖-u + v‖ + 1)))
    (η / (2 * (‖-u + v‖ + 1))))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτr : 2 * τ < r := by
    have h := min_le_left (r / 4) (min (R / (2 * (‖-u + v‖ + 1)))
      (η / (2 * (‖-u + v‖ + 1))))
    change τ ≤ r / 4 at h
    linarith only [h, hr]
  have hτR : τ * (2 * (‖-u + v‖ + 1)) ≤ R := by
    apply (le_div_iff₀ (by positivity)).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hτη : τ * (2 * (‖-u + v‖ + 1)) ≤ η := by
    apply (le_div_iff₀ (by positivity)).mp
    exact (min_le_right _ _).trans (min_le_right _ _)
  let w := b + τ • (-u + v)
  have hdist : dist w b = τ * ‖-u + v‖ := by
    dsimp only [w]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
  have hwR : w ∈ Metric.ball b R := by
    rw [Metric.mem_ball, hdist]
    nlinarith only [hτR, hτ, norm_nonneg (-u + v)]
  have hwu : (star u * (w - b)).im = τ * (star u * v).im := by
    dsimp only [w]
    simp only [add_sub_cancel_left, Complex.star_def, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]
    ring
  have hwv : (star v * (w - b)).im = τ * (star u * v).im := by
    dsimp only [w]
    simp only [add_sub_cancel_left, Complex.star_def, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]
    ring
  have hc : 0 < (star u * v).im := hturn
  have hwF : w ∈ F.val := hface w hwR
    (hwu.symm ▸ mul_pos hτ hc) (hwv.symm ▸ mul_pos hτ hc)
  obtain ⟨hab, hbc, hca⟩ := bend_triangle_cross b u v r τ
  have hwinding : HasWinding (((Path.segment (b - r • u) b).trans
      (Path.segment b (b + r • v))).trans
      (Path.segment (b + r • v) (b - r • u))) w 1 := by
    apply hasWinding_triangle_of_cross_pos
    · rw [show w = b + τ • (-u + v) from rfl, hab]
      exact mul_pos (mul_pos hr hτ) hc
    · rw [show w = b + τ • (-u + v) from rfl, hbc]
      exact mul_pos (mul_pos hr hτ) hc
    · rw [show w = b + τ • (-u + v) from rfl, hca]
      exact mul_pos (mul_pos hr (sub_pos.mpr hτr)) hc
  refine ⟨w, ⟨hwF, hwinding⟩, ?_⟩
  rw [dist_comm, hdist]
  nlinarith only [hτη, hτ, norm_nonneg (-u + v)]

/-- Helper toward Definition 3.2: a strict left bend admits a small
injective straight return chord in its bordering face, with winding-one
face points accumulating at the bend for the resulting triangle. -/
theorem dartBorders_bend_exists_triangle_return_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : 0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      Function.Injective (Path.segment (b + r • v) (b - r • u)) ∧
      (∀ t : I, t ∈ openParams →
        Path.segment (b + r • v) (b - r • u) t ∈ F.val) ∧
      b ∈ closure {w : ℂ | w ∈ F.val ∧
        HasWinding (((Path.segment (b - r • u) b).trans
          (Path.segment b (b + r • v))).trans
          (Path.segment (b + r • v) (b - r • u))) w 1} := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨R, hR, hface⟩ :=
    P.dartBorders_bend_left_wedge_subset_face_of_local_image d F hborder N hN harc hcover hi hturn
  let r := min (1 / 2 : ℝ) (R / (2 * (‖u‖ + ‖v‖ + 1)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hprod : r * (2 * (‖u‖ + ‖v‖ + 1)) ≤ R :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have haR : b - r • u ∈ Metric.ball b R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith only [hprod, hr, norm_nonneg u, norm_nonneg v]
  have hcR : b + r • v ∈ Metric.ball b R := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith only [hprod, hr, norm_nonneg u, norm_nonneg v]
  have hc : 0 < (star u * v).im := hturn
  have hcrossu (t : I) :
      (star u * (Path.segment (b + r • v) (b - r • u) t - b)).im =
        r * (1 - (t : ℝ)) * (star u * v).im := by
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hcrossv (t : I) :
      (star v * (Path.segment (b + r • v) (b - r • u) t - b)).im =
        r * (t : ℝ) * (star u * v).im := by
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hinj : Function.Injective (Path.segment (b + r • v) (b - r • u)) := by
    intro s t heq
    have he := congrArg (fun z : ℂ => (star u * (z - b)).im) heq
    rw [hcrossu, hcrossu] at he
    have he' : (r * (star u * v).im) * (s : ℝ) =
        (r * (star u * v).im) * (t : ℝ) := by nlinarith only [he]
    exact Subtype.ext (mul_left_cancel₀ (ne_of_gt (mul_pos hr hc)) he')
  refine ⟨r, hr, hr1, hinj, ?_,
    P.dartBorders_bend_triangle_mem_closure_winding_of_local_image d F hborder N hN harc hcover hi hturn r hr⟩
  intro t ht
  have ht0 : 0 < (t : ℝ) := ht.1
  have ht1 : (t : ℝ) < 1 := ht.2
  have htR : Path.segment (b + r • v) (b - r • u) t ∈ Metric.ball b R :=
    (convex_ball b R).segment_subset hcR haR (by
      rw [Path.segment_apply]
      exact lineMap_mem_segment ℝ _ _ t.2)
  apply hface _ htR
  · rw [hcrossu]
    exact mul_pos (mul_pos hr (sub_pos.mpr ht1)) hc
  · rw [hcrossv]
    exact mul_pos (mul_pos hr ht0) hc

/-- Helper toward Definition 3.2: a bordering face satisfies the winding
left-side test at a bend with strictly positive turn cross product. -/
theorem dartBorders_toPath_leftAtOn_of_bend_left_turn_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image)
    (s : {t : I // t ∈ openParams}) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hbend : (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1))
    (hturn : 0 < (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im) :
    LeftAtOn F.val (P.arc d).toPath s := by
  let p := P.arc d
  change i + 2 < p.points.length at hi
  let B := p.point (i + 1)
  let u := B - p.point i
  let v := p.point (i + 2) - B
  obtain ⟨r, hr, hr1, hinj, hqface, hcl⟩ :=
    P.dartBorders_bend_exists_triangle_return_of_local_image d F hborder N hN harc hcover hi hturn
  let L := Polyline.segmentParameterStart i
  let M := Polyline.segmentParameterStart (i + 1)
  let H := Polyline.segmentParameterEnd p.points.length (i + 1)
  have hend : Polyline.segmentParameterEnd p.points.length i = M :=
    Polyline.segmentParameterEnd_eq_start_succ (by omega)
  have hLM : L < M := by
    rw [← hend]
    exact Polyline.segmentParameterStart_lt_end p.points.length i
  have hMH : M < H := Polyline.segmentParameterStart_lt_end p.points.length (i + 1)
  have hL0 : 0 ≤ L := (Polyline.segmentParameterStart_mem_Icc i).1
  have hH1 : H ≤ 1 := (Polyline.segmentParameterEnd_mem_Icc p.points.length (i + 1)).2
  let av := M - r * (M - L)
  let bv := M + r * (H - M)
  have hLa : L < av := by
    dsimp only [av]
    nlinarith only [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hLM)]
  have haM : av < M := by
    dsimp only [av]
    linarith only [mul_pos hr (sub_pos.mpr hLM)]
  have hMb : M < bv := by
    dsimp only [bv]
    linarith only [mul_pos hr (sub_pos.mpr hMH)]
  have hbH : bv < H := by
    dsimp only [bv]
    nlinarith only [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hMH)]
  let a : I := ⟨av, ⟨hL0.trans hLa.le, haM.le.trans (hMH.le.trans hH1)⟩⟩
  let b : I := ⟨bv, ⟨(hL0.trans hLM.le).trans hMb.le, hbH.le.trans hH1⟩⟩
  have ha : (0 : I) < a := hL0.trans_lt hLa
  have hb : b < (1 : I) := hbH.trans_le hH1
  have has : a < s.1 := by change av < (s.1 : ℝ); rw [hbend]; exact haM
  have hsb : s.1 < b := by change (s.1 : ℝ) < bv; rw [hbend]; exact hMb
  have hsEval : p.toPath s.1 = B := P.toPath_eq_vertex_at_bend d s hi hbend
  have haEval : p.toPath a = B - r • u := by
    have hf := Polyline.toPath_segment_affine_apply p (i := i) (by omega)
      a hLa.le (by rw [hend]; exact haM.le)
    rw [hend] at hf
    have hratio : ((a : ℝ) - L) / (M - L) = 1 - r := by
      change (M - r * (M - L) - L) / (M - L) = 1 - r
      field_simp
      ring
    change p.toPath a = p.point i + (((((a : ℝ) - L) / (M - L)) : ℝ) : ℂ) * u at hf
    rw [hratio] at hf
    rw [hf]
    dsimp only [u, B]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hbEval : p.toPath b = B + r • v := by
    have hf := Polyline.toPath_segment_affine_apply p (i := i + 1) (by omega)
      b hMb.le hbH.le
    have hratio : ((b : ℝ) - M) / (H - M) = r := by
      change (M + r * (H - M) - M) / (H - M) = r
      field_simp
      ring
    change p.toPath b = B + (((((b : ℝ) - M) / (H - M)) : ℝ) : ℂ) * v at hf
    rw [hratio] at hf
    exact hf
  have hleft := Polyline.toPath_affine_on_segment_subinterval p (i := i) (by omega)
    a s.1 has hLa.le (by rw [hend]; exact hbend.le)
  have hright := Polyline.toPath_affine_on_segment_subinterval p (i := i + 1) (by omega)
    s.1 b hsb hbend.ge hbH.le
  obtain ⟨f, hc, h0, h1, hedge⟩ := edgeSubarc_two_segments_reparam p.toPath a s.1 b
    has hsb hleft hright
  let q := Path.segment (p.toPath b) (p.toPath a)
  have hqinj : Function.Injective q := by
    dsimp only [q]
    rw [haEval, hbEval]
    exact hinj
  have hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val := by
    dsimp only [q]
    rw [haEval, hbEval]
    exact hqface
  have hwind (w : ℂ) (hw : HasWinding (((Path.segment (B - r • u) B).trans
      (Path.segment B (B + r • v))).trans (Path.segment (B + r • v) (B - r • u))) w 1) :
      HasWinding ((edgeSubarc p.toPath a b (has.trans hsb).le).trans q) w 1 := by
    have hw' : HasWinding (((Path.segment (p.toPath a) (p.toPath s.1)).trans
        (Path.segment (p.toPath s.1) (p.toPath b))).trans q) w 1 := by
      dsimp only [q]
      rw [haEval, hbEval, hsEval]
      exact hw
    have ht := hw'.trans_reparam_left f hc h0 h1
    rw [← hedge] at ht
    exact ht
  refine ⟨a, b, ha, has, hsb, hb, q, hqinj, hqF, ?_⟩
  rw [hsEval]
  have hsubset : {w : ℂ | w ∈ F.val ∧
      HasWinding (((Path.segment (B - r • u) B).trans (Path.segment B (B + r • v))).trans
        (Path.segment (B + r • v) (B - r • u))) w 1} ⊆
      {w : ℂ | w ∈ F.val ∧
        HasWinding ((edgeSubarc p.toPath a b (has.trans hsb).le).trans q) w 1} :=
    fun w hw => ⟨hw.1, hwind w hw.2⟩
  exact closure_mono hsubset hcl

/-- Helper toward Definition 3.2: at a strict reflex left bend, the
union of the two small left half-disks belongs to the bordering face. -/
theorem dartBorders_bend_reflex_wedge_subset_face_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im < 0) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ r : ℝ, 0 < r ∧ ∀ y : ℂ, y ∈ Metric.ball b r →
      (0 < (star u * (y - b)).im ∨ 0 < (star v * (y - b)).im) → y ∈ F.val := by
  dsimp only
  let a := (P.arc d).point i
  let b := (P.arc d).point (i + 1)
  let c := (P.arc d).point (i + 2)
  let u := b - a
  let v := c - b
  obtain ⟨r, hr, _, hlocal⟩ := P.bend_contact_local_image_of_local_image d hi N hN
    (by apply harc; rw [Polyline.range_toPath]
        exact (P.arc d).segmentAt_subset_image (by omega) (right_mem_segment ℝ _ _)) hcover
  let A := {y : ℂ | y ∈ Metric.ball b r ∧ 0 < (star u * (y - b)).im}
  let B := {y : ℂ | y ∈ Metric.ball b r ∧ 0 < (star v * (y - b)).im}
  have hAc : Convex ℝ A := by simpa only [one_mul] using signed_halfDisk_convex b u r 1
  have hBc : Convex ℝ B := by simpa only [one_mul] using signed_halfDisk_convex b v r 1
  have hc : (star u * v).im < 0 := hturn
  have hsafe : A ∪ B ⊆ P.imageᶜ := by
    intro y hy hyP
    have hyr : y ∈ Metric.ball b r := hy.elim And.left And.left
    rcases (hlocal y hyr).mp hyP with hleft | hright
    · have hzu := segment_contact_side_eq_zero a b b y (right_mem_segment ℝ a b) hleft
      have hzv : (star v * (y - b)).im ≤ 0 := by
        change y ∈ segment ℝ a b at hleft
        rw [segment_eq_image'] at hleft
        obtain ⟨t, ht, rfl⟩ := hleft
        have heq : a + t • (b - a) - b = (1 - t) • (-u) := by
          change a + t • (b - a) - b = (1 - t) • (-(b - a))
          module
        rw [heq]
        have h := (bend_offset_sides u v 1 (1 - t) 0).2.2.1
        simp only [one_smul, one_mul, one_pow, mul_one, zero_smul, add_zero, zero_mul] at h
        rw [h]
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hc.le
      exact hy.elim (fun hy => (ne_of_gt hy.2) hzu) (fun hy => (not_lt_of_ge hzv) hy.2)
    · have hzv := segment_contact_side_eq_zero b c b y (left_mem_segment ℝ b c) hright
      have hzu : (star u * (y - b)).im ≤ 0 := by
        change y ∈ segment ℝ b c at hright
        rw [segment_eq_image'] at hright
        obtain ⟨t, ht, rfl⟩ := hright
        have h := (bend_offset_sides u v 1 t 0).2.2.2
        simp only [one_smul, one_mul, one_pow, mul_one, zero_smul, add_zero, zero_mul] at h
        rw [add_sub_cancel_left, h]
        exact mul_nonpos_of_nonneg_of_nonpos ht.1 hc.le
      exact hy.elim (fun hy => (not_lt_of_ge hzu) hy.2) (fun hy => (ne_of_gt hy.2) hzv)
  let τ := r / (2 * (‖u - v‖ + 1))
  have hτ : 0 < τ := div_pos hr (by positivity)
  let z := b + τ • (u - v)
  have hzr : z ∈ Metric.ball b r := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖b + τ • (u - v) - b‖ < r
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
    have hp : τ * (2 * (‖u - v‖ + 1)) = r := div_mul_cancel₀ r (by positivity)
    nlinarith only [hp, hτ, norm_nonneg (u - v)]
  have hzu : (star u * (z - b)).im = -τ * (star u * v).im := by
    dsimp only [z]
    simp only [add_sub_cancel_left, Complex.star_def, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hzv : (star v * (z - b)).im = -τ * (star u * v).im := by
    dsimp only [z]
    simp only [add_sub_cancel_left, Complex.star_def, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hp : 0 < -τ * (star u * v).im := mul_pos_of_neg_of_neg (neg_neg_of_pos hτ) hc
  have hzA : z ∈ A := ⟨hzr, hzu.symm ▸ hp⟩
  have hzB : z ∈ B := ⟨hzr, hzv.symm ▸ hp⟩
  have hpre : IsPreconnected (A ∪ B) := hAc.isPreconnected.union z hzA hzB hBc.isPreconnected
  obtain ⟨δ, hδ, hface⟩ := P.dartBorders_bend_left_offsets_mem_face_of_local_image d F hborder N hN harc hcover hi
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hεδ : ε < δ := half_lt_self hδ
  let f : ℝ → ℂ := fun t => b + t • (-u + ε • (Complex.I * u))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfn : f ⁻¹' Metric.ball b r ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds
      (by simpa only [f, zero_smul, add_zero] using Metric.mem_ball_self hr))
  obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp hfn
  let t := min (δ / 2) (e / 2)
  have ht : 0 < t := lt_min (half_pos hδ) (half_pos he)
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hte : t < e := (min_le_right _ _).trans_lt (half_lt_self he)
  have hfr : f t ∈ Metric.ball b r := by
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using hte
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i (by omega)).symm
  have hfu : 0 < (star u * (f t - b)).im := by
    have h := (bend_offset_sides u v 1 t ε).1
    simp only [one_smul, one_mul, one_pow, mul_one] at h
    dsimp only [f]
    rw [add_sub_cancel_left, h]
    exact mul_pos (mul_pos ht hε) (Complex.normSq_pos.mpr hu)
  have hfF : f t ∈ F.val := (hface t ε ht htδ hε hεδ).1
  have hWF : A ∪ B ⊆ F.val := by
    obtain ⟨z, _, hF⟩ := F.property
    rw [hF] at hfF ⊢
    rw [connectedComponentIn_eq hfF]
    exact hpre.subset_connectedComponentIn (Or.inl ⟨hfr, hfu⟩) hsafe
  refine ⟨r, hr, ?_⟩
  intro y hyr hy
  exact hWF (hy.elim (fun hu => Or.inl ⟨hyr, hu⟩) (fun hv => Or.inr ⟨hyr, hv⟩))

/-- Helper toward Definition 3.2: a reflex bend admits a small injective
two-segment return path in the bordering face and winding-one accumulation. -/
theorem dartBorders_bend_exists_reflex_return_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im < 0) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    let v := (P.arc d).point (i + 2) - b
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      let q := (Path.segment (b + r • v) (b + r • (u - v))).trans
        (Path.segment (b + r • (u - v)) (b - r • u))
      Function.Injective q ∧ (∀ t : I, t ∈ openParams → q t ∈ F.val) ∧
      b ∈ closure {w : ℂ | w ∈ F.val ∧
        HasWinding (((Path.segment (b - r • u) b).trans
          (Path.segment b (b + r • v))).trans q) w 1} := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨R, hR, hface⟩ :=
    P.dartBorders_bend_reflex_wedge_subset_face_of_local_image d F hborder N hN harc hcover hi hturn
  let r := min (1 / 2 : ℝ) (R / (2 * (‖u‖ + ‖v‖ + 1)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hprod : r * (2 * (‖u‖ + ‖v‖ + 1)) ≤ R :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have haR : b - r • u ∈ Metric.ball b R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith only [hprod, hr, norm_nonneg u, norm_nonneg v]
  have hcR : b + r • v ∈ Metric.ball b R := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith only [hprod, hr, norm_nonneg u, norm_nonneg v]
  have hpR : b + r • (u - v) ∈ Metric.ball b R := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hn := mul_le_mul_of_nonneg_left (norm_sub_le u v) hr.le
    nlinarith only [hprod, hr, norm_nonneg u, norm_nonneg v, hn]
  let α := Path.segment (b + r • v) (b + r • (u - v))
  let β := Path.segment (b + r • (u - v)) (b - r • u)
  let q := α.trans β
  have hc : (star u * v).im < 0 := hturn
  have hα (t : I) : (star v * (α t - b)).im = -r * (t : ℝ) * (star u * v).im := by
    dsimp only [α]
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hβ (t : I) : (star u * (β t - b)).im = -r * (1 - (t : ℝ)) * (star u * v).im := by
    dsimp only [β]
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hqcross (t : I) : (star (u - v) * (q t - b)).im =
      r * (1 - 2 * (t : ℝ)) * (star u * v).im := by
    dsimp only [q]
    rw [Path.trans_apply]
    split_ifs <;>
      simp only [α, β, Path.segment_apply, AffineMap.lineMap_apply_module,
        Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> ring
  have hqinj : Function.Injective q := by
    intro s t heq
    have he := congrArg (fun z : ℂ => (star (u - v) * (z - b)).im) heq
    rw [hqcross, hqcross] at he
    have he' : (r * (star u * v).im) * (s : ℝ) =
        (r * (star u * v).im) * (t : ℝ) := by nlinarith only [he]
    exact Subtype.ext (mul_left_cancel₀ (mul_ne_zero hr.ne' hc.ne) he')
  have hαR (t : I) : α t ∈ Metric.ball b R :=
    (convex_ball b R).segment_subset hcR hpR (by
      rw [Path.segment_apply]; exact lineMap_mem_segment ℝ _ _ t.2)
  have hβR (t : I) : β t ∈ Metric.ball b R :=
    (convex_ball b R).segment_subset hpR haR (by
      rw [Path.segment_apply]; exact lineMap_mem_segment ℝ _ _ t.2)
  have hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val := by
    intro t ht
    dsimp only [q]
    rw [Path.trans_apply]
    split_ifs with htHalf
    · apply hface _ (hαR _)
      right
      rw [hα]
      exact mul_pos_of_neg_of_neg
        (mul_neg_of_neg_of_pos (neg_neg_of_pos hr) (by change 0 < 2 * (t : ℝ); linarith only [ht.1])) hc
    · apply hface _ (hβR _)
      left
      rw [hβ]
      exact mul_pos_of_neg_of_neg
        (mul_neg_of_neg_of_pos (neg_neg_of_pos hr)
          (by change 0 < 1 - (2 * (t : ℝ) - 1); linarith only [ht.2])) hc
  refine ⟨r, hr, hr1, hqinj, hqF, ?_⟩
  rw [Metric.mem_closure_iff]
  intro η hη
  let τ := min (r / 2) (min (R / (2 * (‖u - v‖ + 1))) (η / (2 * (‖u - v‖ + 1))))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτr : τ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hτR : τ * (2 * (‖u - v‖ + 1)) ≤ R := by
    apply (le_div_iff₀ (by positivity)).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hτη : τ * (2 * (‖u - v‖ + 1)) ≤ η := by
    apply (le_div_iff₀ (by positivity)).mp
    exact (min_le_right _ _).trans (min_le_right _ _)
  let w := b + τ • (u - v)
  have hdist : dist w b = τ * ‖u - v‖ := by
    dsimp only [w]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
  have hwR : w ∈ Metric.ball b R := by
    rw [Metric.mem_ball, hdist]
    nlinarith only [hτR, hτ, norm_nonneg (u - v)]
  have hwu : (star u * (w - b)).im = -τ * (star u * v).im := by
    dsimp only [w]
    simp only [add_sub_cancel_left, Complex.star_def, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hwF : w ∈ F.val := hface w hwR (Or.inl
    (hwu.symm ▸ mul_pos_of_neg_of_neg (neg_neg_of_pos hτ) hc))
  have hwinding := hasWinding_bend_reflex_quadrilateral (b := b) hturn hr hτ hτr
  refine ⟨w, ⟨hwF, hwinding⟩, ?_⟩
  rw [dist_comm, hdist]
  nlinarith only [hτη, hτ, norm_nonneg (u - v)]

/-- Helper toward Definition 3.2: a bordering face satisfies the winding
left-side test at a bend with strictly negative turn cross product. -/
theorem dartBorders_toPath_leftAtOn_of_bend_right_turn_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image)
    (s : {t : I // t ∈ openParams}) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hbend : (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1))
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im < 0) :
    LeftAtOn F.val (P.arc d).toPath s := by
  let p := P.arc d
  change i + 2 < p.points.length at hi
  let B := p.point (i + 1)
  let u := B - p.point i
  let v := p.point (i + 2) - B
  obtain ⟨r, hr, hr1, hinj, hqface, hcl⟩ :=
    P.dartBorders_bend_exists_reflex_return_of_local_image d F hborder N hN harc hcover hi hturn
  let L := Polyline.segmentParameterStart i
  let M := Polyline.segmentParameterStart (i + 1)
  let H := Polyline.segmentParameterEnd p.points.length (i + 1)
  have hend : Polyline.segmentParameterEnd p.points.length i = M :=
    Polyline.segmentParameterEnd_eq_start_succ (by omega)
  have hLM : L < M := by
    rw [← hend]
    exact Polyline.segmentParameterStart_lt_end p.points.length i
  have hMH : M < H := Polyline.segmentParameterStart_lt_end p.points.length (i + 1)
  have hL0 : 0 ≤ L := (Polyline.segmentParameterStart_mem_Icc i).1
  have hH1 : H ≤ 1 := (Polyline.segmentParameterEnd_mem_Icc p.points.length (i + 1)).2
  let av := M - r * (M - L)
  let bv := M + r * (H - M)
  have hLa : L < av := by
    dsimp only [av]
    nlinarith only [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hLM)]
  have haM : av < M := by
    dsimp only [av]
    linarith only [mul_pos hr (sub_pos.mpr hLM)]
  have hMb : M < bv := by
    dsimp only [bv]
    linarith only [mul_pos hr (sub_pos.mpr hMH)]
  have hbH : bv < H := by
    dsimp only [bv]
    nlinarith only [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hMH)]
  let a : I := ⟨av, ⟨hL0.trans hLa.le, haM.le.trans (hMH.le.trans hH1)⟩⟩
  let b : I := ⟨bv, ⟨(hL0.trans hLM.le).trans hMb.le, hbH.le.trans hH1⟩⟩
  have ha : (0 : I) < a := hL0.trans_lt hLa
  have hb : b < (1 : I) := hbH.trans_le hH1
  have has : a < s.1 := by change av < (s.1 : ℝ); rw [hbend]; exact haM
  have hsb : s.1 < b := by change (s.1 : ℝ) < bv; rw [hbend]; exact hMb
  have hsEval : p.toPath s.1 = B := P.toPath_eq_vertex_at_bend d s hi hbend
  have haEval : p.toPath a = B - r • u := by
    have hf := Polyline.toPath_segment_affine_apply p (i := i) (by omega)
      a hLa.le (by rw [hend]; exact haM.le)
    rw [hend] at hf
    have hratio : ((a : ℝ) - L) / (M - L) = 1 - r := by
      change (M - r * (M - L) - L) / (M - L) = 1 - r
      field_simp
      ring
    change p.toPath a = p.point i + (((((a : ℝ) - L) / (M - L)) : ℝ) : ℂ) * u at hf
    rw [hratio] at hf
    rw [hf]
    dsimp only [u, B]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hbEval : p.toPath b = B + r • v := by
    have hf := Polyline.toPath_segment_affine_apply p (i := i + 1) (by omega)
      b hMb.le hbH.le
    have hratio : ((b : ℝ) - M) / (H - M) = r := by
      change (M + r * (H - M) - M) / (H - M) = r
      field_simp
      ring
    change p.toPath b = B + (((((b : ℝ) - M) / (H - M)) : ℝ) : ℂ) * v at hf
    rw [hratio] at hf
    exact hf
  have hleft := Polyline.toPath_affine_on_segment_subinterval p (i := i) (by omega)
    a s.1 has hLa.le (by rw [hend]; exact hbend.le)
  have hright := Polyline.toPath_affine_on_segment_subinterval p (i := i + 1) (by omega)
    s.1 b hsb hbend.ge hbH.le
  obtain ⟨f, hc, h0, h1, hedge⟩ := edgeSubarc_two_segments_reparam p.toPath a s.1 b
    has hsb hleft hright
  let q := (Path.segment (p.toPath b) (B + r • (u - v))).trans
    (Path.segment (B + r • (u - v)) (p.toPath a))
  have hqinj : Function.Injective q := by
    dsimp only [q]
    rw [haEval, hbEval]
    exact hinj
  have hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val := by
    dsimp only [q]
    rw [haEval, hbEval]
    exact hqface
  have hwind (w : ℂ) (hw : HasWinding (((Path.segment (B - r • u) B).trans
      (Path.segment B (B + r • v))).trans (((Path.segment (B + r • v) (B + r • (u - v))).trans
        (Path.segment (B + r • (u - v)) (B - r • u))))) w 1) :
      HasWinding ((edgeSubarc p.toPath a b (has.trans hsb).le).trans q) w 1 := by
    have hw' : HasWinding (((Path.segment (p.toPath a) (p.toPath s.1)).trans
        (Path.segment (p.toPath s.1) (p.toPath b))).trans q) w 1 := by
      dsimp only [q]
      rw [haEval, hbEval, hsEval]
      exact hw
    have ht := hw'.trans_reparam_left f hc h0 h1
    rw [← hedge] at ht
    exact ht
  refine ⟨a, b, ha, has, hsb, hb, q, hqinj, hqF, ?_⟩
  rw [hsEval]
  have hsubset : {w : ℂ | w ∈ F.val ∧
      HasWinding (((Path.segment (B - r • u) B).trans (Path.segment B (B + r • v))).trans
        (((Path.segment (B + r • v) (B + r • (u - v))).trans
        (Path.segment (B + r • (u - v)) (B - r • u))))) w 1} ⊆
      {w : ℂ | w ∈ F.val ∧
        HasWinding ((edgeSubarc p.toPath a b (has.trans hsb).le).trans q) w 1} :=
    fun w hw => ⟨hw.1, hwind w hw.2⟩
  exact closure_mono hsubset hcl

/-- Helper toward Definition 3.2: the two strict-turn constructions give
the left-side test whenever the bend cross product is nonzero. -/
theorem dartBorders_toPath_leftAtOn_of_bend_turn_ne_zero_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image)
    (s : {t : I // t ∈ openParams}) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hbend : (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1))
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im ≠ 0) :
    LeftAtOn F.val (P.arc d).toPath s := by
  rcases lt_or_gt_of_ne hturn with hneg | hpos
  · exact P.dartBorders_toPath_leftAtOn_of_bend_right_turn_of_local_image d F hborder N hN harc hcover s hi hbend hneg
  · exact P.dartBorders_toPath_leftAtOn_of_bend_left_turn_of_local_image d F hborder N hN harc hcover s hi hbend hpos

/-- Helper toward Definition 3.2: the left half-disk at a straight bend
lies in the face bordering the dart. -/
theorem dartBorders_bend_straight_left_halfDisk_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im = 0) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    ∃ r : ℝ, 0 < r ∧ ∀ y : ℂ, y ∈ ball b r →
      0 < (star u * (y - b)).im → y ∈ F.val := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  let v := (P.arc d).point (i + 2) - b
  obtain ⟨α, hα, hv⟩ := bend_directions_pos_parallel (P.arc d) (P.arc_simple d) hi hturn
  change v = α • u at hv
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i (by omega)).symm
  obtain ⟨r, hr, _, hlocal⟩ := P.bend_contact_local_image_of_local_image d hi N hN
    (by apply harc; rw [Polyline.range_toPath]
        exact (P.arc d).segmentAt_subset_image (by omega) (right_mem_segment ℝ _ _)) hcover
  let W := {y : ℂ | y ∈ ball b r ∧ 0 < (star u * (y - b)).im}
  have hWc : Convex ℝ W := by
    simpa only [one_mul] using signed_halfDisk_convex b u r 1
  have hWsafe : W ⊆ P.imageᶜ := by
    intro y hy hyP
    rcases (hlocal y hy.1).mp hyP with hleft | hright
    · have hz := segment_contact_side_eq_zero ((P.arc d).point i) b b y
        (right_mem_segment ℝ _ _) hleft
      exact (ne_of_gt hy.2) hz
    · have hz := segment_contact_side_eq_zero b ((P.arc d).point (i + 2)) b y
        (left_mem_segment ℝ _ _) hright
      change (star v * (y - b)).im = 0 at hz
      rw [hv, star_smul, star_trivial, smul_mul_assoc, Complex.smul_im,
        smul_eq_mul] at hz
      exact (ne_of_gt (mul_pos hα hy.2)) hz
  obtain ⟨δ, hδ, hface⟩ := P.dartBorders_bend_left_offsets_mem_face_of_local_image d F hborder N hN harc hcover hi
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hεδ : ε < δ := half_lt_self hδ
  let f : ℝ → ℂ := fun t => b + t • (-u + ε • (Complex.I * u))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfn : f ⁻¹' ball b r ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds
      (by simpa only [f, zero_smul, add_zero] using mem_ball_self hr))
  obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp hfn
  let t := min (δ / 2) (e / 2)
  have ht : 0 < t := lt_min (half_pos hδ) (half_pos he)
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hte : t < e := (min_le_right _ _).trans_lt (half_lt_self he)
  have hfr : f t ∈ ball b r := by
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using hte
  have hfu : 0 < (star u * (f t - b)).im := by
    have h := (bend_offset_sides u v 1 t ε).1
    simp only [one_smul, one_mul, one_pow, mul_one] at h
    dsimp only [f]
    rw [add_sub_cancel_left, h]
    exact mul_pos (mul_pos ht hε) (Complex.normSq_pos.mpr hu)
  have hfF : f t ∈ F.val := (hface t ε ht htδ hε hεδ).1
  have hWF : W ⊆ F.val := by
    obtain ⟨z, _, hF⟩ := F.property
    rw [hF] at hfF ⊢
    rw [connectedComponentIn_eq hfF]
    exact hWc.isPreconnected.subset_connectedComponentIn ⟨hfr, hfu⟩ hWsafe
  exact ⟨r, hr, fun y hyr hyu => hWF ⟨hyr, hyu⟩⟩

/-- Helper toward Definition 3.2: every sufficiently small semicircle
centered at a straight bend returns through the bordering face, and its
winding-one face points accumulate at the bend. -/
theorem dartBorders_bend_straight_semicircleLoop_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) {i : ℕ}
    (hi : i + 2 < (P.arc d).points.length)
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im = 0) :
    let b := (P.arc d).point (i + 1)
    let u := b - (P.arc d).point i
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      Function.Injective (leftSemicircle b (ε • u)) ∧
      (∀ t : I, t ∈ openParams → leftSemicircle b (ε • u) t ∈ F.val) ∧
      b ∈ closure {w : ℂ | w ∈ F.val ∧ HasWinding (semicircleLoop b (ε • u)) w 1} := by
  dsimp only
  let b := (P.arc d).point (i + 1)
  let u := b - (P.arc d).point i
  have hu : u ≠ 0 := sub_ne_zero.mpr ((P.arc_simple d).1 i (by omega)).symm
  obtain ⟨R, hR, hhalf⟩ :=
    P.dartBorders_bend_straight_left_halfDisk_of_local_image d F hborder N hN harc hcover hi hturn
  refine ⟨R / (‖u‖ + 1), div_pos hR (by positivity), ?_⟩
  intro ε hε hεδ
  let v := ε • u
  have hv : v ≠ 0 := smul_ne_zero hε.ne' hu
  have hvr : ‖v‖ < R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have h := (lt_div_iff₀ (by positivity : 0 < ‖u‖ + 1)).mp hεδ
    nlinarith only [h, hε]
  refine ⟨leftSemicircle_injective b v hv, ?_, Metric.mem_closure_iff.mpr ?_⟩
  · intro t ht
    apply hhalf _
    · rw [Metric.mem_ball, leftSemicircle_dist]
      exact hvr
    · have hp := leftSemicircle_side_pos b v hv t ht
      have he : (star v * (leftSemicircle b v t - b)).im =
          ε * (star u * (leftSemicircle b v t - b)).im := by
        dsimp only [v]
        rw [star_smul, star_trivial, smul_mul_assoc, Complex.smul_im, smul_eq_mul]
      rw [he] at hp
      exact (mul_pos_iff.mp hp).resolve_right (fun h => (not_lt_of_gt hε) h.1) |>.2
  · intro η hη
    let τ := min (1 / 2) (η / (2 * (‖v‖ + 1)))
    have hτ : 0 < τ := lt_min (by norm_num) (div_pos hη (by positivity))
    have hτ1 : τ < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hτη : τ * (2 * (‖v‖ + 1)) ≤ η :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    let w := b + v * (τ * Complex.I)
    have hwx : dist w b = τ * ‖v‖ := by
      rw [dist_eq_norm]
      change ‖b + v * (τ * Complex.I) - b‖ = _
      rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hτ, Complex.norm_I, mul_one, mul_comm]
    have hwF : w ∈ F.val := by
      apply hhalf _
      · rw [Metric.mem_ball, hwx]
        exact (mul_lt_of_lt_one_left (norm_pos_iff.mpr hv) hτ1).trans hvr
      · have he : star u * (w - b) =
            ((ε * τ : ℝ) : ℂ) * Complex.I * (star u * u) := by
          dsimp [w, v]
          push_cast
          ring
        rw [he, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
        simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
          sub_zero, add_zero, mul_one, zero_add]
        exact mul_pos (mul_pos hε hτ) (Complex.normSq_pos.mpr hu)
    refine ⟨w, ⟨hwF, hasWinding_semicircleLoop b v hv τ hτ hτ1⟩, ?_⟩
    rw [dist_comm, hwx]
    nlinarith only [hτη, hτ, norm_nonneg v]

/-- Helper toward Definition 3.2: a bordering face satisfies the winding
left-side test at a bend with zero turn cross product. -/
theorem dartBorders_toPath_leftAtOn_of_bend_turn_eq_zero_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image)
    (s : {t : I // t ∈ openParams}) (i : ℕ)
    (hi : i + 2 < (P.arc d).points.length)
    (hbend : (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1))
    (hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im = 0) :
    LeftAtOn F.val (P.arc d).toPath s := by
  let p := P.arc d
  change i + 2 < p.points.length at hi
  let B := p.point (i + 1)
  let u := B - p.point i
  let v := p.point (i + 2) - B
  obtain ⟨α, hα, hv⟩ := bend_directions_pos_parallel p (P.arc_simple d) hi hturn
  change v = α • u at hv
  obtain ⟨δ, hδ, hreturn⟩ :=
    P.dartBorders_bend_straight_semicircleLoop_of_local_image d F hborder N hN harc hcover hi hturn
  let r := min (δ / 2) (min (1 / 2) (α / 2))
  have hr : 0 < r := lt_min (half_pos hδ) (lt_min (by norm_num) (half_pos hα))
  have hrδ : r < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hr1 : r < 1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have hrα : r < α := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
    (half_lt_self hα)
  let ρ := r / α
  have hρ : 0 < ρ := div_pos hr hα
  have hρ1 : ρ < 1 := (div_lt_one hα).mpr hrα
  have hρv : ρ • v = r • u := by
    rw [hv, smul_smul]
    dsimp only [ρ]
    rw [div_mul_cancel₀ _ hα.ne']
  obtain ⟨hinj, hqface, hcl⟩ := hreturn r hr hrδ
  let L := Polyline.segmentParameterStart i
  let M := Polyline.segmentParameterStart (i + 1)
  let H := Polyline.segmentParameterEnd p.points.length (i + 1)
  have hend : Polyline.segmentParameterEnd p.points.length i = M :=
    Polyline.segmentParameterEnd_eq_start_succ (by omega)
  have hLM : L < M := by
    rw [← hend]
    exact Polyline.segmentParameterStart_lt_end p.points.length i
  have hMH : M < H := Polyline.segmentParameterStart_lt_end p.points.length (i + 1)
  have hL0 : 0 ≤ L := (Polyline.segmentParameterStart_mem_Icc i).1
  have hH1 : H ≤ 1 := (Polyline.segmentParameterEnd_mem_Icc p.points.length (i + 1)).2
  let av := M - r * (M - L)
  let bv := M + ρ * (H - M)
  have hLa : L < av := by
    dsimp only [av]
    nlinarith only [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hLM)]
  have haM : av < M := by
    dsimp only [av]
    linarith only [mul_pos hr (sub_pos.mpr hLM)]
  have hMb : M < bv := by
    dsimp only [bv]
    linarith only [mul_pos hρ (sub_pos.mpr hMH)]
  have hbH : bv < H := by
    dsimp only [bv]
    nlinarith only [mul_pos (sub_pos.mpr hρ1) (sub_pos.mpr hMH)]
  let a : I := ⟨av, ⟨hL0.trans hLa.le, haM.le.trans (hMH.le.trans hH1)⟩⟩
  let b : I := ⟨bv, ⟨(hL0.trans hLM.le).trans hMb.le, hbH.le.trans hH1⟩⟩
  have ha : (0 : I) < a := hL0.trans_lt hLa
  have hb : b < (1 : I) := hbH.trans_le hH1
  have has : a < s.1 := by change av < (s.1 : ℝ); rw [hbend]; exact haM
  have hsb : s.1 < b := by change (s.1 : ℝ) < bv; rw [hbend]; exact hMb
  have hsEval : p.toPath s.1 = B := P.toPath_eq_vertex_at_bend d s hi hbend
  have haEval : p.toPath a = B - r • u := by
    have hf := Polyline.toPath_segment_affine_apply p (i := i) (by omega)
      a hLa.le (by rw [hend]; exact haM.le)
    rw [hend] at hf
    have hratio : ((a : ℝ) - L) / (M - L) = 1 - r := by
      change (M - r * (M - L) - L) / (M - L) = 1 - r
      field_simp
      ring
    change p.toPath a = p.point i + (((((a : ℝ) - L) / (M - L)) : ℝ) : ℂ) * u at hf
    rw [hratio] at hf
    rw [hf]
    dsimp only [u, B]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hbEval : p.toPath b = B + r • u := by
    have hf := Polyline.toPath_segment_affine_apply p (i := i + 1) (by omega)
      b hMb.le hbH.le
    have hratio : ((b : ℝ) - M) / (H - M) = ρ := by
      change (M + ρ * (H - M) - M) / (H - M) = ρ
      field_simp
      ring
    change p.toPath b = B + (((((b : ℝ) - M) / (H - M)) : ℝ) : ℂ) * v at hf
    rw [hratio] at hf
    change p.toPath b = B + ρ • v at hf
    rw [hf, hρv]
  have hleft := Polyline.toPath_affine_on_segment_subinterval p (i := i) (by omega)
    a s.1 has hLa.le (by rw [hend]; exact hbend.le)
  have hright := Polyline.toPath_affine_on_segment_subinterval p (i := i + 1) (by omega)
    s.1 b hsb hbend.ge hbH.le
  obtain ⟨f, hc, h0, h1, hedge⟩ := edgeSubarc_two_segments_reparam p.toPath a s.1 b
    has hsb hleft hright
  let q : Path (p.toPath b) (p.toPath a) :=
    (leftSemicircle B (r • u)).cast hbEval haEval
  have hqinj : Function.Injective q := by
    intro t t' htt'
    exact hinj htt'
  have hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val := by
    intro t ht
    exact hqface t ht
  have hpairfun (t : I) :
      ((Path.segment (p.toPath a) (p.toPath s.1)).trans
        (Path.segment (p.toPath s.1) (p.toPath b))) t =
      Path.segment (B - r • u) (B + r • u) t := by
    rw [haEval, hsEval, hbEval, segment_trans_midpoint]
  have hwind (w : ℂ) (hw : HasWinding (semicircleLoop B (r • u)) w 1) :
      HasWinding ((edgeSubarc p.toPath a b (has.trans hsb).le).trans q) w 1 := by
    have hw' : HasWinding (((Path.segment (p.toPath a) (p.toPath s.1)).trans
        (Path.segment (p.toPath s.1) (p.toPath b))).trans q) w 1 := by
      apply (hasWinding_congr_fun _ (semicircleLoop B (r • u)) w 1 ?_).mpr hw
      intro t
      change (((Path.segment (p.toPath a) (p.toPath s.1)).trans
        (Path.segment (p.toPath s.1) (p.toPath b))).trans q) t =
        ((Path.segment (B - r • u) (B + r • u)).trans (leftSemicircle B (r • u))) t
      rw [Path.trans_apply, Path.trans_apply]
      split_ifs
      · exact hpairfun _
      · rfl
    have ht := hw'.trans_reparam_left f hc h0 h1
    rw [← hedge] at ht
    exact ht
  refine ⟨a, b, ha, has, hsb, hb, q, hqinj, hqF, ?_⟩
  rw [hsEval]
  have hsubset : {w : ℂ | w ∈ F.val ∧ HasWinding (semicircleLoop B (r • u)) w 1} ⊆
      {w : ℂ | w ∈ F.val ∧
        HasWinding ((edgeSubarc p.toPath a b (has.trans hsb).le).trans q) w 1} :=
    fun w hw => ⟨hw.1, hwind w hw.2⟩
  exact closure_mono hsubset hcl

/-- Helper toward Definition 3.2: a bordering face satisfies the winding
left-side test at every interior bend, including straight subdivisions. -/
theorem dartBorders_toPath_leftAtOn_of_bend_of_local_image
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) 
    (d : D) (F : P.Face) (hborder : P.dartBorders d F)
    (N : Set ℂ) (hN : IsOpen N) (harc : Set.range (P.arc d).toPath ⊆ N)
    (hcover : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image)
    (s : {t : I // t ∈ openParams}) (i : ℕ)
    (hi : i + 2 < (P.arc d).points.length)
    (hbend : (s.1 : ℝ) = Polyline.segmentParameterStart (i + 1)) :
    LeftAtOn F.val (P.arc d).toPath s := by
  by_cases hturn : (star ((P.arc d).point (i + 1) - (P.arc d).point i) *
      ((P.arc d).point (i + 2) - (P.arc d).point (i + 1))).im = 0
  · exact P.dartBorders_toPath_leftAtOn_of_bend_turn_eq_zero_of_local_image d F hborder N hN harc hcover s i hi hbend hturn
  · exact P.dartBorders_toPath_leftAtOn_of_bend_turn_ne_zero_of_local_image d F hborder N hN harc hcover s hi hbend hturn

/-- Helper toward Definition 3.2: local coverage of the closed arc suffices
for the left winding-side test at every open parameter, including bends. -/
theorem dartBorders_toPath_leftAtOn_of_local_image
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (hborder : P.dartBorders d F)
    (N : Set ℂ) (hopen : IsOpen N)
    (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∀ s : {t : I // t ∈ openParams}, LeftAtOn F.val (P.arc d).toPath s := by
  intro s
  obtain ⟨i, hi, hstart, hend⟩ := Polyline.exists_segment_parameter_interval
    (P.arc_length d) (s.1 : ℝ) s.1.property.1 s.property.2
  rcases eq_or_lt_of_le hstart with heq | hlt
  · have hi0 : i ≠ 0 := by
      intro hz
      rw [hz, Polyline.segmentParameterStart_zero] at heq
      exact (ne_of_gt s.property.1) heq.symm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    exact P.dartBorders_toPath_leftAtOn_of_bend_of_local_image
      d F hborder N hopen harc hlocal s j (by omega) heq.symm
  · exact P.dartBorders_toPath_leftAtOn_of_local_image_of_strictSegment
      d F hborder hi s hlt hend N hopen harc hlocal

/-- Helper toward Definition 3.2: reversal of the actual simple PL arc
gives the right winding-side test at every open parameter from a border
of the reverse dart, under the same local coverage hypothesis. -/
theorem dartBorders_flip_toPath_rightAtOn_of_local_image
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (hborder : P.dartBorders (flip d) F)
    (N : Set ℂ) (hopen : IsOpen N)
    (harc : Set.range (P.arc d).toPath ⊆ N)
    (hlocal : ∀ z, z ∈ P.image → z ∈ N → z ∈ ⋃ e, (P.arc e).image) :
    ∀ s : {t : I // t ∈ openParams}, RightAtOn F.val (P.arc d).toPath s := by
  apply (P.forall_leftAtOn_flip_toPath_iff_forall_rightAtOn d F.val).mp
  have harc' : Set.range (P.arc (flip d)).toPath ⊆ N := by
    rw [Polyline.range_toPath, P.arc_flip d, Polyline.image_reverse_transfer,
      ← Polyline.range_toPath]
    exact harc
  exact P.dartBorders_toPath_leftAtOn_of_local_image
    (flip d) F hborder N hopen harc' hlocal

end PLDrawing


























































































end DirectedDistances.PlanarMap

end
