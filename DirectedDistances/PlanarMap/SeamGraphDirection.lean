module

public import DirectedDistances.PlanarMap.PlaneRealization
public import DirectedDistances.PlanarMap.SeamSectorDirection
public import DirectedDistances.PlanarMap.SeamSectorTurn
public import DirectedDistances.PlanarMap.CcwPiecewiseLinear

/-! Helper toward Theorem 1.4 (Q-M0-repr drawing: seam directions at seam vertices);
not a paper result. -/

public section
namespace DirectedDistances.PlanarMap

open Set

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: seam directions at seam vertices);
not a paper result. The first segment of a polyline lies in its image. -/
private theorem firstSegment_point_mem_image (p : Polyline)
    (hlen : 2 ≤ p.points.length) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    p.start + t • p.initialDirection ∈ p.image := by
  have hp0 : p.point 0 = p.start := by
    cases p with
    | mk points hpoints =>
      cases points with
      | nil => exact False.elim (hpoints rfl)
      | cons a rest => rfl
  have hline : p.start + t • p.initialDirection =
      AffineMap.lineMap p.start (p.point 1) t := by
    rw [AffineMap.lineMap_apply_module']
    simp only [Polyline.initialDirection]
    abel
  have hseg : p.start + t • p.initialDirection ∈ p.segmentAt 0 := by
    change p.start + t • p.initialDirection ∈ segment ℝ (p.point 0) (p.point 1)
    rw [hp0, hline]
    exact lineMap_mem_segment ℝ p.start (p.point 1) ⟨ht0, ht1⟩
  change p.start + t • p.initialDirection ∈
    {p.start} ∪ {z | ∃ i, i + 1 < p.points.length ∧ z ∈ p.segmentAt i}
  right
  exact ⟨0, by omega, hseg⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: seam directions at seam vertices);
not a paper result. Coordinates on the first segment are affine in its parameter. -/
private theorem firstSegment_coords (p : Polyline) (x0 y0 : ℝ)
    (hs : p.start = (⟨x0, y0⟩ : ℂ)) (t : ℝ) :
    (p.start + t • p.initialDirection).re = x0 + t * p.initialDirection.re ∧
      (p.start + t • p.initialDirection).im = y0 + t * p.initialDirection.im := by
  rw [hs]
  simp

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: seam directions at seam vertices);
not a paper result. There is a positive short parameter staying in the affine window. -/
private theorem exists_small_parameter (r u : ℝ) (hr : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ |t * u| < r := by
  let t := min (1 / 2) (r / (2 * (|u| + 1)))
  have hd : 0 < 2 * (|u| + 1) := by positivity
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num) (div_pos hr hd)
  have ht1 : t < 1 := by
    dsimp [t]
    exact (min_le_left _ _).trans_lt (by norm_num)
  have hprod : t * (2 * (|u| + 1)) ≤ r :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  have htu : t * |u| < r := by
    nlinarith [hprod, abs_nonneg u]
  refine ⟨t, ht, ht1, ?_⟩
  rw [abs_mul, abs_of_pos ht]
  exact htu

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: seam directions at seam vertices);
not a paper result. A graph-constrained segment pointing right has the right seam slope. -/
private theorem initialDirection_graph_slope_right (f : ℝ → ℝ) (x0 r sR : ℝ)
    (hr : 0 < r)
    (hR : ∀ x ∈ Icc x0 (x0 + r), f x = f x0 + sR * (x - x0))
    (p : Polyline) (hs : p.start = (⟨x0, f x0⟩ : ℂ))
    (hlen : 2 ≤ p.points.length) (hgraph : ∀ z ∈ p.image, z.im = f z.re)
    (hright : 0 < p.initialDirection.re) :
    p.initialDirection.im = sR * p.initialDirection.re := by
  obtain ⟨t, ht, ht1, hsmall⟩ := exists_small_parameter r p.initialDirection.re hr
  have hcoord := firstSegment_coords p x0 (f x0) hs t
  have hmem := firstSegment_point_mem_image p hlen t (le_of_lt ht) (le_of_lt ht1)
  have heq := hgraph _ hmem
  rw [hcoord.1, hcoord.2] at heq
  have hbounds := abs_lt.mp hsmall
  have hpositive : 0 < t * p.initialDirection.re := mul_pos ht hright
  have hx : x0 + t * p.initialDirection.re ∈ Icc x0 (x0 + r) := by
    constructor <;> nlinarith
  have hf := hR _ hx
  rw [hf] at heq
  have hmul : t * p.initialDirection.im = t * (sR * p.initialDirection.re) := by
    have heq' : f x0 + t * p.initialDirection.im =
        f x0 + t * (sR * p.initialDirection.re) := by
      calc
        f x0 + t * p.initialDirection.im =
            f x0 + sR * (x0 + t * p.initialDirection.re - x0) := heq
        _ = f x0 + t * (sR * p.initialDirection.re) := by ring
    exact add_left_cancel heq'
  exact mul_left_cancel₀ (ne_of_gt ht) hmul

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: seam directions at seam vertices);
not a paper result. A graph-constrained segment pointing left has the left seam slope. -/
private theorem initialDirection_graph_slope_left (f : ℝ → ℝ) (x0 r sL : ℝ)
    (hr : 0 < r)
    (hL : ∀ x ∈ Icc (x0 - r) x0, f x = f x0 + sL * (x - x0))
    (p : Polyline) (hs : p.start = (⟨x0, f x0⟩ : ℂ))
    (hlen : 2 ≤ p.points.length) (hgraph : ∀ z ∈ p.image, z.im = f z.re)
    (hleft : p.initialDirection.re < 0) :
    p.initialDirection.im = sL * p.initialDirection.re := by
  obtain ⟨t, ht, ht1, hsmall⟩ := exists_small_parameter r p.initialDirection.re hr
  have hcoord := firstSegment_coords p x0 (f x0) hs t
  have hmem := firstSegment_point_mem_image p hlen t (le_of_lt ht) (le_of_lt ht1)
  have heq := hgraph _ hmem
  rw [hcoord.1, hcoord.2] at heq
  have hbounds := abs_lt.mp hsmall
  have hnegative : t * p.initialDirection.re < 0 := mul_neg_of_pos_of_neg ht hleft
  have hx : x0 + t * p.initialDirection.re ∈ Icc (x0 - r) x0 := by
    constructor <;> nlinarith
  have hf := hL _ hx
  rw [hf] at heq
  have hmul : t * p.initialDirection.im = t * (sL * p.initialDirection.re) := by
    have heq' : f x0 + t * p.initialDirection.im =
        f x0 + t * (sL * p.initialDirection.re) := by
      calc
        f x0 + t * p.initialDirection.im =
            f x0 + sL * (x0 + t * p.initialDirection.re - x0) := heq
        _ = f x0 + t * (sL * p.initialDirection.re) := by ring
    exact add_left_cancel heq'
  exact mul_left_cancel₀ (ne_of_gt ht) hmul

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: seam directions at seam vertices);
not a paper result. Graph contact excludes vertical initial directions and fixes the ray. -/
theorem initialDirection_on_graph_sign (f : ℝ → ℝ) (x0 r sL sR : ℝ)
    (hr : 0 < r)
    (hR : ∀ x ∈ Icc x0 (x0 + r), f x = f x0 + sR * (x - x0))
    (hL : ∀ x ∈ Icc (x0 - r) x0, f x = f x0 + sL * (x - x0))
    (p : Polyline) (hs : p.start = (⟨x0, f x0⟩ : ℂ))
    (hlen : 2 ≤ p.points.length) (hne : p.point 1 ≠ p.start)
    (hgraph : ∀ z ∈ p.image, z.im = f z.re) :
    (0 < p.initialDirection.re →
      ∃ c : ℝ, 0 < c ∧ p.initialDirection = (c : ℂ) * ⟨1, sR⟩) ∧
    (p.initialDirection.re < 0 →
      ∃ c : ℝ, 0 < c ∧ p.initialDirection = (c : ℂ) * ⟨-1, -sL⟩) ∧
    p.initialDirection.re ≠ 0 := by
  have hu : p.initialDirection ≠ 0 := by
    intro h
    have hp1 : p.point 1 - p.start = 0 := by
      simpa [Polyline.initialDirection] using h
    exact hne (sub_eq_zero.mp hp1)
  have hvertical : p.initialDirection.re ≠ 0 := by
    intro hz
    obtain ⟨t, ht, ht1, _⟩ := exists_small_parameter r p.initialDirection.re hr
    have hcoord := firstSegment_coords p x0 (f x0) hs t
    have hmem := firstSegment_point_mem_image p hlen t (le_of_lt ht) (le_of_lt ht1)
    have heq := hgraph _ hmem
    rw [hcoord.1, hcoord.2, hz, mul_zero, add_zero] at heq
    have him : p.initialDirection.im = 0 := by
      have hmul : t * p.initialDirection.im = 0 := by linarith [heq]
      exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt ht)
    apply hu
    apply Complex.ext <;> simp [hz, him]
  constructor
  · intro hright
    have him := initialDirection_graph_slope_right f x0 r sR hr hR p hs
      hlen hgraph hright
    refine ⟨p.initialDirection.re, hright, ?_⟩
    apply Complex.ext
    · simp
    · simp [him]
      ring
  constructor
  · intro hleft
    have him := initialDirection_graph_slope_left f x0 r sL hr hL p hs
      hlen hgraph hleft
    refine ⟨-p.initialDirection.re, neg_pos.mpr hleft, ?_⟩
    apply Complex.ext
    · simp
    · simp [him]
      ring
  exact hvertical

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: seam directions at seam vertices);
not a paper result. A segment on a two-sided local affine graph follows one ray. -/
theorem initialDirection_on_graph (f : ℝ → ℝ) (x0 r sL sR : ℝ)
    (hr : 0 < r)
    (hR : ∀ x ∈ Icc x0 (x0 + r), f x = f x0 + sR * (x - x0))
    (hL : ∀ x ∈ Icc (x0 - r) x0, f x = f x0 + sL * (x - x0))
    (p : Polyline) (hs : p.start = (⟨x0, f x0⟩ : ℂ))
    (hlen : 2 ≤ p.points.length) (hne : p.point 1 ≠ p.start)
    (hgraph : ∀ z ∈ p.image, z.im = f z.re) :
    (∃ c : ℝ, 0 < c ∧ p.initialDirection = (c : ℂ) * ⟨1, sR⟩) ∨
      (∃ c : ℝ, 0 < c ∧ p.initialDirection = (c : ℂ) * ⟨-1, -sL⟩) := by
  obtain ⟨hRdir, hLdir, hne_re⟩ := initialDirection_on_graph_sign f x0 r sL sR
    hr hR hL p hs hlen hne hgraph
  rcases lt_trichotomy p.initialDirection.re 0 with hleft | hzero | hright
  · exact Or.inr (hLdir hleft)
  · exact False.elim (hne_re hzero)
  · exact Or.inl (hRdir hright)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: seam directions at seam vertices);
not a paper result. The turn depends only on the two complex arguments. -/
theorem ccwTurn_eq_of_arg_eq {a a' b b' : ℂ}
    (ha : Complex.arg a = Complex.arg a') (hb : Complex.arg b = Complex.arg b') :
    ccwTurn a b = ccwTurn a' b' := by
  simp only [ccwTurn, ha, hb]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: seam directions at seam vertices);
not a paper result. Positive rescaling of the first direction preserves its turn. -/
theorem ccwTurn_smul_left (a b : ℂ) (c : ℝ) (hc : 0 < c) :
    ccwTurn ((c : ℂ) * a) b = ccwTurn a b := by
  simpa using ccwTurn_smul_pos a b c 1 hc zero_lt_one

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: seam directions at seam vertices);
not a paper result. Positive rescaling of the second direction preserves its turn. -/
theorem ccwTurn_smul_right (a b : ℂ) (c : ℝ) (hc : 0 < c) :
    ccwTurn a ((c : ℂ) * b) = ccwTurn a b := by
  simpa using ccwTurn_smul_pos a b 1 c zero_lt_one hc

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: seam directions at seam vertices);
not a paper result. Equal arguments on a star preserve counterclockwise successors. -/
theorem ccwSuccessor_congr_arg {D : Type*} (star : Set D) (dir dir' : D → ℂ)
    (h : ∀ x ∈ star, Complex.arg (dir x) = Complex.arg (dir' x)) (d e : D) :
    CcwSuccessor star dir d e ↔ CcwSuccessor star dir' d e := by
  unfold CcwSuccessor
  constructor
  · rintro ⟨hfin, hd, he, hnext⟩
    refine ⟨hfin, hd, he, ?_⟩
    rcases hnext with hsingle | ⟨hne, hmin⟩
    · exact Or.inl hsingle
    · refine Or.inr ⟨hne, ?_⟩
      intro f hf hfd
      have hde := ccwTurn_eq_of_arg_eq (h d hd) (h e he)
      have hdf := ccwTurn_eq_of_arg_eq (h d hd) (h f hf)
      simpa only [hde, hdf] using hmin f hf hfd
  · rintro ⟨hfin, hd, he, hnext⟩
    refine ⟨hfin, hd, he, ?_⟩
    rcases hnext with hsingle | ⟨hne, hmin⟩
    · exact Or.inl hsingle
    · refine Or.inr ⟨hne, ?_⟩
      intro f hf hfd
      have hde := ccwTurn_eq_of_arg_eq (h d hd) (h e he)
      have hdf := ccwTurn_eq_of_arg_eq (h d hd) (h f hf)
      simpa only [hde, hdf] using hmin f hf hfd

end DirectedDistances.PlanarMap
