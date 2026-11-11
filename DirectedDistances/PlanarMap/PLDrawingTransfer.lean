module

public import DirectedDistances.PlanarMap.PolylineLocalStrip
public import DirectedDistances.PlanarMap.PastTransferMap
public import DirectedDistances.PlanarMap.CcwPiecewiseLinear

public section

namespace DirectedDistances.PlanarMap

noncomputable section

namespace Polyline

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
private theorem initialDirection_ofHead_cons (a b : ℂ) (l : List ℂ) :
    (ofHead a (b :: l)).initialDirection = b - a := by
  simp [initialDirection, point, start, ofHead]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
private theorem cutPoint_sub_start (x : ℝ) (a b : ℂ) :
    cutPoint x a b - a = (cutParameter x a b : ℂ) * (b - a) := by
  simp only [cutPoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
    Complex.real_smul]
  ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem initialDirection_subdivideOne (p : Polyline) (x : ℝ)
    (hlen : 2 ≤ p.points.length) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      (subdivideOne p x).initialDirection = (c : ℂ) * p.initialDirection := by
  rcases p with ⟨l, hl⟩
  cases l with
  | nil => exact (hl rfl).elim
  | cons a l =>
    cases l with
    | nil => simp at hlen
    | cons b l =>
      change ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
        (ofHead a (cutTail x a (b :: l))).initialDirection =
          (c : ℂ) * (ofHead a (b :: l)).initialDirection
      by_cases hc : cutParameter x a b ∈ Set.Ioo 0 1
      · refine ⟨cutParameter x a b, hc.1, hc.2.le, ?_⟩
        rw [cutTail, ite_eq_left hc, initialDirection_ofHead_cons,
          initialDirection_ofHead_cons, cutPoint_sub_start]
      · refine ⟨1, zero_lt_one, le_rfl, ?_⟩
        rw [cutTail, ite_eq_right hc, initialDirection_ofHead_cons,
          initialDirection_ofHead_cons]
        simp

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem point_reverse_transfer (p : Polyline) {i : ℕ} (hi : i < p.points.length) :
    p.reverse.point i = p.point (p.points.length - 1 - i) := by
  change p.points.reverse.getD i p.reverse.start = _
  rw [List.getD_reverse i hi]
  have hj : p.points.length - 1 - i < p.points.length := by omega
  change p.points.getD (p.points.length - 1 - i) p.reverse.start =
    p.points.getD (p.points.length - 1 - i) p.start
  rw [List.getD_eq_getElem (l := p.points) (d := p.reverse.start) hj,
    List.getD_eq_getElem (l := p.points) (d := p.start) hj]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem segmentAt_reverse_transfer (p : Polyline) {i : ℕ}
    (hi : i + 1 < p.points.length) :
    p.reverse.segmentAt i = p.segmentAt (p.points.length - 2 - i) := by
  unfold segmentAt
  rw [point_reverse_transfer p (by omega), point_reverse_transfer p hi]
  have h0 : p.points.length - 1 - i = p.points.length - 2 - i + 1 := by omega
  have h1 : p.points.length - 1 - (i + 1) = p.points.length - 2 - i := by omega
  rw [h0, h1, segment_symm]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
private theorem reverse_initialDirection_prefix (a b : ℂ) (l : List ℂ)
    (hl : 1 ≤ l.length) :
    (ofHead a (b :: l)).reverse.initialDirection = (ofHead b l).reverse.initialDirection := by
  cases l with
  | nil => simp at hl
  | cons c l =>
    simp only [initialDirection, start_reverse]
    rw [reverse_point_one _ (by simp [ofHead]), reverse_point_one _ (by simp [ofHead])]
    simp [ofHead, point, finish, start]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem reverse_initialDirection_subdivideOne (p : Polyline) (x : ℝ)
    (hlen : 2 ≤ p.points.length) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      (subdivideOne p x).reverse.initialDirection = (c : ℂ) * p.reverse.initialDirection := by
  suffices hh : ∀ (l : List ℂ) (a b : ℂ),
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
        (subdivideOne (ofHead a (b :: l)) x).reverse.initialDirection =
          (c : ℂ) * (ofHead a (b :: l)).reverse.initialDirection by
    rcases p with ⟨l, hl⟩
    cases l with
    | nil => exact (hl rfl).elim
    | cons a l =>
      cases l with
      | nil => simp at hlen
      | cons b l => exact hh l a b
  intro l
  induction l with
  | nil =>
    intro a b
    by_cases hc : cutParameter x a b ∈ Set.Ioo 0 1
    · refine ⟨1 - cutParameter x a b, sub_pos.mpr hc.2, by linarith [hc.1], ?_⟩
      have he := cutPoint_sub_start x a b
      simp only [subdivideOne, ofHead, start, List.head_cons, List.tail_cons,
        cutTail, ite_eq_left hc, reverse, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, initialDirection,
        point, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      push_cast
      linear_combination he
    · refine ⟨1, zero_lt_one, le_rfl, ?_⟩
      simp [subdivideOne, ofHead, start, cutTail, hc]
  | cons z l ih =>
    intro a b
    obtain ⟨c, hc, hc1, he⟩ := ih b z
    refine ⟨c, hc, hc1, ?_⟩
    rw [reverse_initialDirection_prefix a b (z :: l) (by simp)]
    rw [← he]
    change (ofHead a (cutTail x a (b :: z :: l))).reverse.initialDirection =
      (ofHead b (cutTail x b (z :: l))).reverse.initialDirection
    have ht : 1 ≤ (cutTail x b (z :: l)).length := by
      simp only [cutTail]
      split <;> simp
    by_cases hab : cutParameter x a b ∈ Set.Ioo 0 1
    · rw [cutTail, ite_eq_left hab]
      rw [reverse_initialDirection_prefix _ _ _ (by simp)]
      exact reverse_initialDirection_prefix _ _ _ ht
    · rw [cutTail, ite_eq_right hab]
      exact reverse_initialDirection_prefix _ _ _ ht

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem image_reverse_transfer (p : Polyline) : p.reverse.image = p.image := by
  have hsub (q : Polyline) : q.reverse.image ⊆ q.image := by
    rintro z (hz | ⟨i, hi, hz⟩)
    · have hz' : z = q.finish := by simpa only [start_reverse, Set.mem_singleton_iff] using hz
      rw [hz', ← q.point_last_eq_finish]
      exact q.point_mem_image (by have := List.length_pos_iff.mpr q.nonempty; omega)
    · have hi' : i + 1 < q.points.length := by simpa [reverse] using hi
      rw [segmentAt_reverse_transfer q hi'] at hz
      exact q.segmentAt_subset_image (by omega) hz
  exact Set.Subset.antisymm (hsub p) (by simpa only [reverse_reverse] using hsub p.reverse)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem interior_reverse_transfer (p : Polyline) : p.reverse.interior = p.interior := by
  simp only [interior, image_reverse_transfer, start_reverse, finish_reverse,
    Set.pair_comm]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem isSimple_reverse_transfer (p : Polyline) (hp : p.IsSimple) : p.reverse.IsSimple := by
  have hlen : p.reverse.points.length = p.points.length := List.length_reverse
  refine ⟨?_, ?_, ?_⟩
  · intro i hi he
    rw [hlen] at hi
    rw [point_reverse_transfer p (by omega), point_reverse_transfer p hi] at he
    have h0 : p.points.length - 1 - i = p.points.length - 2 - i + 1 := by omega
    have h1 : p.points.length - 1 - (i + 1) = p.points.length - 2 - i := by omega
    rw [h0, h1] at he
    exact hp.1 _ (by omega) he.symm
  · intro i hi
    rw [hlen] at hi
    rw [segmentAt_reverse_transfer p (by omega),
      segmentAt_reverse_transfer p (by omega), point_reverse_transfer p (by omega)]
    have h0 : p.points.length - 2 - i = p.points.length - 2 - (i + 1) + 1 := by omega
    have h1 : p.points.length - 1 - (i + 1) =
        p.points.length - 2 - (i + 1) + 1 := by omega
    rw [h0, h1, Set.inter_comm]
    exact hp.2.1 _ (by omega)
  · intro i j hi hj hij
    rw [hlen] at hi hj
    rw [segmentAt_reverse_transfer p hi, segmentAt_reverse_transfer p hj]
    exact (hp.2.2 _ _ (by omega) (by omega) (by omega)).symm

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem length_two_of_start_ne_finish (p : Polyline) (h : p.start ≠ p.finish) :
    2 ≤ p.points.length := by
  cases hp : p.points with
  | nil => exact (p.nonempty hp).elim
  | cons a l =>
    cases l with
    | nil => exact (h (by simp [start, finish, hp])).elim
    | cons b l => simp

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
def transferCuts (p : Polyline) (cuts : Set ℝ)
    (hfin : ∀ s t, (cuts ∩ Set.Icc s t).Finite) : Finset ℝ :=
  (hfin p.start.re p.finish.re).toFinset

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
def transferIncreasing (T : ℂ ≃ₜ ℂ) (cuts : Set ℝ)
    (hfin : ∀ s t, (cuts ∩ Set.Icc s t).Finite) (p : Polyline) : Polyline :=
  mapPoints T (subdivideAt p (transferCuts p cuts hfin))

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. Endpoint order fixes the orientation. -/
def transferArc (T : ℂ ≃ₜ ℂ) (cuts : Set ℝ)
    (hfin : ∀ s t, (cuts ∩ Set.Icc s t).Finite) (p : Polyline) : Polyline :=
  if p.start.re < p.finish.re then transferIncreasing T cuts hfin p
  else (transferIncreasing T cuts hfin p.reverse).reverse

variable (T : ℂ ≃ₜ ℂ) (cuts : Set ℝ)
variable (hfin : ∀ s t, (cuts ∩ Set.Icc s t).Finite)
variable (haff : ∀ s t : ℝ, s < t → (∀ c ∈ cuts, c ∉ Set.Ioo s t) →
  ∃ m0 m1 c0 c1 : ℝ, 0 < m0 ∧ ∀ z : ℂ, s ≤ z.re → z.re ≤ t →
    T z = ⟨-(m0 * z.re) + c0, -z.im + m1 * z.re + c1⟩)

include haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
private theorem transfer_local_affine (p : Polyline) :
    ∀ s t : ℝ, p.start.re ≤ s → s < t → t ≤ p.finish.re →
      (∀ c ∈ transferCuts p cuts hfin, c ∉ Set.Ioo s t) →
      ∃ A : ℂ →ᵃ[ℝ] ℂ, Set.EqOn T A {z | s ≤ z.re ∧ z.re ≤ t} := by
  intro s t hs hst ht hc
  obtain ⟨m0, m1, c0, c1, _, hm⟩ := haff s t hst (by
    intro c hcc hci
    apply hc c
    · change c ∈ (hfin p.start.re p.finish.re).toFinset
      simpa only [Set.Finite.mem_toFinset] using
        (show c ∈ cuts ∩ Set.Icc p.start.re p.finish.re from
          ⟨hcc, hs.trans hci.1.le, hci.2.le.trans ht⟩)
    · exact hci)
  refine ⟨pastTransferAffine m0 (-c0) 0 0 m1 c1, ?_⟩
  intro z hz
  rw [hm z hz.1 hz.2]
  apply Complex.ext <;> simp [pastTransferAffine] <;> ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem start_transferArc (p : Polyline) :
    (transferArc T cuts hfin p).start = T p.start := by
  unfold transferArc transferIncreasing
  split <;> simp only [start_reverse, finish_mapPoints, finish_subdivideAt,
    finish_reverse, start_mapPoints, start_subdivideAt]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem finish_transferArc (p : Polyline) :
    (transferArc T cuts hfin p).finish = T p.finish := by
  unfold transferArc transferIncreasing
  split <;> simp only [finish_reverse, start_mapPoints, start_subdivideAt,
    start_reverse, finish_mapPoints, finish_subdivideAt]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
private theorem endpoint_order (p : Polyline) (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) : p.start.re < p.finish.re := by
  rw [← p.point_zero_eq_start, ← p.point_last_eq_finish]
  exact point_re_lt hp (by omega) (by omega)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
private theorem transfer_orientation (p : Polyline)
    (hp : p.XMonotone ∨ p.reverse.XMonotone) (hlen : 2 ≤ p.points.length) :
    (p.start.re < p.finish.re ∧ p.XMonotone) ∨
      (p.finish.re < p.start.re ∧ p.reverse.XMonotone) := by
  rcases hp with hp | hp
  · exact Or.inl ⟨endpoint_order p hp hlen, hp⟩
  · refine Or.inr ⟨?_, hp⟩
    simpa only [start_reverse, finish_reverse] using
      endpoint_order p.reverse hp (by simpa [reverse] using hlen)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem initialDirection_subdivideAt (p : Polyline) (xs : Finset ℝ)
    (hp : p.XMonotone) (hlen : 2 ≤ p.points.length) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      (subdivideAt p xs).initialDirection = (c : ℂ) * p.initialDirection := by
  have hne : p.start ≠ p.finish := by
    intro he
    exact (ne_of_lt (endpoint_order p hp hlen)) (congrArg Complex.re he)
  suffices hh : ∀ (l : List ℝ) (q : Polyline), q.start ≠ q.finish →
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
        (l.foldl subdivideOne q).initialDirection = (c : ℂ) * q.initialDirection by
    exact hh xs.toList p hne
  intro l
  induction l with
  | nil => intro q _; exact ⟨1, zero_lt_one, le_rfl, by simp⟩
  | cons x l ih =>
    intro q hq
    have hs : (subdivideOne q x).start = q.start := rfl
    have hf : (subdivideOne q x).finish = q.finish := by
      have h := finish_subdivideAt q {x}
      simpa [subdivideAt] using h
    obtain ⟨c, hc, hc1, he⟩ := initialDirection_subdivideOne q x
      (length_two_of_start_ne_finish q hq)
    obtain ⟨d, hd, hd1, he'⟩ := ih (subdivideOne q x) (by rwa [hs, hf])
    refine ⟨d * c, mul_pos hd hc, ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_right hd1 hc.le).trans (by simpa using hc1)
    · simp only [List.foldl_cons, he', he, Complex.ofReal_mul, mul_assoc]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem reverse_initialDirection_subdivideAt (p : Polyline) (xs : Finset ℝ)
    (hp : p.XMonotone) (hlen : 2 ≤ p.points.length) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      (subdivideAt p xs).reverse.initialDirection = (c : ℂ) * p.reverse.initialDirection := by
  have hne : p.start ≠ p.finish := by
    intro he
    exact (ne_of_lt (endpoint_order p hp hlen)) (congrArg Complex.re he)
  suffices hh : ∀ (l : List ℝ) (q : Polyline), q.start ≠ q.finish →
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
        (l.foldl subdivideOne q).reverse.initialDirection = (c : ℂ) * q.reverse.initialDirection by
    exact hh xs.toList p hne
  intro l
  induction l with
  | nil => intro q _; exact ⟨1, zero_lt_one, le_rfl, by simp⟩
  | cons x l ih =>
    intro q hq
    have hs : (subdivideOne q x).start = q.start := rfl
    have hf : (subdivideOne q x).finish = q.finish := by
      have h := finish_subdivideAt q {x}
      simpa [subdivideAt] using h
    obtain ⟨c, hc, hc1, he⟩ := reverse_initialDirection_subdivideOne q x
      (length_two_of_start_ne_finish q hq)
    obtain ⟨d, hd, hd1, he'⟩ := ih (subdivideOne q x) (by rwa [hs, hf])
    refine ⟨d * c, mul_pos hd hc, ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_right hd1 hc.le).trans (by simpa using hc1)
    · simp only [List.foldl_cons, he', he, Complex.ofReal_mul, mul_assoc]

include haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
private theorem transfer_segment_formula (p : Polyline) (hp : p.XMonotone) {i : ℕ}
    (hi : i + 1 < (subdivideAt p (transferCuts p cuts hfin)).points.length) :
    ∃ a b c d : ℝ, 0 < a ∧ ∀ z : ℂ,
      ((subdivideAt p (transferCuts p cuts hfin)).point i).re ≤ z.re →
      z.re ≤ ((subdivideAt p (transferCuts p cuts hfin)).point (i + 1)).re →
      T z = ⟨-(a * z.re) + c, -z.im + b * z.re + d⟩ := by
  let xs := transferCuts p cuts hfin
  let q := subdivideAt p xs
  have hiq : i + 1 < q.points.length := hi
  have hqm : q.XMonotone := xMonotone_subdivideAt p xs hp
  apply haff _ _ (point_re_lt hqm (Nat.lt_succ_self i) hi)
  intro c hc hci
  have hlo := (point_re_bounds_subdivideAt p xs hp (by omega :
    i < q.points.length)).1
  have hhi := (point_re_bounds_subdivideAt p xs hp hi).2
  have hmem : c ∈ xs := by
    change c ∈ (hfin p.start.re p.finish.re).toFinset
    simpa only [Set.Finite.mem_toFinset] using
      (show c ∈ cuts ∩ Set.Icc p.start.re p.finish.re from
        ⟨hc, hlo.trans hci.1.le, hci.2.le.trans hhi⟩)
  rcases doesNotCross_subdivideAt p xs hi hmem with h | h
  · exact (not_lt_of_ge h.2) hci.2
  · exact (not_lt_of_ge h.1) hci.1

include hfin haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem transfer_germs (x : ℝ) :
    ∃ r aPos aNeg bPos bNeg cPos cNeg dPos dNeg : ℝ,
      0 < r ∧ 0 < aPos ∧ 0 < aNeg ∧
      (∀ z : ℂ, x ≤ z.re → z.re ≤ x + r →
        T z = ⟨-(aPos * z.re) + cPos, -z.im + bPos * z.re + dPos⟩) ∧
      (∀ z : ℂ, x - r ≤ z.re → z.re ≤ x →
        T z = ⟨-(aNeg * z.re) + cNeg, -z.im + bNeg * z.re + dNeg⟩) := by
  let S := (cuts ∩ Set.Icc (x - 1) (x + 1)) \ {x}
  have hS : S.Finite := (hfin (x - 1) (x + 1)).subset Set.sdiff_subset
  have hx : x ∈ Sᶜ := by simp [S]
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp hS.isClosed.isOpen_compl x hx
  let r := min e 1 / 2
  have hr : 0 < r := half_pos (lt_min he zero_lt_one)
  have hre : r < e := lt_of_lt_of_le (half_lt_self (lt_min he zero_lt_one))
    (min_le_left e 1)
  have hr1 : r < 1 := lt_of_lt_of_le (half_lt_self (lt_min he zero_lt_one))
    (min_le_right e 1)
  have hcut : ∀ c ∈ cuts, c ∉ Set.Ioo (x - r) x ∧ c ∉ Set.Ioo x (x + r) := by
    intro c hc
    have hbad : c ≠ x → x - r < c → c < x + r → False := by
      intro hne hlo hhi
      have hcS : c ∈ S := ⟨⟨hc, by constructor <;> linarith⟩, hne⟩
      apply hball (show c ∈ Metric.ball x e from ?_) hcS
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    constructor
    · intro h
      exact hbad (ne_of_lt h.2) h.1 (by linarith [h.2])
    · intro h
      exact hbad (ne_of_gt h.1) (by linarith [h.1]) h.2
  obtain ⟨ap, bp, cp, dp, hap, hp⟩ := haff x (x + r) (by linarith)
    (fun c hc => (hcut c hc).2)
  obtain ⟨an, bn, cn, dn, han, hn⟩ := haff (x - r) x (by linarith)
    (fun c hc => (hcut c hc).1)
  exact ⟨r, ap, an, bp, bn, cp, cn, dp, dn, hr, hap, han, hp, hn⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
private theorem strip_slopes_unique (F : ℂ → ℂ) (s t a b c d A B C D : ℝ)
    (hst : s < t)
    (h : ∀ z : ℂ, s ≤ z.re → z.re ≤ t →
      F z = ⟨-(a * z.re) + c, -z.im + b * z.re + d⟩)
    (h' : ∀ z : ℂ, s ≤ z.re → z.re ≤ t →
      F z = ⟨-(A * z.re) + C, -z.im + B * z.re + D⟩) : a = A ∧ b = B := by
  have hs := (h ⟨s, 0⟩ le_rfl hst.le).symm.trans (h' ⟨s, 0⟩ le_rfl hst.le)
  have ht := (h ⟨t, 0⟩ hst.le le_rfl).symm.trans (h' ⟨t, 0⟩ hst.le le_rfl)
  have hsr := congrArg Complex.re hs
  have htr := congrArg Complex.re ht
  have hsi := congrArg Complex.im hs
  have hti := congrArg Complex.im ht
  change -(a * s) + c = -(A * s) + C at hsr
  change -(a * t) + c = -(A * t) + C at htr
  change -0 + b * s + d = -0 + B * s + D at hsi
  change -0 + b * t + d = -0 + B * t + D at hti
  constructor
  · apply (mul_right_cancel₀ (sub_ne_zero.mpr hst.ne'))
    nlinarith only [hsr, htr]
  · apply (mul_right_cancel₀ (sub_ne_zero.mpr hst.ne'))
    nlinarith only [hsi, hti]

include haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
private theorem reverse_initialDirection_transferIncreasing (p : Polyline) (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) (r a b c0 c1 : ℝ) (hr : 0 < r)
    (hg : ∀ z : ℂ, p.finish.re - r ≤ z.re → z.re ≤ p.finish.re →
      T z = ⟨-(a * z.re) + c0, -z.im + b * z.re + c1⟩) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      (transferIncreasing T cuts hfin p).reverse.initialDirection =
        (c : ℂ) * ⟨-a * p.reverse.initialDirection.re,
          -p.reverse.initialDirection.im + b * p.reverse.initialDirection.re⟩ := by
  let xs := transferCuts p cuts hfin
  let q := subdivideAt p xs
  have hqm := xMonotone_subdivideAt p xs hp
  have hqs : q.start = p.start := start_subdivideAt p xs
  have hqf : q.finish = p.finish := finish_subdivideAt p xs
  have hql : 2 ≤ q.points.length := length_two_of_start_ne_finish q (by
    rw [hqs, hqf]
    exact fun he => (ne_of_lt (endpoint_order p hp hlen)) (congrArg Complex.re he))
  have hq0 : q.point (q.points.length - 1) = p.finish :=
    q.point_last_eq_finish.trans hqf
  let i := q.points.length - 2
  have hi : i + 1 < q.points.length := by dsimp [i]; omega
  have hi1 : i + 1 = q.points.length - 1 := by dsimp [i]; omega
  have hlt : (q.point i).re < p.finish.re := by
    rw [← hq0]
    exact point_re_lt hqm (by dsimp [i]; omega)
      (Nat.sub_lt (by omega : 0 < q.points.length) (by decide : 0 < 1))
  obtain ⟨A, B, C, D, _, hf⟩ := transfer_segment_formula T cuts hfin haff p hp
    (i := i) hi
  change ∀ z : ℂ, (q.point i).re ≤ z.re → z.re ≤ (q.point (i + 1)).re →
    T z = ⟨-(A * z.re) + C, -z.im + B * z.re + D⟩ at hf
  have hmin : max (p.finish.re - r) (q.point i).re < p.finish.re :=
    max_lt (by linarith) hlt
  obtain ⟨hA, hB⟩ := strip_slopes_unique T (max (p.finish.re - r) (q.point i).re)
    p.finish.re A B C D a b c0 c1 hmin
    (fun z hz hz' => hf z ((le_max_right _ _).trans hz)
      (by simpa only [hi1, hq0] using hz'))
    (fun z hz hz' => hg z ((le_max_left _ _).trans hz) hz')
  subst A
  subst B
  obtain ⟨c, hc, hc1, he⟩ := reverse_initialDirection_subdivideAt p xs hp hlen
  refine ⟨c, hc, hc1, ?_⟩
  have hT0 := hf q.finish (by simpa only [hqf] using hlt.le)
    (by simp only [hi1, q.point_last_eq_finish, le_refl])
  have hT1 := hf (q.point i) le_rfl (by simpa only [hi1, hq0] using hlt.le)
  change (mapPoints T q).reverse.initialDirection = _
  rw [← mapPoints_reverse]
  have hpoint : q.reverse.point 1 = q.point i := reverse_point_one q hql
  simp only [initialDirection, point_mapPoints, start_mapPoints, start_reverse,
    hpoint, hT0, hT1]
  have hcr := congrArg Complex.re he
  have hci := congrArg Complex.im he
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero] at hcr hci
  have hqr : q.reverse.initialDirection.re = (q.point i).re - q.finish.re := by
    simp only [initialDirection, start_reverse, reverse_point_one q hql, Complex.sub_re]
    rfl
  have hqi : q.reverse.initialDirection.im = (q.point i).im - q.finish.im := by
    simp only [initialDirection, start_reverse, reverse_point_one q hql, Complex.sub_im]
    rfl
  rw [hqr] at hcr
  rw [hqi] at hci
  simp only [initialDirection, start_reverse, Complex.sub_re, Complex.sub_im] at hcr hci
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  · linear_combination -a * hcr
  · linear_combination -hci + b * hcr

include haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
private theorem initialDirection_transferIncreasing (p : Polyline) (hp : p.XMonotone)
    (hlen : 2 ≤ p.points.length) (r a b c0 c1 : ℝ) (hr : 0 < r)
    (hg : ∀ z : ℂ, p.start.re ≤ z.re → z.re ≤ p.start.re + r →
      T z = ⟨-(a * z.re) + c0, -z.im + b * z.re + c1⟩) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      (transferIncreasing T cuts hfin p).initialDirection =
        (c : ℂ) * ⟨-a * p.initialDirection.re,
          -p.initialDirection.im + b * p.initialDirection.re⟩ := by
  let xs := transferCuts p cuts hfin
  let q := subdivideAt p xs
  have hqm := xMonotone_subdivideAt p xs hp
  have hqs : q.start = p.start := start_subdivideAt p xs
  have hqf : q.finish = p.finish := finish_subdivideAt p xs
  have hql : 2 ≤ q.points.length := length_two_of_start_ne_finish q (by
    rw [hqs, hqf]
    exact fun he => (ne_of_lt (endpoint_order p hp hlen)) (congrArg Complex.re he))
  have hq0 : q.point 0 = p.start := q.point_zero_eq_start.trans hqs
  have hlt : p.start.re < (q.point 1).re := by
    rw [← hq0]
    exact point_re_lt hqm (by decide)
      (Nat.lt_of_lt_of_le (by decide : 1 < 2) hql)
  obtain ⟨A, B, C, D, _, hf⟩ := transfer_segment_formula T cuts hfin haff p hp
    (i := 0) (Nat.lt_of_lt_of_le (by decide : 1 < 2) hql)
  change ∀ z : ℂ, (q.point 0).re ≤ z.re → z.re ≤ (q.point 1).re →
    T z = ⟨-(A * z.re) + C, -z.im + B * z.re + D⟩ at hf
  have hmin : p.start.re < min (p.start.re + r) (q.point 1).re :=
    lt_min (by linarith) hlt
  obtain ⟨hA, hB⟩ := strip_slopes_unique T p.start.re
    (min (p.start.re + r) (q.point 1).re) A B C D a b c0 c1 hmin
    (fun z hz hz' => hf z (by simpa only [hq0] using hz)
      (hz'.trans (min_le_right _ _)))
    (fun z hz hz' => hg z hz (hz'.trans (min_le_left _ _)))
  subst A
  subst B
  obtain ⟨c, hc, hc1, he⟩ := initialDirection_subdivideAt p xs hp hlen
  refine ⟨c, hc, hc1, ?_⟩
  have hT0 := hf q.start (by simp only [q.point_zero_eq_start, le_refl])
    (by simpa only [hqs] using hlt.le)
  have hT1 := hf (q.point 1) (by simpa only [hq0] using hlt.le) le_rfl
  change (mapPoints T q).initialDirection = _
  simp only [initialDirection, point_mapPoints, start_mapPoints, hT0, hT1]
  have hcr := congrArg Complex.re he
  have hci := congrArg Complex.im he
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero] at hcr hci
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  · change -(a * (q.point 1).re) + C - (-(a * q.start.re) + C) =
      c * (-a * p.initialDirection.re)
    change (q.point 1).re - q.start.re = c * p.initialDirection.re at hcr
    linear_combination -a * hcr
  · change -(q.point 1).im + b * (q.point 1).re + D -
      (-q.start.im + b * q.start.re + D) =
      c * (-p.initialDirection.im + b * p.initialDirection.re)
    change (q.point 1).re - q.start.re = c * p.initialDirection.re at hcr
    change (q.point 1).im - q.start.im = c * p.initialDirection.im at hci
    linear_combination -hci + b * hcr

include haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem image_transferArc (p : Polyline) (hp : p.XMonotone ∨ p.reverse.XMonotone)
    (hlen : 2 ≤ p.points.length) : (transferArc T cuts hfin p).image = T '' p.image := by
  rcases transfer_orientation p hp hlen with ⟨h, hp⟩ | ⟨h, hp⟩
  · rw [transferArc, ite_eq_left h]
    exact image_mapPoints_subdivideAt_local T p _ hp
      (transfer_local_affine T cuts hfin haff p)
  · rw [transferArc, ite_eq_right (not_lt_of_gt h), image_reverse_transfer]
    simpa only [image_reverse_transfer, transferIncreasing] using
      image_mapPoints_subdivideAt_local T p.reverse _ hp
        (transfer_local_affine T cuts hfin haff p.reverse)

include haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem interior_transferArc (p : Polyline) (hp : p.XMonotone ∨ p.reverse.XMonotone)
    (hlen : 2 ≤ p.points.length) :
    (transferArc T cuts hfin p).interior = T '' p.interior := by
  rcases transfer_orientation p hp hlen with ⟨h, hp⟩ | ⟨h, hp⟩
  · rw [transferArc, ite_eq_left h]
    exact interior_mapPoints_subdivideAt_local T p _ hp
      (transfer_local_affine T cuts hfin haff p) T.injective.injOn
  · rw [transferArc, ite_eq_right (not_lt_of_gt h), interior_reverse_transfer]
    simpa only [interior_reverse_transfer, transferIncreasing] using
      interior_mapPoints_subdivideAt_local T p.reverse _ hp
        (transfer_local_affine T cuts hfin haff p.reverse) T.injective.injOn

include haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem isSimple_transferArc (p : Polyline) (hp : p.XMonotone ∨ p.reverse.XMonotone)
    (hlen : 2 ≤ p.points.length) : (transferArc T cuts hfin p).IsSimple := by
  rcases transfer_orientation p hp hlen with ⟨h, hp⟩ | ⟨h, hp⟩
  · rw [transferArc, ite_eq_left h]
    exact isSimple_mapPoints_subdivideAt_local T p _ hp
      (transfer_local_affine T cuts hfin haff p) T.injective.injOn
  · rw [transferArc, ite_eq_right (not_lt_of_gt h)]
    exact isSimple_reverse_transfer _ (isSimple_mapPoints_subdivideAt_local T p.reverse
      _ hp (transfer_local_affine T cuts hfin haff p.reverse) T.injective.injOn)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem length_transferArc (p : Polyline) (hp : p.XMonotone ∨ p.reverse.XMonotone)
    (hlen : 2 ≤ p.points.length) : 2 ≤ (transferArc T cuts hfin p).points.length := by
  apply length_two_of_start_ne_finish
  rw [start_transferArc, finish_transferArc]
  intro he
  have he' := congrArg Complex.re (T.injective he)
  rcases transfer_orientation p hp hlen with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem reverse_transferArc (p : Polyline) (hp : p.XMonotone ∨ p.reverse.XMonotone)
    (hlen : 2 ≤ p.points.length) :
    transferArc T cuts hfin p.reverse = (transferArc T cuts hfin p).reverse := by
  rcases transfer_orientation p hp hlen with ⟨h, _⟩ | ⟨h, _⟩
  · simp only [transferArc, start_reverse, finish_reverse, ite_eq_left h,
      ite_eq_right (not_lt_of_gt h), reverse_reverse]
  · simp only [transferArc, start_reverse, finish_reverse, ite_eq_left h,
      ite_eq_right (not_lt_of_gt h), reverse_reverse]

end Polyline

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
variable (P : PLDrawing D V flip rot vert)
variable (hmono : ∀ d, (P.arc d).XMonotone ∨ (P.arc d).reverse.XMonotone)
variable (T : ℂ ≃ₜ ℂ) (cuts : Set ℝ)
variable (hfin : ∀ s t, (cuts ∩ Set.Icc s t).Finite)
variable (haff : ∀ s t : ℝ, s < t → (∀ c ∈ cuts, c ∉ Set.Ioo s t) →
  ∃ m0 m1 c0 c1 : ℝ, 0 < m0 ∧ ∀ z : ℂ, s ≤ z.re → z.re ≤ t →
    T z = ⟨-(m0 * z.re) + c0, -z.im + m1 * z.re + c1⟩)

include hmono haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. The same slopes serve the entire star. -/
theorem transferArc_initialDirections (v : V) :
    ∃ aPos aNeg bPos bNeg : ℝ, 0 < aPos ∧ 0 < aNeg ∧
      ∀ d, vert d = v → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
        (Polyline.transferArc T cuts hfin (P.arc d)).initialDirection =
          (c : ℂ) * pastDirection aPos aNeg bPos bNeg (P.arc d).initialDirection := by
  obtain ⟨r, ap, an, bp, bn, cp, cn, dp, dn, hr, hap, han, hp, hn⟩ :=
    Polyline.transfer_germs T cuts hfin haff (P.pos v).re
  refine ⟨ap, an, bp, bn, hap, han, ?_⟩
  intro d hv
  have hs : (P.arc d).start = P.pos v := (P.arc_start d).trans (congrArg P.pos hv)
  rcases Polyline.transfer_orientation (P.arc d) (hmono d) (P.arc_length d) with
    ⟨ho, hm⟩ | ⟨ho, hm⟩
  · obtain ⟨c, hc, hc1, he⟩ := Polyline.initialDirection_transferIncreasing T cuts hfin
      haff (P.arc d) hm (P.arc_length d) r ap bp cp dp hr (by simpa only [hs] using hp)
    refine ⟨c, hc, hc1, ?_⟩
    rw [Polyline.transferArc, ite_eq_left ho, he]
    rw [pastDirection, ite_eq_left (Polyline.initialDirection_re_pos hm (P.arc_length d))]
  · have hl : 2 ≤ (P.arc d).reverse.points.length := by
      simpa [Polyline.reverse] using P.arc_length d
    obtain ⟨c, hc, hc1, he⟩ := Polyline.reverse_initialDirection_transferIncreasing T cuts
      hfin haff (P.arc d).reverse hm hl r an bn cn dn hr (by
        simpa only [Polyline.finish_reverse, hs] using hn)
    refine ⟨c, hc, hc1, ?_⟩
    have hneg : (P.arc d).initialDirection.re < 0 := by
      simpa only [Polyline.reverse_reverse] using
        Polyline.reverse_initialDirection_re_neg hm hl
    rw [Polyline.transferArc, ite_eq_right (not_lt_of_gt ho), he]
    simp only [Polyline.reverse_reverse, pastDirection, ite_eq_right (not_lt_of_gt hneg)]

include hmono in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem transferArc_flip (d : D) :
    Polyline.transferArc T cuts hfin (P.arc (flip d)) =
      (Polyline.transferArc T cuts hfin (P.arc d)).reverse := by
  rw [P.arc_flip]
  exact Polyline.reverse_transferArc T cuts hfin (P.arc d) (hmono d) (P.arc_length d)

include hmono in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
private theorem initialDirection_re_ne_zero (d : D) : (P.arc d).initialDirection.re ≠ 0 := by
  rcases hmono d with hm | hm
  · exact ne_of_gt (Polyline.initialDirection_re_pos hm (P.arc_length d))
  · have hl : 2 ≤ (P.arc d).reverse.points.length := by
      simpa [Polyline.reverse] using P.arc_length d
    have hh := Polyline.reverse_initialDirection_re_neg hm hl
    simpa only [Polyline.reverse_reverse] using ne_of_lt hh

include hmono haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem transferArc_initial_arg_injective (d e : D) (hv : vert d = vert e)
    (harg : Complex.arg (Polyline.transferArc T cuts hfin (P.arc d)).initialDirection =
      Complex.arg (Polyline.transferArc T cuts hfin (P.arc e)).initialDirection) : d = e := by
  obtain ⟨ap, an, bp, bn, hap, han, hh⟩ :=
    transferArc_initialDirections P hmono T cuts hfin haff (vert d)
  obtain ⟨cd, hcd, _, hd⟩ := hh d rfl
  obtain ⟨ce, hce, _, he⟩ := hh e hv.symm
  rw [hd, he, Complex.arg_real_mul _ hcd, Complex.arg_real_mul _ hce] at harg
  have hle := (pastDirection_turn_le_iff ap an bp bn hap han
    (initialDirection_re_ne_zero P hmono d) (initialDirection_re_ne_zero P hmono d)
    (initialDirection_re_ne_zero P hmono e)).mp (by
      simp only [ccwTurn, harg, lt_self_iff_false, ite_false, sub_self, zero_add, le_refl])
  have hself : ccwTurn (P.arc d).initialDirection (P.arc d).initialDirection =
      2 * Real.pi := by simp [ccwTurn]
  rw [hself] at hle
  exact P.initial_arg_injective d e hv ((ccwTurn_eq_two_pi_iff _ _).mp
    (le_antisymm (ccwTurn_le_two_pi _ _) hle))

include hmono haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem transferArc_rotation_agreement (d : D) :
    CcwSuccessor {e | vert e = vert d}
      (fun e => (Polyline.transferArc T cuts hfin (P.arc e)).initialDirection) d (rot d) := by
  obtain ⟨ap, an, bp, bn, hap, han, hh⟩ :=
    transferArc_initialDirections P hmono T cuts hfin haff (vert d)
  obtain ⟨hfinite, hd, he, hs⟩ := P.rotation_agreement d
  refine ⟨hfinite, hd, he, ?_⟩
  rcases hs with hs | ⟨hne, hmin⟩
  · exact Or.inl hs
  · refine Or.inr ⟨hne, ?_⟩
    intro f hf hfd
    obtain ⟨cd, hcd, _, hdirD⟩ := hh d rfl
    obtain ⟨ce, hce, _, hdirE⟩ := hh (rot d) (P.vert_rotation d)
    obtain ⟨cf, hcf, _, hdirF⟩ := hh f hf
    dsimp only
    rw [hdirD, hdirE, hdirF, ccwTurn_smul_pos _ _ _ _ hcd hce,
      ccwTurn_smul_pos _ _ _ _ hcd hcf]
    exact (pastDirection_turn_le_iff ap an bp bn hap han
      (initialDirection_re_ne_zero P hmono d)
      (initialDirection_re_ne_zero P hmono (rot d))
      (initialDirection_re_ne_zero P hmono f)).mpr (hmin f hf hfd)

include hmono haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem transferArc_interior_disjoint (d e : D) (he : e ≠ d) (hf : e ≠ flip d) :
    Disjoint (Polyline.transferArc T cuts hfin (P.arc d)).interior
      (Polyline.transferArc T cuts hfin (P.arc e)).interior := by
  rw [Polyline.interior_transferArc T cuts hfin haff _ (hmono d) (P.arc_length d),
    Polyline.interior_transferArc T cuts hfin haff _ (hmono e) (P.arc_length e)]
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  have hyx' := T.injective hyx
  subst y
  exact Set.disjoint_left.mp (P.interior_disjoint d e he hf) hx hy

include hmono haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem transferArc_interior_avoids_vertices (d : D) (v : V) :
    T (P.pos v) ∉ (Polyline.transferArc T cuts hfin (P.arc d)).interior := by
  rw [Polyline.interior_transferArc T cuts hfin haff _ (hmono d) (P.arc_length d)]
  rintro ⟨x, hx, he⟩
  have he' := T.injective he
  exact P.interior_avoids_vertices d v (he' ▸ hx)

include hmono haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem transferArc_locally_finite (K : Set ℂ) (hK : Bornology.IsBounded K) :
    {d | (K ∩ (Polyline.transferArc T cuts hfin (P.arc d)).image).Nonempty}.Finite := by
  have hb : Bornology.IsBounded (T.symm '' closure K) :=
    (hK.isCompact_closure.image T.symm.continuous).isBounded
  apply (P.locally_finite (T.symm '' closure K) hb).subset
  intro d hd
  obtain ⟨z, hzK, hz⟩ := hd
  rw [Polyline.image_transferArc T cuts hfin haff _ (hmono d) (P.arc_length d)] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  exact ⟨x, ⟨T x, subset_closure hzK, T.symm_apply_apply x⟩, hx⟩

include hmono haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem transferArc_initial_nonzero (d : D) :
    (Polyline.transferArc T cuts hfin (P.arc d)).initialDirection ≠ 0 := by
  let q := Polyline.transferArc T cuts hfin (P.arc d)
  have hs : q.IsSimple :=
    Polyline.isSimple_transferArc T cuts hfin haff _ (hmono d) (P.arc_length d)
  have hl : 2 ≤ q.points.length :=
    Polyline.length_transferArc T cuts hfin _ (hmono d) (P.arc_length d)
  intro hz
  apply hs.1 0 (by omega)
  rw [Polyline.point_zero_eq_start]
  exact (sub_eq_zero.mp hz).symm

include hmono hfin haff in
/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: transport of a PL drawing by the
piecewise-affine past transfer); not a paper result. -/
theorem transfer : ∃ P' : PLDrawing D V flip rot vert,
    P'.pos = T ∘ P.pos ∧ ∀ d,
      (P'.arc d).image = T '' (P.arc d).image ∧
      (P'.arc d).interior = T '' (P.arc d).interior := by
  let P' : PLDrawing D V flip rot vert := {
    flip_involutive := P.flip_involutive
    flip_ne := P.flip_ne
    vert_rotation := P.vert_rotation
    pos := T ∘ P.pos
    pos_injective := T.injective.comp P.pos_injective
    arc := fun d => Polyline.transferArc T cuts hfin (P.arc d)
    arc_simple := fun d => Polyline.isSimple_transferArc T cuts hfin haff _
      (hmono d) (P.arc_length d)
    arc_length := fun d => Polyline.length_transferArc T cuts hfin _
      (hmono d) (P.arc_length d)
    arc_start := fun d => (Polyline.start_transferArc T cuts hfin (P.arc d)).trans
      (congrArg T (P.arc_start d))
    arc_finish := fun d => (Polyline.finish_transferArc T cuts hfin (P.arc d)).trans
      (congrArg T (P.arc_finish d))
    arc_flip := transferArc_flip P hmono T cuts hfin
    interior_disjoint := transferArc_interior_disjoint P hmono T cuts hfin haff
    interior_avoids_vertices := transferArc_interior_avoids_vertices P hmono T cuts hfin haff
    locally_finite := transferArc_locally_finite P hmono T cuts hfin haff
    initial_nonzero := transferArc_initial_nonzero P hmono T cuts hfin haff
    initial_arg_injective := transferArc_initial_arg_injective P hmono T cuts hfin haff
    rotation_agreement := transferArc_rotation_agreement P hmono T cuts hfin haff }
  exact ⟨P', rfl, fun d =>
    ⟨Polyline.image_transferArc T cuts hfin haff _ (hmono d) (P.arc_length d),
      Polyline.interior_transferArc T cuts hfin haff _ (hmono d) (P.arc_length d)⟩⟩

end PLDrawing
end
end DirectedDistances.PlanarMap
