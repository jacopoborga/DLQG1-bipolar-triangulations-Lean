module

public import DirectedDistances.Probability.SkorokhodJ1LocalLawCriterionMain
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Uniform local J1 tail bounds and finite-window law convergence -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter MeasureTheory
open scoped Topology NNReal

/-- Helper toward Theorem 1.6; not a paper result. -/
noncomputable def localJ1TailBound (N : ℕ) : ℝ :=
  2 - ∑ n ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ n

/-- Helper toward Theorem 1.6; not a paper result. -/
theorem localJ1TailBound_nonneg (N : ℕ) : 0 ≤ localJ1TailBound N := by
  exact sub_nonneg.mpr (sum_geometric_two_le (N + 1))

/-- Helper toward Theorem 1.6; not a paper result. -/
theorem tendsto_localJ1TailBound : Tendsto localJ1TailBound atTop (𝓝 0) := by
  have h := hasSum_geometric_two.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun N => 2 - ∑ n ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ n)
    atTop (𝓝 0)
  simpa only [Function.comp_apply, sub_self] using (tendsto_const_nhds (x := (2 : ℝ))).sub h

private theorem term_le_geometric (n : ℕ) (x y : CadlagLocal) :
    localJ1Term n x y ≤ (1 / 2 : ℝ) ^ n := by
  unfold localJ1Term
  calc
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) * 1 :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    _ ≤ (1 / 2 : ℝ) ^ n := by
      rw [pow_succ, mul_one]
      exact mul_le_of_le_one_right (by positivity) (by norm_num)

/-- Helper toward Theorem 1.6; not a paper result. -/
theorem localJ1Tail_le_bound (N : ℕ) (x y : CadlagLocal) :
    (∑' n : {k : ℕ // k ∉ Finset.range (N + 1)}, localJ1Term n.val x y) ≤
      localJ1TailBound N := by
  have hsum :
      (∑ n ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ n) +
        (∑' n : {k : ℕ // k ∉ Finset.range (N + 1)}, (1 / 2 : ℝ) ^ n.val) = 2 := by
    exact summable_geometric_two.sum_add_tsum_compl
      (s := Finset.range (N + 1)) |>.trans tsum_geometric_two
  have hle :
      (∑' n : {k : ℕ // k ∉ Finset.range (N + 1)}, localJ1Term n.val x y) ≤
        ∑' n : {k : ℕ // k ∉ Finset.range (N + 1)}, (1 / 2 : ℝ) ^ n.val := by
    have hlocal : Summable
        (fun n : {k : ℕ // k ∉ Finset.range (N + 1)} => localJ1Term n.val x y) :=
      (localJ1Term_summable x y).subtype _
    have hgeo : Summable
        (fun n : {k : ℕ // k ∉ Finset.range (N + 1)} => (1 / 2 : ℝ) ^ n.val) :=
      summable_geometric_two.subtype _
    exact hlocal.tsum_le_tsum (fun n => term_le_geometric n.val x y) hgeo
  change _ ≤ 2 - ∑ n ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ n
  linarith only [hsum, hle]

/-- Helper toward Theorem 1.6; not a paper result.
Finite-window distance approximates the local metric uniformly; -/
theorem dist_le_finiteCutoffWindowTruncDist_add_bound (N : ℕ) (x y : CadlagLocal) :
    dist x y ≤ finiteCutoffWindowTruncDist (finiteCutoffWindows N x)
      (finiteCutoffWindows N y) + localJ1TailBound N := by
  exact (j1LocalDist_le_finiteCutoffWindowTruncDist_add_tail N x y).trans
    (add_le_add_right (localJ1Tail_le_bound N x y) _)

/-- Helper toward Theorem 1.6; not a paper result. -/
@[instance_reducible] noncomputable instance j1LocalTopologicalSpace :
    TopologicalSpace CadlagLocal :=
  j1LocalMetricSpace.toUniformSpace.toTopologicalSpace

/-- Helper toward Theorem 1.6; not a paper result. -/
@[instance_reducible] noncomputable instance j1LocalMeasurableSpace :
    MeasurableSpace CadlagLocal := borel CadlagLocal

/-- Helper toward Theorem 1.6; not a paper result. -/
instance j1LocalBorelSpace : BorelSpace CadlagLocal := ⟨rfl⟩

/-- Helper toward Theorem 1.6; not a paper result. -/
theorem finiteCutoffWindows_measurable (N : ℕ) : Measurable (finiteCutoffWindows N) := by
  exact (finiteCutoffWindows_continuous N).measurable

/-- Helper toward Theorem 1.6; not a paper result.
Bounded Lipschitz tests admit uniform finite-window approximations; -/
theorem exists_bounded_lipschitz_finiteCutoffWindows_approximation
    (f : CadlagLocal → ℝ) (L : ℝ≥0) (B : ℝ)
    (hfBound : ∀ x, |f x| ≤ B) (hfLip : LipschitzWith L f) (N : ℕ) :
    ∃ g : LocalCutoffTuple N → ℝ, LipschitzWith L g ∧
      (∀ y, |g y| ≤ B + L) ∧
      ∀ x, |f x - g (finiteCutoffWindows N x)| ≤ L * localJ1TailBound N := by
  have : Nonempty CadlagLocal := ⟨⟨fun _ => 0, IsCadlag.const⟩⟩
  simpa only [Real.toNNReal_coe] using
    exists_bounded_lipschitz_finite_map_approximation f (finiteCutoffWindows N)
      finiteCutoffWindowTruncDist (L : ℝ) (localJ1TailBound N) B L.coe_nonneg
      (localJ1TailBound_nonneg N) hfBound hfLip.le_add_mul
      finiteCutoffWindowTruncDist_nonneg finiteCutoffWindowTruncDist_self
      finiteCutoffWindowTruncDist_triangle finiteCutoffWindowTruncDist_le_dist
      finiteCutoffWindowTruncDist_le_one (dist_le_finiteCutoffWindowTruncDist_add_bound N)

/-- Helper toward Theorem 1.6; not a paper result.
Convergence of every finite cutoff-window law implies local J1 law convergence; -/
theorem tendsto_of_tendsto_finiteCutoffWindows
    (μn : ℕ → ProbabilityMeasure CadlagLocal) (μ : ProbabilityMeasure CadlagLocal)
    (hfinite : ∀ N, Tendsto (fun k => (μn k).map (finiteCutoffWindows N)) atTop
      (𝓝 (μ.map (finiteCutoffWindows N)))) : Tendsto μn atTop (𝓝 μ) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro f hfBound ⟨L, hfLip⟩
  let fb : BoundedContinuousFunction CadlagLocal ℝ :=
    { toFun := f
      continuous_toFun := hfLip.continuous
      map_bounded' := hfBound }
  have hfB (x : CadlagLocal) : |f x| ≤ ‖fb‖ := fb.norm_coe_le_norm x
  have hfInt (p : ProbabilityMeasure CadlagLocal) : Integrable f (p : Measure CadlagLocal) :=
    (integrable_const ‖fb‖).mono' hfLip.continuous.aestronglyMeasurable
      (Eventually.of_forall hfB)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ht : Tendsto (fun N => (L : ℝ) * localJ1TailBound N) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := (L : ℝ))).mul tendsto_localJ1TailBound
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ht.eventually_lt_const (show (0 : ℝ) < ε / 3 by positivity))
  have hsmall := hN N le_rfl
  obtain ⟨g, hgLip, hgBound, hgApprox⟩ :=
    exists_bounded_lipschitz_finiteCutoffWindows_approximation f L ‖fb‖ hfB hfLip N
  let gb : BoundedContinuousFunction (LocalCutoffTuple N) ℝ :=
    { toFun := g
      continuous_toFun := hgLip.continuous
      map_bounded' := by
        refine ⟨2 * (‖fb‖ + L), fun x y => ?_⟩
        rw [Real.dist_eq]
        calc
          |g x - g y| ≤ |g x| + |g y| := abs_sub _ _
          _ ≤ 2 * (‖fb‖ + L) := by linarith only [hgBound x, hgBound y] }
  have hgInt (p : ProbabilityMeasure CadlagLocal) :
      Integrable (fun x => g (finiteCutoffWindows N x)) (p : Measure CadlagLocal) :=
    (integrable_const (‖fb‖ + (L : ℝ))).mono'
      (hgLip.continuous.comp (finiteCutoffWindows_continuous N)).aestronglyMeasurable
      (Eventually.of_forall fun x => hgBound _)
  have herr (p : ProbabilityMeasure CadlagLocal) :
      dist (∫ x, f x ∂(p : Measure CadlagLocal))
        (∫ x, g (finiteCutoffWindows N x) ∂(p : Measure CadlagLocal)) ≤
          L * localJ1TailBound N := by
    rw [Real.dist_eq, ← integral_sub (hfInt p) (hgInt p)]
    have h := norm_integral_le_of_norm_le_const
      (μ := (p : Measure CadlagLocal))
      (f := fun x => f x - g (finiteCutoffWindows N x))
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hgApprox x)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  have hmap (p : ProbabilityMeasure CadlagLocal) :
      (∫ y, gb y ∂(p.map (finiteCutoffWindows N) : Measure (LocalCutoffTuple N))) =
        ∫ x, g (finiteCutoffWindows N x) ∂(p : Measure CadlagLocal) := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact integral_map_of_stronglyMeasurable (finiteCutoffWindows_measurable N)
      gb.continuous.stronglyMeasurable
  have hc := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (hfinite N) gb
  simp only [hmap] at hc
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hc (ε / 3) (by positivity)
  refine ⟨M, fun k hk => ?_⟩
  have hmiddle := hM k hk
  have hfirst := herr (μn k)
  have hlast := herr μ
  have htri := dist_triangle4
    (∫ x, f x ∂(μn k : Measure CadlagLocal))
    (∫ x, g (finiteCutoffWindows N x) ∂(μn k : Measure CadlagLocal))
    (∫ x, g (finiteCutoffWindows N x) ∂(μ : Measure CadlagLocal))
    (∫ x, f x ∂(μ : Measure CadlagLocal))
  rw [dist_comm (∫ x, g (finiteCutoffWindows N x) ∂(μ : Measure CadlagLocal))] at htri
  linarith only [htri, hfirst, hmiddle, hlast, hsmall]

end DirectedDistances.Probability
