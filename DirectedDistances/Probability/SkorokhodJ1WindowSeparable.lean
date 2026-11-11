module

public import DirectedDistances.Probability.SkorokhodJ1WindowMetric
public import DirectedDistances.Probability.SkorokhodModulus

import Mathlib.Topology.Bases









@[expose] public section
namespace DirectedDistances.Probability

/-- The path equal to `0` before `q` and `c` at or after `q`, restricted to the window. -/
noncomputable def thresholdStep {T : ℝ} (q c : ℝ) : J1Window T → ℝ :=
  fun t => if q ≤ (t : ℝ) then c else 0

/-- A threshold step path is càdlàg on the window. -/
theorem thresholdStep_isCadlag {T : ℝ} (q c : ℝ) :
    IsCadlag (thresholdStep (T := T) q c) := by
  constructor
  · intro x
    by_cases hx : q ≤ (x : ℝ)
    · apply (Metric.continuousWithinAt_iff).2
      intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      intro y hy _
      have hxy : (x : ℝ) < (y : ℝ) := Subtype.coe_lt_coe.mpr hy
      have hyq : q ≤ (y : ℝ) := hx.trans (le_of_lt hxy)
      simpa [thresholdStep, hx, hyq] using hε
    · have hxq : (x : ℝ) < q := lt_of_not_ge hx
      apply (Metric.continuousWithinAt_iff).2
      intro ε hε
      refine ⟨q - (x : ℝ), sub_pos.mpr hxq, ?_⟩
      intro y hy hdist
      have hdist' : |(y : ℝ) - (x : ℝ)| < q - (x : ℝ) := by
        simpa [Subtype.dist_eq, Real.dist_eq] using hdist
      have hyq : (y : ℝ) < q := by
        rcases abs_lt.mp hdist' with ⟨_, hhi⟩
        have hxy : (x : ℝ) < (y : ℝ) := Subtype.coe_lt_coe.mpr hy
        linarith
      simpa [thresholdStep, hx, not_le_of_gt hyq] using hε
  · intro x
    by_cases hx : q < (x : ℝ)
    · refine ⟨c, ?_⟩
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      refine ⟨(x : ℝ) - q, sub_pos.mpr hx, ?_⟩
      intro y hy hdist
      have hdist' : |(y : ℝ) - (x : ℝ)| < (x : ℝ) - q := by
        simpa [Subtype.dist_eq, Real.dist_eq] using hdist
      have hyq : q < (y : ℝ) := by
        rcases abs_lt.mp hdist' with ⟨hlo, _⟩
        have hyx : (y : ℝ) < (x : ℝ) := Subtype.coe_lt_coe.mpr hy
        linarith
      simpa [thresholdStep, le_of_lt hyq] using hε
    · refine ⟨0, ?_⟩
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      intro y hy _
      have hxq : (x : ℝ) ≤ q := le_of_not_gt hx
      have hyx : (y : ℝ) < (x : ℝ) := Subtype.coe_lt_coe.mpr hy
      have hyq : (y : ℝ) < q := lt_of_lt_of_le hyx hxq
      simpa [thresholdStep, not_le_of_gt hyq, hx] using hε

/-- A finite sum of rational-time jumps, with its right-continuous convention. -/
noncomputable def rationalJumpSum {T : ℝ} (jumps : List (ℚ × ℚ))
    (t : J1Window T) : ℝ :=
  jumps.foldr
    (fun d acc => thresholdStep (d.1 : ℝ) (d.2 : ℝ) t + acc) 0

/-- A finite rational jump sum is càdlàg on the window. -/
theorem rationalJumpSum_isCadlag {T : ℝ} (jumps : List (ℚ × ℚ)) :
    IsCadlag (rationalJumpSum (T := T) jumps) := by
  induction jumps with
  | nil =>
    change IsCadlag (fun _ : J1Window T => (0 : ℝ))
    exact IsCadlag.const
  | cons d ds ih =>
    change IsCadlag (fun t : J1Window T =>
      thresholdStep (d.1 : ℝ) (d.2 : ℝ) t + rationalJumpSum ds t)
    exact (thresholdStep_isCadlag _ _).continuous_comp₂ ih continuous_add

/-- A finite rational-time step path. The list gives rational jump times and
rational jump sizes; `terminal` is the value at `T` when all listed times lie
in `[0,T)`. -/
noncomputable def rationalStepPath {T : ℝ} (_hT : 0 < T) (initial : ℚ)
    (jumps : List (ℚ × ℚ)) (terminal : ℚ) : CadlagWindow T := by
  let correction : ℝ :=
    (terminal : ℝ) - ((initial : ℝ) + (jumps.map fun d => (d.2 : ℝ)).sum)
  refine ⟨fun t => (initial : ℝ) + rationalJumpSum jumps t +
    thresholdStep T correction t, ?_⟩
  have hsum : IsCadlag (fun t : J1Window T =>
      (initial : ℝ) + rationalJumpSum jumps t) :=
    (IsCadlag.const (c := (initial : ℝ))).continuous_comp₂
      (rationalJumpSum_isCadlag jumps) continuous_add
  exact hsum.continuous_comp₂ (thresholdStep_isCadlag T correction) continuous_add

/-- A constant path is approximated by a rational constant step path. -/
theorem exists_rationalStepPath_close_const {T : ℝ} (hT : 0 < T) (c : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℚ,
      j1WindowDist hT ⟨fun _ : J1Window T => c, IsCadlag.const⟩
        (rationalStepPath hT r [] r) < ε := by
  obtain ⟨r, hr⟩ := exists_rat_near c hε
  let : Nonempty (J1Window T) := ⟨⟨0, ⟨le_rfl, hT.le⟩⟩⟩
  have hsup :
      (⨆ t : J1Window T, |c - (rationalStepPath hT r [] r).1 t|) =
        |c - (r : ℝ)| := by
    simp [rationalStepPath, rationalJumpSum, thresholdStep]
  refine ⟨r, ?_⟩
  calc
    j1WindowDist hT ⟨fun _ : J1Window T => c, IsCadlag.const⟩
        (rationalStepPath hT r [] r) ≤
      ⨆ t : J1Window T,
        |c - (rationalStepPath hT r [] r).1 t| :=
      j1WindowDist_le_sup_dist hT _ _
    _ = |c - (r : ℝ)| := hsup
    _ < ε := hr

/-- Rational step paths with finitely many rational jumps form a countable
family. -/
theorem rationalStepPath_range_countable {T : ℝ} (hT : 0 < T) :
    (Set.range fun p : ℚ × (List (ℚ × ℚ) × ℚ) =>
      rationalStepPath hT p.1 p.2.1 p.2.2).Countable :=
  Set.countable_range _

end DirectedDistances.Probability
