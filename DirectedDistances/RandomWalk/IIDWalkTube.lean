module

public import DirectedDistances.RandomWalk.IIDWalkEndpointCLT

/-! # Tube helpers for the iid code walk

Helpers for the uniform block mass in `lem-walk-bdy-sum`

The eventual tube mass theorem is not established in this module. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- A fixed-radius endpoint window has uniformly positive eventual mass over
any compact set of centers and every block starting time. This supplies the
compact recentering input to the block bound in `lem-walk-bdy-sum` -/
theorem iidCodeWalk_endpoint_compact_lower_bound
    (C : Set (ℝ × ℝ)) (hC : IsCompact C) (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ s : ℕ,
      ∀ z ∈ C, c ≤ iidCodeMeasure.real {ω | (Real.sqrt (m : ℝ))⁻¹ •
        (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
         ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈ Metric.ball z r} := by
  classical
  have hrhalf : 0 < r / 2 := half_pos hr
  have hpoint (x : ℝ × ℝ) := iidCodeWalk_endpoint_open_lower_bound
    (Metric.ball x (r / 2)) Metric.isOpen_ball ⟨x, Metric.mem_ball_self hrhalf⟩
  choose c hc m₀ hmass using hpoint
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x => Metric.ball x (r / 2))
    (fun _ => Metric.isOpen_ball)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self hrhalf⟩)
  -- Including one center also handles the empty compact set without a separate case.
  let t' : Finset (ℝ × ℝ) := insert (0, 0) t
  have ht' : t'.Nonempty := Finset.insert_nonempty _ _
  refine ⟨t'.inf' ht' c, (Finset.lt_inf'_iff ht').mpr (fun x _ => hc x),
    t'.sup m₀, ?_⟩
  intro m hm s z hz
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (ht hz)
  obtain ⟨hxt, hzx⟩ := Set.mem_iUnion.mp hx
  have hxt' : x ∈ t' := Finset.mem_insert_of_mem hxt
  have hm' : m₀ x ≤ m := (Finset.le_sup (f := m₀) hxt').trans hm
  have hballs : Metric.ball x (r / 2) ⊆ Metric.ball z r := by
    apply Metric.ball_subset_ball'
    have hzdist : dist x z < r / 2 := by
      simpa only [Metric.mem_ball, dist_comm] using hzx
    linarith only [hzdist]
  exact (Finset.inf'_le c hxt').trans
    ((hmass x m hm' s).trans (measureReal_mono (fun _ hω => hballs hω)))

/-- The second-coordinate tube profile is globally six-Lipschitz, including
across its corner at `1/2`. This controls a block crossing that corner when
integer division leaves a remainder, in the block bound for `lem-walk-bdy-sum` -/
theorem tube_right_profile_abs_sub_le (t u : ℝ) :
    |(-6 * max 0 (t - 1 / 2)) - (-6 * max 0 (u - 1 / 2))| ≤
      6 * |t - u| := by
  have h := abs_max_sub_max_le_max (0 : ℝ) (t - 1 / 2) 0 (u - 1 / 2)
  have heq : (t - 1 / 2) - (u - 1 / 2) = t - u := by ring
  simp only [sub_self, abs_zero, heq, max_eq_right (abs_nonneg (t - u))] at h
  calc
    |(-6 * max 0 (t - 1 / 2)) - (-6 * max 0 (u - 1 / 2))| =
        6 * |max 0 (t - 1 / 2) - max 0 (u - 1 / 2)| := by
          rw [← mul_sub, abs_mul]
          norm_num
    _ ≤ 6 * |t - u| := mul_le_mul_of_nonneg_left h (by norm_num)

/-- Conditional endpoint-minus-excursion estimate, with the maximal-tail
statement as its sole additional analytic input. The constants are uniform
over compact recentering offsets and block starting times. This is an
intermediate estimate for `lem-walk-bdy-sum`, not the eventual tube theorem -/
theorem iidCodeWalk_endpoint_and_max_lower_bound_of_tail
    (htail : ∀ (s m : ℕ), 0 < m → ∀ (a : ℝ), 0 < a →
      iidCodeMeasure.real {ω | ∃ k, k ≤ m ∧
        (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
         a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)} ≤
        4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ))))
    (C : Set (ℝ × ℝ)) (hC : IsCompact C) (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ s : ℕ,
      ∀ z ∈ C, ∀ a : ℝ, 0 < a →
      c - 4 * Real.exp (-(a ^ 2) / (2 * (m : ℝ))) ≤
        iidCodeMeasure.real {ω |
          (Real.sqrt (m : ℝ))⁻¹ •
            (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
             ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈ Metric.ball z r ∧
          ∀ k ≤ m,
            |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| < a ∧
            |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)| < a} := by
  obtain ⟨c, hc, m₀, hmass⟩ :=
    iidCodeWalk_endpoint_compact_lower_bound C hC r hr
  refine ⟨c, hc, max 1 m₀, ?_⟩
  intro m hm s z hz a ha
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 m₀).trans hm)
  have hm₀ : m₀ ≤ m := (le_max_right 1 m₀).trans hm
  let A : Set (ℕ → Fin 3) := {ω | (Real.sqrt (m : ℝ))⁻¹ •
    (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
     ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈ Metric.ball z r}
  let B : Set (ℕ → Fin 3) := {ω | ∃ k, k ≤ m ∧
    (a ≤ |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| ∨
     a ≤ |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)|)}
  have hdiff : iidCodeMeasure.real A - iidCodeMeasure.real B ≤
      iidCodeMeasure.real (A \ B) := le_measureReal_sdiff
  have hgood : A \ B ⊆ {ω |
      (Real.sqrt (m : ℝ))⁻¹ •
        (((codeWalk ω (s + m) - codeWalk ω s).1 : ℝ),
         ((codeWalk ω (s + m) - codeWalk ω s).2 : ℝ)) ∈ Metric.ball z r ∧
      ∀ k ≤ m,
        |((codeWalk ω (s + k) - codeWalk ω s).1 : ℝ)| < a ∧
        |((codeWalk ω (s + k) - codeWalk ω s).2 : ℝ)| < a} := by
    intro ω hω
    refine ⟨hω.1, fun k hk => ⟨?_, ?_⟩⟩
    · exact lt_of_not_ge (fun h => hω.2 ⟨k, hk, Or.inl h⟩)
    · exact lt_of_not_ge (fun h => hω.2 ⟨k, hk, Or.inr h⟩)
  exact (sub_le_sub (hmass m hm₀ s z hz) (htail s m hmpos a ha)).trans
    (hdiff.trans (measureReal_mono hgood))

end DirectedDistances.RandomWalk
