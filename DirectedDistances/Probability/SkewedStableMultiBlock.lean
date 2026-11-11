module

public import DirectedDistances.Probability.SkewedStableTwoBlock
public import DirectedDistances.Probability.SkewedStableCLTTime

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

private theorem charFun_consecutive_blocks_succ {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (mX : ∀ i, AEMeasurable (X i) P)
    (b : ℕ → ℕ) (hb : Monotone b) (a : ℝ) (θ : ℕ → ℝ) (k : ℕ) :
    charFun (P.map (fun ω ↦ ∑ i ∈ Finset.range (k + 1),
      θ i * (a * ∑ j ∈ Finset.Ico (b i) (b (i + 1)), X j ω))) 1 =
      charFun (P.map (fun ω ↦ ∑ i ∈ Finset.range k,
        θ i * (a * ∑ j ∈ Finset.Ico (b i) (b (i + 1)), X j ω))) 1 *
      charFun (P.map (fun ω ↦ a * ∑ j ∈ Finset.Ico (b k) (b (k + 1)), X j ω))
        (θ k) := by
  have hbound (i : Finset.range k) (j : Finset.Ico (b i) (b (i + 1))) :
      j.val ∈ Finset.range (b k) := by
    apply Finset.mem_range.mpr
    exact (Finset.mem_Ico.mp j.property).2.trans_le
      (hb (Nat.succ_le_of_lt (Finset.mem_range.mp i.property)))
  let F (v : Finset.range (b k) → ℝ) : ℝ :=
    ∑ i : Finset.range k, θ i * (a *
      ∑ j : Finset.Ico (b i) (b (i + 1)), v ⟨j, hbound i j⟩)
  let G (v : Finset.Ico (b k) (b (k + 1)) → ℝ) : ℝ :=
    θ k * (a * ∑ j, v j)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hG : Measurable G := by dsimp [G]; fun_prop
  have hcompF : F ∘ (fun ω (j : Finset.range (b k)) ↦ X j ω) =
      (fun ω ↦ ∑ i ∈ Finset.range k,
        θ i * (a * ∑ j ∈ Finset.Ico (b i) (b (i + 1)), X j ω)) := by
    funext ω
    dsimp only [Function.comp_apply, F]
    calc
      _ = ∑ i : Finset.range k,
          θ i * (a * ∑ j ∈ Finset.Ico (b i) (b (i + 1)), X j ω) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun x : ℝ ↦ θ i * (a * x))
          (Finset.sum_coe_sort _ (fun j : ℕ ↦ X j ω))
      _ = _ := Finset.sum_coe_sort _ (fun i : ℕ ↦
        θ i * (a * ∑ j ∈ Finset.Ico (b i) (b (i + 1)), X j ω))
  have hcompG : G ∘ (fun ω (j : Finset.Ico (b k) (b (k + 1))) ↦ X j ω) =
      (fun ω ↦ θ k * (a * ∑ j ∈ Finset.Ico (b k) (b (k + 1)), X j ω)) := by
    funext ω
    exact congrArg (fun x : ℝ ↦ θ k * (a * x))
      (Finset.sum_coe_sort _ (fun j : ℕ ↦ X j ω))
  have hdisj : Disjoint (Finset.range (b k)) (Finset.Ico (b k) (b (k + 1))) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    exact (not_le_of_gt (Finset.mem_range.mp hj)) (Finset.mem_Ico.mp hj').1
  have hi := hindep.indepFun_finset₀ _ _ hdisj mX
  have hi' : IndepFun
      (fun ω ↦ ∑ i ∈ Finset.range k,
        θ i * (a * ∑ j ∈ Finset.Ico (b i) (b (i + 1)), X j ω))
      (fun ω ↦ θ k * (a * ∑ j ∈ Finset.Ico (b k) (b (k + 1)), X j ω)) P := by
    rw [← hcompF, ← hcompG]
    exact hi.comp hF hG
  have mU := Finset.aemeasurable_fun_sum (Finset.range k) (fun i _ ↦
    ((Finset.aemeasurable_fun_sum (Finset.Ico (b i) (b (i + 1)))
      (fun j _ ↦ mX j)).const_mul a).const_mul (θ i))
  have mV := (Finset.aemeasurable_fun_sum (Finset.Ico (b k) (b (k + 1)))
    (fun j _ ↦ mX j)).const_mul a
  have he := congrFun (hi'.charFun_map_fun_add_eq_mul mU (mV.const_mul (θ k))) 1
  simp_rw [Finset.sum_range_succ]
  simpa only [Pi.mul_apply, charFun_map_mul_comp mV, mul_one] using he

/-- Scalar helper toward E-STABLE / thm-busemann-conv
finitely many consecutive disjoint-block normalized iid sums converges to the product of
the one-time skewed stable limits; no joint convergence in distribution, functional
convergence, tightness of paths or Busemann law identification is claimed; not the paper result. -/
theorem tendsto_charFun_skewStable_multiBlock {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {κp κm : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν))
    {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (hmono : Monotone t) (θ : ℕ → ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ ↦ charFun (P.map (fun ω ↦ ∑ i ∈ Finset.range k,
      θ i * ((n : ℝ) ^ (-1 / ν) *
        ∑ j ∈ Finset.Ico ⌊(n : ℝ) * t i⌋₊ ⌊(n : ℝ) * t (i + 1)⌋₊, X j ω))) 1)
      atTop (𝓝 (∏ i ∈ Finset.range k,
        Complex.exp (-(((t (i + 1) - t i : ℝ) : ℂ) *
          ((if 0 ≤ θ i then κp else κm) * (|θ i| ^ ν : ℝ)))))) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hb (n : ℕ) : Monotone (fun i ↦ ⌊(n : ℝ) * t i⌋₊) := by
      intro i j hij
      exact Nat.floor_mono (mul_le_mul_of_nonneg_left (hmono hij) (Nat.cast_nonneg n))
    simp_rw [charFun_consecutive_blocks_succ hindep
      (fun i ↦ (hident i).aemeasurable_fst) _ (hb _) _ θ k, Finset.prod_range_succ]
    exact ih.mul (tendsto_charFun_skewStable_sum_block hindep hident hν hexp
      (ht0.trans (hmono (Nat.zero_le k))) (hmono (Nat.le_succ k)) (θ k))

end DirectedDistances.Probability
