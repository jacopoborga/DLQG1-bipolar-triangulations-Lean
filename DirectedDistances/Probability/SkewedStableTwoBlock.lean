module

public import DirectedDistances.Probability.SkewedStableCLTTime

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

private theorem charFun_two_disjoint_sums {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (mX : ∀ i, AEMeasurable (X i) P)
    (I J : Finset ℕ) (hIJ : Disjoint I J) (a θ₁ θ₂ : ℝ) :
    charFun (P.map (fun ω ↦ θ₁ * (a * ∑ k ∈ I, X k ω) +
      θ₂ * (a * ∑ k ∈ J, X k ω))) 1 =
      charFun (P.map (fun ω ↦ a * ∑ k ∈ I, X k ω)) θ₁ *
        charFun (P.map (fun ω ↦ a * ∑ k ∈ J, X k ω)) θ₂ := by
  have mI := (Finset.aemeasurable_fun_sum I (fun i _ ↦ mX i)).const_mul a
  have mJ := (Finset.aemeasurable_fun_sum J (fun i _ ↦ mX i)).const_mul a
  have hi := hindep.indepFun_finset₀ I J hIJ mX
  have hsum (K : Finset ℕ) (θ : ℝ) :
      (fun v : K → ℝ ↦ θ * (a * ∑ k, v k)) ∘ (fun ω (k : K) ↦ X k ω) =
        (fun ω ↦ θ * (a * ∑ k ∈ K, X k ω)) := by
    funext ω
    exact congrArg (fun x : ℝ ↦ θ * (a * x))
      (Finset.sum_coe_sort K (fun k : ℕ ↦ X k ω))
  have hi' : IndepFun (fun ω ↦ θ₁ * (a * ∑ k ∈ I, X k ω))
      (fun ω ↦ θ₂ * (a * ∑ k ∈ J, X k ω)) P := by
    rw [← hsum I θ₁, ← hsum J θ₂]
    exact hi.comp (by fun_prop) (by fun_prop)
  have he := congrFun (hi'.charFun_map_fun_add_eq_mul
    (mI.const_mul θ₁) (mJ.const_mul θ₂)) 1
  simpa only [Pi.mul_apply, charFun_map_mul_comp mI, charFun_map_mul_comp mJ,
    mul_one] using he

/-- Scalar helper toward E-STABLE / thm-busemann-conv
two disjoint-block normalized iid sums converges to the product of the one-time skewed
stable limits; no joint convergence in distribution, functional convergence, tightness
of paths or Busemann law identification is claimed; not the paper result. -/
theorem tendsto_charFun_skewStable_twoBlock {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {κp κm : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (θ₁ θ₂ : ℝ) :
    Tendsto (fun n : ℕ ↦ charFun (P.map (fun ω ↦
      θ₁ * ((n : ℝ) ^ (-1 / ν) * ∑ k ∈ Finset.range ⌊(n : ℝ) * s⌋₊, X k ω) +
      θ₂ * ((n : ℝ) ^ (-1 / ν) *
        ∑ k ∈ Finset.Ico ⌊(n : ℝ) * s⌋₊ ⌊(n : ℝ) * t⌋₊, X k ω))) 1)
      atTop (𝓝 (Complex.exp (-((s : ℂ) *
        ((if 0 ≤ θ₁ then κp else κm) * (|θ₁| ^ ν : ℝ)))) *
        Complex.exp (-(((t - s : ℝ) : ℂ) *
          ((if 0 ≤ θ₂ then κp else κm) * (|θ₂| ^ ν : ℝ)))))) := by
  have hdisj (m m' : ℕ) : Disjoint (Finset.range m) (Finset.Ico m m') := by
    apply Finset.disjoint_left.mpr
    intro k hk hki
    exact (not_le_of_gt (Finset.mem_range.mp hk)) (Finset.mem_Ico.mp hki).1
  simp_rw [charFun_two_disjoint_sums hindep (fun i ↦ (hident i).aemeasurable_fst)
    _ _ (hdisj _ _)]
  exact (tendsto_charFun_skewStable_sum_floor hindep hident hν hexp hs θ₁).mul
    (tendsto_charFun_skewStable_sum_block hindep hident hν hexp hs hst θ₂)

end DirectedDistances.Probability
