module

public import DirectedDistances.Probability.SkewedStableMultiBlock

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The vector of normalized consecutive disjoint-block sums used by the finite-dimensional -/
@[expose] noncomputable def skewStableBlockVector {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    {ν : ℝ} {t : ℕ → ℝ} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun i : Fin k ↦
    (n : ℝ) ^ (-1 / ν) *
      ∑ j ∈ Finset.Ico ⌊(n : ℝ) * t i.val⌋₊ ⌊(n : ℝ) * t (i.val + 1)⌋₊, X j ω)

/-- Scalar characteristic-function helper toward E-STABLE / thm-busemann-conv
of consecutive disjoint-block normalized iid sums converge to the product formula; this does
not assert joint convergence in distribution, functional convergence, path tightness or
Busemann law identification, and is not the paper result. -/
theorem tendsto_charFun_skewStable_blockVector {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hX : ∀ i, Measurable (X i)) {κp κm : ℂ} {ν : ℝ} (hν : 0 < ν)
    (hexp : (fun t ↦ charFun (P.map (X 0)) t -
      (1 - (if 0 ≤ t then κp else κm) * (|t| ^ ν : ℝ)))
      =o[𝓝 0] (fun t ↦ |t| ^ ν)) {k : ℕ} {t : ℕ → ℝ}
    (ht0 : 0 ≤ t 0) (hmono : Monotone t) (θ : EuclideanSpace ℝ (Fin k)) :
    Tendsto (fun n : ℕ ↦ charFun
      (P.map (skewStableBlockVector (t := t) (ν := ν) X n)) θ) atTop
      (𝓝 (∏ i : Fin k, Complex.exp
        (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
          ((if 0 ≤ θ i then κp else κm) * (|θ i| ^ ν : ℝ)))))) := by
  let θNat : ℕ → ℝ := fun i ↦ if hi : i < k then θ ⟨i, hi⟩ else 0
  have hinner (n : ℕ) (ω : Ω) :
      inner ℝ (skewStableBlockVector (t := t) (ν := ν) X n ω) θ =
        ∑ i ∈ Finset.range k, θNat i *
          ((n : ℝ) ^ (-1 / ν) *
            ∑ j ∈ Finset.Ico ⌊(n : ℝ) * t i⌋₊ ⌊(n : ℝ) * t (i + 1)⌋₊,
              X j ω) := by
    simp only [skewStableBlockVector, PiLp.inner_apply, Real.inner_apply]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [θNat]
    ring
  have hmeas (n : ℕ) : AEMeasurable
      (skewStableBlockVector (k := k) (t := t) (ν := ν) X n) P := by
    have hm : Measurable (skewStableBlockVector (k := k) (t := t) (ν := ν) X n) := by
      change Measurable (fun ω ↦ (WithLp.equiv 2 (Fin k → ℝ)).symm (fun i : Fin k ↦
        (n : ℝ) ^ (-1 / ν) *
          ∑ j ∈ Finset.Ico ⌊(n : ℝ) * t i.val⌋₊
            ⌊(n : ℝ) * t (i.val + 1)⌋₊, X j ω))
      exact (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp
        (measurable_pi_iff.mpr fun i ↦
          (Finset.measurable_fun_sum _ (fun j _ ↦ hX j)).const_mul _)
    exact hm.aemeasurable
  have hcf (n : ℕ) : charFun
      (P.map (skewStableBlockVector (t := t) (ν := ν) X n)) θ =
        charFun (P.map (fun ω ↦ ∑ i ∈ Finset.range k, θNat i *
          ((n : ℝ) ^ (-1 / ν) *
            ∑ j ∈ Finset.Ico ⌊(n : ℝ) * t i⌋₊ ⌊(n : ℝ) * t (i + 1)⌋₊,
              X j ω))) 1 := by
    rw [charFun_map_eq_charFun_map_inner_one (hmeas n) θ]
    congr 2
    funext ω
    exact hinner n ω
  let gNat : ℕ → ℂ := fun i ↦ Complex.exp
    (-(((t (i + 1) - t i : ℝ) : ℂ) *
      ((if 0 ≤ θNat i then κp else κm) * (|θNat i| ^ ν : ℝ))))
  have hprodTerm (i : Fin k) :
      Complex.exp (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
        ((if 0 ≤ θ i then κp else κm) * (|θ i| ^ ν : ℝ)))) =
      gNat i.val := by simp [gNat, θNat]
  have hprodFin :
      (∏ i : Fin k, Complex.exp (-(((t (i.val + 1) - t i.val : ℝ) : ℂ) *
        ((if 0 ≤ θ i then κp else κm) * (|θ i| ^ ν : ℝ))))) =
        ∏ i ∈ Finset.range k, gNat i := by
    calc
      _ = ∏ i : Fin k, gNat i.val := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hprodTerm i
      _ = _ := Fin.prod_univ_eq_prod_range gNat k
  have hlimit := tendsto_charFun_skewStable_multiBlock hindep hident hν hexp
    ht0 hmono θNat k
  rw [hprodFin]
  simpa only [hcf, gNat] using hlimit

end DirectedDistances.Probability
