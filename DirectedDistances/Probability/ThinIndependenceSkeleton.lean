module

public import DirectedDistances.Probability.BackwardIndependenceAssembly
public import Mathlib.Probability.Independence.Basic

/-! # Abstract independence skeleton

(conditional independence on E_k + backward convergence + increasing limit); the concrete -/

public section

namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

/-- independence on events of probability tending to one gives independence by backward
used; not the paper result. -/
theorem indep_of_backward_indicator_factorization
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ k, F k ≤ m0) (hanti : Antitone F)
    (htriv : ∀ A, MeasurableSet[⨅ k, F k] A → μ A = 0 ∨ μ A = 1)
    (E : ℕ → Set Ω) (hE : ∀ k, MeasurableSet[F k] (E k))
    (hEto : Tendsto (fun k => μ (E k)) atTop (𝓝 1))
    (gL gR : MeasurableSpace Ω) (hgL : gL ≤ m0) (hgR : gR ≤ m0)
    (hfac : ∀ k A, MeasurableSet[gL] A → ∀ B, MeasurableSet[gR] B →
      μ[(A ∩ B).indicator (1 : Ω → ℝ) | F k] * (E k).indicator 1 =ᵐ[μ]
        μ[A.indicator (1 : Ω → ℝ) | F k] * μ[B.indicator (1 : Ω → ℝ) | F k] *
          (E k).indicator 1) :
    Indep gL gR μ := by
  apply (Indep_iff gL gR μ).mpr
  intro A B hA hB
  have hAm : MeasurableSet[m0] A := hgL A hA
  have hBm : MeasurableSet[m0] B := hgR B hB
  have hprod := integral_mul_eq_mul_integral_of_backward_factorization
    μ F hF hanti htriv E hE hEto
    (A.indicator (1 : Ω → ℝ)) (B.indicator (1 : Ω → ℝ))
    ((memLp_const (1 : ℝ)).indicator hAm.nullMeasurableSet)
    ((memLp_const (1 : ℝ)).indicator hBm.nullMeasurableSet)
    (fun k => by simpa only [← Set.inter_indicator_one] using hfac k A hA B hB)
  have hreal : μ.real (A ∩ B) = μ.real A * μ.real B := by
    rw [← integral_indicator_one (hAm.inter hBm), ← integral_indicator_one hAm,
      ← integral_indicator_one hBm]
    simpa only [Set.inter_indicator_one, Pi.mul_apply] using hprod
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _)
    (ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _))).mp
  simpa only [ENNReal.toReal_mul, ← measureReal_def] using hreal

/-- passes to the suprema of two increasing sequences of sigma-algebras. The concrete -/
theorem indep_iSup_of_monotone_pairs
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (gL gR : ℕ → MeasurableSpace Ω) (hgL : ∀ s, gL s ≤ m0) (hgR : ∀ s, gR s ≤ m0)
    (hmonoL : Monotone gL) (hmonoR : Monotone gR)
    (hind : ∀ s, Indep (gL s) (gR s) μ) :
    Indep (⨆ s, gL s) (⨆ s, gR s) μ := by
  apply indep_iSup_of_directed_le (m := gL) _ hgL (iSup_le hgR) hmonoL.directed_le
  intro i
  apply Indep.symm
  apply indep_iSup_of_directed_le (m := gR) _ hgR (hgL i) hmonoR.directed_le
  intro j
  exact (indep_of_indep_of_le (hind (max i j))
    (hmonoL (le_max_left i j)) (hmonoR (le_max_right i j))).symm

/-- (conditional independence on E_k + backward convergence + increasing limit), allowing
events depending on the truncation index. The concrete filtration F_k (renewal times, -/
theorem indep_iSup_of_backward_indicator_factorization
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ k, F k ≤ m0) (hanti : Antitone F)
    (htriv : ∀ A, MeasurableSet[⨅ k, F k] A → μ A = 0 ∨ μ A = 1)
    (gL gR : ℕ → MeasurableSpace Ω) (hgL : ∀ s, gL s ≤ m0) (hgR : ∀ s, gR s ≤ m0)
    (hmonoL : Monotone gL) (hmonoR : Monotone gR)
    (E : ℕ → ℕ → Set Ω) (hE : ∀ s k, MeasurableSet[F k] (E s k))
    (hEto : ∀ s, Tendsto (fun k => μ (E s k)) atTop (𝓝 1))
    (hfac : ∀ s k A, MeasurableSet[gL s] A → ∀ B, MeasurableSet[gR s] B →
      μ[(A ∩ B).indicator (1 : Ω → ℝ) | F k] * (E s k).indicator 1 =ᵐ[μ]
        μ[A.indicator (1 : Ω → ℝ) | F k] * μ[B.indicator (1 : Ω → ℝ) | F k] *
          (E s k).indicator 1) :
    Indep (⨆ s, gL s) (⨆ s, gR s) μ := by
  apply indep_iSup_of_monotone_pairs μ gL gR hgL hgR hmonoL hmonoR
  intro s
  exact indep_of_backward_indicator_factorization μ F hF hanti htriv
    (E s) (hE s) (hEto s) (gL s) (gR s) (hgL s) (hgR s) (hfac s)

/-- form of the abstract skeleton (conditional independence on E_k + backward convergence +
increasing limit). Limit maps measurable for the respective generated suprema are
used; not the paper result. -/
theorem indepFun_of_backward_indicator_factorization
    {Ω L R L' R' : Type*} {m0 : MeasurableSpace Ω}
    [mL : MeasurableSpace L] [mR : MeasurableSpace R]
    [MeasurableSpace L'] [MeasurableSpace R']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (hF : ∀ k, F k ≤ m0) (hanti : Antitone F)
    (htriv : ∀ A, MeasurableSet[⨅ k, F k] A → μ A = 0 ∨ μ A = 1)
    (XL : ℕ → Ω → L) (XR : ℕ → Ω → R)
    (hXL : ∀ s, Measurable (XL s)) (hXR : ∀ s, Measurable (XR s))
    (hmonoL : Monotone (fun s => mL.comap (XL s)))
    (hmonoR : Monotone (fun s => mR.comap (XR s)))
    (E : ℕ → ℕ → Set Ω) (hE : ∀ s k, MeasurableSet[F k] (E s k))
    (hEto : ∀ s, Tendsto (fun k => μ (E s k)) atTop (𝓝 1))
    (hfac : ∀ s k A, MeasurableSet[mL.comap (XL s)] A →
      ∀ B, MeasurableSet[mR.comap (XR s)] B →
      μ[(A ∩ B).indicator (1 : Ω → ℝ) | F k] * (E s k).indicator 1 =ᵐ[μ]
        μ[A.indicator (1 : Ω → ℝ) | F k] * μ[B.indicator (1 : Ω → ℝ) | F k] *
          (E s k).indicator 1)
    (XLlim : Ω → L') (XRlim : Ω → R')
    (hXLlim : Measurable[⨆ s, mL.comap (XL s)] XLlim)
    (hXRlim : Measurable[⨆ s, mR.comap (XR s)] XRlim) :
    IndepFun XLlim XRlim μ := by
  apply (IndepFun_iff_Indep XLlim XRlim μ).mpr
  apply indep_of_indep_of_le
    (indep_iSup_of_backward_indicator_factorization μ F hF hanti htriv
      (fun s => mL.comap (XL s)) (fun s => mR.comap (XR s))
      (fun s => (hXL s).comap_le) (fun s => (hXR s).comap_le)
      hmonoL hmonoR E hE hEto hfac)
    hXLlim.comap_le hXRlim.comap_le

end DirectedDistances.Probability
