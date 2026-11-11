module

public import DirectedDistances.Probability.HewittSavage
public import Mathlib.Probability.Independence.InfinitePi

/-! # Hewitt–Savage zero–one law for iid sequences -/

public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory

/-- Hewitt–Savage zero-one law for an iid sequence on an arbitrary probability space; -/
theorem iid_sequence_hs_zero_one
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → S)
    (hZ_meas : ∀ n, Measurable (Z n))
    (hZ_indep : iIndepFun Z μ)
    (hZ_law : ∀ n, μ.map (Z n) = ν)
    {A : Set (ℕ → S)} (hA : MeasurableSet A)
    (hA_perm : ∀ σ : Equiv.Perm ℕ, {i | σ i ≠ i}.Finite →
      (fun x i => x (σ i)) ⁻¹' A = A) :
    μ ((fun ω i => Z i ω) ⁻¹' A) = 0 ∨
      μ ((fun ω i => Z i ω) ⁻¹' A) = 1 := by
  have hjoint : Measurable (fun ω i => Z i ω) := measurable_pi_iff.2 hZ_meas
  have hmap : μ.map (fun ω i => Z i ω) = Measure.infinitePi (fun _ : ℕ => ν) := by
    calc
      μ.map (fun ω i => Z i ω) =
          Measure.infinitePi (fun i => μ.map (Z i)) :=
        hZ_indep.map_fun_eq_infinitePi_map hZ_meas
      _ = Measure.infinitePi (fun _ : ℕ => ν) := by
        congr 1
        funext i
        exact hZ_law i
  have hprob :
      μ ((fun ω i => Z i ω) ⁻¹' A) = (Measure.infinitePi (fun _ : ℕ => ν)) A := by
    rw [← Measure.map_apply hjoint hA, hmap]
  have hzero := infinitePi_hs_zero_one ν A hA hA_perm
  simpa only [hprob] using hzero

end DirectedDistances.Probability
