module

public import DirectedDistances.PaperProofs.Section7.CellLDPUpperAssembly
public import DirectedDistances.PaperProofs.Section7.CellLDPLowerAssembly
public import DirectedDistances.PaperProofs.Section7.LongPathAE
public import DirectedDistances.Recursive.BusemannMeasurable
import DirectedDistances.Recursive.LeftStationaryBusemann

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open Quiver




theorem cell_ldp_upper_of_items
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∀ ε : ℝ, 0 < ε → ε < 2 / 3 → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ A : ℝ, 1 < A →
        1 - C * A ^ (-(2 / 3 : ℝ) + ε) ≤
          iidCodeMeasure.real {ω | ∀ x y : StagePresentVertex
            (fun i => ω (i + 1)) n,
            x.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
            y.id < (kmswStage (fun i => ω (i + 1)) n).nextVertex →
            ldpSup x y ≤
              ((⌊A * (n : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : WithBot ℕ)} := by
  exact cell_ldp_upper_conditional hind
    busemannLDPMeasurableVersion_left_stationary hsym

/-- The negative-side subfamily inherits independence from the full integer
family by injective precomposition and measurable casting to `ℝ`. -/
theorem cell_ldp_negative_subfamily_independent
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure) :
    iIndepFun
      (fun (j : ℕ) ω =>
        (ldpIncrement busemannLDPMeasurableVersion (-((j : ℤ) + 1)) ω : ℝ))
      iidCodeMeasure := by
  let g : ℕ → ℤ := fun j => -((j : ℤ) + 1)
  have hg : Function.Injective g := by
    intro i j hij
    have hcast : (i : ℤ) = j := by dsimp [g] at hij; omega
    exact_mod_cast hcast
  have hpre := hind.precomp (g := g) hg
  have hreal := hpre.comp (fun _ : ℕ => fun z : ℤ => (z : ℝ))
    (fun _ => measurable_of_countable fun z : ℤ => (z : ℝ))
  change iIndepFun (fun j ω =>
    (ldpIncrement busemannLDPMeasurableVersion (g j) ω : ℝ)) iidCodeMeasure at hreal
  simpa only [g] using hreal













theorem cell_ldp_lower_of_items
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    {c x₀ : ℝ} (hc : 0 < c) (hx₀ : 0 < x₀)
    (habs : ∀ x ≥ x₀,
      2 * c * x ^ (-(2 / 3 : ℝ)) ≤ iidCodeMeasure.real
        {ω | x ≤ |(ldpIncrement busemannLDPMeasurableVersion 0 ω : ℝ)|})
    (hinput : ∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
      ∀ ell k : ℕ, 1 ≤ ell → ell < k →
        ∃ P : InfinitePresentPath (fun i => ω (i + 1))
          ⟨boundaryVertex (fun i => ω (i + 1)) h (-(ell : ℤ))⟩,
          P.HasLongestSegments ∧
          ∃ y : ℕ → PresentVertex (fun i => ω (i + 1)),
            Function.Injective y ∧
            (∀ T, ∃ N, ∀ r, N ≤ r →
              ∃ s, T ≤ s ∧ y r = (P.initial s).1) ∧
            (∀ r, Reachable
              (⟨boundaryVertex (fun i => ω (i + 1)) h (-(k : ℤ))⟩ :
                PresentVertex (fun i => ω (i + 1))) (y r)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : ℝ, 1 < A →
      1 - (C * A ^ (-(2 / 3 : ℝ) + ε) +
        c₂ * Real.exp (-(c₃ * A ^ ε))) ≤
        iidCodeMeasure.real {ω | ∃ a b : StagePresentVertex
          (fun i => ω (i + 1)) n, ∃ q : Path a b,
            A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)} := by
  let hmeasInc : ∀ k, Measurable (fun ω =>
      ldpIncrement busemannLDPMeasurableVersion k ω) := by
    intro k
    exact (measurable_busemannLDPMeasurableVersion k).sub
      (measurable_busemannLDPMeasurableVersion (k - 1))
  let hmeas : ∀ j : ℕ, Measurable (fun ω =>
      (ldpIncrement busemannLDPMeasurableVersion (-((j : ℤ) + 1)) ω : ℝ)) := by
    intro j
    exact (measurable_of_countable fun z : ℤ => (z : ℝ)).comp
      (hmeasInc (-((j : ℤ) + 1)))
  exact cell_ldp_lower_conditional busemannLDPMeasurableVersion hmeasInc hmeas
    (cell_ldp_negative_subfamily_independent hind)
    busemannLDPMeasurableVersion_left_stationary hsym hc hx₀ habs
    (longPath_ae hinput) ε hε

end DirectedDistances.PaperProofs.Section7
