module

public import DirectedDistances.PaperProofs.Section7.CellLDPReduction
import DirectedDistances.PaperProofs.Section7.LongPathHinput
import DirectedDistances.KMSW.RawGeodesicAE

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive





theorem cell_ldp_lower_of_items_geodesic
    (hind : iIndepFun
      (fun k ω => ldpIncrement busemannLDPMeasurableVersion k ω) iidCodeMeasure)
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω))
    {c x₀ : ℝ} (hc : 0 < c) (hx₀ : 0 < x₀)
    (habs : ∀ x ≥ x₀,
      2 * c * x ^ (-(2 / 3 : ℝ)) ≤ iidCodeMeasure.real
        {ω | x ≤ |(ldpIncrement busemannLDPMeasurableVersion 0 ω : ℝ)|})
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C c₂ c₃ : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : ℝ, 1 < A →
      1 - (C * A ^ (-(2 / 3 : ℝ) + ε) +
        c₂ * Real.exp (-(c₃ * A ^ ε))) ≤
        iidCodeMeasure.real {ω | ∃ a b : StagePresentVertex
          (fun i => ω (i + 1)) n, ∃ q : Path a b,
            A⁻¹ * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (q.length : ℝ)} := by
  have hgeo : ∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∀ k : ℤ,
        ∃ P : InfinitePresentPath (fun i => ω (i + 1))
          ⟨boundaryVertex (fun i => ω (i + 1)) h k⟩, P.HasLongestSegments := by
    filter_upwards [iidCodes_ae_boundary_infinite_extremal] with ω hω
    exact fun h k => (hω h k).1
  exact cell_ldp_lower_of_items hind hsym hc hx₀ habs
    (longPath_hinput_of_geodesics hgeo) ε hε

end DirectedDistances.PaperProofs.Section7
