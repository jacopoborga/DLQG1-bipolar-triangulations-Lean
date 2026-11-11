module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperProps
public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperProps2
public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperCellInput

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper: CONDITIONAL reduction to three open Props);
not a paper result. This is the explicit uniform-tail provider target used by the assembly:
for every positive delta, one A > 1 works for every r >= 1. It spells out the paper's
"probability tending to one as A tends to infinity, uniformly in r" using the right-vertex-
marked Boltzmann law, `presentDartSDP` between the map's source and sink, and the ENNReal bound.
It is not token-identical to the prose statement in `finite.tex`; those are the precise formal
representations of its probability limit and random map. -/
def boltzmannSdpUpperThreePropsProviderTarget : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
    1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
      {q | ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
          q.1.2.2.out.B.source q.1.2.2.out.B.sink) ≤
        ENNReal.ofReal (A * (r : ℝ) ^ (3 / 4 : ℝ))}









theorem boltzmann_sdp_upper_of_threeProps
    (hL : boltzmannSdpUpper_localExitGeometry)
    (hR : boltzmannSdpUpper_reversalClassGeometry)
    (hB : boltzmannSdpUpper_boundaryPathIntersection) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q | ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
            q.1.2.2.out.B.source q.1.2.2.out.B.sink) ≤
          ENNReal.ofReal (A * (r : ℝ) ^ (3 / 4 : ℝ))} := by
  exact boltzmann_sdp_upper_of_cellBullets_and_openProps
    boltzmannSdpUpper_cellInput_proved
    (boltzmannSdpUpper_cellPathInterception_of_localExitGeometry hL)
    (boltzmannSdpUpper_markedReversal_of_classGeometry hR)
    hB

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper: CONDITIONAL reduction to three open Props);
not a paper result. Comparison theorem: the spelled-out theorem conclusion is the same formal
proposition as the documented provider target. The equivalence is by definitional unfolding. -/
theorem boltzmann_sdp_upper_of_threeProps_matches_providerTarget
    :
    (∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q | ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
            q.1.2.2.out.B.source q.1.2.2.out.B.sink) ≤
          ENNReal.ofReal (A * (r : ℝ) ^ (3 / 4 : ℝ))}) ↔
      boltzmannSdpUpperThreePropsProviderTarget := by
  rfl

end DirectedDistances.PaperProofs.Section7
