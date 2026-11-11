/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperLocalExit

/- # Isolated proof provider for Lemma 7.13 (`lem-boltzmann-sdp-upper`)

forwards to a proved helper; installation, sealing and counting are separate gates. No
conclusion or source hypothesis is added.

the Boltzmann law of maps with right boundary length `r` and a marked left-boundary vertex,
which is the law of `(M̂(r), ẑ(r))` (Lemma 7.9, marked-vertex convention); the map's source is `x₀` and its sink
is `x_r` (source/sink convention). "With probability tending to one as `A → ∞`, uniformly in `r`" is written as: for
every `δ > 0` there is one `A > 1` such that for every `r ≥ 1` the event
`SDP(x₀, x_r) ≤ A r^{3/4}` has probability at least `1 - δ`. `presentDartSDP` is the directed
shortest-path distance along present darts (unreachable = `⊤ = +∞`), compared in `ℝ≥0∞`. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section7

/-- Lemma 7.13 isolated provider (`lem-boltzmann-sdp-upper`, -/
theorem boltzmann_sdp_upper (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q | ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
            q.1.2.2.out.B.source q.1.2.2.out.B.sink) ≤
          ENNReal.ofReal (A * (r : ℝ) ^ (3 / 4 : ℝ))} := by
  exact DirectedDistances.PaperProofs.Section7.boltzmann_sdp_upper_code δ hδ

end DirectedDistances.PaperProofs.SourceResults
