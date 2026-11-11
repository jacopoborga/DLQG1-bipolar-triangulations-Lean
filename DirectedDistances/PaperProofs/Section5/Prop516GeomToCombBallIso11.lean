/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso9
public import DirectedDistances.PlanarMap.D39RadialOrder18

/-! # Successor transport toward Proposition 5.16

Helper toward Proposition 5.16. The radial-segment three-germ comparison in
`D39RadialOrder18` removes the conditional premise from the local successor
transport lemma. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. An orientation-preserving homeomorphism
that maps each short radial segment to a radial segment transports a
counterclockwise successor. -/
theorem d39_CcwSuccessor_transport_of_radial_segments_unconditionally
    {D : Type*} {star : Set D} {dir dir' : D → ℂ} {d e : D}
    (K : ℂ ≃ₜ ℂ) (hK : OrientationPreserving K) (hK0 : K 0 = 0)
    (hdir : ∀ x ∈ star, dir x ≠ 0 ∧ dir' x ≠ 0)
    (harg : ∀ x ∈ star, ∀ y ∈ star,
      Complex.arg (dir x) = Complex.arg (dir y) → x = y)
    (hsegments : ∀ x ∈ star, ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      K '' {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ r ∧ z = (t : ℂ) * dir x} =
        {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ z = (t : ℂ) * dir' x})
    (hsucc : CcwSuccessor star dir d e) :
    CcwSuccessor star dir' d e := by
  apply d39_CcwSuccessor_transport_of_radial_segments K hK hK0
  · intro K' hK' hK0' u v w u' v' w' hu hv hw hu' hv' hw' huv huw hvw
      hsegmentsU hsegmentsV hsegmentsW
    exact orientationPreserving_ccwTurn_lt_iff_of_radial_segments
      K' hK' hK0' u v w u' v' w' hu hv hw hu' hv' hw' huv huw hvw
      hsegmentsU hsegmentsV hsegmentsW
  · exact hdir
  · exact harg
  · exact hsegments
  · exact hsucc








































































end DirectedDistances.PaperProofs.Section5

end
