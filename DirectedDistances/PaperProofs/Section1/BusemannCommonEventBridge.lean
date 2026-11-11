/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BusemannM0Unconditional

/-! Helper toward Theorem 1.4 (thm-busemann); not a paper result.
This packages the separate almost-everywhere code-model SDP and LDP results
are hit-indexed `boundaryPresentVertex` labels on the iid-code exploration
model. No identification with the source planar map or its labels is proved
here. The input theorems provide almost-everywhere propositions rather than
measurable event sets, so this file states the common almost-everywhere
property without asserting a measurable event-set representation. -/

public section
namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory DirectedDistances.KMSW

/-- Helper toward Theorem 1.4 (thm-busemann); not a paper result.
On one almost-sure event in the iid-code exploration model, there is a shared
hit witness and LDP local-finiteness witness for which normalized, eventually
distance-difference SDP and LDP functions each exist uniquely. This does not
identify the code model, graph, or hit-indexed labels with the source objects -/
theorem iidCodes_ae_boundaryBusemann_common :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
          ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
            (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        (∃! X : ℤ → ℤ,
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X) ∧
        (∃! X : ℤ → ℤ,
          IsBoundaryBusemannSDP
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X) := by
  filter_upwards [iidCodes_ae_boundaryBusemannLDP_existsUnique,
    iidCodes_ae_boundaryBusemannSDP_existsUnique] with ω hLDP hSDP
  obtain ⟨hfin, hLDP, XLDP, hXLDP, huniqLDP⟩ := hLDP
  obtain ⟨hSDP, XSDP, hXSDP, huniqSDP⟩ := hSDP
  have hh : hSDP = hLDP := Subsingleton.elim _ _
  subst hSDP
  exact ⟨hfin, hLDP, ⟨XLDP, hXLDP, huniqLDP⟩,
    ⟨XSDP, hXSDP, huniqSDP⟩⟩

end DirectedDistances.PaperProofs.Section1
