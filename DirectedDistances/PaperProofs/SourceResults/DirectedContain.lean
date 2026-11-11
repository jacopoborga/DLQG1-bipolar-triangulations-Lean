/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.DirectedContainMapClause

/-! Supporting lemmas for paper labels `lem-directed-contain` (see CORRESPONDENCE.md). -/

/-! # Isolated proof provider for Lemma 5.2 (lem-directed-contain)


Reading: as in the x080 precedent, "has the same law" is rendered as equality
of generating-code laws. UIQBOT means the KMSW map of the Pitman-conditioned
code, the Definition 4.1 carrier used by the counted Section 4 results.
The pathwise code equalities and `boundaryFutureRootedMapClause` identify
that code's rooted planar map at the actual boundary stopping time.
`M0CutShiftContainment` retains the geometric edge IDs of every finite and
infinite directed cut path. Lean streams start at 0; source edge streams
start at 1, and the padded iid code's raw stream is `fun i => ω (i + 1)`.
One probability-one event supplies the same H, h and hLL for all k : ℤ.

This is exactly the unfolded content of `lemma52FullStatement`, retaining
its exposed path-containment and rooted-map predicates. The import closure
uses the HatLimit identification family, without `HatInducedFirstReturn`.
and counting remain the coordinator's responsibility. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory Quiver DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5




theorem directed_contain_provider :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∀ k : ℤ,
        wholePlaneIIDCodeMeasure.map (boundaryFutureCode k) =
          wholePlaneIIDCodeMeasure.map (boundaryFutureCode 0) ∧
        wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ boundaryFutureCode k) =
          iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) ∧
        (fun i => boundaryFutureCode k W (i + 1)) =
          (fun i => shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h k + i)) ∧
        (∃ hτ : HasFlowLineHits
            (fun i => shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h k + i)),
          hatLawCodes (boundaryFutureCode k W) =
            hatCodes (fun i => shiftedStream W 0
              (boundaryHitTime (shiftedStream W 0) h k + i)) hτ) ∧
        M0CutShiftContainment W H h hLL k ∧
        boundaryFutureRootedMapClause W h k := by
  exact lemma52Full_holds

end DirectedDistances.PaperProofs.SourceResults
