/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass5

/-! Helper toward Definition 3.8 (consumer).

# Finite-window locality of canonical Definition 3.8 balls -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open MeasureTheory Set

/-- Helper toward Definition 3.8 (consumer): a finite KMSW stage of length at
most `2 * N`, viewed from window `N`, is unchanged when the two code words
agree on `[-N,N]`. -/
theorem uibhbotD39Stage_eq_of_codeWindow
    (W W' : ℤ → Fin 3) (N m : ℕ) (hm : m ≤ 2 * N)
    (hwindow : ∀ i : ℤ,
      i ∈ Set.Icc (-(N : ℤ)) (N : ℤ) → W' i = W i) :
    kmswStage (shiftedStream W' N) m = kmswStage (shiftedStream W N) m := by
  apply kmswStage_congr
  intro i hi
  have hlo : -(N : ℤ) ≤ (i : ℤ) - N := by omega
  have hhi : (i : ℤ) - N ≤ N := by omega
  exact hwindow ((i : ℤ) - N) ⟨hlo, hhi⟩

/-- Helper toward Definition 3.8 (consumer): the directed KMSW stages seen
through a finite matching code window are isomorphic, preserving their
directed rotations, edge identities, and face cycles. -/
@[expose] def uibhbotD39StageMapIso_of_codeWindow
    (W W' : ℤ → Fin 3) (N m : ℕ) (hm : m ≤ 2 * N)
    (hwindow : ∀ i : ℤ,
      i ∈ Set.Icc (-(N : ℤ)) (N : ℤ) → W' i = W i) :
    DirectedMapWithMissingIso
      (kmswStageDirectedMap (shiftedStream W' N) m)
      (kmswStageDirectedMap (shiftedStream W N) m) := by
  apply kmswStageDirectedMapIsoOfPrefix
  intro i hi
  have hlo : -(N : ℤ) ≤ (i : ℤ) - N := by omega
  have hhi : (i : ℤ) - N ≤ N := by omega
  exact hwindow ((i : ℤ) - N) ⟨hlo, hhi⟩

/-- Helper toward Definition 3.8 (consumer): under the rotation hypotheses
`H` and `H'`, certified captures `hcap` and `hcap'` at the same window yield
equal faced/framed combinatorial ball classes when the code windows agree. -/
theorem uibhbotD39FacedBallClass_eq_of_codeWindow_and_captures
    (r N : ℕ) (hr : 0 < r) (W W' : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis W')
    (hcap : ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
      (kmswLLCreatedEdge (shiftedStream W N) N) true)
    (hcap' : ∃ c, uibhbotFixedCaptureRel W' r N (2 * N) c
      (kmswLLCreatedEdge (shiftedStream W' N) N) true)
    (hwindow : ∀ i : ℤ,
      i ∈ Set.Icc (-(N : ℤ)) (N : ℤ) → W' i = W i) :
    facedUIBHBOTBallClassRel W r hr = facedUIBHBOTBallClassRel W' r hr :=
  facedUIBHBOTBallClassRel_eq_of_codeWindow_and_captures
    r N hr W W' H H' hcap hcap' hwindow








































end DirectedDistances.PaperProofs.Section5

end
