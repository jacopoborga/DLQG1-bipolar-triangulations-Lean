/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass10

/-! Helper toward Definition 3.8 (consumer).

# Finite-window capture data and canonical ball classes -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open MeasureTheory Set

/-- Helper toward Definition 3.8 (consumer): under code agreement on a window
containing the finite stage, both its strong capture event and its left-seam
index set are unchanged. These are the finite-data parts of a certified
capture; the theorem does not assert that the later-window seam inequalities
or whole-plane root identifications transfer. -/
theorem uibhbotD39FiniteCaptureData_eq_of_codeWindow
    (W W' : ℤ → Fin 3) (N m r c : ℕ) (hm : m ≤ 2 * N)
    (hwindow : ∀ i : ℤ,
      i ∈ Set.Icc (-(N : ℤ)) (N : ℤ) → W' i = W i) :
    (kmswWindowCaptureEventStrongRel (shiftedStream W' N) m r c ↔
      kmswWindowCaptureEventStrongRel (shiftedStream W N) m r c) ∧
    kmswBallLeftSeamSet (shiftedStream W' N) m r c =
      kmswBallLeftSeamSet (shiftedStream W N) m r c := by
  exact ⟨uibhbotD39StrongCaptureEvent_iff_of_codeWindow
      W W' N m r c hm hwindow,
    uibhbotD39LeftSeamSet_eq_of_codeWindow W W' N m r c hm hwindow⟩



































































end DirectedDistances.PaperProofs.Section5

end
