/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTPresentationExposed6

/-! # Integer positions for the exposed UIQBOT boundary -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open MeasureTheory Filter

/-- Helper toward Definition 3.2: assign successive nonnegative positions to
UL and successive negative positions to LR in the exposed UIQBOT presentation. -/
@[expose] def uiqbotCanonicalBoundaryPresentationX_position
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    InfiniteBoundaryDartIndex
      (uiqbotCanonicalBoundaryPresentationX w hfin htrans hR hL0) → ℤ
  | .upperLeft i =>
      ((uiqbotCanonicalUpperLeftIndexEquivX
        w hfin htrans hR hL0 i : ℕ) : ℤ)
  | .upperRight i => nomatch i
  | .lowerRight i =>
      -((uiqbotCanonicalLowerRightIndexEquivX
        w hfin htrans hR hL0 i : ℕ) : ℤ) - 1
  | .lowerLeft i => nomatch i
































end DirectedDistances.PaperProofs.Section4

end
