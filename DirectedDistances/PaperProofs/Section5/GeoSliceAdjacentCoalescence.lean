/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.BusemannClsLeftmost

/-! # Almost-sure adjacent least coalescence -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1




theorem m0Cut_ae_leftmost_xdp_adjacent_least_coalescence :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ R : ℤ → KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
        (∀ k, (R k).vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
          (T k).edge = (R k).edge ∧
          (∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
            ((T k).initial n).1.id ((T k).edge n))) ∧
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        (∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k) ∧
        ∀ m : ℤ, ∃ a b : ℕ,
          M0CutLeastEdgeCoalescence (P m) (P (m + 1)) a b := by
  filter_upwards [m0Cut_ae_leftmost_xdp_least_coalescence] with W hW
  obtain ⟨H, h, hLL, hp, hselected⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨R, T, P, hR, hleft, huniq, hleast⟩ := hselected longest
  refine ⟨R, T, P, hR, hleft, huniq, ?_⟩
  intro m
  obtain ⟨q, hq, _⟩ := hleast (m + 1)
  have hm : (m + 1 : ℤ) - 1 = m := by omega
  rw [hm] at hq
  refine ⟨q.2, q.1, ?_⟩
  constructor
  · intro n
    exact (hq.1 n).symm
  · intro a b hab
    have hab' : M0CutEdgeTailsCoalesce (P (m + 1)) (P m) b a := by
      intro n
      exact (hab n).symm
    have hmin := hq.2 b a hab'
    exact ⟨hmin.2, hmin.1⟩

/-- The selected family in the preceding almost-sure theorem is characterized
among all leftmost families by the pointwise uniqueness clause inherited from
`m0Cut_ae_leftmost_xdp_least_coalescence`. -/
theorem m0Cut_ae_selected_leftmost_family_unique_statement :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      ∃ hp : BoundaryHitWitnesses (kmswPastCode W),
      ∀ longest : Bool,
      ∃ P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest,
      ∃ T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
        (boundaryPresentVertex (shiftedStream W 0) h k),
        (∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k)) ∧
        ∀ k Q, Xdp.CutLeftmostXdp W H h hp hLL longest k Q (T k) → Q = P k := by
  filter_upwards [m0Cut_ae_leftmost_xdp_least_coalescence] with W hW
  obtain ⟨H, h, hLL, hp, hselected⟩ := hW
  refine ⟨H, h, hLL, hp, fun longest => ?_⟩
  obtain ⟨_, T, P, _, hleft, huniq, _⟩ := hselected longest
  exact ⟨P, T, hleft, huniq⟩






















end DirectedDistances.PaperProofs.Section5
