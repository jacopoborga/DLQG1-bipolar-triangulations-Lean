/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole4

/-! This module transports finite-prefix rotation through the natural-number
quotient decoder. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The decoded natural-number rotation relation is exactly the code-dart permutation relation. -/
theorem rMinusDecodedSideOfBlocks_rotation_iff
    (F : State) (M : GeometricSideSubmap)
    (R : Equiv.Perm (RMinusCodeGluedDart F M))
    (a b : RMinusCodeGluedDart F M) :
    (rMinusDecodedSideOfBlocks F M R).rotation
      (rMinusCodeDartId F M a) (rMinusCodeDartId F M b) ↔ R a = b := by
  change (∃ c d : RMinusCodeGluedDart F M,
      rMinusCodeDartId F M c = rMinusCodeDartId F M a ∧
      rMinusCodeDartId F M d = rMinusCodeDartId F M b ∧ R c = d) ↔ R a = b
  constructor
  · rintro ⟨c, d, hc, hd, hR⟩
    have hca : c = a := (rMinusCodeDartId_injective F M).eq_iff.mp hc
    have hdb : d = b := (rMinusCodeDartId_injective F M).eq_iff.mp hd
    simpa [hca, hdb] using hR
  · intro h
    exact ⟨a, b, rfl, rfl, h⟩


/-- Helper toward Lemma 5.5. On prefix darts, the natural-number decoded
rotation relation is exactly the adjusted quotient-dart rotation. -/
theorem rMinusDecodedSideOfBlocks_prefix_rotation_iff
    (w : ℕ → Fin 3) (n : ℕ) {x : XDP} (q : Coherent x)
    (a b : StageDart (kmswStage w n).nextEdge) :
    (rMinusDecodedSideOfBlocks (kmswStage w n)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
      (rMinusCodeInitialAdjustedRotation w n q)).rotation
      (rMinusCodeDartId (kmswStage w n)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
        (rMinusCodePrefixDart (kmswStage w n)
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q) a))
      (rMinusCodeDartId (kmswStage w n)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
        (rMinusCodePrefixDart (kmswStage w n)
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q) b)) ↔
    rMinusCodeInitialAdjustedRotation w n q
      (rMinusCodePrefixDart (kmswStage w n)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q) a) =
      rMinusCodePrefixDart (kmswStage w n)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q) b := by
  rw [← rMinusDecodedDartEquiv_val w n q
      (rMinusCodePrefixDart (kmswStage w n)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q) a),
    ← rMinusDecodedDartEquiv_val w n q
      (rMinusCodePrefixDart (kmswStage w n)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q) b)]
  exact rMinusDecodedSideOfBlocks_rotation_iff _ _ _ _ _




































































end DirectedDistances.PaperProofs.Section5
