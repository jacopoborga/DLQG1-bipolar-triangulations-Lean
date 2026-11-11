/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusCanonicalCoding2

/-! Measurability helpers for the canonical nonpositive R-minus coding, -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. Equal coherent right-side codes give the same
class for the least-token canonical sides, independently of the selected
coherent-path witness. -/
theorem rMinusCanonicalSide_class_eq_of_thinSideCode_eq
    (x : XDP) (w : ℕ → Fin 3) (n : ℕ) (q q' : Coherent x)
    (hc : thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q'.1) :
    geometricSideClass (rMinusCanonicalSide w n q) =
      geometricSideClass (rMinusCanonicalSide w n q') := by
  calc
    geometricSideClass (rMinusCanonicalSide w n q) =
        geometricSideClass (rMinusDecodedSide w n q) :=
      rMinusCanonicalSide_class_eq_decodedSide w n q
    _ = geometricSideClass (rMinusDecodedSide w n q') := by
      rw [rMinusDecodedSide_eq_ofBlocks w n q,
        rMinusDecodedSide_eq_ofBlocks w n q']
      exact (geometricSideClass_eq_iff _ _).mpr
        (rMinusDecodedSideOfBlocks_markedIso_of_eq x w n q q' hc)
    _ = geometricSideClass (rMinusCanonicalSide w n q') :=
      (rMinusCanonicalSide_class_eq_decodedSide w n q').symm




















































































end DirectedDistances.PaperProofs.Section5
