/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55FMapsAE
public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusSideMeasurable9

/-! Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. For a fixed prefix code, the complete decoded
R-minus marked-isomorphism class is constant on equal coherent thin codes. -/
theorem rMinusDecodedSideOfBlocks_class_eq_of_thinSideCode_eq
    (x : XDP) (w : ℕ → Fin 3) (n : ℕ)
    (q q' : Coherent x)
    (hc : thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q'.1) :
    geometricSideClass
        (rMinusDecodedSideOfBlocks (kmswStage w n)
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
          (rMinusCodeInitialAdjustedRotation w n q)) =
      geometricSideClass
        (rMinusDecodedSideOfBlocks (kmswStage w n)
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q')
          (rMinusCodeInitialAdjustedRotation w n q')) := by
  exact (geometricSideClass_eq_iff _ _).2
    (rMinusDecodedSideOfBlocks_markedIso_of_eq x w n q q' hc)

/-- Helper toward Lemma 5.5. The coherent thin-side code is measurable on the
selected coherent domain. -/
theorem measurable_RMinusCoherentThinSideCode (x : XDP) :
    Measurable (fun q : Coherent x =>
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1) :=
  (measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .right).comp
    measurable_subtype_coe























end DirectedDistances.PaperProofs.Section5
