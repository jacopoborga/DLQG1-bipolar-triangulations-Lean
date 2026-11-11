/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusSideMeasurable

/-! # Code dependence for the nonpositive right-side class

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. Equal coherent right-side codes determine the
same marked-isomorphism class before attaching the finite prefix. -/
theorem rMinus_rightSideCode_class_eq_of_eq (x : XDP) (q q' : Coherent x)
    (hc : thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q'.1) :
    geometricSideClass
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q) =
      geometricSideClass
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q') :=
  (geometricSideClass_eq_iff _ _).2
    (rMinus_rightSideCode_markedIso_of_eq x q q' hc)






























end DirectedDistances.PaperProofs.Section5
