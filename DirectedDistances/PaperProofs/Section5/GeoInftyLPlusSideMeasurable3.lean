/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable2
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSide

/-! # Marked block comparison for the nonnegative left presentation

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. Equal coherent left-side codes give a marked
isomorphism of the hatted blocks. -/
theorem lPlusHattedSide_markedIso_of_eq (x : XDP)
    (q q' : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (hc : thinSideCode x renewalTime renewalTime_positiveSuccessTime .left q.1 =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .left q'.1) :
    Nonempty (GeometricSideMarkedIso
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q')) :=
  leftSideCode_markedIso_of_eq x q q' hc

local notation "Code" => (ℕ → Fin 3) × (ℕ → Option FiniteThinMap) × (ℕ → Fin 3)

/-- Helper toward Lemma 5.5. Equal presentation codes force equality of the
stopped-prefix, coherent hatted, and primed code coordinates of their source
witnesses. -/
theorem lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r)
    (s' : LPlusSidePresentationSourceWitness x k r')
    (hr : r.code = r'.code) :
    boundaryPrefixCode k s.W = boundaryPrefixCode k s'.W ∧
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
        (boundaryFutureHattedPath k s.W) =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
        (boundaryFutureHattedPath k s'.W) ∧
      hatLawPrimedCodes (boundaryFutureCode k s.W) =
        hatLawPrimedCodes (boundaryFutureCode k s'.W) := by
  refine ⟨?_, ?_, ?_⟩
  · exact s.prefixCode_eq.trans
      ((congrArg (fun c : Code => c.1) hr).trans s'.prefixCode_eq.symm)
  · exact s.coherentCode_eq.trans
      ((congrArg (fun c : Code => c.2.1) hr).trans s'.coherentCode_eq.symm)
  · exact s.primedCode_eq.trans
      ((congrArg (fun c : Code => c.2.2) hr).trans s'.primedCode_eq.symm)

end DirectedDistances.PaperProofs.Section5



























