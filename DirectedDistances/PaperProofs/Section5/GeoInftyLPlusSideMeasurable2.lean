/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable

/-! # Guarded realization of the nonnegative left presentation

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Code" => (ℕ → Fin 3) × (ℕ → Option FiniteThinMap) × (ℕ → Fin 3)
local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. A source witness for a nonnegative left
presentation retains valid prefix witnesses and identifies each of the three
observed code coordinates with its source code. The second coordinate is
required to come from the coherent hatted left path. -/
structure LPlusSidePresentationSourceWitness (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) where
  W : ℤ → Fin 3
  h : BoundaryHitWitnesses (shiftedStream W 0)
  H : WholePlaneRotationHypothesis W
  hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))
  longest : Bool
  hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)
  hp : BoundaryHitWitnesses (kmswPastCode W)
  P : M0CutInfiniteGeodesic W H h hLL k longest
  hqMode : boundaryFutureHattedPath k W ∈ Coherent
    (if longest then XDP.ldp else XDP.sdp)
  Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k)
  hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)
  hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath
  prefixCode_eq : boundaryPrefixCode k W = r.code.1
  coherentCode_eq : thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
    (boundaryFutureHattedPath k W) = r.code.2.1
  primedCode_eq : hatLawPrimedCodes (boundaryFutureCode k W) = r.code.2.2

/-- Helper toward Lemma 5.5. A presentation has a realization only when its
boundary index is nonnegative and it has source witnesses for the stopped
prefix, coherent hatted code, and primed code. The chosen realization is the
code-built side with its permanent geometric IDs; all failed guards return
`none`. -/
@[expose] noncomputable def lPlusSidePresentationRealization
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x) :
    Option GeometricSideSubmap :=
  if hk : 0 ≤ k then
    if hw : Nonempty (LPlusSidePresentationSourceWitness x k r) then
      let s := Classical.choice hw
      some (lPlusCodeBlockSide (W := s.W) (h := s.h) (k := k) (H := s.H)
        (hLL := s.hLL) (longest := s.longest) s.hτ s.hp s.P s.hqMode
        s.Tpath s.hfin s.hleft hk)
    else none
  else none

/-- Helper toward Lemma 5.5. On the realization guard, the reader returns the
code-built side from the selected source witnesses. -/
theorem lPlusSidePresentationRealization_eq_some_lPlusCodeBlockSide
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (hk : 0 ≤ k) (hw : Nonempty (LPlusSidePresentationSourceWitness x k r)) :
    lPlusSidePresentationRealization x k r =
      some (lPlusCodeBlockSide
        (W := (Classical.choice hw).W) (h := (Classical.choice hw).h)
        (k := k) (H := (Classical.choice hw).H)
        (hLL := (Classical.choice hw).hLL)
        (longest := (Classical.choice hw).longest)
        (Classical.choice hw).hτ (Classical.choice hw).hp
        (Classical.choice hw).P (Classical.choice hw).hqMode
        (Classical.choice hw).Tpath (Classical.choice hw).hfin
        (Classical.choice hw).hleft hk) := by
  simp [lPlusSidePresentationRealization, hk, hw]








































end DirectedDistances.PaperProofs.Section5
