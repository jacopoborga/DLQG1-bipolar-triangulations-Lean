/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable3

/-! # Mode-aligned witnesses for the nonnegative left presentation

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime
local notation "Code" => (ℕ → Fin 3) × (ℕ → Option FiniteThinMap) × (ℕ → Fin 3)

/-- Helper toward Lemma 5.5. A mode-aligned witness retains every field of
the source presentation witness and certifies that its `longest`-selected
coherent domain is the fixed domain indexed by `x`. -/
structure LPlusSourceWitnessAligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) extends
    LPlusSidePresentationSourceWitness x k r where
  hmode : (if longest then XDP.ldp else XDP.sdp) = x

/-- Helper toward Lemma 5.5. Alignment transports a witness's hatted path to
the common coherent domain indexed by the fixed `x`. -/
theorem LPlusSourceWitnessAligned.hattedPath_mem
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) :
    boundaryFutureHattedPath k s.W ∈ Coherent x := by
  simpa only [s.hmode] using s.hqMode

/-- Helper toward Lemma 5.5. The aligned realization is defined only on the
nonnegative-index and source-witness guard, and is absent outside that guard.
On the guard it uses the source witness's code-built side, with no default
side. -/
@[expose] noncomputable def lPlusAlignedSidePresentationRealization
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x) :
    Option GeometricSideSubmap :=
  if hk : 0 ≤ k then
    if hw : Nonempty (LPlusSourceWitnessAligned x k r) then
      let s := Classical.choice hw
      some (lPlusCodeBlockSide (W := s.W) (h := s.h) (k := k) (H := s.H)
        (hLL := s.hLL) (longest := s.longest) s.hτ s.hp s.P s.hqMode
        s.Tpath s.hfin s.hleft hk)
    else none
  else none

/-- Helper toward Lemma 5.5. A negative index is outside the realization
guard. -/
theorem lPlusAlignedSidePresentationRealization_eq_none_of_not_nonneg
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x) (hk : ¬ 0 ≤ k) :
    lPlusAlignedSidePresentationRealization x k r = none := by
  simp [lPlusAlignedSidePresentationRealization, hk]

/-- Helper toward Lemma 5.5. A presentation with no aligned source witness is
outside the realization guard. -/
theorem lPlusAlignedSidePresentationRealization_eq_none_of_no_witness
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (hk : 0 ≤ k) (hw : ¬ Nonempty (LPlusSourceWitnessAligned x k r)) :
    lPlusAlignedSidePresentationRealization x k r = none := by
  simp [lPlusAlignedSidePresentationRealization, hk, hw]

/-- Helper toward Lemma 5.5. On the aligned realization guard, the chosen
source witness returns its `lPlusCodeBlockSide`. -/
theorem lPlusAlignedSidePresentationRealization_eq_some_lPlusCodeBlockSide
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (hk : 0 ≤ k) (hw : Nonempty (LPlusSourceWitnessAligned x k r)) :
    lPlusAlignedSidePresentationRealization x k r =
      some (lPlusCodeBlockSide
        (W := (Classical.choice hw).W) (h := (Classical.choice hw).h)
        (k := k) (H := (Classical.choice hw).H)
        (hLL := (Classical.choice hw).hLL)
        (longest := (Classical.choice hw).longest)
        (Classical.choice hw).hτ (Classical.choice hw).hp
        (Classical.choice hw).P (Classical.choice hw).hqMode
        (Classical.choice hw).Tpath (Classical.choice hw).hfin
        (Classical.choice hw).hleft hk) := by
  simp [lPlusAlignedSidePresentationRealization, hk, hw]

/-- Helper toward Lemma 5.5. Equal presentation codes give equal hatted codes
for aligned source witnesses, now in one common coherent domain. -/
theorem lPlusSourceWitnessAligned_hattedCode_eq_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) :
    thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
        (boundaryFutureHattedPath k s.W) =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
        (boundaryFutureHattedPath k s'.W) := by
  exact s.coherentCode_eq.trans
    ((congrArg (fun c : Code => c.2.1) hr).trans s'.coherentCode_eq.symm)

/-- Helper toward Lemma 5.5. Equal presentation codes for aligned source
witnesses yield a marked isomorphism between their hatted sides in the common
coherent domain indexed by `x`. -/
theorem lPlusSourceWitnessAligned_hatted_markedIso_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) :
    Nonempty (GeometricSideMarkedIso
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left
        (⟨boundaryFutureHattedPath k s.W, s.hattedPath_mem⟩ : Coherent x))
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left
        (⟨boundaryFutureHattedPath k s'.W, s'.hattedPath_mem⟩ : Coherent x))) := by
  let q : Coherent x := ⟨boundaryFutureHattedPath k s.W, s.hattedPath_mem⟩
  let q' : Coherent x := ⟨boundaryFutureHattedPath k s'.W, s'.hattedPath_mem⟩
  apply lPlusHattedSide_markedIso_of_eq x q q'
  exact lPlusSourceWitnessAligned_hattedCode_eq_of_presentation_codes_eq
    x k r r' s s' hr























end DirectedDistances.PaperProofs.Section5
