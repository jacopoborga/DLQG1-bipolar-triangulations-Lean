/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusSideMeasurable3
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole3
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideMarkedIso

/-! # Measurability for the nonpositive right-side construction

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`),

The coordinate measurability theorems for the coherent hatted right side in
`GeoInftyRPlusSideMeasurable3` have no boundary-index binder or sign
hypothesis. They therefore apply to the hatted block at every integer index.
The optional hatted-side class law can also be stated for every integer,
because `boundaryFutureHattedPath_map_law` has that scope. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The optional coherent hatted right-side class
has the same law at every integer boundary index. Incoherent inputs return
`none`, using the same option-valued construction as the nonnegative result. -/
theorem geometricRightSide_class_law_eq_zero_all
    (x : XDP) (k : ℤ) :
    let F : (ℕ → ℤ × ℤ) → Option GeometricSideClass := fun p =>
      if hp : p ∈ Coherent x then
        some (geometricSideClass
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right
            ⟨p, hp⟩))
      else none
    wholePlaneIIDCodeMeasure.map (fun ω => F (boundaryFutureHattedPath k ω)) =
      wholePlaneIIDCodeMeasure.map (fun ω => F (boundaryFutureHattedPath 0 ω)) := by
  intro F
  have hF : Measurable F :=
    (measurable_some_geometricSideClass.comp (measurable_geometricRightSide_class x)).dite
      measurable_const
      (selectedCutCoherentDomain_measurable_conull x renewalTime
        renewalTime_positiveSuccessTime).1
  change wholePlaneIIDCodeMeasure.map (F ∘ boundaryFutureHattedPath k) =
    wholePlaneIIDCodeMeasure.map (F ∘ boundaryFutureHattedPath 0)
  rw [← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable
      (aemeasurable_boundaryFutureHattedPath k),
    ← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable
      (aemeasurable_boundaryFutureHattedPath 0),
    boundaryFutureHattedPath_map_law k, boundaryFutureHattedPath_map_law 0]







































end DirectedDistances.PaperProofs.Section5

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. On nonpositive indices, assemble the complete
side directly from the realized prefix and coherent hatted code. Invalid
indices or blocks have no realization; no default side is supplied. The
natural-number fields are the intrinsic permanent IDs from the code gluing. -/
@[expose] noncomputable def RMinusSidePresentation.wholeRealization
    {x : XDP} (r : RMinusSidePresentation x) : Option GeometricSideSubmap :=
  if _hk : r.boundaryIndex ≤ 0 then
    if hp : r.prefixValid then
      if hq : ∃ q : Coherent x,
          thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 = r.code.2
      then
        some (rMinusDecodedSideOfBlocks
          (kmswStage r.code.1 hp.choose)
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right
            hq.choose)
          (rMinusCodeInitialAdjustedRotation r.code.1 hp.choose hq.choose))
      else none
    else none
  else none

/-- Helper toward Lemma 5.5. The code reader agrees with the code-built
`rMinusDecodedSide`, using the same coherent preimage chosen by the reader. -/
theorem RMinusSidePresentation.wholeRealization_eq_some_rMinusDecodedSide
    {x : XDP} (r : RMinusSidePresentation x)
    (hk : r.boundaryIndex ≤ 0) (hp : r.prefixValid)
    (hq : ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 = r.code.2) :
    r.wholeRealization =
      some (rMinusDecodedSide r.code.1 hp.choose hq.choose) := by
  classical
  simp only [RMinusSidePresentation.wholeRealization,
    dite_eq_left hk, dite_eq_left hp, dite_eq_left hq]
  exact congrArg some
    (rMinusDecodedSide_eq_ofBlocks r.code.1 hp.choose hq.choose).symm





























end DirectedDistances.PaperProofs.Section5

