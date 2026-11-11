/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.FutureMapLawHatted
public import DirectedDistances.PaperProofs.Section5.QuadKMSWIdentified
import DirectedDistances.PaperProofs.Section5.FutureMapLawPrimed

/-! # The identified future-map law

independence and equality of generating-code laws together with both full
rooted planar-map identifications. One almost-sure event supplies these
identifications at every integer shift, with literal code identities.
The primed clause retains the missing, unoriented root under C18 and the
first-triangle convention under initial triangle convention.

final kernel validation remain separate. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk

/-- The full primed rooted-map clause and its literal code identity hold
at every integer shift on one common almost-sure event. The iid witnesses
come from the joint identification of Lemma 5.13, with no geometric premise -/
theorem wholePlane_ae_futureMapShift_primedRootedMap :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ,
      let u := fun i => futureMapShiftedCodePath n W (i + 1)
      ∃ (h : HasFlowLineHits u) (hfin : primedLimitFiniteIncidence u)
        (hb : BoundaryHitWitnesses u),
        hatLawPrimedCodes (futureMapShiftedCodePath n W) =
          primedCode (primedSimInput u) h ∧
        primedRootedMapClause u h hfin hb := by
  have hP : ∀ᵐ ω ∂iidCodeMeasure,
      ∃ (h : HasFlowLineHits (fun i => ω (i + 1)))
        (hfin : primedLimitFiniteIncidence (fun i => ω (i + 1)))
        (hb : BoundaryHitWitnesses (fun i => ω (i + 1))),
        primedRootedMapClause (fun i => ω (i + 1)) h hfin hb := by
    filter_upwards [lemma513_holds] with ω hω
    obtain ⟨h, _hfin_hat, hfin, hb, _hwalk_hat, _hwalk_primed,
      _hhat, hprimed⟩ := hω
    exact ⟨h, hfin, hb, hprimed⟩
  have htransfer := wholePlane_ae_futureMapShift_rawStream_of_iid_ae
    (P := fun u => ∃ (h : HasFlowLineHits u)
      (hfin : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u),
      primedRootedMapClause u h hfin hb) hP
  filter_upwards [htransfer] with W hW
  intro n
  obtain ⟨⟨h, hfin, hb, hclause⟩, _hraw⟩ := hW n
  exact ⟨h, hfin, hb,
    futureMapShift_hatLawPrimedCodes_eq_primedCode n W h, hclause⟩

/-- codes of the two future submaps are independent at each integer shift, and
the hatted code has the UIQBOT Pitman-code law. Both codes identify their
full rooted geometric maps on one common event for all shifts. The two
map clauses share the flow-hit witness and the displayed raw stream. -/
@[expose] def prop51Statement : Prop :=
  (∀ n : ℤ,
    (hatLawCodes ∘ futureMapShiftedCodePath n) ⟂ᵢ[wholePlaneIIDCodeMeasure]
      (hatLawPrimedCodes ∘ futureMapShiftedCodePath n)) ∧
  (∀ n : ℤ,
    wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ futureMapShiftedCodePath n) =
      iidCodeMeasure.map (fun w => pitmanCode (fun i => w (i + 1)))) ∧
  (∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ,
    let u := fun i => futureMapShiftedCodePath n W (i + 1)
    u = shiftedStream (fun k => W (k + n)) 0 ∧
      ∃ (h : HasFlowLineHits u) (hfin_hat : hatLimitFiniteIncidence u)
        (hfin_primed : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u),
        hatLawCodes (futureMapShiftedCodePath n W) = hatCodes u h ∧
        hatLawPrimedCodes (futureMapShiftedCodePath n W) =
          primedCode (primedSimInput u) h ∧
        hatRootedMapClause u h hfin_hat ∧
        primedRootedMapClause u h hfin_primed hb)

/-- The code-law and joint rooted-map formulation of Proposition 5.1 holds -/
theorem prop51_holds : prop51Statement := by
  refine ⟨fun n => (prop_5_1_code_laws n).2.2.2,
    futureMapShifted_hatCode_law_pitman, ?_⟩
  filter_upwards [wholePlane_ae_futureMapShift_hatRootedMap,
    wholePlane_ae_futureMapShift_primedRootedMap] with W hhat hprimed
  intro n
  obtain ⟨hraw, h, hfin_hat, hcode_hat, hclause_hat⟩ := hhat n
  obtain ⟨hprimed, hfin_primed, hb, hcode_primed, hclause_primed⟩ := hprimed n
  exact ⟨hraw, h, hfin_hat, hfin_primed, hb,
    hcode_hat, hcode_primed, hclause_hat, hclause_primed⟩

end DirectedDistances.PaperProofs.Section5
