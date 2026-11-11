module

public import DirectedDistances.KMSW.FutureMapHatLawShift
public import DirectedDistances.KMSW.RPhaseLawTransfer
public import DirectedDistances.PaperProofs.Section5.DirectedContainMapClause

/-! # The hatted half of the future-map law

This file identifies the shifted hatted code law and the rooted hatted map
clause. The primed map identification, which is the primed half of Lemma 5.13,
is not included; consequently these results do not prove Proposition 5.1. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk

/-- At every integer shift, the hatted future-code law is the iid Pitman-code -/
theorem futureMapShifted_hatCode_law_pitman (n : ℤ) :
    wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ futureMapShiftedCodePath n) =
      iidCodeMeasure.map (fun w => pitmanCode (fun i => w (i + 1))) := by
  have hm : AEMeasurable hatLawCodes
      (wholePlaneIIDCodeMeasure.map (futureMapShiftedCodePath n)) := by
    rw [futureMapShiftedCodePath_law]
    exact aemeasurable_hatLawCodes.1
  calc
    wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ futureMapShiftedCodePath n) =
        (wholePlaneIIDCodeMeasure.map (futureMapShiftedCodePath n)).map
          hatLawCodes := by
            rw [← hm.map_map_of_aemeasurable
              (measurable_futureMapShiftedCodePath n).aemeasurable]
    _ = iidCodeMeasure.map hatLawCodes := by
      rw [futureMapShiftedCodePath_law]
    _ = iidCodeMeasure.map (fun w => pitmanCode (fun i => w (i + 1))) := by
      rw [Measure.map_congr hatLawCodes_ae_eq_rCodeSequence]
      exact map_rCodeSequence

/-- A one-sided iid code stream almost surely has the full rooted hatted-map -/
private theorem iidCodes_ae_hatRootedMapClause :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ (h : HasFlowLineHits (fun i => ω (i + 1)))
        (hfin : hatLimitFiniteIncidence (fun i => ω (i + 1))),
        hatRootedMapClause (fun i => ω (i + 1)) h hfin := by
  filter_upwards [iidCodes_ae_hatRootedMapIdentification] with ω hω
  dsimp only at hω
  obtain ⟨h, hfin, _, hclause⟩ := hω
  exact ⟨h, hfin, hclause⟩

/-- At every integer shift, the raw stream is the tail of the padded future
code path and is exactly the zero-start shifted stream of the translated -/
theorem futureMapShiftedCodePath_rawStream (n : ℤ) (W : ℤ → Fin 3) :
    (fun i => futureMapShiftedCodePath n W (i + 1)) =
      shiftedStream (fun k => W (k + n)) 0 := by
  rw [futureMapShiftedCodePath_tail]
  rfl

/-- For every integer time shift, the raw future stream has a rooted hatted
map identification on one common almost-sure event. The displayed stream
identity preserves the source convention: it is the zero-start stream of the -/
theorem wholePlane_ae_futureMapShift_hatRootedMap :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ,
      let u := fun i => futureMapShiftedCodePath n W (i + 1)
      u = shiftedStream (fun k => W (k + n)) 0 ∧
        ∃ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
          hatLawCodes (futureMapShiftedCodePath n W) = hatCodes u hτ ∧
            hatRootedMapClause u hτ hfin := by
  apply ae_all_iff.mpr
  intro n
  have hmap : ∀ᵐ ω ∂wholePlaneIIDCodeMeasure.map (futureMapShiftedCodePath n),
      ∃ (h : HasFlowLineHits (fun i => ω (i + 1)))
        (hfin : hatLimitFiniteIncidence (fun i => ω (i + 1))),
        hatRootedMapClause (fun i => ω (i + 1)) h hfin := by
    rw [futureMapShiftedCodePath_law n]
    exact iidCodes_ae_hatRootedMapClause
  have hpull := (Measure.tendsto_ae_map
    (measurable_futureMapShiftedCodePath n).aemeasurable).eventually hmap
  filter_upwards [hpull] with W hW
  let u := fun i => futureMapShiftedCodePath n W (i + 1)
  have hWu : ∃ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
      hatRootedMapClause u hτ hfin := by
    exact hW
  refine ⟨futureMapShiftedCodePath_rawStream n W, ?_⟩
  obtain ⟨hτ, hfin, hclause⟩ := hWu
  refine ⟨hτ, hfin, ?_, hclause⟩
  have hraw : HasFlowLineHits
      (fun i => futureMapShiftedCodePath n W (i + 1)) := hτ
  simp only [hatLawCodes, dite_eq_left hraw]

/-- The hatted part of the future-map statement at every integer shift,
together with the common-event rooted identification and the code independence
from `prop_5_1_code_laws`. The primed map identification (the primed half of
Lemma 5.13) is not included, so this statement is not Proposition 5.1 -/
@[expose] def prop51HattedStatement : Prop :=
  (∀ n : ℤ,
    wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ futureMapShiftedCodePath n) =
      iidCodeMeasure.map (fun w => pitmanCode (fun i => w (i + 1)))) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℤ,
      let u := fun i => futureMapShiftedCodePath n W (i + 1)
      u = shiftedStream (fun k => W (k + n)) 0 ∧
        ∃ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
          hatLawCodes (futureMapShiftedCodePath n W) = hatCodes u hτ ∧
            hatRootedMapClause u hτ hfin) ∧
    (∀ n : ℤ,
      (hatLawCodes ∘ futureMapShiftedCodePath n) ⟂ᵢ[wholePlaneIIDCodeMeasure]
        (hatLawPrimedCodes ∘ futureMapShiftedCodePath n))

/-- The hatted code-law and rooted-map clauses hold at all integer shifts, -/
theorem prop51Hatted_holds : prop51HattedStatement := by
  exact ⟨futureMapShifted_hatCode_law_pitman,
    wholePlane_ae_futureMapShift_hatRootedMap,
    fun n => (prop_5_1_code_laws n).2.2.2⟩

end DirectedDistances.PaperProofs.Section5
