module

public import DirectedDistances.KMSW.FutureMapHatLaw
public import DirectedDistances.RandomWalk.TwoSidedIIDCodeMeasure

/-! Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.

The integer-start raw stream is the stage-zero stream of the translated two-sided
word. The existing one-sided law has a deterministic dummy coordinate at zero,
so its representative inserts that coordinate before applying the hatted and
primed observations. These are code-law statements; geometric identification -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory ProbabilityTheory
open DirectedDistances.RandomWalk

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The raw KMSW stream starting at integer time `n`. -/
@[expose] def futureMapShiftedStream (n : ℤ) (W : ℤ → Fin 3) : ℕ → Fin 3 :=
  shiftedStream (fun k => W (k + n)) 0

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The integer-start stream reads precisely the codes from time `n` onward. -/
theorem futureMapShiftedStream_apply (n : ℤ) (W : ℤ → Fin 3) (i : ℕ) :
    futureMapShiftedStream n W i = W ((i : ℤ) + n) := by
  simp only [futureMapShiftedStream, shiftedStream, Nat.cast_zero, sub_zero]

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Negative natural starts agree with the existing colimit stream convention. -/
theorem futureMapShiftedStream_neg_nat (N : ℕ) (W : ℤ → Fin 3) :
    futureMapShiftedStream (-(N : ℤ)) W = shiftedStream W N := by
  funext i
  simp only [futureMapShiftedStream_apply, shiftedStream, sub_eq_add_neg]

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The integer-start code path includes the one-sided law's dummy coordinate. -/
@[expose] def futureMapShiftedCodePath (n : ℤ) (W : ℤ → Fin 3) : ℕ → Fin 3 :=
  shiftedCodePath (fun k => W (k + n)) 0

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Removing the dummy coordinate recovers the raw integer-start KMSW stream. -/
theorem futureMapShiftedCodePath_tail (n : ℤ) (W : ℤ → Fin 3) :
    (fun i => futureMapShiftedCodePath n W (i + 1)) = futureMapShiftedStream n W := by
  funext i
  simp only [futureMapShiftedCodePath, shiftedCodePath, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel, futureMapShiftedStream]

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Integer translation of the two-sided code word is measurable. -/
theorem measurable_futureMapCodeShift (n : ℤ) :
    Measurable (fun W : ℤ → Fin 3 => fun k : ℤ => W (k + n)) := by
  exact Measurable.of_eval fun k => measurable_pi_apply (k + n)

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Integer translation preserves the two-sided iid code measure. -/
theorem measurePreserving_futureMapCodeShift (n : ℤ) :
    MeasurePreserving (fun W : ℤ → Fin 3 => fun k : ℤ => W (k + n))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure :=
  ⟨measurable_futureMapCodeShift n, wholePlaneIIDCodeMeasure_map_shift n⟩

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The raw integer-start stream is measurable. -/
theorem measurable_futureMapShiftedStream (n : ℤ) :
    Measurable (futureMapShiftedStream n) := by
  exact Measurable.of_eval fun i => by
    simpa only [futureMapShiftedStream_apply] using
      (measurable_pi_apply ((i : ℤ) + n) :
        Measurable (fun W : ℤ → Fin 3 => W ((i : ℤ) + n)))

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The padded integer-start code path is measurable. -/
theorem measurable_futureMapShiftedCodePath (n : ℤ) :
    Measurable (futureMapShiftedCodePath n) :=
  (measurable_shiftedCodePath 0).comp (measurable_futureMapCodeShift n)

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Every integer-start raw stream has the uniform one-sided product law. -/
theorem futureMapShiftedStream_law (n : ℤ) :
    wholePlaneIIDCodeMeasure.map (futureMapShiftedStream n) =
      Measure.infinitePi (fun _ : ℕ => uniformCodeMeasure) := by
  have hzero : Measurable (fun W : ℤ → Fin 3 => shiftedStream W 0) := by
    exact Measurable.of_eval fun i => by
      simpa only [shiftedStream, Nat.cast_zero, sub_zero] using
        (measurable_pi_apply (i : ℤ) : Measurable (fun W : ℤ → Fin 3 => W i))
  change wholePlaneIIDCodeMeasure.map
    ((fun W : ℤ → Fin 3 => shiftedStream W 0) ∘
      (fun W : ℤ → Fin 3 => fun k : ℤ => W (k + n))) = _
  rw [← Measure.map_map hzero (measurable_futureMapCodeShift n),
    wholePlaneIIDCodeMeasure_map_shift n]
  exact wholePlaneIIDCodeMeasure_map_shiftedStream 0

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Every integer-start padded code path has exactly the existing one-sided iid law. -/
theorem futureMapShiftedCodePath_law (n : ℤ) :
    wholePlaneIIDCodeMeasure.map (futureMapShiftedCodePath n) = iidCodeMeasure := by
  change wholePlaneIIDCodeMeasure.map
    ((fun W : ℤ → Fin 3 => shiftedCodePath W 0) ∘
      (fun W : ℤ → Fin 3 => fun k : ℤ => W (k + n))) = _
  rw [← Measure.map_map (measurable_shiftedCodePath 0)
    (measurable_futureMapCodeShift n), wholePlaneIIDCodeMeasure_map_shift n]
  exact wholePlaneIIDCodeMeasure_map_shiftedPath 0

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The shifted observations are explicitly almost-everywhere measurable. -/
theorem aemeasurable_futureMapShiftedHatCodes (n : ℤ) :
    AEMeasurable (hatLawCodes ∘ futureMapShiftedCodePath n) wholePlaneIIDCodeMeasure ∧
      AEMeasurable (hatLawPrimedCodes ∘ futureMapShiftedCodePath n)
        wholePlaneIIDCodeMeasure := by
  have hu : AEMeasurable hatLawCodes
      (wholePlaneIIDCodeMeasure.map (futureMapShiftedCodePath n)) := by
    rw [futureMapShiftedCodePath_law]
    exact aemeasurable_hatLawCodes.1
  have hp : AEMeasurable hatLawPrimedCodes
      (wholePlaneIIDCodeMeasure.map (futureMapShiftedCodePath n)) := by
    rw [futureMapShiftedCodePath_law]
    exact aemeasurable_hatLawCodes.2
  exact ⟨hu.comp_measurable (measurable_futureMapShiftedCodePath n),
    hp.comp_measurable (measurable_futureMapShiftedCodePath n)⟩

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
Transfer of an almost-everywhere measurable code observation along the padded stream. -/
private theorem futureMapShiftedCodePath_map {α : Type*} [MeasurableSpace α]
    (n : ℤ) (f : (ℕ → Fin 3) → α) (hf : AEMeasurable f iidCodeMeasure) :
    wholePlaneIIDCodeMeasure.map (f ∘ futureMapShiftedCodePath n) =
      iidCodeMeasure.map f := by
  have hm : AEMeasurable f
      (wholePlaneIIDCodeMeasure.map (futureMapShiftedCodePath n)) := by
    rw [futureMapShiftedCodePath_law]
    exact hf
  rw [← hm.map_map_of_aemeasurable
    (measurable_futureMapShiftedCodePath n).aemeasurable,
    futureMapShiftedCodePath_law]

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The unprimed hatted observation at every integer start has the UIQBOT code law. -/
theorem futureMapShiftedHatCodes_law (n : ℤ) :
    wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ futureMapShiftedCodePath n) =
      (conditionedVectorPathLaw 0 0).map hatLawPathCodes := by
  rw [futureMapShiftedCodePath_map n hatLawCodes aemeasurable_hatLawCodes.1]
  exact hatLawCodes_law

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The integrated hatted codes at every integer start have the full conditioned path law. -/
theorem futureMapShiftedHatCodes_integrate_law (n : ℤ) :
    wholePlaneIIDCodeMeasure.map
        (fun W => integrateCodes (hatLawCodes (futureMapShiftedCodePath n W))) =
      conditionedVectorPathLaw 0 0 := by
  have hi : Measurable integrateCodes := by
    apply Measurable.of_eval
    intro j
    exact (Finset.range j).measurable_sum fun i _ =>
      (measurable_of_countable lazyTwoDimensionalStep).comp (measurable_pi_apply i)
  change wholePlaneIIDCodeMeasure.map
    ((fun ω => integrateCodes (hatLawCodes ω)) ∘ futureMapShiftedCodePath n) = _
  rw [futureMapShiftedCodePath_map n (fun ω => integrateCodes (hatLawCodes ω))
    (hi.comp_aemeasurable aemeasurable_hatLawCodes.1)]
  exact hatLawCodes_integrate_law

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The hatted and primed observations of each integer-start stream are independent. -/
theorem futureMapShiftedHatCodes_indep (n : ℤ) :
    (hatLawCodes ∘ futureMapShiftedCodePath n) ⟂ᵢ[wholePlaneIIDCodeMeasure]
      (hatLawPrimedCodes ∘ futureMapShiftedCodePath n) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (aemeasurable_futureMapShiftedHatCodes n).1
    (aemeasurable_futureMapShiftedHatCodes n).2).2
  change wholePlaneIIDCodeMeasure.map
    ((fun ω => (hatLawCodes ω, hatLawPrimedCodes ω)) ∘ futureMapShiftedCodePath n) = _
  rw [futureMapShiftedCodePath_map n _
    (aemeasurable_hatLawCodes.1.prodMk aemeasurable_hatLawCodes.2),
    futureMapShiftedCodePath_map n hatLawCodes aemeasurable_hatLawCodes.1,
    futureMapShiftedCodePath_map n hatLawPrimedCodes aemeasurable_hatLawCodes.2]
  exact hatLawCodes_indep.map_prod_eq_prod_map_map
    aemeasurable_hatLawCodes.1 aemeasurable_hatLawCodes.2

/-- Helper toward Proposition 5.1 (prop-future-map-law); not a paper result.
The integer-start iid, hatted code and integrated path laws, and code independence,
bundled for every `n : ℤ`. This does not assert the remaining geometric identifications. -/
theorem prop_5_1_code_laws (n : ℤ) :
    wholePlaneIIDCodeMeasure.map (futureMapShiftedCodePath n) = iidCodeMeasure ∧
      wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ futureMapShiftedCodePath n) =
        (conditionedVectorPathLaw 0 0).map hatLawPathCodes ∧
      wholePlaneIIDCodeMeasure.map
          (fun W => integrateCodes (hatLawCodes (futureMapShiftedCodePath n W))) =
        conditionedVectorPathLaw 0 0 ∧
      (hatLawCodes ∘ futureMapShiftedCodePath n) ⟂ᵢ[wholePlaneIIDCodeMeasure]
        (hatLawPrimedCodes ∘ futureMapShiftedCodePath n) :=
  ⟨futureMapShiftedCodePath_law n, futureMapShiftedHatCodes_law n,
    futureMapShiftedHatCodes_integrate_law n, futureMapShiftedHatCodes_indep n⟩

end DirectedDistances.KMSW
