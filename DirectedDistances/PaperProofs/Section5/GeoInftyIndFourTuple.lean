module

public import DirectedDistances.PaperProofs.Section5.BoundaryFutureThinSides
public import DirectedDistances.Probability.FrontierIndependence

/-! # Independence at the boundary stopping time

observations of generating codes; identifying the whole glued sides is separate.
The stopping time retains `⊤` on paths which never hit the boundary level.
The existing natural-valued `boundaryCodeTime` is its `toNat` representative. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.Probability DirectedDistances.PlanarMap
open DirectedDistances.Paper.Section4 DirectedDistances.PaperProofs.Section4



@[expose] noncomputable def boundaryCodeStoppingTime (k : ℤ)
    (ω : ℕ → Fin 3) : ℕ∞ :=
  if k = 0 then 0 else if 0 < k then codeSndFirstHit (-k) ω
    else codeFstFirstHit k ω



theorem boundaryCodeStoppingTime_toNat (k : ℤ) (ω : ℕ → Fin 3) :
    (boundaryCodeStoppingTime k ω).toNat = boundaryCodeTime k ω := by
  by_cases hk0 : k = 0
  · simp only [boundaryCodeStoppingTime, boundaryCodeTime, ite_eq_left hk0, ENat.toNat_zero]
  · by_cases hk : 0 < k <;>
      simp only [boundaryCodeStoppingTime, boundaryCodeTime, ite_eq_right hk0, hk,
        ↓reduceIte]



theorem measurableSet_codePast_boundaryCodeStoppingTime_eq (k : ℤ) (j : ℕ) :
    MeasurableSet[codePast j] {ω | boundaryCodeStoppingTime k ω = j} := by
  by_cases hk0 : k = 0
  · simp only [boundaryCodeStoppingTime, ite_eq_left hk0]
    exact MeasurableSet.const _
  · by_cases hk : 0 < k
    · simpa only [boundaryCodeStoppingTime, ite_eq_right hk0, ite_eq_left hk] using
        measurableSet_codePast_codeSndFirstHit_eq (-k) j
    · simpa only [boundaryCodeStoppingTime, ite_eq_right hk0, ite_eq_right hk] using
        measurableSet_codePast_codeFstFirstHit_eq k j



theorem ae_boundaryCodeStoppingTime_lt_top (k : ℤ) :
    ∀ᵐ ω ∂iidCodeMeasure, boundaryCodeStoppingTime k ω < ⊤ := by
  by_cases hk0 : k = 0
  · exact Filter.Eventually.of_forall fun ω => by
      simp only [boundaryCodeStoppingTime, ite_eq_left hk0]
      exact ENat.natCast_lt_top 0
  · by_cases hk : 0 < k
    · simpa only [boundaryCodeStoppingTime, ite_eq_right hk0, ite_eq_left hk] using
        ae_codeSndFirstHit_lt_top_int (-k)
    · simpa only [boundaryCodeStoppingTime, ite_eq_right hk0, ite_eq_right hk] using
        ae_codeFstFirstHit_lt_top_int k



theorem boundaryCodeStoppingTime_ae_eq (k : ℤ) :
    boundaryCodeStoppingTime k =ᵐ[iidCodeMeasure]
      (fun ω => (boundaryCodeTime k ω : ℕ∞)) := by
  filter_upwards [ae_boundaryCodeStoppingTime_lt_top k] with ω hω
  rw [← boundaryCodeStoppingTime_toNat]
  exact (ENat.natCast_toNat hω.ne).symm



theorem measurable_boundaryCodeStoppingTime (k : ℤ) :
    Measurable (boundaryCodeStoppingTime k) := by
  have hm (j : ℕ) : MeasurableSet {ω | boundaryCodeStoppingTime k ω = j} :=
    codePast_le j _ (measurableSet_codePast_boundaryCodeStoppingTime_eq k j)
  apply measurable_to_countable'
  intro j
  cases j with
  | coe j => exact hm j
  | top =>
    have ht : {ω | boundaryCodeStoppingTime k ω = ⊤} =
        (⋃ j : ℕ, {ω | boundaryCodeStoppingTime k ω = j})ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      constructor
      · intro h j hj
        rw [h] at hj
        exact ENat.top_ne_natCast j hj
      · intro h
        by_contra hne
        obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hne
        exact h j hj.symm
    change MeasurableSet {ω | boundaryCodeStoppingTime k ω = ⊤}
    rw [ht]
    exact (MeasurableSet.iUnion hm).compl



theorem measurable_boundaryCodeTime (k : ℤ) : Measurable (boundaryCodeTime k) := by
  have h := (measurable_of_countable ENat.toNat).comp
    (measurable_boundaryCodeStoppingTime k)
  simpa only [Function.comp_def, boundaryCodeStoppingTime_toNat] using h



@[expose] noncomputable def boundaryPrefixCode (k : ℤ)
    (W : ℤ → Fin 3) : ℕ → Fin 3 :=
  codePastVector (boundaryCodeStoppingTime k) (shiftedCodePath W 0)

private theorem measurable_boundaryCodePastVector (k : ℤ) :
    Measurable (codePastVector (boundaryCodeStoppingTime k)) := by
  apply measurable_pi_iff.mpr
  intro i
  have hset : MeasurableSet {ω | (i : ℕ∞) < boundaryCodeStoppingTime k ω} :=
    (measurable_boundaryCodeStoppingTime k)
      (t := {t : ℕ∞ | (i : ℕ∞) < t}) (Set.to_countable _).measurableSet
  exact Measurable.ite
    hset
    (measurable_pi_apply (i + 1)) measurable_const



theorem measurable_boundaryPrefixCode (k : ℤ) : Measurable (boundaryPrefixCode k) :=
  (measurable_boundaryCodePastVector k).comp (measurable_shiftedCodePath 0)



theorem boundaryPrefixCode_ae_eq_toNat (k : ℤ) :
    boundaryPrefixCode k =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => codePastVector (fun ω => (boundaryCodeTime k ω : ℕ∞))
        (shiftedCodePath W 0)) := by
  have h : ∀ᵐ ω ∂wholePlaneIIDCodeMeasure.map (fun W => shiftedCodePath W 0),
      boundaryCodeStoppingTime k ω = (boundaryCodeTime k ω : ℕ∞) := by
    rw [wholePlaneIIDCodeMeasure_map_shiftedPath]
    exact boundaryCodeStoppingTime_ae_eq k
  have h' := (Measure.tendsto_ae_map (measurable_shiftedCodePath 0).aemeasurable).eventually h
  filter_upwards [h'] with W hW
  funext i
  simp only [boundaryPrefixCode, codePastVector, hW]

private theorem boundaryCodePastVector_indep_shift (k : ℤ) :
    IndepFun (codePastVector (boundaryCodeStoppingTime k))
      (boundaryCodeShift k) iidCodeMeasure := by
  have h := indepFun_frontier_of_strongMarkov (boundaryCodeStoppingTime k)
    (measurableSet_codePast_boundaryCodeStoppingTime_eq k)
    (ae_boundaryCodeStoppingTime_lt_top k)
    (G := fun _ : ℕ → Fin 3 => ()) (H := id)
    measurable_const measurable_id (indepFun_const_left () id)
    (fun _ p _ => p) (fun _ => measurable_fst)
  change IndepFun (codePastVector (boundaryCodeStoppingTime k))
    (fun ω => codeShift (boundaryCodeTime k ω) ω) iidCodeMeasure
  simpa only [boundaryCodeStoppingTime_toNat, id_eq] using h



theorem boundaryPrefixCode_indep_futureCode (k : ℤ) :
    IndepFun (boundaryPrefixCode k) (boundaryFutureCode k)
      wholePlaneIIDCodeMeasure := by
  have hm := measurable_shiftedCodePath 0
  have hp := measurable_boundaryCodePastVector k
  have hf := measurable_boundaryCodeShift k
  have hmap : IndepFun (codePastVector (boundaryCodeStoppingTime k))
      (boundaryCodeShift k)
      (wholePlaneIIDCodeMeasure.map (fun W => shiftedCodePath W 0)) := by
    rw [wholePlaneIIDCodeMeasure_map_shiftedPath]
    exact boundaryCodePastVector_indep_shift k
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_boundaryPrefixCode k).aemeasurable
    (measurable_boundaryFutureCode k).aemeasurable).2
  change wholePlaneIIDCodeMeasure.map
      ((fun ω => (codePastVector (boundaryCodeStoppingTime k) ω,
        boundaryCodeShift k ω)) ∘ (fun W => shiftedCodePath W 0)) =
    (wholePlaneIIDCodeMeasure.map
      (codePastVector (boundaryCodeStoppingTime k) ∘ (fun W => shiftedCodePath W 0))).prod
    (wholePlaneIIDCodeMeasure.map (boundaryCodeShift k ∘ (fun W => shiftedCodePath W 0)))
  rw [← Measure.map_map (hp.prodMk hf) hm, ← Measure.map_map hp hm,
    ← Measure.map_map hf hm]
  exact hmap.map_prod_eq_prod_map_map hp.aemeasurable hf.aemeasurable

private theorem indepFun_pullback_of_map
    {Ω Ω' α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : Ω → Ω'} (hT : Measurable T) (hlaw : μ.map T = ν)
    {f : Ω' → α} {g : Ω' → β} (hf : AEMeasurable f ν)
    (hg : AEMeasurable g ν) (hfg : IndepFun f g ν) :
    IndepFun (f ∘ T) (g ∘ T) μ := by
  have hf' : AEMeasurable f (μ.map T) := hlaw.symm ▸ hf
  have hg' : AEMeasurable g (μ.map T) := hlaw.symm ▸ hg
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hf'.comp_measurable hT) (hg'.comp_measurable hT)).2
  change μ.map ((fun ω => (f ω, g ω)) ∘ T) = _
  rw [← AEMeasurable.map_map_of_aemeasurable (hf'.prodMk hg') hT.aemeasurable,
    ← AEMeasurable.map_map_of_aemeasurable hf' hT.aemeasurable,
    ← AEMeasurable.map_map_of_aemeasurable hg' hT.aemeasurable, hlaw]
  exact hfg.map_prod_eq_prod_map_map hf hg

private theorem iIndepFun_of_full_rectangle
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {β : ι → Type*} [m : ∀ i, MeasurableSpace (β i)]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ∀ i, Ω → β i}
    (h : ∀ (sets : ∀ i, Set (β i)), (∀ i, MeasurableSet (sets i)) →
      μ (⋂ i, f i ⁻¹' sets i) = ∏ i, μ (f i ⁻¹' sets i)) :
    iIndepFun f μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  let t : ∀ i, Set (β i) := fun i => if i ∈ S then sets i else Set.univ
  have ht (i) : MeasurableSet (t i) := by
    by_cases hi : i ∈ S
    · exact (show t i = sets i from ite_eq_left hi) ▸ hs i hi
    · simp only [t, ite_eq_right hi, MeasurableSet.univ]
  have heq : (⋂ i ∈ S, f i ⁻¹' sets i) = ⋂ i, f i ⁻¹' t i := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro hω i
      by_cases hi : i ∈ S
      · simpa only [t, ite_eq_left hi] using hω i hi
      · simp only [t, ite_eq_right hi, Set.mem_univ]
    · intro hω i hi
      simpa only [t, ite_eq_left hi] using hω i
  rw [heq, h t ht]
  calc
    (∏ i, μ (f i ⁻¹' t i)) = ∏ i ∈ S, μ (f i ⁻¹' t i) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ S)
      intro i _ hi
      simp only [t, ite_eq_right hi, Set.preimage_univ, measure_univ]
    _ = ∏ i ∈ S, μ (f i ⁻¹' sets i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [t, ite_eq_left hi]



abbrev BoundaryFourObservation : Fin 4 → Type :=
  Fin.cases (ℕ → Fin 3)
    (Fin.cases (ℕ → Option FiniteThinMap)
      (Fin.cases (ℕ → Option FiniteThinMap) (fun _ => ℕ → Fin 3)))

noncomputable instance (i : Fin 4) : MeasurableSpace (BoundaryFourObservation i) :=
  Fin.cases (inferInstanceAs (MeasurableSpace (ℕ → Fin 3)))
    (Fin.cases (inferInstanceAs (MeasurableSpace (ℕ → Option FiniteThinMap)))
      (Fin.cases (inferInstanceAs (MeasurableSpace (ℕ → Option FiniteThinMap)))
        (fun _ => inferInstanceAs (MeasurableSpace (ℕ → Fin 3))))) i



@[expose] noncomputable def boundaryFourObservations (x : XDP) (k : ℤ) :
    (i : Fin 4) → (ℤ → Fin 3) → BoundaryFourObservation i :=
  Fin.cases (boundaryPrefixCode k)
    (Fin.cases
      (fun W => thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
        (boundaryFutureHattedPath k W))
      (Fin.cases
        (fun W => thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
          (boundaryFutureHattedPath k W))
        (fun _ W => hatLawPrimedCodes (boundaryFutureCode k W))))



theorem aemeasurable_boundaryFuturePrimedCode (k : ℤ) :
    AEMeasurable (hatLawPrimedCodes ∘ boundaryFutureCode k)
      wholePlaneIIDCodeMeasure := by
  have hp : AEMeasurable hatLawPrimedCodes
      (wholePlaneIIDCodeMeasure.map (boundaryFutureCode k)) := by
    rw [boundaryFutureCode_law]
    exact aemeasurable_hatLawCodes.2
  exact hp.comp_measurable (measurable_boundaryFutureCode k)



theorem aemeasurable_boundaryFourObservations (x : XDP) (k : ℤ) (i : Fin 4) :
    AEMeasurable (boundaryFourObservations x k i) wholePlaneIIDCodeMeasure := by
  fin_cases i
  · exact (measurable_boundaryPrefixCode k).aemeasurable
  · exact (boundaryFutureThinSides_package x k).1
  · exact (boundaryFutureThinSides_package x k).2.1
  · exact aemeasurable_boundaryFuturePrimedCode k

private theorem boundaryFutureSides_indep_primed (x : XDP) (k : ℤ) :
    IndepFun
      (fun W =>
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
            (boundaryFutureHattedPath k W),
          thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
            (boundaryFutureHattedPath k W)))
      (hatLawPrimedCodes ∘ boundaryFutureCode k) wholePlaneIIDCodeMeasure := by
  let f : (ℕ → Fin 3) → (ℕ → Option FiniteThinMap) × (ℕ → Option FiniteThinMap) :=
    fun c =>
      (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left (integrateCodes c),
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right (integrateCodes c))
  have hf : Measurable f :=
    ((measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .left).comp
      measurable_integrateCodes).prodMk
    ((measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .right).comp
      measurable_integrateCodes)
  have hind : IndepFun (f ∘ hatLawCodes) hatLawPrimedCodes iidCodeMeasure :=
    hatLawCodes_indep.comp₀ aemeasurable_hatLawCodes.1 aemeasurable_hatLawCodes.2
      hf.aemeasurable measurable_id.aemeasurable
  exact indepFun_pullback_of_map (measurable_boundaryFutureCode k)
    (boundaryFutureCode_law k) (hf.comp_aemeasurable aemeasurable_hatLawCodes.1)
    aemeasurable_hatLawCodes.2 hind

private theorem aemeasurable_futureSideTriple (x : XDP) :
    AEMeasurable (fun c =>
      ((thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
          (integrateCodes (hatLawCodes c)),
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
          (integrateCodes (hatLawCodes c))), hatLawPrimedCodes c)) iidCodeMeasure := by
  have hp := measurable_integrateCodes.comp_aemeasurable aemeasurable_hatLawCodes.1
  have hl := (measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime
    .left).comp_aemeasurable hp
  have hr := (measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime
    .right).comp_aemeasurable hp
  exact (hl.prodMk hr).prodMk aemeasurable_hatLawCodes.2




theorem boundaryFourObservations_iIndepFun (x : XDP) (k : ℤ) :
    iIndepFun (boundaryFourObservations x k) wholePlaneIIDCodeMeasure := by
  let a := boundaryPrefixCode k
  let b := fun W => thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
    (boundaryFutureHattedPath k W)
  let c := fun W => thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
    (boundaryFutureHattedPath k W)
  let d := hatLawPrimedCodes ∘ boundaryFutureCode k
  have hbc : IndepFun b c wholePlaneIIDCodeMeasure :=
    (boundaryFutureThinSides_package x k).2.2.1
  have hbcd : IndepFun (fun W => (b W, c W)) d wholePlaneIIDCodeMeasure :=
    boundaryFutureSides_indep_primed x k
  have had : IndepFun a (fun W => ((b W, c W), d W))
      wholePlaneIIDCodeMeasure := by
    have htr : AEMeasurable (fun v =>
        ((thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
            (integrateCodes (hatLawCodes v)),
          thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
            (integrateCodes (hatLawCodes v))), hatLawPrimedCodes v))
        (wholePlaneIIDCodeMeasure.map (boundaryFutureCode k)) := by
      rw [boundaryFutureCode_law]
      exact aemeasurable_futureSideTriple x
    exact (boundaryPrefixCode_indep_futureCode k).comp₀
      (measurable_boundaryPrefixCode k).aemeasurable
      (measurable_boundaryFutureCode k).aemeasurable measurable_id.aemeasurable htr
  apply iIndepFun_of_full_rectangle
  intro sets hs
  have habcd := had.measure_inter_preimage_eq_mul
    (sets 0) ((sets 1 ×ˢ sets 2) ×ˢ sets 3)
    (hs 0) (((hs 1).prod (hs 2)).prod (hs 3))
  have hbcd' := hbcd.measure_inter_preimage_eq_mul
    (sets 1 ×ˢ sets 2) (sets 3) ((hs 1).prod (hs 2)) (hs 3)
  have hbc' := hbc.measure_inter_preimage_eq_mul (sets 1) (sets 2) (hs 1) (hs 2)
  have hi : (⋂ i, boundaryFourObservations x k i ⁻¹' sets i) =
      a ⁻¹' sets 0 ∩ (fun W => ((b W, c W), d W)) ⁻¹'
        ((sets 1 ×ˢ sets 2) ×ˢ sets 3) := by
    ext W
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨h 0, ⟨h 1, h 2⟩, h 3⟩
    · rintro ⟨ha, ⟨hb, hc⟩, hd⟩ i
      fin_cases i <;> assumption
  rw [hi, habcd]
  change wholePlaneIIDCodeMeasure (a ⁻¹' sets 0) *
    wholePlaneIIDCodeMeasure
      ((fun W => (b W, c W)) ⁻¹' (sets 1 ×ˢ sets 2) ∩ d ⁻¹' sets 3) = _
  rw [hbcd']
  change wholePlaneIIDCodeMeasure (a ⁻¹' sets 0) *
    (wholePlaneIIDCodeMeasure (b ⁻¹' sets 1 ∩ c ⁻¹' sets 2) *
      wholePlaneIIDCodeMeasure (d ⁻¹' sets 3)) = _
  rw [hbc']
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change _ = wholePlaneIIDCodeMeasure (a ⁻¹' sets 0) *
    (wholePlaneIIDCodeMeasure (b ⁻¹' sets 1) *
      (wholePlaneIIDCodeMeasure (c ⁻¹' sets 2) *
        wholePlaneIIDCodeMeasure (d ⁻¹' sets 3)))
  simp only [mul_assoc]



theorem boundaryFutureSideTriple_law_eq_zero (x : XDP) (k : ℤ) :
    wholePlaneIIDCodeMeasure.map (fun W =>
      ((thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
          (boundaryFutureHattedPath k W),
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
          (boundaryFutureHattedPath k W)), hatLawPrimedCodes (boundaryFutureCode k W))) =
    wholePlaneIIDCodeMeasure.map (fun W =>
      ((thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
          (boundaryFutureHattedPath 0 W),
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
          (boundaryFutureHattedPath 0 W)), hatLawPrimedCodes (boundaryFutureCode 0 W))) := by
  let f := fun v =>
    ((thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
        (integrateCodes (hatLawCodes v)),
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
        (integrateCodes (hatLawCodes v))), hatLawPrimedCodes v)
  have hf (j : ℤ) : AEMeasurable f
      (wholePlaneIIDCodeMeasure.map (boundaryFutureCode j)) := by
    rw [boundaryFutureCode_law]
    exact aemeasurable_futureSideTriple x
  change wholePlaneIIDCodeMeasure.map (f ∘ boundaryFutureCode k) =
    wholePlaneIIDCodeMeasure.map (f ∘ boundaryFutureCode 0)
  rw [← (hf k).map_map_of_aemeasurable (measurable_boundaryFutureCode k).aemeasurable,
    ← (hf 0).map_map_of_aemeasurable (measurable_boundaryFutureCode 0).aemeasurable,
    boundaryFutureCode_law, boundaryFutureCode_law]

end DirectedDistances.PaperProofs.Section5
