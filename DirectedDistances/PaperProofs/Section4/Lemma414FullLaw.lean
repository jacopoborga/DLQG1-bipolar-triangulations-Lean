module

public import DirectedDistances.PaperProofs.Section4.Lemma414FullSigmaAssembly
-- The obligation has a non-exposed body; this proof-only import permits unfolding it.
import all DirectedDistances.PaperProofs.Section4.Lemma414FullSigmaAssembly

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open MeasureTheory ProbabilityTheory
open scoped Classical

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "ρ" => conditionedVectorPathLaw 0 0
local notation "T" => DirectedDistances.Paper.Section4.renewalTime
local notation "hT" => renewalTime_positiveSuccessTime

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem fullLaw_condIndepFun_congr
    {α β γ : Type*} {F mα : MeasurableSpace α} [StandardBorelSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    {ν : Measure α} [IsFiniteMeasure ν]
    {hF : F ≤ mα} {f f' : α → β} {g g' : α → γ}
    (hf : Measurable f) (hg : Measurable g)
    (hf' : Measurable f') (hg' : Measurable g')
    (hff : f =ᵐ[ν] f') (hgg : g =ᵐ[ν] g')
    (hind : CondIndepFun F hF f g ν) : CondIndepFun F hF f' g' ν := by
  apply (condIndepFun_iff_condExp_inter_preimage_eq_mul hf' hg').2
  intro A B hA hB
  have ha : (f ⁻¹' A).indicator (1 : α → ℝ) =ᵐ[ν]
      (f' ⁻¹' A).indicator (1 : α → ℝ) := by
    filter_upwards [hff] with p hp
    simp only [Set.indicator, Set.mem_preimage, hp]
  have hb : (g ⁻¹' B).indicator (1 : α → ℝ) =ᵐ[ν]
      (g' ⁻¹' B).indicator (1 : α → ℝ) := by
    filter_upwards [hgg] with p hp
    simp only [Set.indicator, Set.mem_preimage, hp]
  have hab : (f ⁻¹' A ∩ g ⁻¹' B).indicator (1 : α → ℝ) =ᵐ[ν]
      (f' ⁻¹' A ∩ g' ⁻¹' B).indicator (1 : α → ℝ) := by
    filter_upwards [hff, hgg] with p hp hq
    simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, hp, hq]
  exact (condExp_congr_ae hab).symm.trans
    (((condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg).1 hind A B hA hB).trans
      ((condExp_congr_ae ha).mul (condExp_congr_ae hb)))

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem fullLaw_factorization_on_restrict
    {α β γ : Type*} {F mα : MeasurableSpace α} [StandardBorelSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    {ν : Measure α} [IsFiniteMeasure ν]
    (hF : F ≤ mα) {E : Set α} (hE : MeasurableSet[F] E)
    {f : α → β} {g : α → γ} (hf : Measurable f) (hg : Measurable g)
    (hind : CondIndepFun F hF f g (ν.restrict E))
    {A : Set β} {B : Set γ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ν[(f ⁻¹' A ∩ g ⁻¹' B).indicator (1 : α → ℝ) | F] =ᵐ[ν.restrict E]
      ν[(f ⁻¹' A).indicator (1 : α → ℝ) | F] *
        ν[(g ⁻¹' B).indicator (1 : α → ℝ) | F] := by
  have ha := condExp_restrict_ae_eq_restrict (μ := ν) hF hE
    ((integrable_const (1 : ℝ)).indicator (hf hA))
  have hb := condExp_restrict_ae_eq_restrict (μ := ν) hF hE
    ((integrable_const (1 : ℝ)).indicator (hg hB))
  have hab := condExp_restrict_ae_eq_restrict (μ := ν) hF hE
    ((integrable_const (1 : ℝ)).indicator ((hf hA).inter (hg hB)))
  exact hab.symm.trans
    (((condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg).1 hind A B hA hB).trans
      (ha.mul hb))

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
private theorem fullLaw_condIndepFun_glue
    {α β γ : Type*} {F mα : MeasurableSpace α} [StandardBorelSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    {ν : Measure α} [IsFiniteMeasure ν]
    (hF : F ≤ mα) {E : Set α} (hE : MeasurableSet[F] E)
    {f : α → β} {g : α → γ} (hf : Measurable f) (hg : Measurable g)
    (hpos : CondIndepFun F hF f g (ν.restrict E))
    (hzero : CondIndepFun F hF f g (ν.restrict Eᶜ)) :
    CondIndepFun F hF f g ν := by
  apply (condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg).2
  intro A B hA hB
  have hp := (ae_restrict_iff' (hF E hE)).1
    (fullLaw_factorization_on_restrict hF hE hf hg hpos hA hB)
  have hz := (ae_restrict_iff' (hF Eᶜ hE.compl)).1
    (fullLaw_factorization_on_restrict hF hE.compl hf hg hzero hA hB)
  filter_upwards [hp, hz] with p hp hz
  by_cases he : p ∈ E
  · exact hp he
  · exact hz he

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result. -/
theorem selectedCutPastCuts_positive_condIndepFun_sourceFiltration
    (x : XDP) (k : ℕ) (hk : 1 ≤ k) :
    CondIndepFun (sourceCutFiltration x k) (sourceCutFiltration_le_ambient x k)
      (fun p => (selectedCutPastCuts x T k p).1)
      (fun p => (selectedCutPastCuts x T k p).2)
      ((ρ).restrict {p | 0 < selectedCutTime T k p}) := by
  let ν := (ρ).restrict {p | 0 < selectedCutTime T k p}
  let B := sourceCutObservation x k
  let C := selectedCutPastCuts x T k
  have hB : Measurable B := assembly_measurable_sourceCutObservation x k
  have hC : Measurable C := measurable_selectedCutPastCuts x T k hT
  let κ := condDistrib (fun p => (C p).1) B ν ×ₖ
    condDistrib (fun p => (C p).2) B ν
  have hFactor : condDistrib C B ν =ᵐ[ν.map B] κ := by
    have hp := selectedCutCodeDistance_positive_conditionalIndependence_measurableVersion
      x T k hk hT B (sourceCutObservation_ae_eq x k hk)
    filter_upwards [hp] with b hb
    change condDistrib C B ν b =
      (condDistrib (fun p => (C p).1) B ν ×ₖ
        condDistrib (fun p => (C p).2) B ν) b
    rw [Kernel.prod_apply]
    exact hb
  have hPair := (condDistrib_ae_eq_iff_measure_eq_compProd
    hB.aemeasurable hC.aemeasurable κ).mp hFactor
  have hJoint : ν.map (fun p => (B p, C p)) =
      (Kernel.id ×ₖ (condDistrib (fun p => (C p).1) B ν ×ₖ
        condDistrib (fun p => (C p).2) B ν)) ∘ₘ ν.map B := by
    rw [← Measure.compProd_eq_comp_prod]
    exact hPair
  exact (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    (μ := ν) (f := fun p => (C p).1) (g := fun p => (C p).2)
    hC.fst hC.snd hB).2 hJoint

/-- Helper toward Lemma 4.14 (lem-finite-ind); not a paper result.
positive branch factors under the source filtration; their measurable union gives the full law. -/
theorem lemma414_full_sigma_assembly_holds : lemma414_full_sigma_assembly_obligation := by
  unfold lemma414_full_sigma_assembly_obligation
  intro x k hk
  let S : Set Ω := {p | 0 < selectedCutTime T k p}
  let C := selectedCutPastSides x T hT k
  let f := fun p => (C p).1
  let g := fun p => (C p).2
  let embed : Lemma414PositiveSide → Lemma414SideOutput := Sum.inr
  let z : Lemma414SideOutput := Sum.inl zeroEdgeMarkedPast
  have hS : MeasurableSet S :=
    (measurable_selectedCutTime T k hT) (Set.to_countable {t : ℕ∞ | 0 < t}).measurableSet
  have hf : Measurable f := measurable_selectedCutPastSides_fst x T hT k
  have hg : Measurable g := measurable_selectedCutPastSides_snd x T hT k
  have hembed : Measurable embed := measurable_of_countable _
  have hcuts := measurable_selectedCutPastCuts x T k hT
  have hind := selectedCutPastCuts_positive_condIndepFun_sourceFiltration x k hk
  have hembedded := hind.comp hembed hembed
  have hleft : (fun p => embed (selectedCutPastCuts x T k p).1) =ᵐ[(ρ).restrict S] f := by
    filter_upwards [ae_restrict_mem hS] with p hp
    exact congrArg Prod.fst (selectedCutPastSides_pos x T hT k p hp).symm
  have hright : (fun p => embed (selectedCutPastCuts x T k p).2) =ᵐ[(ρ).restrict S] g := by
    filter_upwards [ae_restrict_mem hS] with p hp
    exact congrArg Prod.snd (selectedCutPastSides_pos x T hT k p hp).symm
  have hpos : CondIndepFun (sourceCutFiltration x k)
      (sourceCutFiltration_le_ambient x k) f g ((ρ).restrict S) :=
    fullLaw_condIndepFun_congr (hembed.comp hcuts.fst) (hembed.comp hcuts.snd)
      hf hg hleft hright hembedded
  obtain ⟨E, hE, hSE⟩ := selectedCutPositiveSet_sourceCutFiltration_measurable x k hk
  have hF := sourceCutFiltration_le_ambient x k
  have hEamb : MeasurableSet E := hF E hE
  have hposE : CondIndepFun (sourceCutFiltration x k) hF f g ((ρ).restrict E) := by
    have heq : (ρ).restrict S = (ρ).restrict E := Measure.restrict_congr_set hSE
    simpa only [heq] using hpos
  have hzero : C =ᵐ[(ρ).restrict Eᶜ] fun _ => (z, z) := by
    filter_upwards [ae_restrict_of_ae hSE, ae_restrict_mem hEamb.compl] with p hp he
    have hn : ¬ 0 < selectedCutTime T k p := by
      intro h
      exact he ((Iff.of_eq hp).mp h)
    exact selectedCutPastSides_zero x T hT k p (le_antisymm (le_of_not_gt hn) bot_le)
  have hzeroLeft : (fun _ : Ω => z) =ᵐ[(ρ).restrict Eᶜ] f := by
    filter_upwards [hzero] with p hp
    exact congrArg Prod.fst hp.symm
  have hzeroRight : (fun _ : Ω => z) =ᵐ[(ρ).restrict Eᶜ] g := by
    filter_upwards [hzero] with p hp
    exact congrArg Prod.snd hp.symm
  have hzeroE : CondIndepFun (sourceCutFiltration x k) hF f g ((ρ).restrict Eᶜ) :=
    fullLaw_condIndepFun_congr measurable_const measurable_const hf hg
      hzeroLeft hzeroRight (condIndepFun_const_left z (fun _ : Ω => z))
  exact fullLaw_condIndepFun_glue hF hE hf hg hposE hzeroE

end DirectedDistances.PaperProofs.Section4
