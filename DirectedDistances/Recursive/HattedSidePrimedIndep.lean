module

public import DirectedDistances.Recursive.HattedSideCodeIndep
public import DirectedDistances.RandomWalk.PitmanCodes
import DirectedDistances.KMSW.PathSpaceTransfer

/-! Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result. -/

public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section4
open DirectedDistances.RandomWalk
open DirectedDistances.Paper.Section4
open DirectedDistances.PlanarMap

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The coordinate map `((a, b), c) -> ((a, c), b)` gives the reordered product measure. -/
private theorem map_reorder_side_primed
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μα : Measure α) (μβ : Measure β) (μγ : Measure γ)
    [IsFiniteMeasure μα] [IsFiniteMeasure μβ] [IsFiniteMeasure μγ] :
    Measure.map (fun z : (α × β) × γ => ((z.1.1, z.2), z.1.2))
      ((μα.prod μβ).prod μγ) = (μα.prod μγ).prod μβ := by
  apply Measure.ext_prod₃_iff'.2
  intro s t u hs ht hu
  have hpre :
      (fun z : (α × β) × γ => ((z.1.1, z.2), z.1.2)) ⁻¹'
          ((s ×ˢ t) ×ˢ u) = (s ×ˢ u) ×ˢ t := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod]
    tauto
  rw [Measure.map_apply (by fun_prop) ((hs.prod ht).prod hu), hpre]
  simp only [Measure.prod_prod]
  ac_rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The coordinate map `((a, b), c) -> (a, (b, c))` gives the reassociated product measure. -/
private theorem map_reorder_side_primed_symm
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μα : Measure α) (μβ : Measure β) (μγ : Measure γ)
    [IsFiniteMeasure μα] [IsFiniteMeasure μβ] [IsFiniteMeasure μγ] :
    Measure.map (fun z : (α × β) × γ => (z.1.1, (z.1.2, z.2)))
      ((μα.prod μβ).prod μγ) = μα.prod (μβ.prod μγ) := by
  change Measure.map MeasurableEquiv.prodAssoc ((μα.prod μβ).prod μγ) = _
  exact Measure.prodAssoc_prod

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The left code together with the primed code is independent of the right code. -/
theorem hattedLeftPrimed_indep_right (x : XDP) :
    IndepFun
      (fun ω =>
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
            (hattedIntegratedPath ω),
          hatLawPrimedCodes ω))
      (fun ω => thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
        (hattedIntegratedPath ω))
      iidCodeMeasure := by
  let f : (ℕ → Fin 3) → ℕ → Option FiniteThinMap :=
    fun c => thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
      (integrateCodes c)
  let g : (ℕ → Fin 3) → ℕ → Option FiniteThinMap :=
    fun c => thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
      (integrateCodes c)
  let l : (ℕ → Fin 3) → ℕ → Option FiniteThinMap := f ∘ hatLawCodes
  let r : (ℕ → Fin 3) → ℕ → Option FiniteThinMap := g ∘ hatLawCodes
  let p : (ℕ → Fin 3) → ℕ → Fin 3 := hatLawPrimedCodes
  have hf : Measurable f :=
    (measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .left).comp
      measurable_integrateCodes
  have hg : Measurable g :=
    (measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .right).comp
      measurable_integrateCodes
  have hfg : Measurable (fun c => (f c, g c)) := hf.prodMk hg
  have hX := aemeasurable_hatLawCodes.1
  have hP := aemeasurable_hatLawCodes.2
  have hl : AEMeasurable l iidCodeMeasure := hf.comp_aemeasurable hX
  have hr : AEMeasurable r iidCodeMeasure := hg.comp_aemeasurable hX
  have hp : AEMeasurable p iidCodeMeasure := hP
  have hLR : IndepFun l r iidCodeMeasure := by
    dsimp [l, r, f, g, hattedIntegratedPath]
    exact hattedThinSideCodes_indep x
  have hLP : IndepFun l p iidCodeMeasure := by
    exact hatLawCodes_indep.comp₀ hX hP hf.aemeasurable
      measurable_id.aemeasurable
  have hRP : IndepFun r p iidCodeMeasure := by
    exact hatLawCodes_indep.comp₀ hX hP hg.aemeasurable
      measurable_id.aemeasurable
  have hLRMap : iidCodeMeasure.map (fun ω => (l ω, r ω)) =
      (iidCodeMeasure.map l).prod (iidCodeMeasure.map r) :=
    (indepFun_iff_map_prod_eq_prod_map_map hl hr).mp hLR
  have hLPMap : iidCodeMeasure.map (fun ω => (l ω, p ω)) =
      (iidCodeMeasure.map l).prod (iidCodeMeasure.map p) :=
    (indepFun_iff_map_prod_eq_prod_map_map hl hp).mp hLP
  have hPairP : IndepFun (fun ω => (l ω, r ω)) p iidCodeMeasure := by
    exact hatLawCodes_indep.comp₀ hX hP hfg.aemeasurable
      measurable_id.aemeasurable
  have hTripleAEM : AEMeasurable (fun ω => ((l ω, r ω), p ω)) iidCodeMeasure :=
    (hl.prodMk hr).prodMk hp
  have hTriple : iidCodeMeasure.map (fun ω => ((l ω, r ω), p ω)) =
      ((iidCodeMeasure.map l).prod (iidCodeMeasure.map r)).prod
        (iidCodeMeasure.map p) := by
    have h :=
      (indepFun_iff_map_prod_eq_prod_map_map (hl.prodMk hr) hp).mp hPairP
    rw [hLRMap] at h
    exact h
  have hGoal :
      iidCodeMeasure.map (fun ω => ((l ω, p ω), r ω)) =
        (iidCodeMeasure.map (fun ω => (l ω, p ω))).prod (iidCodeMeasure.map r) := by
    calc
      _ = (iidCodeMeasure.map (fun ω => ((l ω, r ω), p ω))).map
          (fun z : ((ℕ → Option FiniteThinMap) × (ℕ → Option FiniteThinMap)) ×
            (ℕ → Fin 3) => ((z.1.1, z.2), z.1.2)) := by
            change iidCodeMeasure.map
              ((fun z : ((ℕ → Option FiniteThinMap) × (ℕ → Option FiniteThinMap)) ×
                (ℕ → Fin 3) => ((z.1.1, z.2), z.1.2)) ∘
                (fun ω => ((l ω, r ω), p ω))) = _
            rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hTripleAEM]
      _ = ((iidCodeMeasure.map l).prod (iidCodeMeasure.map p)).prod
          (iidCodeMeasure.map r) := by
            rw [hTriple, map_reorder_side_primed]
      _ = (iidCodeMeasure.map (fun ω => (l ω, p ω))).prod
          (iidCodeMeasure.map r) := by rw [hLPMap]
  exact (indepFun_iff_map_prod_eq_prod_map_map (hl.prodMk hp) hr).2 hGoal

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The left code is independent of the right and primed codes together. -/
theorem hattedLeft_indep_rightPrimed (x : XDP) :
    IndepFun
      (fun ω => thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
        (hattedIntegratedPath ω))
      (fun ω =>
        (thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
            (hattedIntegratedPath ω),
          hatLawPrimedCodes ω))
      iidCodeMeasure := by
  let f : (ℕ → Fin 3) → ℕ → Option FiniteThinMap :=
    fun c => thinSideCode x renewalTime renewalTime_positiveSuccessTime .left
      (integrateCodes c)
  let g : (ℕ → Fin 3) → ℕ → Option FiniteThinMap :=
    fun c => thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
      (integrateCodes c)
  let l : (ℕ → Fin 3) → ℕ → Option FiniteThinMap := f ∘ hatLawCodes
  let r : (ℕ → Fin 3) → ℕ → Option FiniteThinMap := g ∘ hatLawCodes
  let p : (ℕ → Fin 3) → ℕ → Fin 3 := hatLawPrimedCodes
  have hf : Measurable f :=
    (measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .left).comp
      measurable_integrateCodes
  have hg : Measurable g :=
    (measurable_thinSideCode x renewalTime renewalTime_positiveSuccessTime .right).comp
      measurable_integrateCodes
  have hfg : Measurable (fun c => (f c, g c)) := hf.prodMk hg
  have hX := aemeasurable_hatLawCodes.1
  have hP := aemeasurable_hatLawCodes.2
  have hl : AEMeasurable l iidCodeMeasure := hf.comp_aemeasurable hX
  have hr : AEMeasurable r iidCodeMeasure := hg.comp_aemeasurable hX
  have hp : AEMeasurable p iidCodeMeasure := hP
  have hLR : IndepFun l r iidCodeMeasure := by
    dsimp [l, r, f, g, hattedIntegratedPath]
    exact hattedThinSideCodes_indep x
  have hLP : IndepFun l p iidCodeMeasure := by
    exact hatLawCodes_indep.comp₀ hX hP hf.aemeasurable
      measurable_id.aemeasurable
  have hRP : IndepFun r p iidCodeMeasure := by
    exact hatLawCodes_indep.comp₀ hX hP hg.aemeasurable
      measurable_id.aemeasurable
  have hLRMap : iidCodeMeasure.map (fun ω => (l ω, r ω)) =
      (iidCodeMeasure.map l).prod (iidCodeMeasure.map r) :=
    (indepFun_iff_map_prod_eq_prod_map_map hl hr).mp hLR
  have hRPMap : iidCodeMeasure.map (fun ω => (r ω, p ω)) =
      (iidCodeMeasure.map r).prod (iidCodeMeasure.map p) :=
    (indepFun_iff_map_prod_eq_prod_map_map hr hp).mp hRP
  have hPairP : IndepFun (fun ω => (l ω, r ω)) p iidCodeMeasure := by
    exact hatLawCodes_indep.comp₀ hX hP hfg.aemeasurable
      measurable_id.aemeasurable
  have hTripleAEM : AEMeasurable (fun ω => ((l ω, r ω), p ω)) iidCodeMeasure :=
    (hl.prodMk hr).prodMk hp
  have hTriple : iidCodeMeasure.map (fun ω => ((l ω, r ω), p ω)) =
      ((iidCodeMeasure.map l).prod (iidCodeMeasure.map r)).prod
        (iidCodeMeasure.map p) := by
    have h :=
      (indepFun_iff_map_prod_eq_prod_map_map (hl.prodMk hr) hp).mp hPairP
    rw [hLRMap] at h
    exact h
  have hGoal :
      iidCodeMeasure.map (fun ω => (l ω, (r ω, p ω))) =
        (iidCodeMeasure.map l).prod (iidCodeMeasure.map (fun ω => (r ω, p ω))) := by
    calc
      _ = (iidCodeMeasure.map (fun ω => ((l ω, r ω), p ω))).map
          (fun z : ((ℕ → Option FiniteThinMap) × (ℕ → Option FiniteThinMap)) ×
            (ℕ → Fin 3) => (z.1.1, (z.1.2, z.2))) := by
            change iidCodeMeasure.map
              ((fun z : ((ℕ → Option FiniteThinMap) × (ℕ → Option FiniteThinMap)) ×
                (ℕ → Fin 3) => (z.1.1, (z.1.2, z.2))) ∘
                (fun ω => ((l ω, r ω), p ω))) = _
            rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hTripleAEM]
      _ = (iidCodeMeasure.map l).prod
          ((iidCodeMeasure.map r).prod (iidCodeMeasure.map p)) := by
            rw [hTriple, map_reorder_side_primed_symm]
      _ = (iidCodeMeasure.map l).prod
          (iidCodeMeasure.map (fun ω => (r ω, p ω))) := by rw [hRPMap]
  exact (indepFun_iff_map_prod_eq_prod_map_map hl (hr.prodMk hp)).2 hGoal

end DirectedDistances.Recursive
