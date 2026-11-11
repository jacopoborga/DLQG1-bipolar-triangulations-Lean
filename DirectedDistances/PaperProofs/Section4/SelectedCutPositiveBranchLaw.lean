module

public import DirectedDistances.PaperProofs.Section4.SelectedCutWalkPrefix
public import DirectedDistances.Paper.Section4.RenewalTimeCharacterization

/-! Positive-branch and full-scope stopped-walk law toward Lemma 4.13. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem branch_measurable_firstHit (r : ℕ) :
    Measurable (conditionedSecondCoordinateFirstHit r) := by
  apply ENat.measurable_iff.mpr
  intro n
  change MeasurableSet {p | conditionedSecondCoordinateFirstHit r p =
    (n : ℕ∞)}
  obtain ⟨S, hS, hpre⟩ := MeasurableSpace.measurableSet_comap.mp
    (measurableSet_conditionedVectorPast_firstHit_eq r n)
  rw [← hpre]
  exact hS.preimage (measurable_conditionedVectorPrefix n)

/-- Measurability of the finite first-hit prefix into the countable path carrier. -/
private theorem branch_measurable_prefix (r : ℕ) :
    Measurable (selectedCutFirstHitWalkPrefix r) := by
  let t := fun p => (conditionedSecondCoordinateFirstHit r p).toNat
  have ht : Measurable t :=
    (measurable_of_countable ENat.toNat).comp
      (branch_measurable_firstHit r)
  apply measurable_to_countable'
  rintro ⟨n, q⟩
  have heq : {p | selectedCutFirstHitWalkPrefix r p = ⟨n, q⟩} =
      {p | t p = n} ∩ {p | conditionedVectorPrefix n p = q} := by
    ext p
    constructor
    · intro hp
      rcases Sigma.mk.inj hp with ⟨htn, hpq⟩
      refine ⟨htn, ?_⟩
      subst n
      exact eq_of_heq hpq
    · rintro ⟨htn, hq⟩
      subst n
      exact congrArg (Sigma.mk (t p)) hq
  change MeasurableSet {p | selectedCutFirstHitWalkPrefix r p =
    (⟨n, q⟩ : SelectedCutWalkPrefix)}
  rw [heq]
  exact (ht (measurableSet_singleton n)).inter
    ((measurable_conditionedVectorPrefix n) (measurableSet_singleton q))

private theorem branch_prefix_past_measurable
    (r ell k : ℕ) (A : Set SelectedCutWalkPrefix) (_hA : MeasurableSet A) :
    MeasurableSet[conditionedVectorPast k]
      (selectedCutFirstHitWalkPrefix r ⁻¹' A ∩
        {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)}) := by
  let S : Set (Fin (k + 1) → ℤ × ℤ) :=
    {q | (⟨k, q⟩ : SelectedCutWalkPrefix) ∈ A ∧
      (q (Fin.last k)).1 = (ell : ℤ)}
  have hS : MeasurableSet S := (Set.to_countable _).measurableSet
  have hpre :
      selectedCutFirstHitWalkPrefix r ⁻¹' A ∩
          {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
          {p | (p k).1 = (ell : ℤ)} =
        (conditionedVectorPrefix k ⁻¹' S) ∩
          {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} := by
    ext p
    constructor
    · rintro ⟨⟨hp, hk⟩, hend⟩
      refine ⟨?_, hk⟩
      change (⟨k, conditionedVectorPrefix k p⟩ : SelectedCutWalkPrefix) ∈ A ∧ _
      constructor
      · have hx : selectedCutFirstHitWalkPrefix r p =
            ⟨k, conditionedVectorPrefix k p⟩ := by
          rw [selectedCutFirstHitWalkPrefix, hk]
          simp
        rw [← hx]
        exact hp
      · change (p k).1 = (ell : ℤ) at hend
        exact hend
    · rintro ⟨⟨hp, hend⟩, hk⟩
      refine ⟨⟨?_, hk⟩, ?_⟩
      · have hx : selectedCutFirstHitWalkPrefix r p =
            ⟨k, conditionedVectorPrefix k p⟩ := by
          rw [selectedCutFirstHitWalkPrefix, hk]
          simp
        change selectedCutFirstHitWalkPrefix r p ∈ A
        rw [hx]
        exact hp
      · change (p k).1 = (ell : ℤ) at hend
        exact hend
  rw [hpre]
  exact (show MeasurableSet[conditionedVectorPast k]
      (conditionedVectorPrefix k ⁻¹' S) from ⟨S, hS, rfl⟩).inter
    (measurableSet_conditionedVectorPast_firstHit_eq r k)

private theorem branch_prefix_endpoint_indepFun
    (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell)
    (hpos : 0 < (conditionedVectorPathLaw 0 0)
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 =
          (ell : ℤ)})) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    IndepFun (selectedCutFirstHitWalkPrefix r) Y (μ[|E]) := by
  dsimp only
  exact conditionedFirstHit_endpoint_indepFun r ell hr hell
    (selectedCutFirstHitWalkPrefix r)
    (fun A hA k => branch_prefix_past_measurable r ell k A hA)
    hpos

private theorem branch_firstHit_joint (ell r k : ℕ) (hell : 1 ≤ ell)
    (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let Y := fun p => conditionedVectorShift
      (conditionedSecondCoordinateFirstHit r p).toNat p
    let B := Y ⁻¹' firstHitPositiveBranchFuture ell r k
    (μ.restrict B).map (fun p => (Y p, selectedCutFirstHitWalkPrefix r p)) =
      (μ.restrict B).map Y ⊗ₘ selectedCutWalkKernel := by
  classical
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let X := selectedCutFirstHitWalkPrefix r
  let H := firstHitPositiveBranchFuture ell r k
  let B := Y ⁻¹' H
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hX : Measurable X := branch_measurable_prefix r
  have hH : MeasurableSet H := measurableSet_firstHitPositiveBranchFuture ell r k
  have hB : MeasurableSet B := hY hH
  have hEB : (μ.restrict E).restrict B = μ.restrict B := by
    rw [Measure.restrict_restrict hB]
    apply Measure.restrict_congr_set
    filter_upwards [firstHitPastMap_finite_hit_ae r hr] with p hp
    apply propext
    change (p ∈ B ∧ p ∈ E) ↔ p ∈ B
    constructor
    · exact And.left
    · intro hb
      refine ⟨hb, hp, ?_⟩
      have he := congrArg Prod.fst hb.2
      simpa [Y, conditionedVectorShift] using he
  by_cases hmass : 0 < μ E
  · have hscale : μ E • μ[|E] = μ.restrict E := by
      rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel hmass.ne' (measure_ne_top μ E),
        one_smul]
    have hi := branch_prefix_endpoint_indepFun r ell hr hell hmass
    have hbase : (μ.restrict E).map (fun p => (Y p, X p)) =
        ((μ.restrict E).map Y).prod (selectedCutFirstHitWalkLaw ell r) := by
      have hj := hi.symm.map_prod_eq_prod_map_map hY.aemeasurable hX.aemeasurable
      change (μ[|E]).map (fun p => (Y p, X p)) =
        ((μ[|E]).map Y).prod ((μ[|E]).map X) at hj
      rw [← hscale, Measure.map_smul _ (hY.prodMk hX).aemeasurable,
        Measure.map_smul _ hY.aemeasurable, Measure.prod_smul_left]
      exact congrArg (fun ν => μ E • ν) hj
    have hrestricted : (μ.restrict B).map (fun p => (Y p, X p)) =
        ((μ.restrict B).map Y).prod (selectedCutFirstHitWalkLaw ell r) := by
      calc
        _ = (((μ.restrict E).map (fun p => (Y p, X p))).restrict
            (H ×ˢ Set.univ)) := by
          rw [Measure.restrict_map (hY.prodMk hX) (hH.prod MeasurableSet.univ)]
          have heq : (fun p => (Y p, X p)) ⁻¹' (H ×ˢ Set.univ) = B := by
            ext p
            simp [B]
          rw [heq, hEB]
        _ = _ := by
          rw [hbase, ← Measure.restrict_prod_eq_prod_univ,
            Measure.restrict_map hY hH, hEB]
    have hker : selectedCutWalkKernel =ᵐ[(μ.restrict B).map Y]
        Kernel.const _ (selectedCutFirstHitWalkLaw ell r) := by
      have hindex : ∀ᵐ y ∂(μ.restrict B).map Y,
          y 0 = ((ell : ℤ), -(r : ℤ)) := by
        apply (ae_map_iff hY.aemeasurable (by measurability)).2
        filter_upwards [ae_restrict_mem hB] with p hp
        exact hp.2
      filter_upwards [hindex] with y hy
      rw [selectedCutWalkKernel_positive ell r hell hr y hy]
      exact dite_eq_left hmass
    change (μ.restrict B).map (fun p => (Y p, X p)) =
      (μ.restrict B).map Y ⊗ₘ selectedCutWalkKernel
    rw [hrestricted, Measure.compProd_congr hker, Measure.compProd_const]
  · have hzero : μ.restrict E = 0 :=
      Measure.restrict_eq_zero.mpr (le_antisymm (le_of_not_gt hmass) bot_le)
    have hz : μ.restrict B = 0 := by
      rw [← hEB, hzero, Measure.restrict_zero]
    change (μ.restrict B).map (fun p => (Y p, X p)) =
      (μ.restrict B).map Y ⊗ₘ selectedCutWalkKernel
    simp [hz]

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
Every positive branch, including the null zero-left-endpoint branch, has the -/
theorem selectedCutWalkPrefix_positive_branch_joint_law
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (i : PositiveBranchIx k) :
    ((conditionedVectorPathLaw 0 0).restrict
      ((fun p => conditionedVectorShift
        (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
        firstHitPositiveBranchFuture i.1.1 i.1.2 k)).map
        (fun p => (selectedCutFuture T k p, selectedCutWalkPrefix T k p)) =
      (((conditionedVectorPathLaw 0 0).restrict
        ((fun p => conditionedVectorShift
          (conditionedSecondCoordinateFirstHit i.1.2 p).toNat p) ⁻¹'
          firstHitPositiveBranchFuture i.1.1 i.1.2 k)).map
            (selectedCutFuture T k)) ⊗ₘ selectedCutWalkKernel := by
  classical
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit i.1.2
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let B := Y ⁻¹' firstHitPositiveBranchFuture i.1.1 i.1.2 k
  have hB : MeasurableSet B := (measurable_conditionedFirstHit_future i.1.2)
    (measurableSet_firstHitPositiveBranchFuture i.1.1 i.1.2 k)
  by_cases hell : i.1.1 = 0
  · have hz : μ.restrict B = 0 := by
      apply Measure.restrict_eq_zero.mpr
      have hn := selectedCutWalkPrefix_zero_ell_branch_ae k i.1.2 i.2.1
      have hn' : ∀ᵐ p ∂μ, p ∉ B := by simpa [B, Y, τ, hell] using hn
      have heq : {p | ¬ p ∉ B} = B := by
        ext p
        simp only [Set.mem_ofPred_eq, not_not]
      rw [← heq]
      exact ae_iff.mp hn'
    change (μ.restrict B).map _ = (μ.restrict B).map _ ⊗ₘ _
    simp [hz]
  · have hae : ∀ᵐ p ∂μ.restrict B,
        selectedCutTime T k p = τ p := by
      filter_upwards [ae_restrict_mem hB,
        ae_restrict_of_ae (firstHitPastMap_finite_hit_ae i.1.2 i.2.1),
        ae_restrict_of_ae (selectedCutTime_positiveBranch_event_ae T k i.1.2 i.1.1
          i.2.1 i.2.2 hT)] with p hp hf he
      exact ((Iff.of_eq he).mpr ⟨hf, hp⟩).1
    have hfuture : selectedCutFuture T k =ᵐ[μ.restrict B] Y := by
      filter_upwards [hae] with p hp
      simp only [selectedCutFuture, hp, Y]
    have hprefix : selectedCutWalkPrefix T k =ᵐ[μ.restrict B]
        selectedCutFirstHitWalkPrefix i.1.2 := by
      filter_upwards [hae] with p hp
      change (⟨(selectedCutTime T k p).toNat,
        conditionedVectorPrefix (selectedCutTime T k p).toNat p⟩ :
        SelectedCutWalkPrefix) = ⟨(τ p).toNat, conditionedVectorPrefix (τ p).toNat p⟩
      rw [hp]
    change (μ.restrict B).map _ = (μ.restrict B).map _ ⊗ₘ _
    rw [Measure.map_congr (hfuture.prodMk hprefix), Measure.map_congr hfuture]
    exact branch_firstHit_joint i.1.1 i.1.2 k (by omega) i.2.1

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
The full joint law includes the zero selected time and every positive branch. -/
theorem selectedCutWalkPrefix_joint_law
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞) (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    (conditionedVectorPathLaw 0 0).map
      (fun p => (selectedCutFuture T k p, selectedCutWalkPrefix T k p)) =
      ((conditionedVectorPathLaw 0 0).map (selectedCutFuture T k)) ⊗ₘ
        selectedCutWalkKernel :=
  selectedCutWalkPrefix_joint_law_of_positive_branches T k hk hT
    (selectedCutWalkPrefix_positive_branch_joint_law T k hT)

/-- Helper toward Lemma 4.13 (full-scope ruling); not a paper result.
Conditional law of the stopped walk given the entire uncentered selected future, -/
theorem selectedCutWalkPrefix_condDistrib (k : ℕ) (hk : 1 ≤ k) :
    condDistrib (selectedCutWalkPrefix Paper.Section4.renewalTime k)
      (selectedCutFuture Paper.Section4.renewalTime k) (conditionedVectorPathLaw 0 0)
      =ᵐ[(conditionedVectorPathLaw 0 0).map
        (selectedCutFuture Paper.Section4.renewalTime k)] selectedCutWalkKernel := by
  have hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m
      (Paper.Section4.renewalTime m p) :=
    fun p m => (renewalTime_characterization m p).1
  exact selectedCutWalkPrefix_condDistrib_of_joint_law _ k hT
    (selectedCutWalkPrefix_joint_law _ k hk hT)

end DirectedDistances.PaperProofs.Section4
