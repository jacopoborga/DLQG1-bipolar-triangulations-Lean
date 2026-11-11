module

public import DirectedDistances.KMSW.BoltzmannRightLawProcedure
public import DirectedDistances.KMSW.BoltzmannPartitionLR

/-! Supporting lemmas for paper labels `def-boltzmann-lr`, `lem-past-map` (see CORRESPONDENCE.md). -/

/-! # Conditioning the Boltzmann law on its left boundary length -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Helper: the left-length fiber mass in the equivalence asserted in -/
theorem rightBoltzmannLaw_leftLength_fiber (r ℓ : ℕ)
    (h0 : rightBoltzmannPartition r ≠ 0)
    (htop : rightBoltzmannPartition r ≠ ⊤) :
    rightBoltzmannLaw r h0 htop {q : AllBoltzmannSpace r | q.1 = ℓ} =
      boltzmannPartition ℓ r / rightBoltzmannPartition r := by
  classical
  rw [rightBoltzmannLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_apply _ (show MeasurableSet {q : AllBoltzmannSpace r | q.1 = ℓ}
      from trivial)]
  have hsum : (∑' q : AllBoltzmannSpace r,
      (allBoltzmannWeight q • Measure.dirac q)
        {q : AllBoltzmannSpace r | q.1 = ℓ}) = boltzmannPartition ℓ r := by
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (show MeasurableSet
        {q : AllBoltzmannSpace r | q.1 = ℓ} from trivial),
      Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq]
    change (∑' q : Σ k : ℕ, BoltzmannSpace k r,
      boltzmannWeight q.2 * if q.1 = ℓ then 1 else 0) = _
    rw [tsum_sigma', tsum_eq_single ℓ]
    · simp [boltzmannPartition]
    · intro k hk
      simp [hk]
  rw [hsum, ENNReal.div_eq_inv_mul]

/-- Helper: the left-length conditioning event has positive mass in -/
theorem rightBoltzmannLaw_leftLength_fiber_pos (r ℓ : ℕ)
    (h0 : rightBoltzmannPartition r ≠ 0)
    (htop : rightBoltzmannPartition r ≠ ⊤)
    (h0' : boltzmannPartition ℓ r ≠ 0) :
    0 < rightBoltzmannLaw r h0 htop {q : AllBoltzmannSpace r | q.1 = ℓ} := by
  rw [rightBoltzmannLaw_leftLength_fiber]
  exact ENNReal.div_pos h0' htop

 
theorem rightBoltzmannLaw_cond_leftLength (r ℓ : ℕ)
    (h0 : rightBoltzmannPartition r ≠ 0)
    (htop : rightBoltzmannPartition r ≠ ⊤)
    (h0' : boltzmannPartition ℓ r ≠ 0)
    (htop' : boltzmannPartition ℓ r ≠ ⊤) :
    (rightBoltzmannLaw r h0 htop)[| {q : AllBoltzmannSpace r | q.1 = ℓ}] =
      (boltzmannLaw ℓ r h0' htop').map (β := AllBoltzmannSpace r)
        (fun m => (⟨ℓ, m⟩ : AllBoltzmannSpace r)) := by
  classical
  have hi : Measurable (β := AllBoltzmannSpace r) (fun m : BoltzmannSpace ℓ r =>
      (⟨ℓ, m⟩ : AllBoltzmannSpace r)) := by intro s hs; trivial
  apply Measure.ext_of_singleton
  intro q
  rw [cond_apply' (measurableSet_singleton q) (rightBoltzmannLaw r h0 htop),
    rightBoltzmannLaw_leftLength_fiber,
    Measure.map_apply hi (measurableSet_singleton q)]
  rcases q with ⟨k, m⟩
  by_cases hk : k = ℓ
  · subst k
    have hpre : (fun m : BoltzmannSpace ℓ r => (⟨ℓ, m⟩ : AllBoltzmannSpace r)) ⁻¹'
        {⟨ℓ, m⟩} = {m} := by ext x; simp
    erw [Set.inter_singleton_of_mem (show
      (⟨ℓ, m⟩ : AllBoltzmannSpace r) ∈ {q | q.1 = ℓ} from rfl),
      rightBoltzmannLaw_singleton, hpre, boltzmannLaw_singleton]
    rw [← ENNReal.div_eq_inv_mul]
    change (boltzmannWeight m * (rightBoltzmannPartition r)⁻¹) /
      (boltzmannPartition ℓ r * (rightBoltzmannPartition r)⁻¹) = _
    exact ENNReal.mul_div_mul_right _ _ (ENNReal.inv_ne_zero.mpr htop)
      (ENNReal.inv_ne_top.mpr h0)
  · have hpre : (fun m : BoltzmannSpace ℓ r => (⟨ℓ, m⟩ : AllBoltzmannSpace r)) ⁻¹'
        {⟨k, m⟩} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      intro h
      exact hk (congrArg Sigma.fst h).symm
    erw [Set.inter_singleton_of_notMem (show
      (⟨k, m⟩ : AllBoltzmannSpace r) ∉ {q | q.1 = ℓ} from hk), hpre]
    erw [measure_empty, measure_empty, mul_zero]



theorem rightBoltzmannLaw_cond_leftLength_of_pos (r ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r) :
    (rightBoltzmannLaw r
      (rightBoltzmannPartition_pos_lt_top r hr).1
      (rightBoltzmannPartition_pos_lt_top r hr).2)[|
        {q : AllBoltzmannSpace r | q.1 = ℓ}] =
      (boltzmannLaw ℓ r
        (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
        (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2).map (β := AllBoltzmannSpace r)
          (fun m => (⟨ℓ, m⟩ : AllBoltzmannSpace r)) := by
  exact rightBoltzmannLaw_cond_leftLength r ℓ _ _ _ _

private theorem map_cond_preimage {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    (μ[| f ⁻¹' s]).map f = (μ.map f)[| s] := by
  ext t ht
  rw [Measure.map_apply hf ht, cond_apply' (hf ht) μ,
    cond_apply' ht (μ.map f), Measure.map_apply hf hs,
    Measure.map_apply hf (hs.inter ht), Set.preimage_inter]

 
theorem stoppedMap_cond_leftLength_procedureReading
    (ℓ r : ℕ) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r) :
    (iidCodeMeasure[| boltzmannEvent r ∩ (stoppedMap r hr) ⁻¹'
      {o | ∃ m : BoltzmannSpace ℓ r,
        o = some (⟨ℓ, m⟩ : AllBoltzmannSpace r)}]).map (stoppedMap r hr) =
      ((boltzmannLaw ℓ r
        (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
        (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2).map
          (β := AllBoltzmannSpace r)
          (fun m => (⟨ℓ, m⟩ : AllBoltzmannSpace r))).map some := by
  classical
  let s : Set (Option (AllBoltzmannSpace r)) :=
    {o | ∃ m : BoltzmannSpace ℓ r,
      o = some (⟨ℓ, m⟩ : AllBoltzmannSpace r)}
  have hs : MeasurableSet s := trivial
  have hf := measurable_stoppedMap r hr
  have hsome : Measurable (some : AllBoltzmannSpace r →
      Option (AllBoltzmannSpace r)) := by intro t ht; trivial
  have hE : MeasurableSet (boltzmannEvent r) := by
    have heq : stoppedIndex r hr ⁻¹' {none} = (boltzmannEvent r)ᶜ := by
      ext ω
      simp [stoppedIndex]
    have hm := (measurable_stoppedIndex r hr) (measurableSet_singleton none)
    rw [heq] at hm
    exact hm.of_compl
  have hpre : (some : AllBoltzmannSpace r → Option (AllBoltzmannSpace r)) ⁻¹' s =
      {q : AllBoltzmannSpace r | q.1 = ℓ} := by
    ext q
    change (∃ m : BoltzmannSpace ℓ r,
      some q = some (⟨ℓ, m⟩ : AllBoltzmannSpace r)) ↔ q.1 = ℓ
    constructor
    · rintro ⟨m, hm⟩
      exact congrArg Sigma.fst (Option.some.inj hm)
    · rcases q with ⟨k, m⟩
      intro hk
      change k = ℓ at hk
      subst k
      exact ⟨m, rfl⟩
  change (iidCodeMeasure[| boltzmannEvent r ∩ (stoppedMap r hr) ⁻¹' s]).map
      (stoppedMap r hr) = _
  rw [← cond_cond_eq_cond_inter hE (hf hs) iidCodeMeasure,
    map_cond_preimage _ hf hs, lem_kmsw_boltzmann_procedureReading,
    ← map_cond_preimage _ hsome hs, hpre,
    rightBoltzmannLaw_cond_leftLength_of_pos r ℓ hℓ hr]

end DirectedDistances.KMSW
