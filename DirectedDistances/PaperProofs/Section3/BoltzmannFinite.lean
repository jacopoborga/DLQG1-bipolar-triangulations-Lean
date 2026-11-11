module

public import DirectedDistances.RandomWalk.IIDCodeRelabel
public import Mathlib.Probability.Martingale.OptionalStopping
import DirectedDistances.RandomWalk.IIDWalkEndpointCLT
import DirectedDistances.RandomWalk.IIDWalkMaximal
import Mathlib.Probability.Independence.Integration
public import DirectedDistances.RandomWalk.ConditionedStrongMarkov

/-! # Candidate provider for Lemma 3.12 (`lem-boltzmann-finite`)

2 = (1,-1)) and marked-vertex convention (marked boundary edge versus left boundary vertex). -/

public section
namespace DirectedDistances.PaperProofs.Section3

open MeasureTheory ProbabilityTheory
open scoped Function

private def codeLIncrement (i : ℕ) (ω : ℕ → Fin 3) : ℝ :=
  ((DirectedDistances.RandomWalk.codeWalk ω (i + 1) -
    DirectedDistances.RandomWalk.codeWalk ω i).1 : ℝ)

private theorem codeLIncrement_iIndepFun :
    iIndepFun codeLIncrement DirectedDistances.RandomWalk.iidCodeMeasure := by
  exact DirectedDistances.RandomWalk.iIndepFun_codeWalk_increments.comp
    (fun _ z => (z.1 : ℝ)) (fun _ => measurable_of_countable _)

private theorem measurable_codeLIncrement (i : ℕ) : Measurable (codeLIncrement i) := by
  have hEq : codeLIncrement i = fun ω =>
      ((DirectedDistances.RandomWalk.lazyTwoDimensionalStep (ω (i + 1))).1 : ℝ) := by
    funext ω
    simp [codeLIncrement, DirectedDistances.RandomWalk.codeWalk_succ_sub]
  rw [hEq]
  exact (measurable_of_countable
    (fun c : Fin 3 => ((DirectedDistances.RandomWalk.lazyTwoDimensionalStep c).1 : ℝ))).comp
      (measurable_pi_apply (i + 1))

private def codeFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Fin 3)) where
  seq n := ⨆ i ∈ Set.Iio n, MeasurableSpace.comap (codeLIncrement i) inferInstance
  mono' := by
    intro n m hnm
    refine iSup₂_le fun i hi => ?_
    exact le_iSup_of_le i <| le_iSup_of_le (lt_of_lt_of_le hi hnm) le_rfl
  le' := by
    intro n
    refine iSup₂_le fun i hi => ?_
    exact measurable_iff_comap_le.mp (measurable_codeLIncrement i)

private theorem codeWalk_fst_eq_sum_increments (ω : ℕ → Fin 3) (n : ℕ) :
    ((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ) =
      ∑ i ∈ Finset.range n, codeLIncrement i ω := by
  have h := congrArg Prod.fst
    (DirectedDistances.RandomWalk.codeWalk_block_sub_eq_sum ω 0 n)
  simp [DirectedDistances.RandomWalk.codeWalk_zero] at h
  rw [Prod.fst_sum] at h
  calc
    ((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ) =
        ∑ i ∈ Finset.range n,
          ((DirectedDistances.RandomWalk.lazyTwoDimensionalStep (ω (i + 1))).1 : ℝ) := by
            exact_mod_cast h
    _ = ∑ i ∈ Finset.range n, codeLIncrement i ω := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [codeLIncrement, DirectedDistances.RandomWalk.codeWalk_succ_sub]

private def coordinateMartingaleProcess : ℕ → (ℕ → Fin 3) → ℝ :=
  fun n ω => ((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ) + 1

private theorem stronglyAdapted_coordinateMartingaleProcess :
    StronglyAdapted codeFiltration coordinateMartingaleProcess := by
  intro n
  have hs : Measurable[codeFiltration.seq n]
      (fun ω => ∑ i ∈ Finset.range n, codeLIncrement i ω) := by
    apply (Finset.range n).measurable_sum
    · intro i hi
      apply measurable_iff_comap_le.mpr
      exact le_iSup_of_le i <| le_iSup_of_le (Finset.mem_range.mp hi) le_rfl
  have hm : Measurable[codeFiltration.seq n]
      (fun ω => (∑ i ∈ Finset.range n, codeLIncrement i ω) + 1) := by
    exact hs.add measurable_const
  rw [show coordinateMartingaleProcess n =
      fun ω => (∑ i ∈ Finset.range n, codeLIncrement i ω) + 1 from by
        funext ω
        simp [coordinateMartingaleProcess, codeWalk_fst_eq_sum_increments]]
  exact hm.stronglyMeasurable

private theorem measurable_coordinateMartingaleProcess (n : ℕ) :
    Measurable (coordinateMartingaleProcess n) := by
  have hs : Measurable (fun ω => ∑ i ∈ Finset.range n, codeLIncrement i ω) := by
    apply (Finset.range n).measurable_sum
    intro i hi
    exact measurable_codeLIncrement i
  have hEq : coordinateMartingaleProcess n =
      fun ω => (∑ i ∈ Finset.range n, codeLIncrement i ω) + 1 := by
    funext ω
    simp [coordinateMartingaleProcess, codeWalk_fst_eq_sum_increments]
  rw [hEq]
  exact hs.add_const 1

private theorem integrable_coordinateMartingaleProcess (n : ℕ) :
    Integrable (coordinateMartingaleProcess n)
      DirectedDistances.RandomWalk.iidCodeMeasure := by
  apply Integrable.of_bound (measurable_coordinateMartingaleProcess n).aestronglyMeasurable
    ((n : ℝ) + 1)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, coordinateMartingaleProcess]
  have hcoord := DirectedDistances.RandomWalk.codeWalk_block_sub_coord_abs_le_length ω 0 n
  have hcoord' : |(DirectedDistances.RandomWalk.codeWalk ω n).1| ≤ n := by
    simpa [DirectedDistances.RandomWalk.codeWalk_zero] using hcoord.1
  have hreal : |((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ)| ≤ (n : ℝ) := by
    exact_mod_cast hcoord'
  calc
    |((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ) + 1| ≤
        |((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ)| + 1 := by
          simpa using abs_add_le ((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ) 1
    _ ≤ (n : ℝ) + 1 := by nlinarith

private theorem martingale_coordinateMartingaleProcess :
    Martingale coordinateMartingaleProcess codeFiltration
      DirectedDistances.RandomWalk.iidCodeMeasure := by
  apply martingale_of_setIntegral_eq_succ stronglyAdapted_coordinateMartingaleProcess
    integrable_coordinateMartingaleProcess
  intro n A hA
  have hA' : MeasurableSet A := codeFiltration.le n A hA
  let G : (ℕ → Fin 3) → ℝ := codeLIncrement n
  let H : (ℕ → Fin 3) → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hspaces : iIndep
      (fun i => MeasurableSpace.comap (codeLIncrement i) inferInstance)
      DirectedDistances.RandomWalk.iidCodeMeasure :=
    (iIndepFun_iff_iIndep _ _ _).mp codeLIncrement_iIndepFun
  have hle : ∀ i, MeasurableSpace.comap (codeLIncrement i) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → Fin 3)) := by
    intro i
    exact measurable_iff_comap_le.mp (measurable_codeLIncrement i)
  have hst : Disjoint (Set.Iio n) ({n} : Set ℕ) := by simp
  have hspace : Indep (codeFiltration.seq n)
      (MeasurableSpace.comap G inferInstance) DirectedDistances.RandomWalk.iidCodeMeasure := by
    simpa [codeFiltration, G, iSup_singleton] using
      (indep_iSup_of_disjoint hle hspaces hst)
  have hHmeas : Measurable[codeFiltration.seq n] H := measurable_const.indicator hA
  have hGmeas : Measurable[MeasurableSpace.comap G inferInstance] G :=
    Measurable.of_comap_le le_rfl
  have hind : H ⟂ᵢ[DirectedDistances.RandomWalk.iidCodeMeasure] G := by
    change Indep (MeasurableSpace.comap H inferInstance)
      (MeasurableSpace.comap G inferInstance) DirectedDistances.RandomWalk.iidCodeMeasure
    exact indep_of_indep_of_le hspace
      (measurable_iff_comap_le.mp hHmeas) (measurable_iff_comap_le.mp hGmeas)
  have hHint : Integrable H DirectedDistances.RandomWalk.iidCodeMeasure :=
    (integrable_const (1 : ℝ)).indicator hA'
  have hGint : Integrable G DirectedDistances.RandomWalk.iidCodeMeasure := by
    apply Integrable.of_bound (measurable_codeLIncrement n).aestronglyMeasurable 1
    filter_upwards [] with ω
    change |codeLIncrement n ω| ≤ (1 : ℝ)
    unfold codeLIncrement
    exact_mod_cast (DirectedDistances.RandomWalk.codeWalk_succ_sub_coord_abs_le_one ω n).1
  have hGmean : ∫ ω, G ω ∂DirectedDistances.RandomWalk.iidCodeMeasure = 0 := by
    simpa [G, codeLIncrement] using
      (DirectedDistances.RandomWalk.integral_codeWalk_increment_projection 1 0 n)
  have hfactor := hind.integral_mul_eq_mul_integral
    hHint.aestronglyMeasurable hGint.aestronglyMeasurable
  have hprod : ∫ ω, H ω * G ω ∂DirectedDistances.RandomWalk.iidCodeMeasure = 0 := by
    calc
      ∫ ω, H ω * G ω ∂DirectedDistances.RandomWalk.iidCodeMeasure =
          (∫ ω, H ω ∂DirectedDistances.RandomWalk.iidCodeMeasure) *
            ∫ ω, G ω ∂DirectedDistances.RandomWalk.iidCodeMeasure := hfactor
      _ = 0 := by rw [hGmean]; simp
  have hIndicator : A.indicator G = H * G := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [H, hω]
  have hsetG : ∫ ω in A, G ω ∂DirectedDistances.RandomWalk.iidCodeMeasure = 0 := by
    calc
      ∫ ω in A, G ω ∂DirectedDistances.RandomWalk.iidCodeMeasure =
          ∫ ω, A.indicator G ω ∂DirectedDistances.RandomWalk.iidCodeMeasure :=
            (integral_indicator hA').symm
      _ = ∫ ω, H ω * G ω ∂DirectedDistances.RandomWalk.iidCodeMeasure := by
        rw [hIndicator]
        rfl
      _ = 0 := hprod
  have hstep : coordinateMartingaleProcess (n + 1) = fun ω =>
      coordinateMartingaleProcess n ω + G ω := by
    funext ω
    have h := congrArg Prod.fst (DirectedDistances.RandomWalk.codeWalk_succ_sub ω n)
    simp only [Prod.fst_sub] at h
    have h' : (DirectedDistances.RandomWalk.codeWalk ω (n + 1)).1 =
        (DirectedDistances.RandomWalk.codeWalk ω n).1 +
          (DirectedDistances.RandomWalk.codeWalk ω (n + 1) -
            DirectedDistances.RandomWalk.codeWalk ω n).1 := by
      change (DirectedDistances.RandomWalk.codeWalk ω (n + 1)).1 =
        (DirectedDistances.RandomWalk.codeWalk ω n).1 +
          ((DirectedDistances.RandomWalk.codeWalk ω (n + 1)).1 -
            (DirectedDistances.RandomWalk.codeWalk ω n).1)
      omega
    change ((DirectedDistances.RandomWalk.codeWalk ω (n + 1)).1 : ℝ) + 1 =
      ((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ) + 1 + G ω
    change ((DirectedDistances.RandomWalk.codeWalk ω (n + 1)).1 : ℝ) + 1 =
      ((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ) + 1 +
        ((DirectedDistances.RandomWalk.codeWalk ω (n + 1) -
          DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ)
    rw [h']
    push_cast
    ring
  calc
    ∫ ω in A, coordinateMartingaleProcess n ω ∂DirectedDistances.RandomWalk.iidCodeMeasure =
        ∫ ω in A, coordinateMartingaleProcess n ω ∂DirectedDistances.RandomWalk.iidCodeMeasure + 0 := by simp
    _ = ∫ ω in A, (coordinateMartingaleProcess n ω + G ω)
          ∂DirectedDistances.RandomWalk.iidCodeMeasure := by
            rw [integral_add
              ((integrable_coordinateMartingaleProcess n).integrableOn)
              (hGint.integrableOn)]
            rw [hsetG]
    _ = ∫ ω in A, coordinateMartingaleProcess (n + 1) ω
          ∂DirectedDistances.RandomWalk.iidCodeMeasure := by rw [← hstep]

/-- The first time the iid code walk's second coordinate is `-r`, with a harmless
zero value on paths that never hit; source `lem-boltzmann-finite`, -/
@[expose] noncomputable def boltzmannTau (r : ℕ) (ω : ℕ → Fin 3) : ℕ :=
  by
    classical
    exact if h : ∃ n, (DirectedDistances.RandomWalk.codeWalk ω n).2 = -(r : ℤ)
      then Nat.find h else 0

/-- The conditioning event that the first coordinate stays nonnegative through the
right-coordinate hitting time. Source `lem-boltzmann-finite`, -/
@[expose] def boltzmannEvent (r : ℕ) : Set (ℕ → Fin 3) :=
  {ω | ∃ t, (DirectedDistances.RandomWalk.codeWalk ω t).2 = -(r : ℤ) ∧
    ∀ j ≤ t, 0 ≤ (DirectedDistances.RandomWalk.codeWalk ω j).1}

/-- The source hitting time is finite almost surely, by unboundedness below of `R`. -/
theorem boltzmann_tau_finite_ae (r : ℕ) (_hr : 1 ≤ r) :
    ∀ᵐ ω ∂DirectedDistances.RandomWalk.iidCodeMeasure,
      ∃ n, (DirectedDistances.RandomWalk.codeWalk ω n).2 = -(r : ℤ) := by
  exact DirectedDistances.RandomWalk.ae_exists_codeWalk_snd_eq (by omega)

/-- The value selected by `boltzmannTau` is the target hit whenever such a hit exists. -/
theorem boltzmann_tau_spec (r : ℕ) (ω : ℕ → Fin 3)
    (h : ∃ n, (DirectedDistances.RandomWalk.codeWalk ω n).2 = -(r : ℤ)) :
    (DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).2 = -(r : ℤ) := by
  simp [boltzmannTau, h, Nat.find_spec h]

private theorem boltzmannTau_eq_iff_firstHit (r n : ℕ) (ω : ℕ → Fin 3)
    (hhit : ∃ k, (DirectedDistances.RandomWalk.codeWalk ω k).2 = -(r : ℤ)) :
    boltzmannTau r ω = n ↔
      (DirectedDistances.RandomWalk.codeWalk ω n).2 = -(r : ℤ) ∧
        ∀ j < n, (DirectedDistances.RandomWalk.codeWalk ω j).2 ≠ -(r : ℤ) := by
  classical
  unfold boltzmannTau
  rw [dif_pos hhit, Nat.find_eq_iff]

private theorem boltzmannEvent_eq_firstHitForm (r : ℕ) :
    boltzmannEvent r = {ω | ∃ n,
      (DirectedDistances.RandomWalk.codeWalk ω n).2 = -(r : ℤ) ∧
      (∀ j < n, (DirectedDistances.RandomWalk.codeWalk ω j).2 ≠ -(r : ℤ)) ∧
      ∀ j ≤ n, 0 ≤ (DirectedDistances.RandomWalk.codeWalk ω j).1} := by
  ext ω
  constructor
  · rintro ⟨t, ht, hnonneg⟩
    have hhit : ∃ n, (DirectedDistances.RandomWalk.codeWalk ω n).2 = -(r : ℤ) := ⟨t, ht⟩
    let n := boltzmannTau r ω
    have hn := boltzmann_tau_spec r ω hhit
    have hle : n ≤ t := by
      dsimp [n, boltzmannTau]
      rw [dif_pos hhit]
      exact Nat.find_min' hhit ht
    refine ⟨n, hn, ?_, ?_⟩
    · intro j hj htarget
      have hfirst := (boltzmannTau_eq_iff_firstHit r n ω hhit).mp rfl
      exact hfirst.2 j hj htarget
    · intro j hj
      exact hnonneg j (Nat.le_trans hj hle)
  · rintro ⟨n, hn, hfirst, hnonneg⟩
    exact ⟨n, hn, hnonneg⟩

private theorem boltzmannEvent_tau_hit (r : ℕ) (ω : ℕ → Fin 3)
    (hω : ω ∈ boltzmannEvent r) :
    (DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).2 = -(r : ℤ) := by
  rw [boltzmannEvent_eq_firstHitForm] at hω
  obtain ⟨n, hn, hfirst, _⟩ := hω
  have hhit : ∃ k, (DirectedDistances.RandomWalk.codeWalk ω k).2 = -(r : ℤ) := ⟨n, hn⟩
  exact boltzmann_tau_spec r ω hhit

private def boltzmannTailWord (n : ℕ) (ω : ℕ → Fin 3) : Fin n → Fin 3 :=
  fun i => ω (i.val + 1)

private def boltzmannCodePrefix (n : ℕ) (ω : ℕ → Fin 3) :
    Fin (n + 1) → ℤ × ℤ := fun j => DirectedDistances.RandomWalk.codeWalk ω j.val

private theorem boltzmannCodePrefix_eq_word (n : ℕ) (ω : ℕ → Fin 3) :
    boltzmannCodePrefix n ω =
      DirectedDistances.RandomWalk.lazyTwoDimensionalPrefix 0 0
        (boltzmannTailWord n ω) := by
  funext j
  have hsum (f : Fin 3 → ℤ) :
      ∑ i ∈ Finset.range j.val, f (ω (i + 1)) =
        ∑ i : Fin n with i.val < j.val, f (ω (i.val + 1)) := by
    have hset : Finset.range j.val = (Finset.range n).filter (fun i => i < j.val) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    rw [hset, Finset.sum_filter, Finset.sum_filter,
      Fin.sum_univ_eq_sum_range (fun i => if i < j.val then f (ω (i + 1)) else 0) n]
  unfold boltzmannCodePrefix DirectedDistances.RandomWalk.codeWalk
    DirectedDistances.RandomWalk.lazyTwoDimensionalPrefix boltzmannTailWord
  apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, zero_add] <;>
    first | exact hsum (fun c => (DirectedDistances.RandomWalk.lazyTwoDimensionalStep c).1)
          | exact hsum (fun c => (DirectedDistances.RandomWalk.lazyTwoDimensionalStep c).2)

private theorem iidCodeMeasure_map_boltzmannTailWord (n : ℕ) :
    DirectedDistances.RandomWalk.iidCodeMeasure.map (boltzmannTailWord n) =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3)) := by
  classical
  have hf : boltzmannTailWord n =
      (fun q : Fin (n + 1) → Fin 3 => fun i : Fin n => q i.succ) ∘
        (fun ω : ℕ → Fin 3 => fun j : Fin (n + 1) => ω j.val) := by
    funext ω i
    rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop),
    DirectedDistances.RandomWalk.iidCodeMeasure_map_prefix]
  have hmp := measurePreserving_piFinSuccAbove
    (fun j : Fin (n + 1) => if j.val = 0 then
      Measure.dirac (0 : Fin 3) else DirectedDistances.RandomWalk.uniformCodeMeasure) 0
  have hsnd : (fun q : Fin (n + 1) → Fin 3 => fun i : Fin n => q i.succ) =
      Prod.snd ∘ (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Fin 3) 0) := by
    funext q i
    simp [MeasurableEquiv.piFinSuccAbove]
    rfl
  rw [hsnd, ← Measure.map_map measurable_snd (MeasurableEquiv.measurable _),
    hmp.map_eq, Measure.map_snd_prod]
  simp only [Fin.val_zero, ite_true, measure_univ, one_smul, Fin.val_succ,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Fin.succAbove_zero]
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.pi_singleton, Measure.uniformOfFinset_apply_singleton]
  simp [DirectedDistances.RandomWalk.uniformCodeMeasure,
    Measure.uniformOfFinset_apply_singleton, ENNReal.inv_pow]

private theorem iidCodeMeasure_map_boltzmannCodePrefix (n : ℕ) :
    DirectedDistances.RandomWalk.iidCodeMeasure.map (boltzmannCodePrefix n) =
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
        (DirectedDistances.RandomWalk.lazyTwoDimensionalPrefix 0 0) := by
  have htail : Measurable (boltzmannTailWord n) := by
    exact Measurable.of_eval fun i => measurable_pi_apply (i.val + 1)
  rw [show boltzmannCodePrefix n =
    (DirectedDistances.RandomWalk.lazyTwoDimensionalPrefix 0 0) ∘ boltzmannTailWord n from by
      funext ω
      exact boltzmannCodePrefix_eq_word n ω]
  rw [← Measure.map_map (measurable_of_countable _) htail,
    iidCodeMeasure_map_boltzmannTailWord]

private def boltzmannFirstHitPrefixSet (r n : ℕ) :
    Set (Fin (n + 1) → ℤ × ℤ) :=
  {q | (q (Fin.last n)).2 = -(r : ℤ) ∧
    ∀ j : Fin n, (q j.castSucc).2 ≠ -(r : ℤ)}

private def boltzmannConditionedFirstHitSet (r n : ℕ) :
    Set (ℕ → ℤ × ℤ) :=
  {p | DirectedDistances.RandomWalk.conditionedSecondCoordinateFirstHit r p =
    (n : ℕ∞)}

private def boltzmannConditionedPrefix (n : ℕ) (p : ℕ → ℤ × ℤ) :
    Fin (n + 1) → ℤ × ℤ := fun j => p j.val

private theorem boltzmann_conditionedFirstHit_preimage (r n : ℕ) :
    boltzmannConditionedPrefix n ⁻¹' boltzmannFirstHitPrefixSet r n =
      boltzmannConditionedFirstHitSet r n := by
  ext p
  have hhit :
      DirectedDistances.RandomWalk.conditionedSecondCoordinateFirstHit r p =
          (n : ℕ∞) ↔
        (p n).2 = -(r : ℤ) ∧ ∀ j : Fin n, (p j.val).2 ≠ -(r : ℤ) := by
    unfold DirectedDistances.RandomWalk.conditionedSecondCoordinateFirstHit
    by_cases h : ∃ k, (p k).2 = -(r : ℤ)
    · rw [dif_pos h, Nat.cast_inj, Nat.find_eq_iff]
      constructor
      · rintro ⟨hn, hbefore⟩
        exact ⟨hn, fun j => hbefore j.val j.isLt⟩
      · rintro ⟨hn, hbefore⟩
        exact ⟨hn, fun j hj => hbefore ⟨j, hj⟩⟩
    · rw [dif_neg h]
      constructor
      · intro he
        exact False.elim ((ENat.top_ne_natCast n) he)
      · rintro ⟨hn, _⟩
        exact absurd ⟨n, hn⟩ h
  simpa [boltzmannFirstHitPrefixSet, boltzmannConditionedFirstHitSet,
    boltzmannConditionedPrefix] using hhit.symm

private theorem measurable_boltzmannCodePrefix (n : ℕ) :
    Measurable (boltzmannCodePrefix n) := by
  change Measurable ((fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val) ∘
    (fun ω => fun k => DirectedDistances.RandomWalk.codeWalk ω k))
  exact (Measurable.of_eval fun j => measurable_pi_apply j.val).comp
    DirectedDistances.RandomWalk.measurable_codeWalk

private theorem boltzmann_fixed_prefix_RN_identity (r n : ℕ) :
    DirectedDistances.RandomWalk.conditionedVectorPathLaw 0 0
        (boltzmannConditionedFirstHitSet r n) =
      ∫⁻ ω in boltzmannCodePrefix n ⁻¹' boltzmannFirstHitPrefixSet r n,
        (if ∀ j : Fin (n + 1),
            0 ≤ (boltzmannCodePrefix n ω j).1 then
          ENNReal.ofReal
            ((((boltzmannCodePrefix n ω (Fin.last n)).1 : ℝ) + 1) /
              ((0 : ℝ) + 1))
        else 0) ∂DirectedDistances.RandomWalk.iidCodeMeasure := by
  classical
  let S := boltzmannFirstHitPrefixSet r n
  have hS : MeasurableSet S := (Set.to_countable S).measurableSet
  have hf := measurable_boltzmannCodePrefix n
  have hcf : Measurable (boltzmannConditionedPrefix n) :=
    Measurable.of_eval fun j => measurable_pi_apply j.val
  have hd : Measurable (fun q : Fin (n + 1) → ℤ × ℤ =>
      if ∀ j, 0 ≤ (q j).1 then
        ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((0 : ℝ) + 1)) else 0) :=
    measurable_of_countable _
  calc
    DirectedDistances.RandomWalk.conditionedVectorPathLaw 0 0
        (boltzmannConditionedFirstHitSet r n) =
      (DirectedDistances.RandomWalk.conditionedVectorPathLaw 0 0).map
        (boltzmannConditionedPrefix n) S := by
      rw [Measure.map_apply hcf hS,
        boltzmann_conditionedFirstHit_preimage]
    _ = ∫⁻ q in S,
        (if ∀ j, 0 ≤ (q j).1 then
          ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) /
            ((0 : ℝ) + 1)) else 0)
        ∂((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (DirectedDistances.RandomWalk.lazyTwoDimensionalPrefix 0 0)) := by
      rw [show boltzmannConditionedPrefix n =
          (fun p : ℕ → ℤ × ℤ => fun j : Fin (n + 1) => p j.val) from rfl,
        DirectedDistances.RandomWalk.conditionedVectorPathLaw_map_prefix 0 0 n,
        withDensity_apply _ hS]
      norm_num
    _ = ∫⁻ ω in boltzmannCodePrefix n ⁻¹' S,
        (if ∀ j : Fin (n + 1), 0 ≤ (boltzmannCodePrefix n ω j).1 then
          ENNReal.ofReal
            ((((boltzmannCodePrefix n ω (Fin.last n)).1 : ℝ) + 1) /
              ((0 : ℝ) + 1))
        else 0) ∂DirectedDistances.RandomWalk.iidCodeMeasure := by
      rw [← iidCodeMeasure_map_boltzmannCodePrefix n,
        setLIntegral_map hS hd hf]

private def boltzmannEventSlice (r n : ℕ) : Set (ℕ → Fin 3) :=
  {ω | ω ∈ boltzmannEvent r ∧ boltzmannTau r ω = n}

private theorem boltzmannEventSlice_eq_prefixCylinder (r n : ℕ) :
    boltzmannEventSlice r n =
      (boltzmannCodePrefix n ⁻¹' boltzmannFirstHitPrefixSet r n) ∩
        {ω | ∀ j : Fin (n + 1),
          0 ≤ (boltzmannCodePrefix n ω j).1} := by
  classical
  ext ω
  constructor
  · rintro ⟨hE, hτ⟩
    rw [boltzmannEvent_eq_firstHitForm] at hE
    obtain ⟨k, hk, hbefore, hnonneg⟩ := hE
    have hhit : ∃ m, (DirectedDistances.RandomWalk.codeWalk ω m).2 = -(r : ℤ) :=
      ⟨k, hk⟩
    have hτk : boltzmannTau r ω = k :=
      (boltzmannTau_eq_iff_firstHit r k ω hhit).2 ⟨hk, hbefore⟩
    have hkn : k = n := hτk.symm.trans hτ
    simp only [Set.mem_preimage, boltzmannFirstHitPrefixSet,
      boltzmannCodePrefix, Set.mem_setOf_eq]
    constructor
    · constructor
      · simpa [boltzmannCodePrefix, Fin.val_last, hkn] using hk
      · intro j
        have hj : j.castSucc.val < k := by simp only [Fin.val_castSucc]; omega
        simpa [boltzmannCodePrefix, Fin.val_castSucc] using hbefore j.castSucc.val hj
    · intro j
      have hj : j.val ≤ k := by omega
      have := hnonneg j.val hj
      simpa [Fin.val_last, Fin.val_castSucc, hkn] using this
  · intro h
    simp only [Set.mem_preimage, boltzmannFirstHitPrefixSet,
      boltzmannCodePrefix, Set.mem_setOf_eq, Fin.val_last, Fin.val_castSucc] at h
    obtain ⟨⟨hn, hbefore⟩, hnonnegPrefix⟩ := h
    have hhit : ∃ m, (DirectedDistances.RandomWalk.codeWalk ω m).2 = -(r : ℤ) :=
      ⟨n, hn⟩
    have hτ : boltzmannTau r ω = n := by
      apply (boltzmannTau_eq_iff_firstHit r n ω hhit).2
      refine ⟨hn, ?_⟩
      intro j hj htarget
      exact hbefore ⟨j, hj⟩ htarget
    have hnonneg : ∀ j ≤ n, 0 ≤ (DirectedDistances.RandomWalk.codeWalk ω j).1 := by
      intro j hj
      have hcoord := hnonnegPrefix ⟨j, by omega⟩
      simpa [boltzmannCodePrefix, Fin.val_last, Fin.val_castSucc] using hcoord
    exact ⟨⟨n, hn, hnonneg⟩, hτ⟩

private theorem boltzmann_slice_lintegral_eq (r n : ℕ) :
    DirectedDistances.RandomWalk.conditionedVectorPathLaw 0 0
        (boltzmannConditionedFirstHitSet r n) =
      ∫⁻ ω in boltzmannEventSlice r n,
        ENNReal.ofReal
          ((((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ) + 1))
        ∂DirectedDistances.RandomWalk.iidCodeMeasure := by
  classical
  rw [boltzmann_fixed_prefix_RN_identity]
  let S := boltzmannCodePrefix n ⁻¹' boltzmannFirstHitPrefixSet r n
  let P : Set (ℕ → Fin 3) := {ω | ∀ j : Fin (n + 1),
    0 ≤ (boltzmannCodePrefix n ω j).1}
  let f : (ℕ → Fin 3) → ENNReal := fun ω =>
    ENNReal.ofReal ((((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ) + 1))
  have hfun : (fun ω => if ∀ j : Fin (n + 1),
      0 ≤ (boltzmannCodePrefix n ω j).1 then
      ENNReal.ofReal
        ((((boltzmannCodePrefix n ω (Fin.last n)).1 : ℝ) + 1) /
          ((0 : ℝ) + 1)) else 0) = P.indicator f := by
    funext ω
    by_cases hω : ∀ j : Fin (n + 1),
        0 ≤ (boltzmannCodePrefix n ω j).1
    · have hmem : ω ∈ P := hω
      rw [if_pos hω, Set.indicator_of_mem hmem]
      change ENNReal.ofReal
          ((((boltzmannCodePrefix n ω (Fin.last n)).1 : ℝ) + 1) /
            ((0 : ℝ) + 1)) =
        ENNReal.ofReal ((((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ) + 1))
      congr 1
      norm_num [boltzmannCodePrefix, Fin.val_last]
    · have hmem : ω ∉ P := hω
      rw [if_neg hω, Set.indicator_of_notMem hmem]
  have hPmeas : MeasurableSet P := by
    change MeasurableSet (boltzmannCodePrefix n ⁻¹'
      {q : Fin (n + 1) → ℤ × ℤ | ∀ j, 0 ≤ (q j).1})
    exact (Set.to_countable _).measurableSet.preimage
      (measurable_boltzmannCodePrefix n)
  rw [show boltzmannCodePrefix n ⁻¹' boltzmannFirstHitPrefixSet r n = S from rfl,
    hfun, setLIntegral_indicator hPmeas]
  rw [show P ∩ S = boltzmannEventSlice r n from by
    calc
      P ∩ S = S ∩ P := Set.inter_comm _ _
      _ = boltzmannEventSlice r n := (boltzmannEventSlice_eq_prefixCylinder r n).symm]

private theorem measurable_boltzmannEventSlice (r n : ℕ) :
    MeasurableSet (boltzmannEventSlice r n) := by
  rw [boltzmannEventSlice_eq_prefixCylinder]
  refine MeasurableSet.inter ?_ ?_
  · exact (Set.to_countable _).measurableSet.preimage
      (measurable_boltzmannCodePrefix n)
  · change MeasurableSet (boltzmannCodePrefix n ⁻¹'
      {q : Fin (n + 1) → ℤ × ℤ | ∀ j, 0 ≤ (q j).1})
    exact (Set.to_countable _).measurableSet.preimage
      (measurable_boltzmannCodePrefix n)

private theorem boltzmannEvent_eq_iUnion_eventSlice (r : ℕ) :
    boltzmannEvent r = ⋃ n, boltzmannEventSlice r n := by
  ext ω
  simp only [Set.mem_iUnion, boltzmannEventSlice, Set.mem_setOf_eq]
  constructor
  · intro hE
    exact ⟨boltzmannTau r ω, hE, rfl⟩
  · rintro ⟨n, hE, _⟩
    exact hE

private theorem measurable_boltzmannEvent (r : ℕ) :
    MeasurableSet (boltzmannEvent r) := by
  rw [boltzmannEvent_eq_iUnion_eventSlice]
  exact MeasurableSet.iUnion fun n => measurable_boltzmannEventSlice r n

/-- The disjoint first-hit slices have total mass at most one under the actual
conditioned path law. Candidate numerical-core helper for Lemma 3.12,
almost surely finite under the conditioned law. -/
theorem boltzmann_conditioned_firstHit_mass_sum_le_one (r : ℕ) :
    ∑' n : ℕ,
      DirectedDistances.RandomWalk.conditionedVectorPathLaw 0 0
        {p | DirectedDistances.RandomWalk.conditionedSecondCoordinateFirstHit r p =
          (n : ℕ∞)} ≤ 1 := by
  let ν := DirectedDistances.RandomWalk.conditionedVectorPathLaw 0 0
  let H : ℕ → Set (ℕ → ℤ × ℤ) :=
    fun n => boltzmannConditionedFirstHitSet r n
  have hprefix : ∀ n, Measurable (boltzmannConditionedPrefix n) := by
    intro n
    exact Measurable.of_eval fun j => measurable_pi_apply j.val
  have hmeas : ∀ n, MeasurableSet (H n) := by
    intro n
    rw [show H n = boltzmannConditionedPrefix n ⁻¹'
      boltzmannFirstHitPrefixSet r n from by
        rw [boltzmann_conditionedFirstHit_preimage]]
    exact (Set.to_countable (boltzmannFirstHitPrefixSet r n)).measurableSet.preimage
      (hprefix n)
  have hdisj : Pairwise (AEDisjoint ν on H) := by
    intro i j hij
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro p hpi hpj
    have heq : (i : ℕ∞) = (j : ℕ∞) := by
      exact (show DirectedDistances.RandomWalk.conditionedSecondCoordinateFirstHit r p =
          (i : ℕ∞) from hpi).symm.trans
        (show DirectedDistances.RandomWalk.conditionedSecondCoordinateFirstHit r p =
          (j : ℕ∞) from hpj)
    have : i = j := by exact_mod_cast heq
    exact hij this
  calc
    ∑' n : ℕ, ν (H n) ≤ ν Set.univ :=
      MeasureTheory.tsum_measure_le_measure_univ
        (fun n => (hmeas n).nullMeasurableSet) hdisj
    _ = 1 := by simp [ν]

/-- The first-hit prefix densities sum to at most one, giving the weighted
remain separate obligations. -/
theorem boltzmann_lintegral_le_one (r : ℕ) (hr : 1 ≤ r) :
    ∫⁻ ω in boltzmannEvent r,
      ENNReal.ofReal
        ((((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1))
      ∂DirectedDistances.RandomWalk.iidCodeMeasure ≤ 1 := by
  have _hr' : 1 ≤ r := hr
  let D : ℕ → Set (ℕ → Fin 3) := fun n => boltzmannEventSlice r n
  let f : (ℕ → Fin 3) → ENNReal := fun ω =>
    ENNReal.ofReal
      ((((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1))
  have hmeas : ∀ n, MeasurableSet (D n) := by
    intro n
    exact measurable_boltzmannEventSlice r n
  have hdisj : Pairwise (Disjoint on D) := by
    intro i j hij
    change Disjoint (D i) (D j)
    rw [Set.disjoint_left]
    intro ω hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hunion : (⋃ n, D n) = boltzmannEvent r := by
    ext ω
    simp only [Set.mem_iUnion, D, boltzmannEventSlice, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hE, hτ⟩
      exact hE
    · intro hE
      exact ⟨boltzmannTau r ω, hE, rfl⟩
  have hslice : ∀ n,
      (∫⁻ ω in D n, f ω ∂DirectedDistances.RandomWalk.iidCodeMeasure) =
        DirectedDistances.RandomWalk.conditionedVectorPathLaw 0 0
          (boltzmannConditionedFirstHitSet r n) := by
    intro n
    calc
      ∫⁻ ω in D n, f ω ∂DirectedDistances.RandomWalk.iidCodeMeasure =
          ∫⁻ ω in D n,
            ENNReal.ofReal
              ((((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ) + 1))
            ∂DirectedDistances.RandomWalk.iidCodeMeasure := by
        apply setLIntegral_congr_fun (hmeas n)
        intro ω hω
        simp [f, hω.2]
      _ = DirectedDistances.RandomWalk.conditionedVectorPathLaw 0 0
            (boltzmannConditionedFirstHitSet r n) :=
          (boltzmann_slice_lintegral_eq r n).symm
  calc
    ∫⁻ ω in boltzmannEvent r, f ω ∂DirectedDistances.RandomWalk.iidCodeMeasure =
        ∑' n, ∫⁻ ω in D n, f ω ∂DirectedDistances.RandomWalk.iidCodeMeasure := by
      rw [← hunion, lintegral_iUnion hmeas hdisj f]
    _ = ∑' n,
        DirectedDistances.RandomWalk.conditionedVectorPathLaw 0 0
          (boltzmannConditionedFirstHitSet r n) := by
      apply tsum_congr
      exact hslice
    _ ≤ 1 := boltzmann_conditioned_firstHit_mass_sum_le_one r

/-- Almost surely, `boltzmannTau` selects the first target hit. Candidate helper for -/
theorem boltzmann_tau_is_hit_ae (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ ω ∂DirectedDistances.RandomWalk.iidCodeMeasure,
      (DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).2 = -(r : ℤ) := by
  filter_upwards [boltzmann_tau_finite_ae r hr] with ω hω
  exact boltzmann_tau_spec r ω hω

private def boltzmannTwoPrefixCylinder (r : ℕ) : Set (ℕ → Fin 3) :=
  {ω | ∀ i < r, ω (i + 1) = 2}

private theorem codeWalk_twoPrefix (r : ℕ) (ω : ℕ → Fin 3)
    (hω : ω ∈ boltzmannTwoPrefixCylinder r) (n : ℕ) (hn : n ≤ r) :
    DirectedDistances.RandomWalk.codeWalk ω n = ((n : ℤ), -(n : ℤ)) := by
  induction n with
  | zero => simp [DirectedDistances.RandomWalk.codeWalk_zero]
  | succ n ih =>
      have hcode : ω (n + 1) = 2 := hω n hn
      have hstep : DirectedDistances.RandomWalk.lazyTwoDimensionalStep (ω (n + 1)) = (1, -1) := by
        rw [hcode]
        rfl
      have hrec : DirectedDistances.RandomWalk.codeWalk ω (n + 1) =
          DirectedDistances.RandomWalk.codeWalk ω n + (1, -1) := by
        have h := DirectedDistances.RandomWalk.codeWalk_succ_sub ω n
        rw [hstep] at h
        calc
          _ = (DirectedDistances.RandomWalk.codeWalk ω (n + 1) -
              DirectedDistances.RandomWalk.codeWalk ω n) +
                DirectedDistances.RandomWalk.codeWalk ω n := by abel
          _ = (1, -1) + DirectedDistances.RandomWalk.codeWalk ω n := by rw [h]
          _ = DirectedDistances.RandomWalk.codeWalk ω n + (1, -1) := by abel
      rw [hrec, ih (by omega)]
      simp only [Nat.cast_succ, Prod.mk_add_mk]
      congr 1; omega

/-- The conditioning event has positive probability. The cylinder using the first `r`
KMSW code-2 increments witnesses this; source `lem-boltzmann-finite`, -/
theorem boltzmann_event_positive (r : ℕ) (_hr : 1 ≤ r) :
    0 < DirectedDistances.RandomWalk.iidCodeMeasure.real (boltzmannEvent r) := by
  classical
  let q : Fin (r + 1) → Fin 3 := fun j => if j.val = 0 then 0 else 2
  let prj : (ℕ → Fin 3) → (Fin (r + 1) → Fin 3) := fun ω j => ω j.val
  let C : Set (ℕ → Fin 3) := {ω | prj ω = q}
  have hprj : Measurable prj := Measurable.of_eval fun j => measurable_pi_apply j.val
  have hmass : DirectedDistances.RandomWalk.iidCodeMeasure C = (1 / 3 : ENNReal) ^ r := by
    rw [show C = prj ⁻¹' {q} from rfl,
      ← Measure.map_apply hprj (measurableSet_singleton q),
      DirectedDistances.RandomWalk.iidCodeMeasure_map_prefix, Measure.pi_singleton]
    rw [Fin.prod_univ_succ]
    simp [q, DirectedDistances.RandomWalk.uniformCodeMeasure,
      Measure.uniformOfFinset_apply_singleton]
  have hsubset : C ⊆ boltzmannEvent r := by
    intro ω hω
    have htwo : ω ∈ boltzmannTwoPrefixCylinder r := by
      intro i hi
      have h := congrFun hω ⟨i + 1, by omega⟩
      simpa [prj, q] using h
    refine ⟨r, ?_, ?_⟩
    · rw [codeWalk_twoPrefix r ω htwo r le_rfl]
    · intro j hj
      rw [codeWalk_twoPrefix r ω htwo j (by omega)]
      change 0 ≤ (j : ℤ)
      exact_mod_cast Nat.zero_le j
  have hCpos : 0 < (DirectedDistances.RandomWalk.iidCodeMeasure C).toReal := by
    rw [hmass]
    exact ENNReal.toReal_pos (by norm_num) (by simp)
  rw [Measure.real]
  exact lt_of_lt_of_le hCpos (measureReal_mono hsubset (by finiteness))

/-- The normalized conditional lintegral is finite, with the positivity premise
proved in `boltzmann_event_positive`; numerical-core helper for Lemma 3.12 under -/
theorem boltzmann_conditional_lintegral_lt_top (r : ℕ) (hr : 1 ≤ r) :
    (∫⁻ ω in boltzmannEvent r,
      ENNReal.ofReal
        ((((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1))
      ∂DirectedDistances.RandomWalk.iidCodeMeasure) /
        DirectedDistances.RandomWalk.iidCodeMeasure (boltzmannEvent r) < ⊤ := by
  have hprob := boltzmann_event_positive r hr
  have hprobTop : DirectedDistances.RandomWalk.iidCodeMeasure (boltzmannEvent r) ≠ ⊤ := by
    finiteness
  have hden : DirectedDistances.RandomWalk.iidCodeMeasure (boltzmannEvent r) ≠ 0 :=
    (measureReal_ne_zero_iff hprobTop).mp (ne_of_gt hprob)
  have hnumTop :
      (∫⁻ ω in boltzmannEvent r,
        ENNReal.ofReal
          ((((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1))
        ∂DirectedDistances.RandomWalk.iidCodeMeasure) ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (boltzmann_lintegral_le_one r hr)
  exact ENNReal.div_lt_top hnumTop hden

private theorem measurable_select_countable {Ω ι β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    [MeasurableSpace β] (f : ι → Ω → β) (hf : ∀ i, Measurable (f i))
    (g : Ω → ι) (hg : Measurable g) : Measurable (fun ω => f (g ω) ω) := by
  have h : Measurable (fun p : Ω × ι => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  exact h.comp (measurable_id.prodMk hg)

private theorem measurable_boltzmannTau (r : ℕ) :
    Measurable (boltzmannTau r) := by
  classical
  let hit : ℕ → (ℕ → Fin 3) → Prop := fun n ω =>
    (DirectedDistances.RandomWalk.codeWalk ω n).2 = -(r : ℤ)
  let H : Set (ℕ → Fin 3) := {ω | ∃ n, hit n ω}
  let p : ℕ → (ℕ → Fin 3) → Prop := fun n ω =>
    if h : ω ∈ H then hit n ω else True
  have hhitMeas : ∀ n, MeasurableSet {ω | hit n ω} := by
    intro n
    have hc : Measurable (fun ω : ℕ → Fin 3 =>
        DirectedDistances.RandomWalk.codeWalk ω n) :=
      (measurable_pi_apply n).comp DirectedDistances.RandomWalk.measurable_codeWalk
    exact (measurable_snd.comp hc) (measurableSet_singleton (-(r : ℤ)))
  have hHmeas : MeasurableSet H := by
    rw [show H = ⋃ n, {ω | hit n ω} from by
      ext ω
      simp [H]]
    exact MeasurableSet.iUnion hhitMeas
  have hp : ∀ ω, ∃ n, p n ω := by
    intro ω
    by_cases hω : ω ∈ H
    · have hω' : ∃ k, hit k ω := by simpa [H] using hω
      obtain ⟨k, hk⟩ := hω'
      exact ⟨k, by simp [p, hω, hk]⟩
    · exact ⟨0, by simp [p, hω]⟩
  have hpSet (n : ℕ) : {ω | p n ω} = Hᶜ ∪ {ω | hit n ω} := by
    ext ω
    by_cases hω : ω ∈ H <;> simp [p, hω]
  have hpMeas : ∀ n, MeasurableSet {ω | p n ω} := by
    intro n
    rw [hpSet]
    exact MeasurableSet.union hHmeas.compl (hhitMeas n)
  have hfind : Measurable (fun ω => Nat.find (hp ω)) := measurable_find hp hpMeas
  have hEq : (fun ω => Nat.find (hp ω)) = boltzmannTau r := by
    funext ω
    by_cases hω : ∃ n, hit n ω
    · have hmem : ω ∈ H := by simpa [H] using hω
      have hfindEq : Nat.find (hp ω) = Nat.find hω := by
        apply (Nat.find_eq_iff (hp ω)).2
        constructor
        · simpa [p, hmem] using (Nat.find_spec hω : hit (Nat.find hω) ω)
        · intro k hk
          have hnot : ¬ hit k ω := Nat.find_min hω hk
          simpa [p, hmem] using hnot
      have hτ : boltzmannTau r ω = Nat.find hω := by
        simp [boltzmannTau, hit, hω]
      rw [hτ]
      exact hfindEq
    · have hmem : ω ∉ H := by simpa [H] using hω
      have hzero : Nat.find (hp ω) = 0 :=
        (Nat.find_eq_zero (hp ω)).2 (by simp [p, hmem])
      have hτ : boltzmannTau r ω = 0 := by
        simp [boltzmannTau, hit, hω]
      rw [hτ]
      exact hzero
  rw [← hEq]
  exact hfind

private theorem measurable_boltzmannWeight (r : ℕ) :
    Measurable (fun ω : ℕ → Fin 3 =>
      (((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1)) := by
  apply measurable_select_countable
    (fun (n : ℕ) (ω : ℕ → Fin 3) =>
      (((DirectedDistances.RandomWalk.codeWalk ω n).1 : ℝ) + 1))
  · intro n
    have hc : Measurable (fun ω : ℕ → Fin 3 =>
        DirectedDistances.RandomWalk.codeWalk ω n) :=
      (measurable_pi_apply n).comp DirectedDistances.RandomWalk.measurable_codeWalk
    exact ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (measurable_fst.comp hc)).add_const 1
  · exact measurable_boltzmannTau r

private theorem boltzmannWeight_nonneg_ae (r : ℕ) :
    0 ≤ᵐ[DirectedDistances.RandomWalk.iidCodeMeasure.restrict
      (boltzmannEvent r)] (fun ω : ℕ → Fin 3 =>
        (((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1)) := by
  filter_upwards [ae_restrict_mem (measurable_boltzmannEvent r)] with ω hω
  obtain ⟨t, ht, hnonneg⟩ := hω
  have hhit : ∃ k, (DirectedDistances.RandomWalk.codeWalk ω k).2 = -(r : ℤ) :=
    ⟨t, ht⟩
  have hτle : boltzmannTau r ω ≤ t := by
    dsimp [boltzmannTau]
    rw [dif_pos hhit]
    exact Nat.find_min' hhit ht
  have hL := hnonneg (boltzmannTau r ω) hτle
  have hLreal : 0 ≤
      ((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) := by
    exact_mod_cast hL
  exact add_nonneg hLreal (by norm_num)

/-- The real-valued source weight is integrable on the conditioning event; -/
theorem boltzmann_weight_integrableOn (r : ℕ) (hr : 1 ≤ r) :
    IntegrableOn
      (fun ω : ℕ → Fin 3 =>
        (((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1))
      (boltzmannEvent r) DirectedDistances.RandomWalk.iidCodeMeasure := by
  let f : (ℕ → Fin 3) → ℝ := fun ω =>
    (((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1)
  have hfmeas : Measurable f := measurable_boltzmannWeight r
  have hnonneg : 0 ≤ᵐ[DirectedDistances.RandomWalk.iidCodeMeasure.restrict
      (boltzmannEvent r)] f := by
    exact boltzmannWeight_nonneg_ae r
  change Integrable f (DirectedDistances.RandomWalk.iidCodeMeasure.restrict
    (boltzmannEvent r))
  rw [Integrable]
  refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnonneg]
  change (∫⁻ ω in boltzmannEvent r,
    ENNReal.ofReal (f ω) ∂DirectedDistances.RandomWalk.iidCodeMeasure) < ⊤
  exact lt_of_le_of_lt (boltzmann_lintegral_le_one r hr) (by simp)

/-- The normalized real conditional expectation is bounded by the reciprocal event -/
theorem boltzmann_real_conditional_expectation_le (r : ℕ) (hr : 1 ≤ r) :
    (∫ ω in boltzmannEvent r,
      (((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1)
      ∂DirectedDistances.RandomWalk.iidCodeMeasure) /
        DirectedDistances.RandomWalk.iidCodeMeasure.real (boltzmannEvent r) ≤
      1 / DirectedDistances.RandomWalk.iidCodeMeasure.real (boltzmannEvent r) := by
  let f : (ℕ → Fin 3) → ℝ := fun ω =>
    (((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1)
  have hfi : Integrable f
      (DirectedDistances.RandomWalk.iidCodeMeasure.restrict (boltzmannEvent r)) :=
    boltzmann_weight_integrableOn r hr
  have hnn : 0 ≤ᵐ[DirectedDistances.RandomWalk.iidCodeMeasure.restrict
      (boltzmannEvent r)] f := boltzmannWeight_nonneg_ae r
  have hconvert := ofReal_integral_eq_lintegral_ofReal hfi hnn
  have hbound := boltzmann_lintegral_le_one r hr
  rw [← hconvert] at hbound
  have hreal :
      (∫ ω in boltzmannEvent r, f ω ∂DirectedDistances.RandomWalk.iidCodeMeasure) ≤ 1 :=
    ENNReal.ofReal_le_one.mp hbound
  have hprob := boltzmann_event_positive r hr
  exact div_le_div_of_nonneg_right hreal (le_of_lt hprob)

/-- reading. The marked-Boltzmann clause and marked-vertex convention remain separate obligations; -/
theorem boltzmann_finite_core (r : ℕ) (hr : 1 ≤ r) :
    (∀ᵐ ω ∂DirectedDistances.RandomWalk.iidCodeMeasure,
      ∃ n, (DirectedDistances.RandomWalk.codeWalk ω n).2 = -(r : ℤ)) ∧
    0 < DirectedDistances.RandomWalk.iidCodeMeasure.real (boltzmannEvent r) ∧
    (∫⁻ ω in boltzmannEvent r,
      ENNReal.ofReal
        ((((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1))
      ∂DirectedDistances.RandomWalk.iidCodeMeasure ≤ 1) ∧
    IntegrableOn
      (fun ω : ℕ → Fin 3 =>
        (((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1))
      (boltzmannEvent r) DirectedDistances.RandomWalk.iidCodeMeasure ∧
    (∫ ω in boltzmannEvent r,
      (((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1)
      ∂DirectedDistances.RandomWalk.iidCodeMeasure) /
        DirectedDistances.RandomWalk.iidCodeMeasure.real (boltzmannEvent r) ≤
      1 / DirectedDistances.RandomWalk.iidCodeMeasure.real (boltzmannEvent r) ∧
    ((∫⁻ ω in boltzmannEvent r,
      ENNReal.ofReal
        ((((DirectedDistances.RandomWalk.codeWalk ω (boltzmannTau r ω)).1 : ℝ) + 1))
      ∂DirectedDistances.RandomWalk.iidCodeMeasure) /
        DirectedDistances.RandomWalk.iidCodeMeasure (boltzmannEvent r) < ⊤) := by
  exact ⟨boltzmann_tau_finite_ae r hr, boltzmann_event_positive r hr,
    boltzmann_lintegral_le_one r hr, boltzmann_weight_integrableOn r hr,
    boltzmann_real_conditional_expectation_le r hr,
    boltzmann_conditional_lintegral_lt_top r hr⟩

end DirectedDistances.PaperProofs.Section3
