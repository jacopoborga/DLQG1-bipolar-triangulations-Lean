module

public import DirectedDistances.PaperProofs.Section4.PastMapFirstHitLaw
public import DirectedDistances.RandomWalk.ConditionedFirstHitEndpointIndependence
public import DirectedDistances.RandomWalk.ConditionedFirstHitPastCodeLaw
public import DirectedDistances.PaperProofs.Section4.PastMapPathDecoding

/-! past KMSW map at the first hit τ_r given the whole uncentered future, as one a.e. kernel
statement with null fibers handled; the renewal-time selection T_{m_k} and the T_0 branch -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- map law embedded in the common discrete carrier. Not the paper result. -/
@[expose] noncomputable def firstHitBoltzmannMapLaw (r ell : ℕ)
    (hr : 1 ≤ r) (hell : 1 ≤ ell) : Measure (Option (AllBoltzmannSpace r)) :=
  ((boltzmannLaw ell r
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2).map
      (β := AllBoltzmannSpace r) (fun m => ⟨ell, m⟩)).map some

instance firstHitBoltzmannMapLaw_isProbabilityMeasure (r ell : ℕ)
    (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    IsProbabilityMeasure (firstHitBoltzmannMapLaw r ell hr hell) := by
  unfold firstHitBoltzmannMapLaw
  apply Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.2
  apply Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.2
  infer_instance

/-- Boltzmann kernel indexed by the initial left coordinate of the uncentered future.
The nonpositive branch is a point mass at `none`. The renewal selection and zero
branch of the manuscript are not treated; not the paper result. -/
@[expose] noncomputable def firstHitPastMapKernel (r : ℕ) (hr : 1 ≤ r) :
    Kernel (ℕ → ℤ × ℤ) (Option (AllBoltzmannSpace r)) where
  toFun y := if h : 1 ≤ (y 0).1 then
    firstHitBoltzmannMapLaw r (y 0).1.toNat hr (by omega)
    else Measure.dirac none
  measurable' := by
    let f : ℤ → Measure (Option (AllBoltzmannSpace r)) := fun l =>
      if h : 1 ≤ l then firstHitBoltzmannMapLaw r l.toNat hr (by omega)
      else Measure.dirac none
    exact (measurable_of_countable f).comp
      (measurable_fst.comp (measurable_pi_apply 0))

instance firstHitPastMapKernel_isMarkovKernel (r : ℕ) (hr : 1 ≤ r) :
    IsMarkovKernel (firstHitPastMapKernel r hr) where
  isProbabilityMeasure y := by
    change IsProbabilityMeasure (if h : 1 ≤ (y 0).1 then
      firstHitBoltzmannMapLaw r (y 0).1.toNat hr (by omega) else Measure.dirac none)
    split <;> infer_instance

private theorem firstHit_left_pos (r : ℕ) (hr : 1 ≤ r) (p : ℕ → ℤ × ℤ)
    (h0 : p 0 = (0, 0))
    (hstep : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep)
    (hL : ∀ n, 0 ≤ (p n).1)
    (hfin : conditionedSecondCoordinateFirstHit r p < ⊤) :
    1 ≤ (p (conditionedSecondCoordinateFirstHit r p).toNat).1 := by
  classical
  unfold conditionedSecondCoordinateFirstHit at hfin ⊢
  split at hfin
  next h =>
    rw [dite_eq_left h, ENat.toNat_natCast]
    have hh := Nat.find_spec h
    have hprev : ∀ j < Nat.find h, -(r : ℤ) < (p j).2 := by
      intro j hj
      induction j with
      | zero => simp only [h0]; norm_num; omega
      | succ j ih =>
        have hj' : j < Nat.find h := by omega
        have hb := ih hj'
        have hn := Nat.find_min h hj
        obtain ⟨c, hc⟩ := hstep j
        have hs := congrArg Prod.snd hc
        fin_cases c <;>
          norm_num [lazyTwoDimensionalStep, Prod.fst_sub, Prod.snd_sub] at hs <;> omega
    have ht : 0 < Nat.find h := by
      by_contra hn
      have hz : Nat.find h = 0 := by omega
      simp only [hz, h0] at hh
      norm_num at hh
      omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
    rw [hj] at hh ⊢
    simp only [Nat.succ_eq_add_one] at hh ⊢
    have hb := hprev j (by omega)
    obtain ⟨c, hc⟩ := hstep j
    have hs := congrArg Prod.snd hc
    have hl := congrArg Prod.fst hc
    have hn := hL j
    fin_cases c <;> norm_num [lazyTwoDimensionalStep, Prod.fst_sub, Prod.snd_sub] at hs hl <;> omega
  next h => simp only [lt_self_iff_false] at hfin

private theorem finite_hit_measurable (r : ℕ) :
    MeasurableSet {p | conditionedSecondCoordinateFirstHit r p < ⊤} := by
  have heq : {p | conditionedSecondCoordinateFirstHit r p < ⊤} =
      ⋃ k : ℕ, {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun h => by
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h.ne
      exact ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => hk ▸ ENat.natCast_lt_top k⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  obtain ⟨S, hS, he⟩ := MeasurableSpace.measurableSet_comap.mp
    (measurableSet_conditionedVectorPast_firstHit_eq r k)
  rw [← he]
  exact hS.preimage (measurable_conditionedVectorPrefix k)

/-- endpoint at a finite positive-level first hit is positive almost surely. The renewal
selection and T_0 branch are not treated; not the paper result. -/
theorem firstHitPastMap_left_pos_ae (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    ∀ᵐ p ∂μ[|{p | τ p < ⊤}], 1 ≤ (p (τ p).toNat).1 := by
  have hnonneg : ∀ᵐ p ∂conditionedVectorPathLaw 0 0, ∀ n, 0 ≤ (p n).1 := by
    unfold conditionedVectorPathLaw
    apply ae_map_iff (by fun_prop) (by measurability) |>.2
    exact Filter.Eventually.of_forall fun p n => Int.natCast_nonneg _
  filter_upwards [cond_absolutelyContinuous.ae_le conditionedVectorPathLaw_ae_legal,
    cond_absolutelyContinuous.ae_le hnonneg, ae_cond_mem (finite_hit_measurable r)]
    with p hp hn hf
  exact firstHit_left_pos r hr p hp.1 hp.2 hn hf

private theorem endpoint_measurable (r ell : ℕ) :
    MeasurableSet ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
      {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}) := by
  apply (finite_hit_measurable r).inter
  have h := (measurable_fst.comp (measurable_pi_apply 0)).comp
    (measurable_conditionedFirstHit_future r)
  simpa only [Function.comp_def, conditionedVectorShift, Nat.add_zero,
    Set.preimage, Set.mem_singleton_iff] using
    h (measurableSet_singleton (ell : ℤ))

private theorem endpoint_kernel_law (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    0 < μ E →
      (μ[|E]).map (fun p => (Y p, stoppedMap r hr (pathCode p))) =
        (μ[|E]).map Y ⊗ₘ firstHitPastMapKernel r hr := by
  dsimp only
  intro hpos
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hend : ∀ᵐ y ∂(μ[|E]).map Y, (y 0).1 = (ell : ℤ) := by
    apply (ae_map_iff hY.aemeasurable
      ((measurable_fst.comp (measurable_pi_apply 0))
        (measurableSet_singleton (ell : ℤ)))).2
    filter_upwards [ae_cond_mem (endpoint_measurable r ell)] with p hp
    simpa only [Y, Function.comp_def, conditionedVectorShift, Nat.add_zero,
      Set.mem_singleton_iff, Set.mem_ofPred_eq] using hp.2
  have hc := firstHitPastMap_condDistrib r ell hr hell hpos
  have he : condDistrib (fun p => stoppedMap r hr (pathCode p)) Y (μ[|E])
      =ᵐ[(μ[|E]).map Y] firstHitPastMapKernel r hr := by
    filter_upwards [hc, hend] with y hy he
    rw [hy]
    change firstHitBoltzmannMapLaw r ell hr hell = _
    simp only [firstHitPastMapKernel, Kernel.coe_mk, he, Int.toNat_natCast]
    rw [dite_eq_left (by exact_mod_cast hell)]
  exact (condDistrib_ae_eq_iff_measure_eq_compProd hY.aemeasurable
    (((measurable_stoppedMap r hr).comp measurable_pathCode).aemeasurable)
    (firstHitPastMapKernel r hr)).1 he

private theorem restrict_eq_smul_cond {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (hpos : 0 < μ E) :
    μ.restrict E = μ E • μ[|E] := by
  rw [ProbabilityTheory.cond, smul_smul,
    ENNReal.mul_inv_cancel hpos.ne' (measure_ne_top _ _), one_smul]

private theorem endpoint_restrict_kernel_law (r ell : ℕ) (hr : 1 ≤ r)
    (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    (μ.restrict E).map (fun p => (Y p, stoppedMap r hr (pathCode p))) =
      (μ.restrict E).map Y ⊗ₘ firstHitPastMapKernel r hr := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hX : Measurable (fun p => stoppedMap r hr (pathCode p)) :=
    (measurable_stoppedMap r hr).comp measurable_pathCode
  by_cases hz : μ E = 0
  · rw [Measure.restrict_eq_zero.mpr hz]
    simp
  · have hpos : 0 < μ E := bot_lt_iff_ne_bot.mpr hz
    rw [restrict_eq_smul_cond μ E hpos,
      Measure.map_smul _ (hY.prodMk hX).aemeasurable,
      Measure.map_smul _ hY.aemeasurable, Measure.compProd_smul_left,
      endpoint_kernel_law r ell hr hell hpos]

/-- the past KMSW map at the first hit τ_r and the whole uncentered future, with null
author decisions) are not treated; not the paper result. -/
theorem firstHitPastMap_joint_kernel_law (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let ν := μ[|{p | τ p < ⊤}]
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    ν.map (fun p => (Y p, stoppedMap r hr (pathCode p))) =
      ν.map Y ⊗ₘ firstHitPastMapKernel r hr := by
  dsimp only
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let ν := μ[|{p | τ p < ⊤}]
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  let X := fun p => stoppedMap r hr (pathCode p)
  let E := fun n : ℕ => {p | τ p < ⊤} ∩
    {p | (p (τ p).toNat).1 = ((n + 1 : ℕ) : ℤ)}
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hX : Measurable X := (measurable_stoppedMap r hr).comp measurable_pathCode
  have hE (n : ℕ) : MeasurableSet (E n) := endpoint_measurable r (n + 1)
  have hdisj : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    have he := hi.2.symm.trans hj.2
    have he' : i + 1 = j + 1 := by exact_mod_cast he
    exact hij (Nat.add_right_cancel he')
  have hcover : ∀ᵐ p ∂ν, p ∈ ⋃ n, E n := by
    filter_upwards [firstHitPastMap_left_pos_ae r hr,
      ae_cond_mem (finite_hit_measurable r)] with p hp hf
    apply Set.mem_iUnion.mpr
    refine ⟨(p (τ p).toNat).1.toNat - 1, hf, ?_⟩
    change (p (τ p).toNat).1 = _
    change 1 ≤ (p (τ p).toNat).1 at hp
    omega
  have hsum : ν = Measure.sum (fun n => ν.restrict (E n)) := by
    rw [← Measure.restrict_iUnion hdisj hE,
      Measure.restrict_eq_self_of_ae_mem hcover]
  have hfiber (n : ℕ) :
      (ν.restrict (E n)).map (fun p => (Y p, X p)) =
        (ν.restrict (E n)).map Y ⊗ₘ firstHitPastMapKernel r hr := by
    have he : ν.restrict (E n) =
        (μ {p | τ p < ⊤})⁻¹ • μ.restrict (E n) := by
      rw [show ν = (μ {p | τ p < ⊤})⁻¹ • μ.restrict {p | τ p < ⊤} from rfl,
        Measure.restrict_smul, Measure.restrict_restrict_of_subset]
      exact Set.inter_subset_left
    rw [he, Measure.map_smul _ (hY.prodMk hX).aemeasurable,
      Measure.map_smul _ hY.aemeasurable, Measure.compProd_smul_left,
      endpoint_restrict_kernel_law r (n + 1) hr (by omega)]
  calc
    ν.map (fun p => (Y p, X p)) =
        Measure.sum (fun n => (ν.restrict (E n)).map (fun p => (Y p, X p))) := by
      conv_lhs => rw [hsum]
      exact Measure.map_sum (hY.prodMk hX).aemeasurable
    _ = Measure.sum (fun n => (ν.restrict (E n)).map Y ⊗ₘ
        firstHitPastMapKernel r hr) := congrArg Measure.sum (funext hfiber)
    _ = ν.map Y ⊗ₘ firstHitPastMapKernel r hr := by
      rw [← Measure.compProd_sum_left, ← Measure.map_sum hY.aemeasurable, ← hsum]

/-- law of the past KMSW map at the first hit τ_r given the whole uncentered future,
as one a.e. kernel statement with null fibers handled; the renewal-time selection -/
theorem firstHitPastMap_condDistrib_kernel (r : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let ν := μ[|{p | τ p < ⊤}]
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    condDistrib (fun p => stoppedMap r hr (pathCode p)) Y ν
      =ᵐ[ν.map Y] firstHitPastMapKernel r hr := by
  apply condDistrib_ae_eq_of_measure_eq_compProd
    (measurable_conditionedFirstHit_future r).aemeasurable
    (((measurable_stoppedMap r hr).comp measurable_pathCode).aemeasurable)
  exact firstHitPastMap_joint_kernel_law r hr

/-- event has positive mass, so the conditional measure used here is a probability
decisions) are not treated; not the paper result. -/
theorem firstHitPastMap_finite_hit_pos (r : ℕ) :
    0 < conditionedVectorPathLaw 0 0 {p | conditionedSecondCoordinateFirstHit r p < ⊤} := by
  classical
  let w : Fin r → Fin 3 := fun _ => 2
  have hn : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix 0 0 w j).1 := by
    intro j
    simp only [lazyTwoDimensionalPrefix, w, lazyTwoDimensionalStep_two, zero_add]
    positivity
  have hpos := (conditionedSource_prefix_atom_pos_iff 0 0
    (conditionedVectorPathLaw 0 0) (conditionedVectorPathLaw_map_prefix 0 0) r w).2 hn
  apply lt_of_lt_of_le hpos
  apply measure_mono
  intro p hp
  have hend : (p r).2 = -(r : ℤ) := by
    have he := congrArg (fun q : Fin (r + 1) → ℤ × ℤ => (q (Fin.last r)).2) hp
    simpa [lazyTwoDimensionalPrefix, w, lazyTwoDimensionalStep_two] using he
  have hh : ∃ n, (p n).2 = -(r : ℤ) := ⟨r, hend⟩
  simp only [Set.mem_ofPred_eq, conditionedSecondCoordinateFirstHit, dite_eq_left hh]
  exact ENat.natCast_lt_top _

/-- recovery of the fixed positive-boundary conditional law from the same Boltzmann
family used by the future kernel. The renewal-time selection T_{m_k} and the T_0 -/
theorem firstHitPastMap_condDistrib_endpoint_recovery
    (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    0 < μ E →
      condDistrib (fun p => stoppedMap r hr (pathCode p)) Y (μ[|E])
        =ᵐ[(μ[|E]).map Y] fun _ => firstHitBoltzmannMapLaw r ell hr hell := by
  exact firstHitPastMap_condDistrib r ell hr hell

end DirectedDistances.PaperProofs.Section4
