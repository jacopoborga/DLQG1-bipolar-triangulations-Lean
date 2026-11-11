module

public import DirectedDistances.PaperProofs.Section4.PastMapPathDecoding
public import DirectedDistances.RandomWalk.ConditionedFirstHitEndpointIndependence
public import DirectedDistances.RandomWalk.FirstHitBarrierDecomposition
public import DirectedDistances.KMSW.BoltzmannEndpointFiberLaw
import DirectedDistances.RandomWalk.ConditionedFirstHitPastCodeLaw

/-! past KMSW map at the first hit τ_r of R = −r under the endpoint-conditioned UIQBOT law,
given the whole uncentered future; the renewal-time selection T_{m_k} and the T_0 branch -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem past_to_prefix (k : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (hA : MeasurableSet[conditionedVectorPast k] A) :
    ∃ S : Set (Fin (k + 1) → ℤ × ℤ), A = conditionedVectorPrefix k ⁻¹' S := by
  obtain ⟨S, _, hS⟩ := MeasurableSpace.measurableSet_comap.mp hA
  exact ⟨S, hS.symm⟩

private theorem endpoint_measurable (r ell : ℕ) :
    MeasurableSet ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
      {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}) := by
  have heq : ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
      {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}) =
      ⋃ k : ℕ, {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hfin, hend⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin.ne
      exact ⟨k, hk.symm, by simpa only [← hk, ENat.toNat_natCast] using hend⟩
    · rintro ⟨k, hk, hend⟩
      exact ⟨hk ▸ ENat.natCast_lt_top k, by simpa only [hk, ENat.toNat_natCast]⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  obtain ⟨S, hS, heq⟩ := MeasurableSpace.measurableSet_comap.mp
    (measurableSet_conditionedVectorPast_firstHit_eq r k)
  rw [← heq]
  exact (hS.preimage (measurable_conditionedVectorPrefix k)).inter
    ((measurable_fst.comp (measurable_pi_apply k)) (measurableSet_singleton _))

private theorem iid_endpoint_eq_fiber (r ell : ℕ) (hr : 1 ≤ r) :
    boltzmannEvent r ∩ {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)} =
      boltzmannEvent r ∩ stoppedMap r hr ⁻¹'
        {o : Option (AllBoltzmannSpace r) | ∃ m : BoltzmannSpace ell r,
          o = some (⟨ell, m⟩ : AllBoltzmannSpace r)} := by
  classical
  ext ω
  by_cases hE : ω ∈ boltzmannEvent r
  · have ht := (boltzmann_boundary_observable r hr ω hE).1
    have hcast := (stoppedWord_admissible r hr ω hE).2
    have hL : L (boltzmannKMSWStream ω) (boltzmannTau r ω) =
        (codeWalk ω (boltzmannTau r ω)).1 := by
      rw [kmsw_L_eq, codeWalk_eq_integrateCodes]
      rfl
    have hfst : ∀ q : AllBoltzmannSpace r,
        (∃ m : BoltzmannSpace ell r, some q = some ⟨ell, m⟩) ↔ q.1 = ell := by
      intro q
      constructor
      · rintro ⟨m, hm⟩
        exact congrArg Sigma.fst (Option.some.inj hm)
      · rcases q with ⟨l, m⟩
        intro he
        change l = ell at he
        subst l
        exact ⟨m, rfl⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, hE, true_and]
    let j : StoppedWalkIndex r := ⟨boltzmannTau r ω,
      ⟨(L (boltzmannKMSWStream ω) (boltzmannTau r ω)).toNat,
        ⟨stoppedWord r ω, (stoppedWord_admissible r hr ω hE).1⟩⟩⟩
    have hi : stoppedIndex r hr ω = some j := by
      simp only [stoppedIndex, dite_eq_left hE, j]
    have hm : stoppedMap r hr ω = some (stoppedWalkMap ⟨j, ht⟩) := by
      have hj : 1 ≤ j.1 := ht
      rw [stoppedMap, hi]
      change stoppedWalkMapOption r j = _
      simp only [stoppedWalkMapOption, dite_eq_left hj]
    rw [hm]
    apply Iff.trans _ (hfst (stoppedWalkMap ⟨j, ht⟩)).symm
    change (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ) ↔
      (L (boltzmannKMSWStream ω) (boltzmannTau r ω)).toNat = ell
    rw [hL] at hcast ⊢
    omega
  · simp only [Set.mem_inter_iff, hE, false_and]

private theorem iid_endpoint_positive (r ell : ℕ)
    (hpos : 0 < conditionedVectorPathLaw 0 0
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)})) :
    0 < iidCodeMeasure
      (boltzmannEvent r ∩ {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)}) := by
  classical
  have hpre (k : ℕ) := past_to_prefix k _
    (measurableSet_conditionedVectorPast_firstHit_eq r k)
  choose S hS using hpre
  have hb := conditionedVectorPathLaw_zero_zero_firstHit_bridge r ell Set.univ S
    (fun k => by simpa only [Set.univ_inter] using hS k)
  simp only [Set.univ_inter, Set.preimage_univ] at hb
  rw [hb] at hpos
  by_contra h
  have hz := le_antisymm (not_lt.mp h) bot_le
  rw [hz, mul_zero] at hpos
  exact (lt_irrefl _ hpos)

private def legalPast (r : ℕ) (p : ℕ → ℤ × ℤ) : Prop :=
  p 0 = (0, 0) ∧ ∀ n < (conditionedSecondCoordinateFirstHit r p).toNat,
    p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep

private theorem legalPast_codeWalk (r : ℕ) (ω : ℕ → Fin 3) :
    legalPast r (fun n => codeWalk ω n) := by
  refine ⟨codeWalk_zero ω, fun n _ => ?_⟩
  exact ⟨ω (n + 1), (codeWalk_succ_sub ω n).symm⟩

private noncomputable def legalMap (r : ℕ) (hr : 1 ≤ r)
    (p : ℕ → ℤ × ℤ) : Option (AllBoltzmannSpace r) := by
  classical
  exact if legalPast r p then stoppedMap r hr (pathCode p) else none

private theorem legalMap_ae (r : ℕ) (hr : 1 ≤ r) :
    legalMap r hr =ᵐ[conditionedVectorPathLaw 0 0]
      fun p => stoppedMap r hr (pathCode p) := by
  filter_upwards [conditionedVectorPathLaw_ae_legal] with p hp
  have hl : legalPast r p := ⟨hp.1, fun n _ => hp.2 n⟩
  simp only [legalMap, ite_eq_left hl]

private theorem legalMap_past (r : ℕ) (hr : 1 ≤ r)
    (T : Set (Option (AllBoltzmannSpace r))) (_hT : MeasurableSet T) (k ell : ℕ) :
    MeasurableSet[conditionedVectorPast k]
      (legalMap r hr ⁻¹' T ∩
        {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)}) := by
  classical
  let H : Set (ℕ → ℤ × ℤ) :=
    {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
      {p | (p k).1 = (ell : ℤ)}
  have hH : MeasurableSet[conditionedVectorPast k] H := by
    refine (measurableSet_conditionedVectorPast_firstHit_eq r k).inter ?_
    refine ⟨{q : Fin (k + 1) → ℤ × ℤ | (q (Fin.last k)).1 = (ell : ℤ)},
      (Set.to_countable _).measurableSet, ?_⟩
    rfl
  have hm (U : Set (Option (AllBoltzmannSpace r))) :
      MeasurableSet[conditionedVectorPast k]
        ({p | stoppedMap r hr (pathCode p) ∈ U ∧ legalPast r p} ∩ H) := by
    simpa only [Set.inter_assoc, legalPast, H] using
      measurableSet_stoppedMap_pathCode_firstHit_legal r hr U k ell
  have hl : MeasurableSet[conditionedVectorPast k] ({p | legalPast r p} ∩ H) := by
    simpa only [Set.mem_univ, true_and] using hm Set.univ
  by_cases hn : none ∈ T
  · have heq : legalMap r hr ⁻¹' T ∩
        {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)} =
        ({p | stoppedMap r hr (pathCode p) ∈ T ∧ legalPast r p} ∩ H) ∪
          (H \ ({p | legalPast r p} ∩ H)) := by
      ext p
      by_cases hp : legalPast r p <;> simp [legalMap, hp, hn, H, and_assoc]
    rw [heq]
    exact (hm T).union (hH.diff hl)
  · have heq : legalMap r hr ⁻¹' T ∩
        {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} ∩
        {p | (p k).1 = (ell : ℤ)} =
        {p | stoppedMap r hr (pathCode p) ∈ T ∧ legalPast r p} ∩ H := by
      ext p
      by_cases hp : legalPast r p <;> simp [legalMap, hp, hn, H, and_assoc]
    rw [heq]
    exact hm T

private theorem pastMap_independent (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    0 < μ E → IndepFun (fun p => stoppedMap r hr (pathCode p)) Y (μ[|E]) := by
  dsimp only
  intro hpos
  exact (conditionedFirstHit_endpoint_indepFun r ell hr hell (legalMap r hr)
    (fun T hT k => legalMap_past r hr T hT k ell) hpos).congr
      (cond_absolutelyContinuous.ae_le (legalMap_ae r hr)) (by rfl)

/-- of the past KMSW map at the first hit τ_r of R = −r under the endpoint-conditioned
UIQBOT law, given the whole uncentered future; the renewal-time selection T_{m_k} -/
theorem firstHitPastMap_law (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    0 < μ E →
      (μ[|E]).map (fun p => stoppedMap r hr (pathCode p)) =
        ((boltzmannLaw ell r
          (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
          (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2).map (β := AllBoltzmannSpace r)
            (fun m => (⟨ell, m⟩ : AllBoltzmannSpace r))).map some := by
  classical
  dsimp only
  intro hpos
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let X := fun p => stoppedMap r hr (pathCode p)
  let D := boltzmannEvent r ∩ {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)}
  have hmap : (μ[|E]).map X = (iidCodeMeasure[|D]).map (stoppedMap r hr) := by
    apply Measure.ext
    intro T hT
    have hX : Measurable X :=
      (measurable_stoppedMap r hr).comp measurable_pathCode
    rw [Measure.map_apply hX hT,
      Measure.map_apply (measurable_stoppedMap r hr) hT]
    let A : Set (ℕ → ℤ × ℤ) :=
      {p | X p ∈ T ∧ legalPast r p ∧ (p (τ p).toNat).1 = (ell : ℤ)}
    have hprefix (k : ℕ) : ∃ S : Set (Fin (k + 1) → ℤ × ℤ),
        A ∩ {p | τ p = (k : ℕ∞)} = conditionedVectorPrefix k ⁻¹' S := by
      have hm := measurableSet_stoppedMap_pathCode_firstHit_legal r hr T k ell
      have heq : A ∩ {p | τ p = (k : ℕ∞)} =
          {p | X p ∈ T ∧ legalPast r p} ∩ {p | τ p = (k : ℕ∞)} ∩
            {p | (p k).1 = (ell : ℤ)} := by
        ext p
        by_cases hk : τ p = (k : ℕ∞)
        · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, A, hk,
            ENat.toNat_natCast, and_true]
          tauto
        · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hk, and_false, false_and]
      rw [heq]
      exact past_to_prefix k _ hm
    choose S hS using hprefix
    have hb := conditionedVectorPathLaw_zero_zero_firstHit_conditional r ell A S hS
      (iid_endpoint_positive r ell hpos)
    have hAE : A =ᵐ[μ[|E]] X ⁻¹' T := by
      filter_upwards [cond_absolutelyContinuous.ae_le conditionedVectorPathLaw_ae_legal,
        ae_cond_mem (endpoint_measurable r ell)] with p hp he
      apply propext
      exact ⟨fun h => h.1, fun h => ⟨h, ⟨hp.1, fun n _ => hp.2 n⟩, he.2⟩⟩
    rw [← measure_congr hAE]
    change μ[A | E] = _
    rw [hb]
    have hEm : MeasurableSet (boltzmannEvent r) := by
      have heq : stoppedIndex r hr ⁻¹' {none} = (boltzmannEvent r)ᶜ := by
        ext ω
        simp [stoppedIndex]
      have hm := measurable_stoppedIndex r hr (measurableSet_singleton none)
      rw [heq] at hm
      exact hm.of_compl
    have hDm : MeasurableSet D := by
      rw [show D = _ from iid_endpoint_eq_fiber r ell hr]
      exact hEm.inter ((measurable_stoppedMap r hr) (show MeasurableSet
        {o : Option (AllBoltzmannSpace r) | ∃ m : BoltzmannSpace ell r,
          o = some (⟨ell, m⟩ : AllBoltzmannSpace r)} from trivial))
    apply measure_congr
    filter_upwards [ae_cond_mem hDm] with ω hω
    have hτ : τ (fun n => codeWalk ω n) = (boltzmannTau r ω : ℕ∞) :=
      by
        obtain ⟨t, ht, _⟩ := hω.1
        have hh : ∃ n, (codeWalk ω n).2 = -(r : ℤ) := ⟨t, ht⟩
        simp only [τ, conditionedSecondCoordinateFirstHit, boltzmannTau,
          dite_eq_left hh]
    apply propext
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, A, X,
      stoppedMap_pathCode_codeWalk, legalPast_codeWalk, true_and,
      hτ, ENat.toNat_natCast]
    have hend : (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ) := hω.2
    exact and_iff_left hend
  rw [hmap]
  have hd := iid_endpoint_eq_fiber r ell hr
  change D = _ at hd
  rw [hd]
  exact stoppedMap_cond_leftLength_procedureReading ell r hell hr

private theorem independent_cond_map {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → α) (g : Ω → β)
    (hf : Measurable f) (hI : IndepFun f g ν)
    (F : Set β) (hF : MeasurableSet F) (hpos : 0 < ν (g ⁻¹' F)) :
    (ν[|g ⁻¹' F]).map f = ν.map f := by
  ext T hT
  rw [Measure.map_apply hf hT, Measure.map_apply hf hT, cond_apply' (hf hT),
    Set.inter_comm, hI.measure_inter_preimage_eq_mul T F hT hF,
    mul_comm (ν (f ⁻¹' T)) (ν (g ⁻¹' F)), ← mul_assoc,
    ENNReal.inv_mul_cancel hpos.ne' (measure_ne_top _ _), one_mul]

/-- of the past KMSW map at the first hit τ_r of R = −r under the endpoint-conditioned
UIQBOT law, given the whole uncentered future; the renewal-time selection T_{m_k} -/
theorem firstHitPastMap_future_event_law
    (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell)
    (F : Set (ℕ → ℤ × ℤ)) (hF : MeasurableSet F) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    0 < μ (E ∩ Y ⁻¹' F) →
      (μ[|E ∩ Y ⁻¹' F]).map (fun p => stoppedMap r hr (pathCode p)) =
        ((boltzmannLaw ell r
          (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
          (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2).map
            (β := AllBoltzmannSpace r) (fun m => ⟨ell, m⟩)).map some := by
  dsimp only
  intro hpos
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  let Y := fun p => conditionedVectorShift (τ p).toNat p
  have hE : MeasurableSet E := endpoint_measurable r ell
  have hY : Measurable Y := measurable_conditionedFirstHit_future r
  have hposE : 0 < μ E := lt_of_lt_of_le hpos (measure_mono Set.inter_subset_left)
  have hposF : 0 < (μ[|E]) (Y ⁻¹' F) := cond_pos_of_inter_ne_zero hE hpos.ne'
  rw [← cond_cond_eq_cond_inter hE (hY hF) μ]
  exact (independent_cond_map (μ[|E]) (fun p => stoppedMap r hr (pathCode p)) Y
    ((measurable_stoppedMap r hr).comp measurable_pathCode)
    (pastMap_independent r ell hr hell hposE) F hF hposF).trans
      (firstHitPastMap_law r ell hr hell hposE)

/-- of the past KMSW map at the first hit τ_r of R = −r under the endpoint-conditioned
UIQBOT law, given the whole uncentered future; the renewal-time selection T_{m_k} -/
theorem firstHitPastMap_barrier_law
    (r ell k : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    0 < μ (E ∩ Y ⁻¹' barrierFutureEvent ell r k) →
      (μ[|E ∩ Y ⁻¹' barrierFutureEvent ell r k]).map
        (fun p => stoppedMap r hr (pathCode p)) =
          ((boltzmannLaw ell r
            (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
            (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2).map
              (β := AllBoltzmannSpace r) (fun m => ⟨ell, m⟩)).map some := by
  exact firstHitPastMap_future_event_law r ell hr hell (barrierFutureEvent ell r k)
    (measurableSet_barrierFutureEvent ell r k)

/-- of the past KMSW map at the first hit τ_r of R = −r under the endpoint-conditioned
UIQBOT law, given the whole uncentered future; the renewal-time selection T_{m_k} -/
theorem firstHitPastMap_condDistrib (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    0 < μ E →
      condDistrib (fun p => stoppedMap r hr (pathCode p)) Y (μ[|E])
        =ᵐ[(μ[|E]).map Y] fun _ =>
          ((boltzmannLaw ell r
            (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1
            (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).2).map
              (β := AllBoltzmannSpace r) (fun m => ⟨ell, m⟩)).map some := by
  dsimp only
  intro hpos
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  have hae : legalMap r hr =ᵐ[μ[|E]] fun p => stoppedMap r hr (pathCode p) :=
    cond_absolutelyContinuous.ae_le (legalMap_ae r hr)
  have hc := conditionedFirstHit_endpoint_condDistrib r ell hr hell (legalMap r hr)
    (fun T hT k => legalMap_past r hr T hT k ell) hpos
  rw [condDistrib_congr_left hae, Measure.map_congr hae,
    firstHitPastMap_law r ell hr hell hpos] at hc
  exact hc

/-- of the past KMSW map at the first hit τ_r of R = −r under the endpoint-conditioned
UIQBOT law, given the whole uncentered future; the renewal-time selection T_{m_k} -/
theorem firstHitPastMap_future_law (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    let E := {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
    let Y := fun p => conditionedVectorShift (τ p).toNat p
    0 < μ E → (μ[|E]).map Y = conditionedVectorPathLaw ell (-(r : ℤ)) := by
  exact conditionedFirstHit_endpoint_future_law r ell hr hell

end DirectedDistances.PaperProofs.Section4
