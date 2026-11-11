module

public import DirectedDistances.KMSW.StoppedMarkedBoltzmannLaw
import DirectedDistances.RandomWalk.ConditionedFirstHitPastCodeLaw
import DirectedDistances.KMSW.BoltzmannEndpointFiberLaw

/-! Supporting lemmas for paper labels `lem-uiqbot-boltzmann` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

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

private theorem iid_endpoint_mass (r ell : ℕ) (hr : 1 ≤ r) :
    iidCodeMeasure (boltzmannEvent r ∩
      {ω | (codeWalk ω (boltzmannTau r ω)).1 = (ell : ℤ)}) =
        boltzmannPartition ell r := by
  classical
  let s : Set (Option (AllBoltzmannSpace r)) :=
    {o | ∃ m : BoltzmannSpace ell r, o = some (⟨ell, m⟩ : AllBoltzmannSpace r)}
  have hs : MeasurableSet s := trivial
  have he : MeasurableSet (boltzmannEvent r) := by
    have heq : stoppedIndex r hr ⁻¹' {none} = (boltzmannEvent r)ᶜ := by
      ext ω
      simp [stoppedIndex]
    have hm := (measurable_stoppedIndex r hr) (measurableSet_singleton none)
    rw [heq] at hm
    exact hm.of_compl
  have hpre : (some : AllBoltzmannSpace r → Option (AllBoltzmannSpace r)) ⁻¹' s =
      {q | q.1 = ell} := by
    ext q
    constructor
    · rintro ⟨m, hm⟩
      exact congrArg Sigma.fst (Option.some.inj hm)
    · rcases q with ⟨k, m⟩
      intro hk
      change k = ell at hk
      subst k
      exact ⟨m, rfl⟩
  have h := congrArg (fun ν => ν s) (lem_kmsw_boltzmann_procedureReading r hr)
  rw [Measure.map_apply (measurable_stoppedMap r hr) hs,
    Measure.map_apply (measurable_of_countable _) hs, hpre,
    rightBoltzmannLaw_leftLength_fiber, cond_apply he] at h
  dsimp only [s] at h
  rw [← iid_endpoint_eq_fiber r ell hr] at h
  have hp := rightBoltzmannPartition_pos_lt_top r hr
  rw [← rightBoltzmannPartition_eq_eventProbability_procedureReading r hr] at h
  rw [ENNReal.div_eq_inv_mul] at h
  have hc := congrArg (fun x => rightBoltzmannPartition r * x) h
  simpa only [← mul_assoc, ENNReal.mul_inv_cancel hp.1 hp.2, one_mul] using hc

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9 -/
theorem stoppedMarked_endpoint_mass_raw (r ell : ℕ) (hr : 1 ≤ r) :
    conditionedVectorPathLaw 0 0
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}) =
      ((ell + 1 : ℕ) : ℝ≥0∞) * boltzmannPartition ell r := by
  classical
  have hpre (k : ℕ) : ∃ S : Set (Fin (k + 1) → ℤ × ℤ),
      {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} =
        conditionedVectorPrefix k ⁻¹' S := by
    obtain ⟨S, _, hS⟩ := MeasurableSpace.measurableSet_comap.mp
      (measurableSet_conditionedVectorPast_firstHit_eq r k)
    exact ⟨S, hS.symm⟩
  choose S hS using hpre
  have h := conditionedVectorPathLaw_zero_zero_firstHit_bridge r ell Set.univ S
    (fun k => by simpa only [Set.univ_inter] using hS k)
  simp only [Set.univ_inter, Set.preimage_univ] at h
  rw [iid_endpoint_mass r ell hr] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

private theorem endpoint_partition (r : ℕ) (hr : 1 ≤ r) :
    conditionedVectorPathLaw 0 0 = Measure.sum (fun ell : ℕ =>
      (conditionedVectorPathLaw 0 0).restrict
        ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
          {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)})) := by
  let μ := conditionedVectorPathLaw 0 0
  let τ := conditionedSecondCoordinateFirstHit r
  let E := fun ell : ℕ => {p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}
  have hp : ∀ᵐ p ∂μ, 1 ≤ (p (τ p).toNat).1 := by
    have h := firstHitPastMap_left_pos_ae r hr
    dsimp only at h
    rwa [firstHitPastMap_cond_finite_hit_eq r hr] at h
  have hc : ∀ᵐ p ∂μ, p ∈ ⋃ ell, E ell := by
    filter_upwards [hp, firstHitPastMap_finite_hit_ae r hr] with p hp hf
    apply Set.mem_iUnion.mpr
    refine ⟨(p (τ p).toNat).1.toNat, hf, ?_⟩
    change (p (τ p).toNat).1 = _
    omega
  have hd : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    exact hij (Int.natCast_inj.mp (hi.2.symm.trans hj.2))
  rw [← Measure.restrict_iUnion hd (fun ell => endpoint_measurable r ell),
    Measure.restrict_eq_self_of_ae_mem hc]




theorem stoppedMarked_partition_eq_one (r : ℕ) (hr : 1 ≤ r) :
    rightVertexMarkedPartition r = 1 := by
  have h := congrArg (fun ν : Measure (ℕ → ℤ × ℤ) => ν Set.univ)
    (endpoint_partition r hr)
  rw [measure_univ, Measure.sum_apply _ MeasurableSet.univ] at h
  simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h
  simp_rw [stoppedMarked_endpoint_mass_raw r _ hr] at h
  rw [rightVertexMarkedPartition_eq_tsum]
  change (∑' q : Σ ell : ℕ, BoltzmannSpace ell r,
    ((q.1 + 1 : ℕ) : ℝ≥0∞) * boltzmannWeight q.2) = 1
  rw [tsum_sigma']
  simp_rw [ENNReal.tsum_mul_left]
  exact h.symm



theorem stoppedMarked_endpoint_mass (r ell : ℕ) (hr : 1 ≤ r) :
    let μ := conditionedVectorPathLaw 0 0
    let τ := conditionedSecondCoordinateFirstHit r
    μ ({p | τ p < ⊤} ∩ {p | (p (τ p).toNat).1 = (ell : ℤ)}) =
      (((ell + 1 : ℕ) : ℝ≥0∞) * boltzmannPartition ell r) /
        rightVertexMarkedPartition r := by
  dsimp only
  rw [stoppedMarked_partition_eq_one r hr, div_one]
  exact stoppedMarked_endpoint_mass_raw r ell hr

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
not the paper result. -/
theorem stoppedMarked_endpoint_zero_null (r : ℕ) (hr : 1 ≤ r) :
    conditionedVectorPathLaw 0 0
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (0 : ℤ)}) = 0 := by
  have hp := firstHitPastMap_left_pos_ae r hr
  dsimp only at hp
  rw [firstHitPastMap_cond_finite_hit_eq r hr] at hp
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hp] with p hp
  rintro ⟨_, he⟩
  change (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = 0 at he
  omega

private theorem endpoint_positive (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell) :
    0 < conditionedVectorPathLaw 0 0
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}) := by
  rw [stoppedMarked_endpoint_mass_raw r ell hr]
  exact ENNReal.mul_pos (by positivity)
    (boltzmannPartition_ne_zero_and_ne_top ell r hell hr).1

private theorem endpoint_cond_singleton (r ell : ℕ) (hr : 1 ≤ r) (hell : 1 ≤ ell)
    (q : RightVertexMarkedBoltzmannSpace r) :
    (((conditionedVectorPathLaw 0 0)[|
      {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}]).map
          (stoppedMarked r hr)) {q} =
      if q.1.1 = ell then
        (allBoltzmannWeight q.1 / boltzmannPartition ell r) *
          (((ell + 1 : ℕ) : ℝ≥0∞)⁻¹) else 0 := by
  classical
  rw [stoppedMarked_endpoint_law r ell hr hell (endpoint_positive r ell hr hell)]
  erw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton q)]
  rcases q with ⟨⟨k, m⟩, j⟩
  by_cases hk : k = ell
  · subst k
    have he : (fun z : BoltzmannSpace ell r × Fin (ell + 1) =>
        (⟨⟨ell, z.1⟩, z.2⟩ : RightVertexMarkedBoltzmannSpace r)) ⁻¹'
          {⟨⟨ell, m⟩, j⟩} = {(m, j)} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        have hm := congrArg (fun q : RightVertexMarkedBoltzmannSpace r => q.1) h
        have hmark := (Sigma.mk.inj_iff.mp h).2
        exact Prod.ext (eq_of_heq (Sigma.mk.inj_iff.mp hm).2) (eq_of_heq hmark)
      · rintro rfl
        rfl
    erw [he, ← Set.singleton_prod_singleton, Measure.prod_prod,
      boltzmannLaw_singleton, Measure.uniformOfFinset_apply_singleton]
    simp only [Finset.mem_univ, ↓reduceIte, Finset.card_univ, Fintype.card_fin,
      allBoltzmannWeight, boltzmannWeight]
  · have he : (fun z : BoltzmannSpace ell r × Fin (ell + 1) =>
        (⟨⟨ell, z.1⟩, z.2⟩ : RightVertexMarkedBoltzmannSpace r)) ⁻¹'
          {⟨⟨k, m⟩, j⟩} = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      intro h
      exact hk (congrArg (fun q : RightVertexMarkedBoltzmannSpace r => q.1.1) h).symm
    erw [he, measure_empty]
    simp only [hk, ↓reduceIte]

private theorem endpoint_restrict_singleton (r ell : ℕ) (hr : 1 ≤ r)
    (q : RightVertexMarkedBoltzmannSpace r) :
    (((conditionedVectorPathLaw 0 0).restrict
      ({p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
        {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)})).map
          (stoppedMarked r hr)) {q} =
      if q.1.1 = ell then allBoltzmannWeight q.1 else 0 := by
  classical
  by_cases hell : 1 ≤ ell
  · let μ := conditionedVectorPathLaw 0 0
    let E := {p | conditionedSecondCoordinateFirstHit r p < ⊤} ∩
      {p | (p (conditionedSecondCoordinateFirstHit r p).toNat).1 = (ell : ℤ)}
    have hp : 0 < μ E := endpoint_positive r ell hr hell
    have he : μ.restrict E = μ E • μ[|E] := by
      rw [ProbabilityTheory.cond, smul_smul,
        ENNReal.mul_inv_cancel hp.ne' (measure_ne_top μ E), one_smul]
    change ((μ.restrict E).map (stoppedMarked r hr)) {q} = _
    rw [he, Measure.map_smul _ (measurable_stoppedMarked r hr).aemeasurable,
      Measure.smul_apply, smul_eq_mul]
    rw [endpoint_cond_singleton r ell hr hell q]
    by_cases hq : q.1.1 = ell
    · rw [ite_eq_left hq, ite_eq_left hq]
      rw [show μ E = ((ell + 1 : ℕ) : ℝ≥0∞) * boltzmannPartition ell r from
        stoppedMarked_endpoint_mass_raw r ell hr]
      have ha0 : ((ell + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
      have hat : ((ell + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := by finiteness
      have hz := boltzmannPartition_ne_zero_and_ne_top ell r hell hr
      rw [div_eq_mul_inv]
      calc
        _ = ((((ell + 1 : ℕ) : ℝ≥0∞) * ((ell + 1 : ℕ) : ℝ≥0∞)⁻¹) *
            (boltzmannPartition ell r * (boltzmannPartition ell r)⁻¹)) *
              allBoltzmannWeight q.1 := by
                simp only [mul_assoc, mul_left_comm, mul_comm]
        _ = _ := by rw [ENNReal.mul_inv_cancel ha0 hat,
          ENNReal.mul_inv_cancel hz.1 hz.2, one_mul, one_mul]
    · rw [ite_eq_right hq, ite_eq_right hq, mul_zero]
  · have hel : ell = 0 := by omega
    subst ell
    erw [Measure.restrict_eq_zero.mpr (stoppedMarked_endpoint_zero_null r hr),
      Measure.map_zero]
    simp only [Measure.coe_zero, Pi.zero_apply]
    have hqpos : 1 ≤ q.1.1 := by
      obtain ⟨R⟩ := Quotient.exists_rep q.1.2.2
      exact R.B.left_length_pos
    rw [ite_eq_right (by omega : q.1.1 ≠ 0)]

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
the first R-hit of −r and the post-hit-minimum mark index is the marked Boltzmann
mark). The geometric identification of the mark with the last shared left-boundary
vertex is StoppedLeftBoundaryMarkAE; the edge-count clause, the no-missing-edges
clause and the source-map binding are not treated here; not the paper result. -/
theorem stoppedMarked_law (r : ℕ) (hr : 1 ≤ r) :
    (conditionedVectorPathLaw 0 0).map (stoppedMarked r hr) =
      rightVertexMarkedBoltzmannLaw r := by
  classical
  apply Measure.ext_of_singleton
  intro q
  have hs := endpoint_partition r hr
  have hmap := congrArg (fun μ => μ.map (stoppedMarked r hr)) hs
  rw [Measure.map_sum (measurable_stoppedMarked r hr).aemeasurable] at hmap
  rw [hmap, Measure.sum_apply _ (measurableSet_singleton q)]
  simp_rw [endpoint_restrict_singleton r _ hr q]
  rw [tsum_eq_single q.1.1]
  · rw [ite_eq_left rfl, rightVertexMarkedBoltzmannLaw,
      Measure.smul_apply, smul_eq_mul, Measure.sum_smul_dirac_singleton,
      stoppedMarked_partition_eq_one r hr, inv_one, one_mul]
    rfl
  · intro ell hell
    exact ite_eq_right (Ne.symm hell)

end DirectedDistances.KMSW
