/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWForwardClass
public import DirectedDistances.KMSW.KMSWProcedureBijection
public import DirectedDistances.PlanarMap.FiniteBoltzmannMapLaw
public import DirectedDistances.KMSW.StoppedWalkLawSum
public import DirectedDistances.KMSW.MarkedWalkPartition

/-! # Map-valued stopped-walk law

Helper toward Lemmas 3.11 / 3.12 and `def-boltzmann-lr`
Surjectivity is a named hypothesis where used (`KMSWPeanoPrefixExistsFinal`).
The stopping walk has a random left boundary length, so its map value lies in
the dependent union of the fixed-left-length `BoltzmannSpace` types. Off the
stopping event the variable below is `none`. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Union of the fixed-left-length Boltzmann spaces for a fixed right length.
This is the codomain needed for the stopped walk, whose left length is random. -/
@[expose] noncomputable def AllBoltzmannSpace (r : ℕ) :=
  Σ ell : ℕ, BoltzmannSpace ell r

noncomputable instance (r : ℕ) : MeasurableSpace (AllBoltzmannSpace r) := ⊤

noncomputable instance (r : ℕ) :
    MeasurableSpace (Option (AllBoltzmannSpace r)) := ⊤

instance (r : ℕ) : Countable (AllBoltzmannSpace r) := by
  unfold AllBoltzmannSpace
  infer_instance

/-- The unrooted map class encoded by a positive-time stopped walk index. -/
@[expose] noncomputable def stoppedWalkMap
    {r : ℕ} (i : {i : StoppedWalkIndex r // 1 ≤ i.1}) :
    AllBoltzmannSpace r :=
  ⟨i.1.2.1, ⟨i.1.1, kmswToMapIsoClass i.2 i.1.2.2⟩⟩

/-- Lift the stopped-walk-to-map assignment to all indices, returning `none`
on the impossible zero-time layer. -/
@[expose] noncomputable def stoppedWalkMapOption (r : ℕ)
    (i : StoppedWalkIndex r) : Option (AllBoltzmannSpace r) :=
  if h : 1 ≤ i.1 then some (stoppedWalkMap ⟨i, h⟩) else none

/-- The map-valued random variable on the iid code stream. It is `some` of the
KMSW map class on the stopping event and `none` off that event. -/
@[expose] noncomputable def stoppedMap (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) : Option (AllBoltzmannSpace r) :=
  (stoppedIndex r hr ω).bind (stoppedWalkMapOption r)

/-- The map-valued stopped-walk variable is measurable, including its `none`
value off the stopping event. -/
theorem measurable_stoppedMap (r : ℕ) (hr : 1 ≤ r) :
    Measurable (stoppedMap r hr) := by
  let g : Option (StoppedWalkIndex r) → Option (AllBoltzmannSpace r) :=
    fun i => i.bind (stoppedWalkMapOption r)
  have hg : Measurable g := by
    intro s hs
    trivial
  change Measurable (g ∘ stoppedIndex r hr)
  exact hg.comp (measurable_stoppedIndex r hr)

/-- Distinct positive stopped-walk indices encode distinct unrooted map
classes. This is the required use of the injective half of Theorem 3.5. -/
theorem stoppedWalkMap_injective (r : ℕ) :
    Function.Injective (@stoppedWalkMap r) := by
  intro i j hij
  apply Subtype.ext
  rcases i with ⟨⟨n, ⟨ell, c⟩⟩, hn⟩
  rcases j with ⟨⟨n', ⟨ell', c'⟩⟩, hn'⟩
  change (⟨ell, ⟨n, kmswToMapIsoClass hn c⟩⟩ : AllBoltzmannSpace r) =
    ⟨ell', ⟨n', kmswToMapIsoClass hn' c'⟩⟩ at hij
  obtain ⟨hell, hinner⟩ := Sigma.mk.inj_iff.mp hij
  subst ell'
  have hinnerEq : (⟨n, kmswToMapIsoClass hn c⟩ : BoltzmannSpace ell r) =
      ⟨n', kmswToMapIsoClass hn' c'⟩ := by
    exact eq_of_heq hinner
  obtain ⟨hnn, hclass⟩ := Sigma.mk.inj_iff.mp hinnerEq
  subst n'
  have hclassEq : kmswToMapIsoClass hn c = kmswToMapIsoClass hn' c' := by
    exact eq_of_heq hclass
  have hcc : c = c' := kmswToMapIsoClass_injective hn hclassEq
  subst c'
  rfl

private theorem stoppedWalkMapOption_preimage_singleton (r : ℕ)
    (i : {i : StoppedWalkIndex r // 1 ≤ i.1}) :
    stoppedWalkMapOption r ⁻¹' {some (stoppedWalkMap i)} = {i.1} := by
  classical
  ext j
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hj
    unfold stoppedWalkMapOption at hj
    by_cases hn : 1 ≤ j.1
    · simp [hn] at hj
      have hij := stoppedWalkMap_injective r hj
      exact congrArg Subtype.val hij
    · simp [hn] at hj
  · intro hj
    subst j
    simp [stoppedWalkMapOption, i.2]

private theorem stoppedMap_preimage_singleton (r : ℕ) (hr : 1 ≤ r)
    (i : {i : StoppedWalkIndex r // 1 ≤ i.1}) :
    stoppedMap r hr ⁻¹' {some (stoppedWalkMap i)} =
      stoppedIndex r hr ⁻¹' {some i.1} := by
  classical
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  change ((stoppedIndex r hr ω).bind (stoppedWalkMapOption r) =
      some (stoppedWalkMap i)) ↔ stoppedIndex r hr ω = some i.1
  cases hidx : stoppedIndex r hr ω with
  | none => simp
  | some j =>
      simp only [Option.bind_some]
      have hmem : j ∈ stoppedWalkMapOption r ⁻¹'
          {some (stoppedWalkMap i)} ↔ j = i.1 := by
        rw [stoppedWalkMapOption_preimage_singleton]
        simp
      simpa [hidx] using hmem

/-- Joint mass of the conditioning event and one map class in the image of the
stopped-walk map. It equals the corresponding walk-class cylinder mass, -/
theorem iidCodeMeasure_event_stoppedMap_singleton_mass (r : ℕ)
    (hr : 1 ≤ r) (i : {i : StoppedWalkIndex r // 1 ≤ i.1}) :
    iidCodeMeasure (boltzmannEvent r ∩
        stoppedMap r hr ⁻¹' {some (stoppedWalkMap i)}) =
      (1 / 3 : ENNReal) ^ i.1.1 := by
  rw [stoppedMap_preimage_singleton]
  have hsub : stoppedWalkIndexSet i.1 ⊆ boltzmannEvent r := by
    intro ω hω
    have hcyl : ω ∈ stoppedCylinder i.1.2.2 := by
      simpa [stoppedWalkIndexSet, i.2] using hω
    exact (stoppedCylinder_subset_eventSlice i.2 i.1.2.2 hcyl).1
  have hpre : stoppedIndex r hr ⁻¹' {some i.1} = stoppedWalkIndexSet i.1 :=
    stoppedIndex_preimage_singleton r hr i.1
  rw [hpre, Set.inter_eq_right.mpr hsub]
  rw [show stoppedWalkIndexSet i.1 = stoppedCylinder i.1.2.2 by
    simp [stoppedWalkIndexSet, i.2]]
  exact iidCodeMeasure_stoppedCylinder_mass i.2 i.1.2.2

/-- The event/map-class joint mass is exactly the mass of the corresponding
stopped walk-class cylinder. -/
theorem iidCodeMeasure_event_stoppedMap_eq_walkClassMass (r : ℕ)
    (hr : 1 ≤ r) (i : {i : StoppedWalkIndex r // 1 ≤ i.1}) :
    iidCodeMeasure (boltzmannEvent r ∩
        stoppedMap r hr ⁻¹' {some (stoppedWalkMap i)}) =
      iidCodeMeasure (boltzmannEvent r ∩
        stoppedIndex r hr ⁻¹' {some i.1}) := by
  rw [stoppedMap_preimage_singleton]

/-- A map class outside the image of the stopped-walk encoding has zero joint
mass with the stopping event. -/
theorem iidCodeMeasure_event_stoppedMap_singleton_eq_zero (r : ℕ)
    (hr : 1 ≤ r) (q : AllBoltzmannSpace r)
    (hq : q ∉ Set.range (@stoppedWalkMap r)) :
    iidCodeMeasure (boltzmannEvent r ∩ stoppedMap r hr ⁻¹' {some q}) = 0 := by
  have hempty : boltzmannEvent r ∩ stoppedMap r hr ⁻¹' {some q} = ∅ := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hE, hmap⟩
    have hdecomp := boltzmannEvent_eq_iUnion_stoppedWalkIndex r hr
    have hmem : ω ∈ ⋃ j : StoppedWalkIndex r, stoppedWalkIndexSet j := by
      rw [← hdecomp]
      exact hE
    rcases Set.mem_iUnion.mp hmem with ⟨j, hj⟩
    have hjpos : 1 ≤ j.1 := by
      by_contra h
      have hjzero : j.1 = 0 := by omega
      simp [stoppedWalkIndexSet, hjzero] at hj
    have hidx : stoppedIndex r hr ω = some j := by
      have hmem' : ω ∈ stoppedIndex r hr ⁻¹' {some j} := by
        rw [stoppedIndex_preimage_singleton]
        exact hj
      simpa using hmem'
    have hval : stoppedMap r hr ω = some (stoppedWalkMap ⟨j, hjpos⟩) := by
      simp [stoppedMap, hidx, stoppedWalkMapOption, hjpos]
    have hmap' : stoppedMap r hr ω = some q :=
      Set.mem_singleton_iff.mp hmap
    have hqeq : q = stoppedWalkMap ⟨j, hjpos⟩ :=
      Option.some.inj (hmap'.symm.trans hval)
    exact hq ⟨⟨j, hjpos⟩, hqeq.symm⟩
  rw [hempty, measure_empty]

/-- Boltzmann weight on the dependent union of all fixed-left-length spaces. -/
@[expose] noncomputable def allBoltzmannWeight {r : ℕ}
    (q : AllBoltzmannSpace r) : ENNReal := boltzmannWeight q.2

/-- The Boltzmann partition sum restricted to the image of positive stopped
walk classes. -/
@[expose] noncomputable def stoppedMapRangePartition (r : ℕ) : ENNReal :=
  ∑' q : {q : AllBoltzmannSpace r //
      q ∈ Set.range (@stoppedWalkMap r)}, allBoltzmannWeight q.1

/-- Reindex the restricted map partition by its unique positive stopped-walk
class; injectivity makes this an equivalence of the index types. -/
theorem stoppedMapRangePartition_eq_tsum_walkIndices (r : ℕ) :
    stoppedMapRangePartition r =
      ∑' i : {i : StoppedWalkIndex r // 1 ≤ i.1},
        (1 / 3 : ENNReal) ^ i.1.1 := by
  classical
  let f : {i : StoppedWalkIndex r // 1 ≤ i.1} →
      {q : AllBoltzmannSpace r // q ∈ Set.range (@stoppedWalkMap r)} :=
    fun i => ⟨stoppedWalkMap i, ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      apply Subtype.ext
      exact congrArg Subtype.val
        (stoppedWalkMap_injective r (congrArg Subtype.val h))
    · intro q
      rcases q.2 with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hi
  let e := Equiv.ofBijective f hf
  rw [stoppedMapRangePartition]
  rw [← e.tsum_eq]
  apply tsum_congr
  intro i
  change allBoltzmannWeight (stoppedWalkMap i) =
    (1 / 3 : ENNReal) ^ i.1.1
  simp [allBoltzmannWeight, stoppedWalkMap, boltzmannWeight]





theorem stoppedMapRangePartition_eq_eventProbability
    (r : ℕ) (hr : 1 ≤ r) :
    stoppedMapRangePartition r = iidCodeMeasure (boltzmannEvent r) := by
  rw [stoppedMapRangePartition_eq_tsum_walkIndices]
  rw [iidCodeMeasure_boltzmannEvent_eq_tsum_walkWeights r hr]
  classical
  change (∑' i : {i : (Σ n : ℕ, Σ ell : ℕ, KMSWWalkClass ell r n) //
      1 ≤ i.1}, (1 / 3 : ENNReal) ^ i.1.1) = _
  let e : {i : (Σ n : ℕ, Σ ell : ℕ, KMSWWalkClass ell r n) // 1 ≤ i.1} ≃
      Σ n : {n : ℕ // 1 ≤ n}, Σ ell : ℕ, KMSWWalkClass ell r n.1 := {
    toFun := fun i => ⟨⟨i.1.1, i.2⟩, i.1.2⟩
    invFun := fun j => ⟨⟨j.1.1, j.2⟩, j.1.2⟩
    left_inv := by intro i; rfl
    right_inv := by intro j; rfl }
  let w : (Σ n : {n : ℕ // 1 ≤ n}, Σ ell : ℕ,
      KMSWWalkClass ell r n.1) → ENNReal := fun j =>
        (1 / 3 : ENNReal) ^ j.1.1
  change (∑' i : {i : (Σ n : ℕ, Σ ell : ℕ, KMSWWalkClass ell r n) //
      1 ≤ i.1}, w (e i)) = _
  rw [e.tsum_eq w]
  simp_rw [w]
  rw [tsum_sigma']
  change (∑' n : {n : ℕ // 1 ≤ n},
      ∑' j : (Σ ell : ℕ, KMSWWalkClass ell r n.1),
        (1 / 3 : ENNReal) ^ n.1) = _
  have hinner (n : {n : ℕ // 1 ≤ n}) :
      (∑' j : (Σ ell : ℕ, KMSWWalkClass ell r n.1),
        (1 / 3 : ENNReal) ^ n.1) =
      ∑' ell : ℕ,
        (Fintype.card (KMSWWalkClass ell r n.1) : ENNReal) *
          (1 / 3 : ENNReal) ^ n.1 := by
    rw [tsum_sigma']
    apply tsum_congr
    intro ell
    rw [tsum_fintype]
    simp [Finset.sum_const, nsmul_eq_mul]
  simp_rw [hinner]
  change (∑' n : {n : ℕ // n ∈ ({n : ℕ | 1 ≤ n} : Set ℕ)},
      ∑' ell : ℕ,
        (Fintype.card (KMSWWalkClass ell r n.1) : ENNReal) *
          (1 / 3 : ENNReal) ^ n.1) = _
  rw [tsum_subtype {n : ℕ | 1 ≤ n}
      (fun n => ∑' ell : ℕ,
        (Fintype.card (KMSWWalkClass ell r n) : ENNReal) *
          (1 / 3 : ENNReal) ^ n)]
  change (∑' n : ℕ, (Set.indicator {n | 1 ≤ n}
      (fun n => ∑' ell : ℕ,
        (Fintype.card (KMSWWalkClass ell r n) : ENNReal) *
          (1 / 3 : ENNReal) ^ n)) n) = _
  simp only [Set.indicator_apply]
  apply tsum_congr
  intro n
  by_cases hn : 1 ≤ n
  · simp [hn]
  · simp [hn]

/-- Normalized Boltzmann weights on the stopped-map image, represented as a
measure on the `Option` codomain. The range-restricted partition hypotheses
remain explicit. -/
@[expose] noncomputable def stoppedMapRangeLaw (r : ℕ)
    (_h0 : stoppedMapRangePartition r ≠ 0)
    (_htop : stoppedMapRangePartition r ≠ ⊤) :
    Measure (Option (AllBoltzmannSpace r)) :=
  (stoppedMapRangePartition r)⁻¹ •
    Measure.sum (fun q : {q : AllBoltzmannSpace r //
      q ∈ Set.range (@stoppedWalkMap r)} =>
        allBoltzmannWeight q.1 • Measure.dirac (some q.1))

/-- A singleton in the stopped-map range has its normalized Boltzmann
weight under `stoppedMapRangeLaw`. -/
theorem stoppedMapRangeLaw_singleton (r : ℕ)
    (h0 : stoppedMapRangePartition r ≠ 0)
    (htop : stoppedMapRangePartition r ≠ ⊤)
    (q : AllBoltzmannSpace r) (hq : q ∈ Set.range (@stoppedWalkMap r)) :
    stoppedMapRangeLaw r h0 htop {some q} =
      allBoltzmannWeight q / stoppedMapRangePartition r := by
  classical
  rw [stoppedMapRangeLaw, Measure.smul_apply, smul_eq_mul,
    Measure.sum_apply _ (measurableSet_singleton (some q))]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator_apply, mul_ite, Pi.one_apply, mul_one, mul_zero]
  rw [tsum_eq_single ⟨q, hq⟩]
  · simp [div_eq_mul_inv, mul_comm]
  · intro x hx
    have hne : x.1 ≠ q := by
      intro heq
      apply hx
      exact Subtype.ext heq
    simp [hne]

/-- Under conditioning on `E`, a map in the stopped-walk range has mass
proportional to its Boltzmann weight. -/
theorem iidCodeMeasure_cond_map_singleton_mass (r : ℕ) (hr : 1 ≤ r)
    (i : {i : StoppedWalkIndex r // 1 ≤ i.1}) :
    (iidCodeMeasure[|boltzmannEvent r]).map (stoppedMap r hr)
        {some (stoppedWalkMap i)} =
      (1 / 3 : ENNReal) ^ i.1.1 / iidCodeMeasure (boltzmannEvent r) := by
  rw [Measure.map_apply (measurable_stoppedMap r hr)
    (measurableSet_singleton _)]
  rw [ProbabilityTheory.cond_apply'
    (measurable_stoppedMap r hr (measurableSet_singleton _)) iidCodeMeasure]
  have hmass := iidCodeMeasure_event_stoppedMap_singleton_mass r hr i
  simp_rw [hmass]
  simp only [ENNReal.div_eq_inv_mul, mul_comm]

/-- Under the named open final-prefix step, every positive-size map class of
fixed boundary lengths is in the stopped-walk map range. Helper toward Lemmas
surjectivity is the named hypothesis `KMSWPeanoPrefixExistsFinal`. -/
theorem stoppedWalkMap_range_of_prefix (r ℓ n : ℕ) (hn : 1 ≤ n)
    (hprefix : KMSWPeanoPrefixExistsFinal ℓ r n)
    (q : KMSWMapIsoClass ℓ r n) :
    (⟨ℓ, ⟨n, q⟩⟩ : AllBoltzmannSpace r) ∈ Set.range (@stoppedWalkMap r) := by
  obtain ⟨c, hc⟩ := kmswToMapIsoClass_surjective_of_prefix hprefix hn q
  refine ⟨⟨⟨n, ⟨ℓ, c⟩⟩, hn⟩, ?_⟩
  change (⟨ℓ, ⟨n, kmswToMapIsoClass hn c⟩⟩ : AllBoltzmannSpace r) =
    ⟨ℓ, ⟨n, q⟩⟩
  exact congrArg (fun c : KMSWMapIsoClass ℓ r n =>
    (⟨ℓ, ⟨n, c⟩⟩ : AllBoltzmannSpace r)) hc

/-- Under `KMSWPeanoPrefixExistsFinal`, the conditional stopped-map law gives
each positive-size fixed-boundary map its Boltzmann weight divided by the
stopping-event probability. This is a helper toward Lemmas 3.11 / 3.12 and -/
theorem iidCodeMeasure_cond_map_singleton_mass_of_prefix
    (r : ℕ) (hr : 1 ≤ r) (ℓ n : ℕ) (hn : 1 ≤ n)
    (hprefix : KMSWPeanoPrefixExistsFinal ℓ r n)
    (q : KMSWMapIsoClass ℓ r n) :
    (iidCodeMeasure[|boltzmannEvent r]).map (stoppedMap r hr)
        {some (⟨ℓ, ⟨n, q⟩⟩ : AllBoltzmannSpace r)} =
      allBoltzmannWeight (⟨ℓ, ⟨n, q⟩⟩ : AllBoltzmannSpace r) /
        iidCodeMeasure (boltzmannEvent r) := by
  obtain ⟨c, hc⟩ := kmswToMapIsoClass_surjective_of_prefix hprefix hn q
  let i : {i : StoppedWalkIndex r // 1 ≤ i.1} := ⟨⟨n, ⟨ℓ, c⟩⟩, hn⟩
  have hi : stoppedWalkMap i =
      (⟨ℓ, ⟨n, q⟩⟩ : AllBoltzmannSpace r) := by
    change (⟨ℓ, ⟨n, kmswToMapIsoClass hn c⟩⟩ : AllBoltzmannSpace r) = _
    exact congrArg (fun c : KMSWMapIsoClass ℓ r n =>
      (⟨ℓ, ⟨n, c⟩⟩ : AllBoltzmannSpace r)) hc
  have hset : (Set.singleton (some (stoppedWalkMap i)) :
      Set (Option (AllBoltzmannSpace r))) =
      Set.singleton (some (⟨ℓ, ⟨n, q⟩⟩ : AllBoltzmannSpace r)) := by
    rw [hi]
    rfl
  calc
    (iidCodeMeasure[|boltzmannEvent r]).map (stoppedMap r hr)
        {some (⟨ℓ, ⟨n, q⟩⟩ : AllBoltzmannSpace r)} =
      (iidCodeMeasure[|boltzmannEvent r]).map (stoppedMap r hr)
        {some (stoppedWalkMap i)} :=
      congrArg ((iidCodeMeasure[|boltzmannEvent r]).map (stoppedMap r hr))
        hset.symm
    _ = (1 / 3 : ENNReal) ^ i.1.1 /
        iidCodeMeasure (boltzmannEvent r) :=
      iidCodeMeasure_cond_map_singleton_mass r hr i
    _ = allBoltzmannWeight (⟨ℓ, ⟨n, q⟩⟩ : AllBoltzmannSpace r) /
        iidCodeMeasure (boltzmannEvent r) := rfl

/-- The conditional map singleton weights agree with `stoppedMapRangeLaw` once
the explicit normalizer identity `P(E) = restricted partition` is applied. -/
theorem iidCodeMeasure_cond_map_singleton_eq_stoppedMapRangeLaw
    (r : ℕ) (hr : 1 ≤ r)
    (h0 : stoppedMapRangePartition r ≠ 0)
    (htop : stoppedMapRangePartition r ≠ ⊤)
    (i : {i : StoppedWalkIndex r // 1 ≤ i.1}) :
    (iidCodeMeasure[|boltzmannEvent r]).map (stoppedMap r hr)
        {some (stoppedWalkMap i)} =
      stoppedMapRangeLaw r h0 htop {some (stoppedWalkMap i)} := by
  rw [iidCodeMeasure_cond_map_singleton_mass r hr i]
  rw [stoppedMapRangeLaw_singleton r h0 htop (stoppedWalkMap i) ⟨i, rfl⟩]
  rw [stoppedMapRangePartition_eq_eventProbability r hr]
  rfl

end DirectedDistances.KMSW
