module

public import DirectedDistances.PlanarMap.FacedFramedBall
public import DirectedDistances.Probability.BSLocalCriterion

public section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap
open DirectedDistances.Probability
open Set
open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

universe u v

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
A countable system of compatible ball classes on a universe-polymorphic object type.
If no radius agrees, the distance is the empty infimum, namely ⊤ (∞). -/
structure RootedBallSystem (C : Type v) [Countable C] where
  Object : Type u
  ballClass : ℕ → Object → C
  restriction_compatible : ∀ r x y,
    ballClass (r + 1) x = ballClass (r + 1) y → ballClass r x = ballClass r y

namespace RootedBallSystem

variable {C : Type v} [Countable C]

local instance instMeasurableSpaceGenericClass : MeasurableSpace C := ⊤

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic compatible class-system helper.
If no radius agrees, the infimum is empty and the distance is ⊤ (∞).
Index `r` is source radius `r + 1`, so the weight
`2⁻¹ ^ (r + 1)` is `2 ^ (-(source radius))`. -/
@[expose] noncomputable def bsLocalDistanceGeneric (S : RootedBallSystem C)
    (x y : S.Object) : ℝ≥0∞ :=
  ⨅ r : ℕ, ⨅ (_ : S.ballClass r x = S.ballClass r y),
    (2 : ℝ≥0∞)⁻¹ ^ (r + 1)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic compatible class-system helper. -/
theorem bsLocalDistance_le_of_ballClass_eqGeneric (S : RootedBallSystem C)
    (x y : S.Object) (r : ℕ)
    (h : S.ballClass r x = S.ballClass r y) :
    bsLocalDistanceGeneric S x y ≤ (2 : ℝ≥0∞)⁻¹ ^ (r + 1) := by
  unfold bsLocalDistanceGeneric
  exact iInf_le_of_le r (iInf_le_of_le h le_rfl)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic compatible class-system helper. -/
theorem bsLocalDistance_le_iff_ballClass_eqGeneric (S : RootedBallSystem C)
    (x y : S.Object) (r : ℕ) :
    bsLocalDistanceGeneric S x y ≤ (2 : ℝ≥0∞)⁻¹ ^ (r + 1) ↔
      S.ballClass r x = S.ballClass r y := by
  constructor
  · intro h
    by_contra hne
    have hno (s : ℕ) (hrs : r ≤ s)
        (heq : S.ballClass s x = S.ballClass s y) : False := by
      apply hne
      exact localClass_eq_of_le S.ballClass S.restriction_compatible
        hrs heq
    have hpow (m n : ℕ) :
        (2 : ℝ≥0∞)⁻¹ ^ m < (2 : ℝ≥0∞)⁻¹ ^ n ↔ n < m := by
      rw [← ENNReal.coe_inv_two, ← ENNReal.coe_pow, ← ENNReal.coe_pow,
        ENNReal.coe_lt_coe]
      exact pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)
    have hsmall : (2 : ℝ≥0∞)⁻¹ ^ (r + 1) < (2 : ℝ≥0∞)⁻¹ ^ r :=
      (hpow (r + 1) r).2 (by omega)
    have hbound : (2 : ℝ≥0∞)⁻¹ ^ r ≤ bsLocalDistanceGeneric S x y := by
      unfold bsLocalDistanceGeneric
      apply le_iInf
      intro s
      apply le_iInf
      intro heq
      by_cases hrs : r ≤ s
      · exact (hno s hrs heq).elim
      · have hs : s + 1 ≤ r := by omega
        exact pow_le_pow_right_of_le_one'
          (ENNReal.inv_le_one.2 ENNReal.one_lt_two.le) hs
    have hgt : (2 : ℝ≥0∞)⁻¹ ^ (r + 1) < bsLocalDistanceGeneric S x y :=
      hsmall.trans_le hbound
    change bsLocalDistanceGeneric S x y ≤ (2 : ℝ≥0∞)⁻¹ ^ (r + 1) at h
    exact (not_le_of_gt hgt) h
  · exact bsLocalDistance_le_of_ballClass_eqGeneric S x y r

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic compatible class-system helper. -/
theorem bsLocalDistance_selfGeneric (S : RootedBallSystem C) (x : S.Object) :
    bsLocalDistanceGeneric S x x = 0 := by
  have hpow : Tendsto (fun r : ℕ => (2 : ℝ≥0∞)⁻¹ ^ (r + 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (2 : ℝ≥0∞)⁻¹ ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (2 : ℝ≥0∞)⁻¹ < 1 by norm_num)
    exact h.comp (tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id)
  apply le_antisymm
  · apply le_of_tendsto_of_tendsto' tendsto_const_nhds hpow
    intro r
    exact bsLocalDistance_le_of_ballClass_eqGeneric S x x r rfl
  · exact bot_le

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic compatible class-system helper. -/
theorem bsLocalDistance_symmGeneric (S : RootedBallSystem C) (x y : S.Object) :
    bsLocalDistanceGeneric S x y = bsLocalDistanceGeneric S y x := by
  apply le_antisymm
  · unfold bsLocalDistanceGeneric
    apply le_iInf
    intro r
    apply le_iInf
    intro h
    exact iInf_le_of_le r (iInf_le_of_le h.symm le_rfl)
  · unfold bsLocalDistanceGeneric
    apply le_iInf
    intro r
    apply le_iInf
    intro h
    exact iInf_le_of_le r (iInf_le_of_le h.symm le_rfl)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic compatible class-system helper. -/
theorem bsLocalDistance_ultrametricGeneric (S : RootedBallSystem C)
    (x y z : S.Object) :
    bsLocalDistanceGeneric S x z ≤
      max (bsLocalDistanceGeneric S x y) (bsLocalDistanceGeneric S y z) := by
  by_contra h
  have hlt : max (bsLocalDistanceGeneric S x y) (bsLocalDistanceGeneric S y z) <
      bsLocalDistanceGeneric S x z := lt_of_not_ge h
  obtain ⟨ε, hmaxε, hεxz⟩ := exists_between hlt
  have hxyε : bsLocalDistanceGeneric S x y < ε :=
    (le_max_left _ _).trans_lt hmaxε
  have hyzε : bsLocalDistanceGeneric S y z < ε :=
    (le_max_right _ _).trans_lt hmaxε
  have hxyw : ∃ r, ∃ h : S.ballClass r x = S.ballClass r y,
      (2 : ℝ≥0∞)⁻¹ ^ (r + 1) < ε := by
    simpa only [bsLocalDistanceGeneric, iInf_lt_iff] using hxyε
  have hyzw : ∃ r, ∃ h : S.ballClass r y = S.ballClass r z,
      (2 : ℝ≥0∞)⁻¹ ^ (r + 1) < ε := by
    simpa only [bsLocalDistanceGeneric, iInf_lt_iff] using hyzε
  rcases hxyw with ⟨r, hxy, hrε⟩
  rcases hyzw with ⟨s, hyz, hsε⟩
  let q := min r s
  have hxyq : S.ballClass q x = S.ballClass q y :=
    localClass_eq_of_le S.ballClass S.restriction_compatible
      (show q ≤ r by omega) hxy
  have hyzq : S.ballClass q y = S.ballClass q z :=
    localClass_eq_of_le S.ballClass S.restriction_compatible
      (show q ≤ s by omega) hyz
  have hxzq : S.ballClass q x = S.ballClass q z := hxyq.trans hyzq
  have hqε : (2 : ℝ≥0∞)⁻¹ ^ (q + 1) < ε := by
    dsimp [q]
    by_cases hrs : r ≤ s
    · rw [min_eq_left hrs]
      exact hrε
    · have hsr : s ≤ r := by omega
      rw [min_eq_right hsr]
      exact hsε
  have hdistε : bsLocalDistanceGeneric S x z < ε :=
    (bsLocalDistance_le_of_ballClass_eqGeneric S x z q hxzq).trans_lt hqε
  exact (lt_asymm hdistε hεxz)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic compatible class-system helper. -/
theorem bsLocalDistance_triangleGeneric (S : RootedBallSystem C)
    (x y z : S.Object) :
    bsLocalDistanceGeneric S x z ≤
      bsLocalDistanceGeneric S x y + bsLocalDistanceGeneric S y z := by
  calc
    bsLocalDistanceGeneric S x z ≤
        max (bsLocalDistanceGeneric S x y) (bsLocalDistanceGeneric S y z) :=
      bsLocalDistance_ultrametricGeneric S x y z
    _ ≤ bsLocalDistanceGeneric S x y + bsLocalDistanceGeneric S y z :=
      max_le (le_add_of_nonneg_right (by positivity))
        (le_add_of_nonneg_left (by positivity))

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic compatible class-system helper. -/
theorem bsLocalDistance_ball_eqGeneric (S : RootedBallSystem C) (x : S.Object)
    (ε : ℝ≥0∞) :
    {y | bsLocalDistanceGeneric S x y < ε} =
      ⋃ r : {r : ℕ // (2 : ℝ≥0∞)⁻¹ ^ (r + 1) < ε},
        S.ballClass r.val ⁻¹' {S.ballClass r.val x} := by
  ext y
  simp only [mem_ofPred_eq, bsLocalDistanceGeneric, iInf_lt_iff, mem_iUnion,
    mem_preimage, mem_singleton_iff]
  exact ⟨fun ⟨r, h, hr⟩ => ⟨⟨r, hr⟩, h.symm⟩,
    fun ⟨r, h⟩ => ⟨r.val, h.symm, r.property⟩⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic compatible class-system helper. -/
theorem bsLocalDistance_ballClass_eq_ballGeneric (S : RootedBallSystem C)
    (r : ℕ) (x : S.Object) :
    S.ballClass r ⁻¹' {S.ballClass r x} =
      {y | bsLocalDistanceGeneric S x y < (2 : ℝ≥0∞)⁻¹ ^ r} := by
  have hpow (m n : ℕ) :
      (2 : ℝ≥0∞)⁻¹ ^ m < (2 : ℝ≥0∞)⁻¹ ^ n ↔ n < m := by
    rw [← ENNReal.coe_inv_two, ← ENNReal.coe_pow, ← ENNReal.coe_pow,
      ENNReal.coe_lt_coe]
    exact pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)
  ext y
  simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
  constructor
  · intro h
    apply (show bsLocalDistanceGeneric S x y < (2 : ℝ≥0∞)⁻¹ ^ r from ?_)
    apply (bsLocalDistance_le_of_ballClass_eqGeneric S x y r h.symm).trans_lt
    exact (hpow (r + 1) r).2 (by omega)
  · intro h
    have h' : ∃ s, ∃ heq : S.ballClass s x = S.ballClass s y,
        (2 : ℝ≥0∞)⁻¹ ^ (s + 1) < (2 : ℝ≥0∞)⁻¹ ^ r := by
      simpa only [bsLocalDistanceGeneric, iInf_lt_iff] using h
    rcases h' with ⟨s, heq, hs⟩
    have hrs' : r + 1 ≤ s + 1 :=
      Nat.succ_le_iff.mpr ((hpow (s + 1) r).mp hs)
    have hrs : r ≤ s := by omega
    exact (localClass_eq_of_le S.ballClass S.restriction_compatible hrs heq).symm

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic compatible class-system helper. -/
@[expose, instance_reducible] def bsLocalDistanceTopologyGeneric (S : RootedBallSystem C) :
    TopologicalSpace S.Object :=
  TopologicalSpace.generateFrom
    {s | ∃ x ε, s = {y | bsLocalDistanceGeneric S x y < ε}}

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic compatible class-system helper. -/
theorem bsLocalDistanceTopology_eq_localClassTopologyGeneric
    (S : RootedBallSystem C) :
    bsLocalDistanceTopologyGeneric S = localClassTopology S.ballClass := by
  apply le_antisymm
  · let := bsLocalDistanceTopologyGeneric S
    apply le_generateFrom
    rintro t ⟨r, c, rfl⟩
    cases r with
    | zero =>
        rcases eq_empty_or_nonempty (S.ballClass 0 ⁻¹' {c}) with h | ⟨x, hx⟩
        · rw [h]
          exact isOpen_empty
        · have hx' : S.ballClass 0 x = c := hx
          rw [← hx', bsLocalDistance_ballClass_eq_ballGeneric]
          exact TopologicalSpace.GenerateOpen.basic _ ⟨x, 1, by norm_num⟩
    | succ r =>
        rcases eq_empty_or_nonempty
            (S.ballClass (r + 1) ⁻¹' {c}) with h | ⟨x, hx⟩
        · rw [h]
          exact isOpen_empty
        · have hx' : S.ballClass (r + 1) x = c := hx
          rw [← hx', bsLocalDistance_ballClass_eq_ballGeneric]
          exact TopologicalSpace.GenerateOpen.basic _
            ⟨x, (2 : ℝ≥0∞)⁻¹ ^ (r + 1), rfl⟩
  · let := localClassTopology S.ballClass
    apply le_generateFrom
    rintro t ⟨x, ε, rfl⟩
    rw [bsLocalDistance_ball_eqGeneric]
    exact isOpen_iUnion fun r =>
      isOpen_localCylinder S.ballClass r.val (S.ballClass r.val x)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic compatible class-system helper. -/
theorem def_3_9_bs_topology_providerGeneric (S : RootedBallSystem C) :
    letI : TopologicalSpace C := ⊥
    letI : DiscreteTopology C := ⟨rfl⟩
    letI : MeasurableSpace C := ⊤
    letI := bsLocalDistanceTopologyGeneric S
    letI := borel S.Object
    letI : BorelSpace S.Object := ⟨rfl⟩
    ∀ {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
      {μs : ι → ProbabilityMeasure S.Object} {μ : ProbabilityMeasure S.Object},
      Tendsto μs L (𝓝 μ) ↔
        ∀ r, Tendsto (fun i => (μs i).map (S.ballClass r)) L
          (𝓝 ((μ.map (S.ballClass r)))) := by
  let : TopologicalSpace C := ⊥
  let : DiscreteTopology C := ⟨rfl⟩
  let : MeasurableSpace C := ⊤
  have htop := bsLocalDistanceTopology_eq_localClassTopologyGeneric S
  rw [htop]
  intro ι L hL μs μ
  exact (tendsto_iff_localClass_map S.ballClass S.restriction_compatible)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic measurability helper for the compatible class system. -/
private theorem localClass_coordinateSigma_eq_generateFrom
    (S : RootedBallSystem C) :
    MeasurableSpace.generateFrom (localCylinders S.ballClass) =
      ⨆ r, MeasurableSpace.comap (S.ballClass r) ⊤ := by
  classical
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro t ⟨r, c, rfl⟩
    rw [MeasurableSpace.measurableSet_iSup]
    exact MeasurableSpace.GenerateMeasurable.basic _ ⟨r, by
      exact ⟨{c}, by simp, rfl⟩⟩
  · apply iSup_le
    intro r s hs
    rcases hs with ⟨t, ht, rfl⟩
    have hset : S.ballClass r ⁻¹' t =
        ⋃ c ∈ t, S.ballClass r ⁻¹' {c} := by
      ext x
      simp only [mem_preimage, mem_iUnion, mem_singleton_iff]
      constructor
      · intro hx
        exact ⟨S.ballClass r x, hx, rfl⟩
      · rintro ⟨c, hc, hxc⟩
        exact hxc ▸ hc
    rw [hset]
    exact MeasurableSet.biUnion (Set.to_countable t) fun c hc =>
      MeasurableSpace.measurableSet_generateFrom
        (show S.ballClass r ⁻¹' {c} ∈ localCylinders S.ballClass from ⟨r, c, rfl⟩)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic measurability helper for the compatible class system. -/
theorem borel_bsLocalDistanceTopology_eq_iSup_ballClass_generic
    (S : RootedBallSystem C) :
    letI : TopologicalSpace S.Object := bsLocalDistanceTopologyGeneric S
    borel S.Object = ⨆ r, MeasurableSpace.comap (S.ballClass r) ⊤ := by
  rw [bsLocalDistanceTopology_eq_localClassTopologyGeneric S]
  rw [borel_localClassTopology S.ballClass]
  exact localClass_coordinateSigma_eq_generateFrom S

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic measurability helper for the compatible class system. -/
theorem measurable_into_iff_ballClass_generic
    {α : Type*} [MeasurableSpace α]
    (S : RootedBallSystem C) (f : α → S.Object) :
    letI : TopologicalSpace S.Object := bsLocalDistanceTopologyGeneric S
    letI : MeasurableSpace S.Object := borel S.Object
    letI : MeasurableSpace C := ⊤
    Measurable f ↔ ∀ r, Measurable (S.ballClass r ∘ f) := by
  rw [measurable_iff_comap_le, borel_bsLocalDistanceTopology_eq_iSup_ballClass_generic]
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    iSup_le_iff, measurable_iff_comap_le]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Generic measurability helper for the compatible class system. -/
theorem measure_eq_of_ballClass_map_eq_generic
    (S : RootedBallSystem C) :
    letI : TopologicalSpace S.Object := bsLocalDistanceTopologyGeneric S
    letI : MeasurableSpace S.Object := borel S.Object
    letI : MeasurableSpace C := ⊤
    ∀ {μ ν : Measure S.Object} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      (∀ r, μ.map (S.ballClass r) = ν.map (S.ballClass r)) → μ = ν := by
  intro μ ν hμ hν hmap
  let : TopologicalSpace S.Object := bsLocalDistanceTopologyGeneric S
  let : MeasurableSpace S.Object := borel S.Object
  let : MeasurableSpace C := ⊤
  have hA : @borel S.Object (bsLocalDistanceTopologyGeneric S) =
      MeasurableSpace.generateFrom (localCylinders S.ballClass) := by
    rw [borel_bsLocalDistanceTopology_eq_iSup_ballClass_generic]
    exact (localClass_coordinateSigma_eq_generateFrom S).symm
  have hC : ∀ t ∈ localCylinders S.ballClass, μ t = ν t := by
    rintro t ⟨r, c, rfl⟩
    have h := congrArg (fun m : Measure C => m {c}) (hmap r)
    have hmeas : Measurable (S.ballClass r) := by
      apply measurable_iff_comap_le.mpr
      change MeasurableSpace.comap (S.ballClass r) ⊤ ≤ borel S.Object
      rw [borel_bsLocalDistanceTopology_eq_iSup_ballClass_generic]
      exact le_iSup_of_le r le_rfl
    rw [Measure.map_apply hmeas MeasurableSet.of_discrete,
      Measure.map_apply hmeas MeasurableSet.of_discrete] at h
    exact h
  exact MeasureTheory.ext_of_generate_finite (localCylinders S.ballClass) hA
    (isPiSystem_localCylinders S.ballClass S.restriction_compatible) hC (by simp)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Rooted locally finite maps form a compatible system of faced ball classes. -/
@[expose] noncomputable def rootedLocallyFiniteFacedBallSystem :
    RootedBallSystem FacedFramedBallClass where
  Object := RootedLocallyFinitePlanarMap
  ballClass := rootedLocallyFiniteFacedBallClass
  restriction_compatible := rootedLocallyFiniteFacedBallRestrictionCompatible_proved

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Convergence in law is characterized by convergence of every faced ball-class law. -/
theorem def_3_9_rootedLocallyFiniteFacedBall_criterion :
    letI : TopologicalSpace FacedFramedBallClass := ⊥
    letI : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
    letI : MeasurableSpace FacedFramedBallClass := ⊤
    letI : TopologicalSpace RootedLocallyFinitePlanarMap :=
      bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem
    letI : MeasurableSpace RootedLocallyFinitePlanarMap :=
      borel RootedLocallyFinitePlanarMap
    letI : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
    ∀ {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
      {μs : ι → ProbabilityMeasure RootedLocallyFinitePlanarMap}
      {μ : ProbabilityMeasure RootedLocallyFinitePlanarMap},
      Tendsto μs L (𝓝 μ) ↔
        ∀ r, Tendsto (fun i => (μs i).map
          (rootedLocallyFiniteFacedBallClass r)) L
          (𝓝 (μ.map (rootedLocallyFiniteFacedBallClass r))) := by
  exact def_3_9_bs_topology_providerGeneric rootedLocallyFiniteFacedBallSystem

end RootedBallSystem

end DirectedDistances.PaperProofs.Section3
