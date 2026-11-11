module

public import DirectedDistances.RandomWalk.ConditionedVectorTrajectory
public import DirectedDistances.RandomWalk.ConditionedVectorTail
public import DirectedDistances.Probability.FinitePartition

/-! # Markov properties of the conditioned vector path law

The fixed-time and stopping-time Markov properties used at
Finite-prefix conditional laws are identified with the actual conditioned
path laws by their prefix characterizations. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

/-- The prefix through time `k`, including the state at time `k`. -/
@[expose] def conditionedVectorPrefix (k : ℕ) (p : ℕ → ℤ × ℤ) :
    Fin (k + 1) → ℤ × ℤ := fun j => p j.val

/-- The path viewed from time `k`, retaining its value at time `k`. -/
@[expose] def conditionedVectorShift (k : ℕ) (p : ℕ → ℤ × ℤ) :
    ℕ → ℤ × ℤ := fun j => p (k + j)

theorem measurable_conditionedVectorPrefix (k : ℕ) :
    Measurable (conditionedVectorPrefix k) := by
  exact measurable_pi_iff.mpr fun j => measurable_pi_apply j.val

theorem measurable_conditionedVectorShift (k : ℕ) :
    Measurable (conditionedVectorShift k) := by
  exact measurable_pi_iff.mpr fun j => measurable_pi_apply (k + j)

/-- The natural filtration of the conditioned vector path, with time `k`
containing exactly the information in coordinates `0` through `k`. -/
@[expose, instance_reducible] def conditionedVectorPast (k : ℕ) : MeasurableSpace (ℕ → ℤ × ℤ) :=
  MeasurableSpace.comap (conditionedVectorPrefix k) inferInstance

private theorem map_restrict_eq_smul_of_cond_map_eq
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (J : Set Ω) (hJ : MeasurableSet J)
    (f : Ω → α) (hf : Measurable f) (ρ : Measure α)
    (h : (ProbabilityTheory.cond μ J).map f = ρ) :
    (μ.restrict J).map f = μ J • ρ := by
  ext E hE
  rw [Measure.map_apply hf hE, Measure.restrict_apply (hE.preimage hf),
    Measure.smul_apply, smul_eq_mul, Set.inter_comm]
  have hh := congrArg (fun ν : Measure α => ν E) h
  rw [Measure.map_apply hf hE] at hh
  rw [← cond_mul_eq_inter hJ (f ⁻¹' E) μ, hh, mul_comm]

private theorem conditionedVectorCylinder_future_law
    (x : ℕ) (y : ℤ) (ν : Measure (ℕ → ℤ × ℤ)) [IsProbabilityMeasure ν]
    (hRN : ∀ n : ℕ,
      ν.map (fun q => fun j : Fin (n + 1) => q j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin n → Fin 3))).map
          (lazyTwoDimensionalPrefix (x : ℤ) y)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last n)).1 : ℝ) + 1) / ((x : ℝ) + 1)) else 0))
    (n : ℕ) (w : Fin n → Fin 3)
    (hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1)
    (B : Set (ℕ → ℤ × ℤ)) (hB : MeasurableSet B) :
    ν ({p | (fun j : Fin (n + 1) => p j.val) =
      lazyTwoDimensionalPrefix (x : ℤ) y w} ∩
      (fun p k => p (n + k)) ⁻¹' B) =
      ν {p | (fun j : Fin (n + 1) => p j.val) =
        lazyTwoDimensionalPrefix (x : ℤ) y w} *
      conditionedVectorPathLaw
        (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1.toNat
        (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2 B := by
  classical
  let C : Set (ℕ → ℤ × ℤ) :=
    {p | (fun j : Fin (n + 1) => p j.val) =
      lazyTwoDimensionalPrefix (x : ℤ) y w}
  let X : ℕ := (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1.toNat
  let Y : ℤ := (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2
  let f : (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ) := fun p k => p (n + k)
  have hC : MeasurableSet C := (measurableSet_singleton _).preimage (by fun_prop)
  have hX : (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).1 = (X : ℤ) :=
    (Int.toNat_of_nonneg (hw (Fin.last n))).symm
  have hpos : 0 < ν C :=
    (conditionedSource_prefix_atom_pos_iff x y ν hRN n w).2 hw
  let η : Measure (ℕ → ℤ × ℤ) :=
    (ν C)⁻¹ • (ν.restrict C).map f
  have hηRN : ∀ m : ℕ,
      η.map (fun p => fun j : Fin (m + 1) => p j.val) =
        ((Measure.uniformOfFinset (Finset.univ : Finset (Fin m → Fin 3))).map
          (lazyTwoDimensionalPrefix (X : ℤ)
            (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last n)).2)).withDensity
          (fun q => if ∀ j, 0 ≤ (q j).1 then
            ENNReal.ofReal ((((q (Fin.last m)).1 : ℝ) + 1) / ((X : ℝ) + 1)) else 0) := by
    simpa [η, C, f, X] using
      (conditionedSource_normalized_tail_RN x y ν hRN n X w hw hX)
  have hcond : (ProbabilityTheory.cond ν C).map f =
      conditionedVectorPathLaw X Y := by
    have heta : η = (ProbabilityTheory.cond ν C).map f := by
      change (ν C)⁻¹ • (ν.restrict C).map f =
        ((ν C)⁻¹ • ν.restrict C).map f
      rw [Measure.map_smul _ (by fun_prop)]
    have hcondprob : IsProbabilityMeasure (ProbabilityTheory.cond ν C) :=
      ProbabilityTheory.cond_isProbabilityMeasure hpos.ne'
    have hηprob : IsProbabilityMeasure η := by
      rw [heta]
      exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr hcondprob
    letI := hηprob
    have hηeq : η = conditionedVectorPathLaw X Y :=
      conditioned_vector_law_unique X Y η (conditionedVectorPathLaw X Y)
        hηRN (conditionedVectorPathLaw_map_prefix X Y)
    exact heta.symm.trans hηeq
  have hmap := map_restrict_eq_smul_of_cond_map_eq ν C hC f (by fun_prop)
    (conditionedVectorPathLaw X Y) hcond
  have hmapB := congrArg (fun μ : Measure (ℕ → ℤ × ℤ) => μ B) hmap
  rw [Measure.map_apply (by fun_prop) hB,
    Measure.restrict_apply (hB.preimage (by fun_prop)), Measure.smul_apply,
    smul_eq_mul, Set.inter_comm] at hmapB
  change ν (C ∩ f ⁻¹' B) = ν C * conditionedVectorPathLaw X Y B
  exact hmapB

/-- At a deterministic time, conditioning on any event determined by the first
`k + 1` coordinates leaves a future path with the conditioned law started at
the state at time `k`. The cast of the first coordinate to `ℕ` is valid -/
theorem conditionedVectorPathLaw_markov
    (x : ℕ) (y : ℤ) (k : ℕ) (A : Set (ℕ → ℤ × ℤ))
    (hA : MeasurableSet[conditionedVectorPast k] A)
    (B : Set (ℕ → ℤ × ℤ)) (hB : MeasurableSet B) :
    conditionedVectorPathLaw x y
      (A ∩ conditionedVectorShift k ⁻¹' B) =
    ∫⁻ p in A,
      conditionedVectorPathLaw ((p k).1.toNat) (p k).2 B
      ∂conditionedVectorPathLaw x y := by
  classical
  let ν := conditionedVectorPathLaw x y
  let P := conditionedVectorPrefix k
  let C : (Fin k → Fin 3) → Set (ℕ → ℤ × ℤ) := fun w =>
    {p | P p = lazyTwoDimensionalPrefix (x : ℤ) y w}
  let H : Set (ℕ → ℤ × ℤ) := conditionedVectorShift k ⁻¹' B
  let f : (ℕ → ℤ × ℤ) → ℝ≥0∞ := fun p =>
    conditionedVectorPathLaw ((p k).1.toNat) (p k).2 B
  obtain ⟨S, _, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hA
  change P ⁻¹' S = A at hpre
  let I : Finset (Fin k → Fin 3) := Finset.univ.filter
    (fun w => lazyTwoDimensionalPrefix (x : ℤ) y w ∈ S)
  let U : Set (ℕ → ℤ × ℤ) := ⋃ w ∈ I, C w
  have hC : ∀ w, MeasurableSet (C w) := by
    intro w
    exact (measurableSet_singleton _).preimage
      (measurable_conditionedVectorPrefix k)
  have hd : (I : Set (Fin k → Fin 3)).Pairwise (fun w v => Disjoint (C w) (C v)) := by
    intro w hw v hv hne
    apply Set.disjoint_left.mpr
    intro p hpw hpv
    apply hne
    apply lazyTwoDimensionalPrefix_injective (x : ℤ) y
    have hw' : P p = lazyTwoDimensionalPrefix (x : ℤ) y w := hpw
    have hv' : P p = lazyTwoDimensionalPrefix (x : ℤ) y v := hpv
    exact hw'.symm.trans hv'
  have hH : MeasurableSet H := hB.preimage (measurable_conditionedVectorShift k)
  have hf : Measurable f := by
    exact (measurable_of_countable
      (fun s : ℤ × ℤ => conditionedVectorPathLaw s.1.toNat s.2 B)).comp
      (measurable_pi_apply k)
  have hconst (w : Fin k → Fin 3) (p : ℕ → ℤ × ℤ) (hp : p ∈ C w) :
      f p = conditionedVectorPathLaw
        ((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).1.toNat)
        (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).2 B := by
    have he : p k = lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k) := by
      change P p = lazyTwoDimensionalPrefix (x : ℤ) y w at hp
      have hh := congrFun hp (Fin.last k)
      simpa [P, conditionedVectorPrefix] using hh
    simp [f, he]
  have hpiece : ∀ w,
      ν (C w ∩ H) = ν (C w) *
        conditionedVectorPathLaw
          ((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).1.toNat)
          (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).2 B := by
    intro w
    by_cases hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix (x : ℤ) y w j).1
    · have hfuture := conditionedVectorCylinder_future_law x y ν
        (conditionedVectorPathLaw_map_prefix x y) k w hw B hB
      change ν ({p | (fun j : Fin (k + 1) => p j.val) =
        lazyTwoDimensionalPrefix (x : ℤ) y w} ∩
          (fun p j => p (k + j)) ⁻¹' B) =
        ν {p | (fun j : Fin (k + 1) => p j.val) =
          lazyTwoDimensionalPrefix (x : ℤ) y w} *
          conditionedVectorPathLaw
            ((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).1.toNat)
            (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).2 B
      exact hfuture
    · have hzero : ν (C w) = 0 := by
        have hAtom := conditionedSource_prefix_atom x y ν
          (conditionedVectorPathLaw_map_prefix x y) k w
        change ν (C w) = _ at hAtom
        rw [hAtom]
        simp [hw]
      have hzero' : ν (C w ∩ H) = 0 :=
        measure_mono_null Set.inter_subset_left hzero
      rw [hzero', hzero]
      simp
  have hcover : A =ᵐ[ν] U := by
    filter_upwards [conditionedSource_ae_prefix_mem_range x y ν
      (conditionedVectorPathLaw_map_prefix x y) k] with p hp
    change P p ∈ Set.range (@lazyTwoDimensionalPrefix k (x : ℤ) y) at hp
    obtain ⟨w, hw⟩ := hp
    apply propext
    constructor
    · intro hpA
      have hpS : P p ∈ S := by
        have : p ∈ P ⁻¹' S := by rwa [hpre]
        exact this
      have hwS : lazyTwoDimensionalPrefix (x : ℤ) y w ∈ S := by
        rw [hw]
        exact hpS
      have hwI : w ∈ I :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwS⟩
      have hpC : p ∈ C w := by
        change P p = lazyTwoDimensionalPrefix (x : ℤ) y w
        exact hw.symm
      exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hwI, hpC⟩⟩
    · intro hpU
      simp only [U, Set.mem_iUnion] at hpU
      obtain ⟨w, hwI, hpC⟩ := hpU
      have hwS : lazyTwoDimensionalPrefix (x : ℤ) y w ∈ S :=
        (Finset.mem_filter.mp hwI).2
      have hpS : P p ∈ S := by
        change P p = lazyTwoDimensionalPrefix (x : ℤ) y w at hpC
        rw [hpC]
        exact hwS
      have : p ∈ P ⁻¹' S := hpS
      rwa [hpre] at this
  have hcoverH : (A ∩ H) =ᵐ[ν] (U ∩ H) := by
    filter_upwards [hcover] with p hp
    exact propext (and_congr (Iff.of_eq hp) Iff.rfl)
  have hset : U ∩ H = ⋃ w ∈ I, C w ∩ H := by
    ext p
    simp only [U, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨w, hwI, hpw⟩, hpH⟩
      exact ⟨w, hwI, hpw, hpH⟩
    · rintro ⟨w, hwI, hpw, hpH⟩
      exact ⟨⟨w, hwI, hpw⟩, hpH⟩
  have hdh : (I : Set (Fin k → Fin 3)).Pairwise
      (fun w v => Disjoint (C w ∩ H) (C v ∩ H)) := by
    intro w hw v hv hne
    exact (hd hw hv hne).mono Set.inter_subset_left Set.inter_subset_left
  have hleft : ν (A ∩ H) = ∑ w ∈ I,
      ν (C w ∩ H) := by
    rw [measure_congr hcoverH, hset,
      measure_biUnion_finset hdh (fun w hw => (hC w).inter hH)]
  have hright : ∫⁻ p in A, f p ∂ν = ∑ w ∈ I,
      ν (C w) * conditionedVectorPathLaw
        ((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).1.toNat)
        (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).2 B := by
    rw [setLIntegral_congr hcover,
      lintegral_biUnion_finset hd (fun w hw => hC w) f]
    refine Finset.sum_congr rfl fun w hw => ?_
    calc
      ∫⁻ p in C w, f p ∂ν = ∫⁻ p in C w,
          conditionedVectorPathLaw
            ((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).1.toNat)
            (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).2 B ∂ν := by
        exact setLIntegral_congr_fun (hC w) fun p hp => hconst w p hp
      _ = ν (C w) * conditionedVectorPathLaw
            ((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).1.toNat)
            (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).2 B := by
        rw [setLIntegral_const, mul_comm]
  calc
    ν (A ∩ conditionedVectorShift k ⁻¹' B) =
        ∑ w ∈ I, ν (C w ∩ H) := hleft
    _ = ∑ w ∈ I,
          ν (C w) * conditionedVectorPathLaw
            ((lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).1.toNat)
            (lazyTwoDimensionalPrefix (x : ℤ) y w (Fin.last k)).2 B := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hpiece w
    _ = ∫⁻ p in A, f p ∂ν := hright.symm

/-- Strong Markov property on the event that a stopping time is finite. The
stopped-past measurability hypothesis records the full information available -/
theorem conditionedVectorPathLaw_strongMarkov
    (x : ℕ) (y : ℤ) (τ : (ℕ → ℤ × ℤ) → ℕ∞)
    (_hτ : ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k] {p | τ p = (k : ℕ∞)})
    (A : Set (ℕ → ℤ × ℤ))
    (hA : ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k] (A ∩ {p | τ p = (k : ℕ∞)}))
    (B : Set (ℕ → ℤ × ℤ)) (hB : MeasurableSet B) :
    conditionedVectorPathLaw x y
      (A ∩ {p | τ p < ⊤} ∩
        {p | conditionedVectorShift (τ p).toNat p ∈ B}) =
    ∫⁻ p in A ∩ {p | τ p < ⊤},
      conditionedVectorPathLaw
        ((p ((τ p).toNat)).1.toNat) (p ((τ p).toNat)).2 B
      ∂conditionedVectorPathLaw x y := by
  classical
  let ν := conditionedVectorPathLaw x y
  let Aₖ : ℕ → Set (ℕ → ℤ × ℤ) := fun k => A ∩ {p | τ p = (k : ℕ∞)}
  let Eₖ : ℕ → Set (ℕ → ℤ × ℤ) := fun k =>
    Aₖ k ∩ conditionedVectorShift k ⁻¹' B
  let R : Set (ℕ → ℤ × ℤ) := A ∩ {p | τ p < ⊤}
  let G : Set (ℕ → ℤ × ℤ) :=
    A ∩ {p | τ p < ⊤} ∩ {p | conditionedVectorShift (τ p).toNat p ∈ B}
  let g : (ℕ → ℤ × ℤ) → ℝ≥0∞ := fun p =>
    conditionedVectorPathLaw
      ((p ((τ p).toNat)).1.toNat) (p ((τ p).toNat)).2 B
  have hAₖ_meas : ∀ k, MeasurableSet (Aₖ k) := by
    intro k
    obtain ⟨S, hS, hpre⟩ :=
      MeasurableSpace.measurableSet_comap.mp (hA k)
    change MeasurableSet (A ∩ {p | τ p = (k : ℕ∞)})
    rw [← hpre]
    exact hS.preimage (measurable_conditionedVectorPrefix k)
  have hAₖ_disjoint : ∀ {i j : ℕ}, i ≠ j → Disjoint (Aₖ i) (Aₖ j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    apply hij
    have hiτ : τ p = (i : ℕ∞) := hpi.2
    have hjτ : τ p = (j : ℕ∞) := hpj.2
    exact_mod_cast hiτ.symm.trans hjτ
  have hEₖ_meas : ∀ k, MeasurableSet (Eₖ k) := by
    intro k
    exact (hAₖ_meas k).inter (hB.preimage (measurable_conditionedVectorShift k))
  have hEₖ_disjoint : ∀ {i j : ℕ}, i ≠ j → Disjoint (Eₖ i) (Eₖ j) := by
    intro i j hij
    exact (hAₖ_disjoint hij).mono Set.inter_subset_left Set.inter_subset_left
  have hR : R = ⋃ k, Aₖ k := by
    ext p
    simp only [R, Aₖ, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hpA, hlt⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
      exact ⟨k, hpA, hk.symm⟩
    · rintro ⟨k, hpA, hk⟩
      exact ⟨hpA, by rw [hk]; exact ENat.coe_lt_top k⟩
  have hG : G = ⋃ k, Eₖ k := by
    ext p
    simp only [G, Eₖ, Aₖ, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨⟨hpA, hlt⟩, hfuture⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
      have hτp : τ p = (k : ℕ∞) := hk.symm
      have hto : (τ p).toNat = k := by simp [hτp]
      refine ⟨k, ⟨hpA, hτp⟩, ?_⟩
      simpa [conditionedVectorShift, hto] using hfuture
    · rintro ⟨k, ⟨hpA, hτp⟩, hfuture⟩
      have hlt : τ p < ⊤ := by rw [hτp]; exact ENat.coe_lt_top k
      have hto : (τ p).toNat = k := by simp [hτp]
      refine ⟨⟨hpA, hlt⟩, ?_⟩
      simpa [conditionedVectorShift, hto] using hfuture
  have hright : ∫⁻ p in R, g p ∂ν =
      ∑' k, ∫⁻ p in Aₖ k,
        conditionedVectorPathLaw ((p k).1.toNat) (p k).2 B ∂ν := by
    rw [hR, lintegral_iUnion hAₖ_meas (fun i j hij => hAₖ_disjoint hij) g]
    apply tsum_congr
    intro k
    exact setLIntegral_congr_fun (hAₖ_meas k) fun p hp => by
      have hτp : τ p = (k : ℕ∞) := hp.2
      simp [g, hτp]
  calc
    ν G = ∑' k, ν (Eₖ k) := by
      rw [hG, measure_iUnion (fun i j hij => hEₖ_disjoint hij) hEₖ_meas]
    _ = ∑' k, ∫⁻ p in Aₖ k,
          conditionedVectorPathLaw ((p k).1.toNat) (p k).2 B ∂ν := by
      apply tsum_congr
      intro k
      have hfixed := conditionedVectorPathLaw_markov x y k (Aₖ k) (hA k) B hB
      calc
        ν (Eₖ k) = ∫⁻ p in Aₖ k,
            conditionedVectorPathLaw ((p k).1.toNat) (p k).2 B ∂ν := by
          exact hfixed
        _ = ∫⁻ p in Aₖ k,
            conditionedVectorPathLaw ((p k).1.toNat) (p k).2 B ∂ν := rfl
    _ = ∫⁻ p in R, g p ∂ν := hright.symm

/-- The first time the second coordinate reaches `-r`, with value `⊤` if it
never does. -/
@[expose] noncomputable def conditionedSecondCoordinateFirstHit (r : ℕ)
    (p : ℕ → ℤ × ℤ) : ℕ∞ := by
  classical
  exact if h : ∃ n, (p n).2 = -(r : ℤ) then ((Nat.find h : ℕ) : ℕ∞) else ⊤

/-- Each level set of the first hit of `-r` is determined by the prefix through -/
theorem measurableSet_conditionedVectorPast_firstHit_eq (r k : ℕ) :
    MeasurableSet[conditionedVectorPast k]
      {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} := by
  classical
  let S : Set (Fin (k + 1) → ℤ × ℤ) := {q |
    (q (Fin.last k)).2 = -(r : ℤ) ∧
      ∀ (j : ℕ) (hj : j < k), (q ⟨j, by omega⟩).2 ≠ -(r : ℤ)}
  have hS : MeasurableSet S := (Set.to_countable S).measurableSet
  refine ⟨S, hS, ?_⟩
  ext p
  change (conditionedVectorPrefix k p ∈ S) ↔
    conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)
  have hprefix (p : ℕ → ℤ × ℤ) :
      conditionedVectorPrefix k p ∈ S ↔
        (p k).2 = -(r : ℤ) ∧ ∀ j < k, (p j).2 ≠ -(r : ℤ) := by
    simp [S, conditionedVectorPrefix]
  have hhit (p : ℕ → ℤ × ℤ) :
      conditionedSecondCoordinateFirstHit r p = (k : ℕ∞) ↔
        (p k).2 = -(r : ℤ) ∧ ∀ j < k, (p j).2 ≠ -(r : ℤ) := by
    unfold conditionedSecondCoordinateFirstHit
    by_cases h : ∃ n, (p n).2 = -(r : ℤ)
    · rw [dif_pos h, Nat.cast_inj, Nat.find_eq_iff]
    · rw [dif_neg h]
      constructor
      · intro he
        exact absurd he (ENat.top_ne_natCast k)
      · rintro ⟨hk, _⟩
        exact absurd ⟨k, hk⟩ h
  constructor
  · intro hp
    exact (hhit p).2 ((hprefix p).1 hp)
  · intro ht
    exact (hprefix p).2 ((hhit p).1 ht)

/-- Strong Markov property at the first hit of second-coordinate level `-r`, -/
theorem conditionedVectorPathLaw_firstHit_strongMarkov
    (x : ℕ) (y : ℤ) (r : ℕ) (B : Set (ℕ → ℤ × ℤ)) (hB : MeasurableSet B) :
    conditionedVectorPathLaw x y
      {p | conditionedSecondCoordinateFirstHit r p < ⊤ ∧
        conditionedVectorShift
          (conditionedSecondCoordinateFirstHit r p).toNat p ∈ B} =
    ∫⁻ p in {p | conditionedSecondCoordinateFirstHit r p < ⊤},
      conditionedVectorPathLaw
        ((p ((conditionedSecondCoordinateFirstHit r p).toNat)).1.toNat)
        (p ((conditionedSecondCoordinateFirstHit r p).toNat)).2 B
      ∂conditionedVectorPathLaw x y := by
  have hτ : ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k]
        {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)} :=
    fun k => measurableSet_conditionedVectorPast_firstHit_eq r k
  have hA : ∀ k : ℕ,
      MeasurableSet[conditionedVectorPast k]
        (Set.univ ∩ {p | conditionedSecondCoordinateFirstHit r p = (k : ℕ∞)}) := by
    intro k
    simpa using hτ k
  have hstrong := conditionedVectorPathLaw_strongMarkov x y
    (conditionedSecondCoordinateFirstHit r) hτ Set.univ hA B hB
  have hset :
      (Set.univ ∩ {p | conditionedSecondCoordinateFirstHit r p < ⊤}) ∩
        {p | conditionedVectorShift
          (conditionedSecondCoordinateFirstHit r p).toNat p ∈ B} =
      {p | conditionedSecondCoordinateFirstHit r p < ⊤ ∧
        conditionedVectorShift
          (conditionedSecondCoordinateFirstHit r p).toNat p ∈ B} := by
    ext p
    simp
  rw [hset, Set.univ_inter] at hstrong
  exact hstrong

end DirectedDistances.RandomWalk
