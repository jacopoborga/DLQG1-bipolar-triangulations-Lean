module

public import DirectedDistances.RandomWalk.IIDVectorWalk
public import DirectedDistances.RandomWalk.SecondCoordinateUnbounded
import Mathlib.MeasureTheory.Constructions.Projective

/-! # Shift invariance and the strong Markov property of the iid code walk

Helpers for the uses of the strong Markov property of the iid walk at first-hit times in
`lem-directed-contain`, `lem-geo-infty-ind`, `lem-uihbot-future`, `lem-quadrant-walk` and -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- The code sequence seen from time `k`, keeping the dummy time-zero code; used for the strong
Markov property at first-hit times in `lem-directed-contain`, `lem-geo-infty-ind`,
`lem-uihbot-future`, `lem-quadrant-walk`, `lem-disk-walk-conv` -/
@[expose] def codeShift (k : ℕ) (ω : ℕ → Fin 3) : ℕ → Fin 3 :=
  fun i => if i = 0 then 0 else ω (k + i)

 
theorem measurable_codeShift (k : ℕ) : Measurable (codeShift k) := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold codeShift
  by_cases h : i = 0
  · simp only [h, ite_true]; exact measurable_const
  · simp only [h, ite_false]; exact measurable_pi_apply _

/-- The shifted walk is the increment of the walk (`lem-quadrant-walk`, -/
theorem codeWalk_codeShift (k : ℕ) (ω : ℕ → Fin 3) (n : ℕ) :
    codeWalk (codeShift k ω) n = codeWalk ω (k + n) - codeWalk ω k := by
  induction n with
  | zero => simp [codeWalk_zero]
  | succ n ih =>
    have h1 := codeWalk_succ_sub (codeShift k ω) n
    have h2 := codeWalk_succ_sub ω (k + n)
    have h3 : codeShift k ω (n + 1) = ω (k + n + 1) := by
      simp [codeShift, add_assoc]
    rw [h3] at h1
    rw [show k + (n + 1) = k + n + 1 by omega]
    have : codeWalk (codeShift k ω) (n + 1) = codeWalk (codeShift k ω) n +
        lazyTwoDimensionalStep (ω (k + n + 1)) := by rw [← h1]; abel
    rw [this, ih]
    have : codeWalk ω (k + n + 1) = codeWalk ω (k + n) + lazyTwoDimensionalStep (ω (k + n + 1)) := by
      rw [← h2]; abel
    rw [this]; abel

private theorem lazyStep_injective : Function.Injective lazyTwoDimensionalStep := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [lazyTwoDimensionalStep]

private theorem iIndepFun_coordinates :
    iIndepFun (fun i (ω : ℕ → Fin 3) => ω (i + 1)) iidCodeMeasure := by
  let g : ℤ × ℤ → Fin 3 := fun p => if p.1 = -1 then 0 else if p.1 = 0 then 1 else 2
  have hg : ∀ c : Fin 3, g (lazyTwoDimensionalStep c) = c := by
    intro c; fin_cases c <;> simp [g, lazyTwoDimensionalStep]
  have hgm : Measurable g := measurable_of_countable g
  have := iIndepFun_codeWalk_increments.comp (fun _ : ℕ => g) (fun _ => hgm)
  convert this using 2
  ext ω
  simp only [Function.comp_apply, codeWalk_succ_sub, hg]

private noncomputable def coordLaw (c : Fin 3) : ENNReal :=
  Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ))
    {lazyTwoDimensionalStep c}

private theorem coord_law (i : ℕ) (c : Fin 3) :
    iidCodeMeasure {ω | ω (i + 1) = c} = coordLaw c := by
  have hm : Measurable (fun ω : ℕ → Fin 3 => codeWalk ω (i + 1) - codeWalk ω i) := by
    simp only [codeWalk_succ_sub]
    exact (measurable_of_countable lazyTwoDimensionalStep).comp (measurable_pi_apply (i + 1))
  have hset : {ω : ℕ → Fin 3 | ω (i + 1) = c} =
      (fun ω => codeWalk ω (i + 1) - codeWalk ω i) ⁻¹' {lazyTwoDimensionalStep c} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, codeWalk_succ_sub]
    exact ⟨fun h => by rw [h], fun h => lazyStep_injective h⟩
  rw [hset, ← Measure.map_apply hm (measurableSet_singleton _), map_codeWalk_increment i]
  rfl

private theorem measure_shift_cylinder (k : ℕ) (J : Finset ℕ) (hJ : ∀ i ∈ J, i ≠ 0)
    (q : ℕ → Fin 3) :
    iidCodeMeasure {ω | ∀ i ∈ J, ω (k + i) = q i} = ∏ i ∈ J, coordLaw (q i) := by
  classical
  let J' := J.image (fun i => k + i - 1)
  have hinj : Set.InjOn (fun i => k + i - 1) (J : Set ℕ) := by
    intro a ha b hb h
    have := hJ a ha; have := hJ b hb
    simp only at h
    omega
  have h := iIndepFun_coordinates.measure_inter_preimage_eq_mul J'
    (sets := fun j => {c : Fin 3 | c = q (j + 1 + 0 - k)}) (fun _ _ => (Set.toFinite _).measurableSet)
  have hset : {ω : ℕ → Fin 3 | ∀ i ∈ J, ω (k + i) = q i} =
      ⋂ j ∈ J', (fun ω : ℕ → Fin 3 => ω (j + 1)) ⁻¹' {c : Fin 3 | c = q (j + 1 + 0 - k)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, J', Finset.mem_image]
    constructor
    · rintro hω j ⟨i, hi, rfl⟩
      have := hJ i hi
      have e1 : k + i - 1 + 1 = k + i := by omega
      have e2 : k + i - k = i := by omega
      rw [e1, e2]; exact hω i hi
    · intro hω i hi
      have := hJ i hi
      have e1 : k + i - 1 + 1 = k + i := by omega
      have e2 : k + i - k = i := by omega
      have := hω (k + i - 1) ⟨i, hi, rfl⟩
      rwa [e1, e2] at this
  rw [hset, h, Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun i hi => ?_
  have := hJ i hi
  have e2 : k + i - 1 + 1 + 0 - k = i := by omega
  show iidCodeMeasure {ω : ℕ → Fin 3 | ω (k + i - 1 + 1) = q (k + i - 1 + 1 + 0 - k)} = _
  rw [coord_law, e2]

private theorem measure_codeShift_cylinder (k : ℕ) (I : Finset ℕ) (q : ℕ → Fin 3) :
    iidCodeMeasure {ω | ∀ i ∈ I, codeShift k ω i = q i} =
      if 0 ∈ I ∧ q 0 ≠ 0 then 0 else ∏ i ∈ I.erase 0, coordLaw (q i) := by
  classical
  split_ifs with h
  · have : {ω : ℕ → Fin 3 | ∀ i ∈ I, codeShift k ω i = q i} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨0, h.1, by simpa [codeShift] using Ne.symm h.2⟩
    rw [this]; simp
  · rw [← measure_shift_cylinder k (I.erase 0) (fun i hi => (Finset.mem_erase.mp hi).1) q]
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, Finset.mem_erase]
    constructor
    · intro hω i ⟨hi0, hi⟩
      have := hω i hi
      simpa [codeShift, hi0] using this
    · intro hω i hi
      by_cases hi0 : i = 0
      · subst hi0
        have : q 0 = 0 := by_contra fun hne => h ⟨hi, hne⟩
        simp [codeShift, this]
      · simpa [codeShift, hi0] using hω i ⟨hi0, hi⟩

/-- The shift preserves the iid code law
(`lem-directed-contain`, `lem-geo-infty-ind`, `lem-uihbot-future`, `lem-quadrant-walk`, -/
theorem map_codeShift (k : ℕ) : iidCodeMeasure.map (codeShift k) = iidCodeMeasure := by
  classical
  have key : ∀ k : ℕ, IsProjectiveLimit (iidCodeMeasure.map (codeShift k))
      (fun I : Finset ℕ => (iidCodeMeasure.map (codeShift 0)).map I.restrict) := by
    intro k I
    apply Measure.ext_of_singleton
    intro q
    let q' : ℕ → Fin 3 := fun i => if h : i ∈ I then q ⟨i, h⟩ else 0
    have hq : ∀ k : ℕ, ((iidCodeMeasure.map (codeShift k)).map I.restrict) {q} =
        if 0 ∈ I ∧ q' 0 ≠ 0 then 0 else ∏ i ∈ I.erase 0, coordLaw (q' i) := by
      intro k
      have hr : Measurable (Finset.restrict (π := fun _ : ℕ => Fin 3) I) := by fun_prop
      rw [Measure.map_apply hr (measurableSet_singleton _),
        Measure.map_apply (measurable_codeShift k) (hr (measurableSet_singleton _)),
        ← measure_codeShift_cylinder]
      congr 1
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      constructor
      · intro h i hi
        have := congrFun h ⟨i, hi⟩
        simpa [Finset.restrict, q', hi] using this
      · intro h
        funext ⟨i, hi⟩
        simpa [Finset.restrict, q', hi] using h i hi
    rw [hq k, hq 0]
  have h0 : iidCodeMeasure.map (codeShift 0) = iidCodeMeasure := by
    have hae : codeShift 0 =ᵐ[iidCodeMeasure] id := by
      filter_upwards [DirectedDistances.Probability.markovTrajectory_ae_start
        (Kernel.const (Fin 3) uniformCodeMeasure) (0 : Fin 3)] with ω hω
      funext i
      by_cases hi : i = 0
      · subst hi; simpa [codeShift] using hω.symm
      · simp [codeShift, hi]
    rw [Measure.map_congr hae, Measure.map_id]
  rw [(key k).unique (key 0), h0]

/-- Linear-sequence quotient of the codes seen up to time `k`: the σ-algebra of the first `k`
iid codes, i.e. the past at time `k` (`lem-directed-contain`, `lem-geo-infty-ind`,
`lem-uihbot-future`, `lem-quadrant-walk`, `lem-disk-walk-conv`, -/
@[expose] def codePast (k : ℕ) : MeasurableSpace (ℕ → Fin 3) :=
  MeasurableSpace.comap (fun (ω : ℕ → Fin 3) (j : Fin k) => ω (j.val + 1)) inferInstance

/-- The past at time `k` is a sub-σ-algebra of the product σ-algebra -/
theorem codePast_le (k : ℕ) : codePast k ≤ (inferInstance : MeasurableSpace (ℕ → Fin 3)) :=
  Measurable.comap_le (Measurable.of_eval fun j => measurable_pi_apply (j.val + 1))

/-- The shifted codes are independent of the past at time `k`
(`lem-directed-contain`, `lem-geo-infty-ind`, `lem-uihbot-future`, `lem-quadrant-walk`, -/
theorem iidCodeMeasure_inter_codeShift_preimage (k : ℕ) {A : Set (ℕ → Fin 3)}
    (hA : MeasurableSet[codePast k] A) {B : Set (ℕ → Fin 3)} (hB : MeasurableSet B) :
    iidCodeMeasure (A ∩ codeShift k ⁻¹' B) = iidCodeMeasure A * iidCodeMeasure B := by
  let m : ℕ → MeasurableSpace (ℕ → Fin 3) := fun i =>
    MeasurableSpace.comap (fun ω : ℕ → Fin 3 => ω (i + 1)) inferInstance
  have hind : iIndep m iidCodeMeasure := iIndepFun_coordinates
  have hle : ∀ i, m i ≤ (inferInstance : MeasurableSpace (ℕ → Fin 3)) :=
    fun i => (measurable_pi_apply (i + 1)).comap_le
  have hI := indep_iSup_of_disjoint hle hind
    (S := {i : ℕ | i < k}) (T := {i : ℕ | k ≤ i})
    (Set.disjoint_left.mpr fun i hi hj =>
      absurd (lt_of_lt_of_le (show i < k from hi) (show k ≤ i from hj)) (lt_irrefl _))
  have hpast : codePast k ≤ ⨆ i ∈ {i : ℕ | i < k}, m i := by
    unfold codePast
    change MeasurableSpace.comap _ MeasurableSpace.pi ≤ _
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun j => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂ (f := fun i (_ : i ∈ {i : ℕ | i < k}) => m i) j.val j.isLt
  have hfut : MeasurableSpace.comap (codeShift k) inferInstance ≤ ⨆ i ∈ {i : ℕ | k ≤ i}, m i := by
    change MeasurableSpace.comap _ MeasurableSpace.pi ≤ _
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun j => ?_
    rw [MeasurableSpace.comap_comp]
    by_cases hj : j = 0
    · have : (fun b : ℕ → Fin 3 => b j) ∘ codeShift k = fun _ => 0 := by
        funext ω; simp [codeShift, hj]
      rw [this, MeasurableSpace.comap_const]
      exact bot_le
    · have : (fun b : ℕ → Fin 3 => b j) ∘ codeShift k =
          fun ω => ω (k + j - 1 + 1) := by
        funext ω
        have : k + j - 1 + 1 = k + j := by omega
        simp [codeShift, hj, this]
      rw [this]
      exact le_iSup₂ (f := fun i (_ : i ∈ {i : ℕ | k ≤ i}) => m i) (k + j - 1) (by
        show k ≤ k + j - 1
        omega)
  have hI' := indep_of_indep_of_le hI hpast hfut
  have := (Indep_iff _ _ _).mp hI' A (codeShift k ⁻¹' B) hA ⟨B, hB, rfl⟩
  rw [this, ← Measure.map_apply (measurable_codeShift k) hB, map_codeShift]

private theorem codePast_measurableSet {k : ℕ} {A : Set (ℕ → Fin 3)}
    (hA : MeasurableSet[codePast k] A) : MeasurableSet A :=
  codePast_le k _ hA

/-- Strong Markov property of the iid code walk at a stopping time `tau` of the past filtration
(`lem-directed-contain`, `lem-geo-infty-ind`, `lem-uihbot-future`, `lem-quadrant-walk`, -/
theorem iidCodeMeasure_strongMarkov (tau : (ℕ → Fin 3) → ℕ∞)
    (_htau : ∀ k : ℕ, MeasurableSet[codePast k] {ω | tau ω = k})
    {A : Set (ℕ → Fin 3)}
    (hA : ∀ k : ℕ, MeasurableSet[codePast k] (A ∩ {ω | tau ω = k}))
    {B : Set (ℕ → Fin 3)} (hB : MeasurableSet B) :
    iidCodeMeasure (A ∩ {ω | tau ω < ⊤} ∩ {ω | codeShift (tau ω).toNat ω ∈ B}) =
      iidCodeMeasure (A ∩ {ω | tau ω < ⊤}) * iidCodeMeasure B := by
  have hdisj : ∀ {i j : ℕ}, i ≠ j →
      Disjoint (A ∩ {ω | tau ω = i}) (A ∩ {ω | tau ω = j}) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun ω hi hj => hij ?_
    have h1 : tau ω = i := hi.2
    have h2 : tau ω = j := hj.2
    exact Nat.cast_injective (h1.symm.trans h2)
  have hset1 : A ∩ {ω | tau ω < ⊤} = ⋃ k : ℕ, A ∩ {ω | tau ω = k} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hAω, hlt⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
      exact ⟨k, hAω, hk.symm⟩
    · rintro ⟨k, hAω, hk⟩
      exact ⟨hAω, by rw [hk]; exact ENat.coe_lt_top k⟩
  have hset2 : A ∩ {ω | tau ω < ⊤} ∩ {ω | codeShift (tau ω).toNat ω ∈ B} =
      ⋃ k : ℕ, (A ∩ {ω | tau ω = k}) ∩ codeShift k ⁻¹' B := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨⟨hAω, hlt⟩, hBω⟩
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
      refine ⟨k, ⟨hAω, hk.symm⟩, ?_⟩
      rw [← hk] at hBω
      simpa using hBω
    · rintro ⟨k, ⟨hAω, hk⟩, hBω⟩
      refine ⟨⟨hAω, by rw [hk]; exact ENat.coe_lt_top k⟩, ?_⟩
      rw [hk]
      simpa using hBω
  rw [hset2, hset1]
  rw [measure_iUnion (fun i j hij => ?_) (fun k => ?_), measure_iUnion (fun i j hij => hdisj hij)
    (fun k => codePast_measurableSet (hA k))]
  · rw [← ENNReal.tsum_mul_right]
    exact tsum_congr fun k => iidCodeMeasure_inter_codeShift_preimage k (hA k) hB
  · exact (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
  · exact (codePast_measurableSet (hA k)).inter ((measurable_codeShift k) hB)

private theorem codeWalk_snd_succ_ge (ω : ℕ → Fin 3) (n : ℕ) :
    (codeWalk ω n).2 - 1 ≤ (codeWalk ω (n + 1)).2 := by
  have h := congrArg Prod.snd (codeWalk_succ_sub ω n)
  rw [Prod.snd_sub] at h
  unfold lazyTwoDimensionalStep at h
  dsimp only at h
  split_ifs at h <;> omega

private theorem exists_codeWalk_snd_eq_of_le (ω : ℕ → Fin 3) {a : ℤ} (ha : a ≤ 0)
    (h : ∃ n, (codeWalk ω n).2 ≤ a) : ∃ n, (codeWalk ω n).2 = a := by
  classical
  let n0 := Nat.find h
  have h0 : (codeWalk ω n0).2 ≤ a := Nat.find_spec h
  refine ⟨n0, ?_⟩
  by_cases hn : n0 = 0
  · have : (codeWalk ω n0).2 = 0 := by rw [hn, codeWalk_zero]
    omega
  · obtain ⟨m, hm⟩ : ∃ m, n0 = m + 1 := ⟨n0 - 1, by omega⟩
    have h1 : ¬ (codeWalk ω m).2 ≤ a := Nat.find_min h (by omega)
    have h2 := codeWalk_snd_succ_ge ω m
    rw [hm] at h0 ⊢
    omega

/-- Finiteness of the first hit of a level `a ≤ 0` by the second coordinate of the code walk
(`lem-directed-contain`, `lem-geo-infty-ind`, `lem-uihbot-future`, `lem-quadrant-walk`, -/
theorem ae_exists_codeWalk_snd_eq {a : ℤ} (ha : a ≤ 0) :
    ∀ᵐ ω ∂iidCodeMeasure, ∃ n, (codeWalk ω n).2 = a := by
  filter_upwards [ae_codeWalk_snd_unbounded_below] with ω hω
  exact exists_codeWalk_snd_eq_of_le ω ha (hω a)

/-- First time the second coordinate of the code walk equals `a`, valued in `ℕ∞` (`⊤` if never)
(`lem-directed-contain`, `lem-geo-infty-ind`, `lem-uihbot-future`, `lem-quadrant-walk`, -/
@[expose] noncomputable def codeSndFirstHit (a : ℤ) (ω : ℕ → Fin 3) : ℕ∞ := by
  classical
  exact if h : ∃ n, (codeWalk ω n).2 = a then ((Nat.find h : ℕ) : ℕ∞) else ⊤

/-- The first hit time of a level is finite almost surely when `a ≤ 0` -/
theorem ae_codeSndFirstHit_lt_top {a : ℤ} (ha : a ≤ 0) :
    ∀ᵐ ω ∂iidCodeMeasure, codeSndFirstHit a ω < ⊤ := by
  filter_upwards [ae_exists_codeWalk_snd_eq ha] with ω hω
  classical
  unfold codeSndFirstHit
  rw [dif_pos hω]
  exact ENat.coe_lt_top _

/-- The first hit time of a level by the second coordinate is a stopping time for the past
filtration (`lem-directed-contain`, `lem-geo-infty-ind`, `lem-uihbot-future`, -/
theorem measurableSet_codePast_codeSndFirstHit_eq (a : ℤ) (k : ℕ) :
    MeasurableSet[codePast k] {ω | codeSndFirstHit a ω = k} := by
  classical
  let wk : (Fin k → Fin 3) → ℕ → ℤ × ℤ := fun x j =>
    ∑ i ∈ Finset.range j, if h : i < k then lazyTwoDimensionalStep (x ⟨i, h⟩) else 0
  have hwk : ∀ (ω : ℕ → Fin 3) (j : ℕ), j ≤ k →
      codeWalk ω j = wk (fun i : Fin k => ω (i.val + 1)) j := by
    intro ω j hj
    unfold codeWalk
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i < k := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
    simp [this]
  let S : Set (Fin k → Fin 3) := {x | (wk x k).2 = a ∧ ∀ j < k, (wk x j).2 ≠ a}
  have hS : MeasurableSet S := (Set.toFinite S).measurableSet
  refine ⟨S, hS, ?_⟩
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq, S]
  rw [← hwk ω k le_rfl]
  have hall : (∀ j < k, (wk (fun i : Fin k => ω (i.val + 1)) j).2 ≠ a) ↔
      ∀ j < k, (codeWalk ω j).2 ≠ a := by
    refine forall₂_congr fun j hj => ?_
    rw [hwk ω j hj.le]
  rw [hall]
  unfold codeSndFirstHit
  by_cases h : ∃ n, (codeWalk ω n).2 = a
  · rw [dif_pos h, Nat.cast_inj, Nat.find_eq_iff]
  · rw [dif_neg h]
    constructor
    · rintro ⟨hk, -⟩; exact absurd ⟨k, hk⟩ h
    · intro h'; exact absurd h' (ENat.top_ne_natCast k)

end DirectedDistances.RandomWalk
