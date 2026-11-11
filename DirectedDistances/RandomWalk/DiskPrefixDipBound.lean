module

public import DirectedDistances.RandomWalk.DiskPrefixDipNormalization
public import DirectedDistances.RandomWalk.DiskPrefixDipChunk
public import DirectedDistances.RandomWalk.Lemma518Cemetery
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Algebra.Order.Field

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/

/-! # Disk prefix-dip probability bounds

Helpers toward Proposition 5.16 (`prop-disk-bs-conv`, -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

private theorem measurableSet_bridgeCone (ell n : ℕ) :
    MeasurableSet (coneEvent (ell : ℤ) 0 n) := by
  simp only [coneEvent, Set.ofPred_and]
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
    have hj := (measurable_pi_apply j).comp measurable_codeWalk
    simp only [Set.ofPred_and]
    exact (measurableSet_le measurable_const (measurable_const.add hj.fst)).inter
      (measurableSet_le measurable_const (measurable_const.add hj.snd))
  · exact (measurable_const.add ((measurable_pi_apply n).comp measurable_codeWalk))
      (measurableSet_singleton (0, 0))

private theorem cond_prod_real_swap {Ω Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) (ν : Measure Γ) [SFinite μ] [SFinite ν]
    (E : Set Ω) (hE : MeasurableSet E)
    (S : Set (Ω × Γ)) (hS : MeasurableSet S) :
    ((cond μ E).prod ν).real S =
      (ν.prod μ).real {z | z.2 ∈ E ∧ (z.2, z.1) ∈ S} / μ.real E := by
  rw [ProbabilityTheory.cond, Measure.prod_smul_left, Measure.restrict_prod_eq_prod_univ,
    measureReal_ennreal_smul_apply, ENNReal.toReal_inv]
  rw [Measure.real, Measure.restrict_apply hS]
  have heq : S ∩ (E ×ˢ Set.univ) =
      Prod.swap ⁻¹' {z : Γ × Ω | z.2 ∈ E ∧ (z.2, z.1) ∈ S} := by
    ext z
    simp [Set.mem_prod, and_comm]
  have hm : (μ.prod ν) (Prod.swap ⁻¹' {z : Γ × Ω | z.2 ∈ E ∧ (z.2, z.1) ∈ S}) =
      (ν.prod μ) {z : Γ × Ω | z.2 ∈ E ∧ (z.2, z.1) ∈ S} := by
    have hs : MeasurableSet {z : Γ × Ω | z.2 ∈ E ∧ (z.2, z.1) ∈ S} :=
      (hE.preimage measurable_snd).inter (hS.preimage measurable_swap)
    rw [← Measure.prod_swap (μ := μ) (ν := ν), Measure.map_apply measurable_swap hs]
  rw [heq, hm]
  simp only [Measure.real, div_eq_mul_inv, mul_comm]

private theorem uniform_succ (ell : ℕ) :
    (Measure.uniformOfFinset (Finset.range ell)).map Nat.succ =
      Measure.uniformOfFinset (Finset.Icc 1 ell) := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  cases k with
  | zero =>
    have hz : (Finset.Icc 1 ell).filter (fun x => x = 0) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]
      omega
    simp [Measure.uniformOfFinset_apply, hz]
  | succ k =>
    have hp : Nat.succ ⁻¹' {k + 1} = {k} := by ext x; simp
    rw [hp]
    by_cases hk : k < ell
    · have hk' : k + 1 ≤ ell := by omega
      simp [Measure.uniformOfFinset_apply_singleton, hk, hk']
    · have hk' : ¬ k + 1 ≤ ell := by omega
      simp [Measure.uniformOfFinset_apply_singleton, hk, hk']

private theorem overflow_rhs_le_seven_div (m : ℕ) (hm : 1 ≤ m) :
    1 / ((m : ℝ) + 1) +
        (3 / 2 : ℝ) * ((m : ℝ) ^ 2 + 1) ^ 2 / (m : ℝ) ^ 100 ≤ 7 / (m : ℝ) := by
  have hx : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpow : (m : ℝ) ^ 5 ≤ (m : ℝ) ^ 100 := by
    gcongr
    norm_num
  have hsquare : ((m : ℝ) ^ 2 + 1) ^ 2 ≤ 4 * (m : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((m : ℝ) ^ 2 - 1)]
  have hfirst : 1 / ((m : ℝ) + 1) ≤ 1 / (m : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hsecond :
      (3 / 2 : ℝ) * ((m : ℝ) ^ 2 + 1) ^ 2 / (m : ℝ) ^ 100 ≤ 6 / (m : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (pow_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ)) 4)]
  calc
    1 / ((m : ℝ) + 1) +
        (3 / 2 : ℝ) * ((m : ℝ) ^ 2 + 1) ^ 2 / (m : ℝ) ^ 100 ≤
        1 / (m : ℝ) + 6 / (m : ℝ) := add_le_add hfirst hsecond
    _ = 7 / (m : ℝ) := by ring

private theorem target_deficit (m K0 : ℕ) (hm : 0 < m) :
    1 - ((iidCodeMeasure.map (chunk m (m ^ 100))).prod
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
        {p | p.1.2 = true ∧ K0 ≤ p.2.val} ≤
      iidCodeMeasure.real
        {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} + (K0 : ℝ) / m := by
  let μ := iidCodeMeasure.map (chunk m (m ^ 100))
  let U := Measure.uniformOfFinset (Finset.univ : Finset (Fin m))
  have : IsProbabilityMeasure U := by
    constructor
    simp only [U, Measure.uniformOfFinset_apply, Set.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    exact ENNReal.div_self (by exact_mod_cast hm.ne') (by finiteness)
  let G : Set (((Fin (m ^ 100) → Fin 3) × Bool) × Fin m) :=
    {p | p.1.2 = true ∧ K0 ≤ p.2.val}
  let bad : Set (Fin m) := {o | o.val < K0}
  have hG : MeasurableSet G := (Set.toFinite G).measurableSet
  have hsub : Gᶜ ⊆ ({x | x.2 ≠ true} ×ˢ Set.univ) ∪ (Set.univ ×ˢ bad) := by
    intro p hp
    by_cases hc : p.1.2 = true
    · right
      have ho : ¬ K0 ≤ p.2.val := fun ho => hp ⟨hc, ho⟩
      exact ⟨Set.mem_univ _, Nat.lt_of_not_ge ho⟩
    · exact Or.inl ⟨hc, Set.mem_univ _⟩
  have hbad : U.real bad ≤ (K0 : ℝ) / m := by
    change (Measure.uniformOfFinset _ bad).toReal ≤ _
    rw [Measure.uniformOfFinset_apply, ENNReal.toReal_div]
    simp only [ENNReal.toReal_natCast, Finset.card_univ, Fintype.card_fin]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hc : ((Finset.univ : Finset (Fin m)).filter (fun o => o.val < K0)).card ≤
        K0 := by
      have h := Finset.card_le_card_of_injOn
        (s := (Finset.univ : Finset (Fin m)).filter (fun o => o.val < K0))
        (t := Finset.range K0) (fun o => o.val)
        (by intro o ho; exact Finset.mem_range.mpr (Finset.mem_filter.mp ho).2)
        (by intro a _ b _ hab; exact Fin.ext hab)
      simpa using h
    convert (show (((Finset.univ : Finset (Fin m)).filter
        (fun o => o.val < K0)).card : ℝ) ≤ (K0 : ℝ) by exact_mod_cast hc) using 1
    congr 2
    ext o
    simp [bad]
  have hcap : μ.real {x | x.2 ≠ true} =
      iidCodeMeasure.real {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} := by
    rw [map_measureReal_apply (measurable_chunk _ _) (Set.toFinite _).measurableSet]
    congr 1
    ext ω
    simp [chunk, not_le]
  change 1 - (μ.prod U).real G ≤ _
  have hcomp := measureReal_compl (μ := μ.prod U) hG
  have htotal : (μ.prod U).real Set.univ = 1 := by
    have : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
    simp
  rw [htotal] at hcomp
  rw [← hcomp]
  calc
    (μ.prod U).real Gᶜ ≤ (μ.prod U).real
        (({x | x.2 ≠ true} ×ˢ Set.univ) ∪ (Set.univ ×ˢ bad)) := measureReal_mono hsub
    _ ≤ (μ.prod U).real ({x | x.2 ≠ true} ×ˢ Set.univ) +
        (μ.prod U).real (Set.univ ×ˢ bad) := measureReal_union_le _ _
    _ = μ.real {x | x.2 ≠ true} + U.real bad := by
      rw [measureReal_prod_prod, measureReal_prod_prod]
      have : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
      simp
    _ ≤ _ := by rw [hcap]; exact add_le_add le_rfl hbad





theorem diskPrefixDip_iid_bad_mass_le (m K0 : ℕ) (hm : 1 ≤ m) :
    ((iidCodeMeasure.map (chunk m (m ^ 100))).prod
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
        {p | p.1.2 = false ∨ p.2.val < K0} ≤ 7 / (m : ℝ) + (K0 : ℝ) / m := by
  have hmpos : 0 < m := by omega
  have : IsProbabilityMeasure
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin m))) := by
    constructor
    simp only [Measure.uniformOfFinset_apply, Set.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    exact ENNReal.div_self (by exact_mod_cast hmpos.ne') (by finiteness)
  let Q := (iidCodeMeasure.map (chunk m (m ^ 100))).prod
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))
  have hcomp : {p : ((Fin (m ^ 100) → Fin 3) × Bool) × Fin m |
      p.1.2 = false ∨ p.2.val < K0} = {p | p.1.2 = true ∧ K0 ≤ p.2.val}ᶜ := by
    ext p
    cases hb : p.1.2 <;> simp [hb]
  change Q.real _ ≤ _
  rw [hcomp, measureReal_compl (Set.toFinite _).measurableSet]
  have ht : Q.real Set.univ = 1 := by dsimp [Q]; simp
  rw [ht]
  have hcap := (iidCodeMeasure_real_fstHit_overflow_bound m hm).trans
    (overflow_rhs_le_seven_div m hm)
  exact (target_deficit m K0 hmpos).trans (by linarith only [hcap])





theorem diskPrefixDip_selection_bound (A : ℝ) (hA : 1 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m K0 ell n N : ℕ), K0 < m → m ≤ ell →
      m ^ 100 ≤ N → ∀ δ : ℝ, 0 < δ → 1 ≤ n →
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      (bridgeLevelLaw n ell).real
        {p | ∃ T : ℕ, codeFstFirstHit (-(p.2 : ℤ)) p.1 = T ∧
          ∃ j : ℕ, j + N < T ∧
            (codeWalk p.1 j).1 ≤ (codeWalk p.1 T).1 + (K0 : ℤ)} ≤
        iidCodeMeasure.real
          {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} +
        (K0 : ℝ) / m + δ +
        2 * Fintype.card ((Fin (m ^ 100) → Fin 3) × Bool) *
          Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c +
        (m : ℝ) / ell := by
  obtain ⟨c, hc, hJ⟩ := conditionedUniformLevelChunk_joint_corrected A hA
  refine ⟨c, hc, ?_⟩
  intro m K0 ell n N hmK0 hml hN δ hδ hn hlo hhi hln hcong
  have hm : 0 < m := by omega
  have hell : 0 < ell := hm.trans_le hml
  have : IsProbabilityMeasure (Measure.uniformOfFinset (Finset.Icc 1 ell)) := by
    constructor
    simp only [Measure.uniformOfFinset_apply, Set.mem_univ, Finset.filter_true,
      Nat.card_Icc, Nat.add_sub_cancel]
    exact ENNReal.div_self (by exact_mod_cast hell.ne') (by finiteness)
  let μ := cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)
  let U := Measure.uniformOfFinset (Finset.range ell)
  let P := bridgeLevelLaw n ell
  have : IsFiniteMeasure P := by dsimp [P, bridgeLevelLaw]; infer_instance
  let Q := (iidCodeMeasure.map (chunk m (m ^ 100))).prod
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))
  let G : Set (((Fin (m ^ 100) → Fin 3) × Bool) × Fin m) :=
    {p | p.1.2 = true ∧ K0 ≤ p.2.val}
  let H : Set ((ℕ → Fin 3) × ℕ) :=
    {p | 1 ≤ p.2 ∧ p.2 - 1 < m * (ell / m) ∧
      (cappedLevelChunk m (m ^ 100) ((p.2 - 1) / m) p.1).2 = true ∧
      K0 ≤ (p.2 - 1) % m}
  have hH : MeasurableSet H := by
    have hx : Measurable
        (fun p : (ℕ → Fin 3) × ℕ =>
          (cappedLevelChunk m (m ^ 100) ((p.2 - 1) / m) p.1).2) :=
      measurable_from_prod_countable_left fun k =>
        (measurable_cappedLevelChunk m (m ^ 100) ((k - 1) / m)).snd
    have hk : Measurable (fun p : (ℕ → Fin 3) × ℕ => p.2 - 1) :=
      measurable_snd.sub_const 1
    exact (measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_lt hk measurable_const).inter
        ((hx (measurableSet_singleton true)).inter
          (measurableSet_le measurable_const
            ((measurable_of_countable (fun k : ℕ => k % m)).comp hk))))
  have hP : P.real Set.univ ≤ 1 := by
    dsimp [P, bridgeLevelLaw]
    rw [← Set.univ_prod_univ, measureReal_prod_prod]
    have hu : (Measure.uniformOfFinset (Finset.Icc 1 ell)).real Set.univ = 1 := by
      simp
    rw [hu, mul_one]
    exact measureReal_le_one
  have hshift : P = (μ.prod U).map (Prod.map id Nat.succ) := by
    dsimp [P, bridgeLevelLaw, μ, U]
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_of_countable _),
      Measure.map_id, uniform_succ]
  have hmass : P.real H =
      (((Measure.uniformOfFinset (Finset.range ell)).prod iidCodeMeasure).real
        {z | z.2 ∈ coneEvent (ell : ℤ) 0 n ∧ z.1 < m * (ell / m) ∧
          (cappedLevelChunk m (m ^ 100) (z.1 / m) z.2,
            (⟨z.1 % m, Nat.mod_lt z.1 hm⟩ : Fin m)) ∈ G}) /
        iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n) := by
    rw [hshift, map_measureReal_apply (measurable_id.prodMap
      (measurable_of_countable _)) hH]
    rw [cond_prod_real_swap _ _ _ (measurableSet_bridgeCone ell n) _
      (hH.preimage (measurable_id.prodMap (measurable_of_countable _)))]
    congr 2
    ext z
    simp [H, G, Prod.map]
  have hcompare := hJ m (m ^ 100) ell n hm (Nat.div_pos hml hm)
    δ hδ hn hlo hhi hln hcong G
  rw [← hmass] at hcompare
  change |P.real H - Q.real G| ≤ _ at hcompare
  have hsub : {p : (ℕ → Fin 3) × ℕ |
      ∃ T : ℕ, codeFstFirstHit (-(p.2 : ℤ)) p.1 = T ∧
        ∃ j : ℕ, j + N < T ∧
          (codeWalk p.1 j).1 ≤ (codeWalk p.1 T).1 + (K0 : ℤ)} ⊆ Hᶜ := by
    intro p hp hgood
    obtain ⟨hK, _, hcomplete, ho⟩ := hgood
    obtain ⟨T, hT, hdip⟩ := hp
    have hrepr : p.2 = ((p.2 - 1) / m) * m + (p.2 - 1) % m + 1 := by
      have h := Nat.div_add_mod' (p.2 - 1) m
      omega
    exact completeLevelChunk_no_prefix_dip m p.2 K0 ((p.2 - 1) / m)
      ((p.2 - 1) % m) N T p.1 hmK0 ho (Nat.mod_lt _ hm)
      hrepr hN hcomplete hT hdip
  have hcomp := measureReal_add_measureReal_compl (μ := P) hH
  have hdef := target_deficit m K0 hm
  change 1 - Q.real G ≤ _ at hdef
  have hmono := measureReal_mono (μ := P) hsub
  have hlow := (abs_le.mp hcompare).1
  linarith only [hmono, hcomp, hP, hdef, hlow]

private theorem fixedParameters_eventually
    (A : ℝ) (hA : 1 < A) (m : ℕ) (hm : 0 < m)
    (δ c η : ℝ) (hδ : 0 < δ) (hc : 0 < c) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ ell : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      m ≤ ell ∧
      2 * Fintype.card ((Fin (m ^ 100) → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c ≤ η ∧
      (m : ℝ) / ell ≤ η := by
  have hA0 : 0 < A := lt_trans zero_lt_one hA
  let L : ℕ → ℕ := fun n => ⌈A⁻¹ * Real.sqrt (n : ℝ)⌉₊
  have hlim := conditionedSelectedChunk_bound_tendsto A hA m (m ^ 100) hm δ c hδ hc L
    (Filter.Eventually.of_forall fun n => Nat.le_ceil _)
  have hsqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlow : Filter.Tendsto (fun n : ℕ => A⁻¹ * Real.sqrt (n : ℝ))
      Filter.atTop Filter.atTop := hsqrt.const_mul_atTop (inv_pos.mpr hA0)
  have htail := hlow.const_div_atTop (m : ℝ)
  filter_upwards [hlim.eventually_le_const (show δ < δ + η by linarith),
    htail.eventually_le_const hη, hlow.eventually_ge_atTop (m : ℝ)] with n he ht hmlo
  intro ell hlo
  have hml : m ≤ ell := by exact_mod_cast hmlo.trans hlo
  have hlpos : 0 < A⁻¹ * Real.sqrt (n : ℝ) :=
    lt_of_lt_of_le (by exact_mod_cast hm) hmlo
  refine ⟨hml, ?_, (div_le_div_of_nonneg_left (by positivity) hlpos hlo).trans ht⟩
  have hL : L n ≤ ell := Nat.ceil_le.mpr hlo
  have hd : ((L n / m : ℕ) : ℝ) ≤ ((ell / m : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_le_div_right hL : L n / m ≤ ell / m)
  have hexp : Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) ≤
      Real.exp (-2 * δ ^ 2 * (L n / m : ℕ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hd (by nlinarith only [sq_nonneg δ])
  have he' : δ + 2 * Fintype.card ((Fin (m ^ 100) → Fin 3) × Bool) *
      Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c ≤ δ + η := by
    apply le_trans _ he
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ hc.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)
  linarith only [he']





theorem diskPrefixDip_bound (A : ℝ) (hA : 1 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m K0 ell n N : ℕ), K0 < m → m ≤ ell →
      m ^ 100 ≤ N → ∀ δ : ℝ, 0 < δ → 1 ≤ n →
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      (bridgeLevelLaw n ell).real
        {p | ∃ T : ℕ, codeFstFirstHit (-(p.2 : ℤ)) p.1 = T ∧
          ∃ j : ℕ, j + N < T ∧
            (codeWalk p.1 j).1 ≤ (codeWalk p.1 T).1 + (K0 : ℤ)} ≤
        7 / (m : ℝ) + (K0 : ℝ) / m + δ +
        2 * Fintype.card ((Fin (m ^ 100) → Fin 3) × Bool) *
          Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c +
        (m : ℝ) / ell := by
  obtain ⟨c, hc, hb⟩ := diskPrefixDip_selection_bound A hA
  refine ⟨c, hc, ?_⟩
  intro m K0 ell n N hmK0 hml hN δ hδ hn hlo hhi hln hcong
  have hm : 1 ≤ m := by omega
  have hov := (iidCodeMeasure_real_fstHit_overflow_bound m hm).trans
    (overflow_rhs_le_seven_div m hm)
  exact (hb m K0 ell n N hmK0 hml hN δ hδ hn hlo hhi hln hcong).trans
    (by linarith only [hov])





theorem diskPrefixDip_small (A : ℝ) (hA : 1 < A) (K0 : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ ell : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      (bridgeLevelLaw n ell).real
        {p | ∃ T : ℕ, codeFstFirstHit (-(p.2 : ℤ)) p.1 = T ∧
          ∃ j : ℕ, j + N < T ∧
            (codeWalk p.1 j).1 ≤ (codeWalk p.1 T).1 + (K0 : ℤ)} ≤ ε := by
  obtain ⟨c, hc, hbound⟩ := diskPrefixDip_bound A hA
  have hlim : Filter.Tendsto (fun m : ℕ => (7 + (K0 : ℝ)) / (m : ℝ))
      Filter.atTop (nhds 0) := tendsto_natCast_atTop_atTop.const_div_atTop _
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp
    (hlim.eventually_le_const (show 0 < ε / 3 by positivity))
  let m := max (K0 + 1) m₀
  have hmK0 : K0 < m := lt_of_lt_of_le (Nat.lt_succ_self K0) (le_max_left _ _)
  have hm : 0 < m := by omega
  have hoff : 7 / (m : ℝ) + (K0 : ℝ) / m ≤ ε / 3 := by
    have h := hm₀ m (le_max_right _ _)
    simpa only [add_div] using h
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp
    (fixedParameters_eventually A hA m hm (ε / 6) c (ε / 6)
      (by positivity) hc (by positivity))
  refine ⟨m ^ 100, ?_⟩
  intro N hN
  refine ⟨max 1 k, ?_⟩
  intro n hn ell hlo hhi hln hcong
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  obtain ⟨hml, he, ht⟩ := hk n ((le_max_right _ _).trans hn) ell hlo
  have hb := hbound m K0 ell n N hmK0 hml hN (ε / 6)
    (by positivity) hn1 hlo hhi hln hcong
  linarith only [hb, hoff, he, ht, hε]

end DirectedDistances.RandomWalk
