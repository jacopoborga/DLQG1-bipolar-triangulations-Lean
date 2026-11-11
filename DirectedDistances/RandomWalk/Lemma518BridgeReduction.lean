module

public import DirectedDistances.RandomWalk.BridgeEndpointWindow
public import DirectedDistances.RandomWalk.ConditionedSelectedChunk
public import DirectedDistances.RandomWalk.BridgeWindowContainment

/-! Supporting lemmas for paper labels `lem-disk-walk-conv` (see CORRESPONDENCE.md). -/

/-! # Convention-free finite bridge reduction

Helpers toward corrected `lem-disk-walk-conv`,
infinite-code window below is an auxiliary comparison observable, not a chosen
finite-bridge boundary convention. The cemetery form is in `Lemma518Cemetery`. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal




@[expose] noncomputable def bridgeRawWindow (N : ℕ)
    (p : (ℕ → Fin 3) × ℕ) : Fin (2 * N + 1) → ℤ × ℤ :=
  fun j => codeWalk p.1 ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + j.val - N) -
    codeWalk p.1 ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat)



private theorem measurable_bridgeRawWindow (N : ℕ) : Measurable (bridgeRawWindow N) := by
  have hh (K : ℕ) : Measurable (codeFstFirstHit (-(K : ℤ))) := by
    rw [ENat.measurable_iff]
    intro k
    exact codePast_le k _ (measurableSet_codePast_codeFstFirstHit_eq _ k)
  apply measurable_from_prod_countable_left
  intro K
  have ht : Measurable (fun ω => (codeFstFirstHit (-(K : ℤ)) ω).toNat) :=
    (measurable_of_countable ENat.toNat).comp (hh K)
  apply measurable_pi_iff.mpr
  intro j
  have hw : Measurable (fun z : ℕ × (ℕ → Fin 3) => codeWalk z.2 z.1) :=
    measurable_from_prod_countable_right fun t =>
      (measurable_pi_apply t).comp measurable_codeWalk
  exact (hw.comp (((ht.add_const j.val).sub_const N).prodMk measurable_id)).sub
    (hw.comp (ht.prodMk measurable_id))




private theorem ae_cond_bridgeRawWindow_decode (ell n N m : ℕ) :
    ∀ᵐ ω ∂(cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)), ∀ K : ℕ,
      (cappedLevelChunk m (m ^ 100) (K / m) ω).2 = true →
      N ≤ K % m → K % m + N ≤ m →
      bridgeRawWindow N (ω, K) =
        decodeWindow N m (m ^ 100)
          (cappedLevelChunk m (m ^ 100) (K / m) ω) (K % m) := by
  have h : ∀ᵐ ω ∂iidCodeMeasure, ∀ K : ℕ,
      (cappedLevelChunk m (m ^ 100) (K / m) ω).2 = true →
      N ≤ K % m → K % m + N ≤ m →
      bridgeRawWindow N (ω, K) =
        decodeWindow N m (m ^ 100)
          (cappedLevelChunk m (m ^ 100) (K / m) ω) (K % m) := by
    rw [ae_all_iff]
    intro K
    have h := ae_cappedLevelChunk_decodeWindow N m (K / m) (K % m)
    have heq : K / m * m + K % m = K := Nat.div_add_mod' K m
    filter_upwards [h] with ω hω
    intro hc hN hM
    change (fun j : Fin (2 * N + 1) => codeWalk ω
      ((codeFstFirstHit (-(K : ℤ)) ω).toNat + j.val - N) -
      codeWalk ω ((codeFstFirstHit (-(K : ℤ)) ω).toNat)) = _
    simpa only [heq] using hω hc hN hM
  exact cond_absolutelyContinuous.ae_le h

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



private noncomputable def bridgeSelectedRecord (m : ℕ) (hm : 0 < m)
    (p : (ℕ → Fin 3) × ℕ) : ((Fin (m ^ 100) → Fin 3) × Bool) × Fin m :=
  (cappedLevelChunk m (m ^ 100) (p.2 / m) p.1,
    ⟨p.2 % m, Nat.mod_lt p.2 hm⟩)

private theorem measurable_bridgeSelectedRecord (m : ℕ) (hm : 0 < m) :
    Measurable (bridgeSelectedRecord m hm) := by
  apply measurable_from_prod_countable_left
  intro K
  change Measurable (fun ω =>
    (cappedLevelChunk m (m ^ 100) (K / m) ω,
      (⟨K % m, Nat.mod_lt K hm⟩ : Fin m)))
  exact (measurable_cappedLevelChunk m (m ^ 100) (K / m)).prodMk measurable_const





private theorem bridgeSelectedRecord_setwise_corrected (A : ℝ) (hA : 1 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m ell n : ℕ), (hm : 0 < m) → m ≤ ell →
      ∀ δ : ℝ, 0 < δ → 1 ≤ n →
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      ∀ D : Set (((Fin (m ^ 100) → Fin 3) × Bool) × Fin m),
      |((cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod
          (Measure.uniformOfFinset (Finset.range ell))).real
          {p | p.2 < m * (ell / m) ∧ bridgeSelectedRecord m hm p ∈ D} -
        ((iidCodeMeasure.map (cappedLevelChunk m (m ^ 100) 0)).prod
          (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real D| ≤
      δ + 2 * Fintype.card ((Fin (m ^ 100) → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c +
        (m : ℝ) / ell := by
  obtain ⟨c, hc, hJ⟩ := conditionedUniformLevelChunk_joint_corrected A hA
  refine ⟨c, hc, ?_⟩
  intro m ell n hm hml δ hδ hn hlo hhi hln hcong D
  have hD : MeasurableSet D := (Set.toFinite D).measurableSet
  have hS : MeasurableSet
      {p : (ℕ → Fin 3) × ℕ |
        p.2 < m * (ell / m) ∧ bridgeSelectedRecord m hm p ∈ D} :=
    ((measurableSet_lt measurable_snd measurable_const)).inter
      (hD.preimage (measurable_bridgeSelectedRecord m hm))
  rw [cond_prod_real_swap _ _ _ (measurableSet_bridgeCone ell n) _ hS,
    map_cappedLevelChunk]
  exact hJ m (m ^ 100) ell n hm (Nat.div_pos hml hm) δ hδ hn hlo hhi hln hcong D

private theorem window_reduction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (hP : P.real Set.univ ≤ 1)
    (H S : Set Ω) (hH : MeasurableSet H) {t u e : ℝ}
    (hD : |P.real (H ∩ S) - t| ≤ e) (hG : |P.real H - u| ≤ e) :
    |P.real S - t| ≤ 2 * e + (1 - u) := by
  have hsub : P.real (H ∩ S) ≤ P.real S := measureReal_mono Set.inter_subset_right
  have hunion : P.real (S ∪ H) ≤ 1 :=
    (measureReal_mono (Set.subset_univ _)).trans hP
  have hid := measureReal_union_add_inter (μ := P) (s := S) hH
  rw [Set.inter_comm S H] at hid
  rw [abs_le] at hD hG ⊢
  constructor <;> linarith only [hD.1, hD.2, hG.1, hG.2, hsub, hunion, hid]






private theorem bridgeRawWindow_reduction_corrected (A : ℝ) (hA : 1 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m ell n : ℕ), (hm : 0 < m) → m ≤ ell →
      ∀ (N : ℕ) (δ : ℝ), 0 < δ → 1 ≤ n →
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      ∀ B : Set (Fin (2 * N + 1) → ℤ × ℤ), MeasurableSet B →
      let Q := (iidCodeMeasure.map (cappedLevelChunk m (m ^ 100) 0)).prod
        (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))
      |((cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod
          (Measure.uniformOfFinset (Finset.range ell))).real
            ((bridgeRawWindow N) ⁻¹' B) -
        Q.real {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m ∧
          decodeWindow N m (m ^ 100) p.1 p.2.val ∈ B}| ≤
        2 * (δ + 2 * Fintype.card ((Fin (m ^ 100) → Fin 3) × Bool) *
          Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c +
          (m : ℝ) / ell) +
        (1 - Q.real {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m}) := by
  obtain ⟨c, hc, hJ⟩ := bridgeSelectedRecord_setwise_corrected A hA
  refine ⟨c, hc, ?_⟩
  intro m ell n hm hml N δ hδ hn hlo hhi hln hcong B hB
  dsimp only
  let U := Measure.uniformOfFinset (Finset.range ell)
  have : IsProbabilityMeasure U := by
    constructor
    simp only [U, Measure.uniformOfFinset_apply, Set.mem_univ, Finset.filter_true,
      Finset.card_range]
    exact ENNReal.div_self (by exact_mod_cast (by omega : ell ≠ 0)) (by finiteness)
  let P := (cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod U
  have : IsFiniteMeasure P := by dsimp [P]; infer_instance
  let Q := (iidCodeMeasure.map (cappedLevelChunk m (m ^ 100) 0)).prod
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))
  let G : Set (((Fin (m ^ 100) → Fin 3) × Bool) × Fin m) :=
    {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m}
  let D : Set (((Fin (m ^ 100) → Fin 3) × Bool) × Fin m) :=
    {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m ∧
      decodeWindow N m (m ^ 100) p.1 p.2.val ∈ B}
  let H : Set ((ℕ → Fin 3) × ℕ) :=
    {p | p.2 < m * (ell / m) ∧ bridgeSelectedRecord m hm p ∈ G}
  let S := (bridgeRawWindow N) ⁻¹' B
  have hG : MeasurableSet G := (Set.toFinite G).measurableSet
  have hH : MeasurableSet H :=
    (measurableSet_lt measurable_snd measurable_const).inter
      (hG.preimage (measurable_bridgeSelectedRecord m hm))
  have hdec : ∀ᵐ p ∂P,
      bridgeSelectedRecord m hm p ∈ G →
      bridgeRawWindow N p = decodeWindow N m (m ^ 100)
        (bridgeSelectedRecord m hm p).1 (bridgeSelectedRecord m hm p).2.val := by
    have hh := (Measure.quasiMeasurePreserving_fst (μ := cond iidCodeMeasure
      (coneEvent (ell : ℤ) 0 n)) (ν := U)).ae
        (ae_cond_bridgeRawWindow_decode ell n N m)
    filter_upwards [hh] with p hp
    rintro ⟨hc, hN, hM⟩
    exact hp p.2 hc hN hM
  have hEq : P.real {p | p.2 < m * (ell / m) ∧ bridgeSelectedRecord m hm p ∈ D} =
      P.real (H ∩ S) := by
    apply measureReal_congr
    filter_upwards [hdec] with p hp
    apply propext
    by_cases hg : bridgeSelectedRecord m hm p ∈ G
    · have he := hp hg
      have hgg := hg
      simp only [G, Set.mem_ofPred_eq] at hgg
      simp only [H, D, S, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
        hg, hgg.1, hgg.2.1, hgg.2.2, true_and, and_true, he]
    · simp only [H, D, S, G, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      simp only [G, Set.mem_ofPred_eq] at hg
      tauto
  have hJD := hJ m ell n hm hml δ hδ hn hlo hhi hln hcong D
  have hJG := hJ m ell n hm hml δ hδ hn hlo hhi hln hcong G
  change |P.real _ - Q.real D| ≤ _ at hJD
  rw [hEq] at hJD
  change |P.real H - Q.real G| ≤ _ at hJG
  have hP : P.real Set.univ ≤ 1 := by
    change ((cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod U).real Set.univ ≤ 1
    rw [← Set.univ_prod_univ, measureReal_prod_prod]
    have hu : U.real Set.univ ≤ 1 := by
      change (Measure.uniformOfFinset (Finset.range ell)).real Set.univ ≤ 1
      exact measureReal_le_one
    exact (mul_le_mul_of_nonneg_right measureReal_le_one measureReal_nonneg).trans
      (by simp only [one_mul]; exact hu)
  exact window_reduction P hP H S hH hJD hJG

private theorem offset_bad_card (N m : ℕ) :
    ((Finset.univ : Finset (Fin m)).filter
      (fun o => o.val < N ∨ m < o.val + N)).card ≤ 2 * N := by
  let L := (Finset.univ : Finset (Fin m)).filter (fun o => o.val < N)
  let R := (Finset.univ : Finset (Fin m)).filter (fun o => m < o.val + N)
  have hL : L.card ≤ N := by
    have h := Finset.card_le_card_of_injOn (s := L) (t := Finset.range N)
      (fun o => o.val) (by
        intro o ho
        exact Finset.mem_range.mpr (Finset.mem_filter.mp ho).2)
      (by intro a ha b hb hab; exact Fin.ext hab)
    simpa using h
  have hR : R.card ≤ N := by
    have h := Finset.card_le_card_of_injOn (s := R) (t := Finset.range N)
      (fun o => m - 1 - o.val) (by
        intro o ho
        have ho' := (Finset.mem_filter.mp ho).2
        have holt := o.isLt
        apply Finset.mem_range.mpr
        change m - 1 - o.val < N
        omega)
      (by
        intro a ha b hb hab
        change m - 1 - a.val = m - 1 - b.val at hab
        have hat := a.isLt
        have hbt := b.isLt
        apply Fin.ext
        omega)
    simpa using h
  have heq : ((Finset.univ : Finset (Fin m)).filter
      (fun o => o.val < N ∨ m < o.val + N)) = L ∪ R := by
    ext o
    simp [L, R]
  rw [heq]
  exact (Finset.card_union_le L R).trans (by omega)




private theorem bridgeDecoded_target_deficit (N m : ℕ) (hm : 0 < m) :
    let Q := (iidCodeMeasure.map (cappedLevelChunk m (m ^ 100) 0)).prod
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))
    1 - Q.real {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m} ≤
      iidCodeMeasure.real {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} +
        2 * (N : ℝ) / m := by
  dsimp only
  let μ := iidCodeMeasure.map (chunk m (m ^ 100))
  let U := Measure.uniformOfFinset (Finset.univ : Finset (Fin m))
  have : IsProbabilityMeasure U := by
    constructor
    simp only [U, Measure.uniformOfFinset_apply, Set.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    exact ENNReal.div_self (by exact_mod_cast hm.ne') (by finiteness)
  let G : Set (((Fin (m ^ 100) → Fin 3) × Bool) × Fin m) :=
    {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m}
  let bad : Set (Fin m) := {o | o.val < N ∨ m < o.val + N}
  have hG : MeasurableSet G := (Set.toFinite G).measurableSet
  have hsub : Gᶜ ⊆ ({x | x.2 ≠ true} ×ˢ Set.univ) ∪ (Set.univ ×ˢ bad) := by
    intro p hp
    by_cases hc : p.1.2 = true
    · right
      simp only [G, Set.mem_compl_iff, Set.mem_ofPred_eq, hc, true_and,
        not_and, not_le] at hp
      simp only [Set.mem_prod, Set.mem_univ, true_and, bad, Set.mem_ofPred_eq]
      omega
    · left
      exact ⟨hc, Set.mem_univ _⟩
  have hbad : U.real bad ≤ 2 * (N : ℝ) / m := by
    change (Measure.uniformOfFinset _ bad).toReal ≤ _
    rw [Measure.uniformOfFinset_apply, ENNReal.toReal_div]
    simp only [ENNReal.toReal_natCast, Finset.card_univ, Fintype.card_fin]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hc := offset_bad_card N m
    convert (show (((Finset.univ : Finset (Fin m)).filter
        (fun o => o.val < N ∨ m < o.val + N)).card : ℝ) ≤ 2 * (N : ℝ) by
      exact_mod_cast hc) using 1
    congr 2
    ext o
    simp [bad]
  have hcap : μ.real {x | x.2 ≠ true} =
      iidCodeMeasure.real {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} := by
    rw [map_measureReal_apply (measurable_chunk _ _) (Set.toFinite _).measurableSet]
    congr 1
    ext ω
    simp [chunk, not_le]
  rw [map_cappedLevelChunk]
  change 1 - (μ.prod U).real G ≤ _
  have hcomp := measureReal_compl (μ := μ.prod U) hG
  have htotal : (μ.prod U).real Set.univ = 1 := by
    have : IsProbabilityMeasure μ := by
      dsimp [μ]
      infer_instance
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

private theorem uniformLevel_balance (ell : ℕ) :
    ((ell : ℝ≥0∞)⁻¹ • Measure.dirac (0 : ℕ)) +
        Measure.uniformOfFinset (Finset.Icc 1 ell) =
      ((ell : ℝ≥0∞)⁻¹ • Measure.dirac ell) +
        Measure.uniformOfFinset (Finset.range ell) := by
  let f : ℕ → Measure ℕ := fun k => (ell : ℝ≥0∞)⁻¹ • Measure.dirac k
  have hI : Measure.uniformOfFinset (Finset.Icc 1 ell) =
      ∑ k ∈ Finset.Icc 1 ell, f k := by
    simp only [Measure.uniformOfFinset, Nat.card_Icc, Nat.add_sub_cancel]
    rfl
  have hR : Measure.uniformOfFinset (Finset.range ell) =
      ∑ k ∈ Finset.range ell, f k := by
    simp only [Measure.uniformOfFinset, Finset.card_range]
    rfl
  have hi : insert 0 (Finset.Icc 1 ell) = Finset.range (ell + 1) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_range]
    omega
  have h0 : 0 ∉ Finset.Icc 1 ell := by simp
  change f 0 + _ = f ell + _
  rw [hI, hR, ← Finset.sum_insert h0, hi, Finset.sum_range_succ, add_comm]




private theorem bridgeUniformLevel_shift (ell : ℕ) (hell : 0 < ell)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] (S : Set (Ω × ℕ)) (hS : MeasurableSet S) :
    |(μ.prod (Measure.uniformOfFinset (Finset.Icc 1 ell))).real S -
      (μ.prod (Measure.uniformOfFinset (Finset.range ell))).real S| ≤
        1 / (ell : ℝ) := by
  have : IsProbabilityMeasure (Measure.uniformOfFinset (Finset.Icc 1 ell)) := by
    constructor
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true, Nat.card_Icc, Nat.add_sub_cancel]
    exact ENNReal.div_self (by exact_mod_cast hell.ne') (by finiteness)
  have : IsProbabilityMeasure (Measure.uniformOfFinset (Finset.range ell)) := by
    constructor
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true, Finset.card_range]
    exact ENNReal.div_self (by exact_mod_cast hell.ne') (by finiteness)
  have h := congrArg (fun ν : Measure ℕ => (μ.prod ν).real S) (uniformLevel_balance ell)
  have hw : (ell : ℝ≥0∞)⁻¹ ≠ ∞ := by
    simp only [ENNReal.inv_ne_top, Nat.cast_ne_zero]
    exact hell.ne'
  have hatom (k : ℕ) : (μ.prod ((ell : ℝ≥0∞)⁻¹ • Measure.dirac k)) S ≠ ∞ := by
    rw [Measure.prod_smul_right, Measure.smul_apply]
    exact ENNReal.mul_ne_top hw (by finiteness)
  rw [Measure.prod_add, Measure.prod_add, measureReal_add_apply (hatom 0),
    measureReal_add_apply (hatom ell), Measure.prod_smul_right, Measure.prod_smul_right,
    measureReal_ennreal_smul_apply, measureReal_ennreal_smul_apply,
    Measure.prod_dirac, Measure.prod_dirac,
    map_measureReal_apply (by fun_prop) hS,
    map_measureReal_apply (by fun_prop) hS, ENNReal.toReal_inv,
    ENNReal.toReal_natCast] at h
  have h0 : (ell : ℝ)⁻¹ * μ.real ((fun x => (x, 0)) ⁻¹' S) ≤ (ell : ℝ)⁻¹ := by
    exact (mul_le_mul_of_nonneg_left measureReal_le_one (by positivity)).trans_eq
      (mul_one _)
  have h1 : (ell : ℝ)⁻¹ * μ.real ((fun x => (x, ell)) ⁻¹' S) ≤ (ell : ℝ)⁻¹ := by
    exact (mul_le_mul_of_nonneg_left measureReal_le_one (by positivity)).trans_eq
      (mul_one _)
  have h0n : 0 ≤ (ell : ℝ)⁻¹ * μ.real ((fun x => (x, 0)) ⁻¹' S) := by positivity
  have h1n : 0 ≤ (ell : ℝ)⁻¹ * μ.real ((fun x => (x, ell)) ⁻¹' S) := by positivity
  rw [abs_le, one_div]
  constructor <;> linarith only [h, h0, h1, h0n, h1n]

/-- Convention-free quantitative bridge-to-decoder reduction toward corrected
not needed here: this statement quantifies over every measurable extension agreeing with the
true window on interior bridge outcomes. The error uses J2 twice and has the
same fixed-parameter limits. The cap is always `m^100`; cap failure is measured
under the unconditioned law, never divided by the bridge probability. -/
theorem bridgeWindow_reduction_corrected (A : ℝ) (hA : 1 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m ell n : ℕ), (hm : 0 < m) → m ≤ ell →
      ∀ (N : ℕ) (δ : ℝ), 0 < δ → 1 ≤ n →
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      ∀ W : (ℕ → Fin 3) × ℕ → (Fin (2 * N + 1) → ℤ × ℤ),
      Measurable W →
      (∀ ω K, ω ∈ coneEvent (ell : ℤ) 0 n → 1 ≤ K → K ≤ ell →
        N ≤ K → K + N ≤ ell → W (ω, K) = bridgeRawWindow N (ω, K)) →
      ∀ B : Set (Fin (2 * N + 1) → ℤ × ℤ), MeasurableSet B →
      |((cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod
          (Measure.uniformOfFinset (Finset.Icc 1 ell))).real (W ⁻¹' B) -
        ((iidCodeMeasure.map (cappedLevelChunk m (m ^ 100) 0)).prod
          (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
          {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m ∧
            decodeWindow N m (m ^ 100) p.1 p.2.val ∈ B}| ≤
        2 * (δ + 2 * Fintype.card ((Fin (m ^ 100) → Fin 3) × Bool) *
          Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c +
          (m : ℝ) / ell) +
        iidCodeMeasure.real {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} +
        2 * (N : ℝ) / m + 2 * (N : ℝ) / ell + 1 / (ell : ℝ) := by
  obtain ⟨c, hc, hraw⟩ := bridgeRawWindow_reduction_corrected A hA
  refine ⟨c, hc, ?_⟩
  intro m ell n hm hml N δ hδ hn hlo hhi hln hcong W hW hagree B hB
  have hell : 0 < ell := lt_of_lt_of_le hm hml
  have hext := bridgeWindow_extension_independent ell n N (by omega)
    W (bridgeRawWindow N) hW (measurable_bridgeRawWindow N)
    (by
      intro ω K hω hK hN hKN
      have hk := Finset.mem_Icc.mp hK
      exact hagree ω K hω hk.1 hk.2 hN hKN) B hB
  have hshift := bridgeUniformLevel_shift ell hell
    (cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n))
    ((bridgeRawWindow N) ⁻¹' B) ((measurable_bridgeRawWindow N) hB)
  have hr := hraw m ell n hm hml N δ hδ hn hlo hhi hln hcong B hB
  dsimp only at hr
  have hd := bridgeDecoded_target_deficit N m hm
  dsimp only at hd
  have ht := abs_sub_le
    (((cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod
      (Measure.uniformOfFinset (Finset.Icc 1 ell))).real (W ⁻¹' B))
    (((cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod
      (Measure.uniformOfFinset (Finset.Icc 1 ell))).real ((bridgeRawWindow N) ⁻¹' B))
    (((iidCodeMeasure.map (cappedLevelChunk m (m ^ 100) 0)).prod
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
      {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m ∧
        decodeWindow N m (m ^ 100) p.1 p.2.val ∈ B})
  have ht' := abs_sub_le
    (((cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod
      (Measure.uniformOfFinset (Finset.Icc 1 ell))).real ((bridgeRawWindow N) ⁻¹' B))
    (((cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n)).prod
      (Measure.uniformOfFinset (Finset.range ell))).real ((bridgeRawWindow N) ⁻¹' B))
    (((iidCodeMeasure.map (cappedLevelChunk m (m ^ 100) 0)).prod
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
      {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m ∧
        decodeWindow N m (m ^ 100) p.1 p.2.val ∈ B})
  linarith only [hext, hshift, hr, hd, ht, ht']

end DirectedDistances.RandomWalk
