module

public import DirectedDistances.RandomWalk.BridgeWindowContainment
public import DirectedDistances.RandomWalk.UniformLevelWindow
public import Mathlib.Probability.Distributions.Uniform

/-! # Decoded capped-chunk window laws

Helpers toward the corrected Lemma 5.18 (`lem-disk-walk-conv`, -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory

private theorem hit_zero (ω : ℕ → Fin 3) : codeFstFirstHit 0 ω = 0 := by
  classical
  have h : ∃ n, (codeWalk ω n).1 = 0 := ⟨0, by simp [codeWalk_zero]⟩
  have hf : Nat.find h = 0 := by
    apply (Nat.find_eq_iff h).2
    exact ⟨by simp [codeWalk_zero], by omega⟩
  simp [codeFstFirstHit, h, hf]

private theorem hit_shift_zero (a : ℤ) (ω : ℕ → Fin 3) :
    codeFstFirstHit a (codeShift 0 ω) = codeFstFirstHit a ω := by
  have hw : codeWalk (codeShift 0 ω) = codeWalk ω := by
    funext n
    simp [codeWalk_codeShift, codeWalk_zero]
  unfold codeFstFirstHit
  rw [hw]

/-- The completion bit at the initial block is exactly non-overflow. Helper
for corrected Lemma 5.18 (`lem-disk-walk-conv`, -/
theorem cappedLevelChunk_zero_complete_iff (m C : ℕ) (ω : ℕ → Fin 3) :
    (cappedLevelChunk m C 0 ω).2 = true ↔
      codeFstFirstHit (-(m : ℤ)) ω ≤ C := by
  simp [cappedLevelChunk, chunk, hit_zero, hit_shift_zero]

private theorem level_le_hit (d : ℕ) (ω : ℕ → Fin 3)
    (hfin : codeFstFirstHit (-(d : ℤ)) ω < ⊤) :
    d ≤ (codeFstFirstHit (-(d : ℤ)) ω).toNat := by
  classical
  have hhit : ∃ n, (codeWalk ω n).1 = -(d : ℤ) := by
    by_contra hn
    simp [codeFstFirstHit, hn] at hfin
  have hlo : ∀ n : ℕ, -(n : ℤ) ≤ (codeWalk ω n).1 := by
    intro n
    induction n with
    | zero => simp [codeWalk_zero]
    | succ n ih =>
      have hs := congrArg Prod.fst (codeWalk_succ_sub ω n)
      rw [Prod.fst_sub] at hs
      have hstep : -1 ≤ (lazyTwoDimensionalStep (ω (n + 1))).1 := by
        generalize ω (n + 1) = c
        fin_cases c <;> decide
      omega
  have h := hlo (Nat.find hhit)
  rw [Nat.find_spec hhit] at h
  simpa [codeFstFirstHit, hhit] using (show d ≤ Nat.find hhit by omega)

/-- A completed initial chunk decodes the genuine first-hit-centered window
at every interior offset. Helper toward corrected Lemma 5.18 -/
theorem ae_decodeWindow_eq_centeredWindowAtFirstHit (N m o : ℕ)
    (hNo : N ≤ o) (hoN : o + N ≤ m) :
    ∀ᵐ ω ∂iidCodeMeasure,
      (cappedLevelChunk m (m ^ 100) 0 ω).2 = true →
        decodeWindow N m (m ^ 100) (cappedLevelChunk m (m ^ 100) 0 ω) o =
          centeredWindowAtFirstHit N o ω := by
  filter_upwards [ae_cappedLevelChunk_decodeWindow N m 0 o,
    ae_codeFstFirstHit_lt_top_int (-(o : ℤ))] with ω hd hf
  intro hc
  have htime := hNo.trans (level_le_hit o ω hf)
  simpa [centeredWindowAtFirstHit, htime] using (hd hc hNo hoN).symm

/-- Measurability of the first-hit-centered window. Helper toward corrected
not counted. -/
theorem measurable_centeredWindowAtFirstHit (N o : ℕ) :
    Measurable (centeredWindowAtFirstHit N o) := by
  have hh : Measurable (codeFstFirstHit (-(o : ℤ))) := by
    rw [ENat.measurable_iff]
    intro k
    exact codePast_le k _ (measurableSet_codePast_codeFstFirstHit_eq _ k)
  have ht : Measurable (fun ω => (codeFstFirstHit (-(o : ℤ)) ω).toNat) :=
    (measurable_of_countable ENat.toNat).comp hh
  have heval : Measurable (fun p : (ℕ → Fin 3) × ℕ => codeWalk p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_codeWalk.eval
  have hw := heval.comp (measurable_id.prodMk ht)
  apply Measurable.ite (measurableSet_le measurable_const ht) _ measurable_const
  apply Measurable.of_eval
  intro j
  exact (heval.comp (measurable_id.prodMk
    ((ht.add_const j.val).sub_const N))).sub hw

/-- At a fixed interior level, discarding incomplete chunks loses at most
the overflow probability, setwise. Helper toward corrected Lemma 5.18 -/
theorem decodedChunkWindow_fixedLevel_bound (N m o : ℕ)
    (hNo : N ≤ o) (hoN : o + N ≤ m)
    (B : Set (Fin (2 * N + 1) → ℤ × ℤ)) (hB : MeasurableSet B) :
    |iidCodeMeasure.real {ω |
        (cappedLevelChunk m (m ^ 100) 0 ω).2 = true ∧
          decodeWindow N m (m ^ 100) (cappedLevelChunk m (m ^ 100) 0 ω) o ∈ B} -
      (iidCodeMeasure.map (centeredWindowAtFirstHit N o)).real B| ≤
        iidCodeMeasure.real {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} := by
  let E : Set (ℕ → Fin 3) := {ω | (cappedLevelChunk m (m ^ 100) 0 ω).2 = true}
  let F : Set (ℕ → Fin 3) := {ω | centeredWindowAtFirstHit N o ω ∈ B}
  have heq : iidCodeMeasure.real {ω |
      (cappedLevelChunk m (m ^ 100) 0 ω).2 = true ∧
        decodeWindow N m (m ^ 100) (cappedLevelChunk m (m ^ 100) 0 ω) o ∈ B} =
        iidCodeMeasure.real (E ∩ F) := by
    apply measureReal_congr
    filter_upwards [ae_decodeWindow_eq_centeredWindowAtFirstHit N m o hNo hoN] with ω hω
    apply propext
    change (_ ∧ _) ↔ (_ ∧ _)
    constructor
    · rintro ⟨hc, hb⟩
      exact ⟨hc, by simpa [F, hω hc] using hb⟩
    · rintro ⟨hc, hb⟩
      exact ⟨hc, by simpa [F, hω hc] using hb⟩
  have hcomp : Eᶜ = {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} := by
    ext ω
    simp [E, cappedLevelChunk_zero_complete_iff, not_le]
  rw [heq, map_measureReal_apply (measurable_centeredWindowAtFirstHit N o) hB]
  change |iidCodeMeasure.real (E ∩ F) - iidCodeMeasure.real F| ≤ _
  have hle : iidCodeMeasure.real (E ∩ F) ≤ iidCodeMeasure.real F :=
    measureReal_mono Set.inter_subset_right
  have hcover : F ⊆ (E ∩ F) ∪ Eᶜ := by
    intro ω hω
    by_cases he : ω ∈ E
    · exact Or.inl ⟨he, hω⟩
    · exact Or.inr he
  have hb := (measureReal_mono (μ := iidCodeMeasure) hcover).trans
    (measureReal_union_le (μ := iidCodeMeasure) (E ∩ F) Eᶜ)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  rw [← hcomp]
  linarith

private theorem prod_uniform_real
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : ℕ) (hm : 0 < m) (S : Set (Ω × Fin m)) (hS : MeasurableSet S) :
    (μ.prod (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real S =
      (m : ℝ)⁻¹ * ∑ o : Fin m, μ.real {ω | (ω, o) ∈ S} := by
  let U : Measure (Fin m) := Measure.uniformOfFinset Finset.univ
  have : IsProbabilityMeasure U := by
    constructor
    simp only [U, Measure.uniformOfFinset_apply, Set.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    exact ENNReal.div_self (by exact_mod_cast hm.ne') (by finiteness)
  have hatom (o : Fin m) : U.real {o} = (m : ℝ)⁻¹ := by
    simp [U, Measure.real, Measure.uniformOfFinset_apply_singleton, ENNReal.toReal_inv]
  let F : Fin m → Set (Ω × Fin m) := fun o => {ω | (ω, o) ∈ S} ×ˢ {o}
  have hcover : S = ⋃ o, F o := by
    ext z
    simp [F]
  have hdis : Pairwise (fun o p => Disjoint (F o) (F p)) := by
    intro o p hop
    apply Set.disjoint_left.mpr
    rintro ⟨ω, u⟩ ⟨_, ho⟩ ⟨_, hp⟩
    exact hop (ho.symm.trans hp)
  have hmeas (o : Fin m) : MeasurableSet (F o) :=
    (hS.preimage (measurable_id.prodMk measurable_const)).prod (measurableSet_singleton o)
  change (μ.prod U).real _ = _
  conv_lhs => rw [hcover, measureReal_iUnion_fintype hdis hmeas]
  simp_rw [F, measureReal_prod_prod, hatom]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o ho
  ring

/-- The interior-offset decoded chunk mass differs from the average of the
fixed-level window laws by at most the overflow probability. Helper toward
corrected Lemma 5.18 (`lem-disk-walk-conv`, -/
theorem decodedChunkWindow_average_fixedLevel_bound (N m : ℕ)
    (B : Set (Fin (2 * N + 1) → ℤ × ℤ)) (hB : MeasurableSet B) :
    |((iidCodeMeasure.map (cappedLevelChunk m (m ^ 100) 0)).prod
        (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
        {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m ∧
          decodeWindow N m (m ^ 100) p.1 p.2.val ∈ B} -
      (1 / (m : ℝ)) * ∑ o ∈ (Finset.univ.filter
        (fun o : Fin m => N ≤ o.val ∧ o.val + N ≤ m)),
        (iidCodeMeasure.map (centeredWindowAtFirstHit N o.val)).real B| ≤
      iidCodeMeasure.real {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} := by
  classical
  by_cases hm : m = 0
  · subst m
    simp [Measure.uniformOfFinset, measureReal_nonneg]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  let I := Finset.univ.filter (fun o : Fin m => N ≤ o.val ∧ o.val + N ≤ m)
  let a : Fin m → ℝ := fun o => iidCodeMeasure.real {ω |
    (cappedLevelChunk m (m ^ 100) 0 ω).2 = true ∧
      decodeWindow N m (m ^ 100) (cappedLevelChunk m (m ^ 100) 0 ω) o.val ∈ B}
  let b : Fin m → ℝ := fun o =>
    (iidCodeMeasure.map (centeredWindowAtFirstHit N o.val)).real B
  let r := iidCodeMeasure.real {ω |
    (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω}
  have hmass : ((iidCodeMeasure.map (cappedLevelChunk m (m ^ 100) 0)).prod
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
      {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m ∧
        decodeWindow N m (m ^ 100) p.1 p.2.val ∈ B} =
      (m : ℝ)⁻¹ * ∑ o ∈ I, a o := by
    rw [prod_uniform_real _ m hmpos _ (MeasurableSet.of_discrete)]
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro o _
    rw [map_measureReal_apply (measurable_cappedLevelChunk _ _ _) MeasurableSet.of_discrete]
    by_cases hi : N ≤ o.val ∧ o.val + N ≤ m
    · simp [hi.1, hi.2, a]
    · simp [hi]
      have he : {ω | (cappedLevelChunk m (m ^ 100) 0 ω).2 = true ∧
          N ≤ o.val ∧ o.val + N ≤ m ∧
          decodeWindow N m (m ^ 100) (cappedLevelChunk m (m ^ 100) 0 ω) o.val ∈ B} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        tauto
      simpa using congrArg iidCodeMeasure.real he
  have herr (o : Fin m) (ho : o ∈ I) : |a o - b o| ≤ r := by
    have hi := (Finset.mem_filter.mp ho).2
    exact decodedChunkWindow_fixedLevel_bound N m o.val hi.1 hi.2 B hB
  have hcard : (I.card : ℝ) ≤ m := by
    exact_mod_cast (show I.card ≤ m from
      (Finset.card_filter_le _ _).trans (by simp))
  rw [hmass, one_div]
  change |(m : ℝ)⁻¹ * ∑ o ∈ I, a o - (m : ℝ)⁻¹ * ∑ o ∈ I, b o| ≤ r
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m))]
  calc
    (m : ℝ)⁻¹ * |∑ o ∈ I, (a o - b o)| ≤
        (m : ℝ)⁻¹ * ∑ o ∈ I, |a o - b o| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (inv_nonneg.mpr (Nat.cast_nonneg m))
    _ ≤ (m : ℝ)⁻¹ * ∑ _o ∈ I, r := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg m))
      exact Finset.sum_le_sum herr
    _ = ((I.card : ℝ) / m) * r := by simp; ring
    _ ≤ r := mul_le_of_le_one_left measureReal_nonneg
      ((div_le_one (by exact_mod_cast hmpos)).mpr hcard)

/-- corrected Lemma 5.18 (`lem-disk-walk-conv`, -/
theorem nonInteriorOffset_count_le (N m : ℕ) :
    (Finset.univ.filter (fun o : Fin m => ¬ (N ≤ o.val ∧ o.val + N ≤ m))).card ≤
      2 * N := by
  classical
  let L := Finset.univ.filter (fun o : Fin m => o.val < N)
  let R := Finset.univ.filter (fun o : Fin m => m < o.val + N)
  have hL : L.card ≤ N := by
    calc
      L.card ≤ (Finset.range N).card := by
        apply Finset.card_le_card_of_injOn Fin.val
        · intro o ho
          exact Finset.mem_range.mpr (Finset.mem_filter.mp ho).2
        · intro a _ b _ hab
          exact Fin.ext hab
      _ = N := Finset.card_range _
  have hR : R.card ≤ N := by
    calc
      R.card ≤ (Finset.range N).card := by
        apply Finset.card_le_card_of_injOn (fun o : Fin m => m - 1 - o.val)
        · intro o ho
          have h := (Finset.mem_filter.mp ho).2
          have := o.isLt
          apply Finset.mem_range.mpr
          change m - 1 - o.val < N
          omega
        · intro a _ b _ hab
          have := a.isLt
          have := b.isLt
          apply Fin.ext
          change m - 1 - a.val = m - 1 - b.val at hab
          omega
      _ = N := Finset.card_range _
  have heq : Finset.univ.filter (fun o : Fin m => ¬ (N ≤ o.val ∧ o.val + N ≤ m)) =
      L ∪ R := by
    ext o
    simp [L, R]
    omega
  rw [heq]
  exact (Finset.card_union_le _ _).trans (by omega)

/-- The decoded interior-offset mass approaches the UIBHBOT excursion-window
law, with explicit overflow and boundary errors. Helper toward corrected
not counted. The positive block size is necessary for this normalized bound. -/
theorem decodedChunkWindow_excursionWindow_bound (N m : ℕ) (hm : 0 < m)
    (B : Set (Fin (2 * N + 1) → ℤ × ℤ)) (hB : MeasurableSet B) :
    |((iidCodeMeasure.map (cappedLevelChunk m (m ^ 100) 0)).prod
        (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
        {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m ∧
          decodeWindow N m (m ^ 100) p.1 p.2.val ∈ B} -
      (uibhbotExcursionWindowLaw N).real B| ≤
      iidCodeMeasure.real {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} +
        (2 * (N : ℝ)) / m := by
  classical
  let I := Finset.univ.filter (fun o : Fin m => N ≤ o.val ∧ o.val + N ≤ m)
  let J := Finset.univ.filter (fun o : Fin m => ¬ (N ≤ o.val ∧ o.val + N ≤ m))
  let L := (uibhbotExcursionWindowLaw N).real B
  let w : ℝ := (I.card : ℝ) / m
  let A := ((iidCodeMeasure.map (cappedLevelChunk m (m ^ 100) 0)).prod
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
    {p | p.1.2 = true ∧ N ≤ p.2.val ∧ p.2.val + N ≤ m ∧
      decodeWindow N m (m ^ 100) p.1 p.2.val ∈ B}
  let r := iidCodeMeasure.real {ω |
    (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω}
  have hsum : (∑ o ∈ I,
      (iidCodeMeasure.map (centeredWindowAtFirstHit N o.val)).real B) =
      (I.card : ℝ) * L := by
    calc
      _ = ∑ _o ∈ I, L := by
        apply Finset.sum_congr rfl
        intro o ho
        rw [firstHitWindow_law_eq_excursionWindow N o.val (Finset.mem_filter.mp ho).2.1]
      _ = _ := by simp
  have hfixed : |A - w * L| ≤ r := by
    have h := decodedChunkWindow_average_fixedLevel_bound N m B hB
    change |A - (1 / (m : ℝ)) * ∑ o ∈ I,
      (iidCodeMeasure.map (centeredWindowAtFirstHit N o.val)).real B| ≤ r at h
    rw [hsum] at h
    have he : 1 / (m : ℝ) * ((I.card : ℝ) * L) = w * L := by dsimp [w]; ring
    rwa [he] at h
  have hc : I.card + J.card = m := by
    simpa [I, J] using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin m)))
      (fun o : Fin m => N ≤ o.val ∧ o.val + N ≤ m))
  have hJ : J.card ≤ 2 * N := nonInteriorOffset_count_le N m
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcardR : (I.card : ℝ) + J.card = m := by exact_mod_cast hc
  have hJR : (J.card : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hJ
  have hw : w ≤ 1 := (div_le_one hmR).mpr (by linarith [show (0 : ℝ) ≤ (J.card : ℝ) from Nat.cast_nonneg _])
  have hboundary : 1 - w ≤ 2 * (N : ℝ) / m := by
    dsimp [w]
    apply (le_div_iff₀ hmR).mpr
    field_simp
    linarith
  have hL0 : 0 ≤ L := measureReal_nonneg
  have hL1 : L ≤ 1 := measureReal_le_one
  have herror : |w * L - L| ≤ 2 * (N : ℝ) / m := by
    rw [abs_of_nonpos (by nlinarith only [hw, hL0])]
    calc
      -(w * L - L) = (1 - w) * L := by ring
      _ ≤ 1 - w := mul_le_of_le_one_right (by linarith) hL1
      _ ≤ _ := hboundary
  change |A - L| ≤ r + _
  exact (abs_sub_le A (w * L) L).trans (add_le_add hfixed herror)

end DirectedDistances.RandomWalk
