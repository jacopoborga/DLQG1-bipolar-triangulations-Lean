module

public import DirectedDistances.RandomWalk.ConeProbLowerCorrected
public import DirectedDistances.RandomWalk.QuadrantReturnProb
public import DirectedDistances.RandomWalk.CappedLevelChunks
public import DirectedDistances.Probability.FiniteAlphabetHoeffding
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt

/-! # Conditioned selected chunks

Helpers for the conditioned selected-chunk law in `lem-disk-walk-conv`,
Concentration uses Hoeffding and a union bound in place of Cramér.
These helpers are not counted as numbered paper results. The chunk records
are relative to their starting level; translating the walk by `(ℓ,0)` only
changes the conditioning event. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Function

noncomputable section
open scoped Classical

local instance (priority := 100) classicalDecEq {α : Type*} [Fintype α] : DecidableEq α :=
  Classical.decEq α

local instance (priority := 2000) chunkDecEq (C : ℕ) :
    DecidableEq ((Fin C → Fin 3) × Bool) := Classical.decEq _

private theorem conditionedFiniteAlphabetHoeffding
    {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {ν : Measure α} [IsProbabilityMeasure ν] {X : ℕ → Ω → α}
    (hX : ∀ s, Measurable (X s)) (hind : iIndepFun X μ)
    (hlaw : ∀ s, μ.map (X s) = ν)
    (E : Set Ω) (L : ℕ) (hL : 0 < L) (δ : ℝ) (hδ : 0 < δ) :
    μ.real {ω ∈ E | ∃ a : α,
      δ < |(L : ℝ)⁻¹ * ∑ s ∈ Finset.range L,
        (if X s ω = a then (1 : ℝ) else 0) - ν.real {a}|} / μ.real E ≤
      (2 * Fintype.card α * Real.exp (-2 * δ ^ 2 * L)) / μ.real E := by
  let D : Set Ω := {ω | ∃ a : α,
      δ < |(L : ℝ)⁻¹ * ∑ s ∈ Finset.range L,
        (if X s ω = a then (1 : ℝ) else 0) - ν.real {a}|}
  have h : μ.real D ≤ 2 * Fintype.card α * Real.exp (-2 * δ ^ 2 * L) :=
    DirectedDistances.Probability.finiteAlphabetHoeffding hX hind hlaw L hL δ hδ
  have hmono : μ.real (E ∩ D) ≤ μ.real D :=
    measureReal_mono Set.inter_subset_right
  exact div_le_div_of_nonneg_right (hmono.trans h) measureReal_nonneg

/-- Empirical symbol frequencies under cone conditioning, with the conditioning
cost left as its explicit probability. Helper for `lem-disk-walk-conv`, -/
theorem conditionedChunk_empirical (m C ell n : ℕ) (hm : 0 < m)
    (hL : 0 < ell / m) (δ : ℝ) (hδ : 0 < δ) :
    iidCodeMeasure.real {ω ∈ coneEvent (ell : ℤ) 0 n |
      ∃ a : (Fin C → Fin 3) × Bool,
        δ < |((ell / m : ℕ) : ℝ)⁻¹ *
          ∑ s ∈ Finset.range (ell / m),
            (if cappedLevelChunk m C s ω = a then (1 : ℝ) else 0) -
          (iidCodeMeasure.map (chunk m C)).real {a}|} /
        iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n) ≤
      (2 * Fintype.card ((Fin C → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell / m : ℕ))) /
          iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n) := by
  have hind : iIndepFun (cappedLevelChunk m C) iidCodeMeasure :=
    iIndepFun_cappedLevelChunks m C hm
  exact conditionedFiniteAlphabetHoeffding
    (ν := iidCodeMeasure.map (chunk m C))
    (measurable_cappedLevelChunk m C) hind (map_cappedLevelChunk m C)
    (coneEvent (ell : ℤ) 0 n) (ell / m) hL δ hδ

/-- On the corrected C15/C19 band, one positive constant works for every
admissible size in the conditional empirical estimate. Helper for -/
theorem conditionedChunk_empirical_corrected (A : ℝ) (hA : 1 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m C ell n : ℕ), 0 < m → 0 < ell / m →
      ∀ δ : ℝ, 0 < δ → 1 ≤ n →
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      iidCodeMeasure.real {ω ∈ coneEvent (ell : ℤ) 0 n |
        ∃ a : (Fin C → Fin 3) × Bool,
          δ < |((ell / m : ℕ) : ℝ)⁻¹ *
            ∑ s ∈ Finset.range (ell / m),
              (if cappedLevelChunk m C s ω = a then (1 : ℝ) else 0) -
            (iidCodeMeasure.map (chunk m C)).real {a}|} /
          iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n) ≤
        2 * Fintype.card ((Fin C → Fin 3) × Bool) *
          Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c := by
  obtain ⟨c, hc, hcone⟩ := coneProbLower_corrected A hA
  refine ⟨c, hc, ?_⟩
  intro m C ell n hm hL δ hδ hn hlo hhi hln hcong
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlower := hcone n hn (ell : ℤ) (by simpa using hlo) (by simpa using hhi)
    (by exact_mod_cast hln) hcong
  change c * (n : ℝ) ^ (-3 : ℝ) ≤
    iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n) at hlower
  have hpow : (n : ℝ) ^ (-3 : ℝ) = ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hn0.le]
    norm_num
  rw [hpow] at hlower
  have hlowpos : 0 < c * ((n : ℝ) ^ (3 : ℕ))⁻¹ := by positivity
  have hmass : 0 < iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n) :=
    lt_of_lt_of_le hlowpos hlower
  refine (conditionedChunk_empirical m C ell n hm hL δ hδ).trans ?_
  calc
    _ ≤ (2 * Fintype.card ((Fin C → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell / m : ℕ))) /
        (c * ((n : ℝ) ^ (3 : ℕ))⁻¹) :=
      div_le_div_of_nonneg_left (by positivity) hlowpos hlower
    _ = _ := by field_simp

private theorem conditionedMean_deviation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {E : Set Ω} (_hE : MeasurableSet E) (hpos : 0 < μ.real E)
    {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (hf1 : ∀ ω, f ω ≤ 1) {p δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hδ : 0 < δ) :
    |(∫ ω in E, f ω ∂μ) / μ.real E - p| ≤
      δ + μ.real {ω ∈ E | δ < |f ω - p|} / μ.real E := by
  let D : Set Ω := {ω | δ < |f ω - p|}
  have hD : MeasurableSet D := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (hf.sub measurable_const))
  have hfi : Integrable f (μ.restrict E) :=
    (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]; exact hf1 ω)
  have hdi : Integrable (fun ω => f ω - p) (μ.restrict E) :=
    hfi.sub (integrable_const p)
  have hIi : Integrable (D.indicator (fun _ : Ω => (1 : ℝ))) (μ.restrict E) :=
    (integrable_const (1 : ℝ)).indicator hD
  have hbound : ∀ ω, |f ω - p| ≤ δ + D.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ D
    · rw [Set.indicator_of_mem hω]
      have hab : |f ω - p| ≤ 1 := abs_le.mpr ⟨by linarith [hf0 ω], by linarith [hf1 ω]⟩
      linarith
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact le_of_not_gt hω
  have hint := integral_mono hdi.abs ((integrable_const δ).add hIi) hbound
  have hI : ∫ ω in E, D.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ =
      μ.real {ω ∈ E | δ < |f ω - p|} := by
    rw [integral_indicator hD, setIntegral_const, measureReal_restrict_apply hD,
      smul_eq_mul, mul_one]
    congr 1
    ext ω
    simp [D, and_comm]
  change (∫ x in E, |f x - p| ∂μ) ≤
    ∫ x in E, δ + D.indicator (fun _ => (1 : ℝ)) x ∂μ at hint
  rw [integral_add (integrable_const δ) hIi, setIntegral_const, smul_eq_mul, hI] at hint
  have hsub : ∫ ω in E, (f ω - p) ∂μ = (∫ ω in E, f ω ∂μ) - μ.real E * p := by
    rw [integral_sub hfi (integrable_const p), setIntegral_const, smul_eq_mul]
  have hab := abs_integral_le_integral_abs (f := fun ω => f ω - p) (μ := μ.restrict E)
  rw [hsub] at hab
  have hfinal := hab.trans hint
  rw [div_sub' (ne_of_gt hpos), abs_div, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  calc
    _ ≤ μ.real E * δ + μ.real {ω ∈ E | δ < |f ω - p|} := hfinal
    _ = _ := by field_simp

private theorem setEmpiricalHoeffding
    {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {ν : Measure α} [IsProbabilityMeasure ν] {X : ℕ → Ω → α}
    (hX : ∀ s, Measurable (X s)) (hind : iIndepFun X μ)
    (hlaw : ∀ s, μ.map (X s) = ν)
    (B : Set α) (_hB : MeasurableSet B)
    (L : ℕ) (hL : 0 < L) (δ : ℝ) (hδ : 0 < δ) :
    μ.real {ω | δ < |(L : ℝ)⁻¹ * ∑ s ∈ Finset.range L,
      (if X s ω ∈ B then (1 : ℝ) else 0) - ν.real B|} ≤
      4 * Real.exp (-2 * δ ^ 2 * L) := by
  let _ : DecidableEq Bool := Classical.decEq Bool
  let g : α → Bool := fun a => decide (a ∈ B)
  have hg : Measurable g := measurable_of_finite _
  let Y : ℕ → Ω → Bool := fun s => g ∘ X s
  have hY : ∀ s, Measurable (Y s) := fun s => hg.comp (hX s)
  have hindY : iIndepFun Y μ := hind.comp (fun _ => g) (fun _ => hg)
  have hlawY : ∀ s, μ.map (Y s) = ν.map g := by
    intro s
    rw [show Y s = g ∘ X s from rfl, ← Measure.map_map hg (hX s), hlaw s]
  have hp : (ν.map g).real {true} = ν.real B := by
    rw [map_measureReal_apply hg (measurableSet_singleton true)]
    congr 1
    ext a
    simp [g]
  have h := DirectedDistances.Probability.finiteAlphabetHoeffding
    hY hindY hlawY L hL δ hδ
  have hmono : μ.real {ω | δ < |(L : ℝ)⁻¹ * ∑ s ∈ Finset.range L,
      (if X s ω ∈ B then (1 : ℝ) else 0) - ν.real B|} ≤
      μ.real {ω | ∃ a : Bool, δ < |(L : ℝ)⁻¹ * ∑ s ∈ Finset.range L,
      (if Y s ω = a then (1 : ℝ) else 0) - (ν.map g).real {a}|} := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    refine ⟨true, ?_⟩
    simpa [Y, g, Function.comp_def, hp] using hω
  norm_num only [Fintype.card_bool, Nat.cast_ofNat] at h
  exact hmono.trans h

private theorem conditionedSelected_average
    {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {ν : Measure α} [IsProbabilityMeasure ν] {X : ℕ → Ω → α}
    (hX : ∀ s, Measurable (X s)) (hind : iIndepFun X μ)
    (hlaw : ∀ s, μ.map (X s) = ν)
    (E : Set Ω) (hE : MeasurableSet E) (hpos : 0 < μ.real E)
    (B : Set α) (hB : MeasurableSet B)
    (L : ℕ) (hL : 0 < L) (δ : ℝ) (hδ : 0 < δ) :
    |((L : ℝ)⁻¹ * ∑ s ∈ Finset.range L,
      μ.real {ω ∈ E | X s ω ∈ B}) / μ.real E - ν.real B| ≤
      δ + 4 * Real.exp (-2 * δ ^ 2 * L) / μ.real E := by
  let f : Ω → ℝ := fun ω => (L : ℝ)⁻¹ * ∑ s ∈ Finset.range L,
    if X s ω ∈ B then (1 : ℝ) else 0
  have hI (s : ℕ) : Measurable (fun ω => if X s ω ∈ B then (1 : ℝ) else 0) :=
    Measurable.ite ((hX s) hB) measurable_const measurable_const
  have hf : Measurable f := measurable_const.mul
    (Finset.measurable_sum _ (fun s _ => hI s))
  have hLp : 0 < (L : ℝ) := by exact_mod_cast hL
  have hf0 (ω) : 0 ≤ f ω := by dsimp [f]; positivity
  have hf1 (ω) : f ω ≤ 1 := by
    have hs : (∑ s ∈ Finset.range L,
        if X s ω ∈ B then (1 : ℝ) else 0) ≤ (L : ℝ) := by
      calc
        _ ≤ ∑ _s ∈ Finset.range L, (1 : ℝ) :=
          Finset.sum_le_sum fun s _ => by split_ifs <;> norm_num
        _ = _ := by simp
    calc
      f ω ≤ (L : ℝ)⁻¹ * L := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hLp.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hLp)
  have hmean := conditionedMean_deviation hE hpos hf hf0 hf1
    (p := ν.real B) measureReal_nonneg (by
      calc
        ν.real B ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ _)
        _ = 1 := by simp) hδ
  have hint : (∫ ω in E, f ω ∂μ) = (L : ℝ)⁻¹ *
      ∑ s ∈ Finset.range L, μ.real {ω ∈ E | X s ω ∈ B} := by
    dsimp [f]
    rw [integral_const_mul, integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro s hs
      have hid : (fun ω => if X s ω ∈ B then (1 : ℝ) else 0) =
          {ω | X s ω ∈ B}.indicator (fun _ => (1 : ℝ)) := by
        funext ω
        simp [Set.indicator_apply]
      have hset : MeasurableSet {ω | X s ω ∈ B} := (hX s) hB
      rw [hid, integral_indicator hset, setIntegral_const,
        measureReal_restrict_apply hset, smul_eq_mul, mul_one]
      congr 1
      ext ω
      simp [and_comm]
    · intro s hs
      have hid : (fun ω => if X s ω ∈ B then (1 : ℝ) else 0) =
          {ω | X s ω ∈ B}.indicator (fun _ => (1 : ℝ)) := by
        funext ω
        simp [Set.indicator_apply]
      rw [hid]
      exact (integrable_const (1 : ℝ)).indicator ((hX s) hB)
  rw [hint] at hmean
  refine hmean.trans (add_le_add le_rfl (div_le_div_of_nonneg_right ?_ hpos.le))
  exact (measureReal_mono Set.inter_subset_right).trans
    (setEmpiricalHoeffding hX hind hlaw B hB L hL δ hδ)

private theorem measurableSet_coneEvent' (ell : ℤ) (n : ℕ) :
    MeasurableSet (coneEvent ell 0 n) := by
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

private theorem selectedProduct_eq_average
    {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [MeasurableSpace α] {X : ℕ → Ω → α} (hX : ∀ s, Measurable (X s))
    (E : Set Ω) (hE : MeasurableSet E) (B : Set α) (hB : MeasurableSet B)
    (L : ℕ) (hL : 0 < L) :
    ((Measure.uniformOfFinset (Finset.univ : Finset (Fin L))).prod μ).real
      {z | z.2 ∈ E ∧ X z.1.val z.2 ∈ B} =
      (L : ℝ)⁻¹ * ∑ s ∈ Finset.range L, μ.real {ω ∈ E | X s ω ∈ B} := by
  let U : Measure (Fin L) := Measure.uniformOfFinset Finset.univ
  have : IsProbabilityMeasure U := by
    constructor
    simp only [U, Measure.uniformOfFinset_apply, Set.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    exact ENNReal.div_self (by exact_mod_cast hL.ne') (by finiteness)
  have hatom (s : Fin L) : U.real {s} = (L : ℝ)⁻¹ := by
    simp [U, Measure.real, Measure.uniformOfFinset_apply_singleton, ENNReal.toReal_inv]
  let F : Fin L → Set (Fin L × Ω) := fun s =>
    {s} ×ˢ {ω ∈ E | X s.val ω ∈ B}
  have hcover : {z : Fin L × Ω | z.2 ∈ E ∧ X z.1.val z.2 ∈ B} = ⋃ s, F s := by
    ext z
    simp [F]
  have hdis : Pairwise (Disjoint on F) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    rintro ⟨u, ω⟩ ⟨hs, _⟩ ⟨ht, _⟩
    exact hst (hs.symm.trans ht)
  have hmeas (s : Fin L) : MeasurableSet (F s) :=
    (measurableSet_singleton s).prod (hE.inter ((hX s.val) hB))
  change (U.prod μ).real _ = _
  rw [hcover, measureReal_iUnion_fintype hdis hmeas]
  simp_rw [F, measureReal_prod_prod, hatom]
  rw [← Finset.mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun s : ℕ => μ.real {ω ∈ E | X s ω ∈ B}) L

/-- The conditional law of a chunk selected by an independent uniform index,
written as a product-measure ratio, is setwise close to its unconditioned law.
The corrected C15/C19 lower bound supplies the positive denominator below.
Hoeffding plus union bound replaces Cramér; not counted. -/
theorem conditionedSelectedChunk_corrected (A : ℝ) (hA : 1 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m C ell n : ℕ), 0 < m → 0 < ell / m →
      ∀ δ : ℝ, 0 < δ → 1 ≤ n →
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      ∀ B : Set ((Fin C → Fin 3) × Bool),
      |(((Measure.uniformOfFinset (Finset.univ : Finset (Fin (ell / m)))).prod
          iidCodeMeasure).real
          {z | z.2 ∈ coneEvent (ell : ℤ) 0 n ∧
            cappedLevelChunk m C z.1.val z.2 ∈ B}) /
          iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n) -
        (iidCodeMeasure.map (chunk m C)).real B| ≤
      δ + 2 * Fintype.card ((Fin C → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c := by
  obtain ⟨c, hc, hcone⟩ := coneProbLower_corrected A hA
  refine ⟨c, hc, ?_⟩
  intro m C ell n hm hL δ hδ hn hlo hhi hln hcong B
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlower := hcone n hn (ell : ℤ) (by simpa using hlo) (by simpa using hhi)
    (by exact_mod_cast hln) hcong
  change c * (n : ℝ) ^ (-3 : ℝ) ≤
    iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n) at hlower
  have hpow : (n : ℝ) ^ (-3 : ℝ) = ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hn0.le]
    norm_num
  rw [hpow] at hlower
  have hlowpos : 0 < c * ((n : ℝ) ^ (3 : ℕ))⁻¹ := by positivity
  have hmass := lt_of_lt_of_le hlowpos hlower
  have hB : MeasurableSet B := (Set.toFinite B).measurableSet
  rw [selectedProduct_eq_average (measurable_cappedLevelChunk m C) _
    (measurableSet_coneEvent' _ _) B hB _ hL]
  have hind : iIndepFun (cappedLevelChunk m C) iidCodeMeasure :=
    iIndepFun_cappedLevelChunks m C hm
  have h := conditionedSelected_average (measurable_cappedLevelChunk m C) hind
    (map_cappedLevelChunk m C) _ (measurableSet_coneEvent' _ _) hmass
    B hB _ hL δ hδ
  refine h.trans (add_le_add le_rfl ?_)
  have hcard : (4 : ℝ) ≤ 2 * Fintype.card ((Fin C → Fin 3) × Bool) := by
    simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
    have hp : 1 ≤ Fintype.card (Fin C → Fin 3) := Fintype.card_pos_iff.mpr inferInstance
    have hp' : (1 : ℝ) ≤ Fintype.card (Fin C → Fin 3) := by exact_mod_cast hp
    linarith
  calc
    _ ≤ (2 * Fintype.card ((Fin C → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell / m : ℕ))) /
        iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le) hmass.le
    _ ≤ (2 * Fintype.card ((Fin C → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell / m : ℕ))) /
        (c * ((n : ℝ) ^ (3 : ℕ))⁻¹) :=
      div_le_div_of_nonneg_left (by positivity) hlowpos hlower
    _ = _ := by field_simp

/-- For a fixed finite chunk alphabet and positive deviation, the explicit
conditional selection bound tends to that deviation on every lower
square-root band. In particular it applies to sequences on the corrected
C15/C19 admissible band used in `conditionedSelectedChunk_corrected`.
not counted. -/
theorem conditionedSelectedChunk_bound_tendsto
    (A : ℝ) (hA : 1 < A) (m C : ℕ) (hm : 0 < m)
    (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c) (ell : ℕ → ℕ)
    (hband : ∀ᶠ n : ℕ in Filter.atTop,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell n : ℝ)) :
    Filter.Tendsto (fun n : ℕ => δ +
      2 * Fintype.card ((Fin C → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell n / m : ℕ)) * (n : ℝ) ^ 3 / c)
      Filter.atTop (nhds δ) := by
  have hA0 : 0 < A := by linarith
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  let b : ℝ := 2 * δ ^ 2 / (A * m)
  have hb : 0 < b := by dsimp [b]; positivity
  have hsqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hraw := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 6 b hb).comp hsqrt
  have hsq (n : ℕ) : (Real.sqrt (n : ℝ)) ^ (6 : ℕ) = (n : ℝ) ^ 3 := by
    calc
      _ = ((Real.sqrt (n : ℝ)) ^ 2) ^ 3 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hbase : Filter.Tendsto (fun n : ℕ =>
      (n : ℝ) ^ 3 * Real.exp (-b * Real.sqrt (n : ℝ)))
      Filter.atTop (nhds 0) := by
    have heq : (fun x : ℝ => x ^ (6 : ℝ) * Real.exp (-b * x)) ∘
        (fun n : ℕ => Real.sqrt (n : ℝ)) =
        (fun n : ℕ => (n : ℝ) ^ 3 * Real.exp (-b * Real.sqrt (n : ℝ))) := by
      funext n
      change (Real.sqrt (n : ℝ)) ^ (6 : ℝ) * _ = _
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) from rfl, Real.rpow_natCast, hsq]
    rw [heq] at hraw
    exact hraw
  let K : ℝ := 2 * Fintype.card ((Fin C → Fin 3) × Bool) * Real.exp (2 * δ ^ 2) / c
  have hupper : Filter.Tendsto (fun n : ℕ =>
      K * ((n : ℝ) ^ 3 * Real.exp (-b * Real.sqrt (n : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hbase.const_mul K
  have herror : Filter.Tendsto (fun n : ℕ =>
      2 * Fintype.card ((Fin C → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell n / m : ℕ)) * (n : ℝ) ^ 3 / c)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) _ hupper
    filter_upwards [hband] with n hlo
    have hmod : ((ell n % m : ℕ) : ℝ) ≤ m := by
      exact_mod_cast (Nat.mod_lt (ell n) hm).le
    have hid : (m : ℝ) * ((ell n / m : ℕ) : ℝ) + ((ell n % m : ℕ) : ℝ) = ell n := by
      exact_mod_cast (Nat.div_add_mod (ell n) m)
    have hdiv : (ell n : ℝ) ≤ (m : ℝ) * (((ell n / m : ℕ) : ℝ) + 1) := by
      nlinarith only [hid, hmod]
    have hLbound : Real.sqrt (n : ℝ) / (A * m) - 1 ≤ ((ell n / m : ℕ) : ℝ) := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ (mul_pos hA0 hm0)).mpr
      calc
        Real.sqrt (n : ℝ) = A * (A⁻¹ * Real.sqrt (n : ℝ)) := by field_simp
        _ ≤ A * ((m : ℝ) * (((ell n / m : ℕ) : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (hlo.trans hdiv) hA0.le
        _ = _ := by ring
    have hexponent : -2 * δ ^ 2 * ((ell n / m : ℕ) : ℝ) ≤
        2 * δ ^ 2 + -b * Real.sqrt (n : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hLbound (show 0 ≤ 2 * δ ^ 2 by positivity)
      have heq : 2 * δ ^ 2 * (Real.sqrt (n : ℝ) / (A * m) - 1) =
          b * Real.sqrt (n : ℝ) - 2 * δ ^ 2 := by dsimp [b]; ring
      rw [heq] at hh
      linarith only [hh]
    have hexp := Real.exp_le_exp.mpr hexponent
    rw [Real.exp_add] at hexp
    calc
      _ ≤ (2 * Fintype.card ((Fin C → Fin 3) × Bool) *
          (Real.exp (2 * δ ^ 2) * Real.exp (-b * Real.sqrt (n : ℝ)))) *
          (n : ℝ) ^ 3 / c := by
        apply div_le_div_of_nonneg_right _ hc.le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)
      _ = _ := by dsimp [K]; ring
  simpa only [add_zero] using herror.const_add δ

private theorem prodUniform_real
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
  have hdis : Pairwise (Disjoint on F) := by
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

/-- Joint selected chunk and independent zero-based offset, with one band
constant uniform in the joint event. Helper for `lem-disk-walk-conv`,
The product order is `(uniform block × iid walk) × uniform offset`.
The offset is `K % m`, used as `o.val` by `decodeWindow`. This is a setwise
estimate only; no total-variation convergence conclusion is asserted. -/
theorem conditionedSelectedChunk_joint_corrected (A : ℝ) (hA : 1 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m C ell n : ℕ), 0 < m → 0 < ell / m →
      ∀ δ : ℝ, 0 < δ → 1 ≤ n →
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      ∀ B : Set (((Fin C → Fin 3) × Bool) × Fin m),
      |((((Measure.uniformOfFinset (Finset.univ : Finset (Fin (ell / m)))).prod
          iidCodeMeasure).prod
          (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
          {z | z.1.2 ∈ coneEvent (ell : ℤ) 0 n ∧
            (cappedLevelChunk m C z.1.1.val z.1.2, z.2) ∈ B}) /
          iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n) -
        ((iidCodeMeasure.map (chunk m C)).prod
          (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real B| ≤
      δ + 2 * Fintype.card ((Fin C → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c := by
  obtain ⟨c, hc, hbound⟩ := conditionedSelectedChunk_corrected A hA
  refine ⟨c, hc, ?_⟩
  intro m C ell n hm hL δ hδ hn hlo hhi hln hcong B
  have hB : MeasurableSet B := (Set.toFinite B).measurableSet
  have hchunk : Measurable
      (fun z : Fin (ell / m) × (ℕ → Fin 3) =>
        cappedLevelChunk m C z.1.val z.2) := by
    apply measurable_from_prod_countable_right
    intro s
    exact measurable_cappedLevelChunk m C s.val
  have hS : MeasurableSet
      {z : (Fin (ell / m) × (ℕ → Fin 3)) × Fin m |
        z.1.2 ∈ coneEvent (ell : ℤ) 0 n ∧
        (cappedLevelChunk m C z.1.1.val z.1.2, z.2) ∈ B} :=
    ((measurableSet_coneEvent' _ _).preimage (measurable_snd.comp measurable_fst)).inter
      (hB.preimage ((hchunk.comp measurable_fst).prodMk measurable_snd))
  have : IsProbabilityMeasure
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin (ell / m)))) := by
    constructor
    simp only [Measure.uniformOfFinset_apply, Set.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    exact ENNReal.div_self (by exact_mod_cast hL.ne') (by finiteness)
  rw [prodUniform_real _ m hm _ hS, prodUniform_real _ m hm B hB]
  let D := iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n)
  let p := fun o : Fin m =>
    (((Measure.uniformOfFinset (Finset.univ : Finset (Fin (ell / m)))).prod
      iidCodeMeasure).real {z | z.2 ∈ coneEvent (ell : ℤ) 0 n ∧
        (cappedLevelChunk m C z.1.val z.2, o) ∈ B}) / D -
      (iidCodeMeasure.map (chunk m C)).real {a | (a, o) ∈ B}
  have hid : (m : ℝ)⁻¹ * (∑ o : Fin m,
      (((Measure.uniformOfFinset (Finset.univ : Finset (Fin (ell / m)))).prod
        iidCodeMeasure).real {z | z.2 ∈ coneEvent (ell : ℤ) 0 n ∧
          (cappedLevelChunk m C z.1.val z.2, o) ∈ B})) / D -
      (m : ℝ)⁻¹ * ∑ o : Fin m,
        (iidCodeMeasure.map (chunk m C)).real {a | (a, o) ∈ B} =
      (m : ℝ)⁻¹ * ∑ o : Fin m, p o := by
    simp only [p, Finset.sum_sub_distrib, ← Finset.sum_div]
    ring
  change |(_ / D - _)| ≤ _
  simp only [Set.mem_ofPred_eq]
  rw [hid, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (m : ℝ)⁻¹)]
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ o : Fin m, |p o| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (m : ℝ)⁻¹ * ∑ _o : Fin m,
        (δ + 2 * Fintype.card ((Fin C → Fin 3) × Bool) *
          Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro o ho
      exact hbound m C ell n hm hL δ hδ hn hlo hhi hln hcong {a | (a, o) ∈ B}
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_mul]

private theorem uniformRangeProd_real
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (L : ℕ) (hL : 0 < L) (S : Set (ℕ × Ω)) (hS : MeasurableSet S) :
    ((Measure.uniformOfFinset (Finset.range L)).prod μ).real S =
      (L : ℝ)⁻¹ * ∑ k ∈ Finset.range L, μ.real {ω | (k, ω) ∈ S} := by
  let U : Measure ℕ := Measure.uniformOfFinset (Finset.range L)
  have : IsProbabilityMeasure U := by
    constructor
    simp only [U, Measure.uniformOfFinset_apply, Set.mem_univ, Finset.filter_true,
      Finset.card_range]
    exact ENNReal.div_self (by exact_mod_cast hL.ne') (by finiteness)
  let F : Fin L → Set (ℕ × Ω) := fun k =>
    {(k : ℕ)} ×ˢ {ω | ((k : ℕ), ω) ∈ S}
  have hcover : S ∩ ((↑(Finset.range L) : Set ℕ) ×ˢ Set.univ) = ⋃ k, F k := by
    ext ⟨k, ω⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Finset.mem_coe, Finset.mem_range,
      Set.mem_univ, and_true, Set.mem_iUnion, F, Set.mem_singleton_iff,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hS, hk⟩
      exact ⟨⟨k, hk⟩, rfl, hS⟩
    · rintro ⟨i, hi, hS⟩
      subst k
      exact ⟨hS, i.isLt⟩
  have hdis : Pairwise (Disjoint on F) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro ⟨k, ω⟩ ⟨hi, _⟩ ⟨hj, _⟩
    exact hij (Fin.ext (hi.symm.trans hj))
  have hmeas (k : Fin L) : MeasurableSet (F k) :=
    (measurableSet_singleton _).prod
      (hS.preimage (measurable_const.prodMk measurable_id))
  have hnull : (U.prod μ) (((↑(Finset.range L) : Set ℕ) ×ˢ Set.univ)ᶜ) = 0 := by
    rw [Set.compl_prod_eq_union, Set.compl_univ, Set.prod_empty, Set.union_empty,
      Measure.prod_prod]
    have hu : U (↑(Finset.range L) : Set ℕ)ᶜ = 0 := by
      simp [U, Measure.uniformOfFinset_apply]
    rw [hu, zero_mul]
  have hsupport : (U.prod μ).real S =
      (U.prod μ).real (S ∩ ((↑(Finset.range L) : Set ℕ) ×ˢ Set.univ)) := by
    apply measureReal_congr
    filter_upwards [ae_iff.mpr hnull] with z hz
    have hz' : z ∈ ((↑(Finset.range L) : Set ℕ) ×ˢ Set.univ) := by
      simpa only [Set.mem_compl_iff, not_not] using hz
    simp only [Set.mem_inter_iff, hz', and_true]
  have hatom (k : Fin L) : U.real {(k : ℕ)} = (L : ℝ)⁻¹ := by
    simp [U, Measure.real, Measure.uniformOfFinset_apply_singleton,
      Finset.mem_range, k.isLt, ENNReal.toReal_inv]
  change (U.prod μ).real _ = _
  rw [hsupport]
  conv_lhs => rw [hcover, measureReal_iUnion_fintype hdis hmeas]
  simp_rw [F, measureReal_prod_prod, hatom]
  rw [← Finset.mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => μ.real {ω | (k, ω) ∈ S}) L

private theorem sum_completeBlocks (m L : ℕ) (hm : 0 < m) (f : ℕ → Fin m → ℝ) :
    (∑ k ∈ Finset.range (L * m), f (k / m) ⟨k % m, Nat.mod_lt k hm⟩) =
      ∑ o : Fin m, ∑ s : Fin L, f s.val o := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => f (k / m) ⟨k % m, Nat.mod_lt k hm⟩) (L * m)]
  rw [← (finProdFinEquiv : Fin L × Fin m ≃ Fin (L * m)).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o ho
  apply Finset.sum_congr rfl
  intro s hs
  have hd : (o.val + m * s.val) / m = s.val := by
    rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt o.isLt, zero_add]
  have hr : (o.val + m * s.val) % m = o.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt o.isLt]
  change f ((o.val + m * s.val) / m) _ = _
  rw [hd]
  congr 1
  exact Fin.ext hr

private theorem weightedSetwise_bound {w r t e : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (he : 0 ≤ e) (h : |r - t| ≤ e) :
    |w * r - t| ≤ e + (1 - w) := by
  calc
    _ = |w * (r - t) + -(1 - w) * t| := by congr 1; ring
    _ ≤ |w * (r - t)| + |-(1 - w) * t| := abs_add_le _ _
    _ = w * |r - t| + (1 - w) * t := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_neg,
        abs_of_nonneg (sub_nonneg.mpr hw1), abs_of_nonneg ht0]
    _ ≤ w * e + (1 - w) * 1 := add_le_add
      (mul_le_mul_of_nonneg_left h hw0)
      (mul_le_mul_of_nonneg_left ht1 (sub_nonneg.mpr hw1))
    _ ≤ e + (1 - w) := by nlinarith only [mul_le_mul_of_nonneg_right hw1 he]

private theorem selectedJoint_eq_average
    {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [MeasurableSpace α] {X : ℕ → Ω → α} (hX : ∀ s, Measurable (X s))
    (E : Set Ω) (hE : MeasurableSet E) (m L : ℕ) (hm : 0 < m) (hL : 0 < L)
    (B : Set (α × Fin m)) (hB : MeasurableSet B) :
    (((Measure.uniformOfFinset (Finset.univ : Finset (Fin L))).prod μ).prod
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
      {z | z.1.2 ∈ E ∧ (X z.1.1.val z.1.2, z.2) ∈ B} =
      (m : ℝ)⁻¹ * (L : ℝ)⁻¹ *
        ∑ o : Fin m, ∑ s : Fin L, μ.real {ω ∈ E | (X s.val ω, o) ∈ B} := by
  have : IsProbabilityMeasure
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin L))) := by
    constructor
    simp only [Measure.uniformOfFinset_apply, Set.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    exact ENNReal.div_self (by exact_mod_cast hL.ne') (by finiteness)
  have hX' : Measurable (fun z : Fin L × Ω => X z.1.val z.2) :=
    measurable_from_prod_countable_right (fun s => hX s.val)
  have hS : MeasurableSet
      {z : (Fin L × Ω) × Fin m | z.1.2 ∈ E ∧ (X z.1.1.val z.1.2, z.2) ∈ B} :=
    (hE.preimage (measurable_snd.comp measurable_fst)).inter
      (hB.preimage ((hX'.comp measurable_fst).prodMk measurable_snd))
  rw [prodUniform_real _ m hm _ hS]
  simp only [Set.mem_ofPred_eq]
  have hs (o : Fin m) :
      (((Measure.uniformOfFinset (Finset.univ : Finset (Fin L))).prod μ).real
        {z | z.2 ∈ E ∧ (X z.1.val z.2, o) ∈ B}) =
      (L : ℝ)⁻¹ * ∑ s : Fin L, μ.real {ω ∈ E | (X s.val ω, o) ∈ B} := by
    have h := selectedProduct_eq_average (μ := μ) hX E hE {a | (a, o) ∈ B}
      (hB.preimage (measurable_id.prodMk measurable_const)) L hL
    simp only [Set.mem_ofPred_eq] at h
    rw [h]
    congr 1
    exact (Fin.sum_univ_eq_sum_range
      (fun s => μ.real {ω ∈ E | (X s ω, o) ∈ B}) L).symm
  simp_rw [hs]
  rw [← Finset.mul_sum]
  ring

/- Uniform zero-based level, restricted to the complete blocks, with the
joint chunk/offset law as target. Here `K` is uniform on `Finset.range ell`,
independent of the conditioned bridge, `s = K / m`, and `o = K % m`.
The restriction is a subprobability measure, not renormalized in `K`;
its missing terminal-block mass is at most `m / ell`. -/
theorem conditionedUniformLevelChunk_joint_corrected (A : ℝ) (hA : 1 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m C ell n : ℕ), (hm : 0 < m) → 0 < ell / m →
      ∀ δ : ℝ, 0 < δ → 1 ≤ n →
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ell : ℝ) →
      (ell : ℝ) ≤ A * Real.sqrt (n : ℝ) → ell ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) →
      ∀ B : Set (((Fin C → Fin 3) × Bool) × Fin m),
      |(((Measure.uniformOfFinset (Finset.range ell)).prod iidCodeMeasure).real
          {z | z.2 ∈ coneEvent (ell : ℤ) 0 n ∧ z.1 < m * (ell / m) ∧
            (cappedLevelChunk m C (z.1 / m) z.2,
              (⟨z.1 % m, Nat.mod_lt z.1 hm⟩ : Fin m)) ∈ B}) /
          iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n) -
        ((iidCodeMeasure.map (chunk m C)).prod
          (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real B| ≤
      δ + 2 * Fintype.card ((Fin C → Fin 3) × Bool) *
        Real.exp (-2 * δ ^ 2 * (ell / m : ℕ)) * (n : ℝ) ^ 3 / c + (m : ℝ) / ell := by
  obtain ⟨c, hc, hbound⟩ := conditionedSelectedChunk_joint_corrected A hA
  refine ⟨c, hc, ?_⟩
  intro m C ell n hm hL δ hδ hn hlo hhi hln hcong B
  have hell : 0 < ell := Nat.pos_of_ne_zero (by
    intro he
    subst ell
    simp at hL)
  have hB : MeasurableSet B := (Set.toFinite B).measurableSet
  have hE := measurableSet_coneEvent' (ell : ℤ) n
  let f : ℕ → Fin m → ℝ := fun s o =>
    iidCodeMeasure.real {ω ∈ coneEvent (ell : ℤ) 0 n |
      (cappedLevelChunk m C s ω, o) ∈ B}
  let S : Set (ℕ × (ℕ → Fin 3)) :=
    {z | z.2 ∈ coneEvent (ell : ℤ) 0 n ∧ z.1 < m * (ell / m) ∧
      (cappedLevelChunk m C (z.1 / m) z.2,
        (⟨z.1 % m, Nat.mod_lt z.1 hm⟩ : Fin m)) ∈ B}
  let J := (((Measure.uniformOfFinset (Finset.univ : Finset (Fin (ell / m)))).prod
    iidCodeMeasure).prod (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real
      {z | z.1.2 ∈ coneEvent (ell : ℤ) 0 n ∧
        (cappedLevelChunk m C z.1.1.val z.1.2, z.2) ∈ B}
  let T := ((iidCodeMeasure.map (chunk m C)).prod
    (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real B
  let D := iidCodeMeasure.real (coneEvent (ell : ℤ) 0 n)
  let w : ℝ := (m : ℝ) * ((ell / m : ℕ) : ℝ) / ell
  have hS : MeasurableSet S := by
    have hX : Measurable
        (fun z : ℕ × (ℕ → Fin 3) => cappedLevelChunk m C (z.1 / m) z.2) :=
      measurable_from_prod_countable_right
        (fun k => measurable_cappedLevelChunk m C (k / m))
    have ho : Measurable (fun z : ℕ × (ℕ → Fin 3) =>
        (⟨z.1 % m, Nat.mod_lt z.1 hm⟩ : Fin m)) :=
      (measurable_of_countable (fun k : ℕ => (⟨k % m, Nat.mod_lt k hm⟩ : Fin m))).comp
        measurable_fst
    exact (hE.preimage measurable_snd).inter
      (((measurableSet_lt measurable_id measurable_const).preimage measurable_fst).inter
        (hB.preimage (hX.prodMk ho)))
  have hpell : (ell / m) * m ≤ ell := Nat.div_mul_le_self ell m
  have hsum : (∑ k ∈ Finset.range ell,
      iidCodeMeasure.real {ω | (k, ω) ∈ S}) =
      ∑ k ∈ Finset.range ((ell / m) * m), f (k / m) ⟨k % m, Nat.mod_lt k hm⟩ := by
    have ht := Finset.sum_subset (s₁ := Finset.range ((ell / m) * m))
      (s₂ := Finset.range ell) (f := fun k => iidCodeMeasure.real {ω | (k, ω) ∈ S})
      (Finset.range_mono hpell) (by
        intro k hk hnot
        have hnot' : ¬ k < m * (ell / m) := by simpa [Nat.mul_comm] using hnot
        simp [S, hnot'])
    rw [← ht]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < m * (ell / m) := by simpa [Nat.mul_comm] using hk
    simp only [S, Set.mem_ofPred_eq, hk', true_and, f]
  have hJ : J = (m : ℝ)⁻¹ * ((ell / m : ℕ) : ℝ)⁻¹ *
      ∑ o : Fin m, ∑ s : Fin (ell / m), f s.val o := by
    exact selectedJoint_eq_average (measurable_cappedLevelChunk m C)
      _ hE m (ell / m) hm hL B hB
  have hselection :
      (((Measure.uniformOfFinset (Finset.range ell)).prod iidCodeMeasure).real S) = w * J := by
    rw [uniformRangeProd_real _ ell hell S hS, hsum, sum_completeBlocks m (ell / m) hm f, hJ]
    dsimp [w]
    field_simp
  have hdeviation := hbound m C ell n hm hL δ hδ hn hlo hhi hln hcong B
  change |J / D - T| ≤ _ at hdeviation
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by
    apply (div_le_iff₀ (by exact_mod_cast hell : 0 < (ell : ℝ))).mpr
    simpa [mul_comm] using (show (((ell / m) * m : ℕ) : ℝ) ≤ ell by exact_mod_cast hpell)
  have : IsProbabilityMeasure
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin m))) := by
    constructor
    simp only [Measure.uniformOfFinset_apply, Set.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    exact ENNReal.div_self (by exact_mod_cast hm.ne') (by finiteness)
  have ht0 : 0 ≤ T := measureReal_nonneg
  have ht1 : T ≤ 1 := by
    calc
      T ≤ ((iidCodeMeasure.map (chunk m C)).prod
          (Measure.uniformOfFinset (Finset.univ : Finset (Fin m)))).real Set.univ :=
        measureReal_mono (Set.subset_univ B)
      _ = 1 := by simp
  have htail : 1 - w ≤ (m : ℝ) / ell := by
    have hid : (m : ℝ) * ((ell / m : ℕ) : ℝ) + ((ell % m : ℕ) : ℝ) = ell := by
      exact_mod_cast Nat.div_add_mod ell m
    have hmod : ((ell % m : ℕ) : ℝ) ≤ m := by exact_mod_cast (Nat.mod_lt ell hm).le
    dsimp [w]
    apply (le_div_iff₀ (by exact_mod_cast hell : 0 < (ell : ℝ))).mpr
    rw [sub_mul, div_mul_cancel₀ _ (by exact_mod_cast hell.ne'), one_mul]
    linarith only [hid, hmod]
  change |(_ / D - T)| ≤ _
  change |((((Measure.uniformOfFinset (Finset.range ell)).prod iidCodeMeasure).real S) / D - T)| ≤ _
  rw [hselection, mul_div_assoc]
  exact (weightedSetwise_bound hw0 hw1 ht0 ht1 (by positivity) hdeviation).trans
    (add_le_add le_rfl htail)

end
end DirectedDistances.RandomWalk
