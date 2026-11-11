module

public import DirectedDistances.Probability.HeavyTailMaximal

/-! # Two-sided fluctuation bound for heavy-tailed walks

Helper for `lem-ldp-fluctuation` and `lem-sdp-fluctuation`
not a paper result.  The increments `xi k` are independent, identically distributed for `k ≥ 1`
and for `k ≤ 0` (Theorem `busemann-property`), and the two-sided walk `X` satisfies
`X k - X (k - 1) = xi k`. -/

public section
namespace DirectedDistances.Probability
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Two-sided walk with increments `xi`: `X l = ∑ j ∈ (0, l], xi j` for `l ≥ 0` and
`X l = -∑ j ∈ (l, 0], xi j` for `l < 0`, so that `X k - X (k - 1) = xi k`. -/
@[expose] noncomputable def twoSidedWalk (xi : ℤ → Ω → ℝ) (l : ℤ) (ω : Ω) : ℝ :=
  if 0 ≤ l then ∑ j ∈ Finset.Ioc 0 l, xi j ω else -∑ j ∈ Finset.Ioc l 0, xi j ω

omit mΩ in
private lemma sum_Ioc_pos (xi : ℤ → Ω → ℝ) (ω : Ω) (j : ℕ) :
    ∑ i ∈ Finset.range j, xi ((i : ℤ) + 1) ω = ∑ x ∈ Finset.Ioc (0 : ℤ) j, xi x ω := by
  have hinj : Function.Injective (fun i : ℕ => (i : ℤ) + 1) := fun a b h => by
    simpa using h
  have : Finset.Ioc (0 : ℤ) j = (Finset.range j).map ⟨fun i : ℕ => (i : ℤ) + 1, hinj⟩ := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(x - 1).toNat, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [this, Finset.sum_map]
  rfl

omit mΩ in
private lemma sum_Ioc_neg (xi : ℤ → Ω → ℝ) (ω : Ω) (m : ℕ) :
    ∑ i ∈ Finset.range m, xi (-(i : ℤ)) ω = ∑ x ∈ Finset.Ioc (-(m : ℤ)) 0, xi x ω := by
  have hinj : Function.Injective (fun i : ℕ => -(i : ℤ)) := fun a b h => by
    simpa using h
  have : Finset.Ioc (-(m : ℤ)) 0 = (Finset.range m).map ⟨fun i : ℕ => -(i : ℤ), hinj⟩ := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(-x).toNat, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [this, Finset.sum_map]
  rfl

/-- Two-sided fluctuation bound for walks with independent increments that are identically
distributed for `k ≥ 1` and for `k ≤ 0`, with power-law tails of the same index
`alpha ∈ (0, 2)`: `P[∃ l ∈ [-k, k], A k ^ (1 / alpha) < |X l|] ≤ C' A ^ (-alpha)`.

Helper for `lem-ldp-fluctuation` and `lem-sdp-fluctuation`
not a paper result. -/
theorem twoSidedWalk_fluctuation {P : Measure Ω} [IsProbabilityMeasure P]
    {xi : ℤ → Ω → ℝ} (hmeas : ∀ k, Measurable (xi k)) (hind : iIndepFun xi P)
    (hidPos : ∀ k : ℤ, 1 ≤ k → IdentDistrib (xi k) (xi 1) P P)
    (hidNeg : ∀ k : ℤ, k ≤ 0 → IdentDistrib (xi k) (xi 0) P P)
    (alpha Cp Cn : ℝ) (ha0 : 0 < alpha) (ha2 : alpha < 2) (hCp : 0 < Cp) (hCn : 0 < Cn)
    (htailPos : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |xi 1 ω|} ≤ Cp * x ^ (-alpha))
    (htailNeg : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |xi 0 ω|} ≤ Cn * x ^ (-alpha))
    (hcenterPos : (∀ t : ℝ, 0 ≤ t →
        ∫ ω, Set.indicator {ω | |xi 1 ω| ≤ t} (xi 1) ω ∂P = 0) ∨
      (1 < alpha ∧ Integrable (xi 1) P ∧ ∫ ω, xi 1 ω ∂P = 0))
    (hcenterNeg : (∀ t : ℝ, 0 ≤ t →
        ∫ ω, Set.indicator {ω | |xi 0 ω| ≤ t} (xi 0) ω ∂P = 0) ∨
      (1 < alpha ∧ Integrable (xi 0) P ∧ ∫ ω, xi 0 ω ∂P = 0)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 ≤ A →
      P.real {ω | ∃ l : ℤ, -(k : ℤ) ≤ l ∧ l ≤ k ∧
        A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|} ≤ C' * A ^ (-alpha) := by
  have hinjP : Function.Injective (fun i : ℕ => (i : ℤ) + 1) := fun a b h => by
    simpa using h
  have hinjN : Function.Injective (fun i : ℕ => -(i : ℤ)) := fun a b h => by
    simpa using h
  obtain ⟨Cp', hCp', hP⟩ := heavyTail_maximal (P := P)
    (xi := fun (i : ℕ) => xi ((i : ℤ) + 1)) (fun i => hmeas _) (hind.precomp hinjP)
    (fun i => by
      simpa using hidPos ((i : ℤ) + 1) (by omega))
    alpha Cp ha0 ha2 hCp (by simpa using htailPos)
    (by simpa using hcenterPos)
  obtain ⟨Cn', hCn', hN⟩ := heavyTail_maximal (P := P)
    (xi := fun (i : ℕ) => xi (-(i : ℤ))) (fun i => hmeas _) (hind.precomp hinjN)
    (fun i => by
      simpa using hidNeg (-(i : ℤ)) (by omega))
    alpha Cn ha0 ha2 hCn (by simpa using htailNeg)
    (by simpa using hcenterNeg)
  refine ⟨Cp' + Cn', by positivity, ?_⟩
  intro k hk A hA
  have hsub : {ω | ∃ l : ℤ, -(k : ℤ) ≤ l ∧ l ≤ k ∧
        A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|} ⊆
      {ω | ∃ j ≤ k, A * (k : ℝ) ^ (1 / alpha) <
          |∑ i ∈ Finset.range j, xi ((i : ℤ) + 1) ω|} ∪
        {ω | ∃ j ≤ k, A * (k : ℝ) ^ (1 / alpha) <
          |∑ i ∈ Finset.range j, xi (-(i : ℤ)) ω|} := by
    rintro ω ⟨l, hl1, hl2, hl⟩
    by_cases h0 : 0 ≤ l
    · left
      refine ⟨l.toNat, by omega, ?_⟩
      rw [sum_Ioc_pos, Int.toNat_of_nonneg h0]
      simpa [twoSidedWalk, h0] using hl
    · right
      refine ⟨(-l).toNat, by omega, ?_⟩
      rw [sum_Ioc_neg, Int.toNat_of_nonneg (by omega), neg_neg]
      simpa [twoSidedWalk, h0] using hl
  calc P.real {ω | ∃ l : ℤ, -(k : ℤ) ≤ l ∧ l ≤ k ∧
        A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|}
      ≤ P.real ({ω | ∃ j ≤ k, A * (k : ℝ) ^ (1 / alpha) <
          |∑ i ∈ Finset.range j, xi ((i : ℤ) + 1) ω|} ∪
        {ω | ∃ j ≤ k, A * (k : ℝ) ^ (1 / alpha) <
          |∑ i ∈ Finset.range j, xi (-(i : ℤ)) ω|}) := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ Cp' * A ^ (-alpha) + Cn' * A ^ (-alpha) := add_le_add (hP k hk A hA) (hN k hk A hA)
    _ = (Cp' + Cn') * A ^ (-alpha) := by ring

/-- Corollary in the source's form: with probability at least `1 - C' A ^ (-alpha)`, the walk
satisfies `max_{|l| ≤ k} |X l| ≤ A k ^ (1 / alpha)`, so this probability tends to `1` as
`A → ∞` uniformly in `k`.

Helper for `lem-ldp-fluctuation` and `lem-sdp-fluctuation`
not a paper result. -/
theorem twoSidedWalk_max_le {P : Measure Ω} [IsProbabilityMeasure P]
    {xi : ℤ → Ω → ℝ} (hmeas : ∀ k, Measurable (xi k)) (hind : iIndepFun xi P)
    (hidPos : ∀ k : ℤ, 1 ≤ k → IdentDistrib (xi k) (xi 1) P P)
    (hidNeg : ∀ k : ℤ, k ≤ 0 → IdentDistrib (xi k) (xi 0) P P)
    (alpha Cp Cn : ℝ) (ha0 : 0 < alpha) (ha2 : alpha < 2) (hCp : 0 < Cp) (hCn : 0 < Cn)
    (htailPos : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |xi 1 ω|} ≤ Cp * x ^ (-alpha))
    (htailNeg : ∀ x : ℝ, 1 ≤ x → P.real {ω | x < |xi 0 ω|} ≤ Cn * x ^ (-alpha))
    (hcenterPos : (∀ t : ℝ, 0 ≤ t →
        ∫ ω, Set.indicator {ω | |xi 1 ω| ≤ t} (xi 1) ω ∂P = 0) ∨
      (1 < alpha ∧ Integrable (xi 1) P ∧ ∫ ω, xi 1 ω ∂P = 0))
    (hcenterNeg : (∀ t : ℝ, 0 ≤ t →
        ∫ ω, Set.indicator {ω | |xi 0 ω| ≤ t} (xi 0) ω ∂P = 0) ∨
      (1 < alpha ∧ Integrable (xi 0) P ∧ ∫ ω, xi 0 ω ∂P = 0)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, 1 ≤ A →
      1 - C' * A ^ (-alpha) ≤ P.real {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
        |twoSidedWalk xi l ω| ≤ A * (k : ℝ) ^ (1 / alpha)} := by
  obtain ⟨C', hC', h⟩ := twoSidedWalk_fluctuation hmeas hind hidPos hidNeg alpha Cp Cn ha0 ha2
    hCp hCn htailPos htailNeg hcenterPos hcenterNeg
  refine ⟨C', hC', fun k hk A hA => ?_⟩
  have hcompl : {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
        |twoSidedWalk xi l ω| ≤ A * (k : ℝ) ^ (1 / alpha)} =
      {ω | ∃ l : ℤ, -(k : ℤ) ≤ l ∧ l ≤ k ∧
        A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_and, not_lt]
  have hmeasE : MeasurableSet {ω | ∃ l : ℤ, -(k : ℤ) ≤ l ∧ l ≤ k ∧
        A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|} := by
    have hX : ∀ l : ℤ, Measurable fun ω => twoSidedWalk xi l ω := by
      intro l
      unfold twoSidedWalk
      split_ifs
      · exact Finset.measurable_sum _ fun j _ => hmeas j
      · exact (Finset.measurable_sum _ fun j _ => hmeas j).neg
    have : {ω | ∃ l : ℤ, -(k : ℤ) ≤ l ∧ l ≤ k ∧
        A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|} =
        ⋃ l ∈ Finset.Icc (-(k : ℤ)) k,
          {ω | A * (k : ℝ) ^ (1 / alpha) < |twoSidedWalk xi l ω|} := by
      ext ω
      simp [Finset.mem_Icc, and_assoc]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun l _ =>
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX l))
  rw [hcompl, measureReal_compl hmeasE]
  have := h k hk A hA
  have hu : P.real Set.univ = 1 := by simp
  linarith

end DirectedDistances.Probability
