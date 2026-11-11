/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.CappedLevelChunks
public import DirectedDistances.RandomWalk.HittingTightness
public import DirectedDistances.RandomWalk.IIDCodeRelabel

/-! # Truncation and window containment

Helpers for the truncation and window-containment estimates in -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem fst_hit_overflow_iff_survival (m N : ℕ) (hm : 0 < m)
    (ω : ℕ → Fin 3) :
    (N : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω ↔
      ∀ n ≤ N, -(m : ℤ) < (codeWalk ω n).1 := by
  classical
  have hstep (k : ℕ) : (codeWalk ω k).1 - 1 ≤ (codeWalk ω (k + 1)).1 := by
    have hs := congrArg Prod.fst (codeWalk_succ_sub ω k)
    rw [Prod.fst_sub] at hs
    have hlow : -1 ≤ (lazyTwoDimensionalStep (ω (k + 1))).1 := by
      generalize ω (k + 1) = c
      fin_cases c <;> decide
    omega
  by_cases hex : ∃ n, (codeWalk ω n).1 = -(m : ℤ)
  · have hτ : codeFstFirstHit (-(m : ℤ)) ω = (Nat.find hex : ℕ∞) := by
      simp [codeFstFirstHit, hex]
    rw [hτ]
    constructor
    · intro h n hn
      have hNat : N < Nat.find hex := by exact_mod_cast h
      have hall : ∀ k ≤ N, -(m : ℤ) < (codeWalk ω k).1 := by
        intro k hk
        induction k with
        | zero => simp [codeWalk_zero]; omega
        | succ k ih =>
          have hp := ih (by omega)
          have hsn := hstep k
          have hnot' : (codeWalk ω (k + 1)).1 ≠ -(m : ℤ) :=
            Nat.find_min hex (by omega : k + 1 < Nat.find hex)
          have hge : -(m : ℤ) ≤ (codeWalk ω (k + 1)).1 := by omega
          omega
      exact hall n hn
    · intro h
      have hfind : N < Nat.find hex := by
        by_contra hn
        have hle : Nat.find hex ≤ N := Nat.le_of_not_gt hn
        have hhit := Nat.find_spec hex
        have hbad := h (Nat.find hex) hle
        omega
      exact_mod_cast hfind
  · have hτ : codeFstFirstHit (-(m : ℤ)) ω = ⊤ := by
      simp [codeFstFirstHit, hex]
    rw [hτ]
    constructor
    · intro _ n hn
      have hall : ∀ k ≤ N, -(m : ℤ) < (codeWalk ω k).1 := by
        intro k hk
        induction k with
        | zero => simp [codeWalk_zero]; omega
        | succ k ih =>
          have hp := ih (by omega)
          have hn' : (codeWalk ω (k + 1)).1 ≠ -(m : ℤ) :=
            fun heq => hex ⟨k + 1, heq⟩
          have hstep' := hstep k
          have hge : -(m : ℤ) ≤ (codeWalk ω (k + 1)).1 := by omega
          omega
      exact hall n hn
    · intro _
      simp

private theorem relabel_fst_survival_iff_snd (m N : ℕ) (hm : 0 < m) :
    codeRelabel ⁻¹' {ω | (N : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} =
      {ω | ∀ n ≤ N, -(m : ℤ) < (codeWalk ω n).2} := by
  ext ω
  change ((N : ℕ∞) < codeFstFirstHit (-(m : ℤ)) (codeRelabel ω)) ↔
    ∀ n ≤ N, -(m : ℤ) < (codeWalk ω n).2
  rw [fst_hit_overflow_iff_survival m N hm]
  constructor
  · intro h n hn
    have h' := h n hn
    rw [codeWalk_codeRelabel ω n] at h'
    simpa [stepRotate] using h'
  · intro h n hn
    have h' := h n hn
    rw [codeWalk_codeRelabel ω n]
    simpa [stepRotate] using h'

private theorem measurableSet_fst_hit_overflow (m N : ℕ) (hm : 0 < m) :
    MeasurableSet {ω | (N : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} := by
  rw [show {ω | (N : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} =
      {ω | ∀ n : {k : ℕ // k ≤ N}, -(m : ℤ) < (codeWalk ω n.val).1} by
        ext ω
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h n
          exact (fst_hit_overflow_iff_survival m N hm ω).mp h n.val n.property
        · intro h
          exact (fst_hit_overflow_iff_survival m N hm ω).mpr
            (fun k hk => h ⟨k, hk⟩)]
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun n =>
    measurableSet_lt measurable_const
      (((measurable_pi_apply n.val).comp measurable_codeWalk).fst)

/-- First-coordinate cap overflow has the lazy-survival bound after rotating
This is for the unconditioned iid walk; it is to be transferred to the bridge
through the selected-chunk law, not by dividing by `P[E]`. Helper; not counted
as a paper result. -/
theorem iidCodeMeasure_real_fstHit_overflow_bound (m : ℕ) (hm : 1 ≤ m) :
    iidCodeMeasure.real {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} ≤
      1 / ((m : ℝ) + 1) +
        (3 / 2 : ℝ) * ((m : ℝ) ^ 2 + 1) ^ 2 / (m : ℝ) ^ 100 := by
  have hmpos : 0 < m := by omega
  let N := m ^ 100
  have hsurv : iidCodeMeasure.real
      {ω | (N : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} =
      iidCodeMeasure.real {ω | ∀ n ≤ N, -(m : ℤ) < (codeWalk ω n).2} := by
    have hh := map_measureReal_apply (μ := iidCodeMeasure) measurable_codeRelabel
      (measurableSet_fst_hit_overflow m N hmpos)
    rw [map_codeRelabel] at hh
    rw [relabel_fst_survival_iff_snd m N hmpos] at hh
    exact hh
  have hbound := lazy_survival_bound m (m ^ 2) N hmpos (by nlinarith) (by positivity)
  rw [← hsurv] at hbound
  have halg : (m : ℝ) / ((m : ℝ) + (m : ℝ) ^ 2) = 1 / ((m : ℝ) + 1) := by
    have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
    field_simp
    <;> ring
  have hbound' : iidCodeMeasure.real
      {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} ≤
      (m : ℝ) / ((m : ℝ) + (m : ℝ) ^ 2) +
        (3 / 2 : ℝ) * ((m : ℝ) ^ 2 + 1) ^ 2 / (m : ℝ) ^ 100 := by
    simpa [N, Nat.cast_pow] using hbound
  calc
    iidCodeMeasure.real {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} ≤
        (m : ℝ) / ((m : ℝ) + (m : ℝ) ^ 2) +
          (3 / 2 : ℝ) * ((m : ℝ) ^ 2 + 1) ^ 2 / (m : ℝ) ^ 100 := hbound'
    _ = 1 / ((m : ℝ) + 1) +
        (3 / 2 : ℝ) * ((m : ℝ) ^ 2 + 1) ^ 2 / (m : ℝ) ^ 100 := by rw [halg]

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

/-- The first-coordinate cap-overflow probabilities vanish as the level grows
iid walk; to be transferred to the bridge through the selected-chunk law, not
by dividing by `P[E]`. Helper; not counted as a paper result. -/
theorem exists_fstHit_overflow_eventually_small (ε : ℝ) (hε : 0 < ε) :
    ∃ m₀, ∀ (m : ℕ), m ≥ m₀ →
      iidCodeMeasure.real
        {ω | (m ^ 100 : ℕ∞) < codeFstFirstHit (-(m : ℤ)) ω} ≤ ε := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (7 / ε)
  refine ⟨m₀, fun m hm => ?_⟩
  have hm₀m : (m₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : 1 ≤ m := by
    have hpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (lt_trans (by positivity) hm₀) hm₀m
    exact_mod_cast hpos
  have hsmall : 7 / (m : ℝ) ≤ ε := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ))).2
    have hmul : 7 < ε * (m₀ : ℝ) := by
      have hmul' := (div_lt_iff₀ hε).mp hm₀
      nlinarith [hmul']
    nlinarith [hmul, mul_nonneg hε.le (sub_nonneg.mpr hm₀m)]
  exact (iidCodeMeasure_real_fstHit_overflow_bound m hmpos).trans
    ((overflow_rhs_le_seven_div m hmpos).trans hsmall)

/-- The infinite code stream represented by a finite chunk, with the dummy
time-zero code and zero padding after the cap (`lem-disk-walk-conv`,
result. -/
@[expose] def decodedChunkCodes (C : ℕ) (c : Fin C → Fin 3) : ℕ → Fin 3 :=
  fun i => if hi : i = 0 then 0 else if hC : i ≤ C then c ⟨i - 1, by omega⟩ else 0

/-- Decode a centered window from a capped code chunk and its level offset.
The zero output for an offset beyond the chunk's `m` levels makes this a total
function on the stated domain (`lem-disk-walk-conv`,
`s = k / m` at offset `o = k % m`. The completion bit `x.2` is not consulted,
so the decoded window is the true window only when `x.2 = true`
(`ae_cappedLevelChunk_decodeWindow`). Helper; not counted as a paper
result. -/
@[expose] noncomputable def decodeWindow (N m C : ℕ)
    (x : (Fin C → Fin 3) × Bool) (o : ℕ) : Fin (2 * N + 1) → ℤ × ℤ :=
  if o ≤ m then
    let η := decodedChunkCodes C x.1
    let τ := (codeFstFirstHit (-(o : ℤ)) η).toNat
    fun j => codeWalk η (τ + j.val - N) - codeWalk η τ
  else fun _ => (0, 0)

/-- The decoder is measurable in its finite chunk argument
counted as a paper result. -/
theorem measurable_decodeWindow (N m C : ℕ) :
    Measurable (decodeWindow N m C) := by
  exact Measurable.of_discrete

/-- For a uniform level in `1..ℓ`, the number of levels either within `N`
of a block boundary (using the offset `K % m`) or in the incomplete final
block is at most `2N (⌊ℓ/m⌋ + 1) + m` (`lem-disk-walk-conv`,
blocks is exactly `N ≤ o ∧ o + N ≤ m` with `o = K % m`; it is empty when
`N ≥ m`. Helper; not counted as a paper result. -/
theorem blockBoundaryCount_le (N m ℓ : ℕ) (hm : 1 ≤ m) :
    ((Finset.Icc 1 ℓ).filter fun k =>
      k % m < N ∨ m - N < k % m ∨ m * (ℓ / m) < k).card ≤
        2 * N * (ℓ / m + 1) + m := by
  classical
  let badOffsets := (Finset.range m).filter fun o => o < N ∨ m - N < o
  let leftOffsets := (Finset.range m).filter fun o => o < N
  let rightOffsets := (Finset.range m).filter fun o => m - N < o
  have hmpos : 0 < m := by omega
  have hleft : leftOffsets.card ≤ N := by
    calc
      leftOffsets.card ≤ (Finset.range N).card := by
        apply Finset.card_le_card
        intro o ho
        simp only [leftOffsets, Finset.mem_filter, Finset.mem_range] at ho ⊢
        exact ho.2
      _ = N := Finset.card_range _
  have hright : rightOffsets.card ≤ N := by
    calc
      rightOffsets.card ≤ (Finset.range N).card := by
        apply Finset.card_le_card_of_injOn (fun o => m - 1 - o)
        · intro o ho
          change o ∈ (Finset.range m).filter (fun o => m - N < o) at ho
          have hoF := Finset.mem_filter.mp ho
          have hobound : o < m := Finset.mem_range.mp hoF.1
          change m - 1 - o ∈ Finset.range N
          by_cases hNm : N < m
          · have hsub : m - N + N = m := Nat.sub_add_cancel (Nat.le_of_lt hNm)
            have hominus : m - N ≤ o := Nat.le_of_lt hoF.2
            have hmain : m ≤ N + o := by
              calc
                m = m - N + N := hsub.symm
                _ ≤ o + N := Nat.add_le_add_right hominus N
                _ = N + o := Nat.add_comm _ _
            have hNpos : 1 ≤ N := by omega
            have hsmall : m - 1 - o + 1 ≤ N := by omega
            exact Finset.mem_range.mpr (Nat.lt_of_succ_le hsmall)
          · have hmn : m ≤ N := by omega
            have hlt : m - 1 - o < m :=
              (Nat.sub_le _ _).trans_lt (Nat.sub_lt (by omega) (by decide))
            exact Finset.mem_range.mpr (hlt.trans_le hmn)
        · intro a ha b hb hab
          change a ∈ (Finset.range m).filter (fun o => m - N < o) at ha
          change b ∈ (Finset.range m).filter (fun o => m - N < o) at hb
          have haF := Finset.mem_filter.mp ha
          have hbF := Finset.mem_filter.mp hb
          have habound : a < m := Finset.mem_range.mp haF.1
          have hbbound : b < m := Finset.mem_range.mp hbF.1
          change m - 1 - a = m - 1 - b at hab
          exact (tsub_right_inj (by omega) (by omega)).mp hab
      _ = N := Finset.card_range _
  have hbadOffsetsEq : badOffsets = leftOffsets ∪ rightOffsets := by
    ext o
    simp [badOffsets, leftOffsets, rightOffsets, Finset.filter_or]
  have hbadOffsets : badOffsets.card ≤ 2 * N := by
    rw [hbadOffsetsEq]
    calc
      (leftOffsets ∪ rightOffsets).card ≤ leftOffsets.card + rightOffsets.card :=
        Finset.card_union_le _ _
      _ ≤ N + N := Nat.add_le_add hleft hright
      _ = 2 * N := by omega
  let near := (Finset.Icc 1 ℓ).filter fun k => k % m < N ∨ m - N < k % m
  let target := (Finset.range (ℓ / m + 1)) ×ˢ badOffsets
  have hnear : near.card ≤ (ℓ / m + 1) * (2 * N) := by
    have hinj : near.card ≤ target.card := by
      apply Finset.card_le_card_of_injOn (fun k => (k / m, k % m))
      · intro k hk
        change k ∈ (Finset.Icc 1 ℓ).filter
          (fun k => k % m < N ∨ m - N < k % m) at hk
        rw [Finset.mem_filter] at hk
        have hkbounds : 1 ≤ k ∧ k ≤ ℓ := Finset.mem_Icc.mp hk.1
        change (k / m, k % m) ∈ target
        simp only [target, Finset.mem_product]
        constructor
        · exact Finset.mem_range.mpr
            (Nat.lt_succ_of_le (Nat.div_le_div_right hkbounds.2))
        · change k % m ∈ badOffsets
          simp only [badOffsets, Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.mod_lt k hmpos, hk.2⟩
      · intro a ha b hb hab
        change a ∈ (Finset.Icc 1 ℓ).filter
          (fun k => k % m < N ∨ m - N < k % m) at ha
        change b ∈ (Finset.Icc 1 ℓ).filter
          (fun k => k % m < N ∨ m - N < k % m) at hb
        rw [Finset.mem_filter] at ha hb
        change (a / m, a % m) = (b / m, b % m) at hab
        have hq : a / m = b / m := by simpa using congrArg Prod.fst hab
        have hr : a % m = b % m := by simpa using congrArg Prod.snd hab
        calc
          a = a % m + m * (a / m) := (Nat.mod_add_div a m).symm
          _ = b % m + m * (b / m) := by rw [hr, hq]
          _ = b := Nat.mod_add_div b m
    rw [Finset.card_product, Finset.card_range] at hinj
    exact hinj.trans (Nat.mul_le_mul_left _ hbadOffsets)
  have htail :
      ((Finset.Icc 1 ℓ).filter fun k => m * (ℓ / m) < k).card ≤ m := by
    calc
      ((Finset.Icc 1 ℓ).filter fun k => m * (ℓ / m) < k).card ≤
          (Finset.range m).card := by
            apply Finset.card_le_card_of_injOn (fun k => k % m)
            · intro k hk
              change k ∈ (Finset.Icc 1 ℓ).filter
                (fun k => m * (ℓ / m) < k) at hk
              rw [Finset.mem_filter] at hk
              change k % m ∈ Finset.range m
              exact Finset.mem_range.mpr (Nat.mod_lt k hmpos)
            · intro a ha b hb hab
              change a ∈ (Finset.Icc 1 ℓ).filter
                (fun k => m * (ℓ / m) < k) at ha
              change b ∈ (Finset.Icc 1 ℓ).filter
                (fun k => m * (ℓ / m) < k) at hb
              rw [Finset.mem_filter] at ha hb
              change a % m = b % m at hab
              have habounds : 1 ≤ a ∧ a ≤ ℓ := Finset.mem_Icc.mp ha.1
              have hbbounds : 1 ≤ b ∧ b ≤ ℓ := Finset.mem_Icc.mp hb.1
              have haQ : ℓ / m ≤ a / m := by
                apply (Nat.le_div_iff_mul_le hmpos).2
                nlinarith [ha.2]
              have hbQ : ℓ / m ≤ b / m := by
                apply (Nat.le_div_iff_mul_le hmpos).2
                nlinarith [hb.2]
              have hqa : a / m = ℓ / m :=
                le_antisymm (Nat.div_le_div_right habounds.2) haQ
              have hqb : b / m = ℓ / m :=
                le_antisymm (Nat.div_le_div_right hbbounds.2) hbQ
              calc
                a = a % m + m * (a / m) := (Nat.mod_add_div a m).symm
                _ = b % m + m * (b / m) := by rw [hab, hqa, hqb]
                _ = b := Nat.mod_add_div b m
      _ = m := Finset.card_range _
  have hsplit :
      (Finset.Icc 1 ℓ).filter (fun k =>
        k % m < N ∨ m - N < k % m ∨ m * (ℓ / m) < k) =
      near ∪ (Finset.Icc 1 ℓ).filter (fun k => m * (ℓ / m) < k) := by
    ext k
    simp only [near, Finset.mem_filter, Finset.mem_union]
    tauto
  rw [hsplit]
  calc
    (near ∪ (Finset.Icc 1 ℓ).filter fun k => m * (ℓ / m) < k).card ≤
        near.card + ((Finset.Icc 1 ℓ).filter fun k => m * (ℓ / m) < k).card :=
      Finset.card_union_le _ _
    _ ≤
        (ℓ / m + 1) * (2 * N) + m := Nat.add_le_add hnear htail
    _ = 2 * N * (ℓ / m + 1) + m := by ring

/-- Uniform choice from `1..ℓ` gives the boundary probability bound obtained
from `blockBoundaryCount_le` (`lem-disk-walk-conv`,
identifies it with the uniform law on `Finset.Icc 1 ℓ`. Helper; not counted as
a paper result. -/
theorem blockBoundaryUniform_probability_le (N m ℓ : ℕ)
    (hm : 1 ≤ m) (hℓ : 1 ≤ ℓ) :
    (((Finset.Icc 1 ℓ).filter fun k =>
      k % m < N ∨ m - N < k % m ∨ m * (ℓ / m) < k).card : ℝ) / ℓ ≤
        2 * N / m + (2 * N + m) / ℓ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hcount := blockBoundaryCount_le N m ℓ hm
  have hcountR' :
      (((Finset.Icc 1 ℓ).filter fun k =>
        k % m < N ∨ m - N < k % m ∨ m * (ℓ / m) < k).card : ℝ) ≤
        2 * (N : ℝ) * (((ℓ / m : ℕ) : ℝ) + 1) + m := by
    exact_mod_cast hcount
  have hfloor : ((ℓ / m : ℕ) : ℝ) * (m : ℝ) ≤ ℓ := by
    exact_mod_cast (Nat.div_mul_le_self ℓ m)
  have hquot : ((ℓ / m : ℕ) : ℝ) / ℓ ≤ 1 / m := by
    apply (div_le_div_iff₀ hℓR hmR).2
    simpa using hfloor
  have htwoN : (0 : ℝ) ≤ 2 * N := by positivity
  calc
    (((Finset.Icc 1 ℓ).filter fun k =>
      k % m < N ∨ m - N < k % m ∨ m * (ℓ / m) < k).card : ℝ) / ℓ ≤
        (2 * (N : ℝ) * (((ℓ / m : ℕ) : ℝ) + 1) + m) / ℓ :=
          (div_le_div_iff_of_pos_right hℓR).2 hcountR'
    _ = 2 * N * (((ℓ / m : ℕ) : ℝ) / ℓ + 1 / ℓ) + m / ℓ := by ring
    _ ≤ 2 * N * (1 / m + 1 / ℓ) + m / ℓ := by
      nlinarith [mul_le_mul_of_nonneg_left
        (add_le_add_right hquot (1 / ℓ)) htwoN]
    _ = 2 * N / m + (2 * N + m) / ℓ := by ring

private theorem codeWalk_fst_ge_neg_time (ω : ℕ → Fin 3) (n : ℕ) :
    -(n : ℤ) ≤ (codeWalk ω n).1 := by
  induction n with
  | zero => simp [codeWalk_zero]
  | succ n ih =>
    have hs := congrArg Prod.fst (codeWalk_succ_sub ω n)
    rw [Prod.fst_sub] at hs
    have hstep : -1 ≤ (lazyTwoDimensionalStep (ω (n + 1))).1 := by
      generalize ω (n + 1) = c
      fin_cases c <;> decide
    omega

private theorem codeFstFirstHit_level_le_toNat (d : ℕ) (ω : ℕ → Fin 3)
    (hfin : codeFstFirstHit (-(d : ℤ)) ω < ⊤) :
    d ≤ (codeFstFirstHit (-(d : ℤ)) ω).toNat := by
  classical
  have hhit : ∃ n, (codeWalk ω n).1 = -(d : ℤ) := by
    by_contra hn
    have htop : codeFstFirstHit (-(d : ℤ)) ω = ⊤ := by
      simp [codeFstFirstHit, hn]
    rw [htop] at hfin
    simp at hfin
  let t := Nat.find hhit
  have htime : codeFstFirstHit (-(d : ℤ)) ω = (t : ℕ∞) := by
    simp [codeFstFirstHit, hhit, t]
  have htoNat : (codeFstFirstHit (-(d : ℤ)) ω).toNat = t := by
    rw [htime]
    rfl
  rw [htoNat]
  have hlow := codeWalk_fst_ge_neg_time ω t
  rw [Nat.find_spec hhit] at hlow
  omega

private theorem codeWalk_eq_of_code_prefix (p q : ℕ → Fin 3) (T : ℕ)
    (hcodes : ∀ i ≤ T, p i = q i) :
    ∀ n ≤ T, codeWalk p n = codeWalk q n := by
  intro n hn
  simp only [codeWalk]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcodes (i + 1) (by simp only [Finset.mem_range] at hi; omega)]

private theorem codeFstFirstHit_eq_of_codeWalk_prefix
    (p q : ℕ → Fin 3) (d t T : ℕ)
    (hpt : codeFstFirstHit (-(d : ℤ)) p = (t : ℕ∞)) (ht : t ≤ T)
    (hwalk : ∀ n ≤ T, codeWalk p n = codeWalk q n) :
    codeFstFirstHit (-(d : ℤ)) q = (t : ℕ∞) := by
  classical
  have hp : ∃ n, (codeWalk p n).1 = -(d : ℤ) := by
    by_contra h
    have htop : codeFstFirstHit (-(d : ℤ)) p = ⊤ := by
      simp [codeFstFirstHit, h]
    rw [hpt] at htop
    simp at htop
  have hfind : Nat.find hp = t := by
    have hcast : (Nat.find hp : ℕ∞) = (t : ℕ∞) := by
      simpa [codeFstFirstHit, hp] using hpt
    exact_mod_cast hcast
  have hpspec : (codeWalk p t).1 = -(d : ℤ) := by
    simpa [hfind] using Nat.find_spec hp
  have heqT := congrArg Prod.fst (hwalk t ht)
  have hqspec : (codeWalk q t).1 = -(d : ℤ) := heqT.symm.trans hpspec
  have hq : ∃ n, (codeWalk q n).1 = -(d : ℤ) := ⟨t, hqspec⟩
  have hqfind : Nat.find hq = t := by
    apply (Nat.find_eq_iff hq).2
    constructor
    · exact hqspec
    · intro n hnt hhit
      have hne := Nat.find_min hp (by omega : n < Nat.find hp)
      have heq := congrArg Prod.fst (hwalk n (by omega))
      exact hne (heq.trans hhit)
  simp [codeFstFirstHit, hq, hqfind]

private theorem decodedChunkCodes_eq_of_completed_prefix
    (m C : ℕ) (p : ℕ → Fin 3) (hp0 : p 0 = 0)
    (hcap : codeFstFirstHit (-(m : ℤ)) p ≤ C) (i : ℕ)
    (hi : i ≤ (codeFstFirstHit (-(m : ℤ)) p).toNat) :
    decodedChunkCodes C (chunk m C p).1 i = p i := by
  have hcapNat : (codeFstFirstHit (-(m : ℤ)) p).toNat ≤ C := by
    cases hτ : codeFstFirstHit (-(m : ℤ)) p with
    | top => simp [hτ] at hcap
    | coe k =>
      have hk : (k : ℕ∞) ≤ C := by simpa [hτ] using hcap
      exact_mod_cast hk
  by_cases hi0 : i = 0
  · subst i
    simp [decodedChunkCodes, hp0]
  · have hiC : i ≤ C := hi.trans hcapNat
    have hsub : i - 1 + 1 = i := by omega
    have hlt : i - 1 < (codeFstFirstHit (-(m : ℤ)) p).toNat := by omega
    simp [decodedChunkCodes, hi0, hiC, chunk, hsub, hlt]

private theorem bridge_codeFstFirstHit_zero (ω : ℕ → Fin 3) :
    codeFstFirstHit 0 ω = 0 := by
  classical
  unfold codeFstFirstHit
  let h : ∃ n, (codeWalk ω n).1 = 0 := ⟨0, by simp [codeWalk_zero]⟩
  rw [dif_pos h]
  have hf : Nat.find h = 0 := by
    apply (Nat.find_eq_iff h).2
    constructor
    · simp [codeWalk_zero]
    · intro n hn
      omega
  simp [hf]

private theorem bridge_codeFstFirstHit_eq_coe_toNat {a : ℤ}
    (ω : ℕ → Fin 3) (hfin : codeFstFirstHit a ω < ⊤) :
    codeFstFirstHit a ω = ((codeFstFirstHit a ω).toNat : ℕ∞) := by
  cases h : codeFstFirstHit a ω with
  | top => simp [h] at hfin
  | coe n => simp [h]

private theorem codeWalk_has_level_of_fst_le (d : ℕ) (ω : ℕ → Fin 3)
    (hd : 0 < d) : ∀ n, (codeWalk ω n).1 ≤ -(d : ℤ) →
      ∃ k ≤ n, (codeWalk ω k).1 = -(d : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro hn
    simp [codeWalk_zero] at hn
    omega
  | succ n ih =>
    intro hn
    by_cases hp : (codeWalk ω n).1 ≤ -(d : ℤ)
    · obtain ⟨k, hk, hhit⟩ := ih hp
      exact ⟨k, by omega, hhit⟩
    · have hprev : -(d : ℤ) < (codeWalk ω n).1 := lt_of_not_ge hp
      have hs := congrArg Prod.fst (codeWalk_succ_sub ω n)
      rw [Prod.fst_sub] at hs
      have hstep : -1 ≤ (lazyTwoDimensionalStep (ω (n + 1))).1 := by
        generalize ω (n + 1) = c
        fin_cases c <;> decide
      have hcurr : -(d : ℤ) ≤ (codeWalk ω (n + 1)).1 := by omega
      exact ⟨n + 1, Nat.le_refl _, by omega⟩

private theorem bridge_codeFstFirstHit_intermediate_le (d e : ℕ)
    (ω : ℕ → Fin 3) (hde : d ≤ e)
    (hfin : codeFstFirstHit (-(e : ℤ)) ω < ⊤) :
    codeFstFirstHit (-(d : ℤ)) ω < ⊤ ∧
      (codeFstFirstHit (-(d : ℤ)) ω).toNat ≤
        (codeFstFirstHit (-(e : ℤ)) ω).toNat := by
  by_cases hd : d = 0
  · subst d
    change codeFstFirstHit 0 ω < ⊤ ∧
      (codeFstFirstHit 0 ω).toNat ≤ (codeFstFirstHit (-(e : ℤ)) ω).toNat
    rw [bridge_codeFstFirstHit_zero]
    constructor
    · exact ENat.coe_lt_top 0
    · simp
  · have hdpos : 0 < d := by omega
    have heHit : ∃ n, (codeWalk ω n).1 = -(e : ℤ) := by
      by_contra hn
      have htop : codeFstFirstHit (-(e : ℤ)) ω = ⊤ := by
        simp [codeFstFirstHit, hn]
      rw [htop] at hfin
      simp at hfin
    have heEq : codeFstFirstHit (-(e : ℤ)) ω =
        (Nat.find heHit : ℕ∞) := by
      simp [codeFstFirstHit, heHit]
    have heToNat : (codeFstFirstHit (-(e : ℤ)) ω).toNat = Nat.find heHit := by
      rw [heEq]
      rfl
    have hcross := codeWalk_has_level_of_fst_le d ω hdpos
      (Nat.find heHit) (by rw [Nat.find_spec heHit]; omega)
    obtain ⟨k, hk, hdk⟩ := hcross
    have hdHit : ∃ n, (codeWalk ω n).1 = -(d : ℤ) := ⟨k, hdk⟩
    have hdEq : codeFstFirstHit (-(d : ℤ)) ω = (Nat.find hdHit : ℕ∞) := by
      simp [codeFstFirstHit, hdHit]
    have hdFin : codeFstFirstHit (-(d : ℤ)) ω < ⊤ := by
      rw [hdEq]
      exact ENat.coe_lt_top _
    have hdToNat : (codeFstFirstHit (-(d : ℤ)) ω).toNat = Nat.find hdHit := by
      rw [hdEq]
      rfl
    constructor
    · exact hdFin
    · rw [hdToNat, heToNat]
      exact (Nat.find_min' hdHit hdk).trans hk

private theorem bridge_decodeWindow_eq_of_completed
    (N m C s o : ℕ) (ω : ℕ → Fin 3)
    (hbase : codeFstFirstHit (-((s * m : ℕ) : ℤ)) ω < ⊤)
    (hcomplete : (cappedLevelChunk m C s ω).2 = true)
    (hNo : N ≤ o) (hOm : o + N ≤ m) :
    (fun j : Fin (2 * N + 1) =>
      codeWalk ω
          ((codeFstFirstHit (-((s * m + o : ℕ) : ℤ)) ω).toNat + j.val - N) -
        codeWalk ω ((codeFstFirstHit (-((s * m + o : ℕ) : ℤ)) ω).toNat)) =
      decodeWindow N m C (cappedLevelChunk m C s ω) o := by
  let K : ℕ := s * m
  let p : ℕ → Fin 3 := codeShift (codeFstFirstHit (-((K : ℕ) : ℤ)) ω).toNat ω
  let b : ℕ := (codeFstFirstHit (-((K : ℕ) : ℤ)) ω).toNat
  change codeFstFirstHit (-((K : ℕ) : ℤ)) ω < ⊤ at hbase
  have hbaseEq : codeFstFirstHit (-((K : ℕ) : ℤ)) ω = (b : ℕ∞) := by
    simpa [b] using bridge_codeFstFirstHit_eq_coe_toNat ω hbase
  have hcap : codeFstFirstHit (-(m : ℤ)) p ≤ C := by
    change (if codeFstFirstHit (-(m : ℤ)) p ≤ C then true else false) = true at hcomplete
    by_contra hnot
    simp [hnot] at hcomplete
  have hmfin : codeFstFirstHit (-(m : ℤ)) p < ⊤ :=
    lt_of_le_of_lt hcap (ENat.natCast_lt_top C)
  let L : ℕ := (codeFstFirstHit (-(m : ℤ)) p).toNat
  have hmEq : codeFstFirstHit (-(m : ℤ)) p = (L : ℕ∞) := by
    simpa [L] using bridge_codeFstFirstHit_eq_coe_toNat p hmfin
  have ho_m : o ≤ m := by omega
  have hmid := bridge_codeFstFirstHit_intermediate_le o m p ho_m hmfin
  have hofin : codeFstFirstHit (-(o : ℤ)) p < ⊤ := hmid.1
  let u : ℕ := (codeFstFirstHit (-(o : ℤ)) p).toNat
  have hu_le_L : u ≤ L := by simpa [u, L] using hmid.2
  have hu_ge_o : o ≤ u := codeFstFirstHit_level_le_toNat o p hofin
  have huEq : codeFstFirstHit (-(o : ℤ)) p = (u : ℕ∞) := by
    simpa [u] using bridge_codeFstFirstHit_eq_coe_toNat p hofin
  have hp0 : p 0 = 0 := by simp [p, codeShift]
  let η : ℕ → Fin 3 := decodedChunkCodes C (chunk m C p).1
  have hcodes : ∀ i ≤ L, η i = p i := by
    intro i hi
    exact decodedChunkCodes_eq_of_completed_prefix m C p hp0 hcap i
      (by simpa [L] using hi)
  have hwalk : ∀ n ≤ L, codeWalk p n = codeWalk η n :=
    codeWalk_eq_of_code_prefix p η L (fun i hi => (hcodes i hi).symm)
  have hetaEq : codeFstFirstHit (-(o : ℤ)) η = (u : ℕ∞) :=
    codeFstFirstHit_eq_of_codeWalk_prefix p η o u L huEq hu_le_L hwalk
  have huN : u + N ≤ L := by
    by_cases ho0 : o = 0
    · have hu0 : u = 0 := by
        subst o
        dsimp [u]
        change (codeFstFirstHit 0 p).toNat = 0
        rw [bridge_codeFstFirstHit_zero]
        rfl
      omega
    · have hopos : 0 < o := by omega
      have haddTail := codeFstFirstHit_add o (m - o) hopos p hofin
      have hlevel : o + (m - o) = m := by omega
      have haddTail' : codeFstFirstHit (-(m : ℤ)) p =
          codeFstFirstHit (-(o : ℤ)) p +
            codeFstFirstHit (-((m - o : ℕ) : ℤ)) (codeShift u p) := by
        simpa [hlevel, huEq] using haddTail
      cases ht : codeFstFirstHit (-((m - o : ℕ) : ℤ)) (codeShift u p) with
      | top =>
        have htop : codeFstFirstHit (-(m : ℤ)) p = ⊤ := by
          rw [haddTail', huEq, ht]
          simp
        rw [htop] at hmfin
        simp at hmfin
      | coe v =>
        have hLv : L = u + v := by
          have hsum : (L : ℕ∞) = ((u + v : ℕ) : ℕ∞) := by
            calc
              (L : ℕ∞) = codeFstFirstHit (-(m : ℤ)) p := hmEq.symm
              _ = codeFstFirstHit (-(o : ℤ)) p +
                  codeFstFirstHit (-((m - o : ℕ) : ℤ)) (codeShift u p) := haddTail'
              _ = (u : ℕ∞) + (v : ℕ∞) := by rw [huEq, ht]
              _ = ((u + v : ℕ) : ℕ∞) := by simp [Nat.cast_add]
          exact_mod_cast hsum
        have hvfin : codeFstFirstHit (-((m - o : ℕ) : ℤ))
            (codeShift u p) < ⊤ := by
          rw [ht]
          exact ENat.natCast_lt_top v
        have hvgap := codeFstFirstHit_level_le_toNat (m - o) (codeShift u p) hvfin
        rw [ht] at hvgap
        have hNtail : N ≤ m - o := by omega
        have hNv : N ≤ v := hNtail.trans hvgap
        omega
  have hglobEq : codeFstFirstHit (-((K + o : ℕ) : ℤ)) ω =
      ((b + u : ℕ) : ℕ∞) := by
    by_cases hK0 : K = 0
    · have hb0 : b = 0 := by
        have hzero : codeFstFirstHit (-((K : ℕ) : ℤ)) ω = 0 := by
          simpa [hK0] using bridge_codeFstFirstHit_zero ω
        rw [hzero] at hbaseEq
        exact_mod_cast hbaseEq.symm
      have hbaseTime : (codeFstFirstHit (-((K : ℕ) : ℤ)) ω).toNat = 0 := by
        simpa [b] using hb0
      have hshiftWalk : ∀ n, codeWalk p n = codeWalk ω n := by
        intro n
        change codeWalk (codeShift
          (codeFstFirstHit (-((K : ℕ) : ℤ)) ω).toNat ω) n = codeWalk ω n
        rw [hbaseTime, codeWalk_codeShift]
        simp [codeWalk_zero]
      have hsame := codeFstFirstHit_eq_of_codeWalk_prefix p ω o u u huEq
        (Nat.le_refl _) (fun n _ => hshiftWalk n)
      simpa [hK0, hb0] using hsame
    · have hKpos : 0 < K := by omega
      have hadd := codeFstFirstHit_add K o hKpos ω hbase
      have hadd' : codeFstFirstHit (-((K + o : ℕ) : ℤ)) ω =
          codeFstFirstHit (-((K : ℕ) : ℤ)) ω + codeFstFirstHit (-(o : ℤ)) p := by
        simpa [p] using hadd
      rw [hadd', hbaseEq, huEq]
      simp [Nat.cast_add]
  have hglobTime :
      (codeFstFirstHit (-((K + o : ℕ) : ℤ)) ω).toNat = b + u := by
    rw [hglobEq]
    rfl
  have ho_le_m : o ≤ m := by omega
  funext j
  have hj : j.val ≤ 2 * N := by omega
  have hNu : N ≤ u := by omega
  let r : ℕ := u + j.val - N
  have hrle : r ≤ L := by
    dsimp [r]
    omega
  have hidx : b + u + j.val - N = b + r := by
    dsimp [r]
    omega
  have hshiftAt (n : ℕ) :
      codeWalk ω (b + n) = codeWalk p n + codeWalk ω b := by
    have hs := codeWalk_codeShift b ω n
    calc
      codeWalk ω (b + n) =
          (codeWalk ω (b + n) - codeWalk ω b) + codeWalk ω b := by abel
      _ = codeWalk p n + codeWalk ω b := by rw [← hs]
  have hchunk : cappedLevelChunk m C s ω = chunk m C p := by rfl
  change codeWalk ω
      ((codeFstFirstHit (-((K + o : ℕ) : ℤ)) ω).toNat + j.val - N) -
        codeWalk ω ((codeFstFirstHit (-((K + o : ℕ) : ℤ)) ω).toNat) =
      decodeWindow N m C (cappedLevelChunk m C s ω) o j
  rw [hglobTime, hidx]
  rw [hchunk]
  simp only [decodeWindow, if_pos ho_le_m]
  rw [hetaEq]
  change codeWalk ω (b + r) - codeWalk ω (b + u) =
    codeWalk η r - codeWalk η u
  rw [hshiftAt r, hshiftAt u, hwalk r hrle, hwalk u hu_le_L]
  abel

/-- A completed capped block decodes exactly the walk window centered at its
level-offset first hit, almost surely under iid codes. Helper for
a paper result. -/
theorem ae_cappedLevelChunk_decodeWindow (N m s o : ℕ) :
    ∀ᵐ ω ∂iidCodeMeasure,
      (cappedLevelChunk m (m ^ 100) s ω).2 = true →
      N ≤ o →
      o + N ≤ m →
      (fun j : Fin (2 * N + 1) =>
        codeWalk ω
            ((codeFstFirstHit (-((s * m + o : ℕ) : ℤ)) ω).toNat + j.val - N) -
          codeWalk ω ((codeFstFirstHit (-((s * m + o : ℕ) : ℤ)) ω).toNat)) =
        decodeWindow N m (m ^ 100) (cappedLevelChunk m (m ^ 100) s ω) o := by
  let K : ℕ := s * m
  filter_upwards [ae_codeFstFirstHit_lt_top_int (-((K : ℕ) : ℤ))] with ω hbase
  intro hcomplete hNo hOm
  exact bridge_decodeWindow_eq_of_completed N m (m ^ 100) s o ω hbase
    hcomplete hNo hOm

end DirectedDistances.RandomWalk
