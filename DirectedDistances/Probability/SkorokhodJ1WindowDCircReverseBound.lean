/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowInterpolantTimeChange

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.Probability




theorem windowPartitionSecantSlope_log_abs_le {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hsmall : 4 * η ≤ δ)
    (hclose : ∀ t : J1Window T, |(φ t : ℝ) - t| ≤ η)
    (hsparse : p.IsSparse δ) (i : Fin p.n) :
    |Real.log (windowPartitionSecantSlope p φ i)| ≤ 4 * (η / δ) := by
  let a : ℝ := (p.time i.castSucc : ℝ)
  let b : ℝ := (p.time i.succ : ℝ)
  let q : ℝ := windowPartitionSecantSlope p φ i
  let r : ℝ := 2 * (η / δ)
  have hgap : δ < b - a := by
    simpa [a, b] using hsparse i
  have hden : 0 < b - a := by linarith
  have hratio : q = ((φ (p.time i.succ) : ℝ) -
      (φ (p.time i.castSucc) : ℝ)) / (b - a) := by
    simp [q, windowPartitionSecantSlope, a, b]
  have hdispB := hclose (p.time i.succ)
  have hdispA := hclose (p.time i.castSucc)
  have hdiff : |((φ (p.time i.succ) : ℝ) - b) -
      ((φ (p.time i.castSucc) : ℝ) - a)| ≤ 2 * η := by
    calc
      _ ≤ |(φ (p.time i.succ) : ℝ) - b| +
          |(φ (p.time i.castSucc) : ℝ) - a| := abs_sub _ _
      _ ≤ η + η := add_le_add hdispB hdispA
      _ = 2 * η := by ring
  have hqdist : |q - 1| ≤ r := by
    rw [hratio]
    have hnum : ((φ (p.time i.succ) : ℝ) -
        (φ (p.time i.castSucc) : ℝ)) - (b - a) =
        ((φ (p.time i.succ) : ℝ) - b) -
          ((φ (p.time i.castSucc) : ℝ) - a) := by ring
    rw [show (((φ (p.time i.succ) : ℝ) -
        (φ (p.time i.castSucc) : ℝ)) / (b - a)) - 1 =
        ((((φ (p.time i.succ) : ℝ) -
          (φ (p.time i.castSucc) : ℝ)) - (b - a)) / (b - a)) by
      field_simp]
    rw [hnum, abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    have hratioGap : 1 ≤ (b - a) / δ :=
      (le_div_iff₀ hδ).2 (by simpa using hgap.le)
    have hmul : 2 * η ≤ 2 * η * ((b - a) / δ) := by
      simpa using mul_le_mul_of_nonneg_left hratioGap
        (show 0 ≤ (2 : ℝ) * η by positivity)
    calc
      |((φ (p.time i.succ) : ℝ) - b) -
          ((φ (p.time i.castSucc) : ℝ) - a)| ≤ 2 * η := hdiff
      _ ≤ 2 * η * ((b - a) / δ) := hmul
      _ = (2 * (η / δ)) * (b - a) := by field_simp
  have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
  have hr_half : r ≤ 1 / 2 := by
    calc
      r = (2 * η) / δ := by dsimp [r]; ring
      _ ≤ 1 / 2 := (div_le_iff₀ hδ).2 (by linarith)
  have hqpos : 0 < q := by
    rw [hratio]
    exact div_pos (sub_pos.mpr (by exact_mod_cast φ.strictMono (p.strict i))) hden
  have hqlo : 1 - r ≤ q := by linarith [abs_le.mp hqdist]
  have hqhi : q ≤ 1 + r := by linarith [abs_le.mp hqdist]
  have hbasepos : 0 < 1 - r := by linarith
  have hexp_lo : Real.exp (-2 * r) ≤ 1 - r := by
    have hexp := Real.add_one_le_exp (2 * r)
    have hexp' : 1 + 2 * r ≤ Real.exp (2 * r) := by
      simpa [add_comm] using hexp
    rw [show -2 * r = -(2 * r) by ring, Real.exp_neg]
    apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).2
    calc
      1 ≤ (1 - r) * (1 + 2 * r) := by nlinarith
      _ ≤ (1 - r) * Real.exp (2 * r) :=
        mul_le_mul_of_nonneg_left hexp' (by linarith)
  have hexp_hi : 1 + r ≤ Real.exp (2 * r) := by
    have hexp := Real.add_one_le_exp (2 * r)
    linarith
  have hloglo : -(2 * r) ≤ Real.log q := by
    apply (Real.le_log_iff_exp_le hqpos).2
    have hexp_lo' : Real.exp (-(2 * r)) ≤ 1 - r := by
      simpa [show -2 * r = -(2 * r) by ring] using hexp_lo
    exact hexp_lo'.trans hqlo
  have hloghi : Real.log q ≤ 2 * r := by
    apply (Real.log_le_iff_le_exp hqpos).2
    exact hqhi.trans hexp_hi
  have hlogabs : |Real.log q| ≤ 2 * r := abs_le.mpr ⟨hloglo, hloghi⟩
  calc
    |Real.log (windowPartitionSecantSlope p φ i)| = |Real.log q| := by simp [q]
    _ ≤ 2 * r := hlogabs
    _ = 4 * (η / δ) := by dsimp [r]; ring





theorem windowPartitionInterpolantTimeChange_block_image {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) (i : Fin p.n) :
    windowPartitionInterpolantTimeChange p φ (p.time i.castSucc) =
        φ (p.time i.castSucc) ∧
      windowPartitionInterpolantTimeChange p φ (p.time i.succ) =
        φ (p.time i.succ) := by
  constructor <;> apply Subtype.ext <;>
    rw [windowPartitionInterpolantTimeChange_apply,
      windowPartitionLinearInterpolant_node]





theorem windowPartitionInterpolantTimeChange_symm_image_mem_block
    {T : ℝ} {hT : 0 < T} (p : WindowPartition T hT)
    (φ : J1TimeChange T) (i : Fin p.n) (t : J1Window T)
    (ht : p.time i.castSucc ≤ t ∧ t ≤ p.time i.succ) :
    (windowPartitionInterpolantTimeChange p φ).symm (φ t) ∈
      Set.Icc (p.time i.castSucc) (p.time i.succ) := by
  let μ := windowPartitionInterpolantTimeChange p φ
  have hnodes := windowPartitionInterpolantTimeChange_block_image p φ i
  have hleft : μ (p.time i.castSucc) ≤ φ t := by
    rw [hnodes.1]
    exact φ.monotone ht.1
  have hright : φ t ≤ μ (p.time i.succ) := by
    rw [hnodes.2]
    exact φ.monotone ht.2
  constructor
  · have hm := μ.symm.monotone hleft
    simpa [μ] using hm
  · have hm := μ.symm.monotone hright
    simpa [μ] using hm





theorem windowPartitionInterpolant_inv_comp_mem_block
    {T : ℝ} {hT : 0 < T} (p : WindowPartition T hT)
    (φ : J1TimeChange T) (i : Fin p.n) (s : J1Window T)
    (hs : p.time i.castSucc ≤ s ∧ s ≤ p.time i.succ) :
    φ.symm (windowPartitionInterpolantTimeChange p φ s) ∈
      Set.Icc (p.time i.castSucc) (p.time i.succ) := by
  let μ := windowPartitionInterpolantTimeChange p φ
  have hnodes := windowPartitionInterpolantTimeChange_block_image p φ i
  constructor
  · calc
      p.time i.castSucc = φ.symm (μ (p.time i.castSucc)) := by
        rw [hnodes.1]
        exact (φ.symm_apply_apply _).symm
      _ ≤ φ.symm (μ s) := φ.symm.monotone (μ.monotone hs.1)
  · calc
      φ.symm (μ s) ≤ φ.symm (μ (p.time i.succ)) :=
        φ.symm.monotone (μ.monotone hs.2)
      _ = p.time i.succ := by
        rw [hnodes.2]
        exact φ.symm_apply_apply _

private theorem windowPartitionInterpolant_inv_comp_mem_Ico
    {T : ℝ} {hT : 0 < T} (p : WindowPartition T hT)
    (φ : J1TimeChange T) (i : Fin p.n) (s : J1Window T)
    (hs : p.time i.castSucc ≤ s) (hst : s < p.time i.succ) :
    φ.symm (windowPartitionInterpolantTimeChange p φ s) ∈
      Set.Ico (p.time i.castSucc) (p.time i.succ) := by
  let μ := windowPartitionInterpolantTimeChange p φ
  have hnodes := windowPartitionInterpolantTimeChange_block_image p φ i
  constructor
  · calc
      p.time i.castSucc = φ.symm (μ (p.time i.castSucc)) := by
        rw [hnodes.1]
        exact (φ.symm_apply_apply _).symm
      _ ≤ φ.symm (μ s) := φ.symm.monotone (μ.monotone hs)
  · calc
      φ.symm (μ s) < φ.symm (μ (p.time i.succ)) :=
        φ.symm.strictMono (μ.strictMono hst)
      _ = p.time i.succ := by
        rw [hnodes.2]
        exact φ.symm_apply_apply _

private theorem windowPartition_exists_half_open_block
    {T : ℝ} {hT : 0 < T} (p : WindowPartition T hT)
    (s : J1Window T) (hsT : (s : ℝ) < T) :
    ∃ i : Fin p.n, p.time i.castSucc ≤ s ∧ s < p.time i.succ := by
  classical
  let q : Finset (Fin (p.n + 1)) :=
    Finset.univ.filter fun j => (s : ℝ) < (p.time j : ℝ)
  have hq : q.Nonempty := by
    refine ⟨Fin.last p.n, ?_⟩
    simp only [q, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [p.last]
    exact hsT
  let j := q.min' hq
  have hjq : j ∈ q := Finset.min'_mem q hq
  have hjs : (s : ℝ) < (p.time j : ℝ) := by
    simpa only [q, Finset.mem_filter, Finset.mem_univ, true_and] using hjq
  have hjpos : 0 < j.val := by
    by_contra hj
    have hjzero : j.val = 0 := by omega
    have htime : p.time j = p.time 0 := by
      apply congrArg p.time
      apply Fin.ext
      exact hjzero
    rw [htime, p.first] at hjs
    exact (not_lt_of_ge s.property.1) hjs
  let i : Fin p.n := ⟨j.val - 1, by have := j.isLt; omega⟩
  have hji : i.succ = j := by
    apply Fin.ext
    simp only [Fin.val_succ]
    dsimp [i]
    omega
  have hleft : p.time i.castSucc ≤ s := by
    by_contra hnot
    have hprev : (s : ℝ) < (p.time i.castSucc : ℝ) := by
      exact_mod_cast (lt_of_not_ge hnot)
    have hprev_mem : i.castSucc ∈ q := by
      simp only [q, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hprev
    have hmin := Finset.min'_le q i.castSucc hprev_mem
    have hmin' : i.succ ≤ i.castSucc := by simpa [hji] using hmin
    have hvals : (i.succ).val ≤ (i.castSucc).val := by exact_mod_cast hmin'
    simp only [Fin.val_succ, Fin.val_castSucc] at hvals
    omega
  refine ⟨i, hleft, ?_⟩
  rw [hji]
  exact_mod_cast hjs

private theorem fin_sum_adjacent_sub_reverse (n : ℕ) :
    ∀ f : Fin (n + 1) → ℝ,
      (Finset.univ.sum (fun i : Fin n => f i.succ - f i.castSucc)) =
        f (Fin.last n) - f 0 := by
  induction n with
  | zero =>
    intro f
    simp
  | succ n ih =>
    intro f
    rw [Fin.sum_univ_castSucc]
    have hih := ih (fun j => f (Fin.castSucc j))
    have hsum :
        Finset.univ.sum (fun i : Fin n =>
          f (Fin.succ (Fin.castSucc i)) - f (Fin.castSucc (Fin.castSucc i))) =
        Finset.univ.sum (fun i : Fin n =>
          f (Fin.castSucc (Fin.succ i)) - f (Fin.castSucc (Fin.castSucc i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show Fin.succ (Fin.castSucc i) = Fin.castSucc i.succ by
        exact Fin.ext (by simp)]
    have hfirst :
        Finset.univ.sum (fun i : Fin n =>
          f (Fin.castSucc (Fin.succ i)) - f (Fin.castSucc (Fin.castSucc i))) =
        f (Fin.castSucc (Fin.last n)) - f 0 := by
      simpa using hih
    rw [hsum, hfirst]
    have hlast : f (Fin.last n).succ = f (Fin.last (n + 1)) := by
      congr 1
    rw [hlast]
    ring

private theorem clipped_increment_nonneg_reverse {a b s t : ℝ}
    (hab : a ≤ b) (hst : s ≤ t) :
    0 ≤ (min t b - min t a) - (min s b - min s a) := by
  by_cases hsa : s ≤ a
  · by_cases hta : t ≤ a
    · rw [min_eq_left hta, min_eq_left hsa,
        min_eq_left (le_trans hta hab), min_eq_left (le_trans hsa hab)]
      simp
    · have hat : a < t := lt_of_not_ge hta
      rw [min_eq_left hsa, min_eq_left (le_trans hsa hab), min_eq_right hat.le]
      have ham : a ≤ min t b := le_min hat.le hab
      linarith
  · have has : a < s := lt_of_not_ge hsa
    have hat : a < t := lt_of_lt_of_le has hst
    rw [min_eq_right has.le, min_eq_right hat.le]
    have hmin : min s b ≤ min t b := min_le_min hst le_rfl
    linarith

private theorem clipped_increment_sum_reverse {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) {s t : ℝ}
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hsT : s ≤ T) (htT : t ≤ T) :
    Finset.univ.sum (fun i : Fin p.n =>
      (min t (p.time i.succ : ℝ) - min t (p.time i.castSucc : ℝ)) -
        (min s (p.time i.succ : ℝ) - min s (p.time i.castSucc : ℝ))) = t - s := by
  let f : Fin (p.n + 1) → ℝ := fun j =>
    min t (p.time j : ℝ) - min s (p.time j : ℝ)
  calc
    _ = Finset.univ.sum (fun i : Fin p.n => f i.succ - f i.castSucc) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [f]
      ring
    _ = f (Fin.last p.n) - f 0 := fin_sum_adjacent_sub_reverse p.n f
    _ = t - s := by
      dsimp [f]
      simp only [p.last, p.first, Subtype.coe_mk]
      rw [min_eq_left htT, min_eq_left hsT,
        min_eq_right ht0, min_eq_right hs0]
      ring

private theorem windowPartitionInterpolantTimeChange_slopeNorm_le_of_log_bound
    {T : ℝ} {hT : 0 < T} (p : WindowPartition T hT)
    (φ : J1TimeChange T) {A : ℝ}
    (hlog : ∀ i : Fin p.n,
      |Real.log (windowPartitionSecantSlope p φ i)| ≤ A) :
    j1TimeChangeSlopeNorm (windowPartitionInterpolantTimeChange p φ) ≤
      ENNReal.ofReal A := by
  classical
  let μ := windowPartitionInterpolantTimeChange p φ
  unfold j1TimeChangeSlopeNorm
  apply iSup_le
  intro q
  let x : J1Window T := q.1.1
  let y : J1Window T := q.1.2
  let s : ℝ := x
  let t : ℝ := y
  have hst : s < t := by exact_mod_cast q.2
  let d : Fin p.n → ℝ := fun i =>
    (min t (p.time i.succ : ℝ) - min t (p.time i.castSucc : ℝ)) -
      (min s (p.time i.succ : ℝ) - min s (p.time i.castSucc : ℝ))
  have hd (i : Fin p.n) : 0 ≤ d i := by
    apply clipped_increment_nonneg_reverse
    · exact (p.strict i).le
    · exact hst.le
  have hsum : ∑ i : Fin p.n, d i = t - s := by
    exact clipped_increment_sum_reverse p
      (by exact_mod_cast x.property.1)
      (by exact_mod_cast y.property.1)
      (by exact_mod_cast x.property.2)
      (by exact_mod_cast y.property.2)
  have hdiff :
      windowPartitionLinearInterpolant p φ y -
          windowPartitionLinearInterpolant p φ x =
        ∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i := by
    rw [windowPartitionLinearInterpolant_def, windowPartitionLinearInterpolant_def,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [d, s, t]
    ring
  have hden : 0 < t - s := sub_pos.mpr hst
  have hslope_lo (i : Fin p.n) :
      Real.exp (-A) ≤ windowPartitionSecantSlope p φ i := by
    have h := abs_le.mp (hlog i)
    exact (Real.le_log_iff_exp_le (windowPartitionSecantSlope_pos p φ i)).mp h.1
  have hslope_hi (i : Fin p.n) :
      windowPartitionSecantSlope p φ i ≤ Real.exp A := by
    have h := abs_le.mp (hlog i)
    exact (Real.log_le_iff_le_exp (windowPartitionSecantSlope_pos p φ i)).mp h.2
  have hsumlo : Real.exp (-A) * (t - s) ≤
      ∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i := by
    calc
      Real.exp (-A) * (t - s) =
          ∑ i : Fin p.n, Real.exp (-A) * d i := by rw [← hsum, Finset.mul_sum]
      _ ≤ ∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hslope_lo i) (hd i)
  have hsumhi :
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) ≤
        Real.exp A * (t - s) := by
    calc
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) ≤
          ∑ i : Fin p.n, Real.exp A * d i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hslope_hi i) (hd i)
      _ = Real.exp A * (t - s) := by rw [← Finset.mul_sum, hsum]
  have hnumpos :
      0 < ∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) hden) hsumlo
  have hratio_lo : Real.exp (-A) ≤
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s) :=
    (le_div_iff₀ hden).2 hsumlo
  have hratio_hi :
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s) ≤
        Real.exp A := (div_le_iff₀ hden).2 hsumhi
  have hratio_pos : 0 <
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s) :=
    div_pos hnumpos hden
  have hloglo : -A ≤ Real.log
      ((∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s)) :=
    (Real.le_log_iff_exp_le hratio_pos).2 hratio_lo
  have hloghi : Real.log
      ((∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s)) ≤ A :=
    (Real.log_le_iff_le_exp hratio_pos).2 hratio_hi
  have hlogabs : |Real.log
      ((∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s))| ≤ A :=
    abs_le.mpr ⟨hloglo, hloghi⟩
  have hchord : j1ChordLogSlope μ q = Real.log
      ((∑ i : Fin p.n, windowPartitionSecantSlope p φ i * d i) / (t - s)) := by
    change Real.log (((μ y : ℝ) - (μ x : ℝ)) / (t - s)) = _
    rw [windowPartitionInterpolantTimeChange_apply,
      windowPartitionInterpolantTimeChange_apply, hdiff]
  rw [hchord]
  exact ENNReal.ofReal_le_ofReal hlogabs





theorem j1WindowDCirc_le_of_partition_witness
    {T : ℝ} (hT : 0 < T) (x y : CadlagWindow T)
    (p : WindowPartition T hT) (φ : J1TimeChange T)
    {δ η ω₀ : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η)
    (hsmall : 4 * η ≤ δ) (hsparse : p.IsSparse δ)
    (hosc : ∀ i : Fin p.n,
      blockOscillation x (p.time i.castSucc) (p.time i.succ) ≤ ω₀)
    (hdisp : ∀ t : J1Window T, |(φ t : ℝ) - t| ≤ η)
    (hvalue : ∀ t : J1Window T, |y.1 (φ t) - x.1 t| ≤ η) :
    j1WindowDCirc hT x y ≤ ENNReal.ofReal (max (4 * (η / δ)) (ω₀ + η)) := by
  let μ := windowPartitionInterpolantTimeChange p φ
  have hω₀ : 0 ≤ ω₀ := by
    let i : Fin p.n := ⟨0, p.n_pos⟩
    have hnonneg :
        0 ≤ blockOscillation x (p.time i.castSucc) (p.time i.succ) := by
      unfold blockOscillation
      apply le_csSup (blockOscillation_values_bddAbove x _ _)
      refine ⟨p.time i.castSucc, p.time i.castSucc, le_rfl,
        p.strict i, le_rfl, p.strict i, ?_⟩
      simp
    exact hnonneg.trans (hosc i)
  have hlog (i : Fin p.n) :
      |Real.log (windowPartitionSecantSlope p φ i)| ≤ 4 * (η / δ) :=
    windowPartitionSecantSlope_log_abs_le p φ hδ hη hsmall hdisp hsparse i
  have hnorm : j1TimeChangeSlopeNorm μ ≤ ENNReal.ofReal (4 * (η / δ)) := by
    exact windowPartitionInterpolantTimeChange_slopeNorm_le_of_log_bound p φ hlog
  have htopfix (ψ : J1TimeChange T) :
      ψ ⟨T, hT.le, le_rfl⟩ = ⟨T, hT.le, le_rfl⟩ := by
    apply Subtype.ext
    apply le_antisymm
    · exact (ψ ⟨T, hT.le, le_rfl⟩).property.2
    · obtain ⟨z, hz⟩ := ψ.surjective ⟨T, hT.le, le_rfl⟩
      have hzle : z ≤ (⟨T, hT.le, le_rfl⟩ : J1Window T) := z.property.2
      have hmono := ψ.monotone hzle
      rw [hz] at hmono
      exact hmono
  have hpoint : ∀ s : J1Window T, |y.1 (μ s) - x.1 s| ≤ ω₀ + η := by
    intro s
    let u : J1Window T := φ.symm (μ s)
    have hφu : φ u = μ s := φ.apply_symm_apply (μ s)
    by_cases hsT : (s : ℝ) < T
    · obtain ⟨i, hleft, hright⟩ :=
        windowPartition_exists_half_open_block p s hsT
      have hu := windowPartitionInterpolant_inv_comp_mem_Ico p φ i s
        hleft hright
      have hsosc : |x.1 s - x.1 u| ≤
          blockOscillation x (p.time i.castSucc) (p.time i.succ) := by
        apply le_csSup (blockOscillation_values_bddAbove x _ _)
        refine ⟨s, u, ?_, ?_, ?_, ?_, rfl⟩
        · exact (Set.mem_Ico.mp ⟨hleft, hright⟩).1
        · exact (Set.mem_Ico.mp ⟨hleft, hright⟩).2
        · exact (Set.mem_Ico.mp hu).1
        · exact (Set.mem_Ico.mp hu).2
      calc
        |y.1 (μ s) - x.1 s| ≤
            |y.1 (μ s) - x.1 u| + |x.1 u - x.1 s| := abs_sub_le _ _ _
        _ = |y.1 (φ u) - x.1 u| + |x.1 s - x.1 u| := by
          rw [← hφu]
          rw [abs_sub_comm (x.1 u) (x.1 s)]
        _ ≤ η + ω₀ := add_le_add (hvalue u) (hsosc.trans (hosc i))
        _ = ω₀ + η := add_comm _ _
    · have hsEq : s = (⟨T, hT.le, le_rfl⟩ : J1Window T) := by
        apply Subtype.ext
        exact le_antisymm s.property.2 (not_lt.mp hsT)
      have hphitop := htopfix φ
      have hμtop := windowPartitionInterpolantTimeChange_last p φ
      have hμs : μ s = s := by rw [hsEq, hμtop]
      have hφs : φ s = s := by rw [hsEq, hphitop]
      calc
        |y.1 (μ s) - x.1 s| = |y.1 (φ s) - x.1 s| := by
          rw [hμs, hφs]
        _ ≤ η := hvalue s
        _ ≤ ω₀ + η := by linarith
  have hvalSup : (⨆ s : J1Window T, |y.1 (μ s) - x.1 s|) ≤ ω₀ + η := by
    change sSup (Set.range fun s : J1Window T => |y.1 (μ s) - x.1 s|) ≤ _
    apply csSup_le
    · exact ⟨|y.1 (μ ⟨0, le_rfl, hT.le⟩) - x.1 ⟨0, le_rfl, hT.le⟩|,
        ⟨⟨0, le_rfl, hT.le⟩, rfl⟩⟩
    · rintro z ⟨s, rfl⟩
      exact hpoint s
  have hcost : j1WindowDCircCost y x μ ≤
      ENNReal.ofReal (max (4 * (η / δ)) (ω₀ + η)) := by
    unfold j1WindowDCircCost
    apply max_le
    · exact hnorm.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · exact ENNReal.ofReal_le_ofReal (hvalSup.trans (le_max_right _ _))
  have hreverse : j1WindowDCirc hT y x ≤
      ENNReal.ofReal (max (4 * (η / δ)) (ω₀ + η)) := by
    change (⨅ ψ : J1TimeChange T, j1WindowDCircCost y x ψ) ≤ _
    apply (ciInf_le ?_ μ).trans hcost
    refine ⟨0, ?_⟩
    rintro _ ⟨ψ, rfl⟩
    exact bot_le
  calc
    j1WindowDCirc hT x y = j1WindowDCirc hT y x := j1WindowDCirc_symm hT x y
    _ ≤ _ := hreverse





theorem j1WindowDist_small_implies_dCirc_small {T : ℝ} (hT : 0 < T)
    (x : CadlagWindow T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : CadlagWindow T,
      j1WindowDist hT x y < δ →
        j1WindowDCirc hT x y < ENNReal.ofReal ε := by
  classical
  obtain ⟨p, hp⟩ := exists_partition_oscillation_lt hT x
    (show 0 < ε / 8 by positivity)
  let gap : Fin p.n → ℝ := fun i =>
    (p.time i.succ).val - (p.time i.castSucc).val
  let gaps : Finset ℝ := Finset.univ.image gap
  have hgaps : gaps.Nonempty := by
    refine ⟨gap ⟨0, p.n_pos⟩, ?_⟩
    exact Finset.mem_image.mpr
      ⟨⟨0, p.n_pos⟩, Finset.mem_univ _, rfl⟩
  let γ := gaps.min' hgaps
  have hγpos : 0 < γ := by
    obtain ⟨i, _, hgi⟩ := Finset.mem_image.mp (Finset.min'_mem gaps hgaps)
    change 0 < gaps.min' hgaps
    rw [← hgi]
    exact sub_pos.mpr (p.strict i)
  have hγle (i : Fin p.n) : γ ≤ gap i := by
    exact Finset.min'_le gaps (gap i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hmod := cadlagModulus_tendsto_zero hT x
  rw [Metric.tendsto_nhdsWithin_nhds] at hmod
  obtain ⟨r, hr, hnear⟩ := hmod (ε / 8) (by positivity)
  let Δ := min (r / 2) (min (γ / 2) (T / 2))
  have hΔpos : 0 < Δ := by
    dsimp [Δ]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hΔr : dist Δ 0 < r := by
    have hrhalf : r / 2 < r := by linarith
    rw [Real.dist_eq, sub_zero, abs_of_pos hΔpos]
    exact (min_le_left _ _).trans_lt hrhalf
  have hΔγ : Δ < γ := by
    have hγhalf : γ / 2 < γ := by linarith
    calc
      Δ ≤ min (γ / 2) (T / 2) := min_le_right _ _
      _ ≤ γ / 2 := min_le_left _ _
      _ < γ := hγhalf
  have hΔT : Δ < T := by
    have hThalf : T / 2 < T := by linarith
    calc
      Δ ≤ min (γ / 2) (T / 2) := min_le_right _ _
      _ ≤ T / 2 := min_le_right _ _
      _ < T := hThalf
  have hmodlt : cadlagModulus (hT := hT) x Δ < ε / 8 := by
    have hdist := hnear (x := Δ) hΔpos hΔr
    have habs : |cadlagModulus (hT := hT) x Δ| < ε / 8 := by
      simpa [Real.dist_eq] using hdist
    exact (le_abs_self _).trans_lt habs
  let ω₀ := max (ε / 8) (cadlagModulus (hT := hT) x Δ)
  have hωlt : ω₀ < ε / 4 := by
    dsimp [ω₀]
    apply max_lt_iff.mpr
    constructor <;> linarith
  have hsparse : p.IsSparse Δ := by
    intro i
    exact lt_of_lt_of_le hΔγ (hγle i)
  have hosc (i : Fin p.n) :
      blockOscillation x (p.time i.castSucc) (p.time i.succ) ≤ ω₀ := by
    exact (hp i).le.trans (le_max_left _ _)
  let ρ := min (Δ / 4) (min (ε * Δ / 8) (ε / 4))
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hsmall : 4 * ρ ≤ Δ := by
    have hρΔ : ρ ≤ Δ / 4 := min_le_left _ _
    calc
      4 * ρ ≤ 4 * (Δ / 4) :=
        mul_le_mul_of_nonneg_left hρΔ (by norm_num)
      _ = Δ := by ring
  have hρεΔ : ρ ≤ ε * Δ / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hρε : ρ ≤ ε / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hslope : 4 * (ρ / Δ) < ε := by
    have hratio : 4 * (ρ / Δ) ≤ ε / 2 := by
      rw [show 4 * (ρ / Δ) = (4 * ρ) / Δ by ring]
      apply (div_le_iff₀ hΔpos).2
      nlinarith [hρεΔ]
    linarith
  have hvalue : ω₀ + ρ < ε := by nlinarith [hωlt, hρε]
  have hmax : max (4 * (ρ / Δ)) (ω₀ + ρ) < ε :=
    max_lt_iff.mpr ⟨hslope, hvalue⟩
  refine ⟨ρ, hρpos, ?_⟩
  intro y hy
  have hyx : j1WindowDist hT y x < ρ := by
    simpa only [j1WindowDist_symm hT x y] using hy
  change (⨅ φ : J1TimeChange T,
      max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
        (⨆ t : J1Window T, |y.1 (φ t) - x.1 t|)) < ρ at hyx
  obtain ⟨φ, hcost⟩ := exists_lt_of_ciInf_lt hyx
  have hdisp (t : J1Window T) : |(φ t : ℝ) - t| ≤ ρ := by
    have hlt : |(φ t : ℝ) - t| < ρ := by
      calc
        |(φ t : ℝ) - t| ≤
            ⨆ s : J1Window T, |(φ s : ℝ) - s| :=
          le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove φ) t le_rfl
        _ ≤ max (⨆ s : J1Window T, |(φ s : ℝ) - s|)
            (⨆ s : J1Window T, |y.1 (φ s) - x.1 s|) := le_max_left _ _
        _ < ρ := hcost
    exact hlt.le
  have hval (t : J1Window T) : |y.1 (φ t) - x.1 t| ≤ ρ := by
    have hlt : |y.1 (φ t) - x.1 t| < ρ := by
      calc
        |y.1 (φ t) - x.1 t| ≤
            ⨆ s : J1Window T, |y.1 (φ s) - x.1 s| :=
          le_ciSup_of_le (j1WindowValueError_bddAbove y x φ) t le_rfl
        _ ≤ max (⨆ s : J1Window T, |(φ s : ℝ) - s|)
            (⨆ s : J1Window T, |y.1 (φ s) - x.1 s|) := le_max_right _ _
        _ < ρ := hcost
    exact hlt.le
  have hbound := j1WindowDCirc_le_of_partition_witness hT x y p φ
    hΔpos (show 0 ≤ ρ by exact hρpos.le) hsmall hsparse hosc hdisp hval
  exact hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).2 hmax)

end DirectedDistances.Probability
