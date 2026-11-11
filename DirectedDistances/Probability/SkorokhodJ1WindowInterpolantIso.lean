/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowDCircReverse
public import DirectedDistances.Probability.SkorokhodJ1WindowDCirc
public import DirectedDistances.Probability.SkorokhodModulus

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.Probability



theorem windowPartitionLinearInterpolant_continuous {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) :
    Continuous (windowPartitionLinearInterpolant p φ) := by
  change Continuous (fun t : J1Window T =>
    ∑ i : Fin p.n, windowPartitionSecantSlope p φ i *
      (min (t : ℝ) (p.time i.succ : ℝ) - min (t : ℝ) (p.time i.castSucc : ℝ)))
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul
    ((continuous_subtype_val.min continuous_const).sub
      (continuous_subtype_val.min continuous_const))

private theorem fin_sum_adjacent_sub_iso (n : ℕ) :
    ∀ f : Fin (n + 1) → ℝ,
      (Finset.univ.sum (fun i : Fin n => f i.succ - f (Fin.castSucc i))) =
        f (Fin.last n) - f 0 := by
  induction n with
  | zero =>
    intro f
    simp
  | succ n ih =>
    intro f
    rw [Fin.sum_univ_castSucc]
    have hih := ih (fun j => f (Fin.castSucc j))
    have hfirst :
        Finset.univ.sum (fun i : Fin n =>
          f (Fin.castSucc (Fin.succ i)) - f (Fin.castSucc (Fin.castSucc i))) =
          f (Fin.castSucc (Fin.last n)) - f 0 := by
      simpa using hih
    have hsum :
        Finset.univ.sum (fun i : Fin n =>
          f (Fin.succ (Fin.castSucc i)) - f (Fin.castSucc (Fin.castSucc i))) =
        Finset.univ.sum (fun i : Fin n =>
          f (Fin.castSucc (Fin.succ i)) - f (Fin.castSucc (Fin.castSucc i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show Fin.succ (Fin.castSucc i) = Fin.castSucc i.succ by
        exact Fin.ext (by simp)]
    rw [hsum, hfirst]
    have hlast : f (Fin.last n).succ = f (Fin.last (n + 1)) := by
      congr 1
    rw [hlast]
    ring

private theorem windowPartition_clipped_increment_nonneg {a b s t : ℝ}
    (hab : a ≤ b) (hst : s ≤ t) :
    0 ≤ (min t b - min t a) - (min s b - min s a) := by
  by_cases hsa : s ≤ a
  · by_cases hta : t ≤ a
    · rw [min_eq_left hta, min_eq_left hsa,
        min_eq_left (le_trans hta hab), min_eq_left (le_trans hsa hab)]
      simp
    · have hat : a < t := lt_of_not_ge hta
      have ham : a ≤ min t b := le_min hat.le hab
      rw [min_eq_left hsa, min_eq_left (le_trans hsa hab), min_eq_right hat.le]
      linarith
  · have has : a < s := lt_of_not_ge hsa
    have hat : a < t := lt_of_lt_of_le has hst
    rw [min_eq_right has.le, min_eq_right hat.le]
    have hmin : min s b ≤ min t b := min_le_min hst le_rfl
    linarith

private theorem windowPartition_interpolant_increment_sum {T : ℝ} {hT : 0 < T}
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
    _ = f (Fin.last p.n) - f 0 := fin_sum_adjacent_sub_iso p.n f
    _ = t - s := by
      dsimp [f]
      simp only [p.last, p.first, Subtype.coe_mk]
      rw [min_eq_left htT, min_eq_left hsT,
        min_eq_right ht0, min_eq_right hs0]
      ring




theorem windowPartitionLinearInterpolant_strictMono {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) :
    StrictMono (windowPartitionLinearInterpolant p φ) := by
  let slopes : Fin p.n → ℝ := fun i => windowPartitionSecantSlope p φ i
  let S : Finset ℝ := Finset.univ.image slopes
  have hS : S.Nonempty := by
    refine ⟨slopes ⟨0, p.n_pos⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, p.n_pos⟩, Finset.mem_univ _, rfl⟩
  let c : ℝ := S.min' hS
  have hc_mem : c ∈ S := Finset.min'_mem S hS
  have hcpos : 0 < c := by
    rcases Finset.mem_image.mp hc_mem with ⟨i, _, hci⟩
    rw [← hci]
    exact windowPartitionSecantSlope_pos p φ i
  have hcle (i : Fin p.n) : c ≤ slopes i := by
    exact Finset.min'_le S _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  intro x y hxy
  let s : ℝ := x
  let t : ℝ := y
  let increment : Fin p.n → ℝ := fun i =>
    (min t (p.time i.succ : ℝ) - min t (p.time i.castSucc : ℝ)) -
      (min s (p.time i.succ : ℝ) - min s (p.time i.castSucc : ℝ))
  have hst : s < t := by exact_mod_cast hxy
  have hinc (i : Fin p.n) : 0 ≤ increment i := by
    apply windowPartition_clipped_increment_nonneg
    · exact (p.strict i).le
    · exact hst.le
  have hsuminc : ∑ i : Fin p.n, increment i = t - s := by
    exact windowPartition_interpolant_increment_sum p
      (by exact_mod_cast x.property.1)
      (by exact_mod_cast y.property.1)
      (by exact_mod_cast x.property.2)
      (by exact_mod_cast y.property.2)
  have hdiff :
      windowPartitionLinearInterpolant p φ y -
          windowPartitionLinearInterpolant p φ x =
        ∑ i : Fin p.n, slopes i * increment i := by
    rw [windowPartitionLinearInterpolant_def, windowPartitionLinearInterpolant_def,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [slopes, increment, s, t]
    ring
  have hsumle :
      (∑ i : Fin p.n, c * increment i) ≤
        ∑ i : Fin p.n, slopes i * increment i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hcle i) (hinc i)
  have hconstsum :
      (∑ i : Fin p.n, c * increment i) = c * (t - s) := by
    rw [← Finset.mul_sum, hsuminc]
  have hdiffpos :
      0 < windowPartitionLinearInterpolant p φ y -
        windowPartitionLinearInterpolant p φ x := by
    have hpos : 0 < c * (t - s) := mul_pos hcpos (sub_pos.mpr hst)
    calc
      0 < c * (t - s) := hpos
      _ ≤ windowPartitionLinearInterpolant p φ y -
          windowPartitionLinearInterpolant p φ x := by
        calc
          c * (t - s) = ∑ i : Fin p.n, c * increment i := hconstsum.symm
          _ ≤ ∑ i : Fin p.n, slopes i * increment i := hsumle
          _ = windowPartitionLinearInterpolant p φ y -
              windowPartitionLinearInterpolant p φ x := hdiff.symm
  exact sub_pos.mp hdiffpos



theorem windowPartitionLinearInterpolant_first_endpoint {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) :
    windowPartitionLinearInterpolant p φ
      (⟨0, le_rfl, hT.le⟩ : J1Window T) = 0 := by
  simpa only [p.first] using windowPartitionLinearInterpolant_first p φ

end DirectedDistances.Probability
