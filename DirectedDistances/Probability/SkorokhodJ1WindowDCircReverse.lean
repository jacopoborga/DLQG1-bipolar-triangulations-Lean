/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1Window
public import DirectedDistances.Probability.SkorokhodModulus
public import DirectedDistances.Probability.SkorokhodJ1WindowDCirc
public import DirectedDistances.Probability.SkorokhodJ1WindowCompleteLemmas

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.Probability




@[expose] noncomputable def windowPartitionSecantSlope {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) (i : Fin p.n) : ℝ :=
  ((φ (p.time i.succ) : ℝ) - (φ (p.time i.castSucc) : ℝ)) /
    ((p.time i.succ : ℝ) - (p.time i.castSucc : ℝ))




theorem windowPartitionSecantSlope_def {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) (i : Fin p.n) :
    windowPartitionSecantSlope p φ i =
      ((φ (p.time i.succ) : ℝ) - (φ (p.time i.castSucc) : ℝ)) /
        ((p.time i.succ : ℝ) - (p.time i.castSucc : ℝ)) := rfl




theorem windowPartitionSecantSlope_pos {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) (i : Fin p.n) :
    0 < windowPartitionSecantSlope p φ i := by
  apply div_pos
  · apply sub_pos.mpr
    exact_mod_cast φ.strictMono (p.strict i)
  · exact sub_pos.mpr (p.strict i)









@[expose] noncomputable def windowPartitionLinearInterpolant {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) (t : J1Window T) : ℝ :=
  ∑ i : Fin p.n, windowPartitionSecantSlope p φ i *
    (min (t : ℝ) (p.time i.succ : ℝ) - min (t : ℝ) (p.time i.castSucc : ℝ))




theorem windowPartitionLinearInterpolant_def {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) (t : J1Window T) :
    windowPartitionLinearInterpolant p φ t =
      ∑ i : Fin p.n, windowPartitionSecantSlope p φ i *
        (min (t : ℝ) (p.time i.succ : ℝ) -
          min (t : ℝ) (p.time i.castSucc : ℝ)) := rfl




theorem windowPartitionLinearInterpolant_first {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) :
    windowPartitionLinearInterpolant p φ (p.time 0) = 0 := by
  simp only [windowPartitionLinearInterpolant, p.first]
  apply Finset.sum_eq_zero
  intro i hi
  rw [min_eq_left (by exact_mod_cast (p.time i.succ).property.1),
    min_eq_left (by exact_mod_cast (p.time i.castSucc).property.1)]
  ring

private theorem fin_sum_adjacent_sub (n : ℕ) :
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

private theorem windowPartition_time_strictMono {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) : StrictMono p.time := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact_mod_cast p.strict i




theorem windowPartitionLinearInterpolant_node {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) (k : Fin (p.n + 1)) :
    windowPartitionLinearInterpolant p φ (p.time k) = (φ (p.time k) : ℝ) := by
  classical
  let q : Fin (p.n + 1) → J1Window T := fun j =>
    ⟨min (p.time k : ℝ) (p.time j : ℝ),
      le_min (p.time k).property.1 (p.time j).property.1,
      (min_le_left _ _).trans (p.time k).property.2⟩
  have hqLast : q (Fin.last p.n) = p.time k := by
    apply Subtype.ext
    simp only [q, p.last]
    exact min_eq_left (p.time k).property.2
  have hqZero : q 0 = p.time 0 := by
    apply Subtype.ext
    simp only [q, p.first, Subtype.coe_mk]
    exact min_eq_right (p.time k).property.1
  have hterm (i : Fin p.n) :
      windowPartitionSecantSlope p φ i *
          (min (p.time k : ℝ) (p.time i.succ : ℝ) -
            min (p.time k : ℝ) (p.time i.castSucc : ℝ)) =
        (φ (q i.succ) : ℝ) - (φ (q i.castSucc) : ℝ) := by
    by_cases hik : i.val < k.val
    · have his : i.succ ≤ k :=
        Fin.le_iff_val_le_val.mpr (by simp; omega)
      have hil : i.castSucc ≤ k :=
        Fin.le_iff_val_le_val.mpr (by simp; omega)
      have hupper := (windowPartition_time_strictMono p).monotone his
      have hlower := (windowPartition_time_strictMono p).monotone hil
      have hupper' : (p.time i.succ : ℝ) ≤ (p.time k : ℝ) := by exact_mod_cast hupper
      have hlower' : (p.time i.castSucc : ℝ) ≤ (p.time k : ℝ) := by
        exact_mod_cast hlower
      have hqUpper : q i.succ = p.time i.succ := by
        apply Subtype.ext
        dsimp [q]
        exact min_eq_right hupper'
      have hqLower : q i.castSucc = p.time i.castSucc := by
        apply Subtype.ext
        dsimp [q]
        exact min_eq_right hlower'
      rw [min_eq_right hupper', min_eq_right hlower', hqUpper, hqLower]
      unfold windowPartitionSecantSlope
      have hgap : (p.time i.succ : ℝ) - (p.time i.castSucc : ℝ) ≠ 0 := by
        exact ne_of_gt (sub_pos.mpr (by exact_mod_cast p.strict i))
      field_simp [hgap]
    · have hki : k ≤ i.castSucc :=
        Fin.le_iff_val_le_val.mpr (by simp; omega)
      have his : k ≤ i.succ := le_trans hki (Fin.castSucc_le_succ i)
      have hlower := (windowPartition_time_strictMono p).monotone hki
      have hupper := (windowPartition_time_strictMono p).monotone his
      have hlower' : (p.time k : ℝ) ≤ (p.time i.castSucc : ℝ) := by
        exact_mod_cast hlower
      have hupper' : (p.time k : ℝ) ≤ (p.time i.succ : ℝ) := by
        exact_mod_cast hupper
      have hqUpper : q i.succ = p.time k := by
        apply Subtype.ext
        dsimp [q]
        exact min_eq_left hupper'
      have hqLower : q i.castSucc = p.time k := by
        apply Subtype.ext
        dsimp [q]
        exact min_eq_left hlower'
      rw [min_eq_left hupper', min_eq_left hlower', hqUpper, hqLower]
      simp
  have hsum :
      Finset.univ.sum (fun i : Fin p.n => windowPartitionSecantSlope p φ i *
          (min (p.time k : ℝ) (p.time i.succ : ℝ) -
            min (p.time k : ℝ) (p.time i.castSucc : ℝ))) =
        Finset.univ.sum (fun i : Fin p.n =>
          (φ (q i.succ) : ℝ) - (φ (q (Fin.castSucc i)) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hterm i
  have hφzero : φ (p.time 0) = ⟨0, ⟨le_rfl, hT.le⟩⟩ := by
    have hz : p.time 0 = (⟨0, ⟨le_rfl, hT.le⟩⟩ : J1Window T) := p.first
    rw [hz]
    let z : J1Window T := ⟨0, ⟨le_rfl, hT.le⟩⟩
    have hle : z ≤ φ.symm z := (φ.symm z).property.1
    have hφle : φ z ≤ z := by
      calc
        φ z ≤ φ (φ.symm z) := φ.monotone hle
        _ = z := φ.apply_symm_apply z
    exact Subtype.ext (le_antisymm hφle (φ z).property.1)
  change Finset.univ.sum (fun i : Fin p.n => windowPartitionSecantSlope p φ i *
    (min (p.time k : ℝ) (p.time i.succ : ℝ) -
      min (p.time k : ℝ) (p.time i.castSucc : ℝ))) = (φ (p.time k) : ℝ)
  calc
    Finset.univ.sum (fun i : Fin p.n => windowPartitionSecantSlope p φ i *
        (min (p.time k : ℝ) (p.time i.succ : ℝ) -
          min (p.time k : ℝ) (p.time i.castSucc : ℝ))) =
        Finset.univ.sum (fun i : Fin p.n =>
        (φ (q i.succ) : ℝ) - (φ (q (Fin.castSucc i)) : ℝ)) := hsum
    _ = (φ (q (Fin.last p.n)) : ℝ) - (φ (q 0) : ℝ) :=
      fin_sum_adjacent_sub p.n (fun j => (φ (q j) : ℝ))
    _ = (φ (p.time k) : ℝ) - (φ (p.time 0) : ℝ) := by rw [hqLast, hqZero]
    _ = (φ (p.time k) : ℝ) := by rw [hφzero]; simp

end DirectedDistances.Probability
