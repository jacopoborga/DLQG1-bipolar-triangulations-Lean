/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FlowLineTimes
meta import Lean.Elab.Tactic.Omega

/-! # Primed quadrant walk from its interval decomposition

This helper defines the corrected primed walk of `lem-quadrant-walk`
The `lem-quad-kmsw` missing-root convention C18 is not implemented here.
It uses the interval decomposition `eqn-quad-pre` and is not counted as a
formalization of either paper result. The unresolved source issue
the printed `S'_m` count. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open scoped Classical BigOperators

/-- The left endpoint time of the `k`th interval in `eqn-quad-pre`, using -/
@[expose] noncomputable def primedIntervalLeft (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) : ℕ :=
  walkNL (fun i => ω (i + 1)) h k

/-- The right endpoint time of the `k`th primed interval in `eqn-quad-pre`.
The interval itself has indices from `primedIntervalLeft` up to, but excluding, -/
@[expose] noncomputable def primedIntervalRight (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) : ℕ :=
  walkNR (fun i => ω (i + 1)) h (k + 1)

/-- The natural-number length of the `k`th interval in `eqn-quad-pre`.
The flow-line hit witnesses make this positive. -/
@[expose] noncomputable def primedIntervalWidth (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) : ℕ :=
  primedIntervalRight ω h k - primedIntervalLeft ω h k

/-- The number of primed codes preceding interval `k`, obtained by summing
the lengths of the preceding `eqn-quad-pre` intervals. -/
@[expose] noncomputable def primedIntervalBase (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, primedIntervalWidth ω h i

/-- Each primed interval has at least one code, by the right-hit witness. -/
theorem primedIntervalWidth_pos (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) :
    1 ≤ primedIntervalWidth ω h k := by
  have hgap := (walkNR_succ_spec (fun i => ω (i + 1)) h k).1
  unfold primedIntervalWidth primedIntervalRight primedIntervalLeft
  omega

theorem primedIntervalBase_zero (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    primedIntervalBase ω h 0 = 0 := by
  simp [primedIntervalBase]

theorem primedIntervalBase_succ (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) :
    primedIntervalBase ω h (k + 1) =
      primedIntervalBase ω h k + primedIntervalWidth ω h k := by
  simp [primedIntervalBase, Finset.sum_range_succ]

theorem primedIntervalBase_ge (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k : ℕ) :
    k ≤ primedIntervalBase ω h k := by
  induction k with
  | zero => simp [primedIntervalBase]
  | succ k ih =>
      rw [primedIntervalBase_succ]
      have hw := primedIntervalWidth_pos ω h k
      omega

theorem primedIntervalBase_mono (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) {k l : ℕ} (hkl : k ≤ l) :
    primedIntervalBase ω h k ≤ primedIntervalBase ω h l := by
  induction hkl with
  | refl => exact Nat.le_refl _
  | @step l hkl ih =>
      rw [primedIntervalBase_succ]
      have hw := primedIntervalWidth_pos ω h l
      omega

theorem primedIntervalIndex_exists (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    ∃ k, m < primedIntervalBase ω h (k + 1) := by
  refine ⟨m, ?_⟩
  exact lt_of_lt_of_le (Nat.lt_succ_self m) (primedIntervalBase_ge ω h (m + 1))

/-- The unique interval selected by the cumulative interval lengths. -/
@[expose] noncomputable def primedIntervalIndex (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) : ℕ :=
  Nat.find (primedIntervalIndex_exists ω h m)

theorem primedIntervalIndex_spec (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) :
    m < primedIntervalBase ω h (primedIntervalIndex ω h m + 1) := by
  change m < primedIntervalBase ω h
    (Nat.find (primedIntervalIndex_exists ω h m) + 1)
  exact Nat.find_spec (primedIntervalIndex_exists ω h m)

private theorem primedIntervalIndex_eq_of_mem (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k j : ℕ)
    (hj : j < primedIntervalWidth ω h k) :
    primedIntervalIndex ω h (primedIntervalBase ω h k + j) = k := by
  change Nat.find (primedIntervalIndex_exists ω h
    (primedIntervalBase ω h k + j)) = k
  let m := primedIntervalBase ω h k + j
  have hm : m < primedIntervalBase ω h (k + 1) := by
    rw [primedIntervalBase_succ]
    dsimp [m]
    omega
  let q := Nat.find (primedIntervalIndex_exists ω h m)
  have hfind_spec : m < primedIntervalBase ω h (q + 1) := by
    dsimp [q]
    exact Nat.find_spec (primedIntervalIndex_exists ω h m)
  have hfind_le : q ≤ k := by
    by_contra hnot
    have hmin := Nat.find_min (primedIntervalIndex_exists ω h m)
      (show k < Nat.find (primedIntervalIndex_exists ω h m) from by omega)
    exact hmin hm
  have hk_le : k ≤ q := by
    by_contra hnot
    have hbase : primedIntervalBase ω h (q + 1) ≤ primedIntervalBase ω h k :=
      primedIntervalBase_mono ω h (by omega)
    have hmk : primedIntervalBase ω h k ≤ m := by
      dsimp [m]
      omega
    exact (not_lt_of_ge (Nat.le_trans hbase hmk)) hfind_spec
  have heq : q = k := Nat.le_antisymm hfind_le hk_le
  simpa [q, m] using heq

/-- The corrected primed code stream, formed by concatenating the intervals
from `eqn-quad-pre`. Block `k` consists of the walk increments at the times
`n ∈ [L_k, R_k)` (the increment at time `n` is `w (n - 1)`). Its first entry,
the increment at time `L_k`, is replaced by code `1`, which is the step `(0,1)`;
this follows the replacement rule of `eqn-walk-quadrant'`
The increment at time `R_k` is not included, since that time belongs to the
hatted phase. This is an interval definition and makes no claim about the
is unresolved. The missing-root convention C18 is not implemented here. -/
@[expose] noncomputable def primedCode (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (m : ℕ) : Fin 3 := by
  let k := primedIntervalIndex ω h m
  let j := m - primedIntervalBase ω h k
  exact if j = 0 then 1 else ω (primedIntervalLeft ω h k + j - 1 + 1)

/-- The first primed code is `1`; by `lazyTwoDimensionalStep_primedCode_zero` -/
theorem primedCode_zero (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    primedCode ω h 0 = 1 := by
  rw [primedCode]
  have hidx : primedIntervalIndex ω h 0 = 0 := by
    change Nat.find (primedIntervalIndex_exists ω h 0) = 0
    let q := Nat.find (primedIntervalIndex_exists ω h 0)
    by_contra hq
    have hqpos : 0 < q := by dsimp [q]; omega
    have hmin := Nat.find_min (primedIntervalIndex_exists ω h 0)
      (show q - 1 < Nat.find (primedIntervalIndex_exists ω h 0) from by omega)
    have hnot : ¬ 0 < primedIntervalBase ω h q := by
      simpa [q, Nat.sub_add_cancel (show 1 ≤ q by omega)] using hmin
    have hge := primedIntervalBase_ge ω h q
    omega
  simp [hidx, primedIntervalBase_zero]



theorem lazyTwoDimensionalStep_primedCode_zero (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) :
    lazyTwoDimensionalStep (primedCode ω h 0) = (0, 1) := by
  rw [primedCode_zero]
  rfl

/-- On interval `k`, the `j`th code is the replacement code `1` (the step
`(0,1)`, rule of `eqn-walk-quadrant'`) when `j = 0`. Otherwise it is the
original increment at time `L_k + j`, namely `w (L_k + j - 1)` with
`w i = ω (i+1)`. The increment at time `R_k` is not part of the block -/
theorem primedCode_block (ω : ℕ → Fin 3)
    (h : HasFlowLineHits (fun i => ω (i + 1))) (k j : ℕ)
    (hj : j < primedIntervalWidth ω h k) :
    primedCode ω h (primedIntervalBase ω h k + j) =
      if j = 0 then 1 else
        (fun i => ω (i + 1)) (primedIntervalLeft ω h k + j - 1) := by
  rw [primedCode]
  simp only [primedIntervalIndex_eq_of_mem ω h k j hj, Nat.add_sub_cancel_left]

end DirectedDistances.KMSW
