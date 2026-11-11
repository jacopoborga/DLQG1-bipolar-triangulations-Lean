/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowDCircReverse
public import DirectedDistances.Probability.SkorokhodJ1WindowInterpolantIso
public import DirectedDistances.Probability.SkorokhodJ1WindowDCirc

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.Probability




theorem windowPartitionLinearInterpolant_last_endpoint {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) :
    windowPartitionLinearInterpolant p φ
      (⟨T, hT.le, le_rfl⟩ : J1Window T) = T := by
  let top : J1Window T := ⟨T, hT.le, le_rfl⟩
  let k : Fin (p.n + 1) := Fin.last p.n
  have htime : p.time k = top := by
    simpa [top, k] using p.last
  have hφtop : φ top = top := by
    apply Subtype.ext
    have htop : top ≤ φ top := by
      obtain ⟨x, hx⟩ := φ.surjective top
      have hxle : x ≤ top := x.property.2
      have := φ.monotone hxle
      simpa [hx] using this
    exact le_antisymm (φ top).property.2 (by exact_mod_cast htop)
  calc
    windowPartitionLinearInterpolant p φ (⟨T, hT.le, le_rfl⟩ : J1Window T) =
        windowPartitionLinearInterpolant p φ (p.time k) := by rw [htime]
    _ = (φ (p.time k) : ℝ) := windowPartitionLinearInterpolant_node p φ k
    _ = T := by rw [htime, hφtop]




theorem windowPartitionLinearInterpolant_mem {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) (t : J1Window T) :
    windowPartitionLinearInterpolant p φ t ∈ Set.Icc 0 T := by
  let zero : J1Window T := ⟨0, le_rfl, hT.le⟩
  let top : J1Window T := ⟨T, hT.le, le_rfl⟩
  have hlow : windowPartitionLinearInterpolant p φ zero ≤
      windowPartitionLinearInterpolant p φ t :=
    (windowPartitionLinearInterpolant_strictMono p φ).monotone t.property.1
  have hhigh : windowPartitionLinearInterpolant p φ t ≤
      windowPartitionLinearInterpolant p φ top :=
    (windowPartitionLinearInterpolant_strictMono p φ).monotone t.property.2
  rw [show windowPartitionLinearInterpolant p φ zero = 0 by
    simpa [zero] using windowPartitionLinearInterpolant_first_endpoint p φ] at hlow
  rw [show windowPartitionLinearInterpolant p φ top = T by
    simpa [top] using windowPartitionLinearInterpolant_last_endpoint p φ] at hhigh
  exact ⟨hlow, hhigh⟩

private instance (T : ℝ) : PreconnectedSpace (J1Window T) :=
  Subtype.preconnectedSpace isPreconnected_Icc




theorem windowPartitionLinearInterpolant_range {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) :
    Set.range (windowPartitionLinearInterpolant p φ) = Set.Icc 0 T := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact windowPartitionLinearInterpolant_mem p φ t
  · intro hy
    let zero : J1Window T := ⟨0, le_rfl, hT.le⟩
    let top : J1Window T := ⟨T, hT.le, le_rfl⟩
    have hiv := intermediate_value_univ zero top
      (windowPartitionLinearInterpolant_continuous p φ)
    have hval : y ∈ Set.Icc (windowPartitionLinearInterpolant p φ zero)
        (windowPartitionLinearInterpolant p φ top) := by
      simpa [zero, top, windowPartitionLinearInterpolant_first_endpoint,
        windowPartitionLinearInterpolant_last_endpoint] using hy
    exact hiv hval




@[expose] noncomputable def windowPartitionInterpolantWindowMap {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) : J1Window T → J1Window T :=
  fun t => ⟨windowPartitionLinearInterpolant p φ t,
    windowPartitionLinearInterpolant_mem p φ t⟩




theorem windowPartitionInterpolantWindowMap_strictMono {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) :
    StrictMono (windowPartitionInterpolantWindowMap p φ) := by
  intro x y hxy
  exact windowPartitionLinearInterpolant_strictMono p φ hxy




theorem windowPartitionInterpolantWindowMap_surjective {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) :
    Function.Surjective (windowPartitionInterpolantWindowMap p φ) := by
  intro y
  have hy : (y : ℝ) ∈ Set.range (windowPartitionLinearInterpolant p φ) := by
    rw [windowPartitionLinearInterpolant_range]
    exact y.property
  rcases hy with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx




@[expose] noncomputable def windowPartitionInterpolantTimeChange {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) : J1TimeChange T :=
  StrictMono.orderIsoOfSurjective (windowPartitionInterpolantWindowMap p φ)
    (windowPartitionInterpolantWindowMap_strictMono p φ)
    (windowPartitionInterpolantWindowMap_surjective p φ)




theorem windowPartitionInterpolantTimeChange_apply {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) (t : J1Window T) :
    (windowPartitionInterpolantTimeChange p φ t : ℝ) =
      windowPartitionLinearInterpolant p φ t := by
  simp [windowPartitionInterpolantTimeChange, windowPartitionInterpolantWindowMap]




theorem windowPartitionInterpolantTimeChange_first {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) :
    windowPartitionInterpolantTimeChange p φ ⟨0, le_rfl, hT.le⟩ =
      (⟨0, le_rfl, hT.le⟩ : J1Window T) := by
  apply Subtype.ext
  rw [windowPartitionInterpolantTimeChange_apply,
    windowPartitionLinearInterpolant_first_endpoint]




theorem windowPartitionInterpolantTimeChange_last {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) :
    windowPartitionInterpolantTimeChange p φ ⟨T, hT.le, le_rfl⟩ =
      (⟨T, hT.le, le_rfl⟩ : J1Window T) := by
  apply Subtype.ext
  rw [windowPartitionInterpolantTimeChange_apply,
    windowPartitionLinearInterpolant_last_endpoint]

private theorem fin_sum_adjacent_sub_timeChange (n : ℕ) :
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

private theorem clipped_increment_nonneg_timeChange {a b s t : ℝ}
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

private theorem clipped_increment_sum_timeChange {T : ℝ} {hT : 0 < T}
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
    _ = f (Fin.last p.n) - f 0 := fin_sum_adjacent_sub_timeChange p.n f
    _ = t - s := by
      dsimp [f]
      simp only [p.last, p.first, Subtype.coe_mk]
      rw [min_eq_left htT, min_eq_left hsT,
        min_eq_right ht0, min_eq_right hs0]
      ring




noncomputable def windowPartitionInterpolantSlopeMax {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, p.n_pos⟩⟩)
    (fun i : Fin p.n => |Real.log (windowPartitionSecantSlope p φ i)|)




theorem windowPartitionInterpolantTimeChange_slopeNorm_le {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (φ : J1TimeChange T) :
    j1TimeChangeSlopeNorm (windowPartitionInterpolantTimeChange p φ) ≤
      ENNReal.ofReal (windowPartitionInterpolantSlopeMax p φ) := by
  classical
  let M : ℝ := windowPartitionInterpolantSlopeMax p φ
  have hmax (i : Fin p.n) :
      |Real.log (windowPartitionSecantSlope p φ i)| ≤ M := by
    dsimp [M, windowPartitionInterpolantSlopeMax]
    exact Finset.le_sup' (fun j : Fin p.n =>
      |Real.log (windowPartitionSecantSlope p φ j)|) (Finset.mem_univ i)
  unfold j1TimeChangeSlopeNorm
  apply iSup_le
  intro q
  let x : J1Window T := q.1.1
  let y : J1Window T := q.1.2
  let s : ℝ := x
  let t : ℝ := y
  have hst : s < t := by exact_mod_cast q.2
  let δ : Fin p.n → ℝ := fun i =>
    (min t (p.time i.succ : ℝ) - min t (p.time i.castSucc : ℝ)) -
      (min s (p.time i.succ : ℝ) - min s (p.time i.castSucc : ℝ))
  have hδ (i : Fin p.n) : 0 ≤ δ i := by
    apply clipped_increment_nonneg_timeChange
    · exact (p.strict i).le
    · exact hst.le
  have hsumδ : ∑ i : Fin p.n, δ i = t - s := by
    exact clipped_increment_sum_timeChange p
      (by exact_mod_cast x.property.1)
      (by exact_mod_cast y.property.1)
      (by exact_mod_cast x.property.2)
      (by exact_mod_cast y.property.2)
  have hdiff :
      windowPartitionLinearInterpolant p φ y -
          windowPartitionLinearInterpolant p φ x =
        ∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i := by
    rw [windowPartitionLinearInterpolant_def, windowPartitionLinearInterpolant_def,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [δ, s, t]
    ring
  have hden : 0 < t - s := sub_pos.mpr hst
  have hsumlo : Real.exp (-M) * (t - s) ≤
      ∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i := by
    have hslope (i : Fin p.n) :
        Real.exp (-M) ≤ windowPartitionSecantSlope p φ i := by
      have hlog := abs_le.mp (hmax i)
      exact (Real.le_log_iff_exp_le
        (windowPartitionSecantSlope_pos p φ i)).mp hlog.1
    calc
      Real.exp (-M) * (t - s) =
          ∑ i : Fin p.n, Real.exp (-M) * δ i := by
        rw [← hsumδ, Finset.mul_sum]
      _ ≤ ∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hslope i) (hδ i)
  have hsumhi :
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i) ≤
        Real.exp M * (t - s) := by
    have hslope (i : Fin p.n) :
        windowPartitionSecantSlope p φ i ≤ Real.exp M := by
      have hlog := abs_le.mp (hmax i)
      exact (Real.log_le_iff_le_exp
        (windowPartitionSecantSlope_pos p φ i)).mp hlog.2
    calc
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i) ≤
          ∑ i : Fin p.n, Real.exp M * δ i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hslope i) (hδ i)
      _ = Real.exp M * (t - s) := by
        rw [← Finset.mul_sum, hsumδ]
  have hnum_pos : 0 <
      ∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i := by
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hden) hsumlo
  have hratio_pos :
      0 < (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i) / (t - s) := by
    exact div_pos hnum_pos hden
  have hratio_lo : Real.exp (-M) ≤
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i) / (t - s) :=
    (le_div_iff₀ hden).2 hsumlo
  have hratio_hi :
      (∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i) / (t - s) ≤
        Real.exp M := (div_le_iff₀ hden).2 hsumhi
  have hloglo : -M ≤ Real.log
      ((∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i) / (t - s)) :=
    (Real.le_log_iff_exp_le hratio_pos).mpr hratio_lo
  have hloghi : Real.log
      ((∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i) / (t - s)) ≤ M :=
    (Real.log_le_iff_le_exp hratio_pos).mpr hratio_hi
  have hlogabs : |Real.log
      ((∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i) / (t - s))| ≤ M :=
    abs_le.mpr ⟨hloglo, hloghi⟩
  have hchord : j1ChordLogSlope (windowPartitionInterpolantTimeChange p φ) q =
      Real.log ((∑ i : Fin p.n, windowPartitionSecantSlope p φ i * δ i) / (t - s)) := by
    change Real.log (((windowPartitionInterpolantTimeChange p φ y : ℝ) -
      (windowPartitionInterpolantTimeChange p φ x : ℝ)) / (t - s)) = _
    rw [windowPartitionInterpolantTimeChange_apply,
      windowPartitionInterpolantTimeChange_apply, hdiff]
  rw [hchord]
  exact ENNReal.ofReal_le_ofReal hlogabs

end DirectedDistances.Probability
