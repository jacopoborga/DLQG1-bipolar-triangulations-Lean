/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.Cadlag
public import Mathlib.Topology.Order.MonotoneContinuity

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Skorokhod J1 distance on a finite window -/

@[expose] public section
namespace DirectedDistances.Probability

open Bornology Set

/-- The closed time window `[0,T]`. -/
abbrev J1Window (T : ℝ) := Set.Icc (0 : ℝ) T

/-- Real-valued càdlàg paths on a finite window. -/
abbrev CadlagWindow (T : ℝ) := {f : J1Window T → ℝ // IsCadlag f}

/-- Increasing bijective time changes of a finite window. -/
abbrev J1TimeChange (T : ℝ) := OrderIso (J1Window T) (J1Window T)

/-- Helper toward E-STABLE / thm-busemann-conv
heavy-tailed functional CLT): the Skorokhod J1 distance on càdlàg paths over a
finite window `[0,T]` and its pseudometric properties (Billingsley,
Convergence of Probability Measures, 2nd ed., §12); no completeness, local
separability, Billingsley's complete metric `d°`, local `D(ℝ)` topology,
tightness, or functional convergence is claimed; not the paper result. -/
noncomputable def j1WindowDist {T : ℝ} (_hT : 0 < T)
    (f g : CadlagWindow T) : ℝ :=
  ⨅ φ : J1TimeChange T,
    max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
        (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|)

private noncomputable def j1WindowCost {T : ℝ}
    (f g : CadlagWindow T) (φ : J1TimeChange T) : ℝ :=
  max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
    (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|)

private theorem j1Window_nonempty {T : ℝ} (hT : 0 < T) :
    Nonempty (J1Window T) :=
  ⟨⟨0, ⟨le_rfl, hT.le⟩⟩⟩

private theorem j1Window_compactSpace {T : ℝ} : CompactSpace (J1Window T) := by
  exact compactSpace_Icc 0 T

/-- The time displacement of a time change is bounded on the window. -/
theorem j1WindowTimeChangeDistortion_bddAbove {T : ℝ}
    (φ : J1TimeChange T) :
    BddAbove (range fun t : J1Window T => |((φ t : ℝ) - (t : ℝ))|) := by
  refine ⟨T, ?_⟩
  rintro _ ⟨t, rfl⟩
  have ht := t.property
  have hφt := (φ t).property
  simp only [mem_Icc] at ht hφt
  rw [abs_le]
  constructor <;> linarith

/-- Càdlàg paths are bounded on the compact window, so each value-error
supremum in the J1 cost is bounded above. -/
theorem j1WindowValueError_bddAbove {T : ℝ}
    (f g : CadlagWindow T) (φ : J1TimeChange T) :
    BddAbove (range fun t : J1Window T => |f.1 (φ t) - g.1 t|) := by
  let : CompactSpace (J1Window T) := j1Window_compactSpace
  have hfbd := isBounded_image_of_isCadlag_of_isCompact f.2 isCompact_univ
  have hgbd := isBounded_image_of_isCadlag_of_isCompact g.2 isCompact_univ
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (hfbd.union hgbd)
  refine ⟨C, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hft : f.1 (φ t) ∈ f.1 '' (univ : Set (J1Window T)) :=
    ⟨φ t, mem_univ _, rfl⟩
  have hgt : g.1 t ∈ g.1 '' (univ : Set (J1Window T)) :=
    ⟨t, mem_univ _, rfl⟩
  have hfg : dist (f.1 (φ t)) (g.1 t) ≤ C :=
    hC (Or.inl hft) (Or.inr hgt)
  simpa only [Real.dist_eq] using hfg

private theorem j1WindowCost_nonneg {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) (φ : J1TimeChange T) :
    0 ≤ j1WindowCost f g φ := by
  let : Nonempty (J1Window T) := j1Window_nonempty hT
  have hd := j1WindowTimeChangeDistortion_bddAbove φ
  apply le_max_of_le_left
  exact le_ciSup_of_le hd ⟨0, ⟨le_rfl, hT.le⟩⟩ (abs_nonneg _)

private theorem j1WindowCosts_bddBelow {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) :
    BddBelow (range fun φ : J1TimeChange T => j1WindowCost f g φ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨φ, rfl⟩
  exact j1WindowCost_nonneg hT f g φ

/-- The J1 window distance is nonnegative. -/
theorem j1WindowDist_nonneg {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) : 0 ≤ j1WindowDist hT f g := by
  let : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
  change 0 ≤ ⨅ φ : J1TimeChange T, j1WindowCost f g φ
  apply le_ciInf
  intro φ
  exact j1WindowCost_nonneg hT f g φ

/-- The identity time change proves reflexivity of the J1 window distance. -/
theorem j1WindowDist_self {T : ℝ} (hT : 0 < T)
    (f : CadlagWindow T) : j1WindowDist hT f f = 0 := by
  let : Nonempty (J1Window T) := j1Window_nonempty hT
  apply le_antisymm
  · let : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
    change (⨅ φ : J1TimeChange T, j1WindowCost f f φ) ≤ 0
    have hid : j1WindowCost f f (OrderIso.refl _) = 0 := by
      simp [j1WindowCost]
    calc
      (⨅ φ : J1TimeChange T, j1WindowCost f f φ) ≤
          j1WindowCost f f (OrderIso.refl _) :=
        ciInf_le (j1WindowCosts_bddBelow hT f f) (OrderIso.refl _)
      _ = 0 := hid
  · exact j1WindowDist_nonneg hT f f

/-- Order-isomorphism time changes are continuous on the order topology of the window. -/
theorem j1TimeChange_continuous {T : ℝ} (φ : J1TimeChange T) : Continuous φ :=
  OrderIso.continuous φ

/-- An order-isomorphism time change is a homeomorphism of the window. -/
def j1TimeChange_homeomorph {T : ℝ} (φ : J1TimeChange T) :
    J1Window T ≃ₜ J1Window T :=
  φ.toHomeomorph

private theorem j1WindowCost_inverse_le {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) (φ : J1TimeChange T) :
    j1WindowCost g f φ.symm ≤ j1WindowCost f g φ := by
  let : Nonempty (J1Window T) := j1Window_nonempty hT
  apply max_le
  · apply ciSup_le
    intro t
    have hpoint : |((φ.symm t : ℝ) - (t : ℝ))| ≤
        |((φ (φ.symm t) : ℝ) - (φ.symm t : ℝ))| := by
      rw [φ.apply_symm_apply]
      exact le_of_eq (abs_sub_comm _ _)
    exact (le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove φ)
      (φ.symm t) hpoint).trans (le_max_left _ _)
  · apply ciSup_le
    intro t
    have hpoint : |g.1 (φ.symm t) - f.1 t| ≤
        |f.1 (φ (φ.symm t)) - g.1 (φ.symm t)| := by
      rw [φ.apply_symm_apply]
      exact le_of_eq (abs_sub_comm _ _)
    exact (le_ciSup_of_le (j1WindowValueError_bddAbove f g φ)
      (φ.symm t) hpoint).trans (le_max_right _ _)

/-- Inverting a time change proves symmetry of the J1 window distance. -/
theorem j1WindowDist_symm {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) : j1WindowDist hT f g = j1WindowDist hT g f := by
  let : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
  apply le_antisymm
  · change (⨅ φ : J1TimeChange T, j1WindowCost f g φ) ≤
      ⨅ φ : J1TimeChange T, j1WindowCost g f φ
    apply le_ciInf
    intro φ
    calc
      (⨅ ψ : J1TimeChange T, j1WindowCost f g ψ) ≤
          j1WindowCost f g φ.symm :=
        ciInf_le (j1WindowCosts_bddBelow hT f g) φ.symm
      _ ≤ j1WindowCost g f φ := j1WindowCost_inverse_le hT g f φ
  · change (⨅ φ : J1TimeChange T, j1WindowCost g f φ) ≤
      ⨅ φ : J1TimeChange T, j1WindowCost f g φ
    apply le_ciInf
    intro φ
    calc
      (⨅ ψ : J1TimeChange T, j1WindowCost g f ψ) ≤
          j1WindowCost g f φ.symm :=
        ciInf_le (j1WindowCosts_bddBelow hT g f) φ.symm
      _ ≤ j1WindowCost f g φ := j1WindowCost_inverse_le hT f g φ

private theorem j1WindowCost_comp_le {T : ℝ} (hT : 0 < T)
    (f g h : CadlagWindow T) (φ ψ : J1TimeChange T) :
    j1WindowCost f h (ψ.trans φ) ≤
      j1WindowCost f g φ + j1WindowCost g h ψ := by
  let : Nonempty (J1Window T) := j1Window_nonempty hT
  have hφd :
      (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|) ≤ j1WindowCost f g φ :=
    le_max_left _ _
  have hφv :
      (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|) ≤ j1WindowCost f g φ :=
    le_max_right _ _
  have hψd :
      (⨆ t : J1Window T, |((ψ t : ℝ) - (t : ℝ))|) ≤ j1WindowCost g h ψ :=
    le_max_left _ _
  have hψv :
      (⨆ t : J1Window T, |g.1 (ψ t) - h.1 t|) ≤ j1WindowCost g h ψ :=
    le_max_right _ _
  change max (⨆ t : J1Window T, |((φ (ψ t) : ℝ) - (t : ℝ))|)
      (⨆ t : J1Window T, |f.1 (φ (ψ t)) - h.1 t|) ≤ _
  apply max_le
  · apply ciSup_le
    intro t
    calc
      |(φ (ψ t) : ℝ) - (t : ℝ)| ≤
          |(φ (ψ t) : ℝ) - (ψ t : ℝ)| + |(ψ t : ℝ) - (t : ℝ)| :=
        abs_sub_le _ _ _
      _ ≤ j1WindowCost f g φ + j1WindowCost g h ψ :=
        add_le_add
          ((le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove φ) (ψ t)
            le_rfl).trans hφd)
          ((le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove ψ) t
            le_rfl).trans hψd)
  · apply ciSup_le
    intro t
    calc
      |f.1 (φ (ψ t)) - h.1 t| ≤
          |f.1 (φ (ψ t)) - g.1 (ψ t)| + |g.1 (ψ t) - h.1 t| :=
        abs_sub_le _ _ _
      _ ≤ j1WindowCost f g φ + j1WindowCost g h ψ :=
        add_le_add
          ((le_ciSup_of_le (j1WindowValueError_bddAbove f g φ) (ψ t)
            le_rfl).trans hφv)
          ((le_ciSup_of_le (j1WindowValueError_bddAbove g h ψ) t
            le_rfl).trans hψv)

/-- Composing near-minimizing time changes proves the triangle inequality. -/
theorem j1WindowDist_triangle {T : ℝ} (hT : 0 < T)
    (f g h : CadlagWindow T) :
    j1WindowDist hT f h ≤ j1WindowDist hT f g + j1WindowDist hT g h := by
  let : Nonempty (J1Window T) := j1Window_nonempty hT
  let : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
  by_contra hnot
  have hgap : j1WindowDist hT f g + j1WindowDist hT g h <
      j1WindowDist hT f h := lt_of_not_ge hnot
  let ε := (j1WindowDist hT f h -
    (j1WindowDist hT f g + j1WindowDist hT g h)) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hfg_lt : j1WindowDist hT f g < j1WindowDist hT f g + ε :=
    lt_add_of_pos_right _ hε
  have hgh_lt : j1WindowDist hT g h < j1WindowDist hT g h + ε :=
    lt_add_of_pos_right _ hε
  obtain ⟨φ, hφ⟩ := exists_lt_of_ciInf_lt hfg_lt
  obtain ⟨ψ, hψ⟩ := exists_lt_of_ciInf_lt hgh_lt
  have hcost : j1WindowDist hT f h <
      j1WindowDist hT f g + j1WindowDist hT g h + 2 * ε := by
    change (⨅ θ : J1TimeChange T, j1WindowCost f h θ) < _
    calc
      (⨅ θ : J1TimeChange T, j1WindowCost f h θ) ≤
          j1WindowCost f h (ψ.trans φ) :=
        ciInf_le (j1WindowCosts_bddBelow hT f h) (ψ.trans φ)
      _ ≤ j1WindowCost f g φ + j1WindowCost g h ψ :=
        j1WindowCost_comp_le hT f g h φ ψ
      _ < (j1WindowDist hT f g + ε) + (j1WindowDist hT g h + ε) :=
        add_lt_add hφ hψ
      _ = j1WindowDist hT f g + j1WindowDist hT g h + 2 * ε := by ring
  have hfinal :
      j1WindowDist hT f g + j1WindowDist hT g h + 2 * ε < j1WindowDist hT f h := by
    dsimp [ε]
    linarith
  linarith

/-- The identity time change bounds J1 distance by the uniform distance. -/
theorem j1WindowDist_le_sup_dist {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) :
    j1WindowDist hT f g ≤ ⨆ t : J1Window T, |f.1 t - g.1 t| := by
  let : Nonempty (J1Window T) := j1Window_nonempty hT
  let : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
  have hsup_nonneg : 0 ≤ ⨆ t : J1Window T, |f.1 t - g.1 t| := by
    apply le_ciSup_of_le
      (j1WindowValueError_bddAbove f g (OrderIso.refl _))
      ⟨0, ⟨le_rfl, hT.le⟩⟩
    exact abs_nonneg _
  change (⨅ φ : J1TimeChange T, j1WindowCost f g φ) ≤ _
  calc
    (⨅ φ : J1TimeChange T, j1WindowCost f g φ) ≤
        j1WindowCost f g (OrderIso.refl _) :=
      ciInf_le (j1WindowCosts_bddBelow hT f g) (OrderIso.refl _)
    _ = ⨆ t : J1Window T, |f.1 t - g.1 t| := by
      simp [j1WindowCost, hsup_nonneg]

end DirectedDistances.Probability
