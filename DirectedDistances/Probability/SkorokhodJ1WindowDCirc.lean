/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1Window
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.OrderClosed

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

/-! # Billingsley's complete Skorokhod metric on a finite window -/

@[expose] public section
namespace DirectedDistances.Probability

open Set
open Filter
open scoped ENNReal Topology

/-- The logarithmic chord slope of an increasing time change on an ordered pair. -/
noncomputable def j1ChordLogSlope {T : ℝ} (φ : J1TimeChange T)
    (p : {p : J1Window T × J1Window T // (p.1 : ℝ) < p.2}) : ℝ :=
  Real.log (((φ p.1.2 : ℝ) - (φ p.1.1 : ℝ)) /
    ((p.1.2 : ℝ) - (p.1.1 : ℝ)))






noncomputable def j1TimeChangeSlopeNorm {T : ℝ} (φ : J1TimeChange T) : ℝ≥0∞ :=
  ⨆ p : {p : J1Window T × J1Window T // (p.1 : ℝ) < p.2},
    ENNReal.ofReal |j1ChordLogSlope φ p|

/-- The identity time change has zero logarithmic slope norm. -/
theorem j1TimeChangeSlopeNorm_refl {T : ℝ} :
    j1TimeChangeSlopeNorm (OrderIso.refl (J1Window T)) = 0 := by
  simp [j1TimeChangeSlopeNorm, j1ChordLogSlope]

/-- Inversion preserves the logarithmic slope norm. -/
theorem j1TimeChangeSlopeNorm_symm {T : ℝ} (φ : J1TimeChange T) :
    j1TimeChangeSlopeNorm φ.symm = j1TimeChangeSlopeNorm φ := by
  apply le_antisymm
  · apply iSup_le
    intro p
    let q : {p : J1Window T × J1Window T // (p.1 : ℝ) < p.2} :=
      ⟨(φ.symm p.1.1, φ.symm p.1.2), φ.symm.strictMono p.2⟩
    have hnum : ((φ.symm p.1.2 : ℝ) - (φ.symm p.1.1 : ℝ)) ≠ 0 := by
      have hp := q.2
      exact ne_of_gt (sub_pos.mpr hp)
    have hden : ((p.1.2 : ℝ) - (p.1.1 : ℝ)) ≠ 0 :=
      ne_of_gt (sub_pos.mpr p.2)
    have hlog : j1ChordLogSlope φ.symm p = -j1ChordLogSlope φ q := by
      dsimp [j1ChordLogSlope, q]
      rw [φ.apply_symm_apply, φ.apply_symm_apply]
      rw [Real.log_div hnum hden, Real.log_div hden hnum]
      ring
    rw [hlog, abs_neg]
    exact le_iSup_of_le q le_rfl
  · apply iSup_le
    intro p
    let q : {p : J1Window T × J1Window T // (p.1 : ℝ) < p.2} :=
      ⟨(φ p.1.1, φ p.1.2), φ.strictMono p.2⟩
    have hlog : j1ChordLogSlope φ p = -j1ChordLogSlope φ.symm q := by
      dsimp [j1ChordLogSlope, q]
      rw [φ.symm_apply_apply, φ.symm_apply_apply]
      have hnum : ((φ p.1.2 : ℝ) - (φ p.1.1 : ℝ)) ≠ 0 :=
        ne_of_gt (sub_pos.mpr (φ.strictMono p.2))
      have hden : ((p.1.2 : ℝ) - (p.1.1 : ℝ)) ≠ 0 :=
        ne_of_gt (sub_pos.mpr p.2)
      rw [Real.log_div hnum hden, Real.log_div hden hnum]
      ring
    rw [hlog, abs_neg]
    exact le_iSup_of_le q le_rfl

/-- Composition is subadditive for the logarithmic slope norm. -/
theorem j1TimeChangeSlopeNorm_trans_le {T : ℝ} (φ ψ : J1TimeChange T) :
    j1TimeChangeSlopeNorm (φ.trans ψ) ≤
      j1TimeChangeSlopeNorm φ + j1TimeChangeSlopeNorm ψ := by
  apply iSup_le
  intro p
  let q : {p : J1Window T × J1Window T // (p.1 : ℝ) < p.2} :=
    ⟨(φ p.1.1, φ p.1.2), φ.strictMono p.2⟩
  have hφ : 0 < ((φ p.1.2 : ℝ) - (φ p.1.1 : ℝ)) :=
    sub_pos.mpr (φ.strictMono p.2)
  have hψ : 0 < ((ψ q.1.2 : ℝ) - (ψ q.1.1 : ℝ)) :=
    sub_pos.mpr (ψ.strictMono q.2)
  have hlog : j1ChordLogSlope (φ.trans ψ) p =
      j1ChordLogSlope φ p + j1ChordLogSlope ψ q := by
    dsimp [j1ChordLogSlope, q]
    have hbase :
        (((ψ (φ p.1.2) : ℝ) - (ψ (φ p.1.1) : ℝ)) /
          ((p.1.2 : ℝ) - (p.1.1 : ℝ))) =
        (((φ p.1.2 : ℝ) - (φ p.1.1 : ℝ)) /
          ((p.1.2 : ℝ) - (p.1.1 : ℝ))) *
        (((ψ (φ p.1.2) : ℝ) - (ψ (φ p.1.1) : ℝ)) /
          ((φ p.1.2 : ℝ) - (φ p.1.1 : ℝ))) := by
      field_simp
    rw [hbase,
      Real.log_mul (ne_of_gt (div_pos hφ (sub_pos.mpr p.2)))
        (ne_of_gt (div_pos hψ hφ))]
  rw [hlog]
  have habs : |j1ChordLogSlope φ p + j1ChordLogSlope ψ q| ≤
      |j1ChordLogSlope φ p| + |j1ChordLogSlope ψ q| := abs_add_le _ _
  have hleft := ENNReal.ofReal_le_ofReal habs
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)] at hleft
  exact hleft.trans (add_le_add
    (le_iSup_of_le p le_rfl) (le_iSup_of_le q le_rfl))

/-- The complete J1 cost associated with Billingsley's logarithmic slope norm. -/
noncomputable def j1WindowDCircCost {T : ℝ}
    (f g : CadlagWindow T) (φ : J1TimeChange T) : ℝ≥0∞ :=
  max (j1TimeChangeSlopeNorm φ)
    (ENNReal.ofReal (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|))






noncomputable def j1WindowDCirc {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) : ℝ≥0∞ :=
  let _ : Nonempty (J1Window T) := ⟨⟨0, ⟨le_rfl, hT.le⟩⟩⟩
  ⨅ φ : J1TimeChange T, j1WindowDCircCost f g φ

/-- Each complete-metric cost is nonnegative. -/
private theorem j1WindowDCircCost_nonneg {T : ℝ} (f g : CadlagWindow T)
    (φ : J1TimeChange T) : 0 ≤ j1WindowDCircCost f g φ := by
  exact bot_le

private theorem j1Window_nonempty_local {T : ℝ} (hT : 0 < T) :
    Nonempty (J1Window T) :=
  ⟨⟨0, ⟨le_rfl, hT.le⟩⟩⟩

private theorem j1WindowDCircCosts_bddBelow {T : ℝ}
    (f g : CadlagWindow T) :
    BddBelow (range fun φ : J1TimeChange T => j1WindowDCircCost f g φ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨φ, rfl⟩
  exact j1WindowDCircCost_nonneg f g φ

private theorem j1WindowDCircCost_comp_le {T : ℝ} (hT : 0 < T)
    (f g h : CadlagWindow T) (φ ψ : J1TimeChange T) :
    j1WindowDCircCost f h (ψ.trans φ) ≤
      j1WindowDCircCost f g φ + j1WindowDCircCost g h ψ := by
  let : Nonempty (J1Window T) := j1Window_nonempty_local hT
  have hφv := le_max_right (j1TimeChangeSlopeNorm φ)
    (ENNReal.ofReal (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|))
  have hψv := le_max_right (j1TimeChangeSlopeNorm ψ)
    (ENNReal.ofReal (⨆ t : J1Window T, |g.1 (ψ t) - h.1 t|))
  have hφs := le_max_left (j1TimeChangeSlopeNorm φ)
    (ENNReal.ofReal (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|))
  have hψs := le_max_left (j1TimeChangeSlopeNorm ψ)
    (ENNReal.ofReal (⨆ t : J1Window T, |g.1 (ψ t) - h.1 t|))
  have hsupφ := j1WindowValueError_bddAbove f g φ
  have hsupψ := j1WindowValueError_bddAbove g h ψ
  have hφnonneg : 0 ≤ ⨆ t : J1Window T, |f.1 (φ t) - g.1 t| := by
    exact le_ciSup_of_le hsupφ ⟨0, ⟨le_rfl, hT.le⟩⟩ (abs_nonneg _)
  have hψnonneg : 0 ≤ ⨆ t : J1Window T, |g.1 (ψ t) - h.1 t| := by
    exact le_ciSup_of_le hsupψ ⟨0, ⟨le_rfl, hT.le⟩⟩ (abs_nonneg _)
  have hval :
      (⨆ t : J1Window T, |f.1 (φ (ψ t)) - h.1 t|) ≤
        (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|) +
          (⨆ t : J1Window T, |g.1 (ψ t) - h.1 t|) := by
    apply ciSup_le
    intro t
    calc
      |f.1 (φ (ψ t)) - h.1 t| ≤
          |f.1 (φ (ψ t)) - g.1 (ψ t)| + |g.1 (ψ t) - h.1 t| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add
        (le_ciSup_of_le hsupφ (ψ t) le_rfl)
        (le_ciSup_of_le hsupψ t le_rfl)
  have hvalENN :
      ENNReal.ofReal (⨆ t : J1Window T, |f.1 (φ (ψ t)) - h.1 t|) ≤
        ENNReal.ofReal (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|) +
          ENNReal.ofReal (⨆ t : J1Window T, |g.1 (ψ t) - h.1 t|) := by
    calc
      _ ≤ ENNReal.ofReal
          ((⨆ t : J1Window T, |f.1 (φ t) - g.1 t|) +
            (⨆ t : J1Window T, |g.1 (ψ t) - h.1 t|)) := ENNReal.ofReal_le_ofReal hval
      _ = _ := by rw [ENNReal.ofReal_add hφnonneg hψnonneg]
  change max (j1TimeChangeSlopeNorm (ψ.trans φ))
      (ENNReal.ofReal (⨆ t : J1Window T, |f.1 (φ (ψ t)) - h.1 t|)) ≤
    max (j1TimeChangeSlopeNorm φ)
        (ENNReal.ofReal (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|)) +
      max (j1TimeChangeSlopeNorm ψ)
        (ENNReal.ofReal (⨆ t : J1Window T, |g.1 (ψ t) - h.1 t|))
  apply max_le
  · calc
      j1TimeChangeSlopeNorm (ψ.trans φ) ≤
          j1TimeChangeSlopeNorm ψ + j1TimeChangeSlopeNorm φ :=
        j1TimeChangeSlopeNorm_trans_le ψ φ
      _ = j1TimeChangeSlopeNorm φ + j1TimeChangeSlopeNorm ψ := add_comm _ _
      _ ≤ _ := add_le_add hφs hψs
  · exact hvalENN.trans (add_le_add hφv hψv)

/-- Composing near-minimizing time changes proves the complete J1 triangle inequality. -/
theorem j1WindowDCirc_triangle {T : ℝ} (hT : 0 < T)
    (f g h : CadlagWindow T) :
    j1WindowDCirc hT f h ≤ j1WindowDCirc hT f g + j1WindowDCirc hT g h := by
  let : Nonempty (J1Window T) := j1Window_nonempty_local hT
  let : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _htop
  let η : NNReal := ε / 2
  have hη : 0 < η := by dsimp [η]; exact div_pos hε (by norm_num)
  have hηenn : (0 : ℝ≥0∞) < (η : ℝ≥0∞) := ENNReal.coe_pos.mpr hη
  have hfgfin : j1WindowDCirc hT f g < ⊤ := by
    apply lt_of_le_of_lt _ _htop
    calc
      j1WindowDCirc hT f g = j1WindowDCirc hT f g + 0 := (add_zero _).symm
      _ ≤ j1WindowDCirc hT f g + j1WindowDCirc hT g h := add_le_add le_rfl bot_le
  have hghfin : j1WindowDCirc hT g h < ⊤ := by
    apply lt_of_le_of_lt _ _htop
    calc
      j1WindowDCirc hT g h = 0 + j1WindowDCirc hT g h := (zero_add _).symm
      _ ≤ j1WindowDCirc hT f g + j1WindowDCirc hT g h := add_le_add bot_le le_rfl
  have hfg_lt : j1WindowDCirc hT f g < j1WindowDCirc hT f g + (η : ℝ≥0∞) := by
    calc
      j1WindowDCirc hT f g = j1WindowDCirc hT f g + 0 := (add_zero _).symm
      _ < j1WindowDCirc hT f g + (η : ℝ≥0∞) :=
        ENNReal.add_lt_add_left (ne_top_of_lt hfgfin) hηenn
  have hgh_lt : j1WindowDCirc hT g h < j1WindowDCirc hT g h + (η : ℝ≥0∞) := by
    calc
      j1WindowDCirc hT g h = j1WindowDCirc hT g h + 0 := (add_zero _).symm
      _ < j1WindowDCirc hT g h + (η : ℝ≥0∞) :=
        ENNReal.add_lt_add_left (ne_top_of_lt hghfin) hηenn
  change (⨅ φ : J1TimeChange T, j1WindowDCircCost f g φ) < _ at hfg_lt
  change (⨅ ψ : J1TimeChange T, j1WindowDCircCost g h ψ) < _ at hgh_lt
  obtain ⟨φ, hφ⟩ := exists_lt_of_ciInf_lt hfg_lt
  obtain ⟨ψ, hψ⟩ := exists_lt_of_ciInf_lt hgh_lt
  change (⨅ θ : J1TimeChange T, j1WindowDCircCost f h θ) ≤ _
  apply le_of_lt
  calc
    (⨅ θ : J1TimeChange T, j1WindowDCircCost f h θ) ≤
        j1WindowDCircCost f h (ψ.trans φ) :=
      ciInf_le (j1WindowDCircCosts_bddBelow f h) (ψ.trans φ)
    _ ≤ j1WindowDCircCost f g φ + j1WindowDCircCost g h ψ :=
      j1WindowDCircCost_comp_le hT f g h φ ψ
    _ < (j1WindowDCirc hT f g + (η : ℝ≥0∞)) +
        (j1WindowDCirc hT g h + (η : ℝ≥0∞)) := by
      have hbasefin : j1WindowDCirc hT f g + (η : ℝ≥0∞) < ⊤ :=
        ENNReal.add_lt_top.mpr ⟨hfgfin, ENNReal.coe_lt_top⟩
      exact lt_trans
        (ENNReal.add_lt_add_right (ne_top_of_lt hψ) hφ)
        (ENNReal.add_lt_add_left (ne_top_of_lt hbasefin) hψ)
    _ ≤ j1WindowDCirc hT f g + j1WindowDCirc hT g h + ε := by
      have hηeq : (η : ℝ≥0∞) + (η : ℝ≥0∞) = (ε : ℝ≥0∞) := by
        rw [← ENNReal.coe_add]
        congr 1
        dsimp [η]
        ring
      have heq :
          (j1WindowDCirc hT f g + (η : ℝ≥0∞)) +
              (j1WindowDCirc hT g h + (η : ℝ≥0∞)) =
            j1WindowDCirc hT f g + j1WindowDCirc hT g h + ε := by
        calc
          (j1WindowDCirc hT f g + (η : ℝ≥0∞)) +
              (j1WindowDCirc hT g h + (η : ℝ≥0∞)) =
            j1WindowDCirc hT f g + j1WindowDCirc hT g h +
              ((η : ℝ≥0∞) + (η : ℝ≥0∞)) := by ac_rfl
          _ = _ := by rw [hηeq]
      exact le_of_eq heq

/-- The identity time change makes the complete J1 distance reflexive. -/
theorem j1WindowDCirc_self {T : ℝ} (hT : 0 < T) (f : CadlagWindow T) :
    j1WindowDCirc hT f f = 0 := by
  let : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
  let : Nonempty (J1Window T) := j1Window_nonempty_local hT
  apply le_antisymm
  · change (⨅ φ : J1TimeChange T, j1WindowDCircCost f f φ) ≤ 0
    calc
      (⨅ φ : J1TimeChange T, j1WindowDCircCost f f φ) ≤
          j1WindowDCircCost f f (OrderIso.refl _) :=
        ciInf_le (j1WindowDCircCosts_bddBelow f f) _
      _ = 0 := by
        change max (j1TimeChangeSlopeNorm (OrderIso.refl _))
          (ENNReal.ofReal (⨆ t : J1Window T, |f.1 t - f.1 t|)) = 0
        simp [j1TimeChangeSlopeNorm_refl]
  · exact le_ciInf (fun φ => bot_le)

private theorem j1WindowValueError_symm {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T)
    (φ : J1TimeChange T) :
    (⨆ t : J1Window T, |g.1 (φ.symm t) - f.1 t|) =
      ⨆ t : J1Window T, |f.1 (φ t) - g.1 t| := by
  let : Nonempty (J1Window T) := j1Window_nonempty_local hT
  apply le_antisymm
  · apply ciSup_le
    intro t
    have hpoint : |g.1 (φ.symm t) - f.1 t| ≤
        |f.1 (φ (φ.symm t)) - g.1 (φ.symm t)| := by
      rw [φ.apply_symm_apply]
      exact le_of_eq (abs_sub_comm _ _)
    exact le_ciSup_of_le (j1WindowValueError_bddAbove f g φ) (φ.symm t) hpoint
  · apply ciSup_le
    intro t
    have hpoint : |f.1 (φ t) - g.1 t| ≤
        |g.1 (φ.symm (φ t)) - f.1 (φ t)| := by
      rw [φ.symm_apply_apply]
      exact le_of_eq (abs_sub_comm _ _)
    exact le_ciSup_of_le (j1WindowValueError_bddAbove g f φ.symm) (φ t) hpoint

private theorem j1WindowDCircCost_symm {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T)
    (φ : J1TimeChange T) :
    j1WindowDCircCost g f φ.symm = j1WindowDCircCost f g φ := by
  unfold j1WindowDCircCost
  rw [j1TimeChangeSlopeNorm_symm, j1WindowValueError_symm hT]

/-- Inverting the time change proves symmetry of the complete J1 distance. -/
theorem j1WindowDCirc_symm {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) : j1WindowDCirc hT f g = j1WindowDCirc hT g f := by
  let : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
  apply le_antisymm
  · apply le_ciInf
    intro φ
    calc
      (⨅ ψ : J1TimeChange T, j1WindowDCircCost f g ψ) ≤
          j1WindowDCircCost f g φ.symm :=
        ciInf_le (j1WindowDCircCosts_bddBelow f g) _
      _ = j1WindowDCircCost g f φ := j1WindowDCircCost_symm hT g f φ
  · apply le_ciInf
    intro φ
    calc
      (⨅ ψ : J1TimeChange T, j1WindowDCircCost g f ψ) ≤
          j1WindowDCircCost g f φ.symm :=
        ciInf_le (j1WindowDCircCosts_bddBelow g f) _
      _ = j1WindowDCircCost f g φ := j1WindowDCircCost_symm hT f g φ

/-- The identity change bounds `d°` by the bounded value error. -/
theorem j1WindowDCirc_lt_top {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) : j1WindowDCirc hT f g < ⊤ := by
  let : Nonempty (J1TimeChange T) := ⟨OrderIso.refl _⟩
  let : Nonempty (J1Window T) := j1Window_nonempty_local hT
  have hbound := j1WindowValueError_bddAbove f g (OrderIso.refl _)
  obtain ⟨C, hC⟩ := hbound
  have hCnonneg : 0 ≤ C := by
    have h := hC ⟨⟨0, ⟨le_rfl, hT.le⟩⟩, rfl⟩
    exact (abs_nonneg _).trans h
  have hcost : j1WindowDCircCost f g (OrderIso.refl _) ≤ ENNReal.ofReal C := by
    apply max_le
    · simp [j1TimeChangeSlopeNorm_refl]
    · apply ENNReal.ofReal_le_ofReal
      apply ciSup_le
      intro t
      exact hC ⟨t, rfl⟩
  have hle : j1WindowDCirc hT f g ≤ ENNReal.ofReal C := by
    unfold j1WindowDCirc
    exact (ciInf_le (j1WindowDCircCosts_bddBelow f g) _).trans hcost
  exact hle.trans_lt ENNReal.ofReal_lt_top

/-- A finite logarithmic chord-slope norm controls time displacement. -/
theorem j1TimeChange_displacement_le {T : ℝ} (hT : 0 < T)
    (φ : J1TimeChange T)
    (hφ : j1TimeChangeSlopeNorm φ < ⊤)
    (t : J1Window T) :
    |(φ t : ℝ) - (t : ℝ)| ≤
      T * (Real.exp (j1TimeChangeSlopeNorm φ).toReal - 1) := by
  let zero : J1Window T := ⟨0, ⟨le_rfl, hT.le⟩⟩
  have hzero : φ zero = zero := by
    have hmin : zero ≤ φ.symm zero := by
      exact (φ.symm zero).property.1
    have hle : φ zero ≤ zero := by
      calc
        φ zero ≤ φ (φ.symm zero) := φ.monotone hmin
        _ = zero := φ.apply_symm_apply zero
    apply Subtype.ext
    exact le_antisymm hle (φ zero).property.1
  by_cases ht : (t : ℝ) = 0
  · have hteq : t = zero := Subtype.ext ht
    subst t
    have hfactor : 0 ≤ Real.exp (j1TimeChangeSlopeNorm φ).toReal - 1 := by
      have hp := Real.add_one_le_exp (j1TimeChangeSlopeNorm φ).toReal
      have hnonneg : 0 ≤ (j1TimeChangeSlopeNorm φ).toReal := ENNReal.toReal_nonneg
      linarith
    simpa [hzero] using (mul_nonneg hT.le hfactor)
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    let p : {p : J1Window T × J1Window T // (p.1 : ℝ) < p.2} :=
      ⟨(zero, t), by simpa [zero] using htpos⟩
    let x : ℝ := (φ t : ℝ) / (t : ℝ)
    have hφzero : φ zero < φ t := φ.strictMono htpos
    have hxpos : 0 < x := by
      dsimp [x]
      rw [hzero] at hφzero
      exact div_pos (by exact_mod_cast hφzero) htpos
    have hslope : j1ChordLogSlope φ p = Real.log x := by
      change Real.log (((φ t : ℝ) - (φ zero : ℝ)) /
        ((t : ℝ) - (zero : ℝ))) = Real.log ((φ t : ℝ) / (t : ℝ))
      rw [hzero]
      simp [zero]
    have hchord : ENNReal.ofReal |Real.log x| ≤ j1TimeChangeSlopeNorm φ := by
      rw [← hslope]
      exact le_iSup_of_le p le_rfl
    have habslog : |Real.log x| ≤ (j1TimeChangeSlopeNorm φ).toReal := by
      exact (ENNReal.ofReal_le_iff_le_toReal hφ.ne).mp hchord
    let a : ℝ := (j1TimeChangeSlopeNorm φ).toReal
    have ha : 0 ≤ a := ENNReal.toReal_nonneg
    have hlogbounds : -a ≤ Real.log x ∧ Real.log x ≤ a := by
      have h := (abs_le.mp habslog)
      exact ⟨by simpa [a] using h.1, by simpa [a] using h.2⟩
    have hxupper : x ≤ Real.exp a :=
      (Real.log_le_iff_le_exp hxpos).mp hlogbounds.2
    have hxlower : Real.exp (-a) ≤ x :=
      (Real.le_log_iff_exp_le hxpos).mp hlogbounds.1
    have hsum : 2 ≤ Real.exp a + Real.exp (-a) := by
      have hp := Real.add_one_le_exp a
      have hm := Real.add_one_le_exp (-a)
      nlinarith
    have hlower : 1 - x ≤ Real.exp a - 1 := by
      have haux : 1 - Real.exp (-a) ≤ Real.exp a - 1 := by linarith
      linarith
    have hupper : x - 1 ≤ Real.exp a - 1 := by linarith
    have habsdiff : |x - 1| ≤ Real.exp a - 1 := abs_le.mpr ⟨by linarith, hupper⟩
    have hdiff : (φ t : ℝ) - (t : ℝ) = (t : ℝ) * (x - 1) := by
      dsimp [x]
      field_simp
    rw [hdiff, abs_mul, abs_of_pos htpos]
    have hefactor : 0 ≤ Real.exp a - 1 := by
      have hp := Real.add_one_le_exp a
      linarith
    calc
      (t : ℝ) * |x - 1| ≤ (t : ℝ) * (Real.exp a - 1) :=
        mul_le_mul_of_nonneg_left habsdiff htpos.le
      _ ≤ T * (Real.exp a - 1) :=
        mul_le_mul_of_nonneg_right t.property.2 hefactor

/-- An explicit epsilon-slack comparison of the usual J1 distance with `d°`.
The zero-slack comparison follows by letting `ε` tend to zero. -/
theorem j1WindowDist_le_dCirc_add_eps {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) (ε : ℝ) (hε : 0 < ε) :
    j1WindowDist hT f g ≤
      max (T * (Real.exp ((j1WindowDCirc hT f g).toReal + ε) - 1))
        ((j1WindowDCirc hT f g).toReal + ε) := by
  let d : ℝ≥0∞ := j1WindowDCirc hT f g
  let δ : ℝ≥0∞ := ENNReal.ofReal ε
  have hd : d < ⊤ := by
    dsimp [d]
    exact j1WindowDCirc_lt_top hT f g
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact ENNReal.ofReal_pos.mpr hε
  have hδtop : δ < ⊤ := by
    dsimp [δ]
    exact ENNReal.ofReal_lt_top
  have hsumtop : d + δ < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨hd, hδtop⟩
  have hnear : d < d + δ := by
    calc
      d = d + 0 := (add_zero _).symm
      _ < d + δ := ENNReal.add_lt_add_left hd.ne hδpos
  have hnear' : (⨅ φ : J1TimeChange T, j1WindowDCircCost f g φ) < d + δ := by
    simpa [d, j1WindowDCirc] using hnear
  obtain ⟨φ, hφ⟩ := exists_lt_of_ciInf_lt hnear'
  have hcost : j1WindowDCircCost f g φ ≤ d + δ := le_of_lt hφ
  have hnorm : j1TimeChangeSlopeNorm φ ≤ d + δ :=
    (le_max_left _ _).trans hcost
  have hnormtop : j1TimeChangeSlopeNorm φ < ⊤ :=
    lt_of_le_of_lt hnorm hsumtop
  have hnormreal : (j1TimeChangeSlopeNorm φ).toReal ≤ d.toReal + ε := by
    calc
      (j1TimeChangeSlopeNorm φ).toReal ≤ (d + δ).toReal :=
        ENNReal.toReal_mono hsumtop.ne hnorm
      _ = d.toReal + ε := by
        rw [ENNReal.toReal_add hd.ne (ne_of_lt ENNReal.ofReal_lt_top)]
        simp [ENNReal.toReal_ofReal hε.le]
  have hvalueENN :
      ENNReal.ofReal (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|) ≤ d + δ :=
    (le_max_right _ _).trans hcost
  have hvalue :
      (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|) ≤ d.toReal + ε := by
    let : Nonempty (J1Window T) := j1Window_nonempty_local hT
    have hbdd := j1WindowValueError_bddAbove f g φ
    calc
      (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|) ≤ (d + δ).toReal := by
        exact (ENNReal.ofReal_le_iff_le_toReal hsumtop.ne).mp hvalueENN
      _ = d.toReal + ε := by
        rw [ENNReal.toReal_add hd.ne (ne_of_lt ENNReal.ofReal_lt_top)]
        simp [ENNReal.toReal_ofReal hε.le]
  have hdisplacement :
      (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|) ≤
        T * (Real.exp (d.toReal + ε) - 1) := by
    let : Nonempty (J1Window T) := j1Window_nonempty_local hT
    apply ciSup_le
    intro t
    have hpoint := j1TimeChange_displacement_le hT φ hnormtop t
    have hexp : Real.exp (j1TimeChangeSlopeNorm φ).toReal ≤
        Real.exp (d.toReal + ε) :=
      Real.exp_le_exp.mpr hnormreal
    have hfactor : Real.exp (j1TimeChangeSlopeNorm φ).toReal - 1 ≤
        Real.exp (d.toReal + ε) - 1 := sub_le_sub_right hexp 1
    exact hpoint.trans (mul_le_mul_of_nonneg_left hfactor hT.le)
  have hcostbound :
      max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
          (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|) ≤
        max (T * (Real.exp (d.toReal + ε) - 1)) (d.toReal + ε) :=
    max_le (hdisplacement.trans (le_max_left _ _))
      (hvalue.trans (le_max_right _ _))
  change (⨅ ψ : J1TimeChange T,
      max (⨆ t : J1Window T, |((ψ t : ℝ) - (t : ℝ))|)
        (⨆ t : J1Window T, |f.1 (ψ t) - g.1 t|)) ≤ _
  calc
    (⨅ ψ : J1TimeChange T,
        max (⨆ t : J1Window T, |((ψ t : ℝ) - (t : ℝ))|)
          (⨆ t : J1Window T, |f.1 (ψ t) - g.1 t|)) ≤
        max (⨆ t : J1Window T, |((φ t : ℝ) - (t : ℝ))|)
          (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|) :=
      (ciInf_le ⟨0, by
        rintro _ ⟨ψ, rfl⟩
        exact le_max_of_le_left
          (le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove ψ)
            ⟨0, ⟨le_rfl, hT.le⟩⟩ (abs_nonneg _))⟩ φ)
    _ ≤ max (T * (Real.exp (d.toReal + ε) - 1)) (d.toReal + ε) := hcostbound

/-- Letting the slack decrease to zero gives the exact comparison with `d°`. -/
theorem j1WindowDist_le_dCirc {T : ℝ} (hT : 0 < T)
    (f g : CadlagWindow T) :
    j1WindowDist hT f g ≤
      max (T * (Real.exp (j1WindowDCirc hT f g).toReal - 1))
        (j1WindowDCirc hT f g).toReal := by
  let d : ℝ := (j1WindowDCirc hT f g).toReal
  let bound : ℝ → ℝ := fun x => max (T * (Real.exp x - 1)) x
  have hbound_cont : Continuous bound := by
    dsimp [bound]
    exact (continuous_const.mul (Real.continuous_exp.sub continuous_const)).max
      continuous_id
  have harg : Tendsto (fun n : ℕ => d + (1 / (n + 1 : ℝ))) atTop (𝓝 d) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := d)).add
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimit : Tendsto (fun n : ℕ => bound (d + (1 / (n + 1 : ℝ))))
      atTop (𝓝 (bound d)) :=
    hbound_cont.continuousAt.tendsto.comp harg
  have hle : ∀ᶠ n : ℕ in atTop,
      j1WindowDist hT f g ≤ bound (d + (1 / (n + 1 : ℝ))) := by
    filter_upwards [Filter.Eventually.of_forall fun n =>
      j1WindowDist_le_dCirc_add_eps hT f g (1 / (n + 1 : ℝ)) (by positivity)]
    intro n hn
    simpa [bound, d] using hn
  have hresult := ge_of_tendsto hlimit hle
  simpa [bound, d] using hresult

end DirectedDistances.Probability
