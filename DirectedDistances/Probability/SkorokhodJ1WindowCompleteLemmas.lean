/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.Probability.SkorokhodJ1WindowDCirc
public import Mathlib.Topology.UniformSpace.UniformConvergence

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.OrderClosed

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

@[expose] public section
namespace DirectedDistances.Probability

open Filter
open scoped ENNReal Topology Uniformity




theorem j1TimeChange_lipschitz_bounds {T : ℝ} (φ : J1TimeChange T)
    (hφ : j1TimeChangeSlopeNorm φ < ⊤) (s t : J1Window T) :
    let a := (j1TimeChangeSlopeNorm φ).toReal
    Real.exp (-a) * |(t : ℝ) - s| ≤ |(φ t : ℝ) - φ s| ∧
      |(φ t : ℝ) - φ s| ≤ Real.exp a * |(t : ℝ) - s| := by
  dsimp only
  have hstrict (x y : J1Window T) (hxy : (x : ℝ) < y) :
      Real.exp (-((j1TimeChangeSlopeNorm φ).toReal)) *
          ((y : ℝ) - x) ≤ (φ y : ℝ) - φ x ∧
        (φ y : ℝ) - φ x ≤
          Real.exp ((j1TimeChangeSlopeNorm φ).toReal) * ((y : ℝ) - x) := by
    let p : {p : J1Window T × J1Window T // (p.1 : ℝ) < p.2} := ⟨(x, y), hxy⟩
    let q : ℝ := (((φ y : ℝ) - (φ x : ℝ)) / ((y : ℝ) - (x : ℝ)))
    have hden : 0 < (y : ℝ) - x := sub_pos.mpr hxy
    have hmono : (φ x : ℝ) < (φ y : ℝ) := by
      exact_mod_cast φ.strictMono hxy
    have hnum : 0 < (φ y : ℝ) - (φ x : ℝ) := sub_pos.mpr hmono
    have hq : 0 < q := div_pos hnum hden
    have hslope : j1ChordLogSlope φ p = Real.log q := by
      simp [j1ChordLogSlope, p, q]
    have hnorm : ENNReal.ofReal |Real.log q| ≤ j1TimeChangeSlopeNorm φ := by
      rw [← hslope]
      exact le_iSup_of_le p le_rfl
    have habs : |Real.log q| ≤ (j1TimeChangeSlopeNorm φ).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hφ.ne).mp hnorm
    have hlog : -((j1TimeChangeSlopeNorm φ).toReal) ≤ Real.log q ∧
        Real.log q ≤ (j1TimeChangeSlopeNorm φ).toReal := abs_le.mp habs
    have hqlo : Real.exp (-((j1TimeChangeSlopeNorm φ).toReal)) ≤ q :=
      (Real.le_log_iff_exp_le hq).mp hlog.1
    have hqhi : q ≤ Real.exp ((j1TimeChangeSlopeNorm φ).toReal) :=
      (Real.log_le_iff_le_exp hq).mp hlog.2
    constructor
    · have := mul_le_mul_of_nonneg_right hqlo hden.le
      have hratio : q * ((y : ℝ) - x) = (φ y : ℝ) - φ x := by
        dsimp [q]
        field_simp
      rw [hratio] at this
      exact this
    · have := mul_le_mul_of_nonneg_right hqhi hden.le
      have hratio : q * ((y : ℝ) - x) = (φ y : ℝ) - φ x := by
        dsimp [q]
        field_simp
      rw [hratio] at this
      exact this
  by_cases hst : (s : ℝ) < t
  · have h := hstrict s t hst
    have hmono : (φ s : ℝ) < (φ t : ℝ) := by
      exact_mod_cast φ.strictMono hst
    simpa only [abs_of_pos (sub_pos.mpr hst), abs_of_pos (sub_pos.mpr hmono)] using h
  · by_cases hts : (t : ℝ) < s
    · have h := hstrict t s hts
      have hφts : (φ t : ℝ) < (φ s : ℝ) := by
        exact_mod_cast φ.strictMono hts
      rw [abs_of_neg (sub_neg.mpr hts), abs_of_neg (sub_neg.mpr hφts)]
      simpa only [neg_sub] using h
    · have hst' : (s : ℝ) = t := le_antisymm (le_of_not_gt hts) (le_of_not_gt hst)
      have hsub : s = t := Subtype.ext hst'
      subst t
      simp




theorem isCadlag_of_tendstoUniformly {F : ℕ → J1Window T → ℝ}
    (hF : ∀ n, IsCadlag (F n)) {f : J1Window T → ℝ}
    (hlim : TendstoUniformly F f atTop) : IsCadlag f := by
  have hclose : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ x : J1Window T,
      dist (f x) (F n x) < ε := by
    intro ε hε
    let u : Set (ℝ × ℝ) := {p | dist p.1 p.2 < ε}
    have hu : u ∈ 𝓤 ℝ := Metric.dist_mem_uniformity hε
    have h := hlim u hu
    simpa only [u, Set.mem_ofPred_eq] using h
  refine ⟨?_, ?_⟩
  · intro x
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    have hε3 : 0 < ε / 3 := by positivity
    obtain ⟨n, hn⟩ := (hclose (ε / 3) hε3).exists
    obtain ⟨r, hr, hright⟩ :=
      (Metric.continuousWithinAt_iff.mp ((hF n).isRightContinuous x))
        (ε / 3) hε3
    refine ⟨r, hr, ?_⟩
    intro y hy hyd
    have hfy := hn y
    have hfx := hn x
    have hfn := hright hy hyd
    calc
      dist (f y) (f x) ≤ dist (f y) (F n y) + dist (F n y) (f x) :=
        dist_triangle _ _ _
      _ ≤ dist (f y) (F n y) +
          (dist (F n y) (F n x) + dist (F n x) (f x)) :=
        add_le_add (le_refl _) (dist_triangle _ _ _)
      _ < ε / 3 + (ε / 3 + ε / 3) := by
        apply add_lt_add
        · exact hfy
        · exact add_lt_add hfn (by simpa [dist_comm] using hfx)
      _ = ε := by ring
  · intro x
    by_cases hx : (x : ℝ) = 0
    · have hIio : (Set.Iio x : Set (J1Window T)) = ∅ := by
        ext y
        simp only [Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
        intro hy
        have hyval : (y : ℝ) < (x : ℝ) := by exact_mod_cast hy
        rw [hx] at hyval
        linarith [y.property.1]
      exact ⟨0, by simp [nhdsWithin, hIio]⟩
    · have hxpos : (0 : ℝ) < (x : ℝ) := by
        rcases lt_or_eq_of_le x.property.1 with h | h
        · exact h
        · exact (hx h.symm).elim
      let L : ℕ → ℝ := fun n => Classical.choose ((hF n).tendsto_nhdsLT x)
      have hL (n : ℕ) : Tendsto (F n) (𝓝[<] x) (𝓝 (L n)) :=
        Classical.choose_spec ((hF n).tendsto_nhdsLT x)
      have hne : NeBot (𝓝[<] x) := by
        apply nhdsLT_neBot_of_exists_lt
        refine ⟨⟨0, le_rfl, le_trans x.property.1 x.property.2⟩, ?_⟩
        exact_mod_cast hxpos
      have hLcauchy : CauchySeq L := by
        rw [Metric.cauchySeq_iff]
        intro ε hε
        have hε4 : 0 < ε / 4 := by positivity
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hclose (ε / 4) hε4)
        refine ⟨N, ?_⟩
        intro m hm n hn
        have hdist : Tendsto (fun y : J1Window T => dist (F m y) (F n y))
            (𝓝[<] x) (𝓝 (dist (L m) (L n))) :=
          continuous_dist.continuousAt.tendsto.comp ((hL m).prodMk_nhds (hL n))
        have hbound : ∀ y : J1Window T, dist (F m y) (F n y) < ε / 2 := by
          intro y
          calc
            dist (F m y) (F n y) ≤
                dist (F m y) (f y) + dist (f y) (F n y) := dist_triangle _ _ _
            _ < ε / 4 + ε / 4 := by
              apply add_lt_add
              · simpa [dist_comm] using hN m hm y
              · exact hN n hn y
            _ = ε / 2 := by ring
        have hfrequent : ∀ᶠ y in 𝓝[<] x,
            dist (F m y) (F n y) ≤ ε / 2 :=
          Filter.Eventually.of_forall fun y => (hbound y).le
        have hlimdist := le_of_tendsto hdist hfrequent
        exact lt_of_le_of_lt hlimdist (by linarith)
      obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hLcauchy
      refine ⟨l, ?_⟩
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hε3 : 0 < ε / 3 := by positivity
      obtain ⟨n, hnclose, hnlim⟩ :=
        (hclose (ε / 3) hε3).and (Metric.tendsto_nhds.mp hl (ε / 3) hε3) |>.exists
      have hfnlim : ∀ᶠ y in 𝓝[<] x, dist (F n y) (L n) < ε / 3 :=
        Metric.tendsto_nhds.mp (hL n) (ε / 3) hε3
      filter_upwards [hfnlim] with y hy
      calc
        dist (f y) l ≤ dist (f y) (F n y) + dist (F n y) l := dist_triangle _ _ _
        _ ≤ dist (f y) (F n y) +
            (dist (F n y) (L n) + dist (L n) l) :=
          add_le_add (le_refl _) (dist_triangle _ _ _)
        _ < ε / 3 + (ε / 3 + ε / 3) := by
          apply add_lt_add
          · exact hnclose y
          · exact add_lt_add hy hnlim
        _ = ε := by ring

end DirectedDistances.Probability
