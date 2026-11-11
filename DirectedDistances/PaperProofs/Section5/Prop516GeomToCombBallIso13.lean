/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso12

/-! Helper toward Proposition 5.16. This file records the common-prefix step for
the independent straightening witnesses and the remaining full-star rotation
obligation. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open unitInterval

/-- Helper toward Proposition 5.16. An increasing reparameterization
identifies the two restrictions of corresponding arcs at the smaller of two
prefix cutoffs. -/
theorem d39_common_prefix_of_increasing_reparam
    {D : Type*} (arc arc' : D → I → ℂ) (R : ℂ ≃ₜ ℂ)
    (φ : I ≃ₜ I) (hφ : StrictMono φ) (x : D) (tx ty : I)
    (htx0 : 0 < (tx : ℝ)) (htx1 : (tx : ℝ) < 1)
    (hty0 : 0 < (ty : ℝ)) (hty1 : (ty : ℝ) < 1)
    (hmap : ∀ t, R (arc x t) = arc' x (φ t)) :
    ∃ t : I, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
      (φ t : ℝ) > 0 ∧ (φ t : ℝ) < 1 ∧
      arc x '' Set.Icc (0 : I) t =
        R.symm '' (arc' x '' Set.Icc (0 : I) (φ t)) ∧
      t ≤ tx ∧ φ t ≤ ty := by
  have hend := d39StrictMonoIntervalEndpoints φ hφ
  have hinv_mono : Monotone φ.symm := by
    intro a b hab
    by_contra hnot
    have hlt : φ.symm b < φ.symm a := lt_of_not_ge hnot
    have hlt' := hφ hlt
    have : b < a := by simpa using hlt'
    exact (not_lt_of_ge hab) this
  have hsymm_ty_pos : 0 < (φ.symm ty : ℝ) := by
    have hzero : φ.symm 0 = 0 := by
      calc
        φ.symm 0 = φ.symm (φ 0) := by rw [hend.1]
        _ = 0 := φ.symm_apply_apply 0
    have hlt : (0 : I) < ty := by exact_mod_cast hty0
    have hinv_le : φ.symm 0 ≤ φ.symm ty := hinv_mono hlt.le
    have hinv_ne : φ.symm 0 ≠ φ.symm ty := by
      intro heq
      have hEq : (0 : I) = ty := by
        simpa using congrArg φ heq
      exact (ne_of_lt hlt) hEq
    have hinv_lt : φ.symm 0 < φ.symm ty := lt_of_le_of_ne hinv_le hinv_ne
    rw [hzero] at hinv_lt
    exact_mod_cast hinv_lt
  let t : I := min tx (φ.symm ty)
  have ht0I : (0 : I) < t := by
    apply lt_min
    · exact_mod_cast htx0
    · exact_mod_cast hsymm_ty_pos
  have ht1I : t < (1 : I) := lt_of_le_of_lt (min_le_left _ _) (by
    exact_mod_cast htx1)
  have hφt0I : (0 : I) < φ t := by
    rw [← hend.1]
    exact hφ ht0I
  have hφt1I : φ t < (1 : I) := by
    have hφt_ty : φ t ≤ ty := by
      calc
        φ t ≤ φ (φ.symm ty) := hφ.monotone (min_le_right _ _)
        _ = ty := φ.apply_symm_apply ty
    exact lt_of_le_of_lt hφt_ty (by exact_mod_cast hty1)
  have hpreimage :
      R.symm '' (arc' x '' Set.Icc (0 : I) (φ t)) =
        arc x '' Set.Icc (0 : I) t := by
    ext z
    constructor
    · rintro ⟨w, ⟨s, hs, rfl⟩, hRz⟩
      have hs0 : (0 : I) ≤ φ.symm s := by
        have hzero : φ.symm 0 = 0 := by
          calc
            φ.symm 0 = φ.symm (φ 0) := by rw [hend.1]
            _ = 0 := φ.symm_apply_apply 0
        calc
          0 = φ.symm 0 := hzero.symm
          _ ≤ φ.symm s := hinv_mono hs.1
      have hst : φ.symm s ≤ t := by
        have hle : s ≤ φ t := hs.2
        have := hinv_mono hle
        simpa using this
      have hback : R.symm (arc' x s) = arc x (φ.symm s) := by
        have hm := congrArg R.symm (hmap (φ.symm s))
        simpa using hm.symm
      refine ⟨φ.symm s, ⟨hs0, hst⟩, ?_⟩
      exact hback.symm.trans hRz
    · rintro ⟨s, hs, rfl⟩
      refine ⟨arc' x (φ s), ⟨φ s, ?_, rfl⟩, ?_⟩
      · constructor
        · have hzero : φ 0 = 0 := hend.1
          calc
            0 = φ 0 := hzero.symm
            _ ≤ φ s := hφ.monotone hs.1
        · exact hφ.monotone hs.2
      · have hm := hmap s
        simpa using (congrArg R.symm hm).symm
  refine ⟨t, ?_, ?_, ?_, ?_, hpreimage.symm, min_le_left _ _, ?_⟩
  · exact_mod_cast ht0I
  · exact_mod_cast ht1I
  · exact_mod_cast hφt0I
  · exact_mod_cast hφt1I
  · calc
      φ t ≤ φ (φ.symm ty) := hφ.monotone (min_le_right _ _)
      _ = ty := φ.apply_symm_apply ty

 /-- Helper toward Proposition 5.16. A continuous path prefix contained in a
radial segment and starting at its center has image an initial radial segment
whenever the prefix is nonconstant. -/
theorem d39_continuous_radial_prefix_is_initial_segment
    {a : I} (f : I → ℂ) (u : ℂ) (hf : Continuous f) (hu : u ≠ 0)
    (hstart : f 0 = 0)
    (hcontained : ∀ t ∈ Set.Icc (0 : I) a,
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ f t = (s : ℂ) * u)
    (hnonconstant : ∃ t ∈ Set.Icc (0 : I) a, f t ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      f '' Set.Icc (0 : I) a =
        {z : ℂ | ∃ s : ℝ, 0 ≤ s ∧ s ≤ r ∧ z = (s : ℂ) * u} := by
  let g : I → ℝ := fun t => Complex.re (f t / u)
  let S : Set ℝ := g '' Set.Icc (0 : I) a
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hIcc_nonempty : (Set.Icc (0 : I) a).Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨le_rfl, a.property.1⟩
  have hIcc_connected : IsConnected (Set.Icc (0 : I) a) :=
    ⟨hIcc_nonempty, isPreconnected_Icc⟩
  have hS_connected : IsConnected S := by
    dsimp [S]
    exact hIcc_connected.image g hg.continuousOn
  have hS_compact : IsCompact S := by
    dsimp [S]
    exact isCompact_Icc.image hg
  have hcoord_mul (s : ℝ) : Complex.re (((s : ℂ) * u) / u) = s := by
    simp [hu]
  have hzero_mem : 0 ∈ S := by
    refine ⟨0, ⟨le_rfl, a.property.1⟩, ?_⟩
    simp [g, hstart]
  have hS_nonneg : ∀ q ∈ S, 0 ≤ q := by
    rintro q ⟨t, ht, rfl⟩
    obtain ⟨s, hs0, hs1, hft⟩ := hcontained t ht
    have hgs : g t = s := by
      dsimp [g]
      rw [hft]
      exact hcoord_mul s
    rw [hgs]
    exact hs0
  have hS_nonempty : S.Nonempty := ⟨0, hzero_mem⟩
  have hInf : sInf S = 0 := by
    apply le_antisymm
    · exact csInf_le hS_compact.bddBelow hzero_mem
    · exact le_csInf hS_nonempty hS_nonneg
  obtain ⟨t₀, ht₀, hft₀⟩ := hnonconstant
  obtain ⟨s₀, hs₀, hs₀1, hft₀'⟩ := hcontained t₀ ht₀
  have hs₀_ne : s₀ ≠ 0 := by
    intro heq
    apply hft₀
    rw [hft₀', heq]
    simp
  have hs₀_pos : 0 < s₀ := lt_of_le_of_ne hs₀ (Ne.symm hs₀_ne)
  have hSpos_mem : g t₀ ∈ S := ⟨t₀, ht₀, rfl⟩
  have hg₀ : g t₀ = s₀ := by
    dsimp [g]
    rw [hft₀']
    exact hcoord_mul s₀
  let r : ℝ := sSup S
  have hr : 0 < r := by
    dsimp [r]
    have hle := le_csSup hS_compact.bddAbove hSpos_mem
    rw [hg₀] at hle
    exact lt_of_lt_of_le hs₀_pos hle
  have hS_eq : S = Set.Icc (0 : ℝ) r := by
    calc
      S = Set.Icc (sInf S) (sSup S) :=
        eq_Icc_of_connected_compact hS_connected hS_compact
      _ = Set.Icc (0 : ℝ) r := by rw [hInf]
  refine ⟨r, hr, ?_⟩
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨s, hs0, hs1, hft⟩ := hcontained t ht
    refine ⟨s, hs0, ?_, hft⟩
    have hgs : g t = s := by
      dsimp [g]
      rw [hft]
      exact hcoord_mul s
    have hs_mem : s ∈ S := ⟨t, ht, hgs⟩
    exact (hS_eq ▸ hs_mem).2
  · rintro ⟨s, hs0, hsr, rfl⟩
    have hs_mem : s ∈ S := hS_eq ▸ ⟨hs0, hsr⟩
    rcases hs_mem with ⟨t, ht, hgt⟩
    obtain ⟨q, hq0, hq1, hft⟩ := hcontained t ht
    have hq : q = s := by
      have hcoord : g t = q := by
        dsimp [g]
        rw [hft]
        exact hcoord_mul q
      rw [hcoord] at hgt
      exact hgt
    refine ⟨t, ht, ?_⟩
    rw [hft, hq]






























































end DirectedDistances.PaperProofs.Section5

end
