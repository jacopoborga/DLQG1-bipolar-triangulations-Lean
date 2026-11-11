/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMapSides
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Transfer lemmas for logarithmic winding

Helper toward Definition 3.2. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Definition 3.2: a pointwise quotient in the logarithm slit
plane transfers a winding lift between loops without changing its winding. -/
theorem hasWinding_of_ratio_mem_slitPlane {z z' : ℂ}
    (L : Path z z) (L' : Path z' z') (w : ℂ) (n : ℤ)
    (hL : ∀ t, L t ≠ w) (_hL' : ∀ t, L' t ≠ w)
    (hr : ∀ t, (L' t - w) / (L t - w) ∈ Complex.slitPlane)
    (h : HasWinding L w n) : HasWinding L' w n := by
  obtain ⟨φ, hφ, hinc⟩ := h
  let q : I → ℂ := fun t => (L' t - w) / (L t - w)
  have hden : ∀ t, L t - w ≠ 0 := fun t ht => hL t (sub_eq_zero.mp ht)
  have hq : Continuous q := by
    dsimp [q]
    exact (L'.continuous.sub continuous_const).div
      (L.continuous.sub continuous_const) hden
  let ψ : C(I, ℂ) := ⟨fun t => φ t + Complex.log (q t),
    φ.continuous.add (hq.clog hr)⟩
  have hq01 : q 1 = q 0 := by
    simp [q]
  refine ⟨ψ, ?_, ?_⟩
  · intro t
    change Complex.exp (φ t + Complex.log (q t)) = L' t - w
    rw [Complex.exp_add, hφ t,
      Complex.exp_log (Complex.slitPlane_ne_zero (hr t))]
    field_simp [hden t]
  · change (φ 1 + Complex.log (q 1)) -
      (φ 0 + Complex.log (q 0)) = 2 * Real.pi * Complex.I * n
    calc
      (φ 1 + Complex.log (q 1)) - (φ 0 + Complex.log (q 0)) =
          (φ 1 - φ 0) + (Complex.log (q 1) - Complex.log (q 0)) := by ring
      _ = φ 1 - φ 0 := by rw [hq01]; simp
      _ = 2 * Real.pi * Complex.I * n := hinc

/-- Helper toward Definition 3.2: the integer of a logarithmic winding lift
is unique. -/
theorem hasWinding_unique {z : ℂ} {L : Path z z} {w : ℂ} {m n : ℤ}
    (hm : HasWinding L w m) (hn : HasWinding L w n) : m = n := by
  obtain ⟨φ, hφ, hφinc⟩ := hm
  obtain ⟨ψ, hψ, hψinc⟩ := hn
  let d : I → ℂ := fun t => φ t - ψ t
  have hd : Continuous d := φ.continuous.sub ψ.continuous
  have hdexp : ∀ t, Complex.exp (d t) = 1 := by
    intro t
    dsimp [d]
    rw [Complex.exp_sub, hφ t, hψ t]
    have hg : L t - w ≠ 0 := by rw [← hφ t]; exact Complex.exp_ne_zero _
    exact div_self hg
  let T := AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ)
  letI : DiscreteTopology T := NormedSpace.discreteTopology_zmultiples _
  have hdmem : ∀ t, d t ∈ T := by
    intro t
    have heq : Complex.exp (d t) = Complex.exp (0 : ℂ) := by simpa using hdexp t
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
    change d t ∈ AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ)
    rw [AddSubgroup.mem_zmultiples_iff]
    exact ⟨k, by simpa [zsmul_eq_mul, mul_comm] using hk.symm⟩
  let dT : I → T := fun t => ⟨d t, hdmem t⟩
  have hdTc : Continuous dT := Continuous.subtype_mk hd hdmem
  have hd10 : d 1 = d 0 := by
    have h : dT (1 : I) = dT 0 := PreconnectedSpace.constant inferInstance hdTc
    exact congrArg Subtype.val h
  have hinc : φ 1 - φ 0 = ψ 1 - ψ 0 := by
    dsimp [d] at hd10
    calc
      φ 1 - φ 0 = (φ 1 - ψ 1) - (φ 0 - ψ 0) + (ψ 1 - ψ 0) := by ring
      _ = ψ 1 - ψ 0 := by rw [hd10]; ring
  have hcast : (2 * Real.pi * Complex.I) * (m : ℂ) =
      (2 * Real.pi * Complex.I) * (n : ℂ) := by
    calc
      (2 * Real.pi * Complex.I) * (m : ℂ) = φ 1 - φ 0 := hφinc.symm
      _ = ψ 1 - ψ 0 := hinc
      _ = (2 * Real.pi * Complex.I) * (n : ℂ) := hψinc
  have hnonzero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hmn : (m : ℂ) = n := mul_left_cancel₀ hnonzero hcast
  exact_mod_cast hmn

/-- Helper toward Definition 3.2: an alternate name for uniqueness of the
integer of a logarithmic winding lift. -/
theorem hasWinding_eq_of_hasWinding {z : ℂ} {L : Path z z} {w : ℂ} {m n : ℤ}
    (hm : HasWinding L w m) (hn : HasWinding L w n) : m = n :=
  hasWinding_unique hm hn

/-- Helper toward Definition 3.2: concatenating loops adds their winding
integers. -/
theorem hasWinding_trans_loop {z w : ℂ} {L₁ L₂ : Path z z} {m n : ℤ}
    (h₁ : HasWinding L₁ w m) (h₂ : HasWinding L₂ w n) :
    HasWinding (L₁.trans L₂) w (m + n) := by
  obtain ⟨φ₁, hφ₁, hinc₁⟩ := h₁
  obtain ⟨φ₂, hφ₂, hinc₂⟩ := h₂
  let c : ℂ := φ₁ 1 - φ₂ 0
  have hbase : L₁ 1 = L₂ 0 := by simp
  have hden : L₁ 1 - w ≠ 0 := by
    rw [← hφ₁ 1]
    exact Complex.exp_ne_zero _
  have hden₂ : L₂ 0 - w ≠ 0 := by rw [← hbase]; exact hden
  have hc : Complex.exp c = 1 := by
    dsimp [c]
    rw [Complex.exp_sub, hφ₁ 1, hφ₂ 0, hbase]
    exact div_self hden₂
  let α : Path (φ₁ 0) (φ₁ 1) := ⟨φ₁, rfl, rfl⟩
  let β : Path (φ₁ 1) (φ₂ 1 + c) :=
    ⟨⟨fun t => φ₂ t + c, φ₂.continuous.add continuous_const⟩,
      by dsimp [c]; ring, rfl⟩
  let Ψ : C(I, ℂ) := (α.trans β).toContinuousMap
  refine ⟨Ψ, ?_, ?_⟩
  · intro t
    change Complex.exp ((α.trans β) t) = (L₁.trans L₂) t - w
    rw [Path.trans_apply α β t, Path.trans_apply L₁ L₂ t]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [dif_pos ht]
      exact hφ₁ _
    · simp only [dif_neg ht]
      let u : I := ⟨2 * (t : ℝ) - 1,
        two_mul_sub_one_mem_iff.2 ⟨(not_le.mp ht).le, t.2.2⟩⟩
      change Complex.exp (φ₂ u + c) = L₂ u - w
      rw [Complex.exp_add, hφ₂ u, hc, mul_one]
  · change (α.trans β) 1 - (α.trans β) 0 =
      2 * Real.pi * Complex.I * ((m + n : ℤ) : ℂ)
    have hstart : (α.trans β) 0 = φ₁ 0 := by simp [α]
    have hend : (α.trans β) 1 = φ₂ 1 + c := by simp [β]
    rw [hend, hstart]
    calc
      φ₂ 1 + c - φ₁ 0 = (φ₁ 1 - φ₁ 0) + (φ₂ 1 - φ₂ 0) := by
        dsimp [c]
        ring
      _ = 2 * Real.pi * Complex.I * ((m + n : ℤ) : ℂ) := by
        rw [hinc₁, hinc₂]
        rw [Int.cast_add]
        ring

















end DirectedDistances.PlanarMap

end
