/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDiskArcGluing3

/-! # Parameterized boundary arcs for disk gluing

Helpers toward Proposition 5.16. This file continues the boundary
normalization from `D39PLDiskArcGluing3`. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: the counterclockwise path from `1` to
`-1` is exactly the closed upper semicircle. -/
theorem circle_upper_semicircle_eq_path_range :
    {c : Circle | 0 ≤ (c : ℂ).im} = Set.range (Circle.path (1 : Circle) (-1)) := by
  have hrange : Set.range (Circle.path (1 : Circle) (-1)) =
      Circle.exp '' Set.Icc (0 : ℝ) Real.pi := by
    rw [Circle.range_path]
    simp [Circle.angleDiff, Real.pi_pos.le]
  rw [hrange]
  ext c
  constructor
  · intro hc
    have harg : 0 ≤ (c : ℂ).arg := Complex.arg_nonneg_iff.mpr hc
    have hargpi : (c : ℂ).arg ≤ Real.pi := Complex.arg_le_pi _
    refine ⟨(c : ℂ).arg, ⟨harg, hargpi⟩, ?_⟩
    exact Circle.exp_arg c
  · rintro ⟨r, hr, hrc⟩
    have harg : 0 ≤ Complex.arg ((Circle.exp r : Circle) : ℂ) := by
      rw [Circle.arg_exp (by have hπ := Real.pi_pos; linarith [hr.1]) hr.2]
      exact hr.1
    have harg' : 0 ≤ (c : ℂ).arg := by rw [← hrc]; exact harg
    exact Complex.arg_nonneg_iff.mp harg'

/-- Helper toward Proposition 5.16: the upper semicircle has an interval
parameterization from `1` to `-1`. -/
theorem exists_homeomorph_Icc_upper_semicircle :
    ∃ e : Set.Icc (-1 : ℝ) 1 ≃ₜ {c : Circle // 0 ≤ (c : ℂ).im},
      e ⟨-1, by norm_num⟩ = ⟨1, by simp⟩ ∧
      e ⟨1, by norm_num⟩ = ⟨-1, by simp⟩ := by
  obtain ⟨e, he0, he1⟩ :=
    exists_homeomorph_Icc_circlePath_range (x := (1 : Circle)) (y := -1) (by
      intro h
      have hv : (1 : ℂ) = -1 := congrArg Subtype.val h
      norm_num at hv)
  let h := Homeomorph.setCongr circle_upper_semicircle_eq_path_range.symm
  let E := e.trans h
  refine ⟨E, ?_, ?_⟩
  · apply Subtype.ext
    change ((e ⟨-1, by norm_num⟩ : Set.range (Circle.path (1 : Circle) (-1))) : Circle) = 1
    exact congrArg Subtype.val he0
  · apply Subtype.ext
    change ((e ⟨1, by norm_num⟩ : Set.range (Circle.path (1 : Circle) (-1))) : Circle) = -1
    exact congrArg Subtype.val he1

/-- Helper toward Proposition 5.16: a proper embedded circle arc meets the
closure of its complement exactly at its two endpoints. -/
theorem circle_arc_inter_complement_closure_eq_endpoints
    (gamma : Set Circle)
    (phi : Set.Icc (-1 : ℝ) 1 ≃ₜ gamma)
    (hproper : gamma ≠ Set.univ) :
    gamma ∩ closure (gammaᶜ : Set Circle) =
      {(phi ⟨-1, by norm_num⟩ : Circle), (phi ⟨1, by norm_num⟩ : Circle)} := by
  let x : Circle := (phi ⟨-1, by norm_num⟩ : Circle)
  let y : Circle := (phi ⟨1, by norm_num⟩ : Circle)
  let f : Set.Icc (-1 : ℝ) 1 → Circle := fun t => (phi t : Circle)
  have hf : Continuous f := continuous_subtype_val.comp phi.continuous
  have hfi : Function.Injective f := by
    intro a b hab
    exact phi.injective (Subtype.ext hab)
  have hxy : x ≠ y := by
    intro h
    have ht := hfi (by simpa [f, x, y] using h)
    have hv := congrArg (fun t : Set.Icc (-1 : ℝ) 1 => (t : ℝ)) ht
    norm_num at hv
  have hfrange : Set.range f = gamma := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact (phi t).property
    · intro hz
      obtain ⟨t, ht⟩ := phi.surjective ⟨z, hz⟩
      exact ⟨t, congrArg Subtype.val ht⟩
  have hc : ∃ c : Circle, c ∉ gamma := by
    by_contra hn
    have hall : ∀ z : Circle, z ∈ gamma := by
      intro z
      by_contra hz
      exact hn ⟨z, hz⟩
    apply hproper
    ext z
    simp only [Set.mem_univ, iff_true]
    exact hall z
  obtain ⟨c, hc⟩ := hc
  have hfc : ∀ t, f t ≠ c := by
    intro t h
    exact hc (h ▸ (phi t).property)
  rcases range_embedded_circle_interval_eq_path_or_reverse f hf hfi c hfc with hpath | hpath
  · have hgamma : gamma = Set.range (Circle.path x y) := by
      simpa [f, x, y] using hfrange.symm.trans hpath
    have hclosure : closure (gammaᶜ : Set Circle) = Set.range (Circle.path y x) := by
      rw [hgamma]
      exact closure_circlePath_compl_range_eq_reverse_range hxy
    ext z
    constructor
    · rintro ⟨hz, hzc⟩
      have hz' : z ∈ Set.range (Circle.path x y) := by
        simpa only [hgamma] using hz
      have hzc' : z ∈ Set.range (Circle.path y x) := by
        simpa only [hclosure] using hzc
      have hp : z ∈ ({x, y} : Set Circle) := by
        have hi : z ∈ Set.range (Circle.path x y) ∩ Set.range (Circle.path y x) :=
          ⟨hz', hzc'⟩
        rw [Circle.range_path_inter_range_path hxy] at hi
        exact hi
      change z = x ∨ z = y at hp
      change z = x ∨ z = y
      exact hp
    · intro hz
      change z = x ∨ z = y at hz
      have hp : z ∈ ({x, y} : Set Circle) := by
        change z = x ∨ z = y
        exact hz
      have hi : z ∈ Set.range (Circle.path x y) ∩ Set.range (Circle.path y x) := by
        rw [Circle.range_path_inter_range_path hxy]
        exact hp
      exact ⟨by simpa only [hgamma] using hi.1, by simpa only [hclosure] using hi.2⟩
  · have hgamma : gamma = Set.range (Circle.path y x) := by
      simpa [f, x, y] using hfrange.symm.trans hpath
    have hclosure : closure (gammaᶜ : Set Circle) = Set.range (Circle.path x y) := by
      rw [hgamma]
      exact closure_circlePath_compl_range_eq_reverse_range hxy.symm
    ext z
    constructor
    · rintro ⟨hz, hzc⟩
      have hz' : z ∈ Set.range (Circle.path y x) := by
        simpa only [hgamma] using hz
      have hzc' : z ∈ Set.range (Circle.path x y) := by
        simpa only [hclosure] using hzc
      have hp : z ∈ ({y, x} : Set Circle) := by
        have hi : z ∈ Set.range (Circle.path y x) ∩ Set.range (Circle.path x y) :=
          ⟨hz', hzc'⟩
        rw [Circle.range_path_inter_range_path hxy.symm] at hi
        exact hi
      change z = y ∨ z = x at hp
      change z = x ∨ z = y
      exact hp.symm
    · intro hz
      change z = x ∨ z = y at hz
      have hp : z ∈ ({y, x} : Set Circle) := by
        change z = y ∨ z = x
        exact hz.symm
      have hi : z ∈ Set.range (Circle.path y x) ∩ Set.range (Circle.path x y) := by
        rw [Circle.range_path_inter_range_path hxy.symm]
        exact hp
      exact ⟨by simpa only [hgamma] using hi.1, by simpa only [hclosure] using hi.2⟩








































































































end DirectedDistances.PlanarMap
