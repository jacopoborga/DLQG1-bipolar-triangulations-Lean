/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDiskArcGluing2

/-! # Embedded arcs on the circle

Helpers toward Proposition 5.16. These results identify an embedded interval
with one of the two standard circle paths by cutting at a point outside it. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: the range of an embedded interval that
misses the cut point is exactly the closed slit-argument interval between its
endpoint arguments. -/
theorem range_continuous_injective_circle_interval_eq_slit
    (phi : Set.Icc (-1 : ℝ) 1 → Circle) (hphi : Continuous phi)
    (hinj : Function.Injective phi) (c : Circle) (hc : ∀ t, phi t ≠ c) :
    Set.range phi = {z : Circle | z ≠ c ∧ rotatedCircleArg c z ∈ Set.Icc
      (min (rotatedCircleArg c (phi ⟨-1, by norm_num⟩))
        (rotatedCircleArg c (phi ⟨1, by norm_num⟩)))
      (max (rotatedCircleArg c (phi ⟨-1, by norm_num⟩))
        (rotatedCircleArg c (phi ⟨1, by norm_num⟩)))} := by
  obtain ⟨_, harg⟩ := rotatedCircleArg_interval_range phi hphi hinj c hc
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨hc t, ?_⟩
    rw [← harg]
    exact ⟨t, rfl⟩
  · rintro ⟨hz, hzarg⟩
    have hzrange : rotatedCircleArg c z ∈
        Set.range (fun t => rotatedCircleArg c (phi t)) := by
      rw [harg]
      exact hzarg
    rcases hzrange with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    exact injectiveOn_rotatedCircleArg c (hc t) hz ht

/-- Helper toward Proposition 5.16: an injectively parameterized circle arc
avoiding a point is the range of one of the two oriented standard paths with
the same endpoints. -/
theorem range_embedded_circle_interval_eq_path_or_reverse
    (phi : Set.Icc (-1 : ℝ) 1 → Circle) (hphi : Continuous phi)
    (hinj : Function.Injective phi) (c : Circle) (hc : ∀ t, phi t ≠ c) :
    Set.range phi = Set.range (Circle.path (phi ⟨-1, by norm_num⟩)
      (phi ⟨1, by norm_num⟩)) ∨
    Set.range phi = Set.range (Circle.path (phi ⟨1, by norm_num⟩)
      (phi ⟨-1, by norm_num⟩)) := by
  let x : Circle := phi ⟨-1, by norm_num⟩
  let y : Circle := phi ⟨1, by norm_num⟩
  have hxy : x ≠ y := by
    intro h
    have := hinj (show phi ⟨-1, by norm_num⟩ = phi ⟨1, by norm_num⟩ by simpa [x, y] using h)
    have : (⟨-1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) = ⟨1, by norm_num⟩ := this
    have hval := congrArg (fun t : Set.Icc (-1 : ℝ) 1 => (t : ℝ)) this
    norm_num at hval
  have hcover := Circle.range_path_union_range_path hxy
  have hcUnion : c ∈ Set.range (Circle.path x y) ∨
      c ∈ Set.range (Circle.path y x) := by
    have hcmem : c ∈ Set.range (Circle.path x y) ∪ Set.range (Circle.path y x) := by
      rw [hcover]
      exact Set.mem_univ c
    simpa only [Set.mem_union] using hcmem
  have hcnotinter : c ∉ Set.range (Circle.path x y) ∩
      Set.range (Circle.path y x) := by
    intro hcint
    rw [Circle.range_path_inter_range_path hxy] at hcint
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcint
    rcases hcint with h | h
    · exact (hc ⟨-1, by norm_num⟩) (by simpa [x] using h.symm)
    · exact (hc ⟨1, by norm_num⟩) (by simpa [y] using h.symm)
  have hnotboth : c ∉ Set.range (Circle.path x y) ∨
      c ∉ Set.range (Circle.path y x) := by
    rcases hcUnion with hcx | hcy
    · right
      intro hcy
      exact hcnotinter ⟨hcx, hcy⟩
    · left
      intro hcx
      exact hcnotinter ⟨hcx, hcy⟩
  have hslit := range_continuous_injective_circle_interval_eq_slit
    phi hphi hinj c hc
  rcases hnotboth with havoid | havoid
  · have hpathne : c ≠ x ∧ c ≠ y := by
      constructor
      · exact fun h => hc ⟨-1, by norm_num⟩ (by simpa [x] using h.symm)
      · exact fun h => hc ⟨1, by norm_num⟩ (by simpa [y] using h.symm)
    obtain ⟨e, he0, he1⟩ := exists_homeomorph_Icc_circlePath_range hxy
    let psi : Set.Icc (-1 : ℝ) 1 → Circle := fun t => (e t : Set.range (Circle.path x y))
    have hpsi : Continuous psi := by
      exact continuous_subtype_val.comp e.continuous
    have hpsii : Function.Injective psi := by
      intro a b hab
      exact e.injective (Subtype.ext hab)
    have hcpsi : ∀ t, psi t ≠ c := by
      intro t h
      apply havoid
      rcases (e t).property with ⟨u, hu⟩
      exact ⟨u, hu.trans h⟩
    have hrangePsi : Set.range psi = Set.range (Circle.path x y) := by
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact (e t).property
      · rintro ⟨u, rfl⟩
        let z : Set.range (Circle.path x y) := ⟨_, ⟨u, rfl⟩⟩
        obtain ⟨t, ht⟩ := e.surjective z
        exact ⟨t, congrArg Subtype.val ht⟩
    have hpsiSlit := range_continuous_injective_circle_interval_eq_slit
      psi hpsi hpsii c hcpsi
    have hends : (psi ⟨-1, by norm_num⟩) = x ∧ (psi ⟨1, by norm_num⟩) = y := by
      exact ⟨congrArg Subtype.val he0, congrArg Subtype.val he1⟩
    have hsame : Set.range phi = Set.range psi := by
      rw [hslit, hpsiSlit, hends.1, hends.2]
    exact Or.inl (hsame.trans hrangePsi)
  · obtain ⟨e, he0, he1⟩ := exists_homeomorph_Icc_circlePath_range hxy.symm
    let psi : Set.Icc (-1 : ℝ) 1 → Circle := fun t => (e t : Set.range (Circle.path y x))
    have hpsi : Continuous psi := by
      exact continuous_subtype_val.comp e.continuous
    have hpsii : Function.Injective psi := by
      intro a b hab
      exact e.injective (Subtype.ext hab)
    have hcpsi : ∀ t, psi t ≠ c := by
      intro t h
      apply havoid
      rcases (e t).property with ⟨u, hu⟩
      exact ⟨u, hu.trans h⟩
    have hrangePsi : Set.range psi = Set.range (Circle.path y x) := by
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact (e t).property
      · rintro ⟨u, rfl⟩
        let z : Set.range (Circle.path y x) := ⟨_, ⟨u, rfl⟩⟩
        obtain ⟨t, ht⟩ := e.surjective z
        exact ⟨t, congrArg Subtype.val ht⟩
    have hpsiSlit := range_continuous_injective_circle_interval_eq_slit
      psi hpsi hpsii c hcpsi
    have hends : (psi ⟨-1, by norm_num⟩) = y ∧ (psi ⟨1, by norm_num⟩) = x := by
      exact ⟨congrArg Subtype.val he0, congrArg Subtype.val he1⟩
    have hmin : min (rotatedCircleArg c x) (rotatedCircleArg c y) =
        min (rotatedCircleArg c y) (rotatedCircleArg c x) := min_comm _ _
    have hmax : max (rotatedCircleArg c x) (rotatedCircleArg c y) =
        max (rotatedCircleArg c y) (rotatedCircleArg c x) := max_comm _ _
    have hsame : Set.range phi = Set.range psi := by
      rw [hslit, hpsiSlit, hends.1, hends.2, hmin, hmax]
    exact Or.inr (hsame.trans hrangePsi)

/-- Helper toward Proposition 5.16: the closure of the complement of a
proper embedded circle arc is homeomorphic to the interval, with the
endpoints exchanged. -/
theorem exists_homeomorph_circle_arc_complement
    (gamma : Set Circle)
    (phi : Set.Icc (-1 : ℝ) 1 ≃ₜ gamma)
    (hproper : gamma ≠ Set.univ) :
    ∃ psi : Set.Icc (-1 : ℝ) 1 ≃ₜ closure (gammaᶜ : Set Circle),
      psi ⟨-1, by norm_num⟩ = (phi ⟨1, by norm_num⟩ : Circle) ∧
      psi ⟨1, by norm_num⟩ = (phi ⟨-1, by norm_num⟩ : Circle) := by
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
  have harc := range_embedded_circle_interval_eq_path_or_reverse f hf hfi c hfc
  rcases harc with hforward | hreverse
  · have hgamma : gamma = Set.range (Circle.path x y) := by
      simpa [f, x, y] using hfrange.symm.trans hforward
    have hclosure : closure (gammaᶜ : Set Circle) =
        Set.range (Circle.path y x) := by
      rw [hgamma]
      exact closure_circlePath_compl_range_eq_reverse_range (x := x) (y := y) hxy
    rw [hclosure]
    obtain ⟨e, he0, he1⟩ := exists_homeomorph_Icc_circlePath_range hxy.symm
    refine ⟨e, ?_, ?_⟩
    · simpa [x, y] using congrArg Subtype.val he0
    · simpa [x, y] using congrArg Subtype.val he1
  · have hgamma : gamma = Set.range (Circle.path y x) := by
      simpa [f, x, y] using hfrange.symm.trans hreverse
    have hclosure : closure (gammaᶜ : Set Circle) =
        Set.range (Circle.path x y) := by
      rw [hgamma]
      exact closure_circlePath_compl_range_eq_reverse_range (x := y) (y := x) hxy.symm
    rw [hclosure]
    obtain ⟨e, he0, he1⟩ := exists_homeomorph_Icc_circlePath_range hxy
    let revFun : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1 := fun t =>
      ⟨-(t : ℝ), by
        constructor
        · change (-1 : ℝ) ≤ -(t : ℝ)
          linarith [t.property.2]
        · change -(t : ℝ) ≤ (1 : ℝ)
          linarith [t.property.1]⟩
    let revEquiv : Set.Icc (-1 : ℝ) 1 ≃ Set.Icc (-1 : ℝ) 1 := {
      toFun := revFun
      invFun := revFun
      left_inv := by
        intro t
        apply Subtype.ext
        simp [revFun]
      right_inv := by
        intro t
        apply Subtype.ext
        simp [revFun]
    }
    let rev : Set.Icc (-1 : ℝ) 1 ≃ₜ Set.Icc (-1 : ℝ) 1 := {
      toEquiv := revEquiv
      continuous_toFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _
    }
    have hrev0 : rev ⟨-1, by norm_num⟩ = ⟨1, by norm_num⟩ := by
      apply Subtype.ext
      simp [rev, revEquiv, revFun]
    have hrev1 : rev ⟨1, by norm_num⟩ = ⟨-1, by norm_num⟩ := by
      apply Subtype.ext
      simp [rev, revEquiv, revFun]
    let e' : Set.Icc (-1 : ℝ) 1 ≃ₜ Set.range (Circle.path x y) := rev.trans e
    have he'0 : ((e' ⟨-1, by norm_num⟩ : Set.range (Circle.path x y)) : Circle) = y := by
      change ((e (rev ⟨-1, by norm_num⟩) : Set.range (Circle.path x y)) : Circle) = y
      rw [hrev0]
      exact congrArg Subtype.val he1
    have he'1 : ((e' ⟨1, by norm_num⟩ : Set.range (Circle.path x y)) : Circle) = x := by
      change ((e (rev ⟨1, by norm_num⟩) : Set.range (Circle.path x y)) : Circle) = x
      rw [hrev1]
      exact congrArg Subtype.val he0
    exact ⟨e', by simpa [y] using he'0, by simpa [x] using he'1⟩





























end DirectedDistances.PlanarMap
