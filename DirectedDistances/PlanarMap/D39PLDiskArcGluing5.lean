/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDiskArcGluing4
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Maps.Basic

/-! # Boundary arc transfer for disk gluing

Helpers toward Proposition 5.16. This file transfers an arc and its complementary
arc parameterization through a disk chart's boundary homeomorphism. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: a proper parameterized arc on the boundary
of a disk chart has a complementary-arc parameterization in the boundary
subspace, with the endpoints exchanged. -/
theorem exists_boundary_subtype_complement_homeomorph
    (S T gamma : Set ℂ) (hT : T ⊆ S)
    (h : Metric.closedBall (0 : ℂ) 1 ≃ₜ S)
    (hb : ∀ z : Metric.closedBall (0 : ℂ) 1,
      (h z : ℂ) ∈ T ↔ ‖(z : ℂ)‖ = 1)
    (hgamma : gamma ⊆ T)
    (phi : Set.Icc (-1 : ℝ) 1 ≃ₜ gamma)
    (hproper : gamma ≠ T) :
    ∃ psi : Set.Icc (-1 : ℝ) 1 ≃ₜ
        closure (T \ gamma),
      (psi ⟨-1, by norm_num⟩ : ℂ) = (phi ⟨1, by norm_num⟩ : ℂ) ∧
      (psi ⟨1, by norm_num⟩ : ℂ) = (phi ⟨-1, by norm_num⟩ : ℂ) ∧
      gamma ∩ closure (T \ gamma) =
        {(phi ⟨-1, by norm_num⟩ : ℂ), (phi ⟨1, by norm_num⟩ : ℂ)} := by
  let p : Set.Icc (-1 : ℝ) 1 → T := fun t =>
    ⟨(phi t : ℂ), hgamma (phi t).property⟩
  let b : Circle ≃ₜ T := Classical.choose
    (exists_boundary_homeomorph_of_disk_chart S T hT h hb)
  let f : Set.Icc (-1 : ℝ) 1 → Circle := fun t => b.symm (p t)
  have hf : Continuous f := by
    exact b.symm.continuous.comp (continuous_subtype_val.comp phi.continuous |>.subtype_mk _)
  have hfi : Function.Injective f := by
    intro a c hac
    apply phi.injective
    apply Subtype.ext
    have := congrArg (fun x : Circle => (b x : ℂ)) hac
    simpa [f, p] using this
  let gamma' : Set Circle := Set.range f
  let q : Set.Icc (-1 : ℝ) 1 → gamma' := fun t => ⟨f t, ⟨t, rfl⟩⟩
  have hqcont : Continuous q := hf.subtype_mk _
  have hqbij : Function.Bijective q := by
    constructor
    · intro a c hac
      exact hfi (congrArg Subtype.val hac)
    · rintro ⟨c, ⟨t, rfl⟩⟩
      exact ⟨t, rfl⟩
  let phi' : Set.Icc (-1 : ℝ) 1 ≃ₜ gamma' :=
    hqcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective q hqbij)
  have hproper' : gamma' ≠ Set.univ := by
    intro hfull
    apply hproper
    ext z
    constructor
    · intro hz
      exact hgamma hz
    · intro hz
      let c : Circle := b.symm ⟨z, hz⟩
      have hc : c ∈ gamma' := by rw [hfull]; simp
      obtain ⟨t, ht⟩ := hc
      have hct : b c = p t := by
        have := congrArg b ht
        simpa [f] using this.symm
      have hcz : b c = ⟨z, hz⟩ := by
        dsimp [c]
        exact b.apply_symm_apply ⟨z, hz⟩
      have hpt : p t = ⟨z, hz⟩ := hct.symm.trans hcz
      have hphi : (phi t : ℂ) = z := congrArg (fun x : T => (x : ℂ)) hpt
      rw [← hphi]
      exact (phi t).property
  obtain ⟨psiC, hpsi0, hpsi1⟩ :=
    exists_homeomorph_circle_arc_complement gamma' phi' hproper'
  let gammaT : Set T := Set.range p
  have hgammaT : gammaT = {x : T | (x : ℂ) ∈ gamma} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (phi t).property
    · intro hx
      obtain ⟨t, ht⟩ := phi.surjective ⟨x, hx⟩
      exact ⟨t, Subtype.ext (congrArg (fun y : gamma => (y : ℂ)) ht)⟩
  have hcoimage : Subtype.val '' (gammaTᶜ : Set T) = T \ gamma := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.property, ?_⟩
      intro hz
      apply hx
      rw [hgammaT]
      exact hz
    · rintro ⟨hzT, hzγ⟩
      refine ⟨⟨z, hzT⟩, ?_, rfl⟩
      rw [hgammaT]
      exact hzγ
  have hrelative : closure (gammaTᶜ : Set T) =
      Subtype.val ⁻¹' closure (T \ gamma) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hcoimage]
  have htcompact : IsCompact (T : Set ℂ) := by
    have hrange : Set.range (fun c : Circle => (b c : ℂ)) = T := by
      ext z
      constructor
      · rintro ⟨c, rfl⟩
        exact (b _).property
      · intro hz
        obtain ⟨c, hc⟩ := b.surjective ⟨z, hz⟩
        exact ⟨c, congrArg (fun x : T => (x : ℂ)) hc⟩
    rw [← hrange, ← Set.image_univ]
    exact isCompact_univ.image (continuous_subtype_val.comp b.continuous)
  have hTclosed : IsClosed (T : Set ℂ) := htcompact.isClosed
  have hclosureSub : closure (T \ gamma) ⊆ T :=
    closure_minimal Set.sdiff_subset hTclosed
  have himage : b '' gamma' = gammaT := by
    ext z
    constructor
    · rintro ⟨c, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, by simp [f, p]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨f t, ⟨t, rfl⟩, by simp [f, p]⟩
  have hcomp : b '' (gamma'ᶜ : Set Circle) = gammaTᶜ := by
    ext z
    constructor
    · rintro ⟨c, hc, rfl⟩ hz
      have hz' : b c ∈ b '' gamma' := by
        change b c ∈ gammaT at hz
        simpa only [himage] using hz
      rcases hz' with ⟨d, hd, hdc⟩
      apply hc
      exact b.injective hdc ▸ hd
    · intro hz
      refine ⟨b.symm z, ?_, by simp⟩
      intro hc
      apply hz
      rw [← himage]
      exact ⟨b.symm z, hc, b.apply_symm_apply z⟩
  have hclosure : b '' closure (gamma'ᶜ : Set Circle) = closure (gammaTᶜ) := by
    rw [b.image_closure, hcomp]
  have hto (x : {x : Circle // x ∈ closure (gamma'ᶜ : Set Circle)}) :
      b x.1 ∈ closure (gammaTᶜ) := by
    have hx : b x.1 ∈ b '' closure (gamma'ᶜ : Set Circle) := ⟨x.1, x.2, rfl⟩
    rw [hclosure] at hx
    exact hx
  have hinv (x : {x : T // x ∈ closure (gammaTᶜ)}) :
      b.symm x.1 ∈ closure (gamma'ᶜ : Set Circle) := by
    have hx : x.1 ∈ b '' closure (gamma'ᶜ : Set Circle) := by
      rw [hclosure]
      exact x.2
    rcases hx with ⟨c, hc, hcz⟩
    have : c = b.symm x.1 := by
      apply b.injective
      simpa using hcz
    simpa [this] using hc
  let e : {x : Circle // x ∈ closure (gamma'ᶜ : Set Circle)} ≃ₜ
      {x : T // x ∈ closure (gammaTᶜ)} := {
    toFun := fun x => ⟨b x.1, hto x⟩
    invFun := fun x => ⟨b.symm x.1, hinv x⟩
    left_inv := by intro x; apply Subtype.ext; exact b.symm_apply_apply x.1
    right_inv := by intro x; apply Subtype.ext; exact b.apply_symm_apply x.1
    continuous_toFun := (b.continuous.comp continuous_subtype_val).subtype_mk hto
    continuous_invFun := (b.symm.continuous.comp continuous_subtype_val).subtype_mk hinv }
  let k : {x : T // x ∈ closure (gammaTᶜ)} ≃ₜ closure (T \ gamma) := {
    toFun := fun x => ⟨(x.1 : ℂ), by
      have hx : x.1 ∈ Subtype.val ⁻¹' closure (T \ gamma) := by
        rw [← hrelative]
        exact x.2
      exact hx⟩
    invFun := fun x => ⟨⟨x.1, hclosureSub x.2⟩, by
      change (⟨x.1, hclosureSub x.2⟩ : T) ∈ closure (gammaTᶜ)
      rw [hrelative]
      exact x.2⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun x => by
        have hx : x.1 ∈ Subtype.val ⁻¹' closure (T \ gamma) := by
          rw [← hrelative]
          exact x.2
        exact hx)
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk (fun x => hclosureSub x.2)).subtype_mk
        (fun x => by
          change (⟨x.1, hclosureSub x.2⟩ : T) ∈ closure (gammaTᶜ)
          rw [hrelative]
          exact x.2) }
  let psi : Set.Icc (-1 : ℝ) 1 ≃ₜ closure (T \ gamma) := psiC.trans (e.trans k)
  have hmeetC := circle_arc_inter_complement_closure_eq_endpoints gamma' phi' hproper'
  have hgamPre (z : T) : z ∈ gammaT ↔ b.symm z ∈ gamma' := by
    constructor
    · intro hz
      rw [← himage] at hz
      rcases hz with ⟨c, hc, hcz⟩
      have hceq : c = b.symm z := by
        apply b.injective
        exact hcz.trans (b.apply_symm_apply z).symm
      simpa [hceq] using hc
    · intro hz
      rw [← himage]
      exact ⟨b.symm z, hz, b.apply_symm_apply z⟩
  have hclPre (z : T) : z ∈ closure (gammaTᶜ) ↔
      b.symm z ∈ closure (gamma'ᶜ : Set Circle) := by
    constructor
    · intro hz
      rw [← hclosure] at hz
      rcases hz with ⟨c, hc, hcz⟩
      have hceq : c = b.symm z := by
        apply b.injective
        exact hcz.trans (b.apply_symm_apply z).symm
      simpa [hceq] using hc
    · intro hz
      rw [← hclosure]
      exact ⟨b.symm z, hz, b.apply_symm_apply z⟩
  have hmeetT : gammaT ∩ closure (gammaTᶜ) =
      {p ⟨-1, by norm_num⟩, p ⟨1, by norm_num⟩} := by
    ext z
    constructor
    · intro hz
      have hc : b.symm z ∈ gamma' ∩ closure (gamma'ᶜ : Set Circle) :=
        ⟨(hgamPre z).mp hz.1, (hclPre z).mp hz.2⟩
      rw [hmeetC] at hc
      change b.symm z = (phi' ⟨-1, by norm_num⟩ : Circle) ∨
        b.symm z = (phi' ⟨1, by norm_num⟩ : Circle) at hc
      rcases hc with hc | hc
      · left
        have hb0 : b (phi' ⟨-1, by norm_num⟩ : Circle) = p ⟨-1, by norm_num⟩ := by
          change b (f ⟨-1, by norm_num⟩) = p ⟨-1, by norm_num⟩
          simp [f]
        calc z = b (b.symm z) := (b.apply_symm_apply z).symm
          _ = b (phi' ⟨-1, by norm_num⟩ : Circle) := congrArg b hc
          _ = p ⟨-1, by norm_num⟩ := hb0
      · right
        have hb1 : b (phi' ⟨1, by norm_num⟩ : Circle) = p ⟨1, by norm_num⟩ := by
          change b (f ⟨1, by norm_num⟩) = p ⟨1, by norm_num⟩
          simp [f]
        calc z = b (b.symm z) := (b.apply_symm_apply z).symm
          _ = b (phi' ⟨1, by norm_num⟩ : Circle) := congrArg b hc
          _ = p ⟨1, by norm_num⟩ := hb1
    · intro hz
      rcases hz with hz | hz
      · subst z
        constructor
        · exact ⟨⟨-1, by norm_num⟩, rfl⟩
        · have hc : (phi' ⟨-1, by norm_num⟩ : Circle) ∈
              closure (gamma'ᶜ : Set Circle) := by
            have hmc := hmeetC
            have hh : (phi' ⟨-1, by norm_num⟩ : Circle) ∈
                gamma' ∩ closure (gamma'ᶜ : Set Circle) := by
              rw [hmc]
              simp
            exact hh.2
          have hb0 : b (phi' ⟨-1, by norm_num⟩ : Circle) = p ⟨-1, by norm_num⟩ := by
            change b (f ⟨-1, by norm_num⟩) = p ⟨-1, by norm_num⟩
            simp [f]
          have hx : p ⟨-1, by norm_num⟩ ∈ b '' closure (gamma'ᶜ : Set Circle) :=
            ⟨phi' ⟨-1, by norm_num⟩, hc, hb0⟩
          rw [hclosure] at hx
          exact hx
      · subst z
        constructor
        · exact ⟨⟨1, by norm_num⟩, rfl⟩
        · have hc : (phi' ⟨1, by norm_num⟩ : Circle) ∈
              closure (gamma'ᶜ : Set Circle) := by
            have hmc := hmeetC
            have hh : (phi' ⟨1, by norm_num⟩ : Circle) ∈
                gamma' ∩ closure (gamma'ᶜ : Set Circle) := by
              rw [hmc]
              simp
            exact hh.2
          have hb1 : b (phi' ⟨1, by norm_num⟩ : Circle) = p ⟨1, by norm_num⟩ := by
            change b (f ⟨1, by norm_num⟩) = p ⟨1, by norm_num⟩
            simp [f]
          have hx : p ⟨1, by norm_num⟩ ∈ b '' closure (gamma'ᶜ : Set Circle) :=
            ⟨phi' ⟨1, by norm_num⟩, hc, hb1⟩
          rw [hclosure] at hx
          exact hx
  refine ⟨psi, ?_, ?_, ?_⟩
  · change (b ((psiC ⟨-1, by norm_num⟩ : {x : Circle // _}).1) : ℂ) = _
    rw [hpsi0]
    change (b (phi' ⟨1, by norm_num⟩ : gamma') : ℂ) = _
    change (b (f ⟨1, by norm_num⟩) : ℂ) = _
    simp [f, p]
  · change (b ((psiC ⟨1, by norm_num⟩ : {x : Circle // _}).1) : ℂ) = _
    rw [hpsi1]
    change (b (phi' ⟨-1, by norm_num⟩ : gamma') : ℂ) = _
    change (b (f ⟨-1, by norm_num⟩) : ℂ) = _
    simp [f, p]
  · ext z
    constructor
    · rintro ⟨hzγ, hzcl⟩
      have hzT : (⟨z, hgamma hzγ⟩ : T) ∈ gammaT := by
        rw [hgammaT]
        exact hzγ
      have hzrel : (⟨z, hgamma hzγ⟩ : T) ∈ closure (gammaTᶜ) := by
        rw [hrelative]
        exact hzcl
      have hzpair : (⟨z, hgamma hzγ⟩ : T) ∈
          ({p ⟨-1, by norm_num⟩, p ⟨1, by norm_num⟩} : Set T) := by
        rw [← hmeetT]
        exact ⟨hzT, hzrel⟩
      have hzmeet : z = (phi ⟨-1, by norm_num⟩ : ℂ) ∨
          z = (phi ⟨1, by norm_num⟩ : ℂ) := by
        simpa [p] using hzpair
      rcases hzmeet with hz | hz
      · left
        exact hz
      · right
        simpa only [Set.mem_singleton_iff] using hz
    · intro hz
      rcases hz with hz | hz
      · subst z
        refine ⟨(phi ⟨-1, by norm_num⟩).property, ?_⟩
        have hm : p ⟨-1, by norm_num⟩ ∈ gammaT ∩ closure (gammaTᶜ) := by
          rw [hmeetT]
          simp
        have hmem := hm.2
        rw [hrelative] at hmem
        simpa only [Set.mem_preimage] using hmem
      · have hz' : z = (phi ⟨1, by norm_num⟩ : ℂ) := by
          simpa only [Set.mem_singleton_iff] using hz
        subst z
        refine ⟨(phi ⟨1, by norm_num⟩).property, ?_⟩
        have hm : p ⟨1, by norm_num⟩ ∈ gammaT ∩ closure (gammaTᶜ) := by
          rw [hmeetT]
          simp
        have hmem := hm.2
        rw [hrelative] at hmem
        simpa only [Set.mem_preimage] using hmem

/-- Helper toward Proposition 5.16: the boundary of the upper half-disk model. -/
abbrev polygonDiskUpperHalfBoundary : Type :=
  {x : polygonDiskUpperHalf //
    ‖(((x : Metric.closedBall (0 : ℂ) 1) : ℂ))‖ = 1 ∨
      (((x : Metric.closedBall (0 : ℂ) 1) : ℂ)).im = 0}

/-- Helper toward Proposition 5.16: the diameter piece of the upper half-disk boundary. -/
@[expose] def polygonDiskUpperHalfBoundaryDiameter :
    Set polygonDiskUpperHalfBoundary :=
  {x | (((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)).im = 0}

/-- Helper toward Proposition 5.16: the semicircle piece of the upper half-disk boundary. -/
@[expose] def polygonDiskUpperHalfBoundarySemicircle :
    Set polygonDiskUpperHalfBoundary :=
  {x | ‖((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1}

/-- Helper toward Proposition 5.16: the model boundary is a closed cover by
its diameter and its outer semicircle. -/
theorem polygonDiskUpperHalfBoundary_closed_cover :
    IsClosed polygonDiskUpperHalfBoundaryDiameter ∧
      IsClosed polygonDiskUpperHalfBoundarySemicircle ∧
      polygonDiskUpperHalfBoundaryDiameter ∪ polygonDiskUpperHalfBoundarySemicircle =
        Set.univ := by
  let im : polygonDiskUpperHalfBoundary → ℝ := fun x =>
    (((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)).im
  let norm : polygonDiskUpperHalfBoundary → ℝ := fun x =>
    ‖((x.1 : Metric.closedBall (0 : ℂ) 1) : ℂ)‖
  have him : Continuous im :=
    Complex.continuous_im.comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))
  have hnorm : Continuous norm :=
    continuous_norm.comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))
  refine ⟨?_, ?_, ?_⟩
  · change IsClosed (im ⁻¹' {0})
    exact isClosed_singleton.preimage him
  · change IsClosed (norm ⁻¹' {1})
    exact isClosed_singleton.preimage hnorm
  · ext x
    constructor
    · intro _
      trivial
    · intro _
      simp only [Set.mem_union, polygonDiskUpperHalfBoundaryDiameter,
        polygonDiskUpperHalfBoundarySemicircle, Set.mem_ofPred_eq]
      rcases x.property with hn | hi
      · exact Or.inr hn
      · exact Or.inl hi







































end DirectedDistances.PlanarMap
