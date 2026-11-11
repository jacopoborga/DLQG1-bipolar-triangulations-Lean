/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLOuterChart

/-! Helpers toward Proposition 5.16: finite closed-piece pasting for the
outer-chart construction. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap
open Set Topology

/-- Helper toward Proposition 5.16: three closed pieces with exact overlap
correspondence paste to a homeomorphism when their maps agree on overlaps. -/
theorem exists_homeomorph_of_three_closed_covers_of_overlap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (s : Fin 3 → Set X) (t : Fin 3 → Set Y)
    (hs : ∀ i, IsClosed (s i)) (ht : ∀ i, IsClosed (t i))
    (hcover : ⋃ i, s i = univ) (hcover' : ⋃ i, t i = univ)
    (e : ∀ i, s i ≃ₜ t i)
    (hinter : ∀ i j (x : s i), (e i x : Y) ∈ t j ↔ (x : X) ∈ s j)
    (hagree : ∀ i j (x : X) (hi : x ∈ s i) (hj : x ∈ s j),
      (e i ⟨x, hi⟩ : Y) = (e j ⟨x, hj⟩ : Y)) :
    ∃ H : X ≃ₜ Y, ∀ i (x : s i), H x = (e i x : Y) := by
  exact exists_homeomorph_of_finite_closed_covers_of_overlap
    s t hs ht hcover hcover' e hinter hagree

/-- Helper toward Proposition 5.16: matching boundary maps on a parameterized
arc yield inside extensions that agree on the full common arc in both directions. -/
theorem Polyline.exists_two_inside_extensions_agree_on_parameterized_arc
    (p q p' q' : Polyline)
    (hp : p.IsCyclicSimple) (hq : q.IsCyclicSimple)
    (hp' : p'.IsCyclicSimple) (hq' : q'.IsCyclicSimple)
    (f : p.image ≃ₜ p'.image) (g : q.image ≃ₜ q'.image)
    (A B : Set ℂ) (hAp : A ⊆ p.image) (hAq : A ⊆ q.image)
    (hBp : B ⊆ p'.image) (hBq : B ⊆ q'.image)
    (phi : Icc (-1 : ℝ) 1 ≃ₜ A) (psi : Icc (-1 : ℝ) 1 ≃ₜ B)
    (hf : ∀ u, (f ⟨phi u, hAp (phi u).property⟩ : ℂ) = (psi u : ℂ))
    (hg : ∀ u, (g ⟨phi u, hAq (phi u).property⟩ : ℂ) = (psi u : ℂ)) :
    ∃ H : closure p.inside ≃ₜ closure p'.inside,
    ∃ K : closure q.inside ≃ₜ closure q'.inside,
      (∀ x : A,
        (H ⟨x, p.image_subset_closure_inside_cyclic hp (hAp x.property)⟩ : ℂ) =
          (K ⟨x, q.image_subset_closure_inside_cyclic hq (hAq x.property)⟩ : ℂ)) ∧
      (∀ y : B,
        (H.symm ⟨y, p'.image_subset_closure_inside_cyclic hp' (hBp y.property)⟩ : ℂ) =
          (K.symm ⟨y, q'.image_subset_closure_inside_cyclic hq' (hBq y.property)⟩ : ℂ)) := by
  obtain ⟨H, hH⟩ := p.exists_inside_homeomorph_extending_boundary p' hp hp' f
  obtain ⟨K, hK⟩ := q.exists_inside_homeomorph_extending_boundary q' hq hq' g
  have hH' : ∀ u,
      (H ⟨phi u, p.image_subset_closure_inside_cyclic hp (hAp (phi u).property)⟩ : ℂ) =
        (psi u : ℂ) := by
    intro u
    exact (hH ⟨phi u, hAp (phi u).property⟩).trans (hf u)
  have hK' : ∀ u,
      (K ⟨phi u, q.image_subset_closure_inside_cyclic hq (hAq (phi u).property)⟩ : ℂ) =
        (psi u : ℂ) := by
    intro u
    exact (hK ⟨phi u, hAq (phi u).property⟩).trans (hg u)
  obtain ⟨hforward, hinverse⟩ :=
    Polyline.piece_extensions_agree_on_parameterized_arc p q p' q' A B
      (fun x hx => p.image_subset_closure_inside_cyclic hp (hAp hx))
      (fun x hx => q.image_subset_closure_inside_cyclic hq (hAq hx))
      (fun x hx => p'.image_subset_closure_inside_cyclic hp' (hBp hx))
      (fun x hx => q'.image_subset_closure_inside_cyclic hq' (hBq hx))
      phi psi H K hH' hK'
  exact ⟨H, K, hforward, hinverse⟩











































end DirectedDistances.PlanarMap
