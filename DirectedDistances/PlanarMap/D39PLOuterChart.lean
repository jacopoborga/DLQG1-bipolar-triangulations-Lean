/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLFaceExtension5
public import DirectedDistances.PlanarMap.D39PLArcGluing





public section
noncomputable section
namespace DirectedDistances.PlanarMap
open Set Topology

/-- Helper toward Proposition 5.16: a simple nonclosed polyline admits an
interval parameter with its specified initial and terminal endpoints. -/
@[expose] def SimpleArcParamStatement : Prop :=
  ∀ p : Polyline, p.IsSimple → p.start ≠ p.finish →
    ∃ phi : Icc (-1 : ℝ) 1 ≃ₜ p.image,
      (phi ⟨-1, by norm_num⟩ : ℂ) = p.start ∧
      (phi ⟨1, by norm_num⟩ : ℂ) = p.finish

/-- Helper toward Proposition 5.16: a prescribed square boundary map extends
over the closed unbounded complementary regions, retaining every boundary value. -/
@[expose] def SquareConeStatement : Prop :=
  ∀ (R R' : ℝ) (hR : 0 < R) (_hR' : 0 < R')
    (g : (Polyline.enclosingSquare R).image ≃ₜ (Polyline.enclosingSquare R').image),
    ∃ E : closure (Polyline.enclosingSquare R).outside ≃ₜ
        closure (Polyline.enclosingSquare R').outside,
      ∀ x : (Polyline.enclosingSquare R).image,
        (E ⟨x, (Polyline.enclosingSquare R).image_subset_closure_outside_cyclic
          (Polyline.enclosingSquare_isCyclicSimple R hR) x.property⟩ : ℂ) = (g x : ℂ)

/-- Helper toward Proposition 5.16: an included planar set and its copy inside
an ambient subtype are homeomorphic without changing the planar coordinates. -/
@[expose] def subsetSubtypeHomeomorph (A S : Set ℂ) (hAS : A ⊆ S) :
    A ≃ₜ {x : S | (x : ℂ) ∈ A} where
  toFun x := ⟨⟨x, hAS x.property⟩, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Helper toward Proposition 5.16: finitely many interval-parameterized arcs
give a boundary homeomorphism when the source and target parameters have exactly
the same collisions. Every parameter, including all seam endpoints, is retained. -/
theorem exists_homeomorph_of_finite_parameterized_arcs
    {ι : Type*} [Finite ι] (A B : ι → Set ℂ) (S T : Set ℂ)
    (hA : ∀ i, IsClosed (A i)) (hB : ∀ i, IsClosed (B i))
    (hS : ⋃ i, A i = S) (hT : ⋃ i, B i = T)
    (phi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ A i)
    (psi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ B i)
    (hcollision : ∀ i j u v,
      (phi i u : ℂ) = (phi j v : ℂ) ↔ (psi i u : ℂ) = (psi j v : ℂ)) :
    ∃ H : S ≃ₜ T, ∀ i u,
      (H ⟨phi i u, hS ▸ mem_iUnion.mpr ⟨i, (phi i u).property⟩⟩ : ℂ) =
        (psi i u : ℂ) := by
  let s : ι → Set S := fun i => {x | (x : ℂ) ∈ A i}
  let t : ι → Set T := fun i => {x | (x : ℂ) ∈ B i}
  have hAS (i) : A i ⊆ S := fun _ hx => hS ▸ mem_iUnion.mpr ⟨i, hx⟩
  have hBT (i) : B i ⊆ T := fun _ hx => hT ▸ mem_iUnion.mpr ⟨i, hx⟩
  let a (i) : Icc (-1 : ℝ) 1 ≃ₜ s i :=
    (phi i).trans (subsetSubtypeHomeomorph (A i) S (hAS i))
  let b (i) : Icc (-1 : ℝ) 1 ≃ₜ t i :=
    (psi i).trans (subsetSubtypeHomeomorph (B i) T (hBT i))
  let e (i) : s i ≃ₜ t i := (a i).symm.trans (b i)
  have hscover : ⋃ i, s i = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    change ∃ i, (x : ℂ) ∈ A i
    have hx : (x : ℂ) ∈ ⋃ i, A i := hS.symm ▸ x.property
    exact mem_iUnion.mp hx
  have htcover : ⋃ i, t i = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    change ∃ i, (x : ℂ) ∈ B i
    have hx : (x : ℂ) ∈ ⋃ i, B i := hT.symm ▸ x.property
    exact mem_iUnion.mp hx
  have agree : ∀ i j (x : S) (hi : x ∈ s i) (hj : x ∈ s j),
      (e i ⟨x, hi⟩ : T) = (e j ⟨x, hj⟩ : T) := by
    intro i j x hi hj
    let u := (a i).symm ⟨x, hi⟩
    let v := (a j).symm ⟨x, hj⟩
    have hu : (phi i u : ℂ) = (x : ℂ) :=
      congrArg (fun z : s i => ((z : S) : ℂ)) ((a i).apply_symm_apply ⟨x, hi⟩)
    have hv : (phi j v : ℂ) = (x : ℂ) :=
      congrArg (fun z : s j => ((z : S) : ℂ)) ((a j).apply_symm_apply ⟨x, hj⟩)
    exact Subtype.ext ((hcollision i j u v).mp (hu.trans hv.symm))
  have agree' : ∀ i j (y : T) (hi : y ∈ t i) (hj : y ∈ t j),
      ((e i).symm ⟨y, hi⟩ : S) = ((e j).symm ⟨y, hj⟩ : S) := by
    intro i j y hi hj
    let u := (b i).symm ⟨y, hi⟩
    let v := (b j).symm ⟨y, hj⟩
    have hu : (psi i u : ℂ) = (y : ℂ) :=
      congrArg (fun z : t i => ((z : T) : ℂ)) ((b i).apply_symm_apply ⟨y, hi⟩)
    have hv : (psi j v : ℂ) = (y : ℂ) :=
      congrArg (fun z : t j => ((z : T) : ℂ)) ((b j).apply_symm_apply ⟨y, hj⟩)
    exact Subtype.ext ((hcollision i j u v).mpr (hu.trans hv.symm))
  obtain ⟨H, hH⟩ := exists_homeomorph_of_finite_closed_covers s t
    (fun i => (hA i).preimage continuous_subtype_val)
    (fun i => (hB i).preimage continuous_subtype_val)
    hscover htcover e agree agree'
  refine ⟨H, fun i u => ?_⟩
  have h := congrArg (fun z : T => (z : ℂ)) (hH i (a i u))
  simp only [e, Homeomorph.trans_apply, Homeomorph.symm_apply_apply] at h
  change (H ⟨phi i u, _⟩ : ℂ) = (psi i u : ℂ) at h
  exact h

/-- Helper toward Proposition 5.16: a compatible finite arc boundary map
extends over a cyclically simple polygon piece with the same arc parameters. -/
theorem Polyline.exists_piece_extension_of_parameterized_arcs
    {ι : Type*} [Finite ι] (p q : Polyline)
    (hp : p.IsCyclicSimple) (hq : q.IsCyclicSimple)
    (A B : ι → Set ℂ) (hA : ∀ i, IsClosed (A i)) (hB : ∀ i, IsClosed (B i))
    (hP : ⋃ i, A i = p.image) (hQ : ⋃ i, B i = q.image)
    (phi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ A i)
    (psi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ B i)
    (hcollision : ∀ i j u v,
      (phi i u : ℂ) = (phi j v : ℂ) ↔ (psi i u : ℂ) = (psi j v : ℂ)) :
    ∃ H : closure p.inside ≃ₜ closure q.inside, ∀ i u,
      (H ⟨phi i u, p.image_subset_closure_inside_cyclic hp
        (hP ▸ mem_iUnion.mpr ⟨i, (phi i u).property⟩)⟩ : ℂ) = (psi i u : ℂ) := by
  obtain ⟨f, hf⟩ := exists_homeomorph_of_finite_parameterized_arcs
    A B p.image q.image hA hB hP hQ phi psi hcollision
  obtain ⟨H, hH⟩ := p.exists_inside_homeomorph_extending_boundary q hp hq f
  refine ⟨H, fun i u => ?_⟩
  exact (hH ⟨phi i u, hP ▸ mem_iUnion.mpr ⟨i, (phi i u).property⟩⟩).trans (hf i u)

/-- Helper toward Proposition 5.16: when two parameterized arcs meet in one
specified common endpoint, equality of their points detects exactly those parameters. -/
theorem parameterized_arcs_eq_iff_of_inter_singleton
    (A B : Set ℂ) (phi : Icc (-1 : ℝ) 1 ≃ₜ A)
    (psi : Icc (-1 : ℝ) 1 ≃ₜ B) (u₀ v₀ : Icc (-1 : ℝ) 1)
    (hjoin : (phi u₀ : ℂ) = (psi v₀ : ℂ))
    (hinter : A ∩ B = {(phi u₀ : ℂ)}) (u v : Icc (-1 : ℝ) 1) :
    (phi u : ℂ) = (psi v : ℂ) ↔ u = u₀ ∧ v = v₀ := by
  constructor
  · intro h
    have hm : (phi u : ℂ) ∈ A ∩ B := ⟨(phi u).property, h.symm ▸ (psi v).property⟩
    rw [hinter, mem_singleton_iff] at hm
    exact ⟨phi.injective (Subtype.ext hm),
      psi.injective (Subtype.ext (h.symm.trans (hm.trans hjoin)))⟩
  · rintro ⟨rfl, rfl⟩
    exact hjoin

/-- Helper toward Proposition 5.16: cycles of four closed parameterized arcs
have identical parameter collisions if successive arcs share just their ordered
endpoints and opposite arcs are disjoint. No four-arc gluing premise is used. -/
theorem four_parameterized_arcs_collision_iff
    (A B : Fin 4 → Set ℂ)
    (phi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ A i)
    (psi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ B i)
    (hjoin : ∀ i, (phi i ⟨1, by norm_num⟩ : ℂ) =
      (phi (i + 1) ⟨-1, by norm_num⟩ : ℂ))
    (hjoin' : ∀ i, (psi i ⟨1, by norm_num⟩ : ℂ) =
      (psi (i + 1) ⟨-1, by norm_num⟩ : ℂ))
    (hmeet : ∀ i, A i ∩ A (i + 1) = {(phi i ⟨1, by norm_num⟩ : ℂ)})
    (hmeet' : ∀ i, B i ∩ B (i + 1) = {(psi i ⟨1, by norm_num⟩ : ℂ)})
    (hopp : ∀ i, A i ∩ A (i + 2) = ∅)
    (hopp' : ∀ i, B i ∩ B (i + 2) = ∅) :
    ∀ i j u v,
      (phi i u : ℂ) = (phi j v : ℂ) ↔ (psi i u : ℂ) = (psi j v : ℂ) := by
  have same (i : Fin 4) (u v : Icc (-1 : ℝ) 1) :
      (phi i u : ℂ) = (phi i v : ℂ) ↔ (psi i u : ℂ) = (psi i v : ℂ) := by
    constructor
    · intro h
      exact congrArg (fun z => (psi i z : ℂ)) ((phi i).injective (Subtype.ext h))
    · intro h
      exact congrArg (fun z => (phi i z : ℂ)) ((psi i).injective (Subtype.ext h))
  have next (i : Fin 4) (u v : Icc (-1 : ℝ) 1) :
      (phi i u : ℂ) = (phi (i + 1) v : ℂ) ↔
        (psi i u : ℂ) = (psi (i + 1) v : ℂ) := by
    rw [parameterized_arcs_eq_iff_of_inter_singleton _ _ _ _ _ _ (hjoin i) (hmeet i),
      parameterized_arcs_eq_iff_of_inter_singleton _ _ _ _ _ _ (hjoin' i) (hmeet' i)]
  have opposite (i : Fin 4) (u v : Icc (-1 : ℝ) 1) :
      (phi i u : ℂ) = (phi (i + 2) v : ℂ) ↔
        (psi i u : ℂ) = (psi (i + 2) v : ℂ) := by
    have hn : (phi i u : ℂ) ≠ (phi (i + 2) v : ℂ) := by
      intro h
      have hm : (phi i u : ℂ) ∈ A i ∩ A (i + 2) :=
        ⟨(phi i u).property, h.symm ▸ (phi (i + 2) v).property⟩
      rw [hopp i] at hm
      exact hm
    have hn' : (psi i u : ℂ) ≠ (psi (i + 2) v : ℂ) := by
      intro h
      have hm : (psi i u : ℂ) ∈ B i ∩ B (i + 2) :=
        ⟨(psi i u).property, h.symm ▸ (psi (i + 2) v).property⟩
      rw [hopp' i] at hm
      exact hm
    exact iff_of_false hn hn'
  intro i j u v
  have cases : j = i ∨ j = i + 1 ∨ j = i + 2 ∨ i = j + 1 := by
    fin_cases i <;> fin_cases j <;> decide
  rcases cases with h | h | h | h
  · subst j; exact same i u v
  · subst j; exact next i u v
  · subst j; exact opposite i u v
  · subst i
    simpa only [eq_comm] using next j v u

/-- Helper toward Proposition 5.16: two cycles of four parameterized closed
arcs glue to a homeomorphism of their unions, preserving each chosen parameter. -/
theorem exists_homeomorph_of_four_parameterized_arcs
    (A B : Fin 4 → Set ℂ) (S T : Set ℂ)
    (hA : ∀ i, IsClosed (A i)) (hB : ∀ i, IsClosed (B i))
    (hS : ⋃ i, A i = S) (hT : ⋃ i, B i = T)
    (phi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ A i)
    (psi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ B i)
    (hjoin : ∀ i, (phi i ⟨1, by norm_num⟩ : ℂ) =
      (phi (i + 1) ⟨-1, by norm_num⟩ : ℂ))
    (hjoin' : ∀ i, (psi i ⟨1, by norm_num⟩ : ℂ) =
      (psi (i + 1) ⟨-1, by norm_num⟩ : ℂ))
    (hmeet : ∀ i, A i ∩ A (i + 1) = {(phi i ⟨1, by norm_num⟩ : ℂ)})
    (hmeet' : ∀ i, B i ∩ B (i + 1) = {(psi i ⟨1, by norm_num⟩ : ℂ)})
    (hopp : ∀ i, A i ∩ A (i + 2) = ∅)
    (hopp' : ∀ i, B i ∩ B (i + 2) = ∅) :
    ∃ H : S ≃ₜ T, ∀ i u,
      (H ⟨phi i u, hS ▸ mem_iUnion.mpr ⟨i, (phi i u).property⟩⟩ : ℂ) =
        (psi i u : ℂ) :=
  exists_homeomorph_of_finite_parameterized_arcs A B S T hA hB hS hT phi psi
    (four_parameterized_arcs_collision_iff A B phi psi hjoin hjoin'
      hmeet hmeet' hopp hopp')

/-- Helper toward Proposition 5.16: simple arc parameters give an endpoint
preserving homeomorphism between two nonclosed simple polyline images. -/
theorem Polyline.exists_arc_homeomorph_of_simple_arc_parameters
    (hP1 : SimpleArcParamStatement) (p q : Polyline)
    (hp : p.IsSimple) (hq : q.IsSimple)
    (hpne : p.start ≠ p.finish) (hqne : q.start ≠ q.finish) :
    ∃ f : p.image ≃ₜ q.image,
      (∀ x : p.image, (x : ℂ) = p.start → (f x : ℂ) = q.start) ∧
      (∀ x : p.image, (x : ℂ) = p.finish → (f x : ℂ) = q.finish) := by
  obtain ⟨phi, hphi₀, hphi₁⟩ := hP1 p hp hpne
  obtain ⟨psi, hpsi₀, hpsi₁⟩ := hP1 q hq hqne
  refine ⟨phi.symm.trans psi, ?_, ?_⟩
  · intro x hx
    have he : x = phi ⟨-1, by norm_num⟩ := Subtype.ext (hx.trans hphi₀.symm)
    rw [he, Homeomorph.trans_apply, phi.symm_apply_apply]
    exact hpsi₀
  · intro x hx
    have he : x = phi ⟨1, by norm_num⟩ := Subtype.ext (hx.trans hphi₁.symm)
    rw [he, Homeomorph.trans_apply, phi.symm_apply_apply]
    exact hpsi₁

/-- Helper toward Proposition 5.16: the simple-arc ingredient constructs a
boundary map for four polyline arcs in cyclic order, from their endpoint and
intersection data alone. The endpoint parameters are part of the conclusion. -/
theorem Polyline.exists_four_arc_boundary_map
    (hP1 : SimpleArcParamStatement) (a b : Fin 4 → Polyline) (S T : Set ℂ)
    (ha : ∀ i, (a i).IsSimple) (hb : ∀ i, (b i).IsSimple)
    (hane : ∀ i, (a i).start ≠ (a i).finish)
    (hbne : ∀ i, (b i).start ≠ (b i).finish)
    (hS : ⋃ i, (a i).image = S) (hT : ⋃ i, (b i).image = T)
    (hjoin : ∀ i, (a i).finish = (a (i + 1)).start)
    (hjoin' : ∀ i, (b i).finish = (b (i + 1)).start)
    (hmeet : ∀ i, (a i).image ∩ (a (i + 1)).image = {(a i).finish})
    (hmeet' : ∀ i, (b i).image ∩ (b (i + 1)).image = {(b i).finish})
    (hopp : ∀ i, (a i).image ∩ (a (i + 2)).image = ∅)
    (hopp' : ∀ i, (b i).image ∩ (b (i + 2)).image = ∅) :
    ∃ (phi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ (a i).image)
      (psi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ (b i).image) (H : S ≃ₜ T),
      (∀ i, (phi i ⟨-1, by norm_num⟩ : ℂ) = (a i).start) ∧
      (∀ i, (phi i ⟨1, by norm_num⟩ : ℂ) = (a i).finish) ∧
      (∀ i, (psi i ⟨-1, by norm_num⟩ : ℂ) = (b i).start) ∧
      (∀ i, (psi i ⟨1, by norm_num⟩ : ℂ) = (b i).finish) ∧
      ∀ i u,
        (H ⟨phi i u, hS ▸ mem_iUnion.mpr ⟨i, (phi i u).property⟩⟩ : ℂ) =
          (psi i u : ℂ) := by
  choose phi hphi₀ hphi₁ using fun i => hP1 (a i) (ha i) (hane i)
  choose psi hpsi₀ hpsi₁ using fun i => hP1 (b i) (hb i) (hbne i)
  obtain ⟨H, hH⟩ := exists_homeomorph_of_four_parameterized_arcs
    (fun i => (a i).image) (fun i => (b i).image) S T
    (fun i => (a i).isCompact_image.isClosed)
    (fun i => (b i).isCompact_image.isClosed) hS hT phi psi
    (fun i => (hphi₁ i).trans ((hjoin i).trans (hphi₀ (i + 1)).symm))
    (fun i => (hpsi₁ i).trans ((hjoin' i).trans (hpsi₀ (i + 1)).symm))
    (fun i => (hmeet i).trans (congrArg singleton (hphi₁ i).symm))
    (fun i => (hmeet' i).trans (congrArg singleton (hpsi₁ i).symm)) hopp hopp'
  exact ⟨phi, psi, H, hphi₀, hphi₁, hpsi₀, hpsi₁, hH⟩

/-- Helper toward Proposition 5.16: strict nesting places the whole closed
outside of the outer polygon in the closed outside of the inner polygon. -/
theorem Polyline.closed_outside_subset_closed_outside_of_nested
    (c Q : Polyline) (hc : c.IsCyclicSimple) (hQ : Q.IsCyclicSimple)
    (hnest : closure c.inside ⊆ Q.inside) :
    closure Q.outside ⊆ closure c.outside := by
  have hd := (Polyline.nested_closed_annulus_cover c Q hc hQ hnest).2.2.2
  intro z hz
  have hf : z ∈ closure c.inside ∪ closure c.outside :=
    (c.closed_faces_union_inter_cyclic hc).1.symm ▸ mem_univ z
  exact hf.resolve_left (fun hi => Set.disjoint_left.mp hd hi hz)

/-- Helper toward Proposition 5.16: an annulus partition and the outer closed
outside form exactly the three closed pieces of the inner closed outside. -/
theorem Polyline.closed_outside_eq_cut_pieces_union
    (c Q p q : Polyline) (hc : c.IsCyclicSimple) (hQ : Q.IsCyclicSimple)
    (hnest : closure c.inside ⊆ Q.inside)
    (hpartition : closure p.inside ∪ closure q.inside =
      closure c.outside ∩ closure Q.inside) :
    closure c.outside = (closure p.inside ∪ closure q.inside) ∪ closure Q.outside := by
  rw [hpartition]
  apply Subset.antisymm
  · intro z hz
    have hf : z ∈ closure Q.inside ∪ closure Q.outside :=
      (Q.closed_faces_union_inter_cyclic hQ).1.symm ▸ mem_univ z
    exact hf.elim (fun hi => Or.inl ⟨hz, hi⟩) Or.inr
  · rintro z (hz | hz)
    · exact hz.1
    · exact c.closed_outside_subset_closed_outside_of_nested Q hc hQ hnest hz

/-- Helper toward Proposition 5.16: a closed polygon piece contained in a
closed inside meets the corresponding closed outside exactly on both boundaries. -/
theorem Polyline.closed_inside_inter_closed_outside_eq_boundary_inter
    (p Q : Polyline) (hp : p.IsCyclicSimple) (hQ : Q.IsCyclicSimple)
    (hsubset : closure p.inside ⊆ closure Q.inside) :
    closure p.inside ∩ closure Q.outside = p.image ∩ Q.image := by
  have hpclosed : p.start = p.finish := by
    rw [← p.point_zero_eq_start, ← p.point_last_eq_finish]
    exact hp.2.1
  have hQclosed : Q.start = Q.finish := by
    rw [← Q.point_zero_eq_start, ← Q.point_last_eq_finish]
    exact hQ.2.1
  have hd : Disjoint p.inside Q.outside := by
    apply Set.disjoint_left.mpr
    intro z hz hw
    exact (Q.closure_sides_avoid hQclosed).1 (hsubset (subset_closure hz)) hw
  have hd' := hd.closure_right (p.isOpen_inside hpclosed)
  apply Subset.antisymm
  · intro z hz
    have hpi : z ∈ p.inside ∪ p.image := p.closure_inside_eq_union_image hp ▸ hz.1
    exact ⟨hpi.resolve_left (fun hi => Set.disjoint_left.mp hd' hi hz.2),
      (Q.closed_faces_union_inter_cyclic hQ).2 ▸ ⟨hsubset hz.1, hz.2⟩⟩
  · intro z hz
    exact ⟨p.image_subset_closure_inside_cyclic hp hz.1,
      Q.image_subset_closure_outside_cyclic hQ hz.2⟩

/-- Helper toward Proposition 5.16: a homeomorphism extending a bijection of
specified subsets maps those subsets onto one another exactly. -/
theorem homeomorph_mem_iff_of_boundary_values
    (S T A B : Set ℂ) (hAS : A ⊆ S) (_hBT : B ⊆ T)
    (H : S ≃ₜ T) (f : A ≃ₜ B)
    (hboundary : ∀ x : A, (H ⟨x, hAS x.property⟩ : ℂ) = (f x : ℂ))
    (x : S) : (H x : ℂ) ∈ B ↔ (x : ℂ) ∈ A := by
  constructor
  · intro hx
    let y : A := f.symm ⟨H x, hx⟩
    have he : H ⟨y, hAS y.property⟩ = H x := by
      apply Subtype.ext
      exact (hboundary y).trans (congrArg Subtype.val (f.apply_symm_apply ⟨H x, hx⟩))
    have hy : (y : ℂ) = (x : ℂ) := congrArg Subtype.val (H.injective he)
    exact hy ▸ y.property
  · intro hx
    have he := hboundary ⟨x, hx⟩
    exact he.symm ▸ (f ⟨x, hx⟩).property

/-- Helper toward Proposition 5.16: extending a polygon boundary map across
the closed inside gives exact boundary correspondence, not just containment. -/
theorem Polyline.inside_extension_mem_image_iff
    (p q : Polyline) (hp : p.IsCyclicSimple) (hq : q.IsCyclicSimple)
    (H : closure p.inside ≃ₜ closure q.inside) (f : p.image ≃ₜ q.image)
    (hboundary : ∀ x : p.image,
      (H ⟨x, p.image_subset_closure_inside_cyclic hp x.property⟩ : ℂ) = (f x : ℂ))
    (x : closure p.inside) : (H x : ℂ) ∈ q.image ↔ (x : ℂ) ∈ p.image :=
  homeomorph_mem_iff_of_boundary_values _ _ _ _
    (p.image_subset_closure_inside_cyclic hp) (q.image_subset_closure_inside_cyclic hq)
    H f hboundary x

/-- Helper toward Proposition 5.16: the square-cone ingredient also gives
exact square-boundary correspondence on the entire closed outside. -/
theorem Polyline.exists_square_cone_with_boundary_iff
    (hP2 : SquareConeStatement) (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R')
    (g : (enclosingSquare R).image ≃ₜ (enclosingSquare R').image) :
    ∃ E : closure (enclosingSquare R).outside ≃ₜ closure (enclosingSquare R').outside,
      (∀ x : (enclosingSquare R).image,
        (E ⟨x, (enclosingSquare R).image_subset_closure_outside_cyclic
          (enclosingSquare_isCyclicSimple R hR) x.property⟩ : ℂ) = (g x : ℂ)) ∧
      ∀ x : closure (enclosingSquare R).outside,
        (E x : ℂ) ∈ (enclosingSquare R').image ↔ (x : ℂ) ∈ (enclosingSquare R).image := by
  obtain ⟨E, hE⟩ := hP2 R R' hR hR' g
  exact ⟨E, hE, homeomorph_mem_iff_of_boundary_values _ _ _ _
    ((enclosingSquare R).image_subset_closure_outside_cyclic (enclosingSquare_isCyclicSimple R hR))
    ((enclosingSquare R').image_subset_closure_outside_cyclic (enclosingSquare_isCyclicSimple R' hR'))
    E g hE⟩

/-- Helper toward Proposition 5.16: two polygon piece extensions constructed
with the same source and target seam parameters agree at every seam point. -/
theorem Polyline.piece_extensions_agree_on_parameterized_arc
    (p q p' q' : Polyline) (A B : Set ℂ)
    (hAp : A ⊆ closure p.inside) (hAq : A ⊆ closure q.inside)
    (hBp : B ⊆ closure p'.inside) (hBq : B ⊆ closure q'.inside)
    (phi : Icc (-1 : ℝ) 1 ≃ₜ A) (psi : Icc (-1 : ℝ) 1 ≃ₜ B)
    (H : closure p.inside ≃ₜ closure p'.inside)
    (K : closure q.inside ≃ₜ closure q'.inside)
    (hH : ∀ u, (H ⟨phi u, hAp (phi u).property⟩ : ℂ) = (psi u : ℂ))
    (hK : ∀ u, (K ⟨phi u, hAq (phi u).property⟩ : ℂ) = (psi u : ℂ)) :
    (∀ x : A, (H ⟨x, hAp x.property⟩ : ℂ) = (K ⟨x, hAq x.property⟩ : ℂ)) ∧
    (∀ y : B, (H.symm ⟨y, hBp y.property⟩ : ℂ) =
      (K.symm ⟨y, hBq y.property⟩ : ℂ)) := by
  constructor
  · intro x
    obtain ⟨u, rfl⟩ := phi.surjective x
    exact (hH u).trans (hK u).symm
  · intro y
    obtain ⟨u, rfl⟩ := psi.surjective y
    have hHi : H ⟨phi u, hAp (phi u).property⟩ = ⟨psi u, hBp (psi u).property⟩ :=
      Subtype.ext (hH u)
    have hKi : K ⟨phi u, hAq (phi u).property⟩ = ⟨psi u, hBq (psi u).property⟩ :=
      Subtype.ext (hK u)
    rw [← hHi, ← hKi, H.symm_apply_apply, K.symm_apply_apply]

/-- Helper toward Proposition 5.16: the four-arc boundary map constructed
from P1 extends over a polygon piece and detects its entire boundary exactly. -/
theorem Polyline.exists_four_arc_piece_extension
    (hP1 : SimpleArcParamStatement) (p q : Polyline)
    (hp : p.IsCyclicSimple) (hq : q.IsCyclicSimple)
    (a b : Fin 4 → Polyline)
    (ha : ∀ i, (a i).IsSimple) (hb : ∀ i, (b i).IsSimple)
    (hane : ∀ i, (a i).start ≠ (a i).finish)
    (hbne : ∀ i, (b i).start ≠ (b i).finish)
    (hP : ⋃ i, (a i).image = p.image) (hQ : ⋃ i, (b i).image = q.image)
    (hjoin : ∀ i, (a i).finish = (a (i + 1)).start)
    (hjoin' : ∀ i, (b i).finish = (b (i + 1)).start)
    (hmeet : ∀ i, (a i).image ∩ (a (i + 1)).image = {(a i).finish})
    (hmeet' : ∀ i, (b i).image ∩ (b (i + 1)).image = {(b i).finish})
    (hopp : ∀ i, (a i).image ∩ (a (i + 2)).image = ∅)
    (hopp' : ∀ i, (b i).image ∩ (b (i + 2)).image = ∅) :
    ∃ (phi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ (a i).image)
      (psi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ (b i).image)
      (H : closure p.inside ≃ₜ closure q.inside),
      (∀ i, (phi i ⟨-1, by norm_num⟩ : ℂ) = (a i).start) ∧
      (∀ i, (phi i ⟨1, by norm_num⟩ : ℂ) = (a i).finish) ∧
      (∀ i, (psi i ⟨-1, by norm_num⟩ : ℂ) = (b i).start) ∧
      (∀ i, (psi i ⟨1, by norm_num⟩ : ℂ) = (b i).finish) ∧
      (∀ i u,
        (H ⟨phi i u, p.image_subset_closure_inside_cyclic hp
          (hP ▸ mem_iUnion.mpr ⟨i, (phi i u).property⟩)⟩ : ℂ) = (psi i u : ℂ)) ∧
      ∀ x : closure p.inside, (H x : ℂ) ∈ q.image ↔ (x : ℂ) ∈ p.image := by
  obtain ⟨phi, psi, f, hphi₀, hphi₁, hpsi₀, hpsi₁, hf⟩ :=
    Polyline.exists_four_arc_boundary_map hP1 a b p.image q.image
      ha hb hane hbne hP hQ hjoin hjoin' hmeet hmeet' hopp hopp'
  obtain ⟨H, hH⟩ := p.exists_inside_homeomorph_extending_boundary q hp hq f
  refine ⟨phi, psi, H, hphi₀, hphi₁, hpsi₀, hpsi₁, ?_,
    p.inside_extension_mem_image_iff q hp hq H f hH⟩
  intro i u
  exact (hH ⟨phi i u, hP ▸ mem_iUnion.mpr ⟨i, (phi i u).property⟩⟩).trans (hf i u)




















































end DirectedDistances.PlanarMap
