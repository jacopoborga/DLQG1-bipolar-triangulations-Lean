/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLArcGluing
public import Mathlib.Topology.LocallyFinite




public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set Topology

/-- Helper toward Proposition 5.16: every polygon boundary point belongs
to the closure of the bounded complementary region. -/
theorem Polyline.image_subset_closure_inside_cyclic
    (c : Polyline) (hc : c.IsCyclicSimple) : c.image ⊆ closure c.inside := by
  rw [← (c.frontier_inside_outside_eq_image_cyclic hc).1]
  exact frontier_subset_closure

/-- Helper toward Proposition 5.16: a prescribed homeomorphism between
cyclically simple polygon boundaries extends over their closed inside regions. -/
theorem Polyline.exists_inside_homeomorph_extending_boundary
    (c c' : Polyline) (hc : c.IsCyclicSimple) (hc' : c'.IsCyclicSimple)
    (f : c.image ≃ₜ c'.image) :
    ∃ H : closure c.inside ≃ₜ closure c'.inside,
      ∀ x : c.image,
        (H ⟨x, c.image_subset_closure_inside_cyclic hc x.property⟩ : ℂ) =
          (f x : ℂ) := by
  obtain ⟨h, hb⟩ := c.exists_polygon_disk_chart hc
  obtain ⟨k, kb⟩ := c'.exists_polygon_disk_chart hc'
  exact exists_disk_homeomorph_extending_boundary
    (closure c.inside) c.image (closure c'.inside) c'.image
    (c.image_subset_closure_inside_cyclic hc) (c'.image_subset_closure_inside_cyclic hc')
    h k hb kb f

/-- Helper toward Proposition 5.16: compatible continuous maps on a finite
closed cover paste to a continuous map, retaining their prescribed values. -/
theorem exists_continuous_map_of_finite_closed_cover
    {ι X Y : Type*} [Finite ι] [TopologicalSpace X] [TopologicalSpace Y]
    (s : ι → Set X) (hs : ∀ i, IsClosed (s i)) (hcover : ⋃ i, s i = univ)
    (f : ∀ i, s i → Y) (hf : ∀ i, Continuous (f i))
    (hagree : ∀ i j (x : X) (hi : x ∈ s i) (hj : x ∈ s j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) :
    ∃ F : X → Y, Continuous F ∧ ∀ i (x : s i), F x = f i x := by
  classical
  have hmem (x : X) : ∃ i, x ∈ s i := by
    have hx : x ∈ ⋃ i, s i := hcover.symm ▸ mem_univ x
    exact mem_iUnion.mp hx
  let F : X → Y := fun x => f (hmem x).choose ⟨x, (hmem x).choose_spec⟩
  have hF (i : ι) (x : s i) : F x = f i x :=
    hagree _ i x _ x.property
  refine ⟨F, ?_, hF⟩
  apply (locallyFinite_of_finite s).continuous hcover hs
  intro i
  rw [continuousOn_iff_continuous_domRestrict]
  exact (hf i).congr (fun x => (hF i x).symm)

/-- Helper toward Proposition 5.16: homeomorphisms on finite closed covers
glue when both their forward and inverse maps agree on every overlap.
No compactness of the ambient spaces is required. -/
theorem exists_homeomorph_of_finite_closed_covers
    {ι X Y : Type*} [Finite ι] [TopologicalSpace X] [TopologicalSpace Y]
    (s : ι → Set X) (t : ι → Set Y)
    (hs : ∀ i, IsClosed (s i)) (ht : ∀ i, IsClosed (t i))
    (hcover : ⋃ i, s i = univ) (hcover' : ⋃ i, t i = univ)
    (e : ∀ i, s i ≃ₜ t i)
    (hagree : ∀ i j (x : X) (hi : x ∈ s i) (hj : x ∈ s j),
      (e i ⟨x, hi⟩ : Y) = (e j ⟨x, hj⟩ : Y))
    (hagree' : ∀ i j (y : Y) (hi : y ∈ t i) (hj : y ∈ t j),
      ((e i).symm ⟨y, hi⟩ : X) = ((e j).symm ⟨y, hj⟩ : X)) :
    ∃ H : X ≃ₜ Y, ∀ i (x : s i), H x = (e i x : Y) := by
  obtain ⟨F, hFcont, hF⟩ := exists_continuous_map_of_finite_closed_cover s hs hcover
    (fun i x => (e i x : Y))
    (fun i => continuous_subtype_val.comp (e i).continuous) hagree
  obtain ⟨G, hGcont, hG⟩ := exists_continuous_map_of_finite_closed_cover t ht hcover'
    (fun i y => ((e i).symm y : X))
    (fun i => continuous_subtype_val.comp (e i).symm.continuous) hagree'
  have hleft (x : X) : G (F x) = x := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
    rw [hF i ⟨x, hi⟩, hG i (e i ⟨x, hi⟩), (e i).symm_apply_apply]
  have hright (y : Y) : F (G y) = y := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover'.symm ▸ mem_univ y)
    rw [hG i ⟨y, hi⟩, hF i ((e i).symm ⟨y, hi⟩), (e i).apply_symm_apply]
  exact ⟨{
    toFun := F
    invFun := G
    left_inv := hleft
    right_inv := hright
    continuous_toFun := hFcont
    continuous_invFun := hGcont }, hF⟩

/-- Helper toward Proposition 5.16: exact correspondence of overlaps and
agreement on them suffice to glue homeomorphisms of finite closed covers.
This applies to covers of the plane, including an unbounded face. -/
theorem exists_homeomorph_of_finite_closed_covers_of_overlap
    {ι X Y : Type*} [Finite ι] [TopologicalSpace X] [TopologicalSpace Y]
    (s : ι → Set X) (t : ι → Set Y)
    (hs : ∀ i, IsClosed (s i)) (ht : ∀ i, IsClosed (t i))
    (hcover : ⋃ i, s i = univ) (hcover' : ⋃ i, t i = univ)
    (e : ∀ i, s i ≃ₜ t i)
    (hinter : ∀ i j (x : s i), (e i x : Y) ∈ t j ↔ (x : X) ∈ s j)
    (hagree : ∀ i j (x : X) (hi : x ∈ s i) (hj : x ∈ s j),
      (e i ⟨x, hi⟩ : Y) = (e j ⟨x, hj⟩ : Y)) :
    ∃ H : X ≃ₜ Y, ∀ i (x : s i), H x = (e i x : Y) := by
  apply exists_homeomorph_of_finite_closed_covers s t hs ht hcover hcover' e hagree
  intro i j y hi hj
  let x : s i := (e i).symm ⟨y, hi⟩
  have hxy : (e i x : Y) = y := congrArg Subtype.val ((e i).apply_symm_apply _)
  have hxj : (x : X) ∈ s j := (hinter i j x).mp (hxy.symm ▸ hj)
  have heq : e j ⟨x, hxj⟩ = ⟨y, hj⟩ :=
    Subtype.ext ((hagree i j x x.property hxj).symm.trans hxy)
  have hinv : (e j).symm ⟨y, hj⟩ = ⟨x, hxj⟩ := by
    rw [← heq, (e j).symm_apply_apply]
  exact (congrArg Subtype.val hinv).symm

/-- Helper toward Proposition 5.16: specified homeomorphisms of the shared
boundaries give exact overlap correspondence for finite closed-cover gluing.
The statement also allows overlaps larger than boundaries. -/
theorem exists_homeomorph_of_finite_closed_covers_of_shared_boundaries
    {ι X Y : Type*} [Finite ι] [TopologicalSpace X] [TopologicalSpace Y]
    (s : ι → Set X) (t : ι → Set Y)
    (hs : ∀ i, IsClosed (s i)) (ht : ∀ i, IsClosed (t i))
    (hcover : ⋃ i, s i = univ) (hcover' : ⋃ i, t i = univ)
    (e : ∀ i, s i ≃ₜ t i)
    (b : ∀ i j, ↥(s i ∩ s j) ≃ₜ ↥(t i ∩ t j))
    (hboundary : ∀ i j (x : ↥(s i ∩ s j)),
      (e i ⟨x, x.property.1⟩ : Y) = (b i j x : Y))
    (hagree : ∀ i j (x : X) (hi : x ∈ s i) (hj : x ∈ s j),
      (e i ⟨x, hi⟩ : Y) = (e j ⟨x, hj⟩ : Y)) :
    ∃ H : X ≃ₜ Y, ∀ i (x : s i), H x = (e i x : Y) := by
  apply exists_homeomorph_of_finite_closed_covers_of_overlap
    s t hs ht hcover hcover' e _ hagree
  intro i j x
  constructor
  · intro hx
    let u : ↥(s i ∩ s j) := (b i j).symm ⟨e i x, (e i x).property, hx⟩
    have hu : (e i ⟨u, u.property.1⟩ : Y) = (e i x : Y) :=
      (hboundary i j u).trans
        (congrArg Subtype.val ((b i j).apply_symm_apply _))
    have hux : (u : X) = (x : X) :=
      congrArg Subtype.val ((e i).injective (Subtype.ext hu))
    exact hux ▸ u.property.2
  · intro hx
    have heq := hboundary i j ⟨x, x.property, hx⟩
    exact heq.symm ▸ (b i j ⟨x, x.property, hx⟩).property.2

/-- Helper toward Proposition 5.16: a homeomorphism from a planar subset
to a closed planar subset is proper: points of sufficiently large norm map
outside any prescribed closed ball. -/
theorem homeomorph_closed_sets_norm_proper
    (s t : Set ℂ) (ht : IsClosed t) (H : s ≃ₜ t) :
    ∀ R : ℝ, ∃ S : ℝ, ∀ x : s,
      S < ‖(x : ℂ)‖ → R < ‖(H x : ℂ)‖ := by
  intro R
  have hcompact : IsCompact
      ((fun x : s => (H x : ℂ)) ⁻¹' Metric.closedBall (0 : ℂ) R) :=
    (ht.isClosedEmbedding_subtypeVal.comp H.isClosedEmbedding).isCompact_preimage
      (isCompact_closedBall (0 : ℂ) R)
  obtain ⟨S, hS⟩ := (hcompact.image continuous_subtype_val).isBounded.exists_norm_le
  refine ⟨S, fun x hx => ?_⟩
  by_contra h
  have hxmem : (x : ℂ) ∈ Subtype.val ''
      ((fun x : s => (H x : ℂ)) ⁻¹' Metric.closedBall (0 : ℂ) R) :=
    ⟨x, by simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
      using le_of_not_gt h, rfl⟩
  exact (not_le_of_gt hx) (hS x hxmem)

/-- Helper toward Proposition 5.16: every homeomorphism between the closed
outside regions is proper with respect to the ambient planar norm. This proves
the properness clause separately, without asserting existence of an extension. -/
theorem Polyline.outside_homeomorph_norm_proper
    (c c' : Polyline) (H : closure c.outside ≃ₜ closure c'.outside) :
    ∀ R : ℝ, ∃ S : ℝ, ∀ x : closure c.outside,
      S < ‖(x : ℂ)‖ → R < ‖(H x : ℂ)‖ :=
  homeomorph_closed_sets_norm_proper _ _ isClosed_closure H

/-- Helper toward Proposition 5.16: the closed outside consists exactly of
the outside and the whole polygon boundary. -/
theorem Polyline.closure_outside_eq_union_image_cyclic
    (c : Polyline) (hc : c.IsCyclicSimple) :
    closure c.outside = c.outside ∪ c.image := by
  rw [closure_eq_self_union_frontier, (c.frontier_inside_outside_eq_image_cyclic hc).2]

/-- Helper toward Proposition 5.16: every boundary point also belongs to
the closed outside, including all vertices. -/
theorem Polyline.image_subset_closure_outside_cyclic
    (c : Polyline) (hc : c.IsCyclicSimple) : c.image ⊆ closure c.outside := by
  rw [c.closure_outside_eq_union_image_cyclic hc]
  exact subset_union_right

/-- Helper toward Proposition 5.16: the two closed faces cover the plane
and meet exactly on their common polygon boundary. -/
theorem Polyline.closed_faces_union_inter_cyclic
    (c : Polyline) (hc : c.IsCyclicSimple) :
    (closure c.inside ∪ closure c.outside = univ) ∧
      (closure c.inside ∩ closure c.outside = c.image) := by
  rw [c.closure_inside_eq_union_image hc, c.closure_outside_eq_union_image_cyclic hc]
  constructor
  · ext z
    constructor
    · intro _; exact mem_univ z
    · intro _
      by_cases hz : z ∈ c.image
      · exact Or.inl (Or.inr hz)
      · rcases (c.inside_union_outside.ge hz) with hi | ho
        · exact Or.inl (Or.inl hi)
        · exact Or.inr (Or.inl ho)
  · ext z
    constructor
    · rintro ⟨hi | hi, ho | ho⟩
      · exact False.elim (hi.2 ho.2)
      · exact ho
      · exact hi
      · exact hi
    · intro hz
      exact ⟨Or.inr hz, Or.inr hz⟩


















































end DirectedDistances.PlanarMap
