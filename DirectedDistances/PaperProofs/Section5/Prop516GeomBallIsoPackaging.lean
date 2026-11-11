/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.D39GeometricSourceProviderV2
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Sides

/-! # Geometric ball isomorphism packaging

Helpers toward Proposition 5.16 (`prop-disk-bs-conv`,
coordinator. These helpers do not establish Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16: an endpoint-fixing reparametrization
between injective paths of the same range is strictly increasing. -/
theorem exists_strictMono_path_reparam_of_injective_range_eq {x y : ℂ}
    (γ δ : Path x y) (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hrange : Set.range δ = Set.range γ) :
    ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧ StrictMono φ ∧
      ∀ t, δ t = γ (φ t) := by
  obtain ⟨φ, h0, h1, heq⟩ :=
    exists_path_reparam_of_injective_range_eq γ δ hγ hδ hrange
  refine ⟨φ, h0, h1, ?_, ?_⟩
  · exact φ.continuous.strictMono_of_inj_boundedOrder
      (by change φ 0 ≤ φ 1; rw [h0, h1]; exact zero_le_one) φ.injective
  · intro t
    exact congrArg (fun p : Path x y => p t) heq

/-- Helper toward Proposition 5.16: reversing the endpoint order gives a
strictly decreasing reparametrization of injective paths of the same range. -/
theorem exists_strictAnti_path_reparam_of_injective_range_eq {x y : ℂ}
    (γ : Path x y) (δ : Path y x)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hrange : Set.range δ = Set.range γ) :
    ∃ φ : I ≃ₜ I, φ 0 = 1 ∧ φ 1 = 0 ∧ StrictAnti φ ∧
      ∀ t, δ t = γ (φ t) := by
  have hγs : Function.Injective γ.symm :=
    hγ.comp unitInterval.symm_bijective.injective
  have hrs : Set.range δ = Set.range γ.symm := by
    rw [Path.symm_range]
    exact hrange
  obtain ⟨φ, h0, h1, hm, heq⟩ :=
    exists_strictMono_path_reparam_of_injective_range_eq γ.symm δ hγs hδ hrs
  refine ⟨φ.trans unitInterval.symmHomeomorph, ?_, ?_, ?_, ?_⟩
  · change σ (φ 0) = 1
    rw [h0, unitInterval.symm_zero]
  · change σ (φ 1) = 0
    rw [h1, unitInterval.symm_one]
  · exact unitInterval.strictAnti_symm.comp_strictMono hm
  · exact heq

/-- Helper toward Proposition 5.16: a geometric edge with distinct stored
endpoints has an injective path on the entire closed parameter interval.
The general drawing carrier also permits loops, which are excluded here
explicitly rather than inferred from open-arc injectivity. -/
theorem planeGraphDrawing_arc_injective_of_src_ne_tgt
    {V E : Type*} (D : PlaneGraphDrawing V E) (e : E)
    (hne : D.src e ≠ D.tgt e) : Function.Injective (D.arc e) := by
  intro s t hst
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc s.property with hs | hs | hs
  · have hs0 : s = 0 := Subtype.ext hs
    subst s
    rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with ht | ht | ht
    · exact (Subtype.ext ht).symm
    · have ht1 : t = 1 := Subtype.ext ht
      subst t
      exact (hne (D.pos_injective ((D.arc e).source.symm.trans
        (hst.trans (D.arc e).target)))).elim
    · exact (D.openArc_avoids e (D.src e)
        ⟨t, ht, hst.symm.trans (D.arc e).source⟩).elim
  · have hs1 : s = 1 := Subtype.ext hs
    subst s
    rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with ht | ht | ht
    · have ht0 : t = 0 := Subtype.ext ht
      subst t
      exact (hne (D.pos_injective ((D.arc e).source.symm.trans
        (hst.symm.trans (D.arc e).target)))).elim
    · exact (Subtype.ext ht).symm
    · exact (D.openArc_avoids e (D.tgt e)
        ⟨t, ht, hst.symm.trans (D.arc e).target⟩).elim
  · exact ((D.arc_eq_at_interior_iff e s t hs).mp hst.symm).symm

/-- Helper toward Proposition 5.16: a self-loop in the general drawing
carrier does not have an injective closed-interval path. -/
theorem planeGraphDrawing_arc_not_injective_of_src_eq_tgt
    {V E : Type*} (D : PlaneGraphDrawing V E) (e : E)
    (heq : D.src e = D.tgt e) : ¬ Function.Injective (D.arc e) := by
  intro hi
  apply zero_ne_one (α := I)
  apply hi
  rw [(D.arc e).source, (D.arc e).target, heq]

/-- Helper toward Proposition 5.16: reversing a geometric arc cannot be
realized by a strictly increasing interval homeomorphism. For self-loops,
the reversed path nevertheless has the same endpoints and range. -/
theorem planeGraphDrawing_not_strictMono_arc_reverse_reparam
    {V E : Type*} (D : PlaneGraphDrawing V E) (e : E)
    (s t : openParams) (hst : s < t) :
    ¬ ∃ φ : I ≃ₜ I, StrictMono φ ∧
      ∀ u, D.arc e (σ u) = D.arc e (φ u) := by
  rintro ⟨φ, hm, heq⟩
  have hs : φ s.val = σ s.val :=
    (D.arc_eq_at_interior_iff e (σ s.val) (φ s.val)
      (symm_mem_openParams_iff.mpr s.property)).mp (heq s.val).symm
  have ht : φ t.val = σ t.val :=
    (D.arc_eq_at_interior_iff e (σ t.val) (φ t.val)
      (symm_mem_openParams_iff.mpr t.property)).mp (heq t.val).symm
  have hlt := hm (show s.val < t.val from hst)
  rw [hs, ht] at hlt
  exact (not_lt_of_ge (unitInterval.strictAnti_symm hst).le) hlt

/-- Helper toward Proposition 5.16: a plane homeomorphism carrying the
ranges and the ordered endpoints of two injective paths gives precisely the
monotone or antitone reparametrization specified by the endpoint-order bit. -/
theorem exists_path_reparam_of_planeHomeomorph
    {x y x' y' : ℂ} (γ : Path x y) (δ : Path x' y')
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (H : ℂ ≃ₜ ℂ) (b : Bool)
    (h0 : H x = if b then y' else x')
    (h1 : H y = if b then x' else y')
    (hrange : H '' Set.range γ = Set.range δ) :
    ∃ φ : I ≃ₜ I,
      (b = false → StrictMono φ) ∧ (b = true → StrictAnti φ) ∧
      ∀ t, H (γ t) = δ (φ t) := by
  cases b
  · let η : Path x' y' := (γ.map H.continuous).cast h0.symm h1.symm
    have hη : Function.Injective η := H.injective.comp hγ
    have hr : Set.range η = Set.range δ := by
      change Set.range (H ∘ γ) = Set.range δ
      rw [Set.range_comp]
      exact hrange
    obtain ⟨φ, _, _, hm, heq⟩ :=
      exists_strictMono_path_reparam_of_injective_range_eq δ η hδ hη hr
    refine ⟨φ, fun _ => hm, ?_, heq⟩
    intro h
    cases h
  · let η : Path y' x' := (γ.map H.continuous).cast h0.symm h1.symm
    have hη : Function.Injective η := H.injective.comp hγ
    have hr : Set.range η = Set.range δ := by
      change Set.range (H ∘ γ) = Set.range δ
      rw [Set.range_comp]
      exact hrange
    obtain ⟨φ, _, _, ha, heq⟩ :=
      exists_strictAnti_path_reparam_of_injective_range_eq δ η hδ hη hr
    refine ⟨φ, ?_, fun _ => ha, heq⟩
    intro h
    cases h

/-- Helper toward Proposition 5.16: the discrete correspondence underlying
a geometric ball isomorphism, before supplying a plane homeomorphism or
edge reparametrizations. Missing edges remain geometric edge identities.
This structure imposes no injectivity or looplessness beyond the carriers. -/
structure D39GeomBallCorrespondenceV2 (r : ℕ) (B C : D39DomainRootedMapV2) where
  /-- Helper toward Proposition 5.16: the radius is positive. -/
  radius_pos : 0 < r
  /-- Helper toward Proposition 5.16: ball vertex identities correspond. -/
  vertexEquiv : {v // v ∈ d39GeomBallVertices B.map B.root r} ≃
    {v // v ∈ d39GeomBallVertices C.map C.root r}
  /-- Helper toward Proposition 5.16: all ball edge identities correspond. -/
  edgeEquiv : {e // e ∈ d39GeomBallEdges B.map B.root r} ≃
    {e // e ∈ d39GeomBallEdges C.map C.root r}
  /-- Helper toward Proposition 5.16: retained original faces correspond. -/
  faceEquiv : {F // F ∈ d39GeomRetainedFaces B.map B.root r} ≃
    {F // F ∈ d39GeomRetainedFaces C.map C.root r}
  /-- Helper toward Proposition 5.16: stored endpoint orders may differ. -/
  edgeFlip : {e // e ∈ d39GeomBallEdges B.map B.root r} → Bool
  /-- Helper toward Proposition 5.16: the source endpoint respects that bit. -/
  src_map : ∀ e,
    (vertexEquiv ⟨B.map.toPlaneMapWithMissing.src e.1, e.2.1⟩).1 =
      if edgeFlip e then C.map.toPlaneMapWithMissing.tgt (edgeEquiv e).1
      else C.map.toPlaneMapWithMissing.src (edgeEquiv e).1
  /-- Helper toward Proposition 5.16: the target endpoint respects that bit. -/
  tgt_map : ∀ e,
    (vertexEquiv ⟨B.map.toPlaneMapWithMissing.tgt e.1, e.2.2⟩).1 =
      if edgeFlip e then C.map.toPlaneMapWithMissing.src (edgeEquiv e).1
      else C.map.toPlaneMapWithMissing.tgt (edgeEquiv e).1
  /-- Helper toward Proposition 5.16: missing-edge tags are preserved. -/
  missing_map : ∀ e,
    C.map.toPlaneMapWithMissing.missing (edgeEquiv e).1 ↔
      B.map.toPlaneMapWithMissing.missing e.1
  /-- Helper toward Proposition 5.16: present orientations respect the bit. -/
  orientation_map : ∀ e (he : ¬ B.map.toPlaneMapWithMissing.missing e.1),
    C.map.forward ⟨(edgeEquiv e).1, by simpa [missing_map e] using he⟩ =
      Bool.xor (B.map.forward ⟨e.1, he⟩) (edgeFlip e)
  /-- Helper toward Proposition 5.16: the marked geometric edge is preserved. -/
  root_edge_map :
    (edgeEquiv ⟨B.root.1, d39GeomRootEdge_mem B.map B.root radius_pos⟩).1 = C.root.1
  /-- Helper toward Proposition 5.16: the ordered root mark is preserved. -/
  root_bool_map : C.root.2 = Bool.xor B.root.2
    (edgeFlip ⟨B.root.1, d39GeomRootEdge_mem B.map B.root radius_pos⟩)

namespace D39GeomBallCorrespondenceV2

variable {r : ℕ} {B C : D39DomainRootedMapV2}

/-- Helper toward Proposition 5.16: the discrete vertex and edge maps
preserve the distinction between loops and edges with distinct endpoints. -/
theorem src_ne_tgt (c : D39GeomBallCorrespondenceV2 r B C)
    (e : {e // e ∈ d39GeomBallEdges B.map B.root r})
    (hne : B.map.toPlaneMapWithMissing.src e.1 ≠ B.map.toPlaneMapWithMissing.tgt e.1) :
    C.map.toPlaneMapWithMissing.src (c.edgeEquiv e).1 ≠
      C.map.toPlaneMapWithMissing.tgt (c.edgeEquiv e).1 := by
  intro heq
  apply hne
  have hv :
      c.vertexEquiv ⟨B.map.toPlaneMapWithMissing.src e.1, e.2.1⟩ =
        c.vertexEquiv ⟨B.map.toPlaneMapWithMissing.tgt e.1, e.2.2⟩ := by
    apply Subtype.ext
    rw [c.src_map, c.tgt_map]
    cases c.edgeFlip e <;> simp only [Bool.false_eq_true, ite_false, ite_true, heq]
  exact congrArg Subtype.val (c.vertexEquiv.injective hv)

/-- Helper toward Proposition 5.16: vertex position transport and the
discrete endpoint maps give both endpoint equalities for each ball edge. -/
theorem arc_endpoints_map (c : D39GeomBallCorrespondenceV2 r B C)
    (H : ℂ ≃ₜ ℂ)
    (hpos : ∀ v, H (B.map.toPlaneMapWithMissing.pos v.1) =
      C.map.toPlaneMapWithMissing.pos (c.vertexEquiv v).1)
    (e : {e // e ∈ d39GeomBallEdges B.map B.root r}) :
    (H (B.map.toPlaneMapWithMissing.pos (B.map.toPlaneMapWithMissing.src e.1)) =
      if c.edgeFlip e then
        C.map.toPlaneMapWithMissing.pos (C.map.toPlaneMapWithMissing.tgt (c.edgeEquiv e).1)
      else C.map.toPlaneMapWithMissing.pos
        (C.map.toPlaneMapWithMissing.src (c.edgeEquiv e).1)) ∧
    (H (B.map.toPlaneMapWithMissing.pos (B.map.toPlaneMapWithMissing.tgt e.1)) =
      if c.edgeFlip e then
        C.map.toPlaneMapWithMissing.pos (C.map.toPlaneMapWithMissing.src (c.edgeEquiv e).1)
      else C.map.toPlaneMapWithMissing.pos
        (C.map.toPlaneMapWithMissing.tgt (c.edgeEquiv e).1)) := by
  constructor
  · rw [hpos ⟨_, e.2.1⟩, c.src_map]
    cases c.edgeFlip e <;> rfl
  · rw [hpos ⟨_, e.2.2⟩, c.tgt_map]
    cases c.edgeFlip e <;> rfl

/-- Helper toward Proposition 5.16: for an edge with distinct endpoints,
the given plane homeomorphism and range equality construct its complete
reparametrization field with the prescribed endpoint-order bit. -/
theorem exists_edge_reparam_of_src_ne_tgt (c : D39GeomBallCorrespondenceV2 r B C)
    (H : ℂ ≃ₜ ℂ)
    (hpos : ∀ v, H (B.map.toPlaneMapWithMissing.pos v.1) =
      C.map.toPlaneMapWithMissing.pos (c.vertexEquiv v).1)
    (e : {e // e ∈ d39GeomBallEdges B.map B.root r})
    (hne : B.map.toPlaneMapWithMissing.src e.1 ≠ B.map.toPlaneMapWithMissing.tgt e.1)
    (hrange : H '' Set.range (B.map.toPlaneMapWithMissing.arc e.1) =
      Set.range (C.map.toPlaneMapWithMissing.arc (c.edgeEquiv e).1)) :
    ∃ φ : I ≃ₜ I,
      (c.edgeFlip e = false → StrictMono φ) ∧
      (c.edgeFlip e = true → StrictAnti φ) ∧
      ∀ t, H (B.map.toPlaneMapWithMissing.arc e.1 t) =
        C.map.toPlaneMapWithMissing.arc (c.edgeEquiv e).1 (φ t) := by
  obtain ⟨h0, h1⟩ := c.arc_endpoints_map H hpos e
  exact exists_path_reparam_of_planeHomeomorph
    (B.map.toPlaneMapWithMissing.arc e.1)
    (C.map.toPlaneMapWithMissing.arc (c.edgeEquiv e).1)
    (planeGraphDrawing_arc_injective_of_src_ne_tgt _ _ hne)
    (planeGraphDrawing_arc_injective_of_src_ne_tgt _ _ (c.src_ne_tgt e hne))
    H (c.edgeFlip e) h0 h1 hrange

end D39GeomBallCorrespondenceV2

























































end DirectedDistances.PaperProofs.Section5

end
