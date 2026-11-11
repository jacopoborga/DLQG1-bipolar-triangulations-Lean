/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Instances.Complex
public import Mathlib.Topology.Path
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Data.ENat.Lattice
public import DirectedDistances.PlanarMap.FiniteAcyclicPoles










public section

noncomputable section

namespace DirectedDistances.PlanarMap

open Set
open unitInterval
open scoped Topology

variable {V E : Type*}

/-- The open parameter interval used for the interior of every drawn edge. -/
@[expose] def openParams : Set I := {t : I | 0 < (t : ℝ) ∧ (t : ℝ) < 1}







structure PlaneGraphDrawing (V E : Type*) where
  src : E → V
  tgt : E → V
  pos : V → ℂ
  pos_injective : Function.Injective pos
  arc : (e : E) → Path (pos (src e)) (pos (tgt e))
  arc_injOn : ∀ e, Set.InjOn (arc e) openParams
  openArc_disjoint : ∀ e e', e ≠ e' →
    Disjoint
      ((arc e) '' openParams)
      ((arc e') '' openParams)
  openArc_avoids : ∀ e v,
    pos v ∉ (arc e) '' openParams

namespace PlaneGraphDrawing

variable (D : PlaneGraphDrawing V E)

/-- The image of the open parameter interval of an edge. -/
@[expose] def openArc (e : E) : Set ℂ := D.arc e '' openParams

/-- The union of the vertex positions and all edge images. -/
@[expose] def image : Set ℂ := Set.range D.pos ∪ ⋃ e, Set.range (D.arc e)

/-- A face is a connected component of the complement of the drawing image. -/
@[expose] abbrev Face :=
  {F : Set ℂ // ∃ z, z ∉ D.image ∧ F = connectedComponentIn D.imageᶜ z}

/-- A face is external when it is unbounded. -/
@[expose] def IsExternal (F : D.Face) : Prop := ¬ Bornology.IsBounded F.val

/-- Unfolding the external-face predicate. -/
theorem isExternal_iff (F : D.Face) :
    D.IsExternal F ↔ ¬ Bornology.IsBounded F.val := Iff.rfl

/-- A drawing whose image is closed. This optional predicate is useful when a
statement needs its complementary faces to be open; the general drawing
structure allows accumulation and does not require closed image. -/
@[expose] def IsClosedDrawing : Prop := IsClosed D.image

/-- Under a closed drawing, every face is open in the plane. -/
theorem face_isOpen (hD : D.IsClosedDrawing) (F : D.Face) : IsOpen F.val := by
  obtain ⟨z, hz, hF⟩ := F.property
  rw [hF]
  change IsClosed D.image at hD
  exact hD.isOpen_compl.connectedComponentIn

/-- Every face lies in the complement of the drawing image. -/
theorem face_subset_compl_image (F : D.Face) : F.val ⊆ D.imageᶜ := by
  obtain ⟨z, hz, hF⟩ := F.property
  rw [hF]
  exact connectedComponentIn_subset D.imageᶜ z

/-- For a closed drawing, an edge arc is contained in a face closure exactly
when it is contained in that face's frontier. -/
theorem range_subset_closure_iff_frontier (hD : D.IsClosedDrawing) (F : D.Face)
    (e : E) :
    Set.range (D.arc e) ⊆ closure F.val ↔ Set.range (D.arc e) ⊆ frontier F.val := by
  have hface := D.face_subset_compl_image F
  have hfaceOpen := D.face_isOpen hD F
  have hfaceComplClosed := hfaceOpen.isClosed_compl
  constructor
  · intro h x hx
    rw [frontier_eq_closure_inter_closure]
    refine ⟨h hx, ?_⟩
    have hxedges : x ∈ ⋃ f : E, Set.range (D.arc f) :=
      by exact Set.mem_iUnion.2 ⟨e, hx⟩
    have hximage : x ∈ D.image := by
      change x ∈ Set.range D.pos ∪ (⋃ f : E, Set.range (D.arc f))
      exact Set.mem_union_right _ hxedges
    have hxnotface : x ∉ F.val := by
      intro hxF
      exact hface hxF hximage
    rw [hfaceComplClosed.closure_eq]
    exact hxnotface
  · intro h
    exact h.trans frontier_subset_closure

/-- A face is internal when it is not external. -/
@[expose] def IsInternal (F : D.Face) : Prop := ¬ D.IsExternal F

/-- The side-free edge multiplicity on a face: two when every open-arc point
has the indicated neighborhood, one when the open arc lies in the face closure,
and zero otherwise. All drawn edges, including missing edges, are counted. -/
@[expose] noncomputable def faceMult (e : E) (F : D.Face) : ℕ∞ := by
  classical
  exact if (∀ x ∈ D.openArc e, F.val ∪ Set.range (D.arc e) ∈ 𝓝 x) then 2
    else if D.openArc e ⊆ closure F.val then 1 else 0

/-- The face degree, as the `ENat` sum of edge multiplicities. Missing edges
remain geometric edges and are included in this sum. -/
@[expose] def faceDegree (F : D.Face) : ℕ∞ :=
  ⨆ s : Finset E, ∑ e ∈ s, D.faceMult e F

/-- The definition of an internal face is exactly non-externality. -/
theorem isInternal_iff_not_isExternal (F : D.Face) :
    D.IsInternal F ↔ ¬ D.IsExternal F := Iff.rfl

/-- Every edge has face multiplicity at most two. -/
theorem faceMult_le_two (e : E) (F : D.Face) : D.faceMult e F ≤ 2 := by
  classical
  unfold faceMult
  split_ifs <;> norm_num

end PlaneGraphDrawing

/-- A drawing equipped with an orientation of each edge. `forward e = true`
uses the stored `src` to `tgt` direction; `false` reverses it. -/
structure DirectedPlaneMap (V E : Type*) extends toPlaneGraphDrawing :
    PlaneGraphDrawing V E where
  forward : E → Bool

namespace DirectedPlaneMap

variable (M : DirectedPlaneMap V E)

/-- The initial endpoint in the chosen orientation. -/
@[expose] def tail (e : E) : V := if M.forward e then M.src e else M.tgt e

/-- The terminal endpoint in the chosen orientation. -/
@[expose] def head (e : E) : V := if M.forward e then M.tgt e else M.src e

/-- A directed step in the oriented drawing. -/
@[expose] def step (u w : V) : Prop := ∃ e, M.tail e = u ∧ M.head e = w

/-- Unfolding the directed-step relation. -/
theorem step_iff (u w : V) : M.step u w ↔ ∃ e, M.tail e = u ∧ M.head e = w := Iff.rfl

/-- The orientation has no directed cycle. -/
@[expose] def IsAcyclic : Prop := ∀ v, ¬ Relation.TransGen M.step v v

/-- Unfolding acyclicity of the orientation. -/
theorem isAcyclic_iff : M.IsAcyclic ↔ ∀ v, ¬ Relation.TransGen M.step v v := Iff.rfl

/-- A source has no incoming edge. -/
@[expose] def IsSource (v : V) : Prop := ∀ e, M.head e ≠ v

/-- Unfolding the source predicate. -/
theorem isSource_iff (v : V) : M.IsSource v ↔ ∀ e, M.head e ≠ v := Iff.rfl

/-- A sink has no outgoing edge. -/
@[expose] def IsSink (v : V) : Prop := ∀ e, M.tail e ≠ v

/-- Unfolding the sink predicate. -/
theorem isSink_iff (v : V) : M.IsSink v ↔ ∀ e, M.tail e ≠ v := Iff.rfl

/-- The orientation is bipolar: it is acyclic with at most one source and sink. -/
@[expose] def IsBipolar : Prop :=
  M.IsAcyclic ∧ Subsingleton {v : V // M.IsSource v} ∧
    Subsingleton {v : V // M.IsSink v}

/-- Every internal face of a bipolar orientation has degree three. -/
@[expose] def IsBipolarTriangulation : Prop :=
  M.IsBipolar ∧ ∀ F : M.toPlaneGraphDrawing.Face,
    M.toPlaneGraphDrawing.IsInternal F → M.toPlaneGraphDrawing.faceDegree F = 3

/-- Unfolding the bipolar-triangulation predicate. -/
theorem isBipolarTriangulation_iff : M.IsBipolarTriangulation ↔
    M.IsBipolar ∧ ∀ F : M.toPlaneGraphDrawing.Face,
      M.toPlaneGraphDrawing.IsInternal F → M.toPlaneGraphDrawing.faceDegree F = 3 := Iff.rfl

/-- Unpacking the definition of a bipolar orientation. -/
theorem isBipolar_iff : M.IsBipolar ↔
    M.IsAcyclic ∧ Subsingleton {v : V // M.IsSource v} ∧
      Subsingleton {v : V // M.IsSink v} := Iff.rfl

end DirectedPlaneMap

/-- A geometric drawing with a distinguished predicate of missing edges.
Missing edges remain in the drawing and in its faces. -/
structure PlaneMapWithMissing (V E : Type*) extends toPlaneGraphDrawing :
    PlaneGraphDrawing V E where
  /-- Missing edges remain geometric edges, affect faces, and count in face
  multiplicities and degrees. -/
  missing : E → Prop
  missing_on_external : ∀ e, missing e →
    ∃ F : toPlaneGraphDrawing.Face,
      PlaneGraphDrawing.IsExternal toPlaneGraphDrawing F ∧
        Set.range (arc e) ⊆ closure F.1

/-- A drawing with missing edges, oriented only on present edges. Missing edges
remain geometric edges and count in face multiplicities and degrees. -/
structure DirectedPlaneMapWithMissing (V E : Type*)
    extends toPlaneMapWithMissing : PlaneMapWithMissing V E where
  forward : {e : E // ¬ toPlaneMapWithMissing.missing e} → Bool

namespace DirectedPlaneMapWithMissing

variable (M : DirectedPlaneMapWithMissing V E)

/-- Initial endpoint in the orientation of a present edge. -/
@[expose] def tail (e : {e : E // ¬ M.toPlaneMapWithMissing.missing e}) : V :=
  if M.forward e then M.toPlaneMapWithMissing.src e.val else M.toPlaneMapWithMissing.tgt e.val

/-- Terminal endpoint in the orientation of a present edge. -/
@[expose] def head (e : {e : E // ¬ M.toPlaneMapWithMissing.missing e}) : V :=
  if M.forward e then M.toPlaneMapWithMissing.tgt e.val else M.toPlaneMapWithMissing.src e.val

/-- A directed step using a present edge only. -/
@[expose] def step (u w : V) : Prop :=
  ∃ e : {e : E // ¬ M.toPlaneMapWithMissing.missing e}, M.tail e = u ∧ M.head e = w

/-- Unfolding the directed-step relation on present edges. -/
theorem step_iff (u w : V) : M.step u w ↔
    ∃ e : {e : E // ¬ M.toPlaneMapWithMissing.missing e}, M.tail e = u ∧ M.head e = w := Iff.rfl

/-- The orientation of the present edges is acyclic. -/
@[expose] def IsAcyclic : Prop := ∀ v, ¬ Relation.TransGen M.step v v

/-- Unfolding acyclicity on the present edges. -/
theorem isAcyclic_iff : M.IsAcyclic ↔ ∀ v, ¬ Relation.TransGen M.step v v := Iff.rfl

end DirectedPlaneMapWithMissing



theorem exists_source_and_sink_of_finite_acyclic
    [Finite V] [Nonempty V] (M : DirectedPlaneMap V E) (hM : M.IsAcyclic) :
    (∃ v, M.IsSource v) ∧ (∃ v, M.IsSink v) := by
  have h := DirectedDistances.PlanarMap.exists_source_and_sink
    (R := M.step) hM
  rcases h with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  constructor
  · refine ⟨s, ?_⟩
    intro e hev
    exact hs ⟨M.tail e, ⟨e, rfl, hev⟩⟩
  · refine ⟨t, ?_⟩
    intro e het
    exact ht ⟨M.head e, ⟨e, het, rfl⟩⟩

end DirectedDistances.PlanarMap

end

