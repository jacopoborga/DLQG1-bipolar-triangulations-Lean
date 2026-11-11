/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.IntrinsicFutureCut

/-! # Submap rotation for the intrinsic future cut

its cyclic order is the ambient order restricted to the retained geometric
edges, including geometrically retained missing boundary edges. Accordingly,
rotation relates two cut darts; it is not a first entrance from an arbitrary
ambient dart. The geometric rotation predicate in IntrinsicFutureCut already
has this restriction. This successor interface copies its clauses and makes
the restriction explicit for comparison with the code cut's IsRot relation.
No existence or uniqueness is asserted by the interface. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section1
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3

/-- Helper toward Definition 1.3: the intrinsic cut with the cyclic successor
among cut incidences at their common vertex in the ambient drawing. All
carriers and all source clauses of IntrinsicFutureCut are retained. In
particular, rotation is false if either edge is outside the submap. -/
structure IntrinsicFutureCut2 (A : D39DomainRootedMap.{0}) where
  vertices : Set A.V
  edges : Set A.E
  faces : Set A.map.toPlaneGraphDrawing.Face
  seam : A.E → Prop
  missing : A.E → Prop
  tail : A.E × Bool → Prop
  rotation : (A.E × Bool) → (A.E × Bool) → Prop
  x : ℤ → A.V
  betaRVertex : ℕ → A.V
  betaLVertex : ℕ → A.V
  betaREdge : ℕ → A.E
  betaLEdge : ℕ → A.E
  root_initial : x 0 = d39GeomRootVertex A.map A.root
  root_terminal : x 1 = d39GeomRootOtherVertex A.map A.root
  root_tail : intrinsicFutureAmbientTail A A.root
  betaR_start : betaRVertex 0 = x 1
  betaR_extremal : ∀ n, intrinsicFutureRightmostOutgoingAt A (betaRVertex n) (betaREdge n)
  betaR_step : ∀ n, ∃ he : ¬ A.map.missing (betaREdge n),
    A.map.tail ⟨betaREdge n, he⟩ = betaRVertex n ∧
    A.map.head ⟨betaREdge n, he⟩ = betaRVertex (n + 1)
  betaL_start : betaLVertex 0 = x 0
  betaL_extremal : ∀ n, intrinsicFutureLeftmostIncomingAt A (betaLVertex n) (betaLEdge n)
  betaL_step : ∀ n, ∃ he : ¬ A.map.missing (betaLEdge n),
    A.map.head ⟨betaLEdge n, he⟩ = betaLVertex n ∧
    A.map.tail ⟨betaLEdge n, he⟩ = betaLVertex (n + 1)
  seam_iff : ∀ e, seam e ↔
    e = A.root.1 ∨ e ∈ Set.range betaREdge ∨ e ∈ Set.range betaLEdge
  vertices_iff : ∀ v, v ∈ vertices ↔
    A.map.pos v ∈ closure (intrinsicFutureOpenLeft A seam)
  edges_iff : ∀ e, e ∈ edges ↔
    Set.range (A.map.arc e) ⊆ closure (intrinsicFutureOpenLeft A seam)
  faces_iff : ∀ F, F ∈ faces ↔ F.val ⊆ intrinsicFutureOpenLeft A seam
  seam_mem : ∀ e, seam e → e ∈ edges
  ambient_present : ∀ e, e ∈ edges → ¬ A.map.missing e
  missing_iff : ∀ e, missing e ↔ e ∈ Set.range betaLEdge
  present_iff : ∀ e, (e ∈ edges ∧ ¬ missing e) ↔
    (e ∈ edges ∧ ¬ seam e) ∨ e = A.root.1 ∨ e ∈ Set.range betaREdge
  tail_iff : ∀ d, tail d ↔
    d.1 ∈ edges ∧ intrinsicFutureAmbientTail A d ∧ ¬ missing d.1
  missing_unoriented : ∀ e, missing e → ¬ tail (e, false) ∧ ¬ tail (e, true)
  root_not_missing : ¬ missing A.root.1
  cut_root_tail : tail A.root
  rotation_iff : ∀ d a, rotation d a ↔ intrinsicFutureRotation A edges d a
  x_injective : Function.Injective x
  x_range : Set.range x = {v | ∃ e, seam e ∧ (A.map.src e = v ∨ A.map.tgt e = v)}
  x_mem : ∀ k, x k ∈ vertices
  x_right : ∀ n : ℕ, x ((n : ℤ) + 1) = betaRVertex n
  x_left : ∀ n : ℕ, x (-(n : ℤ)) = betaLVertex n
  acyclic : ∀ v, ¬ Relation.TransGen
    (fun u w => ∃ d : A.E × Bool, tail d ∧
      d39GeomRootVertex A.map d = u ∧ d39GeomRootOtherVertex A.map d = w) v v
  internal_triangles : ∀ F, F ∈ faces → A.map.toPlaneGraphDrawing.faceDegree F = 3

/-- Helper toward Definition 1.3: the original geometric interface already
uses restricted submap rotation; copying the data preserves every clause. -/
@[expose] def IntrinsicFutureCut2.toIntrinsicFutureCut {A : D39DomainRootedMap.{0}}
    (C : IntrinsicFutureCut2 A) : IntrinsicFutureCut A where
  vertices := C.vertices
  edges := C.edges
  faces := C.faces
  seam := C.seam
  missing := C.missing
  tail := C.tail
  rotation := C.rotation
  x := C.x
  betaRVertex := C.betaRVertex
  betaLVertex := C.betaLVertex
  betaREdge := C.betaREdge
  betaLEdge := C.betaLEdge
  root_initial := C.root_initial
  root_terminal := C.root_terminal
  root_tail := C.root_tail
  betaR_start := C.betaR_start
  betaR_extremal := C.betaR_extremal
  betaR_step := C.betaR_step
  betaL_start := C.betaL_start
  betaL_extremal := C.betaL_extremal
  betaL_step := C.betaL_step
  seam_iff := C.seam_iff
  vertices_iff := C.vertices_iff
  edges_iff := C.edges_iff
  faces_iff := C.faces_iff
  seam_mem := C.seam_mem
  ambient_present := C.ambient_present
  missing_iff := C.missing_iff
  present_iff := C.present_iff
  tail_iff := C.tail_iff
  missing_unoriented := C.missing_unoriented
  root_not_missing := C.root_not_missing
  cut_root_tail := C.cut_root_tail
  rotation_iff := C.rotation_iff
  x_injective := C.x_injective
  x_range := C.x_range
  x_mem := C.x_mem
  x_right := C.x_right
  x_left := C.x_left
  acyclic := C.acyclic
  internal_triangles := C.internal_triangles

/-- Helper toward Definition 1.3: copy the complete original interface into
the version whose code comparison is explicitly restricted to cut darts. -/
@[expose] def IntrinsicFutureCut.toIntrinsicFutureCut2 {A : D39DomainRootedMap.{0}}
    (C : IntrinsicFutureCut A) : IntrinsicFutureCut2 A where
  vertices := C.vertices
  edges := C.edges
  faces := C.faces
  seam := C.seam
  missing := C.missing
  tail := C.tail
  rotation := C.rotation
  x := C.x
  betaRVertex := C.betaRVertex
  betaLVertex := C.betaLVertex
  betaREdge := C.betaREdge
  betaLEdge := C.betaLEdge
  root_initial := C.root_initial
  root_terminal := C.root_terminal
  root_tail := C.root_tail
  betaR_start := C.betaR_start
  betaR_extremal := C.betaR_extremal
  betaR_step := C.betaR_step
  betaL_start := C.betaL_start
  betaL_extremal := C.betaL_extremal
  betaL_step := C.betaL_step
  seam_iff := C.seam_iff
  vertices_iff := C.vertices_iff
  edges_iff := C.edges_iff
  faces_iff := C.faces_iff
  seam_mem := C.seam_mem
  ambient_present := C.ambient_present
  missing_iff := C.missing_iff
  present_iff := C.present_iff
  tail_iff := C.tail_iff
  missing_unoriented := C.missing_unoriented
  root_not_missing := C.root_not_missing
  cut_root_tail := C.cut_root_tail
  rotation_iff := C.rotation_iff
  x_injective := C.x_injective
  x_range := C.x_range
  x_mem := C.x_mem
  x_right := C.x_right
  x_left := C.x_left
  acyclic := C.acyclic
  internal_triangles := C.internal_triangles

/-- Helper toward Definition 1.3: the two geometric interfaces carry exactly
the same data; the corrected restriction concerns their code identification. -/
@[expose] def intrinsicFutureCut2Equiv (A : D39DomainRootedMap.{0}) :
    IntrinsicFutureCut2 A ≃ IntrinsicFutureCut A where
  toFun := IntrinsicFutureCut2.toIntrinsicFutureCut
  invFun := IntrinsicFutureCut.toIntrinsicFutureCut2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Helper toward Definition 1.3: every rotation pair consists of retained
geometric darts, including the unoriented darts of missing boundary edges. -/
theorem IntrinsicFutureCut2.rotation_mem {A : D39DomainRootedMap.{0}}
    (C : IntrinsicFutureCut2 A) {d a : A.E × Bool} (h : C.rotation d a) :
    d.1 ∈ C.edges ∧ a.1 ∈ C.edges :=
  ⟨((C.rotation_iff d a).mp h).1, ((C.rotation_iff d a).mp h).2.1⟩

end DirectedDistances.PaperProofs.Section1
end

