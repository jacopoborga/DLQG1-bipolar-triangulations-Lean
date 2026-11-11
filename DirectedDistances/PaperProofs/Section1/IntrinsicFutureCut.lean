/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricClassSpace
public import DirectedDistances.PlanarMap.D39DrawingRepresentation3

/- # Intrinsic geometric data for Definition 1.3

reading recorded in the installed Definition 1.3 anchor. Every carrier below
belongs to the given drawing. The side test uses complementary components and
the winding definition of left along the directed root. No code, source
realization, or chosen map isomorphism occurs in this interface.

This file defines the interface only. Existence, uniqueness and source
satisfaction are separate proof obligations; no object is selected by choice. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section1

open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open unitInterval

/-- Helper toward Definition 1.3: a geometric dart follows the stored arc
when its bit is true and the reversed arc otherwise, including missing edges. -/
@[expose] def intrinsicFutureDartArc (A : D39DomainRootedMap.{0}) (d : A.E × Bool) :
    Path (A.map.pos (d39GeomRootVertex A.map d))
      (A.map.pos (d39GeomRootOtherVertex A.map d)) :=
  match d with
  | (e, false) => (A.map.arc e).symm
  | (e, true) => A.map.arc e

/-- Helper toward Definition 1.3: the ambient tail predicate respects the
stored direction bit and gives neither dart of a missing edge an orientation. -/
@[expose] def intrinsicFutureAmbientTail (A : D39DomainRootedMap.{0})
    (d : A.E × Bool) : Prop :=
  ∃ he : ¬ A.map.missing d.1, A.map.forward ⟨d.1, he⟩ = d.2

/-- Helper toward Definition 1.3: inverse counterclockwise rotation on a
geometric edge restriction, computed from the drawing's topological star.
Both incidences of loops and all parallel edge identities are retained. -/
@[expose] def intrinsicFutureRotation (A : D39DomainRootedMap.{0})
    (edges : Set A.E) (d a : A.E × Bool) : Prop :=
  d.1 ∈ edges ∧ a.1 ∈ edges ∧
    d39GeomRootVertex A.map a = d39GeomRootVertex A.map d ∧
    D39TopologicalCcwSuccessor
      {q : A.E × Bool | q.1 ∈ edges ∧
        d39GeomRootVertex A.map q = d39GeomRootVertex A.map d}
      (fun q t => intrinsicFutureDartArc A q t) a d

/-- Helper toward Definition 1.3: the rightmost outgoing edge is the
outgoing incidence whose inverse-rotation predecessor among present
incidences is incoming. This is the geometric version of the anchor's
missing-dart-skipping convention. -/
@[expose] def intrinsicFutureRightmostOutgoingAt (A : D39DomainRootedMap.{0})
    (v : A.V) (e : A.E) : Prop :=
  ∃ b : Bool, intrinsicFutureAmbientTail A (e, b) ∧
    d39GeomRootVertex A.map (e, b) = v ∧
    ∃ a : A.E × Bool,
      intrinsicFutureRotation A {f | ¬ A.map.missing f} (e, b) a ∧
      intrinsicFutureAmbientTail A (a.1, !a.2)

/-- Helper toward Definition 1.3: the leftmost incoming edge has an
outgoing inverse-rotation predecessor, using the D18 incoming-chain reading. -/
@[expose] def intrinsicFutureLeftmostIncomingAt (A : D39DomainRootedMap.{0})
    (v : A.V) (e : A.E) : Prop :=
  ∃ b : Bool, intrinsicFutureAmbientTail A (e, !b) ∧
    d39GeomRootVertex A.map (e, b) = v ∧
    ∃ a : A.E × Bool,
      intrinsicFutureRotation A {f | ¬ A.map.missing f} (e, b) a ∧
      intrinsicFutureAmbientTail A a

/-- Helper toward Definition 1.3: the complete interface trace retains
the geometric arcs of edges subsequently tagged missing. -/
@[expose] def intrinsicFutureSeamTrace (A : D39DomainRootedMap.{0})
    (seam : A.E → Prop) : Set ℂ :=
  {z | ∃ e, seam e ∧ z ∈ Set.range (A.map.arc e)}

/-- Helper toward Definition 1.3: the open left side consists of the
complementary component touching the directed root on its winding-positive
side. This uses the orientation of the plane, not a coordinate inequality. -/
@[expose] def intrinsicFutureOpenLeft (A : D39DomainRootedMap.{0})
    (seam : A.E → Prop) : Set ℂ :=
  {z | ∃ w : ℂ, w ∉ intrinsicFutureSeamTrace A seam ∧
    z ∈ connectedComponentIn (intrinsicFutureSeamTrace A seam)ᶜ w ∧
    ∀ s, LeftAtOn (connectedComponentIn (intrinsicFutureSeamTrace A seam)ᶜ w)
      (intrinsicFutureDartArc A A.root) s}







structure IntrinsicFutureCut (A : D39DomainRootedMap.{0}) where
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

end DirectedDistances.PaperProofs.Section1
end
