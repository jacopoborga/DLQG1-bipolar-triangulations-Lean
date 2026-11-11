/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyCommonMeeting

/-! # First-meeting meaning of the geodesic-slice offsets

For the argument order `(P (k - 1)), (P k)`, the coordinates are respectively
`theta_k^-` and `theta_k`. Reversing the paths reverses these source names. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open Quiver DirectedDistances.KMSW

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hp : BoundaryHitWitnesses (kmswPastCode W)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}




theorem m0Cut_initial_vertex_eq_of_edge_tails_coalesce {k l : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (Q : M0CutInfiniteGeodesic W H h hLL l longest)
    {a b : ℕ} (hco : M0CutEdgeTailsCoalesce P Q a b) :
    (P.codePath.initial a).1 = (Q.codePath.initial b).1 := by
  have he := wholePlaneEdgeι_injective W 0 (hco 0)
  simp only [Nat.add_zero] at he
  have hid : (P.codePath.initial a).1.id = (Q.codePath.initial b).1.id :=
    (P.codePath.edge_outgoing_at_initial (shiftedStream W 0) a).2.symm.trans
      ((congrArg (edgeWest (shiftedStream W 0)) he).trans
        (Q.codePath.edge_outgoing_at_initial (shiftedStream W 0) b).2)
  exact congrArg PresentVertex.mk hid





theorem m0Cut_least_edge_coalescence_initial_vertex_eq {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) {a b : ℕ}
    (hleast : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    ((P (k - 1)).codePath.initial a).1 = ((P k).codePath.initial b).1 :=
  m0Cut_initial_vertex_eq_of_edge_tails_coalesce (P (k - 1)) (P k) hleast.1





theorem m0Cut_least_edge_coalescence_le_meeting {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hcoal : ∀ k l, ∃ a b, M0CutEdgeTailsCoalesce (P k) (P l) a b)
    (k : ℤ) {a b : ℕ}
    (hleast : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (i j : ℕ)
    (hmeet : wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial i).1.id =
      wholePlaneVertexι W 0 ((P k).codePath.initial j).1.id) :
    a ≤ i ∧ b ≤ j :=
  hleast.2 i j (m0Cut_edge_tails_coalesce_of_meeting P T hleft hcoal
    (k - 1) k i j hmeet)





theorem m0Cut_least_edge_coalescence_iff_first_meeting {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (hcoal : ∀ k l, ∃ a b, M0CutEdgeTailsCoalesce (P k) (P l) a b)
    (k : ℤ) (a b : ℕ) :
    M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b ↔
      wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial a).1.id =
        wholePlaneVertexι W 0 ((P k).codePath.initial b).1.id ∧
      ∀ i j : ℕ,
        wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial i).1.id =
          wholePlaneVertexι W 0 ((P k).codePath.initial j).1.id →
        a ≤ i ∧ b ≤ j := by
  constructor
  · intro hleast
    refine ⟨congrArg (fun v : PresentVertex (shiftedStream W 0) =>
      wholePlaneVertexι W 0 v.id)
        (m0Cut_least_edge_coalescence_initial_vertex_eq P k hleast), ?_⟩
    exact m0Cut_least_edge_coalescence_le_meeting P T hleft hcoal k hleast
  · rintro ⟨hmeet, hfirst⟩
    refine ⟨m0Cut_edge_tails_coalesce_of_meeting P T hleft hcoal
      (k - 1) k a b hmeet, ?_⟩
    intro i j hij
    apply hfirst i j
    exact congrArg (fun v : PresentVertex (shiftedStream W 0) =>
      wholePlaneVertexι W 0 v.id)
        (m0Cut_initial_vertex_eq_of_edge_tails_coalesce (P (k - 1)) (P k) hij)

end DirectedDistances.PaperProofs.Section5
