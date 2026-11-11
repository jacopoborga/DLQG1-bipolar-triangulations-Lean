module

public import DirectedDistances.PaperProofs.Section5.InftyCutIdentified
public import DirectedDistances.KMSW.LeftmostGeodesicCutSuffix







public section
namespace DirectedDistances.PaperProofs.Section5

open Quiver DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk

/-- A Definition 4.5 segment-geodesic path represented on the identified cut.

The code path supplies the exact finite LDP or SDP segment condition characterized by
DirectedDistances.Paper.Section4.infinite_geo; cutStep states that each successive
pair of its vertices is a directed step of m0CutData. This does not assert the separate
planar leftmost-containment clause of Definition 4.5. -/
structure M0CutInfiniteGeodesic (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (k : ℤ) (longest : Bool) where
  /-- The underlying code path starts at the paper's boundary vertex x_k. -/
  codePath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k)
  /-- Every nonempty finite segment is extremal, as in Definition 4.5. -/
  segments : if longest then codePath.HasLongestSegments
    else codePath.HasShortestSegments
  /-- The boundary label in M0CutData agrees with the path's first cut vertex. -/
  startsAtCutBoundary : (m0CutData W H h hLL).x k =
    wholePlaneVertexι W 0 ((codePath.initial 0).1.id)
  /-- Every consecutive pair of represented vertices is a cut directed step. -/
  cutStep : ∀ n, m0CutDirectedStep W H (m0CutData W H h hLL).seam
    (wholePlaneVertexι W 0 ((codePath.initial n).1.id))
    (wholePlaneVertexι W 0 ((codePath.initial (n + 1)).1.id))

namespace M0CutInfiniteGeodesic

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
  {k : ℤ} {longest : Bool}

/-- The represented edge stream retains the original geometric edge identities. -/
def cutEdge (P : M0CutInfiniteGeodesic W H h hLL k longest) (n : ℕ) :
    WholePlaneEdge W :=
  wholePlaneEdgeι W 0 (P.codePath.edge n)

/-- Any code-level tail equality transports to equality of the cut's geometric
edge tails. Parallel edges remain distinguished by wholePlaneEdgeι. -/
theorem tails_coalesce_of_code_tails
    (P Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (hPQ : ∃ i j, (P.codePath.shift i).edge = (Q.codePath.shift j).edge) :
    ∃ i j, ∀ n, P.cutEdge (i + n) = Q.cutEdge (j + n) := by
  obtain ⟨i, j, hij⟩ := hPQ
  refine ⟨i, j, fun n => ?_⟩
  change wholePlaneEdgeι W 0 (P.codePath.edge (i + n)) =
    wholePlaneEdgeι W 0 (Q.codePath.edge (j + n))
  exact congrArg (wholePlaneEdgeι W 0) (congrFun hij n)

end M0CutInfiniteGeodesic

/-- Turn a source-present infinite geodesic into a path of identified cut
directed steps, preserving its LDP/SDP segment condition. This is a deterministic
transport helper toward Lemma 5.4, not its almost-sure existence claim. -/
noncomputable def m0CutInfiniteGeodesicOfPresentPath
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (k : ℤ) (longest : Bool)
    (P : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hP : if longest then P.HasLongestSegments else P.HasShortestSegments) :
    M0CutInfiniteGeodesic W H h hLL k longest := by
  have hstart : (P.initial 0).1.id = boundaryVertex (shiftedStream W 0) h k := by
    have hz := (P.initial 0).2.eq_of_length_zero (P.prefix_length 0)
    exact congrArg PresentVertex.id hz.symm
  refine ⟨P, hP, ?_, ?_⟩
  · exact (m0CutData W H h hLL).x_eq h hLL k |>.trans
      (congrArg (wholePlaneVertexι W 0) hstart.symm)
  · intro n
    apply (m0Cut_identification_directedStep W H h hLL
      ((P.initial n).1.id)
      ((P.initial (n + 1)).1.id)).2
    obtain ⟨he, hw⟩ := P.edge_outgoing_at_initial (shiftedStream W 0) n
    obtain ⟨_, ht⟩ := P.edge_incoming_at_succ (shiftedStream W 0) n
    exact ⟨P.edge n, he, congrArg (wholePlaneVertexι W 0) hw,
      congrArg (wholePlaneVertexι W 0) ht⟩

end DirectedDistances.PaperProofs.Section5
