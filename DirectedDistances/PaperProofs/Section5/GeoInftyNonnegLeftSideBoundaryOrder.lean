/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSide

/-! says: “In particular, the upper boundary of $M_{0,\tau_k-1}$ (Definition
\ref{def-kmsw}) is identified with a segment of the left boundary of
$\wh M_{\tau_k,\infty}'$ starting from the vertex $x_k$, and the right
boundary of $\wh M_{\tau_k,\infty}'$ is identified with the left boundary of
$\wh M_{\tau_k,\infty}^L$.”

The ordered stopped upper-left edges are listed from the attachment vertex by
reversing `UL.dropLast`; `true` records traversal from east to west. The
first-step and chain lemmas below establish this order on the stopped prefix.
Identifying that ordered segment edge-by-edge with the primed left boundary is
the first remaining statement recorded below. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

noncomputable def lPlusPrefixUpperLeftDarts : List (ℕ × Bool) :=
  ((kmswStage (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k)).UL.dropLast.reverse).map
      (fun e => (e, true))

/-- Helper toward Lemma 5.5: the stopped upper-left edge list, read outward
from its attachment vertex, is an ordered chain of reverse-traversed darts. -/
theorem lPlusPrefixUpperLeftDarts_chain :
    List.IsChain
      (fun d e : ℕ × Bool =>
        d.2 = true ∧ e.2 = true ∧
          (kmswStage (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h k)).west d.1 =
          (kmswStage (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h k)).east e.1)
      (lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let s := kmswStage w t
  have hUL : List.IsChain (fun e f => s.east e = s.west f) s.UL :=
    (kmswStageFrontierChain_all w t).UL_chain
  have hrev : List.IsChain (fun e f => s.west e = s.east f)
      (s.UL.dropLast.reverse) := by
    apply List.isChain_reverse.mpr
    exact (hUL.dropLast).imp (fun e f hef => hef.symm)
  change List.IsChain _ ((s.UL.dropLast.reverse).map fun e => (e, true))
  apply List.isChain_map_of_isChain (fun e => (e, true))
  · intro e f hef
    exact ⟨rfl, rfl, hef⟩
  · exact hrev

/-- Helper toward Lemma 5.5: when the ordered stopped upper-left segment is
nonempty, its first reverse-traversed edge starts at $x_k$. -/
theorem lPlusPrefixUpperLeftDarts_first_starts_at_xk
    {e : ℕ} {es : List ℕ}
    (hfirst : (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k)).UL.dropLast.reverse = e :: es) :
    edgeEast (shiftedStream W 0) e = boundaryVertex (shiftedStream W 0) h k := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let s := kmswStage w t
  have heUL : e ∈ s.UL :=
    List.mem_of_mem_dropLast (List.mem_reverse.mp (by rw [hfirst]; simp))
  have halloc : e < s.nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w t).2 e
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl heUL))
  have hinc := (kmswStageFrontierChain_all w t).UL_predecessor_incidence e es hfirst
  have hend := (edge_endpoints_eq w halloc).2
  have hactive := (edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl t))).1
  change edgeEast w e = boundaryVertex w h k
  calc
    edgeEast w e = s.east e := hend.symm
    _ = s.west s.active := hinc
    _ = edgeWest w (act w t) := hactive
    _ = boundaryVertex w h k := (boundaryVertex_eq_edgeWest_hit w h k).symm

/-- Helper toward Lemma 5.5: every edge in the ordered prefix attachment
list is in the source upper-left carrier. -/
theorem lPlusPrefixUpperLeftDarts_mem (d : ℕ × Bool)
    (hd : d ∈ lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k)) :
    d.1 ∈ boundaryGluingUpperLeftEdges W h k := by
  simp only [lPlusPrefixUpperLeftDarts, List.mem_map] at hd
  obtain ⟨e, he, hde⟩ := hd
  rw [← hde]
  simpa [boundaryGluingUpperLeftEdges] using he






























/-- Helper toward Lemma 5.5: unfolding equation. -/
theorem lPlusPrefixUpperLeftDarts_eq :
    lPlusPrefixUpperLeftDarts (W := W) (h := h) (k := k) =
      ((kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k)).UL.dropLast.reverse).map
          (fun e => (e, true)) := by
  rfl

end DirectedDistances.PaperProofs.Section5
