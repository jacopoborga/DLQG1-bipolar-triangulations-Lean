/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.KMSW.RightmostCoalescenceM0
public import DirectedDistances.KMSW.InfiniteRotation
public import DirectedDistances.KMSW.MonotoneStepAll
public import DirectedDistances.PlanarMap.InfiniteRayStrip
public import DirectedDistances.PlanarMap.VariableRayStrip
public import DirectedDistances.PlanarMap.PlaneRealization

/-! # Definition 4.5 (`def-infinite-geo`): provider for the infinite-geodesic clauses


Clause map:
* The path clause is the binder `P : InfinitePresentPath w ⟨x⟩`. Its edge stream and
  compatible finite prefixes give an infinite directed path from `x`, retaining edge IDs.
* The interval clause expands `HasLongestSegments` or `HasShortestSegments`. The source's
  one-based interval `[a,b]`, with `1 ≤ a ≤ b`, is the stream slice obtained by dropping
  `a - 1` edges from the first `b`; its length is `b + 1 - a`.
* The leftmost clause is the anchor's exact planar-region condition: every competing XDP
  geodesic's full trace is contained in the closed submap between `P` and the rightmost
  directed path from `x`. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open Quiver Filter DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Candidate provider toward Definition 4.5 (`def-infinite-geo`); not yet a counted paper
result. For the infinite path `P` from `x`, the existing segment-optimality predicate expands
exactly to the source's intervals for either XDP choice. The leftmost clause is the planar
submap condition used by the counted GeoExist anchor. -/
theorem def_4_5_infinite_geo_provider
    (longest : Bool)
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (ht : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (G : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w))
    (_hG : G = monotoneFamilyDrawing w hfin (monotone_family_all w))
    (x : ℕ)
    (P : InfinitePresentPath w ⟨x⟩) :
    ((if longest then P.HasLongestSegments else P.HasShortestSegments) ∧
      ∀ P' : InfinitePresentPath w ⟨x⟩,
        (if longest then P'.HasLongestSegments else P'.HasShortestSegments) →
          pathTrace G (fun i => (P'.edge i, false)) ⊆
            closedBetween (pathTrace G (fun i => (P.edge i, false)))
              (pathTrace G
                (fun i => ((kmswRightmostPath w hfin hL ht hR x).edge i, false)))) ↔
    ((∀ a b : ℕ, 1 ≤ a → a ≤ b →
        ∃ z, ∃ q : Path z (P.initial b).1,
          q.length = b + 1 - a ∧
          pathEdgeList q = (List.ofFn (fun i : Fin b => P.edge i.val)).drop (a - 1) ∧
          (if longest then IsLongest q else IsShortest q)) ∧
      ∀ P' : InfinitePresentPath w ⟨x⟩,
        (∀ a b : ℕ, 1 ≤ a → a ≤ b →
          ∃ z, ∃ q : Path z (P'.initial b).1,
            q.length = b + 1 - a ∧
            pathEdgeList q = (List.ofFn (fun i : Fin b => P'.edge i.val)).drop (a - 1) ∧
            (if longest then IsLongest q else IsShortest q)) →
          pathTrace G (fun i => (P'.edge i, false)) ⊆
            closedBetween (pathTrace G (fun i => (P.edge i, false)))
              (pathTrace G
                (fun i => ((kmswRightmostPath w hfin hL ht hR x).edge i, false)))) := by
  cases longest <;> rfl

end DirectedDistances.PaperProofs.Section4
