 
 
/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.InfiniteGeo

/-!
# Definition 4.5 (`def-infinite-geo`)

These are the formal statements associated with the indicated paper labels.
See CORRESPONDENCE.md and ERRATA-AND-DEVIATIONS.md for current manuscript scope.
-/



















public section
namespace DirectedDistances.Paper.Section4

open Quiver Filter DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap

 
theorem infinite_geo
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
                (fun i => ((kmswRightmostPath w hfin hL ht hR x).edge i, false)))) :=
 
by exact DirectedDistances.PaperProofs.SourceResults.infinite_geo
      longest w hfin hL ht hR G _hG x P
 
 

end DirectedDistances.Paper.Section4
 
