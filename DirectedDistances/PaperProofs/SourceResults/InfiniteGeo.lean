/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.InfiniteGeodesicDefinitionProvider

/- # Isolated proof provider for Definition 4.5 (`def-infinite-geo`)

and the proof forwards to the candidate provider; installation, sealing and counting are
separate gates. No conclusion or source hypothesis is added. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open Quiver Filter DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Definition 4.5 isolated provider (`def-infinite-geo`, -/
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
                (fun i => ((kmswRightmostPath w hfin hL ht hR x).edge i, false)))) := by
  exact DirectedDistances.PaperProofs.Section4.def_4_5_infinite_geo_provider
    longest w hfin hL ht hR G _hG x P

end DirectedDistances.PaperProofs.SourceResults
