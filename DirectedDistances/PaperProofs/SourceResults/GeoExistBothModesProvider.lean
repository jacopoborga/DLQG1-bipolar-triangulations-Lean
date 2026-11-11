/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.GeoExistBothModes

/-! Supporting lemmas for paper labels `lem-geo-exist` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory Quiver Filter DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Lemma 4.6 v2 isolated provider (both distance modes); packaging only. -/
theorem geo_exist_both_modes_source_provider :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
        (hL : ∀ j, 0 ≤ L w j) (ht : Tendsto (L w) atTop atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a),
        ∃ Q : ∀ n, StageDrawing w n, (∀ n, StageExtends w n (Q n) (Q (n + 1))) ∧
        ∃ G : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2)) (kmswInfRot w hfin)
            (kmswLimitDartVertex w),
          G = monotoneFamilyDrawing w hfin (monotone_family_all w) ∧
          (∀ n v, G.pos v.val = (Q n).pos v) ∧
          (∀ n d, G.arc (d.1.val, d.2) = (Q n).arc d) ∧
          (∃ U : G.Face, G.IsUnbounded U ∧ (∀ F : G.Face, G.IsUnbounded F → F = U) ∧
            ∀ d, G.dartBorders d U ↔ limitExternalDart w d) ∧
          ∀ x : ℕ, (∃ n, x < (kmswStage w n).nextVertex) →
            (∃! P : InfinitePresentPath w ⟨x⟩, P.HasLongestSegments ∧
              ∀ P' : InfinitePresentPath w ⟨x⟩, P'.HasLongestSegments →
                pathTrace G (fun i => (P'.edge i, false)) ⊆
                  closedBetween (pathTrace G (fun i => (P.edge i, false)))
                    (pathTrace G
                      (fun i => ((kmswRightmostPath w hfin hL ht hR x).edge i, false)))) ∧
            (∃! P : InfinitePresentPath w ⟨x⟩, P.HasShortestSegments ∧
              ∀ P' : InfinitePresentPath w ⟨x⟩, P'.HasShortestSegments →
                pathTrace G (fun i => (P'.edge i, false)) ⊆
                  closedBetween (pathTrace G (fun i => (P.edge i, false)))
                    (pathTrace G
                      (fun i => ((kmswRightmostPath w hfin hL ht hR x).edge i, false)))) :=
by exact DirectedDistances.PaperProofs.Section4.geo_exist_both_modes

end DirectedDistances.PaperProofs.SourceResults
