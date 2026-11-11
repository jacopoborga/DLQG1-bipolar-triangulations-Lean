/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.GeoExist
public import DirectedDistances.KMSW.KMSWConstructedRealizationProof
public import DirectedDistances.KMSW.LeftmostRegionForward
public import DirectedDistances.KMSW.LeftmostRegionBackward
public import DirectedDistances.PlanarMap.VariableRayStrip

/-! Supporting lemmas for paper labels `lem-geo-exist` (see CORRESPONDENCE.md). -/













public section
namespace DirectedDistances.PaperProofs.Section4

open MeasureTheory Quiver Filter DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- The constructed family drawing of the KMSW union has a unique unbounded face, and its
bordering darts are exactly the persistent external darts, under the UIQBOT hypotheses. This is
the face clause of `kmswConstructedPlaneRealization` for the specific drawing
`monotoneFamilyDrawing w hfin (monotone_family_all w)`.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem monotoneFamilyDrawing_faceClassification (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    ∃ U : P.Face, P.IsUnbounded U ∧
      (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      ∀ d, P.dartBorders d U ↔ limitExternalDart w d := by
  have hbd := monotoneRegionBoundedExhaustion_of_KMSW w hfin htrans hR hL0
    (familyQ w (monotone_family_all w)) (familyG w (monotone_family_all w))
  refine monotoneFamily_hface w hfin htrans hR hL0 (monotone_family_all w)
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact monotoneLimitExterior_isOpen_of_boundedExhaustion _ _ hbd
  · exact monotoneLimitExterior_isPathConnected_of_KMSW w hfin htrans hR hL0 _ _
  · exact monotoneLimitExterior_unbounded_of_xmin_zero _ _
      (fun n => monotoneStageInvariant_xmin_eq_zero_of_hL0 hL0 _)
  · exact monotoneLimitExterior_frontier_subset_trace _ _ hbd
  · exact fun n => monotoneLimitExterior_disjoint_stageImage _ _ n
  · intro z hz hzE
    apply monotoneStageRegionUnion_mem_cap_of_not_trace _ _ (not_not.mp hzE)
    simp only [monotoneLayoutTraceUnion, Set.mem_iUnion, not_exists]
    exact hz

/-- The stage drawings of the constructed family extend one another.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem familyQ_stageExtends (w : ℕ → Fin 3) (n : ℕ) :
    StageExtends w n (familyQ w (monotone_family_all w) n)
      (familyQ w (monotone_family_all w) (n + 1)) :=
  stageExtends_monotoneLayout w n _ _

/-- Lemma 4.6 (`lem-geo-exist`), planar-region reading, proposed provider. Almost surely for the
UIQBOT Pitman code: the constructed x-monotone drawing `monotoneFamilyDrawing` of the KMSW union
is stage-compatible, has a unique unbounded face whose bordering darts are the persistent external
darts (as in the discharged n308 theorem), and in that drawing (west-to-east x-monotone arcs, so
that the vertical-fiber region `closedBetween` is the closed submap between two paths), from every
vertex `x` there is a unique infinite LDP geodesic
`P` such that every infinite LDP geodesic from `x` (vertices and edges) lies in the closed region
weakly to the right of `P` and weakly to the left of the rightmost directed path from `x`.
LDP only (source flag both-mode scope). Helper toward Lemma 4.6 (lem-geo-exist); not a paper result until an -/
theorem geo_exist_planar :
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
            ∃! P : InfinitePresentPath w ⟨x⟩, P.HasLongestSegments ∧
              ∀ P' : InfinitePresentPath w ⟨x⟩, P'.HasLongestSegments →
                pathTrace G (fun i => (P'.edge i, false)) ⊆
                  closedBetween (pathTrace G (fun i => (P.edge i, false)))
                    (pathTrace G
                      (fun i => ((kmswRightmostPath w hfin hL ht hR x).edge i, false))) := by
  filter_upwards [geo_exist] with ω hω
  obtain ⟨hfin, hL, ht, hR, hall⟩ := hω
  let w := pitmanCode (fun i => ω (i + 1))
  have hfam : ∀ n, ∃ P : StageDrawing w n, Nonempty (MonotoneStageInvariant w n P) :=
    fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
      ((monotone_family_all w) n).choose_spec⟩
  refine ⟨hfin, hL, ht, hR, familyQ w (monotone_family_all w), familyQ_stageExtends w,
    monotoneFamilyDrawing w hfin (monotone_family_all w), rfl,
    familyDrawing_pos w hfin (monotone_family_all w),
    familyDrawing_arc w hfin (monotone_family_all w),
    monotoneFamilyDrawing_faceClassification w hfin ht hR hL, fun x hx => ?_⟩
  have hiff : ∀ P : InfinitePresentPath w ⟨x⟩,
      (P.HasLongestSegments ∧ ∀ P' : InfinitePresentPath w ⟨x⟩, P'.HasLongestSegments →
        InBetweenLeftmostRightmost w hfin hL ht hR x P
          (kmswRightmostPath w hfin hL ht hR x) P') ↔
      (P.HasLongestSegments ∧ ∀ P' : InfinitePresentPath w ⟨x⟩, P'.HasLongestSegments →
        pathTrace (monotoneLimitDrawing w hfin hfam) (fun i => (P'.edge i, false)) ⊆
          closedBetween (pathTrace (monotoneLimitDrawing w hfin hfam)
              (fun i => (P.edge i, false)))
            (pathTrace (monotoneLimitDrawing w hfin hfam)
              (fun i => ((kmswRightmostPath w hfin hL ht hR x).edge i, false)))) := by
    intro P
    refine and_congr_right (fun _ => forall_congr' (fun P' => imp_congr_right (fun _ => ?_)))
    exact ⟨trace_subset_closedBetween_of_inBetween w hfin hL ht hR hfam x P _ P',
      inBetween_of_trace_subset_closedBetween w hfin hL ht hR hfam x P _ P'⟩
  obtain ⟨P, hP, huniq⟩ := hall x hx
  exact ⟨P, (hiff P).mp hP, fun P' hP' => huniq P' ((hiff P').mpr hP')⟩

end DirectedDistances.PaperProofs.Section4
