/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.CutVertexLink
public import DirectedDistances.KMSW.CutVertexDisconnects
public import DirectedDistances.KMSW.PathSpaceTransferCarrier

/-! # Cut vertices and undirected separation

The outer-boundary characterization and the finite-path separation criterion
are equivalent for every code satisfying the carrier hypotheses -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory
open DirectedDistances.RandomWalk

/-- The finite undirected path separation predicate used by
`mapCutVertex_removed_disconnected` (`def-cut-vertex`, -/
@[expose] def RemovingDisconnects (w : ℕ → Fin 3) (v : ℕ) : Prop :=
  ∃ x y, x ≠ v ∧ y ≠ v ∧
    ∀ p : FiniteUndirectedEdgePath w x y, v ∈ p.vertices

/-- A code-level cut vertex is either the source or separates two allocated
vertices by the exact finite-path predicate in `CutVertexDisconnects` -/
theorem mapCutVertex_iff_source_or_removingDisconnects (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (v : ℕ) :
    mapCutVertex w hfin v ↔ v = 0 ∨ RemovingDisconnects w v := by
  constructor
  · intro hcut
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    · right
      obtain ⟨x, y, hxalloc, hyalloc, hx, hy, hpaths⟩ :=
        mapCutVertex_removed_disconnected_allocated w hfin htrans hR hL0 hcut hv0
      exact ⟨x, y, hx, hy, hpaths⟩
  · intro h
    by_cases hv0 : v = 0
    · subst v
      exact mapCutVertex_source w hfin htrans hR hL0
    · rcases h with hv | hdisc
      · exact (hv0 hv).elim
      · rw [mapCutVertex_iff w hfin htrans hR hL0 v]
        exact kmsw_removed_disconnected_implies_IsCutVertex
          w hfin htrans hR hL0 hv0 hdisc

/-- Almost surely, the deterministic source-or-separation characterization
holds for the Pitman code, with finite incidence and the boundary hypotheses
supplied by the existing carrier theorem (`def-cut-vertex`, -/
theorem pitmanCodes_ae_mapCutVertex_iff_source_or_removingDisconnects :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∀ v, mapCutVertex w hfin v ↔ v = 0 ∨ RemovingDisconnects w v := by
  filter_upwards [pitmanCodes_ae_infinite_mapCutVertices] with ω hω
  dsimp at hω
  obtain ⟨hfin, htrans, hR, hL0, _⟩ := hω
  refine ⟨hfin, ?_⟩
  intro v
  exact mapCutVertex_iff_source_or_removingDisconnects
    (pitmanCode (fun i => ω (i + 1))) hfin htrans hR hL0 v

/-- Under the conditioned path law there is an integrating code realization
whose map-level cut vertices obey the same source-or-separation criterion -/
theorem conditionedVectorPathLaw_ae_mapCutVertex_iff_source_or_removingDisconnects :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃ w : ℕ → Fin 3, integrateCodes w = p ∧
        ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
            ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
          Filter.Tendsto (L w) Filter.atTop Filter.atTop ∧
          (∀ a : ℤ, ∃ n, R w n ≤ a) ∧ (∀ j, 0 ≤ L w j) ∧
          ∀ v, mapCutVertex w hfin v ↔ v = 0 ∨ RemovingDisconnects w v := by
  filter_upwards [conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit]
    with p hp
  obtain ⟨w, hwp, hfin, htrans, hR, hL0, _, _⟩ := hp
  refine ⟨w, hwp, hfin, htrans, hR, hL0, ?_⟩
  intro v
  exact mapCutVertex_iff_source_or_removingDisconnects w hfin htrans hR hL0 v

end DirectedDistances.KMSW
