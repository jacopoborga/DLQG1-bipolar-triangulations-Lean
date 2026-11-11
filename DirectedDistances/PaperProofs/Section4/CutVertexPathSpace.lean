module

public import DirectedDistances.KMSW.CutVertexIff

/-! Supporting lemmas for paper labels `def-cut-vertex`, `prop-cut-vertex` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section4

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW








theorem pathSpace_cutVertex_infinite_for_every_integrating_code :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∀ w : ℕ → Fin 3, integrateCodes w = p →
        ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
            ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
          {v : ℕ | mapCutVertex w hfin v}.Infinite := by
  filter_upwards
    [conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit] with p hpath
  obtain ⟨w₀, hwp₀, hfin, htrans, hR, hL0, hinf, _⟩ := hpath
  -- The every-integrating-code form follows from integrateCodes_injective.
  intro w hwp
  have hEq : w = w₀ := integrateCodes_injective (hwp.trans hwp₀.symm)
  subst w
  exact ⟨hfin, hinf⟩










theorem pathSpace_bothBoundary_vertices_infinite :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∀ w : ℕ → Fin 3, integrateCodes w = p →
        ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
            ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
          {v : ℕ | mapLeftBoundaryVertex w hfin v ∧
            mapRightBoundaryVertex w hfin v}.Infinite := by
  simpa only [mapCutVertex] using
    pathSpace_cutVertex_infinite_for_every_integrating_code








theorem pathSpace_cutVertex_characterization :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∀ w : ℕ → Fin 3, integrateCodes w = p →
        ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
            ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
          ∀ v : ℕ,
            (mapLeftBoundaryVertex w hfin v ∧ mapRightBoundaryVertex w hfin v) ↔
              (v = 0 ∨ RemovingDisconnects w v) := by
  filter_upwards
    [conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit] with p hpath
  obtain ⟨w₀, hwp₀, hfin, htrans, hR, hL0, _, _⟩ := hpath
  intro w hwp
  have hEq : w = w₀ := integrateCodes_injective (hwp.trans hwp₀.symm)
  subst w
  refine ⟨hfin, ?_⟩
  intro v
  simpa only [mapCutVertex] using
    mapCutVertex_iff_source_or_removingDisconnects w₀ hfin htrans hR hL0 v

end DirectedDistances.PaperProofs.Section4
