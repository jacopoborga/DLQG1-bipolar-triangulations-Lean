module

public import DirectedDistances.KMSW.CutVertexIff

/-! Supporting lemmas for paper labels `lem-cut-equiv` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section4

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW






theorem pathSpace_cut_equiv :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∀ w : ℕ → Fin 3, integrateCodes w = p →
        ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
            ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
          ∀ n : ℕ,
            (mapCutVertex w hfin (activeInitial w n) ∧
                ∀ j < n, activeInitial w j ≠ activeInitial w n) ↔
              ((∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
                ∀ j, n ≤ j → (p n).1 ≤ (p j).1) := by
  filter_upwards
    [conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit] with p hpath
  obtain ⟨w₀, hwp₀, hfin, htrans, hR, hL0, _, _⟩ := hpath
  intro w hwp
  have hEq : w = w₀ := integrateCodes_injective (hwp.trans hwp₀.symm)
  subst w
  refine ⟨hfin, fun n => ?_⟩
  rw [mapCutVertex_first_visit_iff _ hfin htrans hR hL0 n]
  simp only [kmsw_L_eq, kmsw_R_eq, hwp₀]




theorem pathSpace_cut_equiv_unique_integrating_code :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∃! w : ℕ → Fin 3, integrateCodes w = p ∧
        ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
            ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
          ∀ n : ℕ,
            (mapCutVertex w hfin (activeInitial w n) ∧
                ∀ j < n, activeInitial w j ≠ activeInitial w n) ↔
              ((∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
                ∀ j, n ≤ j → (p n).1 ≤ (p j).1) := by
  filter_upwards
    [conditionedVectorPathLaw_ae_unique_carrier, pathSpace_cut_equiv]
    with p hcarrier hcut
  obtain ⟨w₀, ⟨hwp₀, _, _, _⟩, _⟩ := hcarrier
  refine ⟨w₀, ⟨hwp₀, hcut w₀ hwp₀⟩, ?_⟩
  intro w hw
  exact integrateCodes_injective (hw.1.trans hwp₀.symm)

end DirectedDistances.PaperProofs.Section4
