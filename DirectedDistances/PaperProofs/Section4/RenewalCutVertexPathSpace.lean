module

public import DirectedDistances.KMSW.CutVertexIff
public import DirectedDistances.Paper.Section4.RenewalTimeCharacterization

/-! Supporting lemmas for paper labels `lem-renewal` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section4

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW





theorem pathSpace_renewalTime_cutVertex_rank :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∀ w : ℕ → Fin 3, integrateCodes w = p →
        ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
            ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
          ∀ (m : ℕ) (t : ℕ∞), Paper.Section4.renewalTime m p = t ↔
            IsPositiveSuccessTime
              (fun n => mapCutVertex w hfin (activeInitial w n) ∧
                ∀ j < n, activeInitial w j ≠ activeInitial w n) m t := by
  filter_upwards
    [conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit] with p hpath
  obtain ⟨w₀, hwp₀, hfin, htrans, hR, hL0, _, _⟩ := hpath
  intro w hwp
  have hEq : w = w₀ := integrateCodes_injective (hwp.trans hwp₀.symm)
  subst w
  refine ⟨hfin, ?_⟩
  have hpred :
      (fun n => mapCutVertex w₀ hfin (activeInitial w₀ n) ∧
        ∀ j < n, activeInitial w₀ j ≠ activeInitial w₀ n) =
      (fun j => (∀ k, k < j → (p j).2 ≤ (p k).2 - 1) ∧
        ∀ i, j ≤ i → (p j).1 ≤ (p i).1) := by
    funext n
    apply propext
    rw [mapCutVertex_first_visit_iff _ hfin htrans hR hL0 n]
    simp only [kmsw_L_eq, kmsw_R_eq, hwp₀]
  intro m t
  have hchar := (Paper.Section4.renewalTime_characterization m p).2 t
  rw [← hpred] at hchar
  exact hchar

end DirectedDistances.PaperProofs.Section4
