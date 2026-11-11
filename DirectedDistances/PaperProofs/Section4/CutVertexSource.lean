module

public import DirectedDistances.KMSW.UIQBOTCutVertex
public import DirectedDistances.Paper.Section4.RenewalTimeCharacterization
import DirectedDistances.PaperProofs.Section4.CutVertexPathSpace
import DirectedDistances.PaperProofs.Section4.CutEquivPathSpace
import DirectedDistances.PaperProofs.Section4.RenewalCutVertexPathSpace

/-! Supporting lemmas for paper labels `def-cut-vertex`, `lem-cut-equiv`, `lem-renewal`, `prop-cut-vertex` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section4

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.KMSW








theorem source_cut_vertex_infinite :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      (∃ w : ℕ → Fin 3, integrateCodes w = p) ∧
        ∀ w, integrateCodes w = p → {v : ℕ | uiqbotCutVertex w v}.Infinite := by
  filter_upwards [conditionedVectorPathLaw_ae_unique_carrier,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit,
    pathSpace_cutVertex_infinite_for_every_integrating_code] with p hcarrier hpath hcut
  obtain ⟨wc, ⟨hwc, _⟩, _⟩ := hcarrier
  obtain ⟨w₀, hwp₀, hfin, htrans, hR, hL0, _, _⟩ := hpath
  refine ⟨⟨wc, hwc⟩, ?_⟩
  intro w hwp
  have hEq : w = w₀ := integrateCodes_injective (hwp.trans hwp₀.symm)
  subst w
  obtain ⟨hfin', hinf⟩ := hcut w₀ hwp₀
  exact hinf.mono (fun v hv =>
    (uiqbotCutVertex_iff_mapCutVertex w₀ hfin htrans hR hL0 v).mpr hv)








theorem source_cut_equiv :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      (∃ w : ℕ → Fin 3, integrateCodes w = p) ∧
        ∀ w, integrateCodes w = p → ∀ n : ℕ,
          (uiqbotCutVertex w (activeInitial w n) ∧
              ∀ j < n, activeInitial w j ≠ activeInitial w n) ↔
            ((∀ j < n, (p n).2 ≤ (p j).2 - 1) ∧
              ∀ j, n ≤ j → (p n).1 ≤ (p j).1) := by
  filter_upwards [conditionedVectorPathLaw_ae_unique_carrier,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit,
    pathSpace_cut_equiv] with p hcarrier hpath hcut
  obtain ⟨wc, ⟨hwc, _⟩, _⟩ := hcarrier
  obtain ⟨w₀, hwp₀, hfin, htrans, hR, hL0, _, _⟩ := hpath
  refine ⟨⟨wc, hwc⟩, ?_⟩
  intro w hwp
  have hEq : w = w₀ := integrateCodes_injective (hwp.trans hwp₀.symm)
  subst w
  obtain ⟨hfin', hequiv⟩ := hcut w₀ hwp₀
  intro n
  rw [uiqbotCutVertex_iff_mapCutVertex w₀ hfin htrans hR hL0]
  exact hequiv n








theorem source_renewalTime_cutVertex_rank :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      (∃ w : ℕ → Fin 3, integrateCodes w = p) ∧
        ∀ w, integrateCodes w = p → ∀ (m : ℕ) (t : ℕ∞),
          Paper.Section4.renewalTime m p = t ↔
            IsPositiveSuccessTime
              (fun n => uiqbotCutVertex w (activeInitial w n) ∧
                ∀ j < n, activeInitial w j ≠ activeInitial w n) m t := by
  filter_upwards [conditionedVectorPathLaw_ae_unique_carrier,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit,
    pathSpace_renewalTime_cutVertex_rank] with p hcarrier hpath hcut
  obtain ⟨wc, ⟨hwc, _⟩, _⟩ := hcarrier
  obtain ⟨w₀, hwp₀, hfin, htrans, hR, hL0, _, _⟩ := hpath
  refine ⟨⟨wc, hwc⟩, ?_⟩
  intro w hwp
  have hEq : w = w₀ := integrateCodes_injective (hwp.trans hwp₀.symm)
  subst w
  obtain ⟨hfin', hrank⟩ := hcut w₀ hwp₀
  intro m t
  simpa only [uiqbotCutVertex_iff_mapCutVertex w₀ hfin htrans hR hL0] using
    hrank m t









theorem source_root_source_vertex :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      (∃ w : ℕ → Fin 3, integrateCodes w = p) ∧
        ∀ w, integrateCodes w = p → edgeWest w 0 = 0 ∧
          uiqbotCutVertex w (edgeWest w 0) := by
  filter_upwards [conditionedVectorPathLaw_ae_unique_carrier,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit]
    with p hcarrier hpath
  obtain ⟨wc, ⟨hwc, hroot, _⟩, _⟩ := hcarrier
  obtain ⟨w₀, hwp₀, hfin, htrans, hR, hL0, _, _⟩ := hpath
  have hc : w₀ = wc := integrateCodes_injective (hwp₀.trans hwc.symm)
  have hzero : edgeWest w₀ 0 = 0 := by rw [hc]; exact hroot.1
  refine ⟨⟨w₀, hwp₀⟩, ?_⟩
  intro w hwp
  have hEq : w = w₀ := integrateCodes_injective (hwp.trans hwp₀.symm)
  subst w
  refine ⟨hzero, ?_⟩
  rw [hzero, uiqbotCutVertex_iff_mapCutVertex w₀ hfin htrans hR hL0]
  exact mapCutVertex_source w₀ hfin htrans hR hL0

end DirectedDistances.PaperProofs.Section4
