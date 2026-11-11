module

public import DirectedDistances.KMSW.StageReversalPhi
public import DirectedDistances.PaperProofs.Section7.CellSDPReversalCorr
public import DirectedDistances.PaperProofs.Section7.CellSDPReverseCell

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW



theorem cellSdpRevCorr_codeReversal (n : ℕ) (ω : ℕ → Fin 3) :
    ∃ phi, cellSdpRevCorr (fun i => ω (i + 1))
      (fun i => codeReversal n ω (i + 1)) n phi := by
  have hrev : ∀ i < n, codeReversal n ω (i + 1) =
      Equiv.swap (0 : Fin 3) 1 (ω (n - 1 - i + 1)) := by
    intro i hi
    rw [codeReversal_stageLetter n ω i hi]
    rw [show n - 1 - i + 1 = n - i by omega]
  exact kmswStage_exists_reversal_phi (fun i => codeReversal n ω (i + 1))
    (fun i => ω (i + 1)) n hrev



theorem cellSdpUpper_reversalShortestExitTransport_proved :
    cellSdpUpper_reversalShortestExitTransport := by
  apply cellSdpUpper_reversalShortestExitTransport_of_revCorr
  intro n _ ω
  exact cellSdpRevCorr_codeReversal n ω



theorem cellSdpUpperConclusion_proved : cellSdpUpperConclusion := by
  apply cell_sdp_upper_of_revCorr
  intro n _ ω
  exact cellSdpRevCorr_codeReversal n ω

end DirectedDistances.PaperProofs.Section7
