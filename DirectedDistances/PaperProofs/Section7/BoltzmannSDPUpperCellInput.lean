module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperProps
public import DirectedDistances.PaperProofs.Section7.CellSDPUpperReversalProof
public import DirectedDistances.PaperProofs.Section7.CellSDPUpperOscillation

public section
namespace DirectedDistances.PaperProofs.Section7

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
The joint cell conclusion is definitionally the input proposition. -/
theorem boltzmannSdpUpper_cellInput_proved : boltzmannSdpUpper_cellInput := by
  exact cellSdpUpperConclusion_proved

end DirectedDistances.PaperProofs.Section7
