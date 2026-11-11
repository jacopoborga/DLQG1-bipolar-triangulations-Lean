module

public import DirectedDistances.RandomWalk.IIDVectorWalk
public import DirectedDistances.RandomWalk.PitmanCodes

/-! # Integrated code law for the UIQBOT walk

A path-to-code law helper toward Definition 4.1 (`def-uiqbot`, -/

public section
namespace DirectedDistances.RandomWalk

/-- The integrated Pitman-flipped code walk has the conditioned walk law used in -/
theorem uiqbot_integrated_code_law :
    iidCodeMeasure.map
      (fun ω => integrateCodes (pitmanCode (fun i => ω (i + 1)))) =
    conditionedVectorPathLaw 0 0 := by
  have hfun :
      (fun ω : ℕ → Fin 3 =>
        integrateCodes (pitmanCode (fun i => ω (i + 1)))) =
      (fun ω : ℕ → Fin 3 => fun k => vectorPitman (codeWalk ω) k) := by
    funext ω k
    rw [integrateCodes_pitmanCode]
    have hpath : integrateCodes (fun i => ω (i + 1)) = codeWalk ω := by
      funext n
      exact (codeWalk_eq_integrateCodes ω n).symm
    rw [hpath]
  rw [hfun, map_vectorPitman_codeWalk]

end DirectedDistances.RandomWalk
