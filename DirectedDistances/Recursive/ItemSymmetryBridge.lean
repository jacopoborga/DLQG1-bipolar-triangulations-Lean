module

public import DirectedDistances.Recursive.LeftStationaryBusemann
public import DirectedDistances.Recursive.LDPMasterFromLaw
public import DirectedDistances.Recursive.SDPMasterFromLaw
public import DirectedDistances.Recursive.BusemannMeasurable

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-property` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.Recursive

open MeasureTheory DirectedDistances.RandomWalk



theorem ldp_nonpositive_increment_symmetry
    (hsym : iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω)) :
    ∀ k ≤ 0, iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion k ω) := by
  intro k hk
  have hstat := busemannLDPMeasurableVersion_left_stationary k hk
  have hmeas (i : ℤ) :
      Measurable (fun ω => ldpIncrement busemannLDPMeasurableVersion i ω) := by
    change Measurable (fun ω =>
      busemannLDPMeasurableVersion ω i - busemannLDPMeasurableVersion ω (i - 1))
    exact (measurable_busemannLDPMeasurableVersion i).sub
      (measurable_busemannLDPMeasurableVersion (i - 1))
  calc
    iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k) =
        iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) := hstat
    _ = iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω) := hsym
    _ = (iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0)).map
        (fun z : ℤ => -z) := by
          rw [Measure.map_map measurable_neg (hmeas 0)]
          rfl
    _ = (iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion k)).map
        (fun z : ℤ => -z) :=
          congrArg (fun ν : Measure ℤ => ν.map (fun z : ℤ => -z)) hstat.symm
    _ = iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion k ω) := by
          rw [Measure.map_map measurable_neg (hmeas k)]
          rfl



theorem sdp_nonpositive_increment_symmetry
    (hsym : iidCodeMeasure.map
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω)) :
    ∀ k ≤ 0, iidCodeMeasure.map
        (SDPMasterFromLaw.increment busemannSDPMeasurableVersion k) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion k ω) := by
  intro k hk
  have hstat := busemannSDPMeasurableVersion_left_stationary k hk
  have hmeas (i : ℤ) :
      Measurable (fun ω =>
        SDPMasterFromLaw.increment busemannSDPMeasurableVersion i ω) := by
    change Measurable (fun ω =>
      busemannSDPMeasurableVersion ω i - busemannSDPMeasurableVersion ω (i - 1))
    exact (measurable_busemannSDPMeasurableVersion i).sub
      (measurable_busemannSDPMeasurableVersion (i - 1))
  calc
    iidCodeMeasure.map
        (SDPMasterFromLaw.increment busemannSDPMeasurableVersion k) =
        iidCodeMeasure.map
          (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) := hstat
    _ = iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω) := hsym
    _ = (iidCodeMeasure.map
        (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0)).map
        (fun z : ℤ => -z) := by
          rw [Measure.map_map measurable_neg (hmeas 0)]
          rfl
    _ = (iidCodeMeasure.map
        (SDPMasterFromLaw.increment busemannSDPMeasurableVersion k)).map
        (fun z : ℤ => -z) :=
          congrArg (fun ν : Measure ℤ => ν.map (fun z : ℤ => -z)) hstat.symm
    _ = iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion k ω) := by
          rw [Measure.map_map measurable_neg (hmeas k)]
          rfl

end DirectedDistances.Recursive
