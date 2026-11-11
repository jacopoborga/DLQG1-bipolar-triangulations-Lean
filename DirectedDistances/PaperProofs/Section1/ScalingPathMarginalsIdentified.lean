/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.ScalingPathsIdentified
public import DirectedDistances.Recursive.BusemannWholeLineLimitLdp
public import DirectedDistances.Recursive.BusemannWholeLineLimitSdp
import all DirectedDistances.PaperProofs.Section1.ScalingPathsIdentified
import all DirectedDistances.Recursive.BusemannWholeLineLimitLdp
import all DirectedDistances.Recursive.BusemannWholeLineLimitSdp

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory
open DirectedDistances.Probability DirectedDistances.RandomWalk
open DirectedDistances.Recursive




theorem aemeasurable_identifiedLDPScalingPath (n : ℕ) :
    AEMeasurable (identifiedLDPScalingPath n) wholePlaneIIDCodeMeasure := by
  have hcode :
      (fun W : ℤ → Fin 3 => ldpBusemannWholeLinePath n (shiftedCodePath W 0))
        =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => identifiedLDPScalingPath n W) := by
    filter_upwards [identifiedScalingPaths_eq_code_ae] with W hW
    exact (congrArg (fun f => (f n).1) hW).symm
  exact ((ldpBusemannWholeLinePath_measurable n).comp
    (measurable_shiftedCodePath 0)).aemeasurable.congr hcode




theorem aemeasurable_identifiedSDPScalingPath (n : ℕ) :
    AEMeasurable (identifiedSDPScalingPath n) wholePlaneIIDCodeMeasure := by
  have hcode :
      (fun W : ℤ → Fin 3 => sdpBusemannWholeLinePath n (shiftedCodePath W 0))
        =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => identifiedSDPScalingPath n W) := by
    filter_upwards [identifiedScalingPaths_eq_code_ae] with W hW
    exact (congrArg (fun f => (f n).2) hW).symm
  exact ((sdpBusemannWholeLinePath_measurable n).comp
    (measurable_shiftedCodePath 0)).aemeasurable.congr hcode




theorem identifiedLDPScalingPath_map_eq_wholeLineLaw (n : ℕ) :
    wholePlaneIIDCodeMeasure.map (identifiedLDPScalingPath n) =
      (ldpBusemannWholeLineLaw n : Measure WholeLineCadlag) := by
  have hcode :
      (fun W : ℤ → Fin 3 => identifiedLDPScalingPath n W) =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => ldpBusemannWholeLinePath n (shiftedCodePath W 0)) := by
    filter_upwards [identifiedScalingPaths_eq_code_ae] with W hW
    exact congrArg (fun f => (f n).1) hW
  calc
    wholePlaneIIDCodeMeasure.map (identifiedLDPScalingPath n) =
        wholePlaneIIDCodeMeasure.map
          (fun W => ldpBusemannWholeLinePath n (shiftedCodePath W 0)) :=
      Measure.map_congr hcode
    _ = iidCodeMeasure.map (ldpBusemannWholeLinePath n) := by
      rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0,
        Measure.map_map (ldpBusemannWholeLinePath_measurable n)
          (measurable_shiftedCodePath 0)]
      rfl
    _ = (ldpBusemannWholeLineLaw n : Measure WholeLineCadlag) := rfl




theorem identifiedSDPScalingPath_map_eq_wholeLineLaw (n : ℕ) :
    wholePlaneIIDCodeMeasure.map (identifiedSDPScalingPath n) =
      (sdpBusemannWholeLineLaw n : Measure WholeLineCadlag) := by
  have hcode :
      (fun W : ℤ → Fin 3 => identifiedSDPScalingPath n W) =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => sdpBusemannWholeLinePath n (shiftedCodePath W 0)) := by
    filter_upwards [identifiedScalingPaths_eq_code_ae] with W hW
    exact congrArg (fun f => (f n).2) hW
  calc
    wholePlaneIIDCodeMeasure.map (identifiedSDPScalingPath n) =
        wholePlaneIIDCodeMeasure.map
          (fun W => sdpBusemannWholeLinePath n (shiftedCodePath W 0)) :=
      Measure.map_congr hcode
    _ = iidCodeMeasure.map (sdpBusemannWholeLinePath n) := by
      rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0,
        Measure.map_map (sdpBusemannWholeLinePath_measurable n)
          (measurable_shiftedCodePath 0)]
      rfl
    _ = (sdpBusemannWholeLineLaw n : Measure WholeLineCadlag) := rfl

end DirectedDistances.PaperProofs.Section1
