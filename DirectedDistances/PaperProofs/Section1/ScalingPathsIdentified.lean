/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.LDPFluctuationIdentified
public import DirectedDistances.PaperProofs.Section7.SDPFluctuationIdentified
public import DirectedDistances.Recursive.BusemannWholeLineLimitLdp
public import DirectedDistances.Recursive.BusemannWholeLineLimitSdp
import DirectedDistances.Probability.SkorokhodFloorStep

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/














public section
namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory
open DirectedDistances.Probability DirectedDistances.RandomWalk
open DirectedDistances.Recursive DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section7



@[expose] noncomputable def identifiedLDPScalingPath (n : ℕ)
    (W : ℤ → Fin 3) : WholeLineCadlag :=
  ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
    (identifiedLDPBusemann W ⌊((n + 1 : ℕ) : ℝ) * t⌋ : ℝ),
    floorStep_isCadlag (fun j => (identifiedLDPBusemann W j : ℝ))
      (((n + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity)⟩



@[expose] noncomputable def identifiedSDPScalingPath (n : ℕ)
    (W : ℤ → Fin 3) : WholeLineCadlag :=
  ⟨fun t => ((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ) *
    (identifiedSDPBusemann W ⌊((n + 1 : ℕ) : ℝ) * t⌋ : ℝ),
    floorStep_isCadlag (fun j => (identifiedSDPBusemann W j : ℝ))
      (((n + 1 : ℕ) : ℝ) ^ (-3 / 4 : ℝ)) ((n + 1 : ℕ) : ℝ) (by positivity)⟩



theorem identifiedLDPScalingPath_apply (k : ℕ) (hk : 0 < k)
    (W : ℤ → Fin 3) (t : ℝ) :
    (identifiedLDPScalingPath (k - 1) W).1 t =
      (k : ℝ) ^ (-3 / 2 : ℝ) * (identifiedLDPBusemann W ⌊(k : ℝ) * t⌋ : ℝ) := by
  simp only [identifiedLDPScalingPath, Nat.sub_add_cancel hk]



theorem identifiedSDPScalingPath_apply (k : ℕ) (hk : 0 < k)
    (W : ℤ → Fin 3) (t : ℝ) :
    (identifiedSDPScalingPath (k - 1) W).1 t =
      (k : ℝ) ^ (-3 / 4 : ℝ) * (identifiedSDPBusemann W ⌊(k : ℝ) * t⌋ : ℝ) := by
  simp only [identifiedSDPScalingPath, Nat.sub_add_cancel hk]





theorem identifiedScalingPaths_eq_code_ae :
    (fun W n => (identifiedLDPScalingPath n W, identifiedSDPScalingPath n W))
      =ᵐ[wholePlaneIIDCodeMeasure]
    (fun W n => (ldpBusemannWholeLinePath n (shiftedCodePath W 0),
      sdpBusemannWholeLinePath n (shiftedCodePath W 0))) := by
  filter_upwards [identifiedLDPBusemann_eq_carrier_ae,
    identifiedSDPBusemann_eq_carrier_ae] with W hL hS
  funext n
  apply Prod.ext
  · apply Subtype.ext
    funext t
    simp only [identifiedLDPScalingPath, ldpBusemannWholeLinePath, hL]
  · apply Subtype.ext
    funext t
    simp only [identifiedSDPScalingPath, sdpBusemannWholeLinePath, hS]




theorem identifiedScalingPaths_zero_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ n : ℕ,
      (identifiedLDPScalingPath n W).1 0 = 0 ∧
      (identifiedSDPScalingPath n W).1 0 = 0 := by
  filter_upwards [identifiedScalingPaths_eq_code_ae] with W hW
  intro n
  have hL := congrArg (fun f => (f n).1.1 0) hW
  have hS := congrArg (fun f => (f n).2.1 0) hW
  constructor
  · simpa only [ldpBusemannWholeLinePath_apply, mul_zero, Int.floor_zero,
      busemannLDPMeasurableVersion_zero, Int.cast_zero] using hL
  · simpa only [sdpBusemannWholeLinePath_apply, mul_zero, Int.floor_zero,
      busemannSDPMeasurableVersion_zero, Int.cast_zero] using hS




theorem measurable_codeScalingPaths :
    Measurable (fun ω n => (ldpBusemannWholeLinePath n ω,
      sdpBusemannWholeLinePath n ω)) := by
  apply measurable_pi_iff.mpr
  intro n
  exact (ldpBusemannWholeLinePath_measurable n).prodMk
    (sdpBusemannWholeLinePath_measurable n)




theorem aemeasurable_identifiedScalingPaths :
    AEMeasurable
      (fun W n => (identifiedLDPScalingPath n W, identifiedSDPScalingPath n W))
      wholePlaneIIDCodeMeasure := by
  exact (measurable_codeScalingPaths.comp (measurable_shiftedCodePath 0)).aemeasurable.congr
    identifiedScalingPaths_eq_code_ae.symm




theorem identifiedScalingPaths_map_eq_code :
    wholePlaneIIDCodeMeasure.map
        (fun W n => (identifiedLDPScalingPath n W, identifiedSDPScalingPath n W)) =
      iidCodeMeasure.map
        (fun ω n => (ldpBusemannWholeLinePath n ω, sdpBusemannWholeLinePath n ω)) := by
  calc
    _ = wholePlaneIIDCodeMeasure.map
        (fun W n => (ldpBusemannWholeLinePath n (shiftedCodePath W 0),
          sdpBusemannWholeLinePath n (shiftedCodePath W 0))) :=
      Measure.map_congr identifiedScalingPaths_eq_code_ae
    _ = _ := by
      rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0,
        Measure.map_map measurable_codeScalingPaths (measurable_shiftedCodePath 0)]
      rfl

end DirectedDistances.PaperProofs.Section1
