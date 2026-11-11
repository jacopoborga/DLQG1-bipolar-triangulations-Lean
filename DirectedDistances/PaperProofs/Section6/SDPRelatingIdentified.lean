/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section6.SDPRelating
public import DirectedDistances.PaperProofs.Section7.SDPFluctuationIdentified
import DirectedDistances.Recursive.SDPSplitting
import DirectedDistances.RandomWalk.TwoSidedIIDCodeMeasure

/-! Supporting lemmas for paper labels `lem:SDP-relating-X1-X` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PaperProofs.Section6

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.Recursive DirectedDistances.PaperProofs.Section1
open DirectedDistances.PaperProofs.Section7




private theorem wholePlane_ae_sdp_relating_representatives :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      let omega := shiftedCodePath W 0
      let w := fun i => omega (i + 1)
      let X := busemannSDPMeasurableVersion omega
      let X1 := busemannSDPMeasurableVersion w
      ∃ h0 : BoundaryHitWitnesses w,
      ∃ h1 : BoundaryHitWitnesses (fun i => w (1 + i)),
        IsBoundaryBusemannSDP (boundaryPresentVertex w h0) X ∧
        IsBoundaryBusemannSDP (boundaryPresentVertex _ h1) X1 ∧
        (omega 1 = 2 → (X (-1), X 1) =
          (X1 (-2) - min (X1 (-1)) 1, -min (X1 (-1)) 1)) ∧
        (omega 1 = 0 → (X (-1), X 1) = (-X1 1 - 1, -1)) ∧
        (omega 1 = 1 → (X (-1), X 1) =
          (X1 (-1) - min 0 (X1 2 + 1), X1 2 - min 0 (X1 2 + 1))) := by
  have hp := iidCodes_ae_busemannSDPMeasurableVersion_relating_data
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0] at hp
  exact ae_of_ae_map (measurable_shiftedCodePath 0).aemeasurable hp




private theorem wholePlane_shift_one_measurePreserving :
    MeasurePreserving (fun W : ℤ → Fin 3 => fun i => W (i + 1))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure := by
  refine ⟨measurable_pi_iff.mpr (fun i => measurable_pi_apply (i + 1)), ?_⟩
  exact wholePlaneIIDCodeMeasure_map_shift 1




private theorem sdpVersion_congr_positive {omega eta : ℕ → Fin 3}
    (h : ∀ i, omega (i + 1) = eta (i + 1)) :
    busemannSDPMeasurableVersion omega = busemannSDPMeasurableVersion eta := by
  classical
  have htail : (fun i => omega (i + 1)) = fun i => eta (i + 1) := funext h
  have hw : codeWalk omega = codeWalk eta := by
    funext n
    simp only [codeWalk, h]
  have hfst (a : ℤ) : codeFstFirstHit a omega = codeFstFirstHit a eta := by
    let F (z : ℕ → ℤ × ℤ) : ℕ∞ :=
      if h : ∃ n, (z n).1 = a then (Nat.find h : ℕ∞) else ⊤
    exact congrArg F hw
  have hsnd (a : ℤ) : codeSndFirstHit a omega = codeSndFirstHit a eta := by
    let F (z : ℕ → ℤ × ℤ) : ℕ∞ :=
      if h : ∃ n, (z n).2 = a then (Nat.find h : ℕ∞) else ⊤
    exact congrArg F hw
  have hh : boundaryHitTimeTotal omega = boundaryHitTimeTotal eta := by
    funext k
    simp only [boundaryHitTimeTotal, hfst, hsnd]
  have hid : busemannBoundaryIdTotal omega = busemannBoundaryIdTotal eta := by
    funext k
    simp only [busemannBoundaryIdTotal, htail, hh]
  have hstage (n a b : ℕ) :
      busemannStageSdpCode omega n a b = busemannStageSdpCode eta n a b := by
    exact congrArg (fun w : ℕ → Fin 3 => Int.ofNat
      ((DirectedDistances.sdp
        (⟨a⟩ : DirectedDistances.KMSW.StagePresentVertex w n) ⟨b⟩).toNat)) htail
  funext k
  simp only [busemannSDPMeasurableVersion, boundarySdpDifference, hid, hstage]




private theorem wholePlane_ae_sdp_relating_pins :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (∃ H : WholePlaneRotationHypothesis W,
        ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
          IsIdentifiedM0BusemannSDP (m0CutData W H h hLL)
            (identifiedSDPBusemann W)) ∧
      (let W1 : ℤ → Fin 3 := fun i => W (i + 1)
       ∃ H : WholePlaneRotationHypothesis W1,
        ∃ h : BoundaryHitWitnesses (shiftedStream W1 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W1
          (wholePlaneEdgeι W1 0 (kmswLLCreatedEdge (shiftedStream W1 0)
            (boundaryHitTime (shiftedStream W1 0) h (k - 1)))),
          IsIdentifiedM0BusemannSDP (m0CutData W1 H h hLL)
            (identifiedSDPBusemann W1)) := by
  have hzero : ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL)
          (identifiedSDPBusemann W) := by
    filter_upwards [m0Cut_busemann_identified_ae,
      identifiedSDPBusemann_characterization_ae] with W hdata hchar
    obtain ⟨H, h, hLL, _⟩ := hdata
    exact ⟨H, h, hLL, hchar H h hLL⟩
  have hone := wholePlane_shift_one_measurePreserving.quasiMeasurePreserving.ae hzero
  filter_upwards [hzero, hone] with W h0 h1
  exact ⟨h0, h1⟩




private theorem wholePlane_ae_sdp_relating_carrier_eq :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      identifiedSDPBusemann W =
        busemannSDPMeasurableVersion (shiftedCodePath W 0) ∧
      identifiedSDPBusemann (fun i => W (i + 1)) =
        busemannSDPMeasurableVersion
          (shiftedCodePath (fun i => W (i + 1)) 0) := by
  have hone := wholePlane_shift_one_measurePreserving.quasiMeasurePreserving.ae
    identifiedSDPBusemann_eq_carrier_ae
  filter_upwards [identifiedSDPBusemann_eq_carrier_ae, hone] with W h0 h1
  exact ⟨h0, h1⟩



theorem lem_sdp_relating_identified :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      let W1 : ℤ → Fin 3 := fun i => W (i + 1)
      let X := identifiedSDPBusemann W
      let X1 := identifiedSDPBusemann W1
      (∃ H : WholePlaneRotationHypothesis W,
        ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
          IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X) ∧
      (∃ H : WholePlaneRotationHypothesis W1,
        ∃ h : BoundaryHitWitnesses (shiftedStream W1 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W1
          (wholePlaneEdgeι W1 0 (kmswLLCreatedEdge (shiftedStream W1 0)
            (boundaryHitTime (shiftedStream W1 0) h (k - 1)))),
          IsIdentifiedM0BusemannSDP (m0CutData W1 H h hLL) X1) ∧
      (shiftedStream W 0 0 = 2 →
        (X (-1), X 1) = (X1 (-2) - min (X1 (-1)) 1, -min (X1 (-1)) 1)) ∧
      (shiftedStream W 0 0 = 0 → (X (-1), X 1) = (-X1 1 - 1, -1)) ∧
      (shiftedStream W 0 0 = 1 →
        (X (-1), X 1) =
          (X1 (-1) - min 0 (X1 2 + 1), X1 2 - min 0 (X1 2 + 1))) := by
  filter_upwards [wholePlane_ae_sdp_relating_representatives,
    wholePlane_ae_sdp_relating_pins, wholePlane_ae_sdp_relating_carrier_eq]
      with W hrel hpins heq
  dsimp only at hrel
  obtain ⟨_, _, _, _, hformula⟩ := hrel
  obtain ⟨hp0, hp1⟩ := hpins
  obtain ⟨heq0, heq1⟩ := heq
  have hrep1 : busemannSDPMeasurableVersion
      (fun i => shiftedCodePath W 0 (i + 1)) =
        busemannSDPMeasurableVersion
          (shiftedCodePath (fun i => W (i + 1)) 0) := by
    apply sdpVersion_congr_positive
    intro i
    simp [shiftedCodePath, shiftedStream]
  refine ⟨hp0, hp1, ?_⟩
  rw [← heq0, hrep1, ← heq1] at hformula
  simpa [shiftedCodePath, shiftedStream] using hformula

end DirectedDistances.PaperProofs.Section6
