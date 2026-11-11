module

public import DirectedDistances.PaperProofs.Section7.LDPFluctuationIdentified
public import DirectedDistances.PaperProofs.Section7.SDPFluctuationIdentified
public import DirectedDistances.Recursive.BusemannSdpUnconditional

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-tail` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory Filter Asymptotics
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive
open DirectedDistances.PaperProofs.Section7



private theorem busemannTailIdentified_ldp_probability (i j : ℤ) (p : ℤ → Prop) :
    wholePlaneIIDCodeMeasure.real
        {W | p (identifiedLDPBusemann W i - identifiedLDPBusemann W j)} =
      iidCodeMeasure.real
        {w | p (busemannLDPMeasurableVersion w i - busemannLDPMeasurableVersion w j)} := by
  have hevent : MeasurableSet
      {w | p (busemannLDPMeasurableVersion w i - busemannLDPMeasurableVersion w j)} :=
    (Set.to_countable {z : ℤ | p z}).measurableSet.preimage
      ((measurable_busemannLDPMeasurableVersion i).sub
        (measurable_busemannLDPMeasurableVersion j))
  calc
    _ = wholePlaneIIDCodeMeasure.real
        {W | p (busemannLDPMeasurableVersion (shiftedCodePath W 0) i -
          busemannLDPMeasurableVersion (shiftedCodePath W 0) j)} := by
      apply measureReal_congr
      filter_upwards [identifiedLDPBusemann_eq_carrier_ae] with W hW
      simp only [hW]
    _ = _ := by
      rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0,
        map_measureReal_apply (measurable_shiftedCodePath 0) hevent]
      rfl



private theorem busemannTailIdentified_sdp_probability (i j : ℤ) (p : ℤ → Prop) :
    wholePlaneIIDCodeMeasure.real
        {W | p (identifiedSDPBusemann W i - identifiedSDPBusemann W j)} =
      iidCodeMeasure.real
        {w | p (busemannSDPMeasurableVersion w i - busemannSDPMeasurableVersion w j)} := by
  have hevent : MeasurableSet
      {w | p (busemannSDPMeasurableVersion w i - busemannSDPMeasurableVersion w j)} :=
    (Set.to_countable {z : ℤ | p z}).measurableSet.preimage
      ((measurable_busemannSDPMeasurableVersion i).sub
        (measurable_busemannSDPMeasurableVersion j))
  calc
    _ = wholePlaneIIDCodeMeasure.real
        {W | p (busemannSDPMeasurableVersion (shiftedCodePath W 0) i -
          busemannSDPMeasurableVersion (shiftedCodePath W 0) j)} := by
      apply measureReal_congr
      filter_upwards [identifiedSDPBusemann_eq_carrier_ae] with W hW
      simp only [hW]
    _ = _ := by
      rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0,
        map_measureReal_apply (measurable_shiftedCodePath 0) hevent]
      rfl



theorem busemannTailIdentified_sdp_increment_mean_zero (k : ℤ) :
    Integrable (fun W => ((identifiedSDPBusemann W k -
      identifiedSDPBusemann W (k - 1) : ℤ) : ℝ)) wholePlaneIIDCodeMeasure ∧
      (∫ W, ((identifiedSDPBusemann W k -
        identifiedSDPBusemann W (k - 1) : ℤ) : ℝ) ∂wholePlaneIIDCodeMeasure) = 0 := by
  have heq : (fun W => ((identifiedSDPBusemann W k -
      identifiedSDPBusemann W (k - 1) : ℤ) : ℝ)) =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => ((busemannSDPMeasurableVersion (shiftedCodePath W 0) k -
        busemannSDPMeasurableVersion (shiftedCodePath W 0) (k - 1) : ℤ) : ℝ)) := by
    filter_upwards [identifiedSDPBusemann_eq_carrier_ae] with W hW
    simp only [hW]
  obtain ⟨hi, hz⟩ := busemann_sdp_increment_mean_zero_sdpCode k
  have himap : Integrable (fun w => ((busemannSDPMeasurableVersion w k -
      busemannSDPMeasurableVersion w (k - 1) : ℤ) : ℝ))
      (wholePlaneIIDCodeMeasure.map (fun W => shiftedCodePath W 0)) := by
    rw [wholePlaneIIDCodeMeasure_map_shiftedPath 0]
    exact hi
  refine ⟨(himap.comp_measurable (measurable_shiftedCodePath 0)).congr heq.symm, ?_⟩
  calc
    _ = ∫ W, ((busemannSDPMeasurableVersion (shiftedCodePath W 0) k -
        busemannSDPMeasurableVersion (shiftedCodePath W 0) (k - 1) : ℤ) : ℝ)
        ∂wholePlaneIIDCodeMeasure := integral_congr_ae heq
    _ = ∫ w, ((busemannSDPMeasurableVersion w k -
        busemannSDPMeasurableVersion w (k - 1) : ℤ) : ℝ) ∂iidCodeMeasure := by
      rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0]
      exact (integral_map (measurable_shiftedCodePath 0).aemeasurable
        himap.aestronglyMeasurable).symm
    _ = 0 := hz




theorem thm_busemann_tail_ldp_identified :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) (identifiedLDPBusemann W)) ∧
    ∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => wholePlaneIIDCodeMeasure.real
        {W | ((identifiedLDPBusemann W 1 - identifiedLDPBusemann W 0 : ℤ) : ℝ) ≤ -x} -
          c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) ∧
      ((fun x : ℝ => wholePlaneIIDCodeMeasure.real
        {W | x ≤ |((identifiedLDPBusemann W 0 -
          identifiedLDPBusemann W (-1) : ℤ) : ℝ)|} -
            2 * c * x ^ (-(2 / 3 : ℝ))) =o[atTop]
              (fun x : ℝ => x ^ (-(2 / 3 : ℝ)))) := by
  constructor
  · filter_upwards [thm_busemann_paper,
      identifiedLDPBusemann_characterization_ae] with W hW hchar
    obtain ⟨H, h, hLL, _⟩ := hW
    exact ⟨H, h, hLL, hchar H h hLL⟩
  · obtain ⟨c, hc, hpos, hneg⟩ := busemann_tail_ldp_ldpCode
    refine ⟨c, hc, ?_, ?_⟩
    · have hp (x : ℝ) :=
        busemannTailIdentified_ldp_probability 1 0 (fun z => (z : ℝ) ≤ -x)
      simpa only [hp] using hpos
    · have hp (x : ℝ) :=
        busemannTailIdentified_ldp_probability 0 (-1) (fun z => x ≤ |(z : ℝ)|)
      simpa only [hp] using hneg




theorem thm_busemann_tail_sdp_identified :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) (identifiedSDPBusemann W)) ∧
    (∃ c : ℝ, 0 < c ∧
      ((fun x : ℝ => wholePlaneIIDCodeMeasure.real
        {W | x ≤ ((identifiedSDPBusemann W 1 - identifiedSDPBusemann W 0 : ℤ) : ℝ)} -
          c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
            (fun x : ℝ => x ^ (-(4 / 3 : ℝ)))) ∧
      ((fun x : ℝ => wholePlaneIIDCodeMeasure.real
        {W | x ≤ |((identifiedSDPBusemann W 0 -
          identifiedSDPBusemann W (-1) : ℤ) : ℝ)|} -
            2 * c * x ^ (-(4 / 3 : ℝ))) =o[atTop]
              (fun x : ℝ => x ^ (-(4 / 3 : ℝ))))) ∧
    ∀ k : ℤ,
      Integrable (fun W => ((identifiedSDPBusemann W k -
        identifiedSDPBusemann W (k - 1) : ℤ) : ℝ)) wholePlaneIIDCodeMeasure ∧
        (∫ W, ((identifiedSDPBusemann W k -
          identifiedSDPBusemann W (k - 1) : ℤ) : ℝ) ∂wholePlaneIIDCodeMeasure) = 0 := by
  refine ⟨?_, ?_, busemannTailIdentified_sdp_increment_mean_zero⟩
  · filter_upwards [thm_busemann_paper,
      identifiedSDPBusemann_characterization_ae] with W hW hchar
    obtain ⟨H, h, hLL, _⟩ := hW
    exact ⟨H, h, hLL, hchar H h hLL⟩
  · obtain ⟨c, hc, hpos, hneg⟩ := busemann_tail_sdp_sdpCode
    refine ⟨c, hc, ?_, ?_⟩
    · have hp (x : ℝ) :=
        busemannTailIdentified_sdp_probability 1 0 (fun z => x ≤ (z : ℝ))
      simpa only [hp] using hpos
    · have hp (x : ℝ) :=
        busemannTailIdentified_sdp_probability 0 (-1) (fun z => x ≤ |(z : ℝ)|)
      simpa only [hp] using hneg

end DirectedDistances.PaperProofs.Section1
