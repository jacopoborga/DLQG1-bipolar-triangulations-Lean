module

public import DirectedDistances.PaperProofs.Section7.LDPFluctuationIdentified
public import DirectedDistances.PaperProofs.Section7.SDPFluctuationIdentified
public import DirectedDistances.Recursive.BusemannSdpUnconditional
public import DirectedDistances.Recursive.RightStationaryBusemann
public import DirectedDistances.Recursive.LeftStationaryBusemann
public import DirectedDistances.Recursive.MeasurableVersionPos

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-property` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section1

open MeasureTheory ProbabilityTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.Recursive DirectedDistances.PaperProofs.Section7



private theorem code_independent (F : ℤ → (ℕ → Fin 3) → ℤ)
    (hF : ∀ k, Measurable (F k)) (hi : iIndepFun F iidCodeMeasure) :
    iIndepFun (fun k W => F k (shiftedCodePath W 0)) wholePlaneIIDCodeMeasure := by
  have hmeasure (s : Set (ℕ → Fin 3)) (hs : MeasurableSet s) :
      wholePlaneIIDCodeMeasure ((fun W => shiftedCodePath W 0) ⁻¹' s) =
        iidCodeMeasure s := by
    rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0,
      Measure.map_apply (measurable_shiftedCodePath 0) hs]
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hi ⊢
  intro S sets hs
  have hbig : MeasurableSet (⋂ i ∈ S, F i ⁻¹' sets i) :=
    Finset.measurableSet_biInter S (fun i hi => hF i (hs i hi))
  calc
    _ = wholePlaneIIDCodeMeasure
        ((fun W => shiftedCodePath W 0) ⁻¹' ⋂ i ∈ S, F i ⁻¹' sets i) := by
      simp only [Set.preimage_iInter, Set.preimage_preimage]
    _ = iidCodeMeasure (⋂ i ∈ S, F i ⁻¹' sets i) := hmeasure _ hbig
    _ = ∏ i ∈ S, iidCodeMeasure (F i ⁻¹' sets i) := hi S hs
    _ = _ := Finset.prod_congr rfl (fun i hi => (hmeasure _ (hF i (hs i hi))).symm)



private theorem increment_law (X : (ℤ → Fin 3) → ℤ → ℤ)
    (Y : (ℕ → Fin 3) → ℤ → ℤ) (hY : ∀ k, Measurable (fun ω => Y ω k))
    (heq : X =ᵐ[wholePlaneIIDCodeMeasure] (fun W => Y (shiftedCodePath W 0)))
    (k : ℤ) :
    IdentDistrib (fun W => X W k - X W (k - 1)) (ldpIncrement Y k)
      wholePlaneIIDCodeMeasure iidCodeMeasure := by
  have hc : Measurable (ldpIncrement Y k) := (hY k).sub (hY (k - 1))
  have hm := hc.comp (measurable_shiftedCodePath 0)
  have he : (fun W => X W k - X W (k - 1)) =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => ldpIncrement Y k (shiftedCodePath W 0)) := by
    filter_upwards [heq] with W hW
    simp only [hW, ldpIncrement]
  refine ⟨hm.aemeasurable.congr he.symm, hc.aemeasurable, ?_⟩
  calc
    _ = wholePlaneIIDCodeMeasure.map
        (ldpIncrement Y k ∘ (fun W => shiftedCodePath W 0)) := Measure.map_congr he
    _ = (wholePlaneIIDCodeMeasure.map (fun W => shiftedCodePath W 0)).map
        (ldpIncrement Y k) :=
      (Measure.map_map hc (measurable_shiftedCodePath 0)).symm
    _ = _ := by rw [wholePlaneIIDCodeMeasure_map_shiftedPath 0]




theorem thm_busemann_property_ldp_identified :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) (identifiedLDPBusemann W)) ∧
    iIndepFun (fun k W => identifiedLDPBusemann W k - identifiedLDPBusemann W (k - 1))
      wholePlaneIIDCodeMeasure ∧
    (∀ k : ℤ, 1 ≤ k → IdentDistrib
      (fun W => identifiedLDPBusemann W k - identifiedLDPBusemann W (k - 1))
      (fun W => identifiedLDPBusemann W 1 - identifiedLDPBusemann W (1 - 1))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => identifiedLDPBusemann W k - identifiedLDPBusemann W (k - 1))
      (fun W => identifiedLDPBusemann W 0 - identifiedLDPBusemann W (0 - 1))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ, 1 ≤ k →
      identifiedLDPBusemann W k - identifiedLDPBusemann W (k - 1) ≤ -1) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => identifiedLDPBusemann W k - identifiedLDPBusemann W (k - 1))
      (fun W => identifiedLDPBusemann W (k - 1) - identifiedLDPBusemann W k)
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) := by
  have hm (k : ℤ) : Measurable (ldpIncrement busemannLDPMeasurableVersion k) :=
    (measurable_busemannLDPMeasurableVersion k).sub
      (measurable_busemannLDPMeasurableVersion (k - 1))
  have hlaw := increment_law identifiedLDPBusemann busemannLDPMeasurableVersion
    measurable_busemannLDPMeasurableVersion identifiedLDPBusemann_eq_carrier_ae
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [thm_busemann_paper,
      identifiedLDPBusemann_characterization_ae] with W hW hc
    obtain ⟨H, h, hLL, _⟩ := hW
    exact ⟨H, h, hLL, hc H h hLL⟩
  · apply (code_independent _ hm ldpIncrements_iIndep_ldpCode).congr
    intro k
    filter_upwards [identifiedLDPBusemann_eq_carrier_ae] with W hW
    simp only [hW, ldpIncrement]
  · intro k hk
    exact (hlaw k).trans ((IdentDistrib.mk (hm k).aemeasurable (hm 1).aemeasurable
      (busemannLDPMeasurableVersion_right_stationary k hk)).trans (hlaw 1).symm)
  · intro k hk
    exact (hlaw k).trans ((IdentDistrib.mk (hm k).aemeasurable (hm 0).aemeasurable
      (busemannLDPMeasurableVersion_left_stationary k hk)).trans (hlaw 0).symm)
  · have hp := iidCodes_ae_busemannLDPMeasurableVersion_item_pos
    rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0] at hp
    have hpull := ae_of_ae_map (measurable_shiftedCodePath 0).aemeasurable hp
    filter_upwards [hpull, identifiedLDPBusemann_eq_carrier_ae] with W hW heq
    simpa only [heq] using hW
  · intro k hk
    have hs : IdentDistrib (ldpIncrement busemannLDPMeasurableVersion k)
        (fun ω => -ldpIncrement busemannLDPMeasurableVersion k ω)
        iidCodeMeasure iidCodeMeasure :=
      ⟨(hm k).aemeasurable, (hm k).neg.aemeasurable,
        ldp_nonpositive_increment_symmetry_ldpCode k hk⟩
    simpa only [Function.comp_def, neg_sub] using
      (hlaw k).trans (hs.trans ((hlaw k).symm.comp measurable_neg))




theorem thm_busemann_property_sdp_identified :
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) (identifiedSDPBusemann W)) ∧
    iIndepFun (fun k W => identifiedSDPBusemann W k - identifiedSDPBusemann W (k - 1))
      wholePlaneIIDCodeMeasure ∧
    (∀ k : ℤ, 1 ≤ k → IdentDistrib
      (fun W => identifiedSDPBusemann W k - identifiedSDPBusemann W (k - 1))
      (fun W => identifiedSDPBusemann W 1 - identifiedSDPBusemann W (1 - 1))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => identifiedSDPBusemann W k - identifiedSDPBusemann W (k - 1))
      (fun W => identifiedSDPBusemann W 0 - identifiedSDPBusemann W (0 - 1))
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ k : ℤ, 1 ≤ k →
      -1 ≤ identifiedSDPBusemann W k - identifiedSDPBusemann W (k - 1)) ∧
    (∀ k : ℤ, k ≤ 0 → IdentDistrib
      (fun W => identifiedSDPBusemann W k - identifiedSDPBusemann W (k - 1))
      (fun W => identifiedSDPBusemann W (k - 1) - identifiedSDPBusemann W k)
      wholePlaneIIDCodeMeasure wholePlaneIIDCodeMeasure) := by
  have hm (k : ℤ) : Measurable (ldpIncrement busemannSDPMeasurableVersion k) :=
    (measurable_busemannSDPMeasurableVersion k).sub
      (measurable_busemannSDPMeasurableVersion (k - 1))
  have hlaw := increment_law identifiedSDPBusemann busemannSDPMeasurableVersion
    measurable_busemannSDPMeasurableVersion identifiedSDPBusemann_eq_carrier_ae
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [thm_busemann_paper,
      identifiedSDPBusemann_characterization_ae] with W hW hc
    obtain ⟨H, h, hLL, _⟩ := hW
    exact ⟨H, h, hLL, hc H h hLL⟩
  · apply (code_independent _ hm sdpIncrements_iIndep_sdpCode).congr
    intro k
    filter_upwards [identifiedSDPBusemann_eq_carrier_ae] with W hW
    simp only [hW, ldpIncrement]
  · intro k hk
    exact (hlaw k).trans ((IdentDistrib.mk (hm k).aemeasurable (hm 1).aemeasurable
      (busemannSDPMeasurableVersion_right_stationary k hk)).trans (hlaw 1).symm)
  · intro k hk
    exact (hlaw k).trans ((IdentDistrib.mk (hm k).aemeasurable (hm 0).aemeasurable
      (busemannSDPMeasurableVersion_left_stationary k hk)).trans (hlaw 0).symm)
  · have hp := iidCodes_ae_busemannSDPMeasurableVersion_item_pos
    rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0] at hp
    have hpull := ae_of_ae_map (measurable_shiftedCodePath 0).aemeasurable hp
    filter_upwards [hpull, identifiedSDPBusemann_eq_carrier_ae] with W hW heq
    simpa only [heq] using hW
  · intro k hk
    have hs : IdentDistrib (ldpIncrement busemannSDPMeasurableVersion k)
        (fun ω => -ldpIncrement busemannSDPMeasurableVersion k ω)
        iidCodeMeasure iidCodeMeasure :=
      ⟨(hm k).aemeasurable, (hm k).neg.aemeasurable,
        sdp_nonpositive_increment_symmetry_sdpCode k hk⟩
    simpa only [Function.comp_def, neg_sub] using
      (hlaw k).trans (hs.trans ((hlaw k).symm.comp measurable_neg))

end DirectedDistances.PaperProofs.Section1
