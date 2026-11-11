module

public import DirectedDistances.PaperProofs.Section7.CellSDPUpperUnconditional
public import DirectedDistances.PaperProofs.Section1.BusemannPaperStatement
public import DirectedDistances.PaperProofs.Section1.BusemannM0Identified
public import DirectedDistances.Recursive.BusemannSDPMeasurable

/-! Supporting lemmas for paper labels `lem-sdp-fluctuation` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.Recursive DirectedDistances.PaperProofs.Section1





private theorem wholePlane_ae_sdp_carrier_data :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        IsBoundaryBusemannSDP (boundaryPresentVertex _ h)
          (busemannSDPMeasurableVersion (shiftedCodePath W 0)) := by
  have hp := iidCodes_ae_busemannSDPMeasurableVersion
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0] at hp
  have hpull := ae_of_ae_map (measurable_shiftedCodePath 0).aemeasurable hp
  filter_upwards [hpull] with W hW
  have htail : (fun i => shiftedCodePath W 0 (i + 1)) = shiftedStream W 0 := by
    funext i
    simp [shiftedCodePath]
  rw [htail] at hW
  exact hW





theorem identifiedSDP_eq_carrier_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
        (X : ℤ → ℤ),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X →
          X = busemannSDPMeasurableVersion (shiftedCodePath W 0) := by
  filter_upwards [thm_busemann_paper,
    wholePlane_ae_sdp_carrier_data] with W hW hc
  obtain ⟨H, h, hLL, _, _, _, _, _, _, _, hpair⟩ := hW
  obtain ⟨huniq, _⟩ := hpair
  obtain ⟨h', hrep⟩ := hc
  intro H' h'' hLL' X hX
  have hH : H' = H := Subsingleton.elim _ _
  subst H'
  have hh : h'' = h := Subsingleton.elim _ _
  subst h''
  have hcut : hLL' = hLL := Subsingleton.elim _ _
  subst hLL'
  have hhit : h' = h := Subsingleton.elim _ _
  subst h'
  have hr' := (boundaryBusemannSDP_iff_identified W H h hLL
    (busemannSDPMeasurableVersion (shiftedCodePath W 0))).mp hrep
  obtain ⟨Y, hY, hu⟩ := huniq
  exact (hu X hX).trans (hu _ hr').symm





@[expose] noncomputable def identifiedSDPBusemann
    (W : ℤ → Fin 3) : ℤ → ℤ := by
  classical
  exact if hW : ∃ X : ℤ → ℤ, ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X
  then hW.choose else fun _ => 0





theorem identifiedSDPBusemann_eq_carrier_ae :
    identifiedSDPBusemann =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => busemannSDPMeasurableVersion (shiftedCodePath W 0)) := by
  classical
  filter_upwards [m0Cut_busemann_identified_ae,
    identifiedSDP_eq_carrier_ae] with W hW heq
  obtain ⟨H, h, hLL, _, hSDP, _⟩ := hW
  obtain ⟨X, hX, _⟩ := hSDP
  have hex : ∃ X : ℤ → ℤ, ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL) X := ⟨X, H, h, hLL, hX⟩
  rw [identifiedSDPBusemann, dite_eq_left hex]
  obtain ⟨H', h', hLL', hX'⟩ := hex.choose_spec
  exact heq H' h' hLL' _ hX'





theorem identifiedSDPBusemann_characterization_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1))))),
        IsIdentifiedM0BusemannSDP (m0CutData W H h hLL)
          (identifiedSDPBusemann W) := by
  filter_upwards [wholePlane_ae_sdp_carrier_data,
    identifiedSDPBusemann_eq_carrier_ae] with W hc heq
  obtain ⟨h', hrep⟩ := hc
  intro H h hLL
  rw [heq]
  have hh : h = h' := Subsingleton.elim _ _
  subst h
  exact (boundaryBusemannSDP_iff_identified W H h' hLL _).mp hrep





theorem aemeasurable_identifiedSDPBusemann :
    AEMeasurable identifiedSDPBusemann wholePlaneIIDCodeMeasure := by
  have hm : Measurable
      (fun W => busemannSDPMeasurableVersion (shiftedCodePath W 0)) :=
    (measurable_pi_iff.mpr measurable_busemannSDPMeasurableVersion).comp
      (measurable_shiftedCodePath 0)
  exact hm.aemeasurable.congr identifiedSDPBusemann_eq_carrier_ae.symm





theorem nullMeasurableSet_identifiedSDPBusemann_fluctuation
    (k : ℕ) (A : ℝ) :
    NullMeasurableSet {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(identifiedSDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)}
      wholePlaneIIDCodeMeasure := by
  change NullMeasurableSet (identifiedSDPBusemann ⁻¹'
    {X : ℤ → ℤ | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(X l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)}) wholePlaneIIDCodeMeasure
  apply aemeasurable_identifiedSDPBusemann.nullMeasurableSet_preimage
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro l
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le
    ((measurable_of_countable (fun z : ℤ => |(z : ℝ)|)).comp
      (measurable_pi_apply l)) measurable_const





theorem identifiedSDPBusemann_fluctuation_probability (k : ℕ) (A : ℝ) :
    wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(identifiedSDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)} =
    iidCodeMeasure.real {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(busemannSDPMeasurableVersion ω l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  have hevent : MeasurableSet {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(busemannSDPMeasurableVersion ω l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro l
    apply MeasurableSet.iInter
    intro _
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le
      ((measurable_of_countable (fun z : ℤ => |(z : ℝ)|)).comp
        (measurable_busemannSDPMeasurableVersion l)) measurable_const
  calc
    _ = wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
        |(busemannSDPMeasurableVersion (shiftedCodePath W 0) l : ℝ)| ≤
          A * (k : ℝ) ^ (3 / 4 : ℝ)} := by
      apply measureReal_congr
      filter_upwards [identifiedSDPBusemann_eq_carrier_ae] with W hW
      simp only [hW]
    _ = _ := by
      rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0,
        map_measureReal_apply (measurable_shiftedCodePath 0) hevent]
      rfl





theorem lem_sdp_fluctuation_power_tail_identified :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∀ B : ℝ, 1 ≤ B →
      1 - C * B ^ (-(4 / 3 : ℝ)) ≤
        wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(identifiedSDPBusemann W l : ℝ)| ≤ B * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  obtain ⟨C, hC, hbound⟩ := sdp_fluctuation_power_tail_sdpCode
  refine ⟨C, hC, ?_⟩
  intro k hk B hB
  rw [identifiedSDPBusemann_fluctuation_probability]
  exact hbound k hk B hB





theorem lem_sdp_fluctuation_paper :
    ∀ delta : ℝ, 0 < delta → ∃ A0 : ℝ, 1 < A0 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ A : ℝ, A0 ≤ A →
        1 - delta ≤ wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ,
          -(k : ℤ) ≤ l → l ≤ k →
            |(identifiedSDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 4 : ℝ)} := by
  intro delta hdelta
  obtain ⟨A0, hA0, hbound⟩ := sdp_fluctuation_sdpCode delta hdelta
  refine ⟨A0, hA0, ?_⟩
  intro k hk A hA
  rw [identifiedSDPBusemann_fluctuation_probability]
  exact hbound k hk A hA

end DirectedDistances.PaperProofs.Section7
