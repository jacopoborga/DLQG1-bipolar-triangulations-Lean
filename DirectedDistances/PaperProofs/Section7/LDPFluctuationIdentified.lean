module

public import DirectedDistances.PaperProofs.Section7.Section7LdpUnconditional
public import DirectedDistances.PaperProofs.Section1.BusemannPaperStatement
public import DirectedDistances.Recursive.BusemannLdpUnconditional

/-! Supporting lemmas for paper labels `lem-ldp-fluctuation` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.Recursive DirectedDistances.PaperProofs.Section1





private theorem wholePlane_ae_ldp_carrier_data :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ hb : PresentPathLengthsBounded (w := shiftedStream W 0),
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        IsBoundaryBusemannLDP hb (boundaryPresentVertex _ h)
          (busemannLDPMeasurableVersion (shiftedCodePath W 0)) := by
  have hp := iidCodes_ae_boundaryBusemannLDPMeasurableVersion
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0] at hp
  have hpull := ae_of_ae_map (measurable_shiftedCodePath 0).aemeasurable hp
  filter_upwards [hpull] with W hW
  have htail : (fun i => shiftedCodePath W 0 (i + 1)) = shiftedStream W 0 := by
    funext i
    simp [shiftedCodePath]
  rw [htail] at hW
  obtain ⟨hfin, h, hX⟩ := hW
  exact ⟨presentPathLengthsBounded_of_hfin _ hfin, h, hX⟩






theorem identifiedLDP_eq_carrier_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
        (X : ℤ → ℤ),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X →
          X = busemannLDPMeasurableVersion (shiftedCodePath W 0) := by
  filter_upwards [thm_busemann_paper, wholePlane_ae_ldp_carrier_data] with W hW hc
  obtain ⟨H, h, hLL, _, _, _, _, _, _, _, _, huniq⟩ := hW
  obtain ⟨hb, h', hrep⟩ := hc
  intro H' h'' hLL' X hX
  have hr := (boundaryBusemannLDP_iff_identified W H' h'' hLL' hb
    (busemannLDPMeasurableVersion (shiftedCodePath W 0))).mp hrep
  obtain ⟨Y, hY, hu⟩ := huniq
  exact (hu X hX).trans (hu _ hr).symm






@[expose] noncomputable def identifiedLDPBusemann (W : ℤ → Fin 3) : ℤ → ℤ := by
  classical
  exact if hW : ∃ X : ℤ → ℤ, ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X
  then hW.choose else fun _ => 0





theorem identifiedLDPBusemann_eq_carrier_ae :
    identifiedLDPBusemann =ᵐ[wholePlaneIIDCodeMeasure]
      (fun W => busemannLDPMeasurableVersion (shiftedCodePath W 0)) := by
  classical
  filter_upwards [thm_busemann_paper, identifiedLDP_eq_carrier_ae] with W hW heq
  obtain ⟨H, h, hLL, _, _, _, _, _, _, _, _, X, hX, _⟩ := hW
  have hex : ∃ X : ℤ → ℤ, ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) X := ⟨X, H, h, hLL, hX⟩
  rw [identifiedLDPBusemann, dite_eq_left hex]
  obtain ⟨H', h', hLL', hX'⟩ := hex.choose_spec
  exact heq H' h' hLL' _ hX'





theorem identifiedLDPBusemann_characterization_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1))))),
        IsIdentifiedM0BusemannLDP (m0CutData W H h hLL) (identifiedLDPBusemann W) := by
  filter_upwards [wholePlane_ae_ldp_carrier_data,
    identifiedLDPBusemann_eq_carrier_ae] with W hc heq
  obtain ⟨hb, h', hrep⟩ := hc
  intro H h hLL
  rw [heq]
  exact (boundaryBusemannLDP_iff_identified W H h hLL hb _).mp hrep






theorem aemeasurable_identifiedLDPBusemann :
    AEMeasurable identifiedLDPBusemann wholePlaneIIDCodeMeasure := by
  have hm : Measurable
      (fun W => busemannLDPMeasurableVersion (shiftedCodePath W 0)) :=
    (measurable_pi_iff.mpr measurable_busemannLDPMeasurableVersion).comp
      (measurable_shiftedCodePath 0)
  exact hm.aemeasurable.congr identifiedLDPBusemann_eq_carrier_ae.symm





theorem nullMeasurableSet_identifiedLDPBusemann_fluctuation (k : ℕ) (A : ℝ) :
    NullMeasurableSet {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(identifiedLDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)}
      wholePlaneIIDCodeMeasure := by
  change NullMeasurableSet (identifiedLDPBusemann ⁻¹'
    {X : ℤ → ℤ | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(X l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)}) wholePlaneIIDCodeMeasure
  apply aemeasurable_identifiedLDPBusemann.nullMeasurableSet_preimage
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






theorem identifiedLDPBusemann_fluctuation_probability (k : ℕ) (A : ℝ) :
    wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(identifiedLDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} =
    iidCodeMeasure.real {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(busemannLDPMeasurableVersion ω l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
  have hevent : MeasurableSet {ω | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
      |(busemannLDPMeasurableVersion ω l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro l
    apply MeasurableSet.iInter
    intro _
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le
      ((measurable_of_countable (fun z : ℤ => |(z : ℝ)|)).comp
        (measurable_busemannLDPMeasurableVersion l)) measurable_const
  calc
    _ = wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
        |(busemannLDPMeasurableVersion (shiftedCodePath W 0) l : ℝ)| ≤
          A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
      apply measureReal_congr
      filter_upwards [identifiedLDPBusemann_eq_carrier_ae] with W hW
      simp only [hW]
    _ = _ := by
      rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0,
        map_measureReal_apply (measurable_shiftedCodePath 0) hevent]
      rfl






theorem lem_ldp_fluctuation_identified :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∀ A : ℝ, 1 < A →
      1 - C * A ^ (-(2 / 3 : ℝ)) ≤
        wholePlaneIIDCodeMeasure.real {W | ∀ l : ℤ, -(k : ℤ) ≤ l → l ≤ k →
          |(identifiedLDPBusemann W l : ℝ)| ≤ A * (k : ℝ) ^ (3 / 2 : ℝ)} := by
  obtain ⟨C, hC⟩ := ldp_fluctuation_ldpCode
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro k A hA
  rw [identifiedLDPBusemann_fluctuation_probability]
  have hpow : 0 ≤ A ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hmul := mul_le_mul_of_nonneg_right (le_max_left C 0) hpow
  by_cases hk : k = 0
  · subst k
    have hset : {ω | ∀ l : ℤ, -(0 : ℤ) ≤ l → l ≤ (0 : ℕ) →
        |(busemannLDPMeasurableVersion ω l : ℝ)| ≤
          A * (0 : ℝ) ^ (3 / 2 : ℝ)} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro l hl hl'
      have : l = 0 := by omega
      subst l
      simp [busemannLDPMeasurableVersion_zero]
    simp only [Nat.cast_zero] at hset ⊢
    rw [hset]
    simp only [probReal_univ]
    exact sub_le_self _ (mul_nonneg (le_max_right _ _) hpow)
  · exact (sub_le_sub_left hmul 1).trans (hC k (by omega) A hA)

end DirectedDistances.PaperProofs.Section7
