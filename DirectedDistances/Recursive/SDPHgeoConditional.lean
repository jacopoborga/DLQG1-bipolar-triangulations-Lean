module

public import DirectedDistances.Recursive.SDPIdentifyBusemann
public import DirectedDistances.Recursive.KappaHgeoTransfer
public import DirectedDistances.Recursive.MeasurableVersionPos
public import DirectedDistances.Recursive.BusemannSDPMeasurable











public section

namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.Recursive.SDPExpansion

/-- One constant works for every `k ≥ 1`. This bound needs no increment-law
hypotheses; the three open item hypotheses are used by `sdp_hgeo_of_items`.
It is an input to the `κ > 0` exclusion, not a paper statement; F1/F4 apply. -/
theorem sdp_measurableVersion_linear_bound :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ, 1 ≤ k →
      1 - δ ≤ iidCodeMeasure.real
        {ω | (busemannSDPMeasurableVersion ω (-(k : ℤ)) : ℝ) ≤
          2 * A * (k : ℝ) + 1} := by
  intro δ hδ
  obtain ⟨A, _, hA⟩ := iidCodes_ae_boundaryBusemannSDP_linear_bound δ hδ
  refine ⟨A, fun k hk => ?_⟩
  let E : Set (ℕ → Fin 3) :=
    {ω | ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
      ∀ X : ℤ → ℤ,
        IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => ω (i + 1)) h) X →
          (X (-(k : ℤ)) : ℝ) ≤ 2 * A * (k : ℝ) + 1}
  let G : Set (ℕ → Fin 3) :=
    {ω | ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
      IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => ω (i + 1)) h)
        (busemannSDPMeasurableVersion ω)}
  have hcongr : E ∩ G =ᵐ[iidCodeMeasure] E := by
    filter_upwards [iidCodes_ae_busemannSDPMeasurableVersion] with ω hω
    exact propext ⟨fun he => he.1, fun he => ⟨he, hω⟩⟩
  have hsubset : E ∩ G ⊆
      {ω | (busemannSDPMeasurableVersion ω (-(k : ℤ)) : ℝ) ≤
        2 * A * (k : ℝ) + 1} := by
    intro ω hω
    obtain ⟨⟨h, hAll⟩, ⟨h', hY⟩⟩ := hω
    -- Hit witnesses are proofs of a proposition, hence agree by proof irrelevance.
    exact hAll (busemannSDPMeasurableVersion ω) hY
  calc
    1 - δ ≤ iidCodeMeasure.real E := hA k hk
    _ = iidCodeMeasure.real (E ∩ G) := (measureReal_congr hcongr).symm
    _ ≤ iidCodeMeasure.real
        {ω | (busemannSDPMeasurableVersion ω (-(k : ℤ)) : ℝ) ≤
          2 * A * (k : ℝ) + 1} := measureReal_mono hsubset

/-- CONDITIONAL helper supplying exactly the canonical iid `hgeo` input for
`eqn-sdp-identify-bound`). The law forms of the three items `ind`,
`stationary`, and `sym` of `thm-busemann-property` are open and assumed here.
This is not a paper statement, and the F1/F4 caveats remain in force. -/
theorem sdp_hgeo_of_items
    (hind : iIndepFun (KappaHgeoTransfer.increment busemannSDPMeasurableVersion)
      iidCodeMeasure)
    (hstatL : ∀ k ≤ 0,
      iidCodeMeasure.map (KappaHgeoTransfer.increment busemannSDPMeasurableVersion k) =
        iidCodeMeasure.map (KappaHgeoTransfer.increment busemannSDPMeasurableVersion 0))
    (hsym :
      iidCodeMeasure.map (KappaHgeoTransfer.increment busemannSDPMeasurableVersion 0) =
        iidCodeMeasure.map
          (fun ω => -KappaHgeoTransfer.increment busemannSDPMeasurableVersion 0 ω)) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, ∀ k : ℕ,
      1 - δ ≤
        (Measure.infinitePi (fun _ : ℕ => mu_f
          (KappaHgeoTransfer.incrementMass iidCodeMeasure
            busemannSDPMeasurableVersion))).real
          {ω : ℕ → ℝ | ∑ i ∈ Finset.range k, ω i ≤ 2 * A * (k : ℝ) + 1} := by
  exact KappaHgeoTransfer.hgeo_of_linear_bound iidCodeMeasure
    busemannSDPMeasurableVersion measurable_busemannSDPMeasurableVersion
    busemannSDPMeasurableVersion_zero hind hstatL hsym sdp_measurableVersion_linear_bound

/-- literal SDP time-zero increment mass. This definitional identity proves none
of the three open item hypotheses. It supports the `κ > 0` exclusion input,
is not a paper statement, and retains the F1/F4 caveats. -/
theorem sdp_incrementMass_eq (x : ℤ) :
    KappaHgeoTransfer.incrementMass iidCodeMeasure busemannSDPMeasurableVersion x =
      iidCodeMeasure.real
        {ω | busemannSDPMeasurableVersion ω 0 -
          busemannSDPMeasurableVersion ω (-1) = x} := by
  rfl

end DirectedDistances.Recursive
