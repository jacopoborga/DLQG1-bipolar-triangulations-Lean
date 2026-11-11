module

public import DirectedDistances.KMSW.BusemannItemForms
public import DirectedDistances.Recursive.BusemannMeasurable
public import DirectedDistances.Recursive.BusemannSDPMeasurable
public import DirectedDistances.Recursive.LDPMasterFromLaw
public import DirectedDistances.Recursive.SDPMasterFromLaw

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk MeasureTheory



theorem ldp_measurable_increment_bound :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ k : ℤ, 1 ≤ k →
      ldpIncrement busemannLDPMeasurableVersion k ω ≤ -1 := by
  filter_upwards [item_busemann_pos_ldp,
    iidCodes_ae_existsUnique_eq_canonicalBusemannLDP,
    iidCodes_ae_busemannLDPMeasurableVersion_eq] with ω hpos hdata hversion
  obtain ⟨hfin, h, X, hX, _, hcanonical⟩ := hdata
  have hversionX : busemannLDPMeasurableVersion ω = X :=
    hversion.trans hcanonical.symm
  have hbound := hpos hfin h X hX
  intro k hk
  change busemannLDPMeasurableVersion ω k -
    busemannLDPMeasurableVersion ω (k - 1) ≤ -1
  rw [hversionX]
  exact hbound k hk



theorem sdp_measurable_increment_bound :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ k : ℤ, 1 ≤ k →
      -1 ≤ SDPMasterFromLaw.increment busemannSDPMeasurableVersion k ω := by
  filter_upwards [item_busemann_pos_sdp,
    iidCodes_ae_busemannSDPMeasurableVersion] with ω hpos hdata
  obtain ⟨h, hX⟩ := hdata
  have hbound := hpos h (busemannSDPMeasurableVersion ω) hX
  intro k hk
  change -1 ≤ busemannSDPMeasurableVersion ω k -
    busemannSDPMeasurableVersion ω (k - 1)
  exact hbound k hk

end DirectedDistances.Recursive
