module

public import DirectedDistances.KMSW.BusemannItemForms
public import DirectedDistances.Recursive.BusemannMeasurable
public import DirectedDistances.Recursive.BusemannSDPMeasurable

/-! # Positivity bounds for measurable Busemann versions

These helper statements transfer item-busemann-pos
representatives. The recursive use concerns the support of `g`
paper statements. The F1/F4 caveats in -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW MeasureTheory Filter
open DirectedDistances.RandomWalk

/-- The totalized LDP representative is normalized at zero for every code.
This is a pointwise helper, not a paper statement; item-busemann-pos is at
interpretation. -/
theorem busemannLDPMeasurableVersion_zero (ω : ℕ → Fin 3) :
    busemannLDPMeasurableVersion ω 0 = 0 := by
  unfold busemannLDPMeasurableVersion
  apply eventualIntValue_eq
  filter_upwards [] with j
  unfold boundaryLdpDifference
  apply eventualIntValue_eq
  filter_upwards [] with n
  simp

/-- The totalized SDP representative is normalized at zero for every code.
This is a pointwise helper, not a paper statement; item-busemann-pos is at
interpretation. -/
theorem busemannSDPMeasurableVersion_zero (ω : ℕ → Fin 3) :
    busemannSDPMeasurableVersion ω 0 = 0 := by
  unfold busemannSDPMeasurableVersion
  apply eventualIntValue_eq
  filter_upwards [] with j
  unfold boundarySdpDifference
  apply eventualIntValue_eq
  filter_upwards [] with n
  simp

/-- Almost surely the measurable LDP version has the item-busemann-pos
increment bound at every positive index. This is a helper transfer of -/
theorem iidCodes_ae_busemannLDPMeasurableVersion_item_pos :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∀ k : ℤ, 1 ≤ k →
        busemannLDPMeasurableVersion ω k -
          busemannLDPMeasurableVersion ω (k - 1) ≤ -1 := by
  filter_upwards [iidCodes_ae_busemannLDPMeasurableVersion_eq,
    iidCodes_ae_existsUnique_eq_canonicalBusemannLDP,
    item_busemann_pos_ldp] with ω hrep hdata hpos
  obtain ⟨hfin, h, X, hX, _, hcanon⟩ := hdata
  have hXrep : busemannLDPMeasurableVersion ω = X := hrep.trans hcanon.symm
  intro k hk
  simpa only [hXrep] using hpos hfin h X hX k hk

/-- Almost surely the measurable SDP version has the item-busemann-pos
increment bound at every positive index. This is a helper transfer of -/
theorem iidCodes_ae_busemannSDPMeasurableVersion_item_pos :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∀ k : ℤ, 1 ≤ k →
        -1 ≤ busemannSDPMeasurableVersion ω k -
          busemannSDPMeasurableVersion ω (k - 1) := by
  filter_upwards [iidCodes_ae_busemannSDPMeasurableVersion,
    item_busemann_pos_sdp] with ω hdata hpos
  obtain ⟨h, hX⟩ := hdata
  intro k hk
  exact hpos h (busemannSDPMeasurableVersion ω) hX k hk

/-- The LDP item-busemann-pos bound also holds almost surely for the raw
one-step shifted representative. The null-set pullback uses the
measure-preserving reset shift and its pointwise representative identity.
not a paper statement; the F1/F4 caveats in -/
theorem iidCodes_ae_busemannLDPMeasurableVersion_shift_item_pos :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∀ k : ℤ, 1 ≤ k →
        busemannLDPMeasurableVersion (fun i => ω (i + 1)) k -
          busemannLDPMeasurableVersion (fun i => ω (i + 1)) (k - 1) ≤ -1 := by
  have hshift := measurePreserving_codeShift_one.quasiMeasurePreserving.ae
    iidCodes_ae_busemannLDPMeasurableVersion_item_pos
  filter_upwards [hshift] with ω hω
  have hω' := hω
  rw [← busemannLDPMeasurableVersion_shift_eq ω] at hω'
  exact hω'

/-- The SDP item-busemann-pos bound also holds almost surely for the raw
one-step shifted representative. The null-set pullback uses the
measure-preserving reset shift and its pointwise representative identity.
not a paper statement; the F1/F4 caveats in -/
theorem iidCodes_ae_busemannSDPMeasurableVersion_shift_item_pos :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∀ k : ℤ, 1 ≤ k →
        -1 ≤ busemannSDPMeasurableVersion (fun i => ω (i + 1)) k -
          busemannSDPMeasurableVersion (fun i => ω (i + 1)) (k - 1) := by
  have hshift := measurePreserving_codeShift_one.quasiMeasurePreserving.ae
    iidCodes_ae_busemannSDPMeasurableVersion_item_pos
  filter_upwards [hshift] with ω hω
  have hω' := hω
  rw [← busemannSDPMeasurableVersion_shift_eq ω] at hω'
  exact hω'

end DirectedDistances.Recursive
