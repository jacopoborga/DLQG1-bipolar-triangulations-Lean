module

public import DirectedDistances.KMSW.M0CutData
public import DirectedDistances.KMSW.M0CutBusemann
public import DirectedDistances.PaperProofs.SourceResults.BusemannM0
public import DirectedDistances.RandomWalk.TwoSidedIIDCodeMeasure
public import DirectedDistances.KMSW.WholePlaneRotationAE
public import DirectedDistances.KMSW.WholePlaneLeftmostIncomingAmbient

public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk





theorem m0Cut_busemann_ae :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
        ∃ D : M0CutData W H,
          (∃! X : ℤ → ℤ, m0CutIsBoundaryBusemannSDP W H D.seam D.x X) ∧
          (∃! X : ℤ → ℤ, m0CutIsBoundaryBusemannLDP W H D.seam D.x X) := by
  have hprovider :
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        ∃ hfin : ∀ v : ℕ, {e : ℕ | ∃ n : ℕ,
            e < (kmswStage (shiftedStream W 0) n).nextEdge ∧
            ((kmswStage (shiftedStream W 0) n).west e = v ∨
              (kmswStage (shiftedStream W 0) n).east e = v)}.Finite,
        ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
          (∃! X : ℤ → ℤ,
            IsBoundaryBusemannSDP (boundaryPresentVertex (shiftedStream W 0) h) X) ∧
          (∃! X : ℤ → ℤ,
            IsBoundaryBusemannLDP
              (presentPathLengthsBounded_of_hfin (shiftedStream W 0) hfin)
              (boundaryPresentVertex (shiftedStream W 0) h) X) := by
    have hp := DirectedDistances.PaperProofs.SourceResults.thm_busemann
    rw [← RandomWalk.wholePlaneIIDCodeMeasure_map_shiftedPath 0] at hp
    have hp' := ae_of_ae_map
      (RandomWalk.measurable_shiftedCodePath 0).aemeasurable hp
    filter_upwards [hp'] with W hw
    simp [RandomWalk.shiftedCodePath] at hw
    rcases hw with ⟨hfin, h, _U, _, _, _, _, _, _, _, _, hsdp, hldp⟩
    exact ⟨hfin, h, hsdp, hldp⟩
  filter_upwards [hprovider, wholePlaneIID_ae_leftBoundary_leftmost_chain]
    with W hprov hleft
  obtain ⟨hfin, h, hsdp, hldp⟩ := hprov
  obtain ⟨H, hRuns⟩ := hleft
  obtain ⟨h', hLL, _⟩ := hRuns 0
  have hEq : h' = h := Subsingleton.elim _ _
  subst h'
  refine ⟨H, ?_⟩
  let D : M0CutData W H := m0CutData W H h hLL
  refine ⟨D, ?_⟩
  have hS : ∀ e, D.seam e ↔
      e ∈ wholePlaneEdgeι W 0 '' boundaryOuterEdgeSet (shiftedStream W 0) h := by
    intro e
    change m0CutSeamEdge W H e ↔ _
    exact m0Cut_seamEdge_iff W H h hLL e
  have hx : D.x = fun k =>
      wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k) := by
    funext k
    exact D.x_eq h hLL k
  have hSDP : ∃! X : ℤ → ℤ,
      m0CutIsBoundaryBusemannSDP W H D.seam D.x X := by
    rw [hx]
    exact (m0Cut_existsUnique_isBoundaryBusemannSDP_iff W H h hLL
      D.seam hS).mpr hsdp
  let hbound := presentPathLengthsBounded_of_hfin (shiftedStream W 0) hfin
  have hLDP : ∃! X : ℤ → ℤ,
      m0CutIsBoundaryBusemannLDP W H D.seam D.x X := by
    rw [hx]
    exact (m0Cut_existsUnique_isBoundaryBusemannLDP_iff W H h hLL
      D.seam hS hbound).mpr hldp
  exact ⟨hSDP, hLDP⟩

end DirectedDistances.KMSW
