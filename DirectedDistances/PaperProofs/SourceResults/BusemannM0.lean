module

public import DirectedDistances.KMSW.TwoSidedDrawingFaceClassification
public import DirectedDistances.KMSW.KMSWFutureMapDistance
public import DirectedDistances.PaperProofs.Section1.BusemannFutureMapCommonEvent

/-! Isolated proof provider for Theorem 1.4 (thm-busemann); packaging only. -/

public section
namespace DirectedDistances.PaperProofs.SourceResults

open MeasureTheory Filter DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- packaging only. -/
theorem thm_busemann :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w : ℕ → Fin 3 := fun i => ω (i + 1)
      ∃ hfin : ∀ v : ℕ, {e : ℕ | ∃ n : ℕ,
          e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses w,
        let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
        ∃ U : P.Face,
          P.IsUnbounded U ∧
          (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
          (∀ d : ℕ × Bool,
            P.dartBorders d U ↔ ∃ k : ℤ, d = futureMapBoundaryDart w h k) ∧
          {v : ℕ | ∃ d : ℕ × Bool,
            P.dartBorders d U ∧ kmswLimitDartVertex w d = v} =
              Set.range (boundaryVertex w h) ∧
          (∀ k : ℤ,
            kmswInfFaceSucc w hfin (futureMapBoundaryDart w h k) =
              futureMapBoundaryDart w h (k - 1)) ∧
          (∀ k : ℤ,
            futureMapVertexEquiv w hfin
              (rootedLocallyFiniteVertexClass (kmswInfRot w hfin)
                (futureMapBoundaryDart w h (k - 1))) =
              boundaryPresentVertex w h k) ∧
          (∀ u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin),
            futureMapCarrierSDP w hfin u v =
              sdp (futureMapVertexEquiv w hfin u) (futureMapVertexEquiv w hfin v)) ∧
          (∀ u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin),
            futureMapCarrierLDP w hfin u v =
              presentLdp (futureMapVertexEquiv w hfin u) (futureMapVertexEquiv w hfin v)) ∧
          (∃! X : ℤ → ℤ,
            IsBoundaryBusemannSDP (boundaryPresentVertex w h) X) ∧
          (∃! X : ℤ → ℤ,
            IsBoundaryBusemannLDP
              (presentPathLengthsBounded_of_hfin w hfin)
              (boundaryPresentVertex w h) X) := by
  filter_upwards [Section1.iidCodes_ae_boundaryBusemann_futureMap_common] with ω hω
  obtain ⟨hfin, h, hLDP, hSDP, hvertex, hsucc⟩ := hω
  obtain ⟨U, hU, huniq, _, hlabel, hvertices, _⟩ :=
    monotoneFamilyDrawing_realized_boundary_twoSided (fun i => ω (i + 1)) hfin h
  refine ⟨hfin, h, U, hU, huniq, hlabel, hvertices, hsucc, hvertex, ?_, ?_, hSDP, hLDP⟩
  · exact fun u v => futureMapCarrierSDP_eq_present (fun i => ω (i + 1)) hfin u v
  · exact fun u v => futureMapCarrierLDP_eq_present (fun i => ω (i + 1)) hfin u v

end DirectedDistances.PaperProofs.SourceResults
