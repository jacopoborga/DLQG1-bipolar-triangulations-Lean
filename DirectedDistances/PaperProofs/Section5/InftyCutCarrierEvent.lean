module

public import DirectedDistances.PaperProofs.SourceResults.BusemannM0
public import DirectedDistances.KMSW.InftyCutSequence

/-! Helper toward Lemma 5.3 (lem-infty-cut); not a paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Quiver DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk

/-- Helper toward Lemma 5.3 (lem-infty-cut); not a paper result.
The external-face realization, carrier boundary identification, and cut sequence
hold on one iid-code event with the same boundary-hit witness. -/
theorem iidCodes_ae_lem_infty_cut_carrier :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ hfin : ∀ v : ℕ, {e : ℕ | ∃ n : ℕ,
          e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses w,
        let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
        (∃ U : P.Face,
          P.IsUnbounded U ∧
          (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
          (∀ d : ℕ × Bool,
            P.dartBorders d U ↔ ∃ k : ℤ, d = futureMapBoundaryDart w h k) ∧
          {v : ℕ | ∃ d : ℕ × Bool,
            P.dartBorders d U ∧ kmswLimitDartVertex w d = v} =
              Set.range (boundaryVertex w h) ∧
          (∀ k : ℤ,
            kmswInfFaceSucc w hfin (futureMapBoundaryDart w h k) =
              futureMapBoundaryDart w h (k - 1))) ∧
        (∀ k : ℤ,
          futureMapVertexEquiv w hfin
            (rootedLocallyFiniteVertexClass (kmswInfRot w hfin)
              (futureMapBoundaryDart w h (k - 1))) =
                boundaryPresentVertex w h k) ∧
        (∀ k k' : ℤ, k < k' →
          ∃ v : ℕ → PresentVertex w,
            Function.Injective v ∧
            ∀ ℓ : ℤ, ℓ ∈ Set.Icc k k' →
              ∀ y : ℕ → PresentVertex w,
                Function.Injective y →
                (∀ j, Reachable (boundaryPresentVertex w h ℓ) (y j)) →
                ∀ m, ∃ J, ∀ j, J ≤ j → ∀ p : Path
                  (boundaryPresentVertex w h ℓ) (y j),
                  List.Mem (v m)
                    (Quiver.Path.vertices (V := PresentVertex w) p)) := by
  filter_upwards [DirectedDistances.PaperProofs.SourceResults.thm_busemann,
    DirectedDistances.KMSW.ae_lem_infty_cut_sequence] with ω hgeo hcut
  rcases hgeo with
    ⟨hfin, h, U, hU, huniq, hborder, hvertices, hsucc, hcarrier, _, _, _, _⟩
  rcases hcut with ⟨hcut, hseq⟩
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  have hh : h = hcut := Subsingleton.elim _ _
  subst hcut
  refine ⟨hfin, h,
    ⟨⟨U, hU, huniq, hborder, hvertices, hsucc⟩, hcarrier, ?_⟩⟩
  simpa [boundaryPresentVertex] using hseq

end DirectedDistances.PaperProofs.Section5
