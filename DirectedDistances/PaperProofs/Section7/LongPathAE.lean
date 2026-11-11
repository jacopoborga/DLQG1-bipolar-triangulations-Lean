module

public import DirectedDistances.PaperProofs.Section7.LongPathAssembly
public import DirectedDistances.PaperProofs.Section7.CellLDPUpperShiftedBusemann
public import DirectedDistances.KMSW.UIBOTBoundaryShift

/-! Supporting lemmas for paper labels `lem-cell-ldp-lower`, `lem-long-path` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory Filter DirectedDistances.KMSW DirectedDistances.RandomWalk
open Quiver DirectedDistances.Recursive




theorem longPath_ae
    (hinput : ∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
      ∀ ell k : ℕ, 1 ≤ ell → ell < k →
        ∃ P : InfinitePresentPath (fun i => ω (i + 1))
          ⟨boundaryVertex (fun i => ω (i + 1)) h (-(ell : ℤ))⟩,
          P.HasLongestSegments ∧
          ∃ y : ℕ → PresentVertex (fun i => ω (i + 1)),
            Function.Injective y ∧
            (∀ T, ∃ N, ∀ r, N ≤ r →
              ∃ s, T ≤ s ∧ y r = (P.initial s).1) ∧
            (∀ r, Reachable
              (⟨boundaryVertex (fun i => ω (i + 1)) h (-(k : ℤ))⟩ :
                PresentVertex (fun i => ω (i + 1))) (y r))) :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hw : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∀ ℓ k : ℕ, 1 ≤ ℓ → ℓ < k →
          ∃ a b : StagePresentVertex (fun i => ω (i + 1))
            (boundaryHitTime (fun i => ω (i + 1)) hw (-(k : ℤ))),
            ∃ q : Path a b,
              (max (busemannLDPMeasurableVersion ω (-(ℓ : ℤ)) -
                busemannLDPMeasurableVersion ω (-(k : ℤ))) 0).toNat ≤ q.length := by
  filter_upwards [iidCodes_ae_boundaryBusemannLDPMeasurableVersion,
    iidCodes_ae_uibotBoundary_allTimes, hinput] with ω hBusemann hshift hgeom
  obtain ⟨hfin, hw, hX⟩ := hBusemann
  refine ⟨hw, fun ell k hell hlt => ?_⟩
  obtain ⟨P, hP, y, hy, htail, hreach⟩ := hgeom hw ell k hell hlt
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let n := boundaryHitTime w hw (-(k : ℤ))
  have hFuture : BoundaryHitWitnesses (fun i => w (n + i)) := by
    obtain ⟨hpackage, _, _⟩ := hshift n
    obtain ⟨_, hfuture, _⟩ := hpackage
    exact hfuture
  have hfamily : boundaryPresentVertex w hw =
      (fun i => (⟨boundaryVertex w hw i⟩ : PresentVertex w)) := by
    funext i
    rfl
  have hX' : IsBoundaryBusemannLDP
      (presentPathLengthsBounded_of_hfin w hfin)
      (fun i => (⟨boundaryVertex w hw i⟩ : PresentVertex w))
      (busemannLDPMeasurableVersion ω) := by
    rw [← hfamily]
    exact hX
  obtain ⟨a, b, _, _, q, hq⟩ :=
    exists_stage_path_ge_boundaryBusemannDiff w hw
      (presentPathLengthsBounded_of_hfin w hfin)
      (busemannLDPMeasurableVersion ω) hX' ell k (by omega) hlt P hP y hy
      htail hreach hFuture
  exact ⟨a, b, q, hq⟩

end DirectedDistances.PaperProofs.Section7
