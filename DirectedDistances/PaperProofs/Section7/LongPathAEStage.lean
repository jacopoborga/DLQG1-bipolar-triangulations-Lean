module

public import DirectedDistances.PaperProofs.Section7.LongPathHinput
import DirectedDistances.KMSW.RawGeodesicAE

/-! Supporting lemmas for paper labels `lem-long-path` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory Filter DirectedDistances.KMSW DirectedDistances.RandomWalk
open Quiver DirectedDistances.Recursive





theorem lem_long_path :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ h : BoundaryHitWitnesses w,
        ∀ ell k : ℕ, 1 ≤ ell → ell < k →
          let n := boundaryHitTime w h (-(k : ℤ))
          ∃ a b : StagePresentVertex w n,
            a.id < (kmswStage w n).nextVertex ∧
            b.id < (kmswStage w n).nextVertex ∧
            ∃ q : Path a b,
              (max (busemannLDPMeasurableVersion ω (-(ell : ℤ)) -
                busemannLDPMeasurableVersion ω (-(k : ℤ))) 0).toNat ≤ q.length := by
  have hgeo : ∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∀ k : ℤ,
        ∃ P : InfinitePresentPath (fun i => ω (i + 1))
          ⟨boundaryVertex (fun i => ω (i + 1)) h k⟩, P.HasLongestSegments := by
    filter_upwards [iidCodes_ae_boundary_infinite_extremal] with ω hω
    intro h k
    exact (hω h k).1
  have hinput := longPath_hinput_of_geodesics hgeo
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
  obtain ⟨a, b, ha, hb, q, hq⟩ :=
    exists_stage_path_ge_boundaryBusemannDiff w hw
      (presentPathLengthsBounded_of_hfin w hfin)
      (busemannLDPMeasurableVersion ω) hX' ell k (by omega) hlt P hP y hy
      htail hreach hFuture
  exact ⟨a, b, ha, hb, q, hq⟩

end DirectedDistances.PaperProofs.Section7

