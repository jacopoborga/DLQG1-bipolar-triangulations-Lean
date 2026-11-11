/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass3
public import DirectedDistances.PaperProofs.Section5.FacedDiskWindowCompare
public import DirectedDistances.PaperProofs.Section5.Prop516D39DiskBall
public import DirectedDistances.PaperProofs.Section5.Prop516D39SourceBallLaw

/-! # Finite-window determination of canonical Definition 3.8 balls

Helpers toward Definition 3.8. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Definition 3.8: the finite stage faced/framed ball built
from the shifted code window depends only on the code on `[-N,N]`. -/
theorem facedUIBHBOTWindowStageBallClass_eq_of_codeWindow
    (N r : ℕ) (W W' : ℤ → Fin 3)
    (hwindow : ∀ i : ℤ, i ∈ Set.Icc (-(N : ℤ)) (N : ℤ) → W' i = W i) :
    facedUIBHBOTWindowStageBallClass N r (shiftedStream W N) =
      facedUIBHBOTWindowStageBallClass N r (shiftedStream W' N) := by
  apply facedUIBHBOTWindowStageBallClass_eq_prefix
  intro i hi
  have hlo : -(N : ℤ) ≤ (i : ℤ) - N := by omega
  have hhi : (i : ℤ) - N ≤ (N : ℤ) := by omega
  exact (hwindow ((i : ℤ) - N) ⟨hlo, hhi⟩).symm

/-- Helper toward Definition 3.8: under the whole-plane rotation hypotheses
`H` and `H'` (finite-incidence and eventual-freshness conditions), if both
codes have certified captures at the same radius and symmetric window, their
faced/framed combinatorial ball classes agree whenever the code windows agree. -/
theorem facedUIBHBOTBallClassRel_eq_of_codeWindow_and_captures
    (r N : ℕ) (hr : 0 < r) (W W' : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis W')
    (hcap : ∃ c, uibhbotFixedCaptureRel W r N (2 * N) c
      (kmswLLCreatedEdge (shiftedStream W N) N) true)
    (hcap' : ∃ c, uibhbotFixedCaptureRel W' r N (2 * N) c
      (kmswLLCreatedEdge (shiftedStream W' N) N) true)
    (hwindow : ∀ i : ℤ, i ∈ Set.Icc (-(N : ℤ)) (N : ℤ) → W' i = W i) :
    facedUIBHBOTBallClassRel W r hr = facedUIBHBOTBallClassRel W' r hr := by
  rw [facedUIBHBOTBallClassRel_eq_windowStageClass W H N r hr hcap,
    facedUIBHBOTBallClassRel_eq_windowStageClass W' H' N r hr hcap']
  exact facedUIBHBOTWindowStageBallClass_eq_of_codeWindow N r W W' hwindow

/-- Helper toward Definition 3.8: equality of the faced/framed balls gives
equality of the corresponding combinatorial local topology ball classes. -/
theorem d39BallClass_eq_of_rootedLocallyFiniteFacedBallClass_eq
    (M N : RootedLocallyFinitePlanarMap) (r : ℕ)
    (h : rootedLocallyFiniteFacedBallClass r M =
      rootedLocallyFiniteFacedBallClass r N) :
    d39BallClass M.toRootedLocallyFiniteMap.toD39RootedMap (r + 1)
        (Nat.succ_pos r) =
      d39BallClass N.toRootedLocallyFiniteMap.toD39RootedMap (r + 1)
        (Nat.succ_pos r) := by
  rw [d39BallClass_eq_facedFramedBallClassToD39BallClass M r,
    d39BallClass_eq_facedFramedBallClassToD39BallClass N r]
  exact congrArg facedFramedBallClassToD39BallClass h










































end DirectedDistances.PaperProofs.Section5

end
