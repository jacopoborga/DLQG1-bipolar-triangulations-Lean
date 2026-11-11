/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization19

/-! # The exact finite-stage to whole-plane comparison

This exports the proved deterministic comparison with all its binders visible.
with the sole coordinator. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5

/-- Helper toward Proposition 3.9: the exact DC conclusion for the actual
finite exterior map and an arbitrary whole-plane drawing, with every binder
of `UIBOTDeterministicComparison` and all geometric ball-isomorphism fields. -/
theorem uibotFiniteStageExterior_wholePlane_ballIso
    (n N r : ℕ) (hr : 0 < r)
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    Nonempty (D39GeomBallIsoV2 r
      (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega))
      (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G)) :=
  uibotDeterministicComparison_proved n N r hr w j W H G hp P U hU hborder hwindow hcap

end DirectedDistances.PaperProofs.Section3

end
