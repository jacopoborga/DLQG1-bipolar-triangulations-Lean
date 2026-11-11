/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRepresentation4

/-! # Sample stage frontier field

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. In the sample stage drawing, a dart
borders the PL left face of another dart exactly when they lie in one
face-successor cycle. -/
theorem diskSampleRootedStageDrawing_dartBorders_leftFace_iff_sameCycle
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) //
      q.IsChanneled} × Fin ell)
    (P : StageDrawing (diskSampleCanonicalStageCode ell n hell p) n)
    (d e : StageDart
      (kmswStage (diskSampleCanonicalStageCode ell n hell p) n).nextEdge) :
    P.dartBorders e (kmswStageDrawing_leftFace P d) ↔
      Equiv.Perm.SameCycle
        ((diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.rot.symm *
          (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.edgeInv) d e := by
  let w := diskSampleCanonicalStageCode ell n hell p
  have hleft : kmswStageDrawing_leftFace P e = kmswStageDrawing_leftFace P d ↔
      P.dartBorders e (kmswStageDrawing_leftFace P d) :=
    kmswStageDrawing_leftFace_eq_iff P e (kmswStageDrawing_leftFace P d)
  rw [← hleft]
  constructor
  · intro h
    exact kmswStageDrawing_sameCycle_of_leftFace_eq P d e h.symm
  · intro h
    exact (kmswStageDrawing_leftFace_eq_of_sameCycle P d e h).symm
























































end DirectedDistances.PaperProofs.Section5

end

















