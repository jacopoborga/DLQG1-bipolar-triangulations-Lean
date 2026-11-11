/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRepresentation
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingBaseRepresentation4
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingFrontierIncidence2
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRotation

/-! # Finite sample stage representation continuation

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. The stage domain map agrees with the
exterior-face construction using the certificate's designated exterior face. -/
theorem kmswStageDrawingDomainRootedMap_eq_of_exteriorFace
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (G : StageGeom w n P) :
    kmswStageDrawingDomainRootedMap P G =
      kmswStageDrawingDomainRootedMapOfExteriorFace P G.exteriorFace
        G.exteriorFace_unbounded G.dartBorders_iff := by
  rfl





























































end DirectedDistances.PaperProofs.Section5

end
