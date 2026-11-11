/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingBaseRepresentation
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRootedIso

/-! # Finite stage drawing rotation

This file makes no paper-completion claim. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. In the canonical monotone layout drawing,
the finite-stage rotation sends each dart to the counterclockwise successor
of its initial arc direction among the darts at the same stage vertex. -/
theorem kmswMonotoneLayoutDrawing_rotation_ccwSuccessor
    (w : ℕ → Fin 3) (n : ℕ) (h : LayoutGood w n)
    (d : StageDart (kmswStage w n).nextEdge) :
    CcwSuccessor {e | stageVertex w n e = stageVertex w n d}
      (fun e => ((monotoneLayoutDrawing w n h).arc e).initialDirection)
      d (stageRot w n d) := by
  change CcwSuccessor {e | stageVertex w n e = stageVertex w n d}
    (fun e => (layoutDart w n e).initialDirection) d (stageRot w n d)
  exact h.rotation_agreement d

/-- Helper toward Proposition 5.16. The stage-zero rotation order is the
counterclockwise successor order of the stage-zero arc germs. -/
theorem kmswStageZero_rotation_ccwSuccessor
    (w : ℕ → Fin 3) (d : StageDart (kmswStage w 0).nextEdge) :
    CcwSuccessor {e | stageVertex w 0 e = stageVertex w 0 d}
      (fun e => ((kmswStage0Drawing w).arc e).initialDirection)
      d (stageRot w 0 d) := by
  exact (kmswStage0Drawing w).rotation_agreement d

/-- Helper toward Proposition 5.16. Each inductive KMSW stage step supplies
the counterclockwise-successor rotation invariant for its canonical drawing. -/
theorem kmswStageSucc_rotation_ccwSuccessor
    (w : ℕ → Fin 3) (n : ℕ) {P : StageDrawing w n}
    (G : MonotoneStageInvariant w n P) :
    ∃ h : LayoutGood w (n + 1),
      ∀ d : StageDart (kmswStage w (n + 1)).nextEdge,
        CcwSuccessor
          {e | stageVertex w (n + 1) e = stageVertex w (n + 1) d}
          (fun e => ((monotoneLayoutDrawing w (n + 1) h).arc e).initialDirection)
          d (stageRot w (n + 1) d) := by
  obtain ⟨h, _⟩ := monotoneStepFrom_all w n G
  exact ⟨h, fun d => kmswMonotoneLayoutDrawing_rotation_ccwSuccessor
    w (n + 1) h d⟩

/-- Helper toward Proposition 5.16. Every finite KMSW stage has a canonical
monotone layout whose rotation is the counterclockwise successor order of its
arc germs at each vertex. -/
theorem kmswStage_rotation_ccwSuccessor_all
    (w : ℕ → Fin 3) (n : ℕ) :
    ∃ h : LayoutGood w n,
      ∀ d : StageDart (kmswStage w n).nextEdge,
        CcwSuccessor {e | stageVertex w n e = stageVertex w n d}
          (fun e => ((monotoneLayoutDrawing w n h).arc e).initialDirection)
          d (stageRot w n d) := by
  obtain ⟨h, _⟩ := monotone_family_all w n
  exact ⟨h, fun d => kmswMonotoneLayoutDrawing_rotation_ccwSuccessor w n h d⟩





























end DirectedDistances.PaperProofs.Section5

end
