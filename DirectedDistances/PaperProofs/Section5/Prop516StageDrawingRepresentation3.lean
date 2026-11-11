/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRepresentation2

/-! # Finite stage drawing representation continuation

This file makes no paper-completion claim. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW

/-- Helper toward Proposition 5.16. Every finite KMSW stage has a drawing
with its unique unbounded face and the exact outer-dart boundary criterion.
This extracts the stage drawing and boundary data proved by
`kmswStageGeometry_induction_all`; it does not assert a `StageGeom` cell
certificate. -/
theorem kmswStageDrawing_exists_withUniqueOuterFace (w : ℕ → Fin 3) (n : ℕ) :
    ∃ P : StageDrawing w n, ∃ U : P.Face,
      P.IsUnbounded U ∧
      (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      ∀ d, P.dartBorders d U ↔
        (d.2 = false ∧
            d.1.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR) ∨
          (d.2 = true ∧
            d.1.val ∈ (kmswStage w n).LL ++ (kmswStage w n).LR) := by
  obtain ⟨Q, _, _, hfaces, _, _⟩ := kmswStageGeometry_induction_all w
  obtain ⟨U, hU, hunique, hborder⟩ := hfaces n
  exact ⟨Q n, U, hU, hunique, hborder⟩

/- The remaining StageGeom existence target, with its full binders, is

    ∀ (w : ℕ → Fin 3) (n : ℕ),
      ∃ P : StageDrawing w n, Nonempty (StageGeom w n P)

Three construction routes were checked. First, from
`MonotoneStageInvariant.stageGeom_cap_data`, the monotone cap regions give
open bounded cells, their edge frontiers, and an unbounded exterior; this
does not produce the noncollinear triangle coordinates and active/left
`StageExteriorSector` certificates required by `StageGeom`. Second,
`kmswStageGeometry_induction_all` supplies the finite drawings, their unique
unbounded faces, and the missing-LL/outer-word information (the preceding
theorem extracts its boundary clause), but its induction invariant has no
`StageGeom` conclusion or step constructing those triangle-sector fields.
Third, `WholePlaneDrawingGluing` glues compatible run drawings into a
whole-plane drawing; its output is not a finite `StageDrawing w n` with the
specified triangle cellulation. These do not establish the displayed target. -/

































































end DirectedDistances.PaperProofs.Section5

end
