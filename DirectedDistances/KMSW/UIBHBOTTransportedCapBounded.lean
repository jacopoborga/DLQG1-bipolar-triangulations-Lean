/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBHBOTGlueDrawingAssembly
public import DirectedDistances.KMSW.MonotoneFamilyCapBounded
import Mathlib.Topology.MetricSpace.Bounded

/-! # Bounded transported creation caps for the UIBHBOT assembly

Helper toward Definition 5.8
The future and attached past cap images are bounded. The hypotheses below are
the corresponding witnesses supplied to `uibhbotCcw_assemblyDrawing`; no past
right-boundary hit witness is needed. Identifying these sets with faces of the
assembled drawing is a separate obligation. -/

public section

namespace DirectedDistances.KMSW

open Set DirectedDistances.PaperProofs.Section5

/-- Helper toward Definition 5.8: a continuous plane map takes a bounded set
to a bounded set, by compactness of its closure in the plane. -/
theorem isBounded_image_of_continuous_complex {S : Set ℂ} {T : ℂ → ℂ}
    (hS : Bornology.IsBounded S) (hT : Continuous T) :
    Bornology.IsBounded (T '' S) := by
  exact (hS.isCompact_closure.image hT).isBounded.subset
    (Set.image_mono subset_closure)

/-- Helper toward Definition 5.8: the half-turn used to attach the past is
continuous on the entire plane. -/
theorem continuous_uibhbotAssemblyHalfTurn : Continuous uibhbotAssemblyHalfTurn :=
  continuous_id.neg.sub continuous_const

section Future

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))

local notation "w0" => shiftedStream W 0
local notation "Tf" => uibhbotGlueFutureTransfer w0 h0 ((And.left H) 0)
local notation "C0" => fun j : TriangleCreationTime w0 =>
  Tf '' Subtype.val (capFace w0 ((And.left H) 0) j)

/-- Helper toward Definition 5.8: every future creation cap remains bounded
under the future transfer used by the assembly. -/
theorem uibhbot_future_transported_cap_bounded :
    ∀ j : TriangleCreationTime w0, Bornology.IsBounded (C0 j) := by
  intro j
  exact isBounded_image_of_continuous_complex (capFace_bounded w0 (H.1 0) j)
    (Homeomorph.continuous Tf)

end Future

section Past

variable (W : ℤ → Fin 3)
  (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
  (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
  (hfin : KMSWFiniteIncidence (kmswPastCode W))

local notation "wp" => kmswPastCode W
local notation "Tp" => uibhbotPastStraightTransfer W hL hR
local notation "A" => uibhbotAssemblyHalfTurn
local notation "Cp" => fun j : TriangleCreationTime wp =>
  A '' (Tp '' Subtype.val (capFace wp hfin j))

/-- Helper toward Definition 5.8: every past creation cap remains bounded
under the past transfer followed by the assembly's half-turn. -/
theorem uibhbot_past_transported_cap_bounded :
    ∀ j : TriangleCreationTime wp, Bornology.IsBounded (Cp j) := by
  intro j
  apply isBounded_image_of_continuous_complex
    (isBounded_image_of_continuous_complex (capFace_bounded wp hfin j)
      (Homeomorph.continuous Tp))
    continuous_uibhbotAssemblyHalfTurn

end Past

end DirectedDistances.KMSW
