/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization3
public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitIdentification2
public import DirectedDistances.PaperProofs.Section3.UIBOTPeanoStageIdentification
public import DirectedDistances.KMSW.WholePlanePastGlueDrawing
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingBaseRepresentation2

/-! # Actual finite patches in the glued whole-plane drawing

These are comparisons of the canonical finite future and past patches with
the actual glued drawing. They do not identify a centered finite-word ball.
The finite drawings have proved exterior faces; no StageGeom is used. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open WholePlanePastGlueData Set unitInterval

/-- Helper toward Proposition 3.9: the canonical monotone finite drawing
has the exterior-face certificate needed for the StageGeom-free domain. -/
theorem uibotCanonicalStage_exterior (w : ℕ → Fin 3) (n : ℕ) :
    let P := familyQ w (monotone_family_all w) n
    ∃ U : P.Face, P.IsUnbounded U ∧
      (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d := by
  obtain ⟨_, U, _, hU, huniq, hborder⟩ :=
    (familyG w (monotone_family_all w) n).face_partition
  exact ⟨U, hU, huniq, hborder⟩

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
local notation "Qf" => familyQ (shiftedStream W 0) (monotone_family_all (shiftedStream W 0))
local notation "Qp" => familyQ (kmswPastCode W) (monotone_family_all (kmswPastCode W))
local notation "T" => PastDrawingTransfer.transfer (shiftedStream W 0) (kmswPastCode W)
  h0 hpast ((And.left H) 0) (past_finiteIncidence W H)

/-- Helper toward Proposition 3.9: every allocated future-stage vertex
has exactly its original position in the glued whole-plane drawing. -/
theorem uibotGlued_futureStage_pos (n : ℕ)
    (v : Fin (kmswStage (shiftedStream W 0) n).nextVertex) :
    (G).pos (wholePlaneVertexι W 0 v.val) = (Qf n).pos v := by
  change gluedPos W h0 hpast H _ = _
  rw [gluedPos_runZero]
  exact familyDrawing_pos _ _ _ n v

/-- Helper toward Proposition 3.9: future-stage dart polylines, including
seam darts and their parameter schedules, are retained exactly. -/
theorem uibotGlued_futureStage_arc (n : ℕ)
    (d : StageDart (kmswStage (shiftedStream W 0) n).nextEdge) :
    (G).arc (wholePlaneDartι W 0 (d.1.val, d.2)) = (Qf n).arc d := by
  change gluedArc W h0 hpast H _ = _
  rw [gluedArc_runZero]
  exact familyDrawing_arc _ _ _ n d

/-- Helper toward Proposition 3.9: one orientation-preserving ambient
homeomorphism and increasing interval parameters simultaneously compare all
vertices and darts in each canonical future patch. -/
theorem uibotGlued_futureStage_geometry (n : ℕ) :
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ v : Fin (kmswStage (shiftedStream W 0) n).nextVertex,
        h ((Qf n).pos v) = (G).pos (wholePlaneVertexι W 0 v.val)) ∧
      ∀ d : StageDart (kmswStage (shiftedStream W 0) n).nextEdge,
        ∃ φ : I ≃ₜ I, StrictMono φ ∧ φ 0 = 0 ∧ φ 1 = 1 ∧
          ∀ t, h (((Qf n).arc d).toPath t) =
            ((G).arc (wholePlaneDartι W 0 (d.1.val, d.2))).toPath (φ t) := by
  refine ⟨Homeomorph.refl ℂ, orientationPreserving_refl, ?_, ?_⟩
  · intro v
    exact (uibotGlued_futureStage_pos W h0 hpast H n v).symm
  · intro d
    refine ⟨Homeomorph.refl I, strictMono_id, rfl, rfl, ?_⟩
    intro t
    rw [uibotGlued_futureStage_arc]
    rfl

/-- Helper toward Proposition 3.9: every allocated past-stage vertex is
carried to its actual glued position by the single explicit past transfer. -/
theorem uibotGlued_pastStage_pos (n : ℕ)
    (v : Fin (kmswStage (kmswPastCode W) n).nextVertex) :
    (G).pos (kmswPastVertex W v.val) = T ((Qp n).pos v) := by
  change gluedPos W h0 hpast H _ = _
  rw [gluedPos_past]
  exact congrArg T (familyDrawing_pos (kmswPastCode W) (past_finiteIncidence W H)
    (monotone_family_all (kmswPastCode W)) n v)

/-- Helper toward Proposition 3.9: off the seam the past transfer carries
each complete finite-stage arc image to the actual glued arc image. -/
theorem uibotGlued_pastStage_arc_image (n : ℕ)
    (d : StageDart (kmswStage (kmswPastCode W) n).nextEdge)
    (hd : ¬ kmswPastSeamEdge W d.1.val) :
    ((G).arc (kmswPastDart W (d.1.val, d.2))).image = T '' ((Qp n).arc d).image := by
  change (gluedArc W h0 hpast H _).image = _
  rw [gluedArc_past W h0 hpast H _ hd, (pastDrawing_arc W h0 hpast H _).1]
  exact congrArg (fun p : Polyline => T '' p.image)
    (familyDrawing_arc (kmswPastCode W) (past_finiteIncidence W H)
      (monotone_family_all (kmswPastCode W)) n d)

/-- Helper toward Proposition 3.9: each canonical future cap is the same
original open face before and after whole-plane gluing. -/
theorem uibotGlued_futureStage_cap_face (n : ℕ)
    (i : Fin (kmswStage (shiftedStream W 0) n).triangles.length) :
    ∃ F : (Qf n).Face, ∃ F' : (G).Face,
      F.val = ((familyG _ (monotone_family_all _) n).cap i).region ∧ F'.val = F.val := by
  let w := shiftedStream W 0
  let hf := monotone_family_all w
  obtain ⟨F, hF⟩ := (familyG w hf n).face_partition.1 i
  obtain ⟨L, hL, hbounded⟩ := monotoneLimit_cap_faces w (H.1 0)
    (familyQ w hf) (familyG w hf) (monotoneFamilyDrawing w (H.1 0) hf)
    (familyDrawing_pos w (H.1 0) hf) (familyDrawing_arc w (H.1 0) hf)
    (family_cap_persistence w hf) n i
  have hLu : ¬ (monotoneFamilyDrawing w (H.1 0) hf).IsUnbounded L := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbounded
    intro hu
    obtain ⟨z, hz, hlt⟩ := hu R
    exact hlt.not_ge (hR z hz)
  obtain ⟨z, _, hz, hc⟩ :=
    WholePlanePastGlueFacesUpper.glued_component_of_boundedFace W h0 hpast H L hLu
  refine ⟨F, ⟨L.val, z, hz, hc.symm⟩, hF, ?_⟩
  exact hL.trans hF.symm

/-- Helper toward Proposition 3.9: each canonical past cap is an original
whole-plane face after applying the explicit past transfer. -/
theorem uibotGlued_pastStage_cap_face (n : ℕ)
    (i : Fin (kmswStage (kmswPastCode W) n).triangles.length) :
    ∃ F : (Qp n).Face, ∃ F' : (G).Face,
      F.val = ((familyG _ (monotone_family_all _) n).cap i).region ∧
        F'.val = T '' F.val := by
  let w := kmswPastCode W
  let hf := monotone_family_all w
  let hfin := past_finiteIncidence W H
  obtain ⟨F, hF⟩ := (familyG w hf n).face_partition.1 i
  obtain ⟨L, hL, hbounded⟩ := monotoneLimit_cap_faces w hfin
    (familyQ w hf) (familyG w hf) (monotoneFamilyDrawing w hfin hf)
    (familyDrawing_pos w hfin hf) (familyDrawing_arc w hfin hf)
    (family_cap_persistence w hf) n i
  have hLu : ¬ (monotoneFamilyDrawing w hfin hf).IsUnbounded L := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbounded
    intro hu
    obtain ⟨z, hz, hlt⟩ := hu R
    exact hlt.not_ge (hR z hz)
  obtain ⟨z, _, hz, hc⟩ :=
    WholePlanePastGlueFacesLower.glued_component_of_past_boundedFace W h0 hpast H L hLu
  refine ⟨F, ⟨T '' L.val, z, hz, hc.symm⟩, hF, ?_⟩
  exact congrArg (fun s : Set ℂ => T '' s) (hL.trans hF.symm)

end DirectedDistances.PaperProofs.Section3
end
