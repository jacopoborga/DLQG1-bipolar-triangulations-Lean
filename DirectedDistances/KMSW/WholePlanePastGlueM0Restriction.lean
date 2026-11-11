/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.WholePlaneM0Drawing
public import DirectedDistances.KMSW.WholePlanePastGlueFacesUpper

public section

namespace DirectedDistances.KMSW.WholePlanePastGlueM0Restriction

open DirectedDistances.PlanarMap Set WholePlanePastGlueData
open WholePlanePastGlueGeometry

noncomputable section

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "w0" => shiftedStream W 0
local notation "wp" => kmswPastCode W
local notation "P0" => monotoneFamilyDrawing w0 ((And.left H) 0)
  (monotone_family_all w0)
local notation "Pp" => monotoneFamilyDrawing wp (past_finiteIncidence W H)
  (monotone_family_all wp)
local notation "T" => PastDrawingTransfer.transfer w0 wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)
local notation "f0" => seamFun w0 h0 ((And.left H) 0)
local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h0 hp H
local notation "Upper" => Set.ofPred (fun z : ℂ => f0 (Complex.re z) < Complex.im z)
local notation "closedUpper" =>
  Set.ofPred (fun z : ℂ => f0 (Complex.re z) ≤ Complex.im z)
local notation "Lower" => Set.ofPred (fun z : ℂ => Complex.im z < f0 (Complex.re z))




theorem restrict_pos (v : ℕ) :
    (G).pos (wholePlaneVertexι W 0 v) = (P0).pos v := by
  rw [WholePlanePastGlueDrawing.glueDrawing_pos]
  exact gluedPos_runZero W h0 hp H v




theorem restrict_arc (d : ℕ × Bool) :
    (G).arc (wholePlaneDartι W 0 d) = (P0).arc d := by
  rw [WholePlanePastGlueDrawing.glueDrawing_arc]
  exact gluedArc_runZero W h0 hp H d




theorem bounded_face_is_glued_face (F0 : (P0).Face)
    (hF0 : ¬ (P0).IsUnbounded F0) :
    ∃ F : (G).Face, F.val = F0.val := by
  obtain ⟨z, hzF, hzG, hcomp⟩ :=
    WholePlanePastGlueFacesUpper.glued_component_of_boundedFace
      W h0 hp H F0 hF0
  have hzImage : z ∉ (G).image := by
    rw [WholePlanePastGlueDrawing.glueDrawing_image]
    exact hzG
  let F : (G).Face := ⟨connectedComponentIn (G).imageᶜ z, z, hzImage, rfl⟩
  have hval : F.val = F0.val := by
    change connectedComponentIn (G).imageᶜ z = F0.val
    rw [WholePlanePastGlueDrawing.glueDrawing_image]
    exact hcomp
  exact ⟨F, hval⟩




theorem m0_restriction :
    Function.Injective (wholePlaneVertexι W 0) ∧
    Function.Injective (wholePlaneDartι W 0) ∧
    (∀ V : WholePlaneVertex W,
      (G).pos V ∈ closedUpper ↔ V ∈ Set.range (wholePlaneVertexι W 0)) ∧
    (∀ D : WholePlaneDart W,
      ((G).arc D).image ⊆ closedUpper ↔
        D ∈ Set.range (wholePlaneDartι W 0)) ∧
    (∀ v : ℕ, (G).pos (wholePlaneVertexι W 0 v) = (P0).pos v) ∧
    (∀ d : ℕ × Bool, (G).arc (wholePlaneDartι W 0 d) = (P0).arc d) ∧
    (∀ F : (G).Face,
      F.val ⊆ Upper ↔
        ∃ F0 : (P0).Face, ¬ (P0).IsUnbounded F0 ∧ F.val = F0.val) ∧
    (∀ F0 : (P0).Face, ¬ (P0).IsUnbounded F0 →
      ∃ F : (G).Face, F.val = F0.val) ∧
    (∀ F0 : (P0).Face,
      (P0).IsUnbounded F0 ↔ F0.val = {z : ℂ | z.im < f0 z.re}) ∧
    Lower = {z : ℂ | z.im < f0 z.re} := by
  have hdart : Function.Injective (wholePlaneDartι W 0) := by
    intro d e h
    rcases d with ⟨d, b⟩
    rcases e with ⟨e, c⟩
    change (wholePlaneEdgeι W 0 d, b) = (wholePlaneEdgeι W 0 e, c) at h
    have he := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    have hde := wholePlaneEdgeι_injective W 0 he
    cases hde
    cases hb
    rfl
  refine ⟨wholePlaneVertexι_injective W 0, hdart, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro V
    exact WholePlaneM0Drawing.m0_vertex_iff W h0 hp H V
  · intro D
    exact WholePlaneM0Drawing.m0_dart_iff W h0 hp H D
  · intro v
    exact restrict_pos W h0 hp H v
  · intro d
    exact restrict_arc W h0 hp H d
  · intro F
    exact WholePlaneM0Drawing.m0_face_iff W h0 hp H F
  · intro F0 hF0
    exact bounded_face_is_glued_face W h0 hp H F0 hF0
  · intro F0
    change (P0).IsUnbounded F0 ↔ F0.val = Lower
    exact unbounded_face_eq_lower w0 h0 ((And.left H) 0) F0




noncomputable def faces_upper_bijection :
    {F0 : (P0).Face // ¬ (P0).IsUnbounded F0} ≃
      {F : (G).Face // F.val ⊆ Upper} := by
  classical
  let source := {F0 : (P0).Face // ¬ (P0).IsUnbounded F0}
  let target := {F : (G).Face // F.val ⊆ Upper}
  let faceExists (F0 : source) : ∃ F : (G).Face, F.val = F0.val.val :=
    bounded_face_is_glued_face W h0 hp H F0.val F0.property
  let f : source → target := fun F0 =>
    ⟨Classical.choose (faceExists F0), by
      rw [Classical.choose_spec (faceExists F0)]
      exact boundedFace_subset_upper w0 h0 ((And.left H) 0)
        F0.val F0.property⟩
  have hf_value (F0 : source) : (f F0).val.val = F0.val.val :=
    Classical.choose_spec (faceExists F0)
  have hf_inj : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    apply Subtype.ext
    calc
      A.val.val = (f A).val.val := (hf_value A).symm
      _ = (f B).val.val := congrArg (fun F : target => F.val.val) h
      _ = B.val.val := hf_value B
  have hf_surj : Function.Surjective f := by
    intro F
    obtain ⟨F0, hF0, hval⟩ :=
      (WholePlaneM0Drawing.m0_face_iff W h0 hp H F.val).mp F.property
    refine ⟨⟨F0, hF0⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (hf_value ⟨F0, hF0⟩).trans hval.symm
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

end
end DirectedDistances.KMSW.WholePlanePastGlueM0Restriction
