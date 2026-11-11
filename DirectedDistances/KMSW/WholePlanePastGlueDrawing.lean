module

public import DirectedDistances.KMSW.WholePlaneGlueSeamRotation
public import DirectedDistances.KMSW.WholePlaneGlueRotationRunZero
public import DirectedDistances.KMSW.WholePlaneGlueRotationPastAgree
public import DirectedDistances.KMSW.WholePlanePastGlueFaces
public import DirectedDistances.KMSW.WholePlaneRootedMapLocalFinite

public section
namespace DirectedDistances.KMSW.WholePlanePastGlueDrawing

open DirectedDistances.PlanarMap Set WholePlanePastGlueData

noncomputable section

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "w0" => shiftedStream W 0
local notation "wp" => kmswPastCode W
local notation "P0" => monotoneFamilyDrawing w0 ((And.left H) 0) (monotone_family_all w0)
local notation "Pp" => monotoneFamilyDrawing wp (past_finiteIncidence W H)
  (monotone_family_all wp)
local notation "T" => PastDrawingTransfer.transfer w0 wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)
local notation "f0" => seamFun w0 h0 ((And.left H) 0)




private theorem dart_cases (D : WholePlaneDart W) :
    (∃ k : ℤ, wholePlaneDartVertex W D =
      wholePlaneVertexι W 0 (boundaryVertex w0 h0 k)) ∨
    (∃ d : ℕ × Bool,
      (∀ k : ℤ, kmswLimitDartVertex w0 d ≠ boundaryVertex w0 h0 k) ∧
      D = wholePlaneDartι W 0 d) ∨
    (∃ d : ℕ × Bool,
      (∀ k : ℤ, kmswLimitDartVertex wp d ≠ boundaryVertex wp hp k) ∧
      D = kmswPastDart W d) := by
  classical
  rcases dart_cover W D with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · by_cases hv : ∃ k : ℤ, kmswLimitDartVertex w0 d = boundaryVertex w0 h0 k
    · obtain ⟨k, hk⟩ := hv
      left
      exact ⟨k, by rw [wholePlaneDartVertex_ι, hk]⟩
    · right
      left
      exact ⟨d, fun k hk => hv ⟨k, hk⟩, rfl⟩
  · by_cases hv : ∃ k : ℤ, kmswLimitDartVertex wp d = boundaryVertex wp hp k
    · obtain ⟨k, hk⟩ := hv
      left
      exact ⟨1 - k, by rw [pastDart_vertex, hk, seam_vertex W h0 hp]⟩
    · right
      right
      exact ⟨d, fun k hk => hv ⟨k, hk⟩, rfl⟩




private theorem glued_initial_arg_injective (D E : WholePlaneDart W)
    (he : wholePlaneDartVertex W D = wholePlaneDartVertex W E)
    (ha : Complex.arg (gluedArc W h0 hp H D).initialDirection =
      Complex.arg (gluedArc W h0 hp H E).initialDirection) : D = E := by
  rcases dart_cases W h0 hp D with ⟨k, hk⟩ | ⟨d, hv, rfl⟩ | ⟨d, hv, rfl⟩
  · exact WholePlaneGlueSeamRotation.initial_arg_injective_seam_unfolded
      W h0 hp H k D E hk (he.symm.trans hk) ha
  · exact (WholePlaneGlueRotationRunZero.initial_arg_injective_runZero_offSeam
      W h0 hp H d hv E he.symm ha.symm).symm
  · exact (WholePlaneGlueRotationPastAgree.initial_arg_injective_past_offSeam
      W h0 hp H d hv E he.symm ha.symm).symm




private theorem glued_rotation_agreement (D : WholePlaneDart W) :
    CcwSuccessor {E | wholePlaneDartVertex W E = wholePlaneDartVertex W D}
      (fun E => (gluedArc W h0 hp H E).initialDirection) D
      (wholePlaneRotation W H D) := by
  rcases dart_cases W h0 hp D with ⟨k, hk⟩ | ⟨d, hv, rfl⟩ | ⟨d, hv, rfl⟩
  · have hs := WholePlaneGlueSeamRotation.rotation_agreement_seam_unfolded
      W h0 hp H k D hk
    rw [← hk] at hs
    exact hs
  · exact WholePlaneGlueRotationRunZero.rotation_agreement_runZero_offSeam
      W h0 hp H d hv
  · exact WholePlaneGlueRotationPastAgree.rotation_agreement_past_offSeam
      W h0 hp H d hv




@[expose] noncomputable def glueDrawing : WholePlaneDrawing W H where
  flip_involutive := wholePlaneDartFlip_involutive W
  flip_ne := wholePlaneDartFlip_ne W
  vert_rotation := wholePlaneRotation_preserves_dartVertex W H
  pos := gluedPos W h0 hp H
  pos_injective := WholePlanePastGlueGeometry.glued_pos_injective W h0 hp H
  arc := gluedArc W h0 hp H
  arc_simple := gluedArc_simple W h0 hp H
  arc_length := gluedArc_length W h0 hp H
  arc_start := gluedArc_start W h0 hp H
  arc_finish := gluedArc_finish W h0 hp H
  arc_flip := gluedArc_flip W h0 hp H
  interior_disjoint := WholePlanePastGlueGeometry.glued_interior_disjoint W h0 hp H
  interior_avoids_vertices :=
    WholePlanePastGlueGeometry.glued_interior_avoids_vertices W h0 hp H
  locally_finite := WholePlanePastGlueGeometry.glued_locally_finite W h0 hp H
  initial_nonzero := gluedArc_initial_nonzero W h0 hp H
  initial_arg_injective := by exact glued_initial_arg_injective W h0 hp H
  rotation_agreement := by exact glued_rotation_agreement W h0 hp H




theorem glueDrawing_pos : (glueDrawing W h0 hp H).pos = gluedPos W h0 hp H := rfl




theorem glueDrawing_arc : (glueDrawing W h0 hp H).arc = gluedArc W h0 hp H := rfl




theorem glueDrawing_image :
    (glueDrawing W h0 hp H).image = WholePlanePastGlueImage.gluedImage W h0 hp H := rfl




theorem glueDrawing_face_bounded (F : (glueDrawing W h0 hp H).Face) :
    ¬ (glueDrawing W h0 hp H).IsUnbounded F := by
  obtain ⟨z, hz, hF⟩ := F.property
  change z ∉ WholePlanePastGlueImage.gluedImage W h0 hp H at hz
  change F.val =
    connectedComponentIn (WholePlanePastGlueImage.gluedImage W h0 hp H)ᶜ z at hF
  have hb := WholePlanePastGlueFaces.component_isBounded W h0 hp H z hz
  rw [← hF] at hb
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
  intro hu
  obtain ⟨q, hq, hlt⟩ := hu R
  exact hlt.not_ge (hR q hq)




theorem glueDrawing_faces (F : (glueDrawing W h0 hp H).Face) :
    (∃ F0 : (P0).Face, ¬ (P0).IsUnbounded F0 ∧ F.val = F0.val) ∨
    (∃ Fp : (Pp).Face, ¬ (Pp).IsUnbounded Fp ∧ F.val = T '' Fp.val) := by
  obtain ⟨z, hz, hF⟩ := F.property
  change z ∉ WholePlanePastGlueImage.gluedImage W h0 hp H at hz
  change F.val =
    connectedComponentIn (WholePlanePastGlueImage.gluedImage W h0 hp H)ᶜ z at hF
  rw [hF]
  exact WholePlanePastGlueFaces.component_classification W h0 hp H z hz

end
end DirectedDistances.KMSW.WholePlanePastGlueDrawing
