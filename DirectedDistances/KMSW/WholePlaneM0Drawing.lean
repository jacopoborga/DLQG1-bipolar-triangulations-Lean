module

public import DirectedDistances.KMSW.WholePlanePastGlueDrawing

public section
namespace DirectedDistances.KMSW.WholePlaneM0Drawing

open DirectedDistances.PlanarMap Set WholePlanePastGlueData WholePlanePastGlueGeometry

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
local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h0 hp H
local notation "Upper" => Set.ofPred (fun z : ℂ => f0 (Complex.re z) < Complex.im z)
local notation "closedUpper" => Set.ofPred (fun z : ℂ => f0 (Complex.re z) ≤ Complex.im z)
local notation "Lower" => Set.ofPred (fun z : ℂ => Complex.im z < f0 (Complex.re z))




theorem m0_vertex_iff (V : WholePlaneVertex W) :
    (G).pos V ∈ closedUpper ↔ V ∈ Set.range (wholePlaneVertexι W 0) := by
  constructor
  · intro hv
    by_contra hn
    obtain ⟨v, rfl⟩ := (vertex_cover W V).resolve_left hn
    have hvb : ∀ k : ℤ, v ≠ boundaryVertex wp hp k := by
      intro k hk
      apply hn
      rw [hk, seam_vertex W h0 hp k]
      exact ⟨_, rfl⟩
    have hb := past_pos_strictly_below W h0 hp H v hvb
    change f0 (gluedPos W h0 hp H (kmswPastVertex W v)).re ≤
      (gluedPos W h0 hp H (kmswPastVertex W v)).im at hv
    exact not_lt_of_ge hv hb
  · rintro ⟨v, rfl⟩
    exact runZero_pos_above W h0 hp H v




private theorem arc_interior_nonempty (D : WholePlaneDart W) :
    ((G).arc D).interior.Nonempty := by
  let p := (G).arc D
  let a := midpoint ℝ p.start (p.point 1)
  let b := midpoint ℝ p.start a
  have hne : p.start ≠ p.point 1 := by
    intro he
    exact (G).initial_nonzero D (sub_eq_zero.mpr he.symm)
  have ha : a ≠ p.start := fun he => hne ((midpoint_eq_left_iff ℝ).mp he)
  have hb : b ≠ p.start := by
    intro he
    exact ha ((midpoint_eq_left_iff ℝ).mp he).symm
  have hba : b ≠ a := by
    intro he
    exact ha ((midpoint_eq_right_iff ℝ).mp he).symm
  have ham : a ∈ segment ℝ p.start (p.point 1) :=
    midpoint_mem_segment p.start (p.point 1)
  have hbm : b ∈ segment ℝ p.start (p.point 1) :=
    (convex_segment p.start (p.point 1)).segment_subset
      (left_mem_segment ℝ p.start (p.point 1)) ham (midpoint_mem_segment p.start a)
  have himage {z : ℂ} (hz : z ∈ segment ℝ p.start (p.point 1)) : z ∈ p.image := by
    refine Or.inr ⟨0, ?_, ?_⟩
    · have hl := (G).arc_length D
      change 2 ≤ p.points.length at hl
      omega
    · change z ∈ segment ℝ (p.point 0) (p.point 1)
      rw [Polyline.point_zero_eq_start]
      exact hz
  by_cases haf : a = p.finish
  · refine ⟨b, himage hbm, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hb, fun he => hba (he.trans haf.symm)⟩
  · refine ⟨a, himage ham, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha, haf⟩




theorem m0_dart_iff (D : WholePlaneDart W) :
    ((G).arc D).image ⊆ closedUpper ↔ D ∈ Set.range (wholePlaneDartι W 0) := by
  constructor
  · intro hd
    rcases dart_cover_off_seam W h0 D with hrun | ⟨d, hn, rfl⟩
    · exact hrun
    · obtain ⟨z, hz⟩ := arc_interior_nonempty W h0 hp H (kmswPastDart W d)
      have ha := hd hz.1
      have hb := past_interior_below W h0 hp H d hn hz
      change f0 z.re ≤ z.im at ha
      change z.im < f0 z.re at hb
      exact (not_lt_of_ge ha hb).elim
  · rintro ⟨d, rfl⟩ z hz
    exact runZero_arc_above W h0 hp H d hz




theorem m0_face_iff (F : (G).Face) :
    F.val ⊆ Upper ↔ ∃ F0 : (P0).Face, ¬ (P0).IsUnbounded F0 ∧ F.val = F0.val := by
  constructor
  · intro hup
    obtain ⟨z, hz, hF⟩ := F.property
    have hzF : z ∈ F.val := hF ▸ mem_connectedComponentIn hz
    change z ∉ WholePlanePastGlueImage.gluedImage W h0 hp H at hz
    obtain ⟨_, F0, hF0, _, hcomp⟩ :=
      WholePlanePastGlueFacesUpper.glued_upper_component W h0 hp H z (hup hzF) hz
    exact ⟨F0, hF0, hF.trans hcomp⟩
  · rintro ⟨F0, hF0, he⟩
    rw [he]
    exact boundedFace_subset_upper w0 h0 ((And.left H) 0) F0 hF0




theorem face_side (F : (G).Face) : F.val ⊆ Upper ∨ F.val ⊆ Lower := by
  rcases WholePlanePastGlueDrawing.glueDrawing_faces W h0 hp H F with
    ⟨F0, hF0, he⟩ | ⟨Fp, hFp, he⟩
  · left
    rw [he]
    exact boundedFace_subset_upper w0 h0 ((And.left H) 0) F0 hF0
  · right
    rw [he]
    exact PastFacesLower.image_boundedFace_subset_lower W h0 hp H Fp hFp




theorem m0_dart_iff_edge (D : WholePlaneDart W) :
    D ∈ Set.range (wholePlaneDartι W 0) ↔
      D.1 ∈ Set.range (wholePlaneEdgeι W 0) := by
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d.1, rfl⟩
  · rintro ⟨e, he⟩
    exact ⟨(e, D.2), Prod.ext he rfl⟩

end
end DirectedDistances.KMSW.WholePlaneM0Drawing
