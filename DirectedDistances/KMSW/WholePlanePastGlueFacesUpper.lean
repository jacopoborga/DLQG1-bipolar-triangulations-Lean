/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.WholePlanePastGlueImage
public import DirectedDistances.KMSW.MonotoneFamilyFacesUpper
public import DirectedDistances.PlanarMap.PLDrawingFaceTransfer
import all DirectedDistances.KMSW.KMSWWindowInfiniteMaps
import DirectedDistances.KMSW.StageVertices

public section
namespace DirectedDistances.KMSW.WholePlanePastGlueFacesUpper

open DirectedDistances.PlanarMap Set WholePlanePastGlueData WholePlanePastGlueImage

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
local notation "Pt" => pastDrawing W h0 hp H
local notation "T" => PastDrawingTransfer.transfer w0 wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)
local notation "f0" => seamFun w0 h0 ((And.left H) 0)
local notation "fp" => seamFun wp hp (past_finiteIncidence W H)
local notation "pos" => gluedPos W h0 hp H
local notation "arc" => gluedArc W h0 hp H
local notation "G" => gluedImage W h0 hp H
local notation "Upper" => (Set.ofPred (fun z : ℂ => f0 (Complex.re z) < Complex.im z))




theorem runZero_image_isClosed : IsClosed (P0).image := by
  apply PLDrawing.image_isClosed
  intro v
  obtain ⟨d, hd⟩ := stageEndpoint_exists w0 (4 * v + 1) v (vertex_allocated_at w0 v)
  refine ⟨(d.1.val, d.2), ?_⟩
  have he := edge_endpoints_eq w0 d.1.isLt
  cases hb : d.2 <;>
    simpa only [kmswLimitDartVertex, stageEndpoint, hb, Bool.false_eq_true,
      ite_false, ite_true, he.1, he.2] using hd




private theorem runZero_upper_agreement :
    ((P0).image ∩ closure Upper ⊆ G) ∧ (G ∩ Upper ⊆ (P0).image) := by
  have hclosure : closure Upper ⊆ {z : ℂ | f0 z.re ≤ z.im} := by
    apply closure_minimal
    · intro z hz
      change f0 z.re ≤ z.im
      exact (show f0 z.re < z.im from hz).le
    · exact isClosed_le ((seamFun_continuous w0 h0 ((And.left H) 0)).comp
        Complex.continuous_re) Complex.continuous_im
  constructor
  · rintro z ⟨hzP, hzcl⟩
    by_cases hzup : f0 z.re < z.im
    · have hz : z ∈ G ∩ Upper := by
        rw [gluedImage_inter_upper W h0 hp H]
        exact ⟨hzP, hzup⟩
      exact hz.1
    · have hzgraph : z ∈ {z : ℂ | z.im = f0 z.re} :=
        le_antisymm (not_lt.mp hzup) (hclosure hzcl)
      have hz : z ∈ G ∩ {z : ℂ | z.im = f0 z.re} := by
        rw [gluedImage_inter_graph W h0 hp H]
        exact hzgraph
      exact hz.1
  · intro z hz
    have hzP : z ∈ (P0).image ∩ Upper := by
      rw [← gluedImage_inter_upper W h0 hp H]
      exact hz
    exact hzP.1




theorem glued_upper_component (z : ℂ) (hz : z ∈ Upper) (hzG : z ∉ G) :
    z ∉ (P0).image ∧ ∃ F : (P0).Face, ¬ (P0).IsUnbounded F ∧ z ∈ F.val ∧
      connectedComponentIn Gᶜ z = F.val := by
  have hagree := runZero_upper_agreement W h0 hp H
  have hzP : z ∉ (P0).image := by
    intro hzP
    exact hzG (hagree.1 ⟨hzP, subset_closure hz⟩)
  obtain ⟨F, hF, hzF, hcompF⟩ := mem_boundedFace_of_upper w0 h0 ((And.left H) 0)
    z hz hzP
  have hupper : connectedComponentIn (P0).imageᶜ z ⊆ Upper := by
    rw [hcompF]
    exact boundedFace_subset_upper w0 h0 ((And.left H) 0) F hF
  obtain ⟨_, hcomp⟩ := connectedComponentIn_compl_eq_of_agree
    (runZero_image_isClosed W H) hzP hupper hagree.1 hagree.2
  exact ⟨hzP, F, hF, hzF, hcomp.trans hcompF⟩




theorem glued_component_of_boundedFace (F : (P0).Face) (hF : ¬ (P0).IsUnbounded F) :
    ∃ z ∈ F.val, z ∉ G ∧ connectedComponentIn Gᶜ z = F.val := by
  obtain ⟨z, hzP, hFz⟩ := F.property
  have hzF : z ∈ F.val := by
    rw [hFz]
    exact mem_connectedComponentIn hzP
  have hagree := runZero_upper_agreement W h0 hp H
  have hupper : connectedComponentIn (P0).imageᶜ z ⊆ Upper := by
    rw [← hFz]
    exact boundedFace_subset_upper w0 h0 ((And.left H) 0) F hF
  obtain ⟨hzG, hcomp⟩ := connectedComponentIn_compl_eq_of_agree
    (runZero_image_isClosed W H) hzP hupper hagree.1 hagree.2
  exact ⟨z, hzF, hzG, hcomp.trans hFz.symm⟩




theorem glued_upper_component_subset (z : ℂ) (hz : z ∈ Upper) (hzG : z ∉ G) :
    connectedComponentIn Gᶜ z ⊆ Upper := by
  obtain ⟨_, F, hF, _, hcomp⟩ := glued_upper_component W h0 hp H z hz hzG
  rw [hcomp]
  exact boundedFace_subset_upper w0 h0 ((And.left H) 0) F hF

end
end DirectedDistances.KMSW.WholePlanePastGlueFacesUpper
