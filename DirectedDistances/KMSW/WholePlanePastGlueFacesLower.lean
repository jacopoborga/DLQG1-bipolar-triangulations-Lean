/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.WholePlanePastGlueImage
public import DirectedDistances.KMSW.PastFacesLower
public import DirectedDistances.KMSW.MonotoneSeamRegions
public import DirectedDistances.PlanarMap.PLDrawingFaceTransfer
import all DirectedDistances.KMSW.KMSWWindowInfiniteMaps
import DirectedDistances.KMSW.StageVertices

public section
namespace DirectedDistances.KMSW.WholePlanePastGlueFacesLower

open DirectedDistances.PlanarMap Set WholePlanePastGlueData WholePlanePastGlueImage
  DirectedDistances.KMSW.PastFacesLower

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
local notation "Pt" => pastDrawing W h0 hp H
local notation "T" => PastDrawingTransfer.transfer w0 wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)
local notation "f0" => seamFun w0 h0 ((And.left H) 0)
local notation "fp" => seamFun wp hp (past_finiteIncidence W H)
local notation "pos" => gluedPos W h0 hp H
local notation "arc" => gluedArc W h0 hp H
local notation "G" => gluedImage W h0 hp H
local notation "Lower" =>
  Set.ofPred (fun z : ℂ => Complex.im z < f0 (Complex.re z))




theorem pastImage_isClosed : IsClosed (T '' (Pp).image) := by
  have hclosed : IsClosed (Pp).image := by
    apply PLDrawing.image_isClosed
    intro v
    obtain ⟨d, hd⟩ := stageEndpoint_exists wp (4 * v + 1) v
      (vertex_allocated_at wp v)
    refine ⟨(d.1.val, d.2), ?_⟩
    have he := edge_endpoints_eq wp d.1.isLt
    cases hb : d.2 <;>
      simpa only [kmswLimitDartVertex, stageEndpoint, hb, Bool.false_eq_true,
        ite_false, ite_true, he.1, he.2] using hd
  exact (T).isClosedMap _ hclosed




private theorem lower_agreement :
    ((T '' (Pp).image) ∩ closure Lower ⊆ G) ∧
      (G ∩ Lower ⊆ T '' (Pp).image) := by
  have hclosure : closure Lower ⊆ {z : ℂ | z.im ≤ f0 z.re} := by
    apply closure_minimal
    · intro z hz
      change z.im < f0 z.re at hz
      exact hz.le
    · exact isClosed_le Complex.continuous_im
        ((seamFun_continuous w0 h0 ((And.left H) 0)).comp Complex.continuous_re)
  constructor
  · rintro z ⟨hzX, hzcl⟩
    by_cases hzLower : z.im < f0 z.re
    · have hzLowerSet : z ∈ Lower := by
        change z.im < f0 z.re
        exact hzLower
      have hzXLower : z ∈ (T '' (Pp).image) ∩ Lower := ⟨hzX, hzLowerSet⟩
      have hzGLower : z ∈ G ∩ Lower := by
        rw [WholePlanePastGlueImage.gluedImage_inter_lower W h0 hp H]
        exact hzXLower
      exact hzGLower.1
    · have hge : f0 z.re ≤ z.im := le_of_not_gt hzLower
      have hzgraph : z.im = f0 z.re := le_antisymm (hclosure hzcl) hge
      have hzGgraph : z ∈ G ∩ {z : ℂ | z.im = f0 z.re} := by
        rw [gluedImage_inter_graph W h0 hp H]
        exact hzgraph
      exact hzGgraph.1
  · intro z hz
    change z ∈ G ∧ z.im < f0 z.re at hz
    have hzLowerSet : z ∈ Lower := by
      change z.im < f0 z.re
      exact hz.2
    have hzGLower : z ∈ G ∩ Lower := ⟨hz.1, hzLowerSet⟩
    rw [WholePlanePastGlueImage.gluedImage_inter_lower W h0 hp H] at hzGLower
    exact hzGLower.1




theorem glued_lower_component (z : ℂ) (hz : z ∈ Lower) (hzG : z ∉ G) :
    z ∉ T '' (Pp).image ∧
      ∃ F : (Pp).Face, ¬ (Pp).IsUnbounded F ∧ z ∈ T '' F.val ∧
        connectedComponentIn Gᶜ z = T '' F.val := by
  have hagree := lower_agreement W h0 hp H
  have hzX : z ∉ T '' (Pp).image := by
    intro hzX
    have hzLower : z ∈ Lower := by
      change z.im < f0 z.re
      exact hz
    exact hzG (hagree.1 ⟨hzX, subset_closure hzLower⟩)
  obtain ⟨F, hF, hzF, hcompF⟩ :=
    mem_image_boundedFace_of_lower W h0 hp H z hz hzX
  have hUA : connectedComponentIn (T '' (Pp).image)ᶜ z ⊆ Lower := by
    rw [hcompF]
    exact image_boundedFace_subset_lower W h0 hp H F hF
  obtain ⟨_, hcomp⟩ := connectedComponentIn_compl_eq_of_agree
    (pastImage_isClosed W h0 hp H) hzX hUA hagree.1 hagree.2
  exact ⟨hzX, F, hF, hzF, hcomp.trans hcompF⟩




theorem glued_component_of_past_boundedFace (F : (Pp).Face)
    (hF : ¬ (Pp).IsUnbounded F) :
    ∃ z ∈ T '' F.val, z ∉ G ∧ connectedComponentIn Gᶜ z = T '' F.val := by
  obtain ⟨x, hxP, hFx⟩ := F.property
  have hxP' : x ∈ (Pp).imageᶜ := by simpa using hxP
  let z := T x
  have hzX : z ∉ T '' (Pp).image := by
    rintro ⟨y, hy, hzy⟩
    exact hxP ((T).injective hzy ▸ hy)
  have himageComp := Homeomorph.image_connectedComponentIn_compl T (Pp).image x
  rw [← hFx] at himageComp
  have hcompX : connectedComponentIn (T '' (Pp).image)ᶜ z = T '' F.val := by
    simpa only [z] using himageComp.symm
  have hzX' : z ∈ (T '' (Pp).image)ᶜ := by
    simpa only [Set.mem_compl_iff] using hzX
  have hzF : z ∈ T '' F.val := by
    rw [← hcompX]
    exact mem_connectedComponentIn hzX'
  have hagree := lower_agreement W h0 hp H
  have hUA : connectedComponentIn (T '' (Pp).image)ᶜ z ⊆ Lower := by
    rw [hcompX]
    exact image_boundedFace_subset_lower W h0 hp H F hF
  obtain ⟨hzG, hcomp⟩ := connectedComponentIn_compl_eq_of_agree
    (pastImage_isClosed W h0 hp H) hzX hUA hagree.1 hagree.2
  exact ⟨z, hzF, hzG, hcomp.trans hcompX⟩




theorem glued_lower_component_subset (z : ℂ) (hz : z ∈ Lower) (hzG : z ∉ G) :
    connectedComponentIn Gᶜ z ⊆ Lower := by
  obtain ⟨_, F, hF, _, hcomp⟩ := glued_lower_component W h0 hp H z hz hzG
  rw [hcomp]
  exact image_boundedFace_subset_lower W h0 hp H F hF

end
end DirectedDistances.KMSW.WholePlanePastGlueFacesLower
