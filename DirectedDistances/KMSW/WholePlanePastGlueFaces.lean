module

public import DirectedDistances.KMSW.WholePlanePastGlueFacesUpper
public import DirectedDistances.KMSW.WholePlanePastGlueFacesLower
public import DirectedDistances.KMSW.WholePlanePastGlueImage
public import DirectedDistances.KMSW.PastFacesLower
public import DirectedDistances.PlanarMap.PlaneRealization

public section
namespace DirectedDistances.KMSW.WholePlanePastGlueFaces

open DirectedDistances.PlanarMap Set WholePlanePastGlueData WholePlanePastGlueImage
  DirectedDistances.KMSW.PastFacesLower
  DirectedDistances.KMSW.WholePlanePastGlueFacesUpper
  DirectedDistances.KMSW.WholePlanePastGlueFacesLower

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
local notation "G" => gluedImage W h0 hp H
local notation "Upper" =>
  Set.ofPred (fun z : ℂ => f0 (Complex.re z) < Complex.im z)
local notation "Lower" =>
  Set.ofPred (fun z : ℂ => Complex.im z < f0 (Complex.re z))




theorem not_mem_side (z : ℂ) (hz : z ∉ G) : z ∈ Upper ∨ z ∈ Lower := by
  by_cases hup : f0 z.re < z.im
  · exact Or.inl hup
  · by_cases hlow : z.im < f0 z.re
    · exact Or.inr hlow
    · have heq : z.im = f0 z.re := by
        apply le_antisymm
        · exact le_of_not_gt hup
        · exact le_of_not_gt hlow
      have hgraph : z ∈ {q : ℂ | q.im = f0 q.re} := heq
      have hmem : z ∈ G ∩ {q : ℂ | q.im = f0 q.re} := by
        rw [gluedImage_inter_graph W h0 hp H]
        exact hgraph
      exact (hz hmem.1).elim




theorem component_classification (z : ℂ) (hz : z ∉ G) :
    (∃ F : (P0).Face, ¬ (P0).IsUnbounded F ∧
      connectedComponentIn Gᶜ z = F.val) ∨
    (∃ F : (Pp).Face, ¬ (Pp).IsUnbounded F ∧
      connectedComponentIn Gᶜ z = T '' F.val) := by
  rcases not_mem_side W h0 hp H z hz with hup | hlow
  · obtain ⟨_, F, hF, _, hcomp⟩ :=
      glued_upper_component W h0 hp H z hup hz
    exact Or.inl ⟨F, hF, hcomp⟩
  · obtain ⟨_, F, hF, _, hcomp⟩ :=
      glued_lower_component W h0 hp H z hlow hz
    exact Or.inr ⟨F, hF, hcomp⟩




theorem component_isBounded (z : ℂ) (hz : z ∉ G) :
    Bornology.IsBounded (connectedComponentIn Gᶜ z) := by
  rcases component_classification W h0 hp H z hz with
    ⟨F, hF, hcomp⟩ | ⟨F, hF, hcomp⟩
  · rw [hcomp]
    by_contra hb
    apply hF
    intro R
    by_contra hR
    apply hb
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R, ?_⟩
    intro q hq
    exact le_of_not_gt (fun hgt => hR ⟨q, hq, hgt⟩)
  · rw [hcomp]
    exact image_boundedFace_isBounded W h0 hp H F hF




theorem components_eq :
    {C : Set ℂ | ∃ z ∉ G, C = connectedComponentIn Gᶜ z} =
      {C : Set ℂ | ∃ F : (P0).Face, ¬ (P0).IsUnbounded F ∧ C = F.val} ∪
        {C : Set ℂ | ∃ F : (Pp).Face, ¬ (Pp).IsUnbounded F ∧ C = T '' F.val} := by
  ext C
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases component_classification W h0 hp H z hz with
      ⟨F, hF, hcomp⟩ | ⟨F, hF, hcomp⟩
    · exact Or.inl ⟨F, hF, hcomp⟩
    · exact Or.inr ⟨F, hF, hcomp⟩
  · intro hC
    rcases hC with ⟨F, hF, hC⟩ | ⟨F, hF, hC⟩
    · obtain ⟨z, _, hz, hcomp⟩ :=
        glued_component_of_boundedFace W h0 hp H F hF
      exact ⟨z, hz, hC.trans hcomp.symm⟩
    · obtain ⟨z, _, hz, hcomp⟩ :=
        glued_component_of_past_boundedFace W h0 hp H F hF
      exact ⟨z, hz, hC.trans hcomp.symm⟩

end
end DirectedDistances.KMSW.WholePlanePastGlueFaces
