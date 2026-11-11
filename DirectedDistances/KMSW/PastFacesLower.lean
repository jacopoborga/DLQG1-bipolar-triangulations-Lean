/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.MonotoneFamilyFacesUpper
public import DirectedDistances.KMSW.WholePlanePastGlueData
public import DirectedDistances.PlanarMap.ComponentTransfer

public section

namespace DirectedDistances.KMSW.PastFacesLower

open DirectedDistances.PlanarMap Set WholePlanePastGlueData
open scoped Classical

noncomputable section




theorem isBounded_image_iff (T : ℂ ≃ₜ ℂ) (S : Set ℂ) :
    Bornology.IsBounded (T '' S) ↔ Bornology.IsBounded S := by
  constructor
  · intro h
    apply ((h.isCompact_closure.image (T).symm.continuous).isBounded).subset
    intro z hz
    exact ⟨T z, subset_closure ⟨z, hz, rfl⟩, (T).symm_apply_apply z⟩
  · intro h
    exact ((h.isCompact_closure.image T.continuous).isBounded).subset
      (image_mono subset_closure)

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




theorem isUnbounded_iff_not_isBounded (F : (Pp).Face) :
    (Pp).IsUnbounded F ↔ ¬ Bornology.IsBounded F.val := by
  constructor
  · intro hF hb
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
    obtain ⟨z, hz, hlt⟩ := hF R
    exact hlt.not_ge (hR z hz)
  · intro hb R
    by_contra hR
    apply hb
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R, fun z hz => le_of_not_gt ?_⟩
    intro hlt
    exact hR ⟨z, hz, hlt⟩




theorem image_boundedFace_subset_lower (F : (Pp).Face) (hF : ¬ (Pp).IsUnbounded F) :
    T '' F.val ⊆ {z | z.im < f0 z.re} := by
  have himage : T '' {z : ℂ | fp z.re < z.im} = {z | z.im < f0 z.re} :=
    pastTransfer_image_above (PastDrawingTransfer.phi w0 wp h0 hp
      ((And.left H) 0) (past_finiteIncidence W H)) f0 fp
  rw [← himage]
  exact image_mono (boundedFace_subset_upper wp hp (past_finiteIncidence W H) F hF)





theorem mem_image_boundedFace_of_lower (z : ℂ) (hz : z.im < f0 z.re)
    (hzT : z ∉ T '' (Pp).image) :
    ∃ F : (Pp).Face, ¬ (Pp).IsUnbounded F ∧ z ∈ T '' F.val ∧
      connectedComponentIn (T '' (Pp).image)ᶜ z = T '' F.val := by
  have himage : T '' {z : ℂ | fp z.re < z.im} = {z | z.im < f0 z.re} :=
    pastTransfer_image_above (PastDrawingTransfer.phi w0 wp h0 hp
      ((And.left H) 0) (past_finiteIncidence W H)) f0 fp
  have hz' : fp ((T).symm z).re < ((T).symm z).im := by
    have hmem : z ∈ T '' {q : ℂ | fp q.re < q.im} := by
      rw [himage]
      exact hz
    rw [(T).image_eq_preimage_symm] at hmem
    exact hmem
  have hzP : (T).symm z ∉ (Pp).image := by
    intro hP
    exact hzT ⟨(T).symm z, hP, (T).apply_symm_apply z⟩
  obtain ⟨F, hF, hzF, hcomp⟩ := mem_boundedFace_of_upper wp hp
    (past_finiteIncidence W H) ((T).symm z) hz' hzP
  refine ⟨F, hF, ⟨(T).symm z, hzF, (T).apply_symm_apply z⟩, ?_⟩
  have hc := Homeomorph.image_connectedComponentIn_compl T (Pp).image ((T).symm z)
  rw [(T).apply_symm_apply, hcomp] at hc
  exact hc.symm




theorem image_boundedFace_isBounded (F : (Pp).Face) (hF : ¬ (Pp).IsUnbounded F) :
    Bornology.IsBounded (T '' F.val) := by
  apply (isBounded_image_iff T F.val).mpr
  by_contra hb
  exact hF ((isUnbounded_iff_not_isBounded W H F).mpr hb)

end

end DirectedDistances.KMSW.PastFacesLower
