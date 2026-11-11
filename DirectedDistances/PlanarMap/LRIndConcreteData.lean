module

public import DirectedDistances.PlanarMap.LRCutGlueRep
public import DirectedDistances.PlanarMap.PlanarPathGlueCutRot
public import DirectedDistances.PlanarMap.PlanarPathCutGlueIso
public import DirectedDistances.PlanarMap.LRCutRepIsoRight
public import DirectedDistances.PlanarMap.LRIndFinal
public import DirectedDistances.PlanarMap.PlanarPathGlueRep
public import DirectedDistances.PlanarMap.LRGlueRepLen
public import DirectedDistances.PlanarMap.LRCutRep
public import DirectedDistances.PlanarMap.LRCutRepRight

import all DirectedDistances.PlanarMap.PlanarPathGlueCutLeft

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PlanarMap

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

section Rotation

variable {DL DR : Type*} [Fintype DL] [DecidableEq DL]
  [Fintype DR] [DecidableEq DR] {ℓ s r : ℕ}
variable (BL : BipolarTriangulationWithBoundaryBase DL ℓ s)
  (BR : BipolarTriangulationWithBoundaryBase DR s r)



theorem glueCutLeftEquiv_rot (d : DL) :
    glueCutLeftEquiv BL BR (BL.map.toCombinatorialMap.rot d) =
      (pathCutLeftHalfMap (glueBase BL BR) (glueSeamPathBase BL BR)).rot
        (glueCutLeftEquiv BL BR d) := by
  rw [glueCutLeftEquiv.eq_def]
  exact (glueCutLeft_rot BL BR d).symm



theorem glueCutRightEquiv_rot (d : DR) :
    glueCutRightEquiv BL BR (BR.map.toCombinatorialMap.rot d) =
      (pathCutRightHalfMap (glueBase BL BR) (glueSeamPathBase BL BR)).rot
        (glueCutRightEquiv BL BR d) := by
  rw [glueCutRightEquiv.eq_def]
  exact (glueCutRight_rot BL BR d).symm

end Rotation



theorem cut_glueRep' {x : XDP} {ℓ s r a b : ℕ}
    (A : KMSWMapRep ℓ s a) (Bm : KMSWMapRep s r b)
    (hA : IsMLRepresentative x A) (hB : IsMRRepresentative x Bm) :
    Nonempty (BipolarBoundaryBaseIso
      (cutLRep (glueRep A Bm) (glueRep_len A Bm hA hB)).2.B A.B) ∧
    Nonempty (BipolarBoundaryBaseIso
      (cutRRep (glueRep A Bm) (glueRep_len A Bm hA hB)).2.B Bm.B) :=
  cut_glueRep A Bm hA hB
    (fun d => glueCutLeftEquiv_rot A.B Bm.B d)
    (fun d => glueCutRightEquiv_rot A.B Bm.B d)



@[expose] noncomputable def lrCutGlueRepData (x : XDP) (ℓ s r : ℕ) :
    LRCutGlueRepData x ℓ s r where
  glue := fun A B _ _ => glueRep A B
  glue_edges := fun A B _ _ => glueRep_edges A B
  glue_iso := glueRep_iso
  glue_len := glueRep_len
  cutL := cutLRep
  cutR := cutRRep
  cut_iso := cutRep_iso
  cutL_ML := cutLRep_ML
  cutR_MR := cutRRep_MR
  cut_edges := cutRep_edges
  cut_glue := cut_glueRep'
  glue_cut := glueRep_cutRep_iso

 
@[simp] theorem lrCutGlueRepData_cutL {x : XDP} {ℓ s r n : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = s) :
    (lrCutGlueRepData x ℓ s r).cutL R hR = cutLRep R hR := rfl

 
@[simp] theorem lrCutGlueRepData_cutR {x : XDP} {ℓ s r n : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = s) :
    (lrCutGlueRepData x ℓ s r).cutR R hR = cutRRep R hR := rfl

 
@[simp] theorem lrCutGlueRepData_glue {x : XDP} {ℓ s r a b : ℕ}
    (A : KMSWMapRep ℓ s a) (Bm : KMSWMapRep s r b)
    (hA : IsMLRepresentative x A) (hB : IsMRRepresentative x Bm) :
    (lrCutGlueRepData x ℓ s r).glue A Bm hA hB = glueRep A Bm := rfl

end DirectedDistances.PlanarMap
