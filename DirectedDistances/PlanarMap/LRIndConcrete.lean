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
public import DirectedDistances.PlanarMap.LRIndConcreteData

import all DirectedDistances.PlanarMap.PlanarPathGlueCutLeft

/- Concrete representative cut/glue data toward `lem-lr-ind`. -/

public section
namespace DirectedDistances.PlanarMap

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

/- left and right cut classes are independent under the conditioned Boltzmann law. -/
theorem lem_lr_ind {x : XDP} {ℓ s r : ℕ}
    (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r)
    (hF : 0 < boltzmannLaw ℓ r
      (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
      (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2
      (boltzmannFiber (ℓ := ℓ) (r := r) x s)) :
    ∃ default :
      {mL : BoltzmannSpace ℓ s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR},
      ProbabilityTheory.IndepFun
        (Subtype.val ∘ lrCutLeftClass (lrCutGlueRepData x ℓ s r) default)
        (Subtype.val ∘ lrCutRightClass (lrCutGlueRepData x ℓ s r) default)
        ((boltzmannLaw ℓ r
          (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
          (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]) :=
  lem_lr_ind_of_data (lrCutGlueRepData x ℓ s r) hℓ hr hF

/- two representative cut functions written out on the selected-length fiber. -/
theorem lem_lr_ind_concrete {x : XDP} {ℓ s r : ℕ}
    (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r)
    (hF : 0 < boltzmannLaw ℓ r
      (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
      (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2
      (boltzmannFiber (ℓ := ℓ) (r := r) x s)) :
    ∃ default :
      {mL : BoltzmannSpace ℓ s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR},
      ProbabilityTheory.IndepFun
        (β := BoltzmannSpace ℓ s) (γ := BoltzmannSpace s r)
        (fun m : BoltzmannSpace ℓ r =>
          if hm : xdpLen x m = s then
            let R : KMSWMapRep ℓ r m.1 := Quotient.out m.2
            let hR : xdpLengthBase R.B x = s := by
              have h := hm
              change xdpLenClass x m.2 = s at h
              have hout : KMSWMapIsoClass.mk R = m.2 := Quotient.out_eq m.2
              rw [← hout, xdpLenClass_mk] at h
              exact h
            let L := cutLRep R hR
            (⟨L.1, KMSWMapIsoClass.mk L.2⟩ : BoltzmannSpace ℓ s)
          else default.1.1)
        (fun m : BoltzmannSpace ℓ r =>
          if hm : xdpLen x m = s then
            let R : KMSWMapRep ℓ r m.1 := Quotient.out m.2
            let hR : xdpLengthBase R.B x = s := by
              have h := hm
              change xdpLenClass x m.2 = s at h
              have hout : KMSWMapIsoClass.mk R = m.2 := Quotient.out_eq m.2
              rw [← hout, xdpLenClass_mk] at h
              exact h
            let T := cutRRep R hR
            (⟨T.1, KMSWMapIsoClass.mk T.2⟩ : BoltzmannSpace s r)
          else default.2.1)
        ((boltzmannLaw ℓ r
          (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
          (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]) := by
  obtain ⟨default, h⟩ := lem_lr_ind (x := x) (s := s) hℓ hr hF
  refine ⟨default, ?_⟩
  simpa only [Function.comp_def, lrCutLeftClass, lrCutRightClass,
    lrRepresentativeCutPair, lrCutGlueRepData_cutL, lrCutGlueRepData_cutR,
    apply_dite] using h

end DirectedDistances.PlanarMap
