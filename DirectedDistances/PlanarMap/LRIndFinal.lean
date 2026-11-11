module

public import DirectedDistances.PlanarMap.LRIndNormalizers
public import DirectedDistances.KMSW.BoltzmannPartitionLR

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PlanarMap

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory




@[expose] noncomputable def lrRepresentativeCutPair {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (m : BoltzmannSpace ℓ r) (hm : xdpLen x m = s) :
    {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR} := by
  let R : KMSWMapRep ℓ r m.1 := Quotient.out m.2
  have hR : xdpLengthBase R.B x = s := by
    have h := hm
    change xdpLenClass x m.2 = s at h
    have hout : KMSWMapIsoClass.mk R = m.2 := Quotient.out_eq m.2
    rw [← hout, xdpLenClass_mk] at h
    exact h
  let L := d.cutL R hR
  let T := d.cutR R hR
  refine (⟨⟨L.1, KMSWMapIsoClass.mk L.2⟩, ?_⟩,
    ⟨⟨T.1, KMSWMapIsoClass.mk T.2⟩, ?_⟩)
  · change IsMLClass x (KMSWMapIsoClass.mk L.2)
    rw [IsMLClass_mk]
    exact d.cutL_ML R hR
  · change IsMRClass x (KMSWMapIsoClass.mk T.2)
    rw [IsMRClass_mk]
    exact d.cutR_MR R hR




@[expose] noncomputable def lrCutLeftClass {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR})
    (m : BoltzmannSpace ℓ r) : {mL : BoltzmannSpace ℓ s // IsML x mL} :=
  if hm : xdpLen x m = s then (lrRepresentativeCutPair d m hm).1 else default.1




@[expose] noncomputable def lrCutRightClass {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR})
    (m : BoltzmannSpace ℓ r) : {mR : BoltzmannSpace s r // IsMR x mR} :=
  if hm : xdpLen x m = s then (lrRepresentativeCutPair d m hm).2 else default.2




theorem lrRepresentativeCutPair_eq_lrClassEquiv_symm {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (m : BoltzmannSpace ℓ r) (hm : xdpLen x m = s) :
    lrRepresentativeCutPair d m hm = (lrClassEquiv d).symm ⟨m, hm⟩ := by
  apply Prod.ext
  · apply Subtype.ext
    rw [lrClassEquiv_symm_fst]
    rfl
  · apply Subtype.ext
    rw [lrClassEquiv_symm_snd]
    rfl




theorem lrCutLeftClass_eq_boltzmannLRLeftCutOutput_on_fiber
    {x : XDP} {ℓ s r : ℕ} (d : LRCutGlueRepData x ℓ s r)
    (default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR})
    (m : BoltzmannSpace ℓ r) (hm : xdpLen x m = s) :
    lrCutLeftClass d default m =
      boltzmannLRLeftCutOutput ℓ s r x (lrClassEquiv d) default m := by
  unfold lrCutLeftClass boltzmannLRLeftCutOutput boltzmannLRCutOutputPair
  simp only [dite_eq_left hm]
  exact congrArg Prod.fst (lrRepresentativeCutPair_eq_lrClassEquiv_symm d m hm)




theorem lrCutRightClass_eq_boltzmannLRRightCutOutput_on_fiber
    {x : XDP} {ℓ s r : ℕ} (d : LRCutGlueRepData x ℓ s r)
    (default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR})
    (m : BoltzmannSpace ℓ r) (hm : xdpLen x m = s) :
    lrCutRightClass d default m =
      boltzmannLRRightCutOutput ℓ s r x (lrClassEquiv d) default m := by
  unfold lrCutRightClass boltzmannLRRightCutOutput boltzmannLRCutOutputPair
  simp only [dite_eq_left hm]
  exact congrArg Prod.snd (lrRepresentativeCutPair_eq_lrClassEquiv_symm d m hm)

local instance instMeasurableSpaceLRFinalML {x : XDP} {ℓ s : ℕ} :
    MeasurableSpace {mL : BoltzmannSpace ℓ s // IsML x mL} := ⊤
local instance instMeasurableSpaceLRFinalMR {x : XDP} {s r : ℕ} :
    MeasurableSpace {mR : BoltzmannSpace s r // IsMR x mR} := ⊤





theorem lem_lr_ind_of_data {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r)
    (hF : 0 < boltzmannLaw ℓ r
      (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
      (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2
      (boltzmannFiber (ℓ := ℓ) (r := r) x s)) :
    ∃ default :
      {mL : BoltzmannSpace ℓ s // IsML x mL} ×
        {mR : BoltzmannSpace s r // IsMR x mR},
      ProbabilityTheory.IndepFun
        (Subtype.val ∘ lrCutLeftClass d default)
        (Subtype.val ∘ lrCutRightClass d default)
        ((boltzmannLaw ℓ r
          (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
          (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]) := by
  classical
  let h0 := (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
  let htop := (KMSW.boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2
  have hF' : 0 < boltzmannLaw ℓ r h0 htop
      (boltzmannFiber (ℓ := ℓ) (r := r) x s) := hF
  obtain ⟨m, hm⟩ := nonempty_of_measure_ne_zero hF'.ne'
  change xdpLen x m = s at hm
  let default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR} :=
    lrRepresentativeCutPair d m hm
  refine ⟨default, ?_⟩
  have hred := lem_lr_ind_reduced d h0 htop (ne_of_gt hF') default
  have hleft : (Subtype.val ∘ lrCutLeftClass d default) =
      (Subtype.val ∘ boltzmannLRLeftCutOutput ℓ s r x
        (lrClassEquiv d) default) := by
    funext z
    change (lrCutLeftClass d default z).1 =
      (boltzmannLRLeftCutOutput ℓ s r x (lrClassEquiv d) default z).1
    by_cases hz : xdpLen x z = s
    · exact congrArg Subtype.val
        (lrCutLeftClass_eq_boltzmannLRLeftCutOutput_on_fiber d default z hz)
    · simp [lrCutLeftClass, boltzmannLRLeftCutOutput,
        boltzmannLRCutOutputPair, hz]
  have hright : (Subtype.val ∘ lrCutRightClass d default) =
      (Subtype.val ∘ boltzmannLRRightCutOutput ℓ s r x
        (lrClassEquiv d) default) := by
    funext z
    change (lrCutRightClass d default z).1 =
      (boltzmannLRRightCutOutput ℓ s r x (lrClassEquiv d) default z).1
    by_cases hz : xdpLen x z = s
    · exact congrArg Subtype.val
        (lrCutRightClass_eq_boltzmannLRRightCutOutput_on_fiber d default z hz)
    · simp [lrCutRightClass, boltzmannLRRightCutOutput,
        boltzmannLRCutOutputPair, hz]
  have hleftAE : (Subtype.val ∘ lrCutLeftClass d default) =ᵐ[
      (boltzmannLaw ℓ r h0 htop)[|
        boltzmannFiber (ℓ := ℓ) (r := r) x s]]
      (Subtype.val ∘ boltzmannLRLeftCutOutput ℓ s r x
        (lrClassEquiv d) default) :=
    Filter.Eventually.of_forall fun z => congrFun hleft z
  have hrightAE : (Subtype.val ∘ lrCutRightClass d default) =ᵐ[
      (boltzmannLaw ℓ r h0 htop)[|
        boltzmannFiber (ℓ := ℓ) (r := r) x s]]
      (Subtype.val ∘ boltzmannLRRightCutOutput ℓ s r x
        (lrClassEquiv d) default) :=
    Filter.Eventually.of_forall fun z => congrFun hright z
  have hvalL : Measurable (Subtype.val :
      {mL : BoltzmannSpace ℓ s // IsML x mL} → BoltzmannSpace ℓ s) :=
    by
      change Measurable[⊤] (Subtype.val :
        {mL : BoltzmannSpace ℓ s // IsML x mL} → BoltzmannSpace ℓ s)
      exact measurable_from_top
  have hvalR : Measurable (Subtype.val :
      {mR : BoltzmannSpace s r // IsMR x mR} → BoltzmannSpace s r) :=
    by
      change Measurable[⊤] (Subtype.val :
        {mR : BoltzmannSpace s r // IsMR x mR} → BoltzmannSpace s r)
      exact measurable_from_top
  have hcomp := hred.1.comp hvalL hvalR
  simpa [h0, htop] using hcomp.congr hleftAE.symm hrightAE.symm

end DirectedDistances.PlanarMap
