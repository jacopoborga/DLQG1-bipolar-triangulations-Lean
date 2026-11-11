/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.LRIndFactorization

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PlanarMap

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory








structure LRCutGlueRepData (x : XDP) (ℓ s r : ℕ) where
  glue {a b : ℕ} (A : KMSWMapRep ℓ s a) (B : KMSWMapRep s r b)
      (hA : IsMLRepresentative x A) (hB : IsMRRepresentative x B) :
      KMSWMapRep ℓ r (a + b - s)
  glue_edges {a b : ℕ} (A : KMSWMapRep ℓ s a) (B : KMSWMapRep s r b)
      (hA : IsMLRepresentative x A) (hB : IsMRRepresentative x B) :
      (a + b - s) + s = a + b
  glue_iso {a b : ℕ} {A A' : KMSWMapRep ℓ s a} {B B' : KMSWMapRep s r b}
      (hA : IsMLRepresentative x A) (hA' : IsMLRepresentative x A')
      (hB : IsMRRepresentative x B) (hB' : IsMRRepresentative x B')
      (hAA : Nonempty (BipolarBoundaryBaseIso A.B A'.B))
      (hBB : Nonempty (BipolarBoundaryBaseIso B.B B'.B)) :
      Nonempty (BipolarBoundaryBaseIso (glue A B hA hB).B
        (glue A' B' hA' hB').B)
  glue_len {a b : ℕ} (A : KMSWMapRep ℓ s a) (B : KMSWMapRep s r b)
      (hA : IsMLRepresentative x A) (hB : IsMRRepresentative x B) :
      xdpLengthBase (glue A B hA hB).B x = s
  cutL {n : ℕ} (R : KMSWMapRep ℓ r n)
      (hR : xdpLengthBase R.B x = s) :
      Σ a : ℕ, KMSWMapRep ℓ s a
  cutR {n : ℕ} (R : KMSWMapRep ℓ r n)
      (hR : xdpLengthBase R.B x = s) :
      Σ b : ℕ, KMSWMapRep s r b
  cut_iso {n : ℕ} {R R' : KMSWMapRep ℓ r n}
      (hR : xdpLengthBase R.B x = s) (hR' : xdpLengthBase R'.B x = s)
      (hRR' : Nonempty (BipolarBoundaryBaseIso R.B R'.B)) :
      Nonempty (BipolarBoundaryBaseIso (cutL R hR).2.B (cutL R' hR').2.B) ∧
      Nonempty (BipolarBoundaryBaseIso (cutR R hR).2.B (cutR R' hR').2.B)
  cutL_ML {n : ℕ} (R : KMSWMapRep ℓ r n)
      (hR : xdpLengthBase R.B x = s) :
      IsMLRepresentative x (cutL R hR).2
  cutR_MR {n : ℕ} (R : KMSWMapRep ℓ r n)
      (hR : xdpLengthBase R.B x = s) :
      IsMRRepresentative x (cutR R hR).2
  cut_edges {n : ℕ} (R : KMSWMapRep ℓ r n)
      (hR : xdpLengthBase R.B x = s) :
      (cutL R hR).1 + (cutR R hR).1 = n + s
  cut_glue {a b : ℕ} (A : KMSWMapRep ℓ s a) (B : KMSWMapRep s r b)
      (hA : IsMLRepresentative x A) (hB : IsMRRepresentative x B) :
      Nonempty (BipolarBoundaryBaseIso
        (cutL (glue A B hA hB) (glue_len A B hA hB)).2.B A.B) ∧
      Nonempty (BipolarBoundaryBaseIso
        (cutR (glue A B hA hB) (glue_len A B hA hB)).2.B B.B)
  glue_cut {n : ℕ} (R : KMSWMapRep ℓ r n)
      (hR : xdpLengthBase R.B x = s) :
      Nonempty (BipolarBoundaryBaseIso
        (glue (cutL R hR).2 (cutR R hR).2 (cutL_ML R hR) (cutR_MR R hR)).B R.B)

private noncomputable def repOfClass {ℓ r n : ℕ}
    (q : KMSWMapIsoClass ℓ r n) : KMSWMapRep ℓ r n := Quotient.out q

private theorem mk_repOfClass {ℓ r n : ℕ} (q : KMSWMapIsoClass ℓ r n) :
    KMSWMapIsoClass.mk (repOfClass q) = q := Quotient.out_eq q

private theorem boltzmannSpace_eq_of_iso {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (R' : KMSWMapRep ℓ r m)
    (h : Nonempty (BipolarBoundaryBaseIso R.B R'.B)) :
    (⟨n, KMSWMapIsoClass.mk R⟩ : BoltzmannSpace ℓ r) =
      ⟨m, KMSWMapIsoClass.mk R'⟩ := by
  have hnm : n = m := by
    rcases h with ⟨I⟩
    have hn := I.numEdges_eq
    rw [R.edges, R'.edges] at hn
    exact hn
  subst m
  exact congrArg
    (fun q : KMSWMapIsoClass ℓ r n =>
      (⟨n, q⟩ : BoltzmannSpace ℓ r))
    ((KMSWMapIsoClass.mk_eq_mk_iff R R').2 h)

private theorem mlRep_repOfClass {x : XDP} {ℓ s n : ℕ}
    (q : KMSWMapIsoClass ℓ s n) (h : IsMLClass x q) :
    IsMLRepresentative x (repOfClass q) := by
  have h' : IsMLClass x (KMSWMapIsoClass.mk (repOfClass q)) := by
    rw [mk_repOfClass]
    exact h
  simpa using h'

private theorem mrRep_repOfClass {x : XDP} {s r n : ℕ}
    (q : KMSWMapIsoClass s r n) (h : IsMRClass x q) :
    IsMRRepresentative x (repOfClass q) := by
  have h' : IsMRClass x (KMSWMapIsoClass.mk (repOfClass q)) := by
    rw [mk_repOfClass]
    exact h
  simpa using h'

private noncomputable def lrGlueValue {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (a : {mL : BoltzmannSpace ℓ s // IsML x mL})
    (b : {mR : BoltzmannSpace s r // IsMR x mR}) :
    {m : BoltzmannSpace ℓ r // xdpLen x m = s} := by
  let A := repOfClass a.1.2
  let B := repOfClass b.1.2
  let hA := mlRep_repOfClass a.1.2 a.2
  let hB := mrRep_repOfClass b.1.2 b.2
  let G := d.glue A B hA hB
  refine ⟨⟨a.1.1 + b.1.1 - s, KMSWMapIsoClass.mk G⟩, ?_⟩
  change xdpLenClass x (KMSWMapIsoClass.mk G) = s
  rw [xdpLenClass_mk]
  exact d.glue_len A B hA hB

private noncomputable def lrCutValue {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (z : {m : BoltzmannSpace ℓ r // xdpLen x m = s}) :
    ({mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) := by
  rcases z with ⟨⟨n, q⟩, hz⟩
  let R := repOfClass q
  have hR : xdpLengthBase R.B x = s := by
    have hlen := hz
    change xdpLenClass x q = s at hlen
    rw [← mk_repOfClass q, xdpLenClass_mk] at hlen
    exact hlen
  let L := d.cutL R hR
  let T := d.cutR R hR
  have hL : IsML x (⟨L.1, KMSWMapIsoClass.mk L.2⟩ : BoltzmannSpace ℓ s) := by
    change IsMLClass x (KMSWMapIsoClass.mk L.2)
    rw [IsMLClass_mk]
    exact d.cutL_ML R hR
  have hT : IsMR x (⟨T.1, KMSWMapIsoClass.mk T.2⟩ : BoltzmannSpace s r) := by
    change IsMRClass x (KMSWMapIsoClass.mk T.2)
    rw [IsMRClass_mk]
    exact d.cutR_MR R hR
  exact (⟨⟨L.1, KMSWMapIsoClass.mk L.2⟩, hL⟩,
    ⟨⟨T.1, KMSWMapIsoClass.mk T.2⟩, hT⟩)





noncomputable def lrClassEquiv {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r) :
    ({mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) ≃
    {m : BoltzmannSpace ℓ r // xdpLen x m = s} where
  toFun := fun p => lrGlueValue d p.1 p.2
  invFun := lrCutValue d
  left_inv := by
    intro p
    rcases p with ⟨a, b⟩
    change lrCutValue d (lrGlueValue d a b) = (a, b)
    let A := repOfClass a.1.2
    let B := repOfClass b.1.2
    let hA := mlRep_repOfClass a.1.2 a.2
    let hB := mrRep_repOfClass b.1.2 b.2
    let G := d.glue A B hA hB
    let z := lrGlueValue d a b
    let H := repOfClass z.1.2
    have hH : xdpLengthBase H.B x = s := by
      have hz := z.2
      change xdpLenClass x z.1.2 = s at hz
      rw [← mk_repOfClass z.1.2, xdpLenClass_mk] at hz
      exact hz
    have hclass : KMSWMapIsoClass.mk H = KMSWMapIsoClass.mk G := by
      simpa [H, z, lrGlueValue] using
        (mk_repOfClass (KMSWMapIsoClass.mk G))
    have hHG : Nonempty (BipolarBoundaryBaseIso H.B G.B) :=
      (KMSWMapIsoClass.mk_eq_mk_iff H G).1 hclass
    have hcut := d.cut_iso (R := H) (R' := G) hH
      (d.glue_len A B hA hB) hHG
    have hcutG := d.cut_glue A B hA hB
    apply Prod.ext
    · apply Subtype.ext
      change (⟨(d.cutL H hH).1,
        KMSWMapIsoClass.mk (d.cutL H hH).2⟩ : BoltzmannSpace ℓ s) = a.1
      have hfirst :
          (⟨(d.cutL H hH).1, KMSWMapIsoClass.mk (d.cutL H hH).2⟩ :
            BoltzmannSpace ℓ s) =
          (⟨a.1.1, KMSWMapIsoClass.mk A⟩ : BoltzmannSpace ℓ s) :=
        boltzmannSpace_eq_of_iso (d.cutL H hH).2 A
          (hcut.1.elim fun I => hcutG.1.elim fun J => ⟨I.trans J⟩)
      have hsecond :
          (⟨a.1.1, KMSWMapIsoClass.mk A⟩ : BoltzmannSpace ℓ s) = a.1 :=
        congrArg (fun q : KMSWMapIsoClass ℓ s a.1.1 =>
          (⟨a.1.1, q⟩ : BoltzmannSpace ℓ s)) (mk_repOfClass a.1.2)
      exact hfirst.trans hsecond
    · apply Subtype.ext
      change (⟨(d.cutR H hH).1,
        KMSWMapIsoClass.mk (d.cutR H hH).2⟩ : BoltzmannSpace s r) = b.1
      have hfirst :
          (⟨(d.cutR H hH).1, KMSWMapIsoClass.mk (d.cutR H hH).2⟩ :
            BoltzmannSpace s r) =
          (⟨b.1.1, KMSWMapIsoClass.mk B⟩ : BoltzmannSpace s r) :=
        boltzmannSpace_eq_of_iso (d.cutR H hH).2 B
          (hcut.2.elim fun I => hcutG.2.elim fun J => ⟨I.trans J⟩)
      have hsecond :
          (⟨b.1.1, KMSWMapIsoClass.mk B⟩ : BoltzmannSpace s r) = b.1 :=
        congrArg (fun q : KMSWMapIsoClass s r b.1.1 =>
          (⟨b.1.1, q⟩ : BoltzmannSpace s r)) (mk_repOfClass b.1.2)
      exact hfirst.trans hsecond
  right_inv := by
    intro z
    rcases z with ⟨⟨n, q⟩, hz⟩
    let H := repOfClass q
    have hH : xdpLengthBase H.B x = s := by
      have hlen := hz
      change xdpLenClass x q = s at hlen
      rw [← mk_repOfClass q, xdpLenClass_mk] at hlen
      exact hlen
    let L := d.cutL H hH
    let T := d.cutR H hH
    let hL := d.cutL_ML H hH
    let hT := d.cutR_MR H hH
    let a : {mL : BoltzmannSpace ℓ s // IsML x mL} :=
      ⟨⟨L.1, KMSWMapIsoClass.mk L.2⟩, by
        change IsMLClass x (KMSWMapIsoClass.mk L.2)
        rw [IsMLClass_mk]
        exact hL⟩
    let b : {mR : BoltzmannSpace s r // IsMR x mR} :=
      ⟨⟨T.1, KMSWMapIsoClass.mk T.2⟩, by
        change IsMRClass x (KMSWMapIsoClass.mk T.2)
        rw [IsMRClass_mk]
        exact hT⟩
    let A := repOfClass a.1.2
    let B := repOfClass b.1.2
    let hA := mlRep_repOfClass a.1.2 a.2
    let hB := mrRep_repOfClass b.1.2 b.2
    let G := d.glue A B hA hB
    have hAL : Nonempty (BipolarBoundaryBaseIso A.B L.2.B) :=
      (KMSWMapIsoClass.mk_eq_mk_iff A L.2).1 (mk_repOfClass a.1.2)
    have hBT : Nonempty (BipolarBoundaryBaseIso B.B T.2.B) :=
      (KMSWMapIsoClass.mk_eq_mk_iff B T.2).1 (mk_repOfClass b.1.2)
    have hGL : Nonempty (BipolarBoundaryBaseIso G.B
        (d.glue L.2 T.2 hL hT).B) :=
      d.glue_iso hA hL hB hT hAL hBT
    have hcutGlue := d.glue_cut H hH
    have hGR : Nonempty (BipolarBoundaryBaseIso G.B H.B) :=
      hGL.elim fun I => hcutGlue.elim fun J => ⟨I.trans J⟩
    apply Subtype.ext
    change (⟨L.1 + T.1 - s, KMSWMapIsoClass.mk G⟩ :
      BoltzmannSpace ℓ r) = ⟨n, q⟩
    calc
      (⟨L.1 + T.1 - s, KMSWMapIsoClass.mk G⟩ : BoltzmannSpace ℓ r) =
          ⟨a.1.1 + b.1.1 - s, KMSWMapIsoClass.mk G⟩ := by rfl
      _ = ⟨n, KMSWMapIsoClass.mk H⟩ := boltzmannSpace_eq_of_iso G H hGR
      _ = ⟨n, q⟩ := by
        exact congrArg (fun c : KMSWMapIsoClass ℓ r n =>
          (⟨n, c⟩ : BoltzmannSpace ℓ r)) (mk_repOfClass q)

private theorem boltzmannWeight_pow_sub (a b s : ℕ)
    (h : (a + b - s) + s = a + b) :
    (1 / 3 : ℝ≥0∞) ^ (a + b - s) =
      (3 : ℝ≥0∞) ^ s * (1 / 3 : ℝ≥0∞) ^ a *
        (1 / 3 : ℝ≥0∞) ^ b := by
  have hleft : (1 / 3 : ℝ≥0∞) ^ (a + b - s) ≠ ⊤ :=
    ENNReal.pow_ne_top (by norm_num)
  have hright :
      (3 : ℝ≥0∞) ^ s * (1 / 3 : ℝ≥0∞) ^ a *
        (1 / 3 : ℝ≥0∞) ^ b ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
        (ENNReal.pow_ne_top (by norm_num))
    · exact ENNReal.pow_ne_top (by norm_num)
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).1
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  simp only [div_pow, one_pow]
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  field_simp
  rw [← pow_add, ← pow_add, h]





theorem lrClassEquiv_weight {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (a : {mL : BoltzmannSpace ℓ s // IsML x mL})
    (b : {mR : BoltzmannSpace s r // IsMR x mR}) :
    boltzmannWeight (lrClassEquiv d (a, b)).1 =
      (3 : ℝ≥0∞) ^ s * boltzmannWeight a.1 * boltzmannWeight b.1 := by
  let A := repOfClass a.1.2
  let B := repOfClass b.1.2
  let hA := mlRep_repOfClass a.1.2 a.2
  let hB := mrRep_repOfClass b.1.2 b.2
  have hedge := d.glue_edges A B hA hB
  change (1 / 3 : ℝ≥0∞) ^ (a.1.1 + b.1.1 - s) =
    (3 : ℝ≥0∞) ^ s * (1 / 3 : ℝ≥0∞) ^ a.1.1 *
      (1 / 3 : ℝ≥0∞) ^ b.1.1
  exact boltzmannWeight_pow_sub a.1.1 b.1.1 s hedge

local instance instMeasurableSpaceLRML {x : XDP} {ℓ s : ℕ} :
    MeasurableSpace {mL : BoltzmannSpace ℓ s // IsML x mL} := ⊤
local instance instMeasurableSpaceLRMR {x : XDP} {s r : ℕ} :
    MeasurableSpace {mR : BoltzmannSpace s r // IsMR x mR} := ⊤
local instance instMeasurableSpaceLRFiber {x : XDP} {ℓ r s : ℕ} :
    MeasurableSpace {m : BoltzmannSpace ℓ r // xdpLen x m = s} := ⊤





theorem lem_lr_ind_of_repData {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (hC0 : boltzmannPartition ℓ r ≠ 0)
    (hCtop : boltzmannPartition ℓ r ≠ ⊤)
    (hZA0 : (∑' a : {mL : BoltzmannSpace ℓ s // IsML x mL},
      boltzmannWeight a.1) ≠ 0)
    (hZAtop : (∑' a : {mL : BoltzmannSpace ℓ s // IsML x mL},
      boltzmannWeight a.1) ≠ ⊤)
    (hZB0 : (∑' b : {mR : BoltzmannSpace s r // IsMR x mR},
      boltzmannWeight b.1) ≠ 0)
    (hZBtop : (∑' b : {mR : BoltzmannSpace s r // IsMR x mR},
      boltzmannWeight b.1) ≠ ⊤)
    (hL0 : boltzmannPartition ℓ s ≠ 0)
    (hLtop : boltzmannPartition ℓ s ≠ ⊤)
    (hR0 : boltzmannPartition s r ≠ 0)
    (hRtop : boltzmannPartition s r ≠ ⊤)
    (default : {mL : BoltzmannSpace ℓ s // IsML x mL} ×
      {mR : BoltzmannSpace s r // IsMR x mR}) :
    ProbabilityTheory.IndepFun
      (boltzmannLRLeftCutOutput ℓ s r x (lrClassEquiv d) default)
      (boltzmannLRRightCutOutput ℓ s r x (lrClassEquiv d) default)
      ((boltzmannLaw ℓ r hC0 hCtop)[|
        boltzmannFiber (ℓ := ℓ) (r := r) x s]) ∧
    Measure.map
        (Subtype.val ∘ boltzmannLRLeftCutOutput ℓ s r x
          (lrClassEquiv d) default)
        ((boltzmannLaw ℓ r hC0 hCtop)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]) =
      (boltzmannLaw ℓ s hL0 hLtop)[|{mL | IsML x mL}] ∧
    Measure.map
        (Subtype.val ∘ boltzmannLRRightCutOutput ℓ s r x
          (lrClassEquiv d) default)
        ((boltzmannLaw ℓ r hC0 hCtop)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]) =
      (boltzmannLaw s r hR0 hRtop)[|{mR | IsMR x mR}] := by
  apply boltzmannLaw_cond_fiber_IndepFun ℓ s r x
    hC0 hCtop hZA0 hZAtop hZB0 hZBtop hL0 hLtop hR0 hRtop
    (lrClassEquiv d)
  · intro a b
    exact lrClassEquiv_weight d a b




theorem lrClassEquiv_symm_fst {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (m : BoltzmannSpace ℓ r) (hm : xdpLen x m = s) :
    let R : KMSWMapRep ℓ r m.1 := Quotient.out m.2
    let hR : xdpLengthBase R.B x = s := by
      have h := hm
      change xdpLenClass x m.2 = s at h
      have hout : KMSWMapIsoClass.mk R = m.2 := Quotient.out_eq m.2
      rw [← hout, xdpLenClass_mk] at h
      exact h
    let L := d.cutL R hR
    let hL : IsML x (⟨L.1, KMSWMapIsoClass.mk L.2⟩ : BoltzmannSpace ℓ s) := by
      change IsMLClass x (KMSWMapIsoClass.mk L.2)
      rw [IsMLClass_mk]
      exact d.cutL_ML R hR
    ((lrClassEquiv d).symm ⟨m, hm⟩).1 = ⟨⟨L.1,
      KMSWMapIsoClass.mk L.2⟩, hL⟩ := by
  dsimp only [lrClassEquiv, Equiv.symm, lrCutValue]
  apply Subtype.ext
  rfl




theorem lrClassEquiv_symm_snd {x : XDP} {ℓ s r : ℕ}
    (d : LRCutGlueRepData x ℓ s r)
    (m : BoltzmannSpace ℓ r) (hm : xdpLen x m = s) :
    let R : KMSWMapRep ℓ r m.1 := Quotient.out m.2
    let hR : xdpLengthBase R.B x = s := by
      have h := hm
      change xdpLenClass x m.2 = s at h
      have hout : KMSWMapIsoClass.mk R = m.2 := Quotient.out_eq m.2
      rw [← hout, xdpLenClass_mk] at h
      exact h
    let T := d.cutR R hR
    let hT : IsMR x (⟨T.1, KMSWMapIsoClass.mk T.2⟩ : BoltzmannSpace s r) := by
      change IsMRClass x (KMSWMapIsoClass.mk T.2)
      rw [IsMRClass_mk]
      exact d.cutR_MR R hR
    ((lrClassEquiv d).symm ⟨m, hm⟩).2 = ⟨⟨T.1,
      KMSWMapIsoClass.mk T.2⟩, hT⟩ := by
  dsimp only [lrClassEquiv, Equiv.symm, lrCutValue]
  apply Subtype.ext
  rfl

end DirectedDistances.PlanarMap
