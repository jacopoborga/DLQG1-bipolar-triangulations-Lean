/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusCanonicalCodingMeasurable4

/-! Measurable finite interface and adjusted rotation toward Lemma 5.5 -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime
local notation "Fz" z => kmswStage (Prod.fst (RMinusSidePresentation.code (Prod.fst (Subtype.val z)))) (Exists.choose (And.left (Subtype.property z)))
local notation "Mz" z => geometricSideSubmap _ renewalTime renewalTime_positiveSuccessTime ThinMapSide.right (Prod.snd (Subtype.val z))
local notation "Sz" z => rMinusCanonicalSide (Prod.fst (RMinusSidePresentation.code (Prod.fst (Subtype.val z)))) (Exists.choose (And.left (Subtype.property z))) (Prod.snd (Subtype.val z))

/-- Helper toward Lemma 5.5. Ambient finite-interface coordinates, with a
fixed value outside the allocated interface. -/
@[expose] def rMinusBoundaryCornerEntry (F : State) (a : ℕ × Bool) : ℕ × Bool :=
  if h : a.1 < (F.active :: F.UR).length then
    let b := rMinusBoundaryCornerPerm (F.active :: F.UR).length (⟨a.1, h⟩, a.2)
    (b.1.val, b.2)
  else (0, false)

/-- Helper toward Lemma 5.5. The canonical coordinate of a finite-interface
port, defined for every ambient index. -/
@[expose] noncomputable def rMinusCertifiedBoundaryPort (x : XDP)
    (z : RMinusCanonicalCertifiedPairs x) (a : ℕ × Bool) : ℕ × Bool :=
  (rMinusRawTokenEqvGenMinimum x z
    (2 * ((Fz z).active :: (Fz z).UR)[a.1]?.getD 0), a.2)

/-- Helper toward Lemma 5.5. Every finite-interface port is measurable. -/
theorem measurable_rMinusCertifiedBoundaryPort (x : XDP) (a : ℕ × Bool) :
    Measurable (fun z => rMinusCertifiedBoundaryPort x z a) :=
  (measurable_rMinusCertifiedEdgeMinimum_eval x _
    (measurable_rMinusCertifiedStage_reader x
      (fun F => 2 * (F.active :: F.UR)[a.1]?.getD 0))).prodMk measurable_const

/-- Helper toward Lemma 5.5. Allocated interface ports have exactly their
intrinsic canonical dart coordinate. -/
theorem rMinusCertifiedBoundaryPort_eq (x : XDP) (z : RMinusCanonicalCertifiedPairs x)
    (a : StageDart ((Fz z).active :: (Fz z).UR).length) :
    rMinusCertifiedBoundaryPort x z (a.1.val, a.2) =
      rMinusCanonicalDartId (Fz z) (Mz z)
        (rMinusCodeBoundaryDart z.1.1.code.1 z.property.1.choose (Mz z) a) := by
  simpa only [rMinusCertifiedBoundaryPort, rMinusCodeBoundaryDart, rMinusCertifiedDartId,
    rMinusPrefixBoundaryDart, Bool.false_eq_true, ↓reduceIte,
    List.getElem?_eq_getElem a.1.isLt, Option.getD_some] using
    rMinusCertifiedDartId_prefix x z
      (rMinusPrefixBoundaryDart z.1.1.code.1 z.property.1.choose a)

/-- Helper toward Lemma 5.5. The finite corner graph has a countable
certificate, retaining its endpoint ports and interior transpositions. -/
theorem measurableSet_rMinusCertified_boundaryCornerGraph (x : XDP) (d e : ℕ × Bool) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      rMinusEncodedPermGraph
        (rMinusCanonicalDartId (Fz z) (Mz z) ∘
          rMinusCodeBoundaryDart z.1.1.code.1 z.property.1.choose (Mz z))
        (rMinusBoundaryCornerPerm ((Fz z).active :: (Fz z).UR).length) d e} := by
  have he : {z : RMinusCanonicalCertifiedPairs x |
      rMinusEncodedPermGraph
        (rMinusCanonicalDartId (Fz z) (Mz z) ∘
          rMinusCodeBoundaryDart z.1.1.code.1 z.property.1.choose (Mz z))
        (rMinusBoundaryCornerPerm ((Fz z).active :: (Fz z).UR).length) d e} =
      {z | ∃ a b : ℕ × Bool,
        a.1 < ((Fz z).active :: (Fz z).UR).length ∧
        b.1 < ((Fz z).active :: (Fz z).UR).length ∧
        rMinusCertifiedBoundaryPort x z a = d ∧
        rMinusCertifiedBoundaryPort x z b = e ∧
        rMinusBoundaryCornerEntry (Fz z) a = b} := by
    ext z
    constructor
    · rintro ⟨a, ha, hb⟩
      let b := rMinusBoundaryCornerPerm ((Fz z).active :: (Fz z).UR).length a
      exact ⟨(a.1.val, a.2), (b.1.val, b.2), a.1.isLt, b.1.isLt,
        (rMinusCertifiedBoundaryPort_eq x z a).trans ha,
        (rMinusCertifiedBoundaryPort_eq x z b).trans hb,
        by simp only [rMinusBoundaryCornerEntry, dite_eq_left a.1.isLt]; rfl⟩
    · rintro ⟨a, b, ham, hbm, ha, hb, hr⟩
      let A : StageDart ((Fz z).active :: (Fz z).UR).length := (⟨a.1, ham⟩, a.2)
      let B : StageDart ((Fz z).active :: (Fz z).UR).length := (⟨b.1, hbm⟩, b.2)
      have hrot : rMinusBoundaryCornerPerm ((Fz z).active :: (Fz z).UR).length A = B := by
        simp only [rMinusBoundaryCornerEntry, dite_eq_left ham] at hr
        exact Prod.ext (Fin.ext (congrArg Prod.fst hr))
          (congrArg (fun p : ℕ × Bool => p.2) hr)
      refine ⟨A, (rMinusCertifiedBoundaryPort_eq x z A).symm.trans ha, ?_⟩
      change rMinusCanonicalDartId (Fz z) (Mz z)
        (rMinusCodeBoundaryDart _ _ _ (rMinusBoundaryCornerPerm _ A)) = e
      rw [hrot]
      exact (rMinusCertifiedBoundaryPort_eq x z B).symm.trans hb
  have hlt (a : ℕ) : MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      a < ((Fz z).active :: (Fz z).UR).length} := by
    simpa only [decide_eq_true_eq] using
      ((measurable_rMinusCertifiedStage_reader x
        (fun F => decide (a < (F.active :: F.UR).length))).eq_const true).setOf
  rw [he]
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
    (hlt a.1).inter ((hlt b.1).inter
    (((measurable_rMinusCertifiedBoundaryPort x a).eq_const d).setOf.inter
    (((measurable_rMinusCertifiedBoundaryPort x b).eq_const e).setOf.inter
    ((measurable_rMinusCertifiedStage_reader x
      (fun F => rMinusBoundaryCornerEntry F a)).eq_const b).setOf)))))

/-- Helper toward Lemma 5.5. Countable-coordinate graph composition is
measurable even when the intrinsic carrier varies. -/
theorem measurableSet_rMinusEncodedPermGraph_mul
    {Ω γ : Type*} [MeasurableSpace Ω] [Countable γ]
    {A : Ω → Type*} (f : ∀ z, A z → γ) (hf : ∀ z, Function.Injective (f z))
    (p q : ∀ z, Equiv.Perm (A z))
    (hp : ∀ d e, MeasurableSet {z | rMinusEncodedPermGraph (f z) (p z) d e})
    (hq : ∀ d e, MeasurableSet {z | rMinusEncodedPermGraph (f z) (q z) d e})
    (d e : γ) :
    MeasurableSet {z | rMinusEncodedPermGraph (f z) (p z * q z) d e} := by
  have he : {z | rMinusEncodedPermGraph (f z) (p z * q z) d e} =
      ⋃ m : γ, {z | rMinusEncodedPermGraph (f z) (q z) d m} ∩
        {z | rMinusEncodedPermGraph (f z) (p z) m e} := by
    ext z
    simpa only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq] using
      rMinusEncodedPermGraph_mul (f z) (hf z) (p z) (q z) d e
  rw [he]
  exact MeasurableSet.iUnion fun m => (hq d m).inter (hp m e)

/-- Helper toward Lemma 5.5. The canonical dart range is exactly the
canonical edge carrier with either endpoint bit. -/
theorem measurableSet_rMinusCertified_dartRange (x : XDP) (d : ℕ × Bool) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      d ∈ Set.range (rMinusCanonicalDartId (Fz z) (Mz z))} := by
  have he : {z : RMinusCanonicalCertifiedPairs x |
      d ∈ Set.range (rMinusCanonicalDartId (Fz z) (Mz z))} =
      {z | d.1 ∈ (Sz z).edges} := by
    ext z
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a.1, congrArg Prod.fst ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨(a, d.2), Prod.ext ha rfl⟩
  rw [he]
  exact measurableSet_rMinusCertified_edges x d.1

/-- Helper toward Lemma 5.5. Graph measurability for any extension with
the specified image action and fixed complement. This is independent of the
decision procedure used to implement the finite embedded range. -/
theorem measurableSet_rMinusEncodedPermGraph_extension
    {Ω γ : Type*} [MeasurableSpace Ω] [Countable γ]
    {A B : Ω → Type*} (f : ∀ z, B z → γ) (hf : ∀ z, Function.Injective (f z))
    (j : ∀ z, A z → B z) (p : ∀ z, Equiv.Perm (A z)) (P : ∀ z, Equiv.Perm (B z))
    (himage : ∀ z a, P z (j z a) = j z (p z a))
    (hout : ∀ z b, b ∉ Set.range (j z) → P z b = b)
    (hrange : ∀ d, MeasurableSet {z | d ∈ Set.range (f z)})
    (hp : ∀ d e, MeasurableSet {z | rMinusEncodedPermGraph (f z ∘ j z) (p z) d e})
    (d e : γ) : MeasurableSet {z | rMinusEncodedPermGraph (f z) (P z) d e} := by
  have he : {z | rMinusEncodedPermGraph (f z) (P z) d e} =
      {z | rMinusEncodedPermGraph (f z ∘ j z) (p z) d e} ∪
        ({z | d = e} ∩ {z | d ∈ Set.range (f z)} ∩
          (⋃ m : γ, {z | rMinusEncodedPermGraph (f z ∘ j z) (p z) d m})ᶜ) := by
    ext z
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨b, hb, he⟩
      by_cases h : b ∈ Set.range (j z)
      · obtain ⟨a, rfl⟩ := h
        exact Or.inl ⟨a, hb, by change f z (j z (p z a)) = e; rw [← himage]; exact he⟩
      · refine Or.inr ⟨⟨hb.symm.trans ((hout z b h) ▸ he), b, hb⟩, ?_⟩
        rintro ⟨m, a, ha, _⟩
        exact h ⟨a, hf z (ha.trans hb.symm)⟩
    · rintro (⟨a, ha, he⟩ | ⟨⟨hde, b, hb⟩, hn⟩)
      · exact ⟨j z a, ha, by rw [himage]; exact he⟩
      · have h : b ∉ Set.range (j z) := by
          rintro ⟨a, rfl⟩
          exact hn ⟨f z (j z (p z a)), a, hb, rfl⟩
        exact ⟨b, hb, (congrArg (f z) (hout z b h)).trans (hb.trans hde)⟩
  rw [he]
  have hde : MeasurableSet {z : Ω | d = e} := by by_cases h : d = e <;> simp [h]
  exact (hp d e).union ((hde.inter (hrange d)).inter
    (MeasurableSet.iUnion (fun m => hp d m)).compl)

/-- Helper toward Lemma 5.5. The full three-factor splice graph is
measurable on the exact certified-pair carrier. -/
theorem measurableSet_rMinusCertified_spliceRotationGraph (x : XDP) (d e : ℕ × Bool) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      rMinusEncodedPermGraph (rMinusCanonicalDartId (Fz z) (Mz z))
        (rMinusCodeSpliceRotation z.1.1.code.1 z.property.1.choose z.1.2) d e} := by
  let f (z : RMinusCanonicalCertifiedPairs x) := rMinusCanonicalDartId (Fz z) (Mz z)
  have hf (z : RMinusCanonicalCertifiedPairs x) : Function.Injective (f z) :=
    rMinusCanonicalDartId_injective _ _
  let H (z : RMinusCanonicalCertifiedPairs x) := (rMinusHattedRotation x z.1.2).extendDomain
    (Equiv.ofInjective (rMinusCodeHattedDart (Fz z) (Mz z))
      (rMinusCodeHattedDart_injective z.1.1.code.1 z.property.1.choose z.1.2))
  let C (z : RMinusCanonicalCertifiedPairs x) :=
    (rMinusBoundaryCornerPerm ((Fz z).active :: (Fz z).UR).length).extendDomain
      (Equiv.ofInjective (rMinusCodeBoundaryDart z.1.1.code.1 z.property.1.choose (Mz z))
        (rMinusCodeBoundaryDart_injective z.1.1.code.1 z.property.1.choose z.1.2))
  let P (z : RMinusCanonicalCertifiedPairs x) :=
    (stageRot z.1.1.code.1 z.property.1.choose).extendDomain
      (Equiv.ofInjective (rMinusCodePrefixDart (Fz z) (Mz z))
        (rMinusCodePrefixDart_injective z.1.1.code.1 z.property.1.choose z.1.2))
  have hhat (d e) : MeasurableSet {z | rMinusEncodedPermGraph (f z) (H z) d e} :=
    measurableSet_rMinusEncodedPermGraph_extension f hf
      (fun z => rMinusCodeHattedDart (Fz z) (Mz z))
      (fun z => rMinusHattedRotation x z.1.2) H
      (fun z a => Equiv.Perm.extendDomain_apply_image _ _ a)
      (fun z b h => Equiv.Perm.extendDomain_apply_not_subtype _ _ h)
      (measurableSet_rMinusCertified_dartRange x)
      (measurableSet_rMinusCertified_hattedRotationGraph x) d e
  have hcorner (d e) : MeasurableSet {z | rMinusEncodedPermGraph (f z) (C z) d e} :=
    measurableSet_rMinusEncodedPermGraph_extension f hf
      (fun z => rMinusCodeBoundaryDart z.1.1.code.1 z.property.1.choose (Mz z))
      (fun z => rMinusBoundaryCornerPerm ((Fz z).active :: (Fz z).UR).length) C
      (fun z a => Equiv.Perm.extendDomain_apply_image _ _ a)
      (fun z b h => Equiv.Perm.extendDomain_apply_not_subtype _ _ h)
      (measurableSet_rMinusCertified_dartRange x)
      (measurableSet_rMinusCertified_boundaryCornerGraph x) d e
  have hpre (d e) : MeasurableSet {z | rMinusEncodedPermGraph (f z) (P z) d e} :=
    measurableSet_rMinusEncodedPermGraph_extension f hf
      (fun z => rMinusCodePrefixDart (Fz z) (Mz z))
      (fun z => stageRot z.1.1.code.1 z.property.1.choose) P
      (fun z a => Equiv.Perm.extendDomain_apply_image _ _ a)
      (fun z b h => Equiv.Perm.extendDomain_apply_not_subtype _ _ h)
      (measurableSet_rMinusCertified_dartRange x)
      (measurableSet_rMinusCertified_prefixRotationGraph x) d e
  exact measurableSet_rMinusEncodedPermGraph_mul f hf (fun z => H z * C z) P
    (measurableSet_rMinusEncodedPermGraph_mul f hf H C hhat hcorner) hpre d e

/-- Helper toward Lemma 5.5. Swaps of measurably located canonical ports
have measurable graphs on the full allocated dart range. -/
theorem measurableSet_rMinusEncodedPermGraph_swap
    {Ω : Type*} [MeasurableSpace Ω] {A : Ω → Type*}
    [∀ z, DecidableEq (A z)]
    (f : ∀ z, A z → ℕ × Bool) (hf : ∀ z, Function.Injective (f z))
    (a b : ∀ z, A z)
    (ha : Measurable (fun z => f z (a z)))
    (hb : Measurable (fun z => f z (b z)))
    (hrange : ∀ d, MeasurableSet {z | d ∈ Set.range (f z)})
    (d e : ℕ × Bool) :
    MeasurableSet {z | rMinusEncodedPermGraph (f z) (Equiv.swap (a z) (b z)) d e} := by
  have he : {z | rMinusEncodedPermGraph (f z) (Equiv.swap (a z) (b z)) d e} =
      {z | d = f z (a z)} ∩ {z | e = f z (b z)} ∪
      ({z | d = f z (b z)} ∩ {z | e = f z (a z)} ∪
      ({z | d = f z (a z)}ᶜ ∩ {z | d = f z (b z)}ᶜ ∩
        {z | d = e} ∩ {z | d ∈ Set.range (f z)})) := by
    ext z
    simpa only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_ofPred_eq, and_assoc] using
      rMinusEncodedPermGraph_swap (f z) (hf z) (a z) (b z) d e
  rw [he]
  have had := ((measurable_const : Measurable (fun _ : Ω => d)).eq ha).setOf
  have hae := ((measurable_const : Measurable (fun _ : Ω => e)).eq ha).setOf
  have hbd := ((measurable_const : Measurable (fun _ : Ω => d)).eq hb).setOf
  have hbe := ((measurable_const : Measurable (fun _ : Ω => e)).eq hb).setOf
  have hde : MeasurableSet {z : Ω | d = e} := by by_cases h : d = e <;> simp [h]
  exact (had.inter hbe).union ((hbd.inter hae).union
    (((had.compl.inter hbd.compl).inter hde).inter (hrange d)))

/-- Helper toward Lemma 5.5. Evaluation of a countable family of measurable
canonical dart coordinates at a measurable ambient dart is measurable. -/
theorem measurable_rMinusCertifiedDartId_eval (x : XDP) (hat : Bool)
    (a : RMinusCanonicalCertifiedPairs x → ℕ × Bool) (ha : Measurable a) :
    Measurable (fun z => rMinusCertifiedDartId x z hat (a z)) :=
  (measurable_from_prod_countable_left
    (f := fun p : RMinusCanonicalCertifiedPairs x × (ℕ × Bool) =>
      rMinusCertifiedDartId x p.1 hat p.2)
    (measurable_rMinusCertifiedDartId x hat)).comp (measurable_id.prodMk ha)

/-- Helper toward Lemma 5.5. The prefix successor of the initial shared
port has measurable canonical coordinates. -/
theorem measurable_rMinusCertified_initialSuccessor (x : XDP) :
    Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      rMinusCanonicalDartId (Fz z) (Mz z)
        (rMinusCodePrefixDart (Fz z) (Mz z)
          (stageRot z.1.1.code.1 z.property.1.choose
            (rMinusPrefixBoundaryDart z.1.1.code.1 z.property.1.choose
              (⟨0, by simp⟩, false))))) := by
  let a (z : RMinusCanonicalCertifiedPairs x) : ℕ × Bool := ((Fz z).active, false)
  have ha : Measurable a :=
    (measurable_rMinusCertifiedStage_reader x State.active).prodMk measurable_const
  have hr : Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      finiteRotationEntry z.1.1.code.1 z.property.1.choose (a z)) :=
    (measurable_from_prod_countable_left
      (f := fun p : RMinusCanonicalCertifiedPairs x × (ℕ × Bool) =>
        finiteRotationEntry p.1.1.1.code.1 p.1.property.1.choose p.2)
      (measurable_rMinusCertified_prefixRotation x)).comp (measurable_id.prodMk ha)
  have hm := measurable_rMinusCertifiedDartId_eval x false _ hr
  convert hm using 1
  funext z
  have hlt : (Fz z).active < (Fz z).nextEdge := act_lt_nextEdge _ (le_refl _)
  simpa only [finiteRotationEntry, a, dite_eq_left hlt, rMinusPrefixBoundaryDart,
    List.getElem_cons_zero] using
    (rMinusCertifiedDartId_prefix x z
      (stageRot z.1.1.code.1 z.property.1.choose
        (⟨(Fz z).active, hlt⟩, false))).symm

/-- Helper toward Lemma 5.5. The conjugating initial swap is measurable;
both of its ports retain their intrinsic canonical coordinates. -/
theorem measurableSet_rMinusCertified_initialSwapGraph (x : XDP) (d e : ℕ × Bool) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      let a := rMinusCodeBoundaryDart z.1.1.code.1 z.property.1.choose (Mz z)
        (⟨0, by simp⟩, false)
      let b := rMinusCodePrefixDart (Fz z) (Mz z)
        (stageRot z.1.1.code.1 z.property.1.choose
          (rMinusPrefixBoundaryDart z.1.1.code.1 z.property.1.choose
            (⟨0, by simp⟩, false)))
      rMinusEncodedPermGraph (rMinusCanonicalDartId (Fz z) (Mz z))
        (Equiv.swap a b) d e} := by
  apply measurableSet_rMinusEncodedPermGraph_swap _
    (fun z => rMinusCanonicalDartId_injective (Fz z) (Mz z))
    _ _ ?_ (measurable_rMinusCertified_initialSuccessor x)
    (measurableSet_rMinusCertified_dartRange x) d e
  convert measurable_rMinusCertifiedBoundaryPort x (0, false) using 1
  funext z
  exact (rMinusCertifiedBoundaryPort_eq x z (⟨0, by simp⟩, false)).symm

/-- Helper toward Lemma 5.5. Rotation in the canonical side is the encoded
initially adjusted permutation graph. -/
theorem rMinusCertified_rotation_iff (x : XDP) (z : RMinusCanonicalCertifiedPairs x)
    (d e : ℕ × Bool) :
    (Sz z).rotation d e ↔
      rMinusEncodedPermGraph (rMinusCanonicalDartId (Fz z) (Mz z))
        (rMinusCodeInitialAdjustedRotation z.1.1.code.1 z.property.1.choose z.1.2) d e := by
  constructor
  · rintro ⟨a, b, ha, hb, hr⟩
    exact ⟨a, ha, hr ▸ hb⟩
  · rintro ⟨a, ha, hb⟩
    exact ⟨a, _, ha, hb, rfl⟩

/-- Helper toward Lemma 5.5. Every exact canonical rotation coordinate is
measurable, including the finite corner and initial conjugation. -/
theorem measurableSet_rMinusCertified_rotation (x : XDP) (d e : ℕ × Bool) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x | (Sz z).rotation d e} := by
  have he : {z : RMinusCanonicalCertifiedPairs x | (Sz z).rotation d e} =
      {z : RMinusCanonicalCertifiedPairs x |
        rMinusEncodedPermGraph (rMinusCanonicalDartId (Fz z) (Mz z))
          (rMinusCodeInitialAdjustedRotation z.1.1.code.1 z.property.1.choose z.1.2) d e} :=
    Set.ext (fun z => rMinusCertified_rotation_iff x z d e)
  rw [he]
  unfold rMinusCodeInitialAdjustedRotation
  exact measurableSet_rMinusEncodedPermGraph_mul _
    (fun z => rMinusCanonicalDartId_injective (Fz z) (Mz z)) _ _
    (measurableSet_rMinusEncodedPermGraph_mul _
      (fun z => rMinusCanonicalDartId_injective (Fz z) (Mz z)) _ _
      (measurableSet_rMinusCertified_initialSwapGraph x)
      (measurableSet_rMinusCertified_spliceRotationGraph x))
    (measurableSet_rMinusCertified_initialSwapGraph x) d e

/-- Helper toward Lemma 5.5. The full marked canonical code is measurable
on its exact certification domain. -/
theorem measurable_rMinusCanonicalSide_codeOnCertifiedPairs (x : XDP) :
    MeasurableSet {z : RMinusSidePresentation x × Coherent x |
      z.1.prefixValid ∧ thinSideCode x renewalTime renewalTime_positiveSuccessTime
        .right z.2.1 = z.1.code.2} ∧
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => geometricSideCode (Sz z)) := by
  refine ⟨measurableSet_rMinusCanonicalSide_certifiedDomain x, ?_⟩
  have hdec (P : RMinusCanonicalCertifiedPairs x → Prop)
      (hP : MeasurableSet {z | P z}) : Measurable (fun z => decide (P z)) := by
    apply measurable_to_bool
    simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using hP
  have hV := measurable_pi_iff.mpr (fun n => hdec _ (measurableSet_rMinusCertified_vertices x n))
  have hE := measurable_pi_iff.mpr (fun n => hdec _ (measurableSet_rMinusCertified_edges x n))
  have hW := measurable_pi_iff.mpr (measurable_rMinusCertified_endpoint x false)
  have hX := measurable_pi_iff.mpr (measurable_rMinusCertified_endpoint x true)
  have hP := measurable_pi_iff.mpr (fun n => hdec _ (measurableSet_rMinusCertified_present x n))
  have hR := measurable_pi_iff.mpr (fun d => measurable_pi_iff.mpr
    (fun e => hdec _ (measurableSet_rMinusCertified_rotation x d e)))
  have hF := measurable_pi_iff.mpr (fun d => measurable_pi_iff.mpr
    (fun e => hdec _ (measurableSet_rMinusCertified_faceNext x d e)))
  have hB := measurable_pi_iff.mpr (measurable_rMinusCertified_boundary x)
  have hS := measurable_pi_iff.mpr (measurable_rMinusCertified_seam x)
  simpa only [geometricSideCode, rMinusCanonicalSide] using
    hV.prodMk (hE.prodMk (hW.prodMk (hX.prodMk (hP.prodMk
      (hR.prodMk (hF.prodMk ((measurable_rMinusCertified_root x).prodMk
        (hB.prodMk hS))))))))

/-- Helper toward Lemma 5.5. All canonical marked-field readers are
jointly measurable on certified pairs, including rotation. -/
theorem measurable_rMinusCanonicalSide_fieldsOnCertifiedPairs (x : XDP)
    (v e i : ℕ) (d f : ℕ × Bool) :
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => decide (v ∈ (Sz z).vertices)) ∧
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => decide (e ∈ (Sz z).edges)) ∧
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => ((Sz z).west v, (Sz z).east v)) ∧
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => decide (e ∈ (Sz z).present)) ∧
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => (Sz z).root) ∧
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => (Sz z).boundary i) ∧
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => (Sz z).seam i) ∧
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => decide ((Sz z).rotation d f)) ∧
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => decide ((Sz z).faceNext d f)) := by
  have hdec (P : RMinusCanonicalCertifiedPairs x → Prop)
      (hP : MeasurableSet {z | P z}) : Measurable (fun z => decide (P z)) := by
    apply measurable_to_bool
    change MeasurableSet {z : RMinusCanonicalCertifiedPairs x | decide (P z) = true}
    simpa only [decide_eq_true_eq] using hP
  refine ⟨hdec _ (measurableSet_rMinusCertified_vertices x v),
    hdec _ (measurableSet_rMinusCertified_edges x e), ?_,
    hdec _ (measurableSet_rMinusCertified_present x e),
    measurable_rMinusCertified_root x, measurable_rMinusCertified_boundary x i,
    measurable_rMinusCertified_seam x i, hdec _ (measurableSet_rMinusCertified_rotation x d f),
    hdec _ (measurableSet_rMinusCertified_faceNext x d f)⟩
  exact (measurable_rMinusCertified_endpoint x false v).prodMk
    (measurable_rMinusCertified_endpoint x true v)

/-- Helper toward Lemma 5.5. The exact raw certification set is measurable;
code agreement is checked on the coherent-path subtype. -/
theorem measurableSet_rMinusRawCanonicalDomain (x : XDP) :
    MeasurableSet {z : RMinusSidePresentation x × (ℕ → ℤ × ℤ) |
      z.1.prefixValid ∧ z.2 ∈ (Coherent x) ∧
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right z.2 =
          z.1.code.2} := by
  let C : Set (RMinusSidePresentation x × (ℕ → ℤ × ℤ)) :=
    {z | z.2 ∈ (Coherent x)}
  have hC : MeasurableSet C :=
    (selectedCutCoherentDomain_measurable_conull x renewalTime
      renewalTime_positiveSuccessTime).1.preimage measurable_snd
  let f (z : C) : RMinusSidePresentation x × Coherent x :=
    (z.1.1, ⟨z.1.2, z.2⟩)
  have hf : Measurable f :=
    (measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk)
  have hcert := (measurableSet_rMinusCanonicalSide_certifiedDomain x).preimage hf
  have him := MeasurableSet.subtype_image hC hcert
  have he : Subtype.val '' (f ⁻¹' {z : RMinusSidePresentation x × Coherent x |
      z.1.prefixValid ∧ thinSideCode x renewalTime renewalTime_positiveSuccessTime
        .right z.2.1 = z.1.code.2}) =
      {z : RMinusSidePresentation x × (ℕ → ℤ × ℤ) |
        z.1.prefixValid ∧ z.2 ∈ (Coherent x) ∧
          thinSideCode x renewalTime renewalTime_positiveSuccessTime .right z.2 = z.1.code.2} := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu.1, u.2, hu.2⟩
    · rintro ⟨hp, hq, hc⟩
      exact ⟨⟨z, hq⟩, ⟨hp, hc⟩, rfl⟩
  rwa [he] at him

/-- Helper toward Lemma 5.5. The raw optional canonical class is present
exactly on the original prefix/coherent-code certification domain. -/
@[expose] noncomputable def rMinusRawCanonicalClassOption (x : XDP)
    (z : RMinusSidePresentation x × (ℕ → ℤ × ℤ)) : Option GeometricSideClass :=
  if hp : z.1.prefixValid then
    if hq : z.2 ∈ (Coherent x) ∧
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right z.2 = z.1.code.2 then
      some (geometricSideClass (rMinusCanonicalSide z.1.code.1 hp.choose ⟨z.2, hq.1⟩))
    else none
  else none

/-- Helper toward Lemma 5.5. The guarded canonical class is measurable
without an extra measurability or identification premise. -/
theorem measurable_rMinusRawCanonicalClassOption (x : XDP) :
    Measurable (fun z : RMinusSidePresentation x × (ℕ → ℤ × ℤ) =>
      if hp : z.1.prefixValid then
        if hq : z.2 ∈ (Coherent x) ∧
            thinSideCode x renewalTime renewalTime_positiveSuccessTime .right z.2 = z.1.code.2 then
          some (geometricSideClass (rMinusCanonicalSide z.1.code.1 hp.choose ⟨z.2, hq.1⟩))
        else none
      else none) := by
  let D : Set (RMinusSidePresentation x × (ℕ → ℤ × ℤ)) :=
    {z | z.1.prefixValid ∧ z.2 ∈ (Coherent x) ∧
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right z.2 = z.1.code.2}
  let f (z : D) : RMinusCanonicalCertifiedPairs x :=
    ⟨(z.1.1, ⟨z.1.2, z.2.2.1⟩), z.2.1, z.2.2.2⟩
  have hf : Measurable f :=
    ((measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk)).subtype_mk
  have hside : Measurable (fun z : RMinusCanonicalCertifiedPairs x => Sz z) :=
    measurable_comap_iff.mpr (measurable_rMinusCanonicalSide_codeOnCertifiedPairs x).2
  have hclass : Measurable (fun z : D => some (geometricSideClass (Sz (f z)))) :=
    (measurable_some_geometricSideClass.comp (measurable_geometricSideClass.comp hside)).comp hf
  have hm := hclass.dite
    (measurable_const : Measurable (fun _ : {z // z ∉ D} => (none : Option GeometricSideClass)))
    (measurableSet_rMinusRawCanonicalDomain x)
  convert hm using 1
  funext z
  by_cases hp : z.1.prefixValid
  · by_cases hq : z.2 ∈ (Coherent x) ∧
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right z.2 = z.1.code.2
    · have hz : z ∈ D := ⟨hp, hq⟩
      simp only [dite_eq_left hp, dite_eq_left hq, dite_eq_left hz]
      rfl
    · have hn : ¬ z ∈ D := fun h => hq h.2
      simp only [dite_eq_left hp, dite_eq_right hq, dite_eq_right hn]
  · have hn : ¬ z ∈ D := fun h => hp h.1
    simp only [dite_eq_right hp, dite_eq_right hn]

/-- Helper toward Lemma 5.5. The source observation's exact R-minus class
reader is a.e. measurable at every nonpositive boundary index. -/
theorem aemeasurable_decodeRMinus_rightSideObsNonpos_classOption
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    AEMeasurable (fun W => (decodeRMinus x k (rightSideObsNonpos x k W)).classOption)
      wholePlaneIIDCodeMeasure := by
  have hm := (measurable_rMinusRawCanonicalClassOption x).comp_aemeasurable
    ((aemeasurable_decodeRMinus_rightSideObsNonpos x k).prodMk
      (aemeasurable_boundaryFutureHattedPath k))
  apply hm.congr
  filter_upwards [ae_decodeRMinus_rightSideObsNonpos_blocksRealization_isSome x k,
    (boundaryFutureThinSides_package x k).2.2.2.2.2] with W hb hq
  let r := decodeRMinus x k (rightSideObsNonpos x k W)
  have hp : r.prefixValid := by
    by_contra hn
    have hnone := (r.blocksRealization_eq_none_iff).mpr (Or.inl hn)
    rw [hnone] at hb
    cases hb
  have hcode : thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
      (boundaryFutureHattedPath k W) = r.code.2 := rfl
  have hex : ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 = r.code.2 :=
    ⟨⟨boundaryFutureHattedPath k W, hq⟩, hcode⟩
  change (if hp : r.prefixValid then
    if hq' : boundaryFutureHattedPath k W ∈ (Coherent x) ∧
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right
        (boundaryFutureHattedPath k W) = r.code.2 then
      some (geometricSideClass (rMinusCanonicalSide r.code.1 hp.choose
        ⟨boundaryFutureHattedPath k W, hq'.1⟩)) else none else none) = r.classOption
  rw [dite_eq_left hp, dite_eq_left ⟨hq, hcode⟩,
    r.classOption_eq_canonicalSide (show r.boundaryIndex ≤ 0 from hk) hp hex]
  exact congrArg some (rMinusCanonicalSide_class_eq_of_thinSideCode_eq x r.code.1 hp.choose
    ⟨boundaryFutureHattedPath k W, hq⟩ hex.choose (hcode.trans hex.choose_spec.symm))

/-- Helper toward Lemma 5.5. The exact R-minus class reader is a.e.
measurable under the observation law, by the established measurable descent. -/
theorem aemeasurable_RMinusSidePresentation_classOption
    (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    AEMeasurable (RMinusSidePresentation.classOption (x := x))
      (wholePlaneIIDCodeMeasure.map
        (fun W => decodeRMinus x k (rightSideObsNonpos x k W))) :=
  aemeasurable_RMinusSidePresentation_classOption_of_source x k
    (aemeasurable_decodeRMinus_rightSideObsNonpos_classOption x k hk) hk

end DirectedDistances.PaperProofs.Section5
