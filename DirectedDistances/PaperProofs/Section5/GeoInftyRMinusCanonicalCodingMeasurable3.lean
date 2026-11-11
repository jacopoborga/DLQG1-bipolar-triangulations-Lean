/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusCanonicalCodingMeasurable2

/-! raw-token gluing and its countable equivalence closure on certified pairs. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. A certified pair consists of a valid finite
prefix presentation and a coherent right path with the same right code. -/
abbrev RMinusCanonicalCertifiedPairs (x : XDP) :=
  {z : RMinusSidePresentation x × Coherent x //
    z.1.prefixValid ∧
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right z.2.1 =
        z.1.code.2}

/-- Helper toward Lemma 5.5. Fixed numeric raw-token gluing is measurable on
the certified pair space. The event is a countable union over the boundary
index, finite stopping frontier, and shared boundary-edge index. -/
theorem measurableSet_rMinusRawTokenGluingOnCertifiedPairs (x : XDP)
    (i j : ℕ) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      rMinusRawTokenGluing
        (kmswStage z.1.1.code.1 z.property.1.choose)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right z.1.2)
        i j} := by
  let side (q : Coherent x) :=
    geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
  have hcoords := measurable_rMinusSidePresentation_coordinates x
  have hindex : Measurable (fun r : RMinusSidePresentation x => r.boundaryIndex) :=
    measurable_fst.comp hcoords
  have hcode : Measurable (fun r : RMinusSidePresentation x => r.code) :=
    measurable_snd.comp hcoords
  have hprefix : Measurable (fun r : RMinusSidePresentation x => r.code.1) :=
    measurable_fst.comp hcode
  have hpath : Measurable (fun r : RMinusSidePresentation x =>
      rMinusPrefixPath r.code.1) := by
    apply measurable_pi_iff.mpr
    intro s
    by_cases hs : s = 0
    · simp [rMinusPrefixPath, hs]
    · simp only [rMinusPrefixPath, hs, ↓reduceIte]
      exact (measurable_pi_apply (s - 1)).comp hprefix
  have hstop (k : ℤ) (n : ℕ) :
      MeasurableSet {r : RMinusSidePresentation x |
        boundaryCodeStoppingTime k (rMinusPrefixPath r.code.1) = n} :=
    (((measurable_boundaryCodeStoppingTime k).comp hpath).eq_const n).setOf
  have hpad (n : ℕ) : MeasurableSet {r : RMinusSidePresentation x |
      ∀ s, n ≤ s → r.code.1 s = (0 : Fin 3)} := by
    have he : {r : RMinusSidePresentation x |
        ∀ s, n ≤ s → r.code.1 s = (0 : Fin 3)} =
        ⋂ s : ℕ, {r | n ≤ s → r.code.1 s = (0 : Fin 3)} := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [he]
    exact MeasurableSet.iInter fun s => by
      by_cases hs : n ≤ s
      · simpa only [hs, true_implies, Function.comp_apply] using
          (((measurable_pi_apply s).comp hprefix).eq_const (0 : Fin 3)).setOf
      · have he' : {r : RMinusSidePresentation x |
          n ≤ s → r.code.1 s = (0 : Fin 3)} = Set.univ := by
          ext r
          simp [hs]
        rw [he']
        exact MeasurableSet.univ
  have hstage (n t : ℕ) : Measurable (fun r : RMinusSidePresentation x =>
      decide (((kmswStage r.code.1 n).active :: (kmswStage r.code.1 n).UR)[t]? =
        some (i / 2))) := by
    have hs : Measurable (fun w : ℕ → Fin 3 =>
        decide (((kmswStage w n).active :: (kmswStage w n).UR)[t]? =
          some (i / 2))) :=
      measurable_of_factors_prefix n _ (by
        intro w w' hw
        exact congrArg (fun F : State =>
          decide ((F.active :: F.UR)[t]? = some (i / 2))) (kmswStage_congr hw))
    exact hs.comp hprefix
  have hsideEdge (b : ℕ) : Measurable (fun q : Coherent x =>
      decide (b ∈ (side q).edges)) := by
    simpa only [side] using measurable_geometricRightSide_edges x b
  have hsideBoundary (t : ℕ) : Measurable (fun q : Coherent x =>
      (side q).boundary t) := by
    simpa only [side] using measurable_geometricRightSide_boundary x t
  have hevent :
      {z : RMinusCanonicalCertifiedPairs x |
        rMinusRawTokenGluing
          (kmswStage z.1.1.code.1 z.property.1.choose) (side z.1.2) i j} =
      ⋃ k : ℤ, ⋃ n : ℕ, ⋃ t : ℕ,
        {z : RMinusCanonicalCertifiedPairs x |
          z.1.1.boundaryIndex = k ∧
          boundaryCodeStoppingTime k (rMinusPrefixPath z.1.1.code.1) = n ∧
          (∀ s, n ≤ s → z.1.1.code.1 s = (0 : Fin 3)) ∧
          i % 2 = 0 ∧ j % 2 = 1 ∧
          (((kmswStage z.1.1.code.1 n).active ::
            (kmswStage z.1.1.code.1 n).UR)[t]? = some (i / 2)) ∧
          ((side z.1.2).boundary t).1 = j / 2 ∧
          j / 2 ∈ (side z.1.2).edges} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hglue
      have hp := z.property.1
      have hn := hp.choose_spec.1
      have hpadding := hp.choose_spec.2
      rcases hglue with ⟨a, b, hai, hbj, hab⟩
      cases a with
      | inl a =>
        cases b with
        | inl b => simp [rMinusCodeEdgeGluing] at hab
        | inr b =>
          have hi : i % 2 = 0 := by
            change 2 * a.val = i at hai
            omega
          have hj : j % 2 = 1 := by
            change 2 * b.val + 1 = j at hbj
            omega
          have ha : a.val = i / 2 := by
            change 2 * a.val = i at hai
            omega
          have hb : b.val = j / 2 := by
            change 2 * b.val + 1 = j at hbj
            omega
          rcases hab with ⟨t, ht, hbt⟩
          refine ⟨z.1.1.boundaryIndex, hp.choose, t, rfl, hn, hpadding,
            hi, hj, ?_, ?_, ?_⟩
          · simpa [ha] using ht
          · simpa [hb] using hbt
          · simpa [hb] using b.property
      | inr a => cases b <;> simp [rMinusCodeEdgeGluing] at hab
    · rintro ⟨k, n, t, hk, hn, hpadding, hi, hj, hstage, hboundary, hedge⟩
      have hp := z.property.1
      have hn' : boundaryCodeStoppingTime z.1.1.boundaryIndex
          (rMinusPrefixPath z.1.1.code.1) = n := by
        simpa [hk] using hn
      have hchosen : z.property.1.choose = n :=
        rMinus_prefix_frontier_unique z.1.1.boundaryIndex z.1.1.code.1
          z.property.1.choose n hp.choose_spec.1 hn'
      have hstage' : ((kmswStage z.1.1.code.1
          z.property.1.choose).active ::
          (kmswStage z.1.1.code.1 z.property.1.choose).UR)[t]? =
          some (i / 2) := by
        simpa [hchosen] using hstage
      have hboundary' :
          ((side z.1.2).boundary t).1 = j / 2 := hboundary
      refine ⟨.inl ⟨i / 2, ?_⟩, .inr ⟨j / 2, hedge⟩, ?_, ?_, ?_⟩
      · have hmem : i / 2 ∈ (kmswStage z.1.1.code.1 n).active ::
            (kmswStage z.1.1.code.1 n).UR := by
          exact (List.mem_iff_getElem?).2 ⟨t, by simpa using hstage⟩
        rcases List.mem_cons.mp hmem with hact | hur
        · simpa [hchosen, hact] using kmswStage_active_lt z.1.1.code.1 n
        · simpa [hchosen] using stageRun_edge_bound z.1.1.code.1 n (i / 2)
            (Or.inl (Or.inl (Or.inr hur)))
      · change 2 * (i / 2) = i
        omega
      · change 2 * (j / 2) + 1 = j
        omega
      · exact ⟨t, by simpa using hstage', hboundary'⟩
  rw [hevent]
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro t
  have hprojP : Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.1) :=
    measurable_fst.comp measurable_subtype_coe
  have hprojQ : Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.2) :=
    measurable_snd.comp measurable_subtype_coe
  have hindexEq : MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      z.1.1.boundaryIndex = k} :=
    ((hindex.eq_const k).setOf).preimage
      ((measurable_fst.comp measurable_subtype_coe).comp measurable_id)
  have hstopEq : MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      boundaryCodeStoppingTime k (rMinusPrefixPath z.1.1.code.1) = n} :=
    ((hstop k n).preimage hprojP)
  have hpaddingEq : MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      ∀ s, n ≤ s → z.1.1.code.1 s = (0 : Fin 3)} :=
    hpad n |>.preimage hprojP
  have hstageEq : MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      (((kmswStage z.1.1.code.1 n).active ::
        (kmswStage z.1.1.code.1 n).UR)[t]? = some (i / 2))} := by
    have hm := (hstage n t).comp hprojP
    have hh := (hm.eq_const true).setOf
    change MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      decide (((kmswStage z.1.1.code.1 n).active ::
        (kmswStage z.1.1.code.1 n).UR)[t]? = some (i / 2)) = true} at hh
    simpa only [decide_eq_true_eq] using hh
  have hboundaryEq : MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      ((side z.1.2).boundary t).1 = j / 2} := by
    have hm := (measurable_fst.comp (hsideBoundary t)).comp
      hprojQ
    exact (hm.eq_const (j / 2)).setOf
  have hedgeEq : MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      j / 2 ∈ (side z.1.2).edges} := by
    have hm := (hsideEdge (j / 2)).comp
      hprojQ
    have hh := (hm.eq_const true).setOf
    change MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      decide (j / 2 ∈ (side z.1.2).edges) = true} at hh
    simpa only [decide_eq_true_eq] using hh
  exact MeasurableSet.inter hindexEq
    (MeasurableSet.inter hstopEq
      (MeasurableSet.inter hpaddingEq
        (MeasurableSet.inter (MeasurableSet.const (i % 2 = 0))
          (MeasurableSet.inter (MeasurableSet.const (j % 2 = 1))
            (MeasurableSet.inter hstageEq (MeasurableSet.inter hboundaryEq hedgeEq))))))

/-- Helper toward Lemma 5.5. On the certified pair space, equivalence
closure of numeric raw-token gluing is measurable for every fixed pair. -/
theorem measurableSet_rMinusRawTokenEqvGenOnCertifiedPairs (x : XDP)
    (i j : ℕ) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      Relation.EqvGen (fun a b =>
        rMinusRawTokenGluing
          (kmswStage z.1.1.code.1 z.property.1.choose)
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right z.1.2)
          a b) i j} := by
  apply measurableSet_rMinusEqvGen
  intro a b
  exact measurableSet_rMinusRawTokenGluingOnCertifiedPairs x a b


/-- Helper toward Lemma 5.5. The numeric generator relation at a certified
pair is the source gluing relation on its selected finite stage and hatted side. -/
@[expose] def rMinusRawTokenGeneratorAt (x : XDP)
    (z : RMinusCanonicalCertifiedPairs x) : ℕ → ℕ → Prop :=
  fun a b => rMinusRawTokenGluing
    (kmswStage z.1.1.code.1 z.property.1.choose)
    (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right z.1.2)
    a b

/-- Helper toward Lemma 5.5. The least numeric token in a raw-token
EqvGen class is defined by Nat.find; reflexivity supplies a witness even for
an unused numeric label. -/
@[expose] noncomputable def rMinusRawTokenEqvGenMinimum (x : XDP)
    (z : RMinusCanonicalCertifiedPairs x) (i : ℕ) : ℕ :=
  Nat.find ⟨i, Relation.EqvGen.refl (r := rMinusRawTokenGeneratorAt x z) i⟩

/-- Helper toward Lemma 5.5. Each fixed fiber of the least numeric token is
measurable, using the measurable EqvGen events and the `Nat.find` minimality
characterization. -/
theorem measurableSet_rMinusRawTokenEqvGenMinimum_eq (x : XDP)
    (i j : ℕ) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      rMinusRawTokenEqvGenMinimum x z i = j} := by
  have hfind (z : RMinusCanonicalCertifiedPairs x) :
      rMinusRawTokenEqvGenMinimum x z i = j ↔
        Relation.EqvGen (rMinusRawTokenGeneratorAt x z) i j ∧
          ∀ k < j, ¬ Relation.EqvGen (rMinusRawTokenGeneratorAt x z) i k :=
    by
      simpa [rMinusRawTokenEqvGenMinimum] using
        (Nat.find_eq_iff ⟨i, Relation.EqvGen.refl
          (r := rMinusRawTokenGeneratorAt x z) i⟩)
  have he : {z : RMinusCanonicalCertifiedPairs x |
      rMinusRawTokenEqvGenMinimum x z i = j} =
      {z | Relation.EqvGen (rMinusRawTokenGeneratorAt x z) i j} ∩
        {z | ∀ k < j, ¬ Relation.EqvGen (rMinusRawTokenGeneratorAt x z) i k} := by
    ext z
    exact hfind z
  rw [he]
  apply MeasurableSet.inter
  · exact measurableSet_rMinusRawTokenEqvGenOnCertifiedPairs x i j
  · have he' : {z : RMinusCanonicalCertifiedPairs x |
        ∀ k < j, ¬ Relation.EqvGen (rMinusRawTokenGeneratorAt x z) i k} =
        ⋂ k : ℕ, {z | k < j →
          ¬ Relation.EqvGen (rMinusRawTokenGeneratorAt x z) i k} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [he']
    exact MeasurableSet.iInter fun k => by
      by_cases hk : k < j
      · have hc := measurableSet_rMinusRawTokenEqvGenOnCertifiedPairs x i k
        have he'' : {z : RMinusCanonicalCertifiedPairs x |
            k < j → ¬ Relation.EqvGen (rMinusRawTokenGeneratorAt x z) i k} =
            {z | ¬ Relation.EqvGen (rMinusRawTokenGeneratorAt x z) i k} := by
          ext z
          simp [hk]
        rw [he'']
        exact hc.compl
      · have he'' : {z : RMinusCanonicalCertifiedPairs x |
            k < j → ¬ Relation.EqvGen (rMinusRawTokenGeneratorAt x z) i k} =
            Set.univ := by
          ext z
          simp [hk]
        rw [he'']
        exact MeasurableSet.univ

/-- Helper toward Lemma 5.5. The least numeric token is a measurable
natural-valued function on certified pairs. -/
theorem measurable_rMinusRawTokenEqvGenMinimum (x : XDP) (i : ℕ) :
    Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      rMinusRawTokenEqvGenMinimum x z i) := by
  intro s hs
  have he : {z : RMinusCanonicalCertifiedPairs x |
      rMinusRawTokenEqvGenMinimum x z i ∈ s} =
      ⋃ j : ℕ, ⋃ (_ : j ∈ s),
        {z | rMinusRawTokenEqvGenMinimum x z i = j} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hz
      exact ⟨rMinusRawTokenEqvGenMinimum x z i, hz, rfl⟩
    · rintro ⟨j, hj, hEq⟩
      rw [hEq]
      exact hj
  change MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
    rMinusRawTokenEqvGenMinimum x z i ∈ s}
  rw [he]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
    measurableSet_rMinusRawTokenEqvGenMinimum_eq x i j

























































































end DirectedDistances.PaperProofs.Section5

