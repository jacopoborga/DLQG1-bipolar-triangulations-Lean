/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusCanonicalCodingMeasurable3
public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusMeasurableDescent

/-! Identification of measurable raw-token minima with intrinsic canonical IDs. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. Numeric gluing chains starting at an allocated
raw edge lift to the original edge quotient; unused tokens cannot intervene. -/
theorem rMinusRawTokenEqvGen_iff (F : State) (M : GeometricSideSubmap)
    (a : Sum {e : ℕ // e < F.nextEdge} M.edges) (j : ℕ) :
    Relation.EqvGen (rMinusRawTokenGluing F M) (rMinusRawEdgeToken F M a) j ↔
      ∃ b, rMinusRawEdgeToken F M b = j ∧
        (⟦b⟧ : RMinusCodeGluedEdge F M) = ⟦a⟧ := by
  constructor
  · intro h
    obtain ⟨l, hl⟩ := (rMinusEqvGen_iff_exists_finiteGluingChain _ _ _).mp h
    have liftChain : ∀ (l : List ℕ) (a : Sum {e : ℕ // e < F.nextEdge} M.edges),
        rMinusFiniteGluingChain (rMinusRawTokenGluing F M)
          (rMinusRawEdgeToken F M a) l j →
        ∃ b, rMinusRawEdgeToken F M b = j ∧
          (⟦b⟧ : RMinusCodeGluedEdge F M) = ⟦a⟧ := by
      intro l
      induction l with
      | nil => intro a h; exact ⟨a, h, rfl⟩
      | cons c l ih =>
        intro a h
        obtain ⟨hc, ht⟩ := h
        rcases hc with hc | hc
        · obtain ⟨u, v, hu, hv, hg⟩ := hc
          have hua := rMinusRawEdgeToken_injective F M hu
          subst u
          rw [← hv] at ht
          obtain ⟨b, hb, he⟩ := ih v ht
          exact ⟨b, hb, he.trans (Quotient.sound (Relation.EqvGen.rel _ _ hg)).symm⟩
        · obtain ⟨u, v, hu, hv, hg⟩ := hc
          have hva := rMinusRawEdgeToken_injective F M hv
          subst v
          rw [← hu] at ht
          obtain ⟨b, hb, he⟩ := ih u ht
          exact ⟨b, hb, he.trans (Quotient.sound (Relation.EqvGen.rel _ _ hg))⟩
    exact liftChain l a hl
  · rintro ⟨b, hb, he⟩
    rw [← hb]
    have hraw : Relation.EqvGen (rMinusCodeEdgeGluing F M) a b :=
      (Quotient.exact he).symm
    clear hb he
    induction hraw with
    | rel u v h => exact Relation.EqvGen.rel _ _ ⟨u, v, rfl, rfl, h⟩
    | refl u => exact .refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Helper toward Lemma 5.5. The measurable numeric minimum is exactly
the intrinsic least-token edge ID, including singleton edge classes. -/
theorem rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId
    (x : XDP) (z : RMinusCanonicalCertifiedPairs x)
    (a : Sum {e : ℕ // e <
      (kmswStage z.1.1.code.1 z.property.1.choose).nextEdge}
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime
        .right z.1.2).edges) :
    rMinusRawTokenEqvGenMinimum x z
        (rMinusRawEdgeToken
          (kmswStage z.1.1.code.1 z.property.1.choose)
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime
            .right z.1.2) a) =
      rMinusCanonicalEdgeId
        (kmswStage z.1.1.code.1 z.property.1.choose)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime
          .right z.1.2) (⟦a⟧) := by
  apply Nat.le_antisymm
  · apply Nat.find_min'
    exact (rMinusRawTokenEqvGen_iff _ _ a _).mpr
      (rMinusCanonicalEdgeId_spec _ _ _)
  · apply Nat.find_min'
    exact (rMinusRawTokenEqvGen_iff _ _ a _).mp
      (Nat.find_spec ⟨_, Relation.EqvGen.refl
        (r := rMinusRawTokenGeneratorAt x z) _⟩)

/-- Helper toward Lemma 5.5. Every reader of the selected finite KMSW
stage is measurable. The finite stopping frontier is certified and unique. -/
theorem measurable_rMinusCertifiedStage_reader (x : XDP)
    {β : Type*} [MeasurableSpace β] (f : State → β) :
    Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      f (kmswStage z.1.1.code.1 z.property.1.choose)) := by
  have hcoords := (measurable_rMinusSidePresentation_coordinates x).comp
    (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.1) from
      measurable_fst.comp measurable_subtype_coe)
  have hp := hcoords.snd.fst
  have hpath : Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      rMinusPrefixPath z.1.1.code.1) := by
    apply measurable_pi_iff.mpr
    intro s
    by_cases hs : s = 0
    · simp [rMinusPrefixPath, hs]
    · simp only [rMinusPrefixPath, hs, ↓reduceIte]
      exact (measurable_pi_apply (s - 1)).comp hp
  have hstop : Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      boundaryCodeStoppingTime z.1.1.boundaryIndex
        (rMinusPrefixPath z.1.1.code.1)) :=
    (measurable_from_prod_countable_right
      (f := fun y : ℤ × (ℕ → Fin 3) => boundaryCodeStoppingTime y.1 y.2)
      (fun k => measurable_boundaryCodeStoppingTime k)).comp
        (hcoords.fst.prodMk hpath)
  let hex (z : RMinusCanonicalCertifiedPairs x) :=
    (show ∃ n : ℕ, boundaryCodeStoppingTime z.1.1.boundaryIndex
      (rMinusPrefixPath z.1.1.code.1) = n from
        ⟨z.property.1.choose, z.property.1.choose_spec.1⟩)
  have hm : Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      f (kmswStage z.1.1.code.1 (Nat.find (hex z)))) := by
    refine Measurable.find
      (f := fun n (z : RMinusCanonicalCertifiedPairs x) => f (kmswStage z.1.1.code.1 n))
      (p := fun n (z : RMinusCanonicalCertifiedPairs x) =>
        boundaryCodeStoppingTime z.1.1.boundaryIndex (rMinusPrefixPath z.1.1.code.1) = n)
      ?_ ?_ hex
    · intro n
      exact (measurable_of_factors_prefix n _ (fun w w' h =>
        congrArg f (kmswStage_congr h))).comp hp
    · intro n
      exact (hstop.eq_const (n : WithTop ℕ)).setOf
  convert hm using 1
  funext z
  exact congrArg (fun n => f (kmswStage z.1.1.code.1 n))
    (rMinus_prefix_frontier_unique _ _ _ _ z.property.1.choose_spec.1
      (Nat.find_spec (hex z)))

/-- Helper toward Lemma 5.5. Vertex gluing is certified by one numeric
shared-edge pair and one of its two endpoints. -/
theorem rMinusCertifiedVertexGluing_iff (x : XDP)
    (z : RMinusCanonicalCertifiedPairs x) (u v : Sum ℕ ℕ) :
    rMinusCodeVertexGluing
      (kmswStage z.1.1.code.1 z.property.1.choose)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right z.1.2)
      u v ↔ ∃ a b : ℕ,
      rMinusRawTokenGeneratorAt x z (2 * a) (2 * b + 1) ∧ ∃ s : Bool,
      Sum.inl (if s then (kmswStage z.1.1.code.1 z.property.1.choose).east a
        else (kmswStage z.1.1.code.1 z.property.1.choose).west a) = u ∧
      Sum.inr (if s then (geometricSideSubmap x renewalTime
          renewalTime_positiveSuccessTime .right z.1.2).east b
        else (geometricSideSubmap x renewalTime
          renewalTime_positiveSuccessTime .right z.1.2).west b) = v := by
  constructor
  · rintro ⟨a, b, hg, s, hu, hv⟩
    cases a with
    | inr a => cases b <;> exact False.elim hg
    | inl a =>
      cases b with
      | inl b => exact False.elim hg
      | inr b => exact ⟨a.val, b.val, ⟨.inl a, .inr b, rfl, rfl, hg⟩, s, hu, hv⟩
  · rintro ⟨a, b, ⟨c, d, hc, hd, hg⟩, s, hu, hv⟩
    cases c with
    | inr c =>
      change 2 * c.val + 1 = 2 * a at hc
      omega
    | inl c =>
      cases d with
      | inl d =>
        change 2 * d.val = 2 * b + 1 at hd
        omega
      | inr d =>
        have hca : c.val = a := by change 2 * c.val = 2 * a at hc; omega
        have hdb : d.val = b := by change 2 * d.val + 1 = 2 * b + 1 at hd; omega
        exact ⟨.inl c, .inr d, hg, s,
          by simpa only [rMinusCodeRawEndpoint, hca] using hu,
          by simpa only [rMinusCodeRawEndpoint, hdb] using hv⟩

/-- Helper toward Lemma 5.5. Every original raw vertex generator event
is measurable on certified pairs. -/
theorem measurableSet_rMinusCertifiedVertexGluing (x : XDP) (u v : Sum ℕ ℕ) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      rMinusCodeVertexGluing
        (kmswStage z.1.1.code.1 z.property.1.choose)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right z.1.2)
        u v} := by
  have hp (a : ℕ) (s : Bool) : MeasurableSet
      {z : RMinusCanonicalCertifiedPairs x |
        (Sum.inl (if s then (kmswStage z.1.1.code.1 z.property.1.choose).east a
          else (kmswStage z.1.1.code.1 z.property.1.choose).west a) : Sum ℕ ℕ) = u} := by
    cases u with
    | inl u =>
      simpa only [Sum.inl.injEq] using ((measurable_rMinusCertifiedStage_reader x
        (fun F => if s then F.east a else F.west a)).eq_const u).setOf
    | inr u => simp only [Sum.inl_ne_inr, Set.ofPred_false, MeasurableSet.empty]
  have hh (b : ℕ) (s : Bool) : MeasurableSet
      {z : RMinusCanonicalCertifiedPairs x |
        (Sum.inr (if s then (geometricSideSubmap x renewalTime
            renewalTime_positiveSuccessTime .right z.1.2).east b
          else (geometricSideSubmap x renewalTime
            renewalTime_positiveSuccessTime .right z.1.2).west b) : Sum ℕ ℕ) = v} := by
    cases v with
    | inl v => simp only [Sum.inr_ne_inl, Set.ofPred_false, MeasurableSet.empty]
    | inr v =>
      have hm : Measurable (fun q : Coherent x =>
          if s then (geometricSideSubmap x renewalTime
            renewalTime_positiveSuccessTime .right q).east b
          else (geometricSideSubmap x renewalTime
            renewalTime_positiveSuccessTime .right q).west b) := by
        cases s
        · exact measurable_geometricRightSide_west x b
        · exact measurable_geometricRightSide_east x b
      simpa only [Sum.inr.injEq, Function.comp_apply] using
        ((hm.comp (measurable_snd.comp measurable_subtype_coe)).eq_const v).setOf
  simp only [rMinusCertifiedVertexGluing_iff, Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
    (measurableSet_rMinusRawTokenGluingOnCertifiedPairs x (2 * a) (2 * b + 1)).inter
      (MeasurableSet.iUnion (fun s => (hp a s).inter (hh b s)))))

/-- Helper toward Lemma 5.5. Original raw vertex equivalence events are
measurable by countably many finite gluing chains. -/
theorem measurableSet_rMinusCertifiedVertexSetoid (x : XDP) (u v : Sum ℕ ℕ) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      rMinusCodeVertexSetoid
        (kmswStage z.1.1.code.1 z.property.1.choose)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right z.1.2)
        u v} := by
  exact measurableSet_rMinusEqvGen _ (measurableSet_rMinusCertifiedVertexGluing x) u v

/-- Helper toward Lemma 5.5. Each fixed canonical raw vertex ID is
measurable, with the original quotient and its full unallocated carrier. -/
theorem measurable_rMinusCanonicalVertexIdOnCertifiedPairs (x : XDP)
    (a : Sum ℕ ℕ) :
    Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      rMinusCanonicalVertexId
        (kmswStage z.1.1.code.1 z.property.1.choose)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right z.1.2)
        (⟦a⟧)) := by
  apply measurable_find
  intro n
  have he : {z : RMinusCanonicalCertifiedPairs x |
      rMinusCanonicalVertexCandidate
        (kmswStage z.1.1.code.1 z.property.1.choose)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right z.1.2)
        ⟦a⟧ n} = ⋃ b : Sum ℕ ℕ,
      {z | rMinusRawVertexToken b = n} ∩
      {z | rMinusCodeVertexSetoid
        (kmswStage z.1.1.code.1 z.property.1.choose)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right z.1.2)
        b a} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      rMinusCanonicalVertexCandidate]
    exact exists_congr (fun b => and_congr_right (fun _ =>
      ⟨Quotient.exact, Quotient.sound⟩))
  rw [he]
  exact MeasurableSet.iUnion (fun b => (MeasurableSet.const _).inter
    (measurableSet_rMinusCertifiedVertexSetoid x b a))

local notation "Fz" z => kmswStage (Prod.fst (RMinusSidePresentation.code (Prod.fst (Subtype.val z)))) (Exists.choose (And.left (Subtype.property z)))
local notation "Mz" z => geometricSideSubmap _ renewalTime renewalTime_positiveSuccessTime ThinMapSide.right (Prod.snd (Subtype.val z))
local notation "Sz" z => rMinusCanonicalSide (Prod.fst (RMinusSidePresentation.code (Prod.fst (Subtype.val z)))) (Exists.choose (And.left (Subtype.property z))) (Prod.snd (Subtype.val z))

/-- Helper toward Lemma 5.5. Variable numeric-token evaluation retains
measurability of the least edge token. -/
theorem measurable_rMinusCertifiedEdgeMinimum_eval (x : XDP)
    (i : RMinusCanonicalCertifiedPairs x → ℕ) (hi : Measurable i) :
    Measurable (fun z => rMinusRawTokenEqvGenMinimum x z (i z)) :=
  (measurable_from_prod_countable_right
    (f := fun p : ℕ × RMinusCanonicalCertifiedPairs x =>
      rMinusRawTokenEqvGenMinimum x p.2 p.1)
    (measurable_rMinusRawTokenEqvGenMinimum x)).comp (hi.prodMk measurable_id)

/-- Helper toward Lemma 5.5. Canonical edge allocation is exactly the
range of the least tokens of allocated prefix and hatted representatives. -/
theorem rMinusCertified_mem_edges_iff (x : XDP)
    (z : RMinusCanonicalCertifiedPairs x) (e : ℕ) :
    e ∈ (Sz z).edges ↔
      (∃ a : ℕ, a < (Fz z).nextEdge ∧
        rMinusRawTokenEqvGenMinimum x z (2 * a) = e) ∨
      ∃ b : ℕ, b ∈ (Mz z).edges ∧
        rMinusRawTokenEqvGenMinimum x z (2 * b + 1) = e := by
  constructor
  · rintro ⟨a, ha⟩
    revert ha
    refine Quotient.inductionOn a ?_
    intro a ha
    cases a with
    | inl a => exact Or.inl ⟨a.val, a.property,
        (rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId x z (.inl a)).trans ha⟩
    | inr b => exact Or.inr ⟨b.val, b.property,
        (rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId x z (.inr b)).trans ha⟩
  · rintro (⟨a, ha, he⟩ | ⟨b, hb, he⟩)
    · exact ⟨⟦Sum.inl ⟨a, ha⟩⟧,
        (rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId x z (.inl ⟨a, ha⟩)).symm.trans he⟩
    · exact ⟨⟦Sum.inr ⟨b, hb⟩⟧,
        (rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId x z (.inr ⟨b, hb⟩)).symm.trans he⟩

/-- Helper toward Lemma 5.5. Every canonical edge membership event is
measurable on certified pairs. -/
theorem measurableSet_rMinusCertified_edges (x : XDP) (e : ℕ) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x | e ∈ (Sz z).edges} := by
  simp only [rMinusCertified_mem_edges_iff, Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro a
    have ha : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | a < (Fz z).nextEdge} := by
      have h := ((measurable_rMinusCertifiedStage_reader x
        (fun F => decide (a < F.nextEdge))).eq_const true).setOf
      simpa only [Function.comp_apply, decide_eq_true_eq] using h
    exact ha.inter ((measurable_rMinusRawTokenEqvGenMinimum x (2 * a)).eq_const e).setOf
  · apply MeasurableSet.iUnion
    intro b
    have hb : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | b ∈ (Mz z).edges} := by
      have h := (((measurable_geometricRightSide_edges x b).comp
        (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.2) from
          measurable_snd.comp measurable_subtype_coe)).eq_const true).setOf
      simpa only [Function.comp_apply, decide_eq_true_eq] using h
    exact hb.inter ((measurable_rMinusRawTokenEqvGenMinimum x (2 * b + 1)).eq_const e).setOf

/-- Helper toward Lemma 5.5. Canonical vertex allocation uses precisely
the original finite and hatted allocated raw vertices. -/
theorem rMinusCertified_mem_vertices_iff (x : XDP)
    (z : RMinusCanonicalCertifiedPairs x) (v : ℕ) :
    v ∈ (Sz z).vertices ↔
      (∃ a : ℕ, a < (Fz z).nextVertex ∧
        rMinusCanonicalVertexId (Fz z) (Mz z) ⟦Sum.inl a⟧ = v) ∨
      ∃ b : ℕ, b ∈ (Mz z).vertices ∧
        rMinusCanonicalVertexId (Fz z) (Mz z) ⟦Sum.inr b⟧ = v := by
  constructor
  · rintro ⟨⟨a, ha⟩, hv⟩
    rcases ha with ⟨b, hb⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨b.val, b.isLt, by rw [hb]; exact hv⟩
    · exact Or.inr ⟨b.val, b.property, by rw [hb]; exact hv⟩
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · exact ⟨⟨⟦Sum.inl a⟧, Or.inl ⟨⟨a, ha⟩, rfl⟩⟩, hv⟩
    · exact ⟨⟨⟦Sum.inr b⟧, Or.inr ⟨⟨b, hb⟩, rfl⟩⟩, hv⟩

/-- Helper toward Lemma 5.5. Every canonical vertex membership event is
measurable on certified pairs. -/
theorem measurableSet_rMinusCertified_vertices (x : XDP) (v : ℕ) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x | v ∈ (Sz z).vertices} := by
  simp only [rMinusCertified_mem_vertices_iff, Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro a
    have hlt : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | a < (Fz z).nextVertex} := by
      have h := ((measurable_rMinusCertifiedStage_reader x
        (fun F => decide (a < F.nextVertex))).eq_const true).setOf
      simpa only [Function.comp_apply, decide_eq_true_eq] using h
    exact hlt.inter ((measurable_rMinusCanonicalVertexIdOnCertifiedPairs x (.inl a)).eq_const v).setOf
  · apply MeasurableSet.iUnion
    intro b
    have hb : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | b ∈ (Mz z).vertices} := by
      have h := (((measurable_geometricRightSide_vertices x b).comp
        (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.2) from
          measurable_snd.comp measurable_subtype_coe)).eq_const true).setOf
      simpa only [Function.comp_apply, decide_eq_true_eq] using h
    exact hb.inter ((measurable_rMinusCanonicalVertexIdOnCertifiedPairs x (.inr b)).eq_const v).setOf

/-- Helper toward Lemma 5.5. Variable raw vertex coordinates can be read
measurably in either block. -/
theorem measurable_rMinusCertifiedVertexId_eval (x : XDP) (hat : Bool)
    (i : RMinusCanonicalCertifiedPairs x → ℕ) (hi : Measurable i) :
    Measurable (fun z => rMinusCanonicalVertexId (Fz z) (Mz z)
      ⟦if hat then Sum.inr (i z) else Sum.inl (i z)⟧) := by
  exact (measurable_from_prod_countable_right
    (f := fun p : ℕ × RMinusCanonicalCertifiedPairs x =>
      rMinusCanonicalVertexId (Fz p.2) (Mz p.2)
        ⟦if hat then Sum.inr p.1 else Sum.inl p.1⟧)
    (fun n => by
      cases hat
      · simpa only [Bool.false_eq_true, ↓reduceIte] using
          measurable_rMinusCanonicalVertexIdOnCertifiedPairs x (Sum.inl n)
      · simpa only [↓reduceIte] using
          measurable_rMinusCanonicalVertexIdOnCertifiedPairs x (Sum.inr n))).comp
      (hi.prodMk measurable_id)

/-- Helper toward Lemma 5.5. The canonical root retains the measurable
hatted root's original vertex class. -/
theorem measurable_rMinusCertified_root (x : XDP) :
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => (Sz z).root) :=
  measurable_rMinusCertifiedVertexId_eval x true _
    ((measurable_geometricRightSide_root x).comp
      (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.2) from
        measurable_snd.comp measurable_subtype_coe))

/-- Helper toward Lemma 5.5. The canonical seam keeps the measurable
hatted seam's edge class and endpoint bit. -/
theorem measurable_rMinusCertified_seam (x : XDP) (i : ℕ) :
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => (Sz z).seam i) := by
  have hs := (measurable_geometricRightSide_seam x i).comp
    (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.2) from
      measurable_snd.comp measurable_subtype_coe)
  have he := measurable_rMinusCertifiedEdgeMinimum_eval x
    (fun z => 2 * ((Mz z).seam i).1 + 1)
    ((measurable_of_countable (fun n : ℕ => 2 * n + 1)).comp hs.fst)
  convert he.prodMk hs.snd using 1
  funext z
  exact Prod.ext
    (rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId x z
      (.inr ⟨((Mz z).seam i).1, by
          change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
            renewalTime_positiveSuccessTime .right z.1.2 j
          rw [iUnion_geometricAncestorEdges]
          exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i⟩)).symm rfl

/-- Helper toward Lemma 5.5. The original canonical endpoint reader is
characterized by allocated raw representatives and its defined exterior zero. -/
theorem rMinusCertified_endpoint_eq_iff (x : XDP)
    (z : RMinusCanonicalCertifiedPairs x) (s : Bool) (e v : ℕ) :
    rMinusCanonicalEndpointId z.1.1.code.1 z.property.1.choose z.1.2 s e = v ↔
      (e ∉ (Sz z).edges ∧ 0 = v) ∨
      (∃ a : ℕ, a < (Fz z).nextEdge ∧
        rMinusRawTokenEqvGenMinimum x z (2 * a) = e ∧
        rMinusCanonicalVertexId (Fz z) (Mz z)
          ⟦Sum.inl (if s then (Fz z).east a else (Fz z).west a)⟧ = v) ∨
      ∃ b : ℕ, b ∈ (Mz z).edges ∧
        rMinusRawTokenEqvGenMinimum x z (2 * b + 1) = e ∧
        rMinusCanonicalVertexId (Fz z) (Mz z)
          ⟦Sum.inr (if s then (Mz z).east b else (Mz z).west b)⟧ = v := by
  have rep (a : Sum {e : ℕ // e < (Fz z).nextEdge} (Mz z).edges) :
      rMinusCanonicalEndpointId z.1.1.code.1 z.property.1.choose z.1.2 s
        (rMinusRawTokenEqvGenMinimum x z (rMinusRawEdgeToken (Fz z) (Mz z) a)) =
      rMinusCanonicalVertexId (Fz z) (Mz z) ⟦rMinusCodeRawEndpoint (Fz z) (Mz z) s a⟧ := by
    rw [rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId,
      rMinusCanonicalEndpointId_id]
    rfl
  constructor
  · intro h
    by_cases he : e ∈ (Sz z).edges
    · rcases (rMinusCertified_mem_edges_iff x z e).mp he with ⟨a, ha, hn⟩ | ⟨b, hb, hn⟩
      · exact Or.inr (Or.inl ⟨a, ha, hn, (rep (.inl ⟨a, ha⟩)).symm.trans (hn.symm ▸ h)⟩)
      · exact Or.inr (Or.inr ⟨b, hb, hn, (rep (.inr ⟨b, hb⟩)).symm.trans (hn.symm ▸ h)⟩)
    · change e ∉ Set.range (rMinusCanonicalEdgeId (Fz z) (Mz z)) at he
      exact Or.inl ⟨he, by simpa only [rMinusCanonicalEndpointId, dite_eq_right he] using h⟩
  · rintro (⟨he, hv⟩ | ⟨a, ha, hn, hv⟩ | ⟨b, hb, hn, hv⟩)
    · change e ∉ Set.range (rMinusCanonicalEdgeId (Fz z) (Mz z)) at he
      simpa only [rMinusCanonicalEndpointId, dite_eq_right he] using hv
    · rw [← hn]
      exact (rep (.inl ⟨a, ha⟩)).trans hv
    · rw [← hn]
      exact (rep (.inr ⟨b, hb⟩)).trans hv

/-- Helper toward Lemma 5.5. Both canonical endpoint readers are
measurable, including values outside the geometric edge carrier. -/
theorem measurable_rMinusCertified_endpoint (x : XDP) (s : Bool) (e : ℕ) :
    Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      rMinusCanonicalEndpointId z.1.1.code.1 z.property.1.choose z.1.2 s e) := by
  have hleft (a : ℕ) := measurable_rMinusCertifiedVertexId_eval x false _
    (measurable_rMinusCertifiedStage_reader x (fun F => if s then F.east a else F.west a))
  have hright (b : ℕ) : Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      rMinusCanonicalVertexId (Fz z) (Mz z)
        ⟦Sum.inr (if s then (Mz z).east b else (Mz z).west b)⟧) := by
    apply measurable_rMinusCertifiedVertexId_eval x true
    cases s
    · exact (measurable_geometricRightSide_west x b).comp
        (measurable_snd.comp measurable_subtype_coe)
    · exact (measurable_geometricRightSide_east x b).comp
        (measurable_snd.comp measurable_subtype_coe)
  apply measurable_to_countable'
  intro v
  change MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
    rMinusCanonicalEndpointId z.1.1.code.1 z.property.1.choose z.1.2 s e = v}
  simp only [rMinusCertified_endpoint_eq_iff, Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  · exact (measurableSet_rMinusCertified_edges x e).compl.inter (MeasurableSet.const _)
  · apply MeasurableSet.union
    · apply MeasurableSet.iUnion
      intro a
      have ha : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | a < (Fz z).nextEdge} := by
        simpa only [decide_eq_true_eq] using
          ((measurable_rMinusCertifiedStage_reader x (fun F => decide (a < F.nextEdge))).eq_const true).setOf
      exact ha.inter (((measurable_rMinusRawTokenEqvGenMinimum x (2 * a)).eq_const e).setOf.inter
        ((hleft a).eq_const v).setOf)
    · apply MeasurableSet.iUnion
      intro b
      have hb : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | b ∈ (Mz z).edges} := by
        simpa only [Function.comp_apply, decide_eq_true_eq] using
          (((measurable_geometricRightSide_edges x b).comp
            (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.2) from
              measurable_snd.comp measurable_subtype_coe)).eq_const true).setOf
      exact hb.inter (((measurable_rMinusRawTokenEqvGenMinimum x (2 * b + 1)).eq_const e).setOf.inter
        ((hright b).eq_const v).setOf)

/-- Helper toward Lemma 5.5. Presence is read from the two original
directed edge carriers without discarding missing geometric edges. -/
theorem rMinusCertified_mem_present_iff (x : XDP)
    (z : RMinusCanonicalCertifiedPairs x) (e : ℕ) :
    e ∈ (Sz z).present ↔
      (∃ a : ℕ, a < (Fz z).nextEdge ∧ (Fz z).present a = true ∧
        rMinusRawTokenEqvGenMinimum x z (2 * a) = e) ∨
      ∃ b : ℕ, b ∈ (Mz z).edges ∧ b ∈ (Mz z).present ∧
        rMinusRawTokenEqvGenMinimum x z (2 * b + 1) = e := by
  constructor
  · rintro ⟨a, ha, hp⟩
    rcases hp with ⟨b, hb, hba⟩ | ⟨b, hb, hba⟩
    · exact Or.inl ⟨b.val, b.property, hb,
        (rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId x z (.inl b)).trans
          ((congrArg _ hba).trans ha)⟩
    · exact Or.inr ⟨b.val, b.property, hb,
        (rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId x z (.inr b)).trans
          ((congrArg _ hba).trans ha)⟩
  · rintro (⟨a, ha, hp, hn⟩ | ⟨b, hb, hp, hn⟩)
    · exact ⟨⟦Sum.inl ⟨a, ha⟩⟧,
        (rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId x z (.inl ⟨a, ha⟩)).symm.trans hn,
        Or.inl ⟨⟨a, ha⟩, hp, rfl⟩⟩
    · exact ⟨⟦Sum.inr ⟨b, hb⟩⟧,
        (rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId x z (.inr ⟨b, hb⟩)).symm.trans hn,
        Or.inr ⟨⟨b, hb⟩, hp, rfl⟩⟩

/-- Helper toward Lemma 5.5. Every canonical directed-presence event
is measurable on certified pairs. -/
theorem measurableSet_rMinusCertified_present (x : XDP) (e : ℕ) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x | e ∈ (Sz z).present} := by
  simp only [rMinusCertified_mem_present_iff, Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro a
    have ha : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | a < (Fz z).nextEdge} := by
      simpa only [decide_eq_true_eq] using
        ((measurable_rMinusCertifiedStage_reader x (fun F => decide (a < F.nextEdge))).eq_const true).setOf
    exact ha.inter (((measurable_rMinusCertifiedStage_reader x
      (fun F => F.present a)).eq_const true).setOf.inter
      ((measurable_rMinusRawTokenEqvGenMinimum x (2 * a)).eq_const e).setOf)
  · apply MeasurableSet.iUnion
    intro b
    have hb : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | b ∈ (Mz z).edges} := by
      simpa only [Function.comp_apply, decide_eq_true_eq] using
        (((measurable_geometricRightSide_edges x b).comp
          (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.2) from
            measurable_snd.comp measurable_subtype_coe)).eq_const true).setOf
    exact hb.inter (((measurableSet_geometricRightSide_present x b).preimage
      (measurable_snd.comp measurable_subtype_coe)).inter
      ((measurable_rMinusRawTokenEqvGenMinimum x (2 * b + 1)).eq_const e).setOf)

/-- Helper toward Lemma 5.5. The finite stopping frontier itself is
measurable; no infinite frontier is coerced to a finite stage. -/
theorem measurable_rMinusCertified_frontier (x : XDP) :
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.property.1.choose) := by
  have hcoords := (measurable_rMinusSidePresentation_coordinates x).comp
    (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.1) from
      measurable_fst.comp measurable_subtype_coe)
  have hpath : Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      rMinusPrefixPath z.1.1.code.1) := by
    apply measurable_pi_iff.mpr
    intro s
    by_cases hs : s = 0
    · simp [rMinusPrefixPath, hs]
    · simp only [rMinusPrefixPath, hs, ↓reduceIte]
      exact (measurable_pi_apply (s - 1)).comp hcoords.snd.fst
  have hstop := (measurable_from_prod_countable_right
    (f := fun p : ℤ × (ℕ → Fin 3) => boundaryCodeStoppingTime p.1 p.2)
    (fun k => measurable_boundaryCodeStoppingTime k)).comp (hcoords.fst.prodMk hpath)
  apply measurable_to_countable'
  intro n
  have he : {z : RMinusCanonicalCertifiedPairs x | z.property.1.choose = n} =
      {z | boundaryCodeStoppingTime z.1.1.boundaryIndex
        (rMinusPrefixPath z.1.1.code.1) = n} := by
    ext z
    constructor
    · intro h
      rw [← h]
      exact z.property.1.choose_spec.1
    · intro h
      exact rMinus_prefix_frontier_unique _ _ _ _ z.property.1.choose_spec.1 h
  change MeasurableSet {z : RMinusCanonicalCertifiedPairs x | z.property.1.choose = n}
  rw [he]
  exact (hstop.eq_const (n : WithTop ℕ)).setOf

/-- Helper toward Lemma 5.5. Any measurable finite-prefix reader may
be evaluated at the certified stopping frontier. -/
theorem measurable_rMinusCertified_prefixReader (x : XDP)
    {β : Type*} [MeasurableSpace β] (f : (ℕ → Fin 3) → ℕ → β)
    (hf : ∀ n, Measurable (fun w => f w n)) :
    Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      f z.1.1.code.1 z.property.1.choose) :=
  (measurable_from_prod_countable_left (f := fun p : (ℕ → Fin 3) × ℕ => f p.1 p.2)
    hf).comp
      ((((measurable_rMinusSidePresentation_coordinates x).comp
        (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.1) from
          measurable_fst.comp measurable_subtype_coe)).snd.fst).prodMk
        (measurable_rMinusCertified_frontier x))

/-- Helper toward Lemma 5.5. Fixed ambient darts have measurable numeric
canonical coordinates before imposing their block allocation. -/
@[expose] noncomputable def rMinusCertifiedDartId (x : XDP)
    (z : RMinusCanonicalCertifiedPairs x) (hat : Bool) (d : ℕ × Bool) : ℕ × Bool :=
  (rMinusRawTokenEqvGenMinimum x z (if hat then 2 * d.1 + 1 else 2 * d.1), d.2)

/-- Helper toward Lemma 5.5. Each fixed ambient dart ID is measurable. -/
theorem measurable_rMinusCertifiedDartId (x : XDP) (hat : Bool) (d : ℕ × Bool) :
    Measurable (fun z => rMinusCertifiedDartId x z hat d) :=
  (measurable_rMinusRawTokenEqvGenMinimum x _).prodMk measurable_const

/-- Helper toward Lemma 5.5. Ambient prefix dart IDs agree with intrinsic
canonical dart IDs on allocated prefix darts. -/
theorem rMinusCertifiedDartId_prefix (x : XDP) (z : RMinusCanonicalCertifiedPairs x)
    (d : StageDart (Fz z).nextEdge) :
    rMinusCertifiedDartId x z false (d.1.val, d.2) =
      rMinusCanonicalDartId (Fz z) (Mz z) (rMinusCodePrefixDart (Fz z) (Mz z) d) :=
  Prod.ext (rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId x z
    (.inl ⟨d.1.val, d.1.isLt⟩)) rfl

/-- Helper toward Lemma 5.5. Ambient hatted dart IDs agree with intrinsic
canonical dart IDs on geometric hatted darts. -/
theorem rMinusCertifiedDartId_hatted (x : XDP) (z : RMinusCanonicalCertifiedPairs x)
    (d : {d : ℕ × Bool // d.1 ∈ (Mz z).edges}) :
    rMinusCertifiedDartId x z true d.val =
      rMinusCanonicalDartId (Fz z) (Mz z) (rMinusCodeHattedDart (Fz z) (Mz z) d) :=
  Prod.ext (rMinusRawTokenEqvGenMinimum_eq_rMinusCanonicalEdgeId x z
    (.inr ⟨d.val.1, d.property⟩)) rfl

/-- Helper toward Lemma 5.5. Retained face succession has exactly the
two original block certificates, expressed in measurable ambient dart IDs. -/
theorem rMinusCertified_faceNext_iff (x : XDP) (z : RMinusCanonicalCertifiedPairs x)
    (d e : ℕ × Bool) :
    (Sz z).faceNext d e ↔
      (∃ a b : ℕ × Bool, a.1 < (Fz z).nextEdge ∧ b.1 < (Fz z).nextEdge ∧
        rMinusCertifiedDartId x z false a = d ∧ rMinusCertifiedDartId x z false b = e ∧
        rMinusPrefixFaceNext (Fz z) a b) ∨
      ∃ a b : ℕ × Bool, a.1 ∈ (Mz z).edges ∧ b.1 ∈ (Mz z).edges ∧
        rMinusCertifiedDartId x z true a = d ∧ rMinusCertifiedDartId x z true b = e ∧
        (Mz z).faceNext a b := by
  constructor
  · rintro ⟨u, v, hu, hv, h⟩
    rcases h with ⟨a, b, hr, ha, hb⟩ | ⟨a, b, hr, ha, hb⟩
    · subst u; subst v
      exact Or.inl ⟨(a.1.val, a.2), (b.1.val, b.2), a.1.isLt, b.1.isLt,
        (rMinusCertifiedDartId_prefix x z a).trans hu,
        (rMinusCertifiedDartId_prefix x z b).trans hv, hr⟩
    · subst u; subst v
      exact Or.inr ⟨a.val, b.val, a.property, b.property,
        (rMinusCertifiedDartId_hatted x z a).trans hu,
        (rMinusCertifiedDartId_hatted x z b).trans hv, hr⟩
  · rintro (⟨a, b, ham, hbm, ha, hb, hr⟩ | ⟨a, b, ham, hbm, ha, hb, hr⟩)
    · exact ⟨_, _, (rMinusCertifiedDartId_prefix x z (⟨a.1, ham⟩, a.2)).symm.trans ha,
        (rMinusCertifiedDartId_prefix x z (⟨b.1, hbm⟩, b.2)).symm.trans hb,
        Or.inl ⟨_, _, hr, rfl, rfl⟩⟩
    · exact ⟨_, _, (rMinusCertifiedDartId_hatted x z ⟨a, ham⟩).symm.trans ha,
        (rMinusCertifiedDartId_hatted x z ⟨b, hbm⟩).symm.trans hb,
        Or.inr ⟨_, _, hr, rfl, rfl⟩⟩

/-- Helper toward Lemma 5.5. Every retained-face coordinate is measurable
on certified pairs, without replacing faces by rotation shortcuts. -/
theorem measurableSet_rMinusCertified_faceNext (x : XDP) (d e : ℕ × Bool) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x | (Sz z).faceNext d e} := by
  have hstage (P : State → Prop) : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | P (Fz z)} := by
    simpa only [decide_eq_true_eq] using
      ((measurable_rMinusCertifiedStage_reader x (fun F => decide (P F))).eq_const true).setOf
  have hedge (a : ℕ) : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | a ∈ (Mz z).edges} := by
    simpa only [Function.comp_apply, decide_eq_true_eq] using
      (((measurable_geometricRightSide_edges x a).comp
        (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.2) from
          measurable_snd.comp measurable_subtype_coe)).eq_const true).setOf
  simp only [rMinusCertified_faceNext_iff, Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  exact (MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
    (hstage (fun F => a.1 < F.nextEdge)).inter
    ((hstage (fun F => b.1 < F.nextEdge)).inter
    (((measurable_rMinusCertifiedDartId x false a).eq_const d).setOf.inter
    (((measurable_rMinusCertifiedDartId x false b).eq_const e).setOf.inter
      (hstage (fun F => rMinusPrefixFaceNext F a b)))))))).union
    (MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
      (hedge a.1).inter ((hedge b.1).inter
      (((measurable_rMinusCertifiedDartId x true a).eq_const d).setOf.inter
      (((measurable_rMinusCertifiedDartId x true b).eq_const e).setOf.inter
      (by
        simpa only [Function.comp_apply, decide_eq_true_eq] using
          (((measurable_geometricRightSide_faceNext x a b).comp
            (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.2) from
              measurable_snd.comp measurable_subtype_coe)).eq_const true).setOf)))))))

/-- Helper toward Lemma 5.5. The graph of a permutation in injective
countable coordinates, without choosing an inverse outside its carrier. -/
@[expose] def rMinusEncodedPermGraph {α β : Type*} (f : α → β)
    (p : Equiv.Perm α) (d e : β) : Prop :=
  ∃ a, f a = d ∧ f (p a) = e

/-- Helper toward Lemma 5.5. Products of encoded permutation graphs are
relational compositions; injectivity preserves the intermediate cell. -/
theorem rMinusEncodedPermGraph_mul {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (p q : Equiv.Perm α) (d e : β) :
    rMinusEncodedPermGraph f (p * q) d e ↔
      ∃ m, rMinusEncodedPermGraph f q d m ∧ rMinusEncodedPermGraph f p m e := by
  constructor
  · rintro ⟨a, ha, hb⟩
    exact ⟨f (q a), ⟨a, ha, rfl⟩, ⟨q a, rfl, hb⟩⟩
  · rintro ⟨m, ⟨a, ha, hm⟩, ⟨b, hb, he⟩⟩
    have hab := hf (hm.trans hb.symm)
    subst b
    exact ⟨a, ha, he⟩

/-- Helper toward Lemma 5.5. Extending a block permutation adds precisely
the fixed darts outside the embedded block, within the geometric carrier. -/
theorem rMinusEncodedPermGraph_extend {α β γ : Type*} (f : β → γ)
    (hf : Function.Injective f) (j : α → β) (hj : Function.Injective j)
    (p : Equiv.Perm α) (d e : γ) :
    rMinusEncodedPermGraph f (p.extendDomain (Equiv.ofInjective j hj)) d e ↔
      rMinusEncodedPermGraph (f ∘ j) p d e ∨
        (d = e ∧ d ∈ Set.range f ∧
          ¬ ∃ m, rMinusEncodedPermGraph (f ∘ j) p d m) := by
  have happ (a : α) : p.extendDomain (Equiv.ofInjective j hj) (j a) = j (p a) :=
    Equiv.Perm.extendDomain_apply_image p (Equiv.ofInjective j hj) a
  constructor
  · rintro ⟨b, hb, he⟩
    by_cases h : b ∈ Set.range j
    · obtain ⟨a, rfl⟩ := h
      exact Or.inl ⟨a, hb, by change f (j (p a)) = e; rw [← happ]; exact he⟩
    · have hfix := Equiv.Perm.extendDomain_apply_not_subtype p
        (Equiv.ofInjective j hj) h
      refine Or.inr ⟨hb.symm.trans (hfix ▸ he), ⟨b, hb⟩, ?_⟩
      rintro ⟨m, a, ha, _⟩
      exact h ⟨a, hf (ha.trans hb.symm)⟩
  · rintro (⟨a, ha, he⟩ | ⟨hde, ⟨b, hb⟩, hn⟩)
    · exact ⟨j a, ha, by rw [happ]; exact he⟩
    · have h : b ∉ Set.range j := by
        rintro ⟨a, rfl⟩
        exact hn ⟨f (j (p a)), a, hb, rfl⟩
      exact ⟨b, hb, (congrArg f (Equiv.Perm.extendDomain_apply_not_subtype p
        (Equiv.ofInjective j hj) h)).trans (hb.trans hde)⟩

/-- Helper toward Lemma 5.5. A swap has its literal two moved-coordinate
branches and fixes every other allocated coordinate. -/
theorem rMinusEncodedPermGraph_swap {α β : Type*} [DecidableEq α] (f : α → β)
    (hf : Function.Injective f) (a b : α) (d e : β) :
    rMinusEncodedPermGraph f (Equiv.swap a b) d e ↔
      (d = f a ∧ e = f b) ∨ (d = f b ∧ e = f a) ∨
        (d ≠ f a ∧ d ≠ f b ∧ d = e ∧ d ∈ Set.range f) := by
  constructor
  · rintro ⟨u, hu, hv⟩
    by_cases ha : u = a
    · subst u
      exact Or.inl ⟨hu.symm, by simpa only [Equiv.swap_apply_left] using hv.symm⟩
    · by_cases hb : u = b
      · subst u
        exact Or.inr (Or.inl ⟨hu.symm, by simpa only [Equiv.swap_apply_right] using hv.symm⟩)
      · rw [Equiv.swap_apply_of_ne_of_ne ha hb] at hv
        exact Or.inr (Or.inr ⟨fun h => ha (hf (hu.trans h)),
          fun h => hb (hf (hu.trans h)), hu.symm.trans hv, u, hu⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ha, hb, rfl, u, hu⟩)
    · exact ⟨a, rfl, congrArg f (Equiv.swap_apply_left a b)⟩
    · exact ⟨b, rfl, congrArg f (Equiv.swap_apply_right a b)⟩
    · refine ⟨u, hu, ?_⟩
      rw [Equiv.swap_apply_of_ne_of_ne (fun h => ha (hu.symm.trans (congrArg f h)))
        (fun h => hb (hu.symm.trans (congrArg f h)))]
      exact hu

/-- Helper toward Lemma 5.5. The encoded hatted rotation graph has a
countable certificate using the measurable hatted rotation relation. -/
theorem measurableSet_rMinusCertified_hattedRotationGraph (x : XDP) (d e : ℕ × Bool) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      rMinusEncodedPermGraph
        (rMinusCanonicalDartId (Fz z) (Mz z) ∘ rMinusCodeHattedDart (Fz z) (Mz z))
        (rMinusHattedRotation x z.1.2) d e} := by
  have he : {z : RMinusCanonicalCertifiedPairs x |
      rMinusEncodedPermGraph
        (rMinusCanonicalDartId (Fz z) (Mz z) ∘ rMinusCodeHattedDart (Fz z) (Mz z))
        (rMinusHattedRotation x z.1.2) d e} =
      {z | ∃ a b : ℕ × Bool, a.1 ∈ (Mz z).edges ∧ b.1 ∈ (Mz z).edges ∧
        rMinusCertifiedDartId x z true a = d ∧ rMinusCertifiedDartId x z true b = e ∧
        (Mz z).rotation a b} := by
    ext z
    constructor
    · rintro ⟨a, ha, hb⟩
      let b := rMinusHattedRotation x z.1.2 a
      exact ⟨a.val, b.val, a.property, b.property,
        (rMinusCertifiedDartId_hatted x z a).trans ha,
        (rMinusCertifiedDartId_hatted x z b).trans hb,
        (rMinusHattedRotation_iff x z.1.2 a b).mpr rfl⟩
    · rintro ⟨a, b, ham, hbm, ha, hb, hr⟩
      have h := (rMinusHattedRotation_iff x z.1.2 ⟨a, ham⟩ ⟨b, hbm⟩).mp hr
      refine ⟨⟨a, ham⟩, (rMinusCertifiedDartId_hatted x z ⟨a, ham⟩).symm.trans ha, ?_⟩
      change rMinusCanonicalDartId (Fz z) (Mz z)
        (rMinusCodeHattedDart (Fz z) (Mz z) (rMinusHattedRotation x z.1.2 ⟨a, ham⟩)) = e
      rw [h]
      exact (rMinusCertifiedDartId_hatted x z ⟨b, hbm⟩).symm.trans hb
  have hedge (a : ℕ) : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | a ∈ (Mz z).edges} := by
    simpa only [Function.comp_apply, decide_eq_true_eq] using
      (((measurable_geometricRightSide_edges x a).comp
        (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.2) from
          measurable_snd.comp measurable_subtype_coe)).eq_const true).setOf
  rw [he]
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
    (hedge a.1).inter ((hedge b.1).inter
    (((measurable_rMinusCertifiedDartId x true a).eq_const d).setOf.inter
    (((measurable_rMinusCertifiedDartId x true b).eq_const e).setOf.inter
    (by
      simpa only [Function.comp_apply, decide_eq_true_eq] using
        (((measurable_geometricRightSide_rotation x a b).comp
          (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.2) from
            measurable_snd.comp measurable_subtype_coe)).eq_const true).setOf))))))

/-- Helper toward Lemma 5.5. The numeric boundary formula preserves the
finite lower word and the unattached hatted boundary tail. -/
@[expose] noncomputable def rMinusCertifiedBoundaryRead (x : XDP)
    (z : RMinusCanonicalCertifiedPairs x) (i : ℕ) : ℕ × Bool :=
  if i < ((Fz z).LL ++ (Fz z).LR).length then
    (rMinusRawTokenEqvGenMinimum x z
      (2 * ((Fz z).LL ++ (Fz z).LR)[i]?.getD 0), false)
  else
    let b := (Mz z).boundary
      (i - ((Fz z).LL ++ (Fz z).LR).length + ((Fz z).active :: (Fz z).UR).length)
    (rMinusRawTokenEqvGenMinimum x z (2 * b.1 + 1), b.2)

/-- Helper toward Lemma 5.5. The numeric boundary formula is the exact
canonical boundary, with its original finite/hatted split. -/
theorem rMinusCertifiedBoundaryRead_eq (x : XDP)
    (z : RMinusCanonicalCertifiedPairs x) (i : ℕ) :
    rMinusCertifiedBoundaryRead x z i = (Sz z).boundary i := by
  by_cases hi : i < ((Fz z).LL ++ (Fz z).LR).length
  · simp only [rMinusCertifiedBoundaryRead, rMinusCanonicalSide, rMinusDecodedBoundary,
      hi, ↓reduceIte, ↓reduceDIte, List.getElem?_eq_getElem hi, Option.getD_some]
    have ha : ((Fz z).LL ++ (Fz z).LR)[i] < (Fz z).nextEdge := by
      apply (kmswStage_boundary_ids_lt_nextEdge z.1.1.code.1 z.property.1.choose).2
      have hm := List.getElem_mem hi
      simp only [List.mem_append] at hm ⊢
      tauto
    exact rMinusCertifiedDartId_prefix x z (⟨((Fz z).LL ++ (Fz z).LR)[i], ha⟩, false)
  · simp only [rMinusCertifiedBoundaryRead, rMinusCanonicalSide, rMinusDecodedBoundary,
      hi, ↓reduceIte, ↓reduceDIte]
    let j := i - ((Fz z).LL ++ (Fz z).LR).length + ((Fz z).active :: (Fz z).UR).length
    exact rMinusCertifiedDartId_hatted x z
      ⟨(Mz z).boundary j, rMinus_hatted_boundary_mem x z.1.2 j⟩

/-- Helper toward Lemma 5.5. The numeric exterior-boundary formula is
measurable on certified pairs. -/
theorem measurable_rMinusCertifiedBoundaryRead (x : XDP) (i : ℕ) :
    Measurable (fun z => rMinusCertifiedBoundaryRead x z i) := by
  unfold rMinusCertifiedBoundaryRead
  let len (F : State) := (F.LL ++ F.LR).length
  let edge (F : State) := (F.LL ++ F.LR)[i]?.getD 0
  have htest : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | i < len (Fz z)} := by
    simpa only [decide_eq_true_eq] using
      ((measurable_rMinusCertifiedStage_reader x (fun F => decide (i < len F))).eq_const true).setOf
  have hpre : Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      (rMinusRawTokenEqvGenMinimum x z (2 * edge (Fz z)), false)) :=
    (measurable_rMinusCertifiedEdgeMinimum_eval x (fun z => 2 * edge (Fz z))
      (measurable_rMinusCertifiedStage_reader x (fun F => 2 * edge F))).prodMk measurable_const
  have hind : Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      i - len (Fz z) + ((Fz z).active :: (Fz z).UR).length) :=
    measurable_rMinusCertifiedStage_reader x (fun F => i - len F + (F.active :: F.UR).length)
  have hbd : Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      (Mz z).boundary (i - len (Fz z) + ((Fz z).active :: (Fz z).UR).length)) := by
    apply measurable_to_countable'
    intro d
    have he : {z : RMinusCanonicalCertifiedPairs x |
        (Mz z).boundary (i - len (Fz z) + ((Fz z).active :: (Fz z).UR).length) = d} =
        ⋃ j : ℕ, {z | i - len (Fz z) + ((Fz z).active :: (Fz z).UR).length = j} ∩
          {z | (Mz z).boundary j = d} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨_, rfl, h⟩
      · rintro ⟨j, hj, hd⟩; rw [hj]; exact hd
    change MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      (Mz z).boundary (i - len (Fz z) + ((Fz z).active :: (Fz z).UR).length) = d}
    rw [he]
    exact MeasurableSet.iUnion (fun j => ((hind.eq_const j).setOf).inter
      ((((measurable_geometricRightSide_boundary x j).comp
        (show Measurable (fun z : RMinusCanonicalCertifiedPairs x => z.1.2) from
          measurable_snd.comp measurable_subtype_coe)).eq_const d).setOf))
  have hhat : Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      (rMinusRawTokenEqvGenMinimum x z
        (2 * ((Mz z).boundary (i - len (Fz z) + ((Fz z).active :: (Fz z).UR).length)).1 + 1),
       ((Mz z).boundary (i - len (Fz z) + ((Fz z).active :: (Fz z).UR).length)).2)) :=
    (measurable_rMinusCertifiedEdgeMinimum_eval x
      (fun z => 2 * ((Mz z).boundary (i - len (Fz z) + ((Fz z).active :: (Fz z).UR).length)).1 + 1)
    ((measurable_of_countable (fun n : ℕ => 2 * n + 1)).comp hbd.fst)).prodMk hbd.snd
  dsimp only [len, edge] at htest hpre hhat
  exact hpre.ite htest hhat

/-- Helper toward Lemma 5.5. Every exact canonical boundary coordinate
is measurable on certified pairs. -/
theorem measurable_rMinusCertified_boundary (x : XDP) (i : ℕ) :
    Measurable (fun z : RMinusCanonicalCertifiedPairs x => (Sz z).boundary i) := by
  have he : (fun z : RMinusCanonicalCertifiedPairs x => (Sz z).boundary i) =
      (fun z => rMinusCertifiedBoundaryRead x z i) :=
    funext (fun z => (rMinusCertifiedBoundaryRead_eq x z i).symm)
  rw [he]
  exact measurable_rMinusCertifiedBoundaryRead x i

/-- Helper toward Lemma 5.5. Finite-prefix rotation entries are measurable
at the certified frontier, by finite-prefix dependence at each fixed stage. -/
theorem measurable_rMinusCertified_prefixRotation (x : XDP) (d : ℕ × Bool) :
    Measurable (fun z : RMinusCanonicalCertifiedPairs x =>
      finiteRotationEntry z.1.1.code.1 z.property.1.choose d) :=
  measurable_rMinusCertified_prefixReader x (fun w n => finiteRotationEntry w n d)
    (fun n => measurable_of_factors_prefix n _
      (fun w w' h => finiteRotationEntry_of_prefix w w' n h d))

/-- Helper toward Lemma 5.5. The encoded prefix rotation graph has a
countable certificate through allocated ambient darts. -/
theorem measurableSet_rMinusCertified_prefixRotationGraph (x : XDP) (d e : ℕ × Bool) :
    MeasurableSet {z : RMinusCanonicalCertifiedPairs x |
      rMinusEncodedPermGraph
        (rMinusCanonicalDartId (Fz z) (Mz z) ∘ rMinusCodePrefixDart (Fz z) (Mz z))
        (stageRot z.1.1.code.1 z.property.1.choose) d e} := by
  have he : {z : RMinusCanonicalCertifiedPairs x |
      rMinusEncodedPermGraph
        (rMinusCanonicalDartId (Fz z) (Mz z) ∘ rMinusCodePrefixDart (Fz z) (Mz z))
        (stageRot z.1.1.code.1 z.property.1.choose) d e} =
      {z | ∃ a b : ℕ × Bool, a.1 < (Fz z).nextEdge ∧ b.1 < (Fz z).nextEdge ∧
        rMinusCertifiedDartId x z false a = d ∧ rMinusCertifiedDartId x z false b = e ∧
        finiteRotationEntry z.1.1.code.1 z.property.1.choose a = b} := by
    ext z
    constructor
    · rintro ⟨a, ha, hb⟩
      let b := stageRot z.1.1.code.1 z.property.1.choose a
      exact ⟨(a.1.val, a.2), (b.1.val, b.2), a.1.isLt, b.1.isLt,
        (rMinusCertifiedDartId_prefix x z a).trans ha,
        (rMinusCertifiedDartId_prefix x z b).trans hb,
        by simp only [finiteRotationEntry, a.1.isLt, ↓reduceDIte]; rfl⟩
    · rintro ⟨a, b, ham, hbm, ha, hb, hr⟩
      let A : StageDart (Fz z).nextEdge := (⟨a.1, ham⟩, a.2)
      let B : StageDart (Fz z).nextEdge := (⟨b.1, hbm⟩, b.2)
      have hrot : stageRot z.1.1.code.1 z.property.1.choose A = B := by
        simp only [finiteRotationEntry, ham, ↓reduceDIte] at hr
        exact Prod.ext (Fin.ext (congrArg Prod.fst hr)) (congrArg (fun p : ℕ × Bool => p.2) hr)
      refine ⟨A, (rMinusCertifiedDartId_prefix x z A).symm.trans ha, ?_⟩
      change rMinusCanonicalDartId (Fz z) (Mz z)
        (rMinusCodePrefixDart (Fz z) (Mz z) (stageRot z.1.1.code.1 z.property.1.choose A)) = e
      rw [hrot]
      exact (rMinusCertifiedDartId_prefix x z B).symm.trans hb
  have hlt (a : ℕ) : MeasurableSet {z : RMinusCanonicalCertifiedPairs x | a < (Fz z).nextEdge} := by
    simpa only [decide_eq_true_eq] using
      ((measurable_rMinusCertifiedStage_reader x (fun F => decide (a < F.nextEdge))).eq_const true).setOf
  rw [he]
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
    (hlt a.1).inter ((hlt b.1).inter
    (((measurable_rMinusCertifiedDartId x false a).eq_const d).setOf.inter
    (((measurable_rMinusCertifiedDartId x false b).eq_const e).setOf.inter
      ((measurable_rMinusCertified_prefixRotation x a).eq_const b).setOf)))))
































































































end DirectedDistances.PaperProofs.Section5
