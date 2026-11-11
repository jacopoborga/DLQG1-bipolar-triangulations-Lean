/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusCanonicalCodingMeasurable
public import DirectedDistances.PaperProofs.Section5.GeoInftyRPlusMeasurableClass3

/-! of canonical minimal-token data is developed on certified presentation/path pairs. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

local instance : MeasurableSingletonClass (Option FiniteThinMap) where
  measurableSet_singleton _ := trivial

/-- Helper toward Lemma 5.5. Valid finite prefixes form a measurable set of
presentations. The proof writes the witness frontier as a countable union and
the zero-padding clause as a countable intersection. -/
theorem measurableSet_rMinusPrefixValid (x : XDP) :
    MeasurableSet {r : RMinusSidePresentation x | r.prefixValid} := by
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
    intro i
    by_cases hi : i = 0
    · simp [rMinusPrefixPath, hi]
    · simp only [rMinusPrefixPath, hi, ↓reduceIte]
      exact (measurable_pi_apply (i - 1)).comp hprefix
  have heq : {r : RMinusSidePresentation x | r.prefixValid} =
      ⋃ k : ℤ, ⋃ n : ℕ,
        {r | r.boundaryIndex = k} ∩
          {r | boundaryCodeStoppingTime k (rMinusPrefixPath r.code.1) = n} ∩
          ⋂ i : ℕ, {r | n ≤ i → r.code.1 i = (0 : Fin 3)} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, RMinusSidePresentation.prefixValid]
    constructor
    · rintro ⟨n, hn, hpad⟩
      exact ⟨r.boundaryIndex, n, ⟨rfl, hn⟩, hpad⟩
    · rintro ⟨k, n, ⟨hk, hn⟩, hpad⟩
      subst k
      exact ⟨n, hn, hpad⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro n
  have hA : MeasurableSet {r : RMinusSidePresentation x | r.boundaryIndex = k} :=
    (hindex.eq_const k).setOf
  have hB : MeasurableSet {r : RMinusSidePresentation x |
      boundaryCodeStoppingTime k (rMinusPrefixPath r.code.1) = n} :=
    ((measurable_boundaryCodeStoppingTime k).comp hpath).eq_const n |>.setOf
  have hC : MeasurableSet (⋂ i : ℕ,
      {r : RMinusSidePresentation x | n ≤ i → r.code.1 i = (0 : Fin 3)}) :=
    MeasurableSet.iInter fun i => by
    by_cases hi : n ≤ i
    · simpa only [hi, true_implies, Function.comp_apply] using
        (((measurable_pi_apply i).comp hprefix).eq_const (0 : Fin 3)).setOf
    · have he : {r : RMinusSidePresentation x | n ≤ i → r.code.1 i = (0 : Fin 3)} =
          Set.univ := by
        ext r
        simp [hi]
      rw [he]
      exact MeasurableSet.univ
  exact MeasurableSet.inter (MeasurableSet.inter hA hB) hC

/-- Helper toward Lemma 5.5. Coherent right codes vary measurably on the
certified coherent-path subtype. -/
theorem measurable_thinSideCode_onCoherentRight (x : XDP) :
    Measurable (fun q : Coherent x =>
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1) := by
  have h := measurable_rightThinCodeVal.comp (measurable_coherentRightThinCode x)
  convert h using 1
  funext q
  exact (coherentRightThinCode_val x q).symm

/-- Helper toward Lemma 5.5. The certified presentation/path domain is
measurable and expresses prefix validity together with exact code agreement. -/
theorem measurableSet_rMinusCanonicalSide_certifiedDomain (x : XDP) :
    MeasurableSet {z : RMinusSidePresentation x × Coherent x |
      z.1.prefixValid ∧
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right z.2.1 =
          z.1.code.2} := by
  have hp : MeasurableSet {z : RMinusSidePresentation x × Coherent x |
      z.1.prefixValid} :=
    (measurableSet_rMinusPrefixValid x).preimage measurable_fst
  have hcode : Measurable (fun z : RMinusSidePresentation x × Coherent x => z.1.code.2) :=
    measurable_snd.comp (measurable_snd.comp
      ((measurable_rMinusSidePresentation_coordinates x).comp measurable_fst))
  have heq :
      {z : RMinusSidePresentation x × Coherent x |
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right z.2.1 = z.1.code.2} =
        ⋂ s : ℕ, {z | (coherentRightThinCode x z.2 s).1 = z.1.code.2 s} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hz s
      calc
        (coherentRightThinCode x z.2 s).1 =
            rightThinCodeVal (coherentRightThinCode x z.2) s := rfl
        _ = thinSideCode x renewalTime renewalTime_positiveSuccessTime .right z.2.1 s :=
          congrFun (coherentRightThinCode_val x z.2) s
        _ = z.1.code.2 s := congrFun hz s
    · intro hz
      apply funext
      intro s
      calc
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right z.2.1 s =
            (coherentRightThinCode x z.2 s).1 :=
          (congrFun (coherentRightThinCode_val x z.2) s).symm
        _ = z.1.code.2 s := hz s
  have hc : MeasurableSet {z : RMinusSidePresentation x × Coherent x |
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right z.2.1 = z.1.code.2} := by
    rw [heq]
    exact MeasurableSet.iInter fun s => by
      have hleft : Measurable (fun z : RMinusSidePresentation x × Coherent x =>
          (coherentRightThinCode x z.2 s).1) :=
        measurable_subtype_coe.comp
          ((measurable_pi_apply s).comp
            ((measurable_coherentRightThinCode x).comp measurable_snd))
      have hright : Measurable (fun z : RMinusSidePresentation x × Coherent x =>
          z.1.code.2 s) := (measurable_pi_apply s).comp hcode
      have heqCoord :
          {z : RMinusSidePresentation x × Coherent x |
            (coherentRightThinCode x z.2 s).1 = z.1.code.2 s} =
            ⋃ v : RightThinValue s,
              {z | (coherentRightThinCode x z.2 s).1 = v.1} ∩
                {z | z.1.code.2 s = v.1} := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro hz
          exact ⟨coherentRightThinCode x z.2 s, rfl, hz.symm⟩
        · rintro ⟨v, hv, hg⟩
          exact hv.trans hg.symm
      rw [heqCoord]
      exact MeasurableSet.iUnion fun v =>
        ((hleft.eq_const v.1).setOf).inter ((hright.eq_const v.1).setOf)
  simpa only [Set.ofPred_and] using MeasurableSet.inter hp hc

/-- Helper toward Lemma 5.5. A fixed prefix edge glues to a specified
hatted edge precisely when that edge occurs at one of the prefix boundary
indices, a measurable event on coherent right paths. -/
theorem measurableSet_rMinusCodeEdgeGluing_fixedPrefixHatted
    (x : XDP) (F : State) (a : {e : ℕ // e < F.nextEdge}) (b : ℕ) :
    MeasurableSet {q : Coherent x |
      ∃ e : {e : ℕ // e ∈ (geometricSideSubmap x renewalTime
          renewalTime_positiveSuccessTime .right q).edges},
        e.1 = b ∧ rMinusCodeEdgeGluing F
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
          (.inl a) (.inr e)} := by
  let M (q : Coherent x) :=
    geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
  have he :
      {q : Coherent x | ∃ e : {e : ℕ // e ∈ (M q).edges}, e.1 = b ∧
        rMinusCodeEdgeGluing F (M q) (.inl a) (.inr e)} =
      {q | b ∈ (M q).edges} ∩
        ⋃ i : ℕ,
          {q | (F.active :: F.UR)[i]? = some a.1} ∩
            {q | ((M q).boundary i).1 = b} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion,
      rMinusCodeEdgeGluing]
    constructor
    · rintro ⟨e, he, i, hi, hb⟩
      have hmem : b ∈ (M q).edges := by simpa [he] using e.2
      exact ⟨hmem, i, hi, by simpa [he] using hb⟩
    · rintro ⟨hb, i, hi, hbd⟩
      exact ⟨⟨b, hb⟩, rfl, i, hi, hbd⟩
  have hmem : MeasurableSet {q : Coherent x | b ∈ (M q).edges} := by
    have h := measurable_geometricRightSide_edges x b
    have hh : MeasurableSet {q : Coherent x | decide (b ∈ (M q).edges) = true} :=
      (h.eq_const true).setOf
    simpa only [decide_eq_true_eq] using hh
  rw [he]
  refine MeasurableSet.inter hmem ?_
  exact MeasurableSet.iUnion fun i =>
    MeasurableSet.inter (MeasurableSet.const ((F.active :: F.UR)[i]? = some a.1))
      (((measurable_fst.comp (measurable_geometricRightSide_boundary x i)).eq_const b).setOf)

/-- Helper toward Lemma 5.5. A finite chain in a symmetric generator; the
empty chain includes equality, even for isolated tokens. -/
@[expose] def rMinusFiniteGluingChain {α : Type*} (R : α → α → Prop)
    (a : α) : List α → α → Prop
  | [], b => a = b
  | c :: l, b => (R a c ∨ R c a) ∧ rMinusFiniteGluingChain R c l b

/-- Helper toward Lemma 5.5. Equivalence closure is exactly existence of a
finite symmetric-generator chain, with no length bound. -/
theorem rMinusEqvGen_iff_exists_finiteGluingChain {α : Type*}
    (R : α → α → Prop) (a b : α) :
    Relation.EqvGen R a b ↔ ∃ l, rMinusFiniteGluingChain R a l b := by
  rw [← Relation.EqvGen.reflTransGen_symmGen]
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], rfl⟩
    | @head a c h _ ih =>
      obtain ⟨l, hl⟩ := ih
      exact ⟨c :: l, h, hl⟩
  · rintro ⟨l, hl⟩
    induction l generalizing a with
    | nil =>
      change a = b at hl
      subst a
      exact .refl
    | cons c l ih => exact (ih c hl.2).head hl.1

/-- Helper toward Lemma 5.5. If every fixed generator event is measurable,
then each fixed pair's equivalence-closure event is measurable by countably
many finite chains. -/
theorem measurableSet_rMinusEqvGen {β α : Type*} [MeasurableSpace β]
    [Countable α] (R : β → α → α → Prop)
    (hR : ∀ a b, MeasurableSet {z : β | R z a b}) (a b : α) :
    MeasurableSet {z : β | Relation.EqvGen (R z) a b} := by
  have hchain (l : List α) :
      MeasurableSet {z : β | rMinusFiniteGluingChain (R z) a l b} := by
    induction l generalizing a with
    | nil => exact MeasurableSet.const (a = b)
    | cons c l ih => exact ((hR a c).union (hR c a)).inter (ih c)
  have he : {z : β | Relation.EqvGen (R z) a b} =
      ⋃ l : List α, {z | rMinusFiniteGluingChain (R z) a l b} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion,
      rMinusEqvGen_iff_exists_finiteGluingChain]
  rw [he]
  exact MeasurableSet.iUnion hchain














































































































end DirectedDistances.PaperProofs.Section5
