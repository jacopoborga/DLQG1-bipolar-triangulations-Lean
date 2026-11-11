/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusCanonicalCodingMeasurable
public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusRawGluingMeasurable

/-! Countable finite-chain certificates for raw gluing and measurable minimal
tokens on presentation/path pairs. Descent from these pairs to presentations
alone is a separate obligation; no hatted-label reconstruction is assumed. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

local instance : MeasurableSingletonClass (Sum ℕ ℕ) where
  measurableSet_singleton a := by
    cases a with
    | inl a =>
      simpa only [Set.image_singleton] using
        (show MeasurableSet (Sum.inl '' ({a} : Set ℕ) : Set (Sum ℕ ℕ)) from
          (measurableSet_singleton a).inl_image)
    | inr a =>
      simpa only [Set.image_singleton] using
        (show MeasurableSet (Sum.inr '' ({a} : Set ℕ) : Set (Sum ℕ ℕ)) from
          (measurableSet_singleton a).inr_image)

/-- Helper toward Lemma 5.5. A finite chain in the symmetric generator;
the empty chain records equality, including isolated geometric edges. -/
@[expose] def lMinusFiniteGluingChain {α : Type*} (R : α → α → Prop)
    (a : α) : List α → α → Prop
  | [], b => a = b
  | c :: l, b => (R a c ∨ R c a) ∧ lMinusFiniteGluingChain R c l b

/-- Helper toward Lemma 5.5. The equivalence closure is exactly existence
of a finite chain, without any bounded-length or attainment assumption. -/
theorem lMinusEqvGen_iff_exists_finiteGluingChain {α : Type*}
    (R : α → α → Prop) (a b : α) :
    Relation.EqvGen R a b ↔ ∃ l, lMinusFiniteGluingChain R a l b := by
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
    | cons c l ih =>
      exact (ih c hl.2).head hl.1

/-- Helper toward Lemma 5.5. The raw generator on fixed block-tagged
edge labels, before restricting hatted labels to their geometric carrier. -/
@[expose] def lMinusRawEdgeGenerator {x : XDP}
    (z : LMinusSidePresentation x × (ℕ → ℤ × ℤ)) :
    Sum ℕ ℕ → Sum ℕ ℕ → Prop
  | .inl a, .inr b => lMinusRawCodeEdgeGluing z.1 z.2 a b
  | _, _ => False

/-- Helper toward Lemma 5.5. Each fixed raw generator event is measurable. -/
theorem measurableSet_lMinusRawEdgeGenerator (x : XDP) (a b : Sum ℕ ℕ) :
    MeasurableSet {z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) |
      lMinusRawEdgeGenerator z a b} := by
  cases a <;> cases b
  · exact MeasurableSet.empty
  · exact measurableSet_lMinusRawCodeEdgeGluing x _ _
  · exact MeasurableSet.empty
  · exact MeasurableSet.empty

/-- Helper toward Lemma 5.5. A fixed finite-chain certificate is a finite
intersection of measurable symmetric generator events. -/
theorem measurableSet_lMinusRawFiniteGluingChain (x : XDP)
    (a b : Sum ℕ ℕ) (l : List (Sum ℕ ℕ)) :
    MeasurableSet {z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) |
      lMinusFiniteGluingChain (lMinusRawEdgeGenerator z) a l b} := by
  induction l generalizing a with
  | nil => exact MeasurableSet.const (a = b)
  | cons c l ih =>
    exact ((measurableSet_lMinusRawEdgeGenerator x a c).union
      (measurableSet_lMinusRawEdgeGenerator x c a)).inter (ih c)

/-- Helper toward Lemma 5.5. The raw equivalence event is the countable
union over finite chains of their finite intersection events. -/
theorem setOf_lMinusRawEdgeEqvGen_eq_iUnion (x : XDP) (a b : Sum ℕ ℕ) :
    {z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) |
      Relation.EqvGen (lMinusRawEdgeGenerator z) a b} =
      ⋃ l : List (Sum ℕ ℕ),
        {z | lMinusFiniteGluingChain (lMinusRawEdgeGenerator z) a l b} := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion,
    lMinusEqvGen_iff_exists_finiteGluingChain]

/-- Helper toward Lemma 5.5. Finite-chain gluing closure is measurable
for each fixed pair of raw tokens, including all missing-edge tokens. -/
theorem measurableSet_lMinusRawEdgeEqvGen (x : XDP) (a b : Sum ℕ ℕ) :
    MeasurableSet {z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) |
      Relation.EqvGen (lMinusRawEdgeGenerator z) a b} := by
  rw [setOf_lMinusRawEdgeEqvGen_eq_iUnion]
  exact MeasurableSet.iUnion (measurableSet_lMinusRawFiniteGluingChain x a b)

/-- Helper toward Lemma 5.5. Numeric candidates in the raw edge closure
use the same even/odd token convention as the canonical coding. -/
@[expose] def lMinusRawEdgeClosureCandidate {x : XDP}
    (z : LMinusSidePresentation x × (ℕ → ℤ × ℤ))
    (a : Sum ℕ ℕ) (n : ℕ) : Prop :=
  ∃ b : Sum ℕ ℕ, lMinusRawVertexToken b = n ∧
    Relation.EqvGen (lMinusRawEdgeGenerator z) b a

/-- Helper toward Lemma 5.5. Every raw edge has a candidate, even if it
participates in no gluing. -/
theorem lMinusRawEdgeClosureCandidate_exists {x : XDP}
    (z : LMinusSidePresentation x × (ℕ → ℤ × ℤ)) (a : Sum ℕ ℕ) :
    ∃ n, lMinusRawEdgeClosureCandidate z a n :=
  ⟨lMinusRawVertexToken a, a, rfl, Relation.EqvGen.refl a⟩

/-- Helper toward Lemma 5.5. Fixed minimal-token candidate events are
countable unions of measurable closure events. -/
theorem measurableSet_lMinusRawEdgeClosureCandidate (x : XDP)
    (a : Sum ℕ ℕ) (n : ℕ) :
    MeasurableSet {z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) |
      lMinusRawEdgeClosureCandidate z a n} := by
  unfold lMinusRawEdgeClosureCandidate
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun b =>
    (MeasurableSet.const (lMinusRawVertexToken b = n)).inter
      (measurableSet_lMinusRawEdgeEqvGen x b a))

/-- Helper toward Lemma 5.5. The least raw edge token in its generated
equivalence class, on presentation/path pairs. -/
@[expose] noncomputable def lMinusRawEdgeClosureId {x : XDP}
    (z : LMinusSidePresentation x × (ℕ → ℤ × ℤ)) (a : Sum ℕ ℕ) : ℕ :=
  Nat.find (lMinusRawEdgeClosureCandidate_exists z a)

/-- Helper toward Lemma 5.5. Minimization over the measurable closure
gives a measurable ID for every fixed raw edge token. -/
theorem measurable_lMinusRawEdgeClosureId (x : XDP) (a : Sum ℕ ℕ) :
    Measurable (fun z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) =>
      lMinusRawEdgeClosureId z a) :=
  measurable_find (fun z => lMinusRawEdgeClosureCandidate_exists z a)
    (measurableSet_lMinusRawEdgeClosureCandidate x a)

/-- Helper toward Lemma 5.5. Restriction of the raw gluing test to
coherent hatted paths retains measurability. -/
theorem measurableSet_lMinusCoherentRawCodeEdgeGluing (x : XDP) (a b : ℕ) :
    MeasurableSet {z : LMinusSidePresentation x × Coherent x |
      lMinusRawCodeEdgeGluing z.1 z.2.val a b} :=
  (measurableSet_lMinusRawCodeEdgeGluing x a b).preimage
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

/-- Helper toward Lemma 5.5. The concrete normal-form candidate test
for either raw edge block, on coherent presentation/path pairs. -/
@[expose] def lMinusCoherentEdgeCandidate {x : XDP}
    (z : LMinusSidePresentation x × Coherent x) : Sum ℕ ℕ → ℕ → Prop
  | .inl a, n => n = 2 * a ∨ ∃ b : ℕ,
      b ∈ (lMinusCoherentLeftSide x z.2).edges ∧ n = 2 * b + 1 ∧
        lMinusRawCodeEdgeGluing z.1 z.2.val a b
  | .inr b, n => n = 2 * b + 1 ∨ ∃ a : ℕ,
      n = 2 * a ∧ lMinusRawCodeEdgeGluing z.1 z.2.val a b

/-- Helper toward Lemma 5.5. The normal-form test agrees with the actual
canonical quotient candidate for every allocated edge representative. -/
theorem lMinusCoherentEdgeCandidate_iff {x : XDP}
    (r : LMinusSidePresentation x) (q : Coherent x)
    (a : Sum ℕ (lMinusCoherentLeftSide x q).edges) (n : ℕ) :
    lMinusCoherentEdgeCandidate (r, q) (a.map id Subtype.val) n ↔
      lMinusCanonicalEdgeCandidate r (lMinusCoherentLeftSide x q) (⟦a⟧) n := by
  cases a with
  | inl a =>
    rw [lMinusCanonicalEdgeCandidate_primed_iff]
    change (n = 2 * a ∨ ∃ b : ℕ, b ∈ _ ∧ n = 2 * b + 1 ∧
      lMinusRawCodeEdgeGluing r q.val a b) ↔ _
    constructor
    · rintro (h | ⟨b, hb, hn, hg⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨b, hb⟩, hn,
          (lMinusRawCodeEdgeGluing_iff_codeEdgeGluing r q a ⟨b, hb⟩).mp hg⟩
    · rintro (h | ⟨b, hn, hg⟩)
      · exact Or.inl h
      · exact Or.inr ⟨b.val, b.property, hn,
          (lMinusRawCodeEdgeGluing_iff_codeEdgeGluing r q a b).mpr hg⟩
  | inr b =>
    rw [lMinusCanonicalEdgeCandidate_hatted_iff]
    exact or_congr Iff.rfl (exists_congr (fun a => and_congr_right (fun _ =>
      lMinusRawCodeEdgeGluing_iff_codeEdgeGluing r q a b)))

/-- Helper toward Lemma 5.5. All normal-form edge candidate events are
measurable on coherent presentation/path pairs. -/
theorem measurableSet_lMinusCoherentEdgeCandidate (x : XDP)
    (a : Sum ℕ ℕ) (n : ℕ) :
    MeasurableSet {z : LMinusSidePresentation x × Coherent x |
      lMinusCoherentEdgeCandidate z a n} := by
  cases a with
  | inl a =>
    simp only [lMinusCoherentEdgeCandidate, Set.ofPred_or]
    apply MeasurableSet.union (MeasurableSet.const (n = 2 * a))
    change MeasurableSet {z : LMinusSidePresentation x × Coherent x |
      ∃ b : ℕ, b ∈ (lMinusCoherentLeftSide x z.2).edges ∧
        n = 2 * b + 1 ∧ lMinusRawCodeEdgeGluing z.1 z.2.val a b}
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun b =>
      ((measurableSet_lMinusCoherentLeftSide_edges x b).preimage measurable_snd).inter
        ((MeasurableSet.const (n = 2 * b + 1)).inter
          (measurableSet_lMinusCoherentRawCodeEdgeGluing x a b)))
  | inr b =>
    simp only [lMinusCoherentEdgeCandidate, Set.ofPred_or]
    apply MeasurableSet.union (MeasurableSet.const (n = 2 * b + 1))
    change MeasurableSet {z : LMinusSidePresentation x × Coherent x |
      ∃ a : ℕ, n = 2 * a ∧ lMinusRawCodeEdgeGluing z.1 z.2.val a b}
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun a =>
      (MeasurableSet.const (n = 2 * a)).inter
        (measurableSet_lMinusCoherentRawCodeEdgeGluing x a b))

/-- Helper toward Lemma 5.5. Every coherent normal-form test has its
own raw edge token as a candidate. -/
theorem lMinusCoherentEdgeCandidate_exists {x : XDP}
    (z : LMinusSidePresentation x × Coherent x) (a : Sum ℕ ℕ) :
    ∃ n, lMinusCoherentEdgeCandidate z a n := by
  cases a with
  | inl a => exact ⟨2 * a, Or.inl rfl⟩
  | inr b => exact ⟨2 * b + 1, Or.inl rfl⟩

/-- Helper toward Lemma 5.5. Least-token edge IDs in the normal form,
extended to unallocated hatted raw labels only for coordinate testing. -/
@[expose] noncomputable def lMinusCoherentEdgeId {x : XDP}
    (z : LMinusSidePresentation x × Coherent x) (a : Sum ℕ ℕ) : ℕ :=
  Nat.find (lMinusCoherentEdgeCandidate_exists z a)

/-- Helper toward Lemma 5.5. The measurable normal-form ID is exactly
the existing canonical ID on every actual geometric edge. -/
theorem lMinusCoherentEdgeId_eq {x : XDP}
    (r : LMinusSidePresentation x) (q : Coherent x)
    (a : Sum ℕ (lMinusCoherentLeftSide x q).edges) :
    lMinusCoherentEdgeId (r, q) (a.map id Subtype.val) =
      lMinusCanonicalEdgeId r (lMinusCoherentLeftSide x q) (⟦a⟧) := by
  apply Nat.le_antisymm
  · apply Nat.find_min'
    exact (lMinusCoherentEdgeCandidate_iff r q a _).mpr
      (lMinusCanonicalEdgeId_spec r _ _)
  · apply Nat.find_min'
    exact (lMinusCoherentEdgeCandidate_iff r q a _).mp
      (Nat.find_spec (lMinusCoherentEdgeCandidate_exists _ _))

/-- Helper toward Lemma 5.5. Each least-token edge ID is measurable on
the coherent presentation/path product, without any chosen preimage. -/
theorem measurable_lMinusCoherentEdgeId (x : XDP) (a : Sum ℕ ℕ) :
    Measurable (fun z : LMinusSidePresentation x × Coherent x =>
      lMinusCoherentEdgeId z a) :=
  measurable_find (fun z => lMinusCoherentEdgeCandidate_exists z a)
    (measurableSet_lMinusCoherentEdgeCandidate x a)

/-- Helper toward Lemma 5.5. Vertex gluing has a countable certificate
consisting of a shared raw edge and one of its two actual endpoints. -/
theorem lMinusCodeVertexGluing_iff_raw {x : XDP}
    (r : LMinusSidePresentation x) (q : Coherent x) (u v : Sum ℕ ℕ) :
    lMinusCodeVertexGluing r (lMinusCoherentLeftSide x q) u v ↔
      ∃ a b : ℕ, b ∈ (lMinusCoherentLeftSide x q).edges ∧
        lMinusRawCodeEdgeGluing r q.val a b ∧ ∃ s : Bool,
          Sum.inl (kmswLimitDartVertex r.code.1
            (a, s ^^ lMinusCodePrimedSideFlip r a)) = u ∧
          Sum.inr (if s then (lMinusCoherentLeftSide x q).east b
            else (lMinusCoherentLeftSide x q).west b) = v := by
  constructor
  · rintro ⟨a, b, hg, s, hu, hv⟩
    cases a with
    | inr a => exact False.elim hg
    | inl a =>
      cases b with
      | inl b => exact False.elim hg
      | inr b =>
        exact ⟨a, b.val, b.property,
          (lMinusRawCodeEdgeGluing_iff_codeEdgeGluing r q a b).mpr hg, s, hu, hv⟩
  · rintro ⟨a, b, hb, hg, s, hu, hv⟩
    exact ⟨.inl a, .inr ⟨b, hb⟩,
      (lMinusRawCodeEdgeGluing_iff_codeEdgeGluing r q a ⟨b, hb⟩).mp hg,
      s, hu, hv⟩

/-- Helper toward Lemma 5.5. The original vertex generator is measurable
on coherent presentation/path pairs, including the primed orientation flip. -/
theorem measurableSet_lMinusCoherentVertexGluing (x : XDP) (u v : Sum ℕ ℕ) :
    MeasurableSet {z : LMinusSidePresentation x × Coherent x |
      lMinusCodeVertexGluing z.1 (lMinusCoherentLeftSide x z.2) u v} := by
  have hp (a : ℕ) (s : Bool) : MeasurableSet
      {z : LMinusSidePresentation x × Coherent x |
        (Sum.inl (kmswLimitDartVertex z.1.code.1
          (a, s ^^ lMinusCodePrimedSideFlip z.1 a)) : Sum ℕ ℕ) = u} := by
    cases u with
    | inl u =>
      simpa only [Sum.inl.injEq, Function.comp_def] using
        (((measurable_lMinusPrimedDartEndpoint x a s).comp measurable_fst).eq_const u).setOf
    | inr u => simp only [Sum.inl_ne_inr, Set.ofPred_false, MeasurableSet.empty]
  have hh (b : ℕ) (s : Bool) : MeasurableSet
      {z : LMinusSidePresentation x × Coherent x |
        (Sum.inr (if s then (lMinusCoherentLeftSide x z.2).east b
          else (lMinusCoherentLeftSide x z.2).west b) : Sum ℕ ℕ) = v} := by
    cases v with
    | inl v => simp only [Sum.inr_ne_inl, Set.ofPred_false, MeasurableSet.empty]
    | inr v =>
      simpa only [Sum.inr.injEq, Set.preimage_ofPred_eq] using
        (measurableSet_lMinusCoherentLeftSide_incident x (b, s) v).preimage measurable_snd
  simp only [lMinusCodeVertexGluing_iff_raw, Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
    ((measurableSet_lMinusCoherentLeftSide_edges x b).preimage measurable_snd).inter
      ((measurableSet_lMinusCoherentRawCodeEdgeGluing x a b).inter
        (MeasurableSet.iUnion (fun s => (hp a s).inter (hh b s))))))

/-- Helper toward Lemma 5.5. Every fixed finite vertex-chain event is a
finite intersection of the measurable original vertex generator events. -/
theorem measurableSet_lMinusCoherentVertexChain (x : XDP)
    (u v : Sum ℕ ℕ) (l : List (Sum ℕ ℕ)) :
    MeasurableSet {z : LMinusSidePresentation x × Coherent x |
      lMinusFiniteGluingChain
        (lMinusCodeVertexGluing z.1 (lMinusCoherentLeftSide x z.2)) u l v} := by
  induction l generalizing u with
  | nil => exact MeasurableSet.const (u = v)
  | cons w l ih =>
    exact ((measurableSet_lMinusCoherentVertexGluing x u w).union
      (measurableSet_lMinusCoherentVertexGluing x w u)).inter (ih w)

/-- Helper toward Lemma 5.5. The actual vertex equivalence closure is
measurable for every fixed pair of block-tagged raw vertices. -/
theorem measurableSet_lMinusCoherentVertexSetoid (x : XDP) (u v : Sum ℕ ℕ) :
    MeasurableSet {z : LMinusSidePresentation x × Coherent x |
      lMinusCodeVertexSetoid z.1 (lMinusCoherentLeftSide x z.2) u v} := by
  change MeasurableSet {z : LMinusSidePresentation x × Coherent x |
    Relation.EqvGen (lMinusCodeVertexGluing z.1 (lMinusCoherentLeftSide x z.2)) u v}
  simp only [lMinusEqvGen_iff_exists_finiteGluingChain, Set.ofPred_exists]
  exact MeasurableSet.iUnion (measurableSet_lMinusCoherentVertexChain x u v)

/-- Helper toward Lemma 5.5. Raw vertex candidates for the unchanged
vertex quotient, without its allocated-subtype restriction. -/
@[expose] def lMinusCoherentVertexCandidate {x : XDP}
    (z : LMinusSidePresentation x × Coherent x) (u : Sum ℕ ℕ) (n : ℕ) : Prop :=
  ∃ v : Sum ℕ ℕ, lMinusRawVertexToken v = n ∧
    lMinusCodeVertexSetoid z.1 (lMinusCoherentLeftSide x z.2) v u

/-- Helper toward Lemma 5.5. Every raw vertex class has a candidate. -/
theorem lMinusCoherentVertexCandidate_exists {x : XDP}
    (z : LMinusSidePresentation x × Coherent x) (u : Sum ℕ ℕ) :
    ∃ n, lMinusCoherentVertexCandidate z u n :=
  ⟨lMinusRawVertexToken u, u, rfl, Relation.EqvGen.refl u⟩

/-- Helper toward Lemma 5.5. Fixed raw vertex candidate events are measurable. -/
theorem measurableSet_lMinusCoherentVertexCandidate (x : XDP)
    (u : Sum ℕ ℕ) (n : ℕ) :
    MeasurableSet {z : LMinusSidePresentation x × Coherent x |
      lMinusCoherentVertexCandidate z u n} := by
  unfold lMinusCoherentVertexCandidate
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun v =>
    (MeasurableSet.const (lMinusRawVertexToken v = n)).inter
      (measurableSet_lMinusCoherentVertexSetoid x v u))

/-- Helper toward Lemma 5.5. The least token of the original raw vertex
quotient, before restricting to allocated classes. -/
@[expose] noncomputable def lMinusCoherentVertexId {x : XDP}
    (z : LMinusSidePresentation x × Coherent x) (u : Sum ℕ ℕ) : ℕ :=
  Nat.find (lMinusCoherentVertexCandidate_exists z u)

/-- Helper toward Lemma 5.5. All raw vertex minimal-token IDs are measurable. -/
theorem measurable_lMinusCoherentVertexId (x : XDP) (u : Sum ℕ ℕ) :
    Measurable (fun z : LMinusSidePresentation x × Coherent x =>
      lMinusCoherentVertexId z u) :=
  measurable_find (fun z => lMinusCoherentVertexCandidate_exists z u)
    (measurableSet_lMinusCoherentVertexCandidate x u)

/-- Helper toward Lemma 5.5. The measurable vertex ID agrees with the
existing canonical ID whenever that raw vertex class is allocated. -/
theorem lMinusCoherentVertexId_eq {x : XDP}
    (r : LMinusSidePresentation x) (q : Coherent x) (u : Sum ℕ ℕ)
    (hu : (⟦u⟧ : LMinusCodeRawVertex r (lMinusCoherentLeftSide x q)) ∈
      lMinusCodeVertexAllocated r (lMinusCoherentLeftSide x q)) :
    lMinusCoherentVertexId (r, q) u =
      lMinusCanonicalVertexId r (lMinusCoherentLeftSide x q) ⟨⟦u⟧, hu⟩ := by
  have hc (n : ℕ) : lMinusCoherentVertexCandidate (r, q) u n ↔
      lMinusCanonicalVertexCandidate r (lMinusCoherentLeftSide x q) ⟦u⟧ n := by
    exact exists_congr (fun v => and_congr_right (fun _ =>
      ⟨Quotient.sound, Quotient.exact⟩))
  apply Nat.le_antisymm
  · exact Nat.find_min' _ ((hc _).mpr (Nat.find_spec
      (lMinusCanonicalVertexCandidate_exists r _ ⟦u⟧)))
  · exact Nat.find_min' _ ((hc _).mp (Nat.find_spec
      (lMinusCoherentVertexCandidate_exists (r, q) u)))

/-- Helper toward Lemma 5.5. Edge membership in the canonical side is
exactly the range of the measurable block-token IDs over allocated raw edges. -/
theorem lMinusCanonicalSide_mem_edges_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (n : ℕ) :
    n ∈ (lMinusCanonicalSide x r q hf).edges ↔
      (∃ a : ℕ, lMinusCoherentEdgeId (r, q) (.inl a) = n) ∨
      ∃ b : ℕ, b ∈ (lMinusCoherentLeftSide x q).edges ∧
        lMinusCoherentEdgeId (r, q) (.inr b) = n := by
  constructor
  · rintro ⟨e, he⟩
    revert he
    refine Quotient.inductionOn e ?_
    intro a ha
    cases a with
    | inl a => exact Or.inl ⟨a, (lMinusCoherentEdgeId_eq r q (.inl a)).trans ha⟩
    | inr b => exact Or.inr ⟨b.val, b.property,
        (lMinusCoherentEdgeId_eq r q (.inr b)).trans ha⟩
  · rintro (⟨a, ha⟩ | ⟨b, hb, hn⟩)
    · exact ⟨⟦Sum.inl a⟧, (lMinusCoherentEdgeId_eq r q (.inl a)).symm.trans ha⟩
    · exact ⟨⟦Sum.inr ⟨b, hb⟩⟧,
        (lMinusCoherentEdgeId_eq r q (.inr ⟨b, hb⟩)).symm.trans hn⟩

/-- Helper toward Lemma 5.5. Vertex membership in the canonical side
uses exactly the original allocated vertex classes, with no new allocation. -/
theorem lMinusCanonicalSide_mem_vertices_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (n : ℕ) :
    n ∈ (lMinusCanonicalSide x r q hf).vertices ↔
      (∃ a : ℕ, lMinusCoherentVertexId (r, q) (.inl a) = n) ∨
      ∃ b : ℕ, b ∈ (lMinusCoherentLeftSide x q).vertices ∧
        lMinusCoherentVertexId (r, q) (.inr b) = n := by
  constructor
  · rintro ⟨⟨v, hv⟩, he⟩
    rcases hv with ⟨a, ha⟩ | ⟨b, hb⟩
    · subst v
      exact Or.inl ⟨a, (lMinusCoherentVertexId_eq r q (.inl a) _).trans he⟩
    · subst v
      exact Or.inr ⟨b.val, b.property,
        (lMinusCoherentVertexId_eq r q (.inr b.val) _).trans he⟩
  · rintro (⟨a, ha⟩ | ⟨b, hb, hn⟩)
    · let h : (⟦Sum.inl a⟧ : LMinusCodeRawVertex r (lMinusCoherentLeftSide x q)) ∈
          lMinusCodeVertexAllocated r (lMinusCoherentLeftSide x q) := Or.inl ⟨a, rfl⟩
      exact ⟨⟨⟦Sum.inl a⟧, h⟩, (lMinusCoherentVertexId_eq r q (.inl a) h).symm.trans ha⟩
    · let h : (⟦Sum.inr b⟧ : LMinusCodeRawVertex r (lMinusCoherentLeftSide x q)) ∈
          lMinusCodeVertexAllocated r (lMinusCoherentLeftSide x q) :=
          Or.inr ⟨⟨b, hb⟩, rfl⟩
      exact ⟨⟨⟦Sum.inr b⟧, h⟩, (lMinusCoherentVertexId_eq r q (.inr b) h).symm.trans hn⟩

/-- Helper toward Lemma 5.5. The canonical constructor's actual domain
of coherent pairs with its original primed finite-incidence certificate.
This is not a domain of presentations alone. -/
abbrev LMinusCanonicalCodingDomain (x : XDP) :=
  {z : LMinusSidePresentation x × Coherent x // KMSWFiniteIncidence z.1.code.1}

/-- Helper toward Lemma 5.5. The unchanged canonical side on its domain
of coherent pairs; no selection of a coherent preimage is made. -/
@[expose] noncomputable def lMinusCanonicalSideOnCoherent (x : XDP)
    (z : LMinusCanonicalCodingDomain x) : GeometricSideSubmap :=
  lMinusCanonicalSide x z.val.1 z.val.2 z.property

/-- Helper toward Lemma 5.5. Every canonical edge membership coordinate
is measurable on the certified coherent-pair domain. -/
theorem measurableSet_lMinusCanonicalSideOnCoherent_edges (x : XDP) (n : ℕ) :
    MeasurableSet {z : LMinusCanonicalCodingDomain x |
      n ∈ (lMinusCanonicalSideOnCoherent x z).edges} := by
  simp only [lMinusCanonicalSideOnCoherent, lMinusCanonicalSide_mem_edges_iff,
    Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion (fun a =>
      (((measurable_lMinusCoherentEdgeId x (.inl a)).comp
        measurable_subtype_coe).eq_const n).setOf)
  · exact MeasurableSet.iUnion (fun b =>
      ((measurableSet_lMinusCoherentLeftSide_edges x b).preimage
        (measurable_snd.comp measurable_subtype_coe)).inter
      (((measurable_lMinusCoherentEdgeId x (.inr b)).comp
        measurable_subtype_coe).eq_const n).setOf)

/-- Helper toward Lemma 5.5. Every canonical vertex membership
coordinate is measurable on the certified coherent-pair domain. -/
theorem measurableSet_lMinusCanonicalSideOnCoherent_vertices (x : XDP) (n : ℕ) :
    MeasurableSet {z : LMinusCanonicalCodingDomain x |
      n ∈ (lMinusCanonicalSideOnCoherent x z).vertices} := by
  simp only [lMinusCanonicalSideOnCoherent, lMinusCanonicalSide_mem_vertices_iff,
    Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion (fun a =>
      (((measurable_lMinusCoherentVertexId x (.inl a)).comp
        measurable_subtype_coe).eq_const n).setOf)
  · exact MeasurableSet.iUnion (fun b =>
      ((measurableSet_lMinusCoherentLeftSide_vertices x b).preimage
        (measurable_snd.comp measurable_subtype_coe)).inter
      (((measurable_lMinusCoherentVertexId x (.inr b)).comp
        measurable_subtype_coe).eq_const n).setOf)

/-- Helper toward Lemma 5.5. Joint evaluation of the measurable edge
ID at a variable countable raw token is measurable. -/
theorem measurable_lMinusCoherentEdgeId_uncurry (x : XDP) :
    Measurable (fun z : Sum ℕ ℕ × (LMinusSidePresentation x × Coherent x) =>
      lMinusCoherentEdgeId z.2 z.1) :=
  measurable_from_prod_countable_right (measurable_lMinusCoherentEdgeId x)

/-- Helper toward Lemma 5.5. Joint evaluation of the measurable vertex
ID at a variable countable raw token is measurable. -/
theorem measurable_lMinusCoherentVertexId_uncurry (x : XDP) :
    Measurable (fun z : Sum ℕ ℕ × (LMinusSidePresentation x × Coherent x) =>
      lMinusCoherentVertexId z.2 z.1) :=
  measurable_from_prod_countable_right (measurable_lMinusCoherentVertexId x)

/-- Helper toward Lemma 5.5. Every full exterior boundary dart coordinate
is measurable on the certified coherent-pair domain. -/
theorem measurable_lMinusCanonicalSideOnCoherent_boundary (x : XDP) (i : ℕ) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      (lMinusCanonicalSideOnCoherent x z).boundary i) := by
  have hraw : Measurable (fun z : LMinusCanonicalCodingDomain x =>
      (Sum.inl (lMinusCodeExteriorBoundaryEdge z.val.1.code.1 i) : Sum ℕ ℕ)) :=
    measurable_inl.comp ((measurable_lMinusCodeExteriorBoundaryEdge_presentation_apply x i).comp
      (measurable_fst.comp measurable_subtype_coe))
  have hid := (measurable_lMinusCoherentEdgeId_uncurry x).comp
    (hraw.prodMk measurable_subtype_coe)
  convert hid.prodMk (measurable_const (a := true)) using 1
  funext z
  apply Prod.ext
  · exact (lMinusCoherentEdgeId_eq z.val.1 z.val.2
      (.inl (lMinusCodeExteriorBoundaryEdge z.val.1.code.1 i))).symm
  · rfl

/-- Helper toward Lemma 5.5. The raw endpoint reader on fixed ambient
block tokens, with exactly the original primed orientation correction. -/
@[expose] noncomputable def lMinusCoherentRawEndpoint {x : XDP}
    (z : LMinusSidePresentation x × Coherent x) (s : Bool) : Sum ℕ ℕ → Sum ℕ ℕ
  | .inl a => .inl (kmswLimitDartVertex z.1.code.1
      (a, s ^^ lMinusCodePrimedSideFlip z.1 a))
  | .inr b => .inr (if s then (lMinusCoherentLeftSide x z.2).east b
      else (lMinusCoherentLeftSide x z.2).west b)

/-- Helper toward Lemma 5.5. Fixed raw endpoint readers are measurable
on coherent pairs, before applying the measurable minimal vertex ID. -/
theorem measurable_lMinusCoherentRawEndpoint (x : XDP) (s : Bool) (a : Sum ℕ ℕ) :
    Measurable (fun z : LMinusSidePresentation x × Coherent x =>
      lMinusCoherentRawEndpoint z s a) := by
  cases a with
  | inl a =>
    exact measurable_inl.comp
      ((measurable_lMinusPrimedDartEndpoint x a s).comp measurable_fst)
  | inr b =>
    apply measurable_inr.comp
    apply measurable_to_countable'
    intro n
    exact (measurableSet_lMinusCoherentLeftSide_incident x (b, s) n).preimage
      measurable_snd

/-- Helper toward Lemma 5.5. The measurable endpoint-ID formula agrees
with the canonical whole endpoint at every allocated raw edge. -/
theorem lMinusCanonicalEndpointId_coherent_rep (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x) (s : Bool)
    (a : Sum ℕ (lMinusCoherentLeftSide x q).edges) :
    lMinusCanonicalEndpointId x r q s
        (lMinusCoherentEdgeId (r, q) (a.map id Subtype.val)) =
      lMinusCoherentVertexId (r, q)
        (lMinusCoherentRawEndpoint (r, q) s (a.map id Subtype.val)) := by
  rw [lMinusCoherentEdgeId_eq, lMinusCanonicalEndpointId_id]
  have hraw : lMinusCoherentRawEndpoint (r, q) s (a.map id Subtype.val) =
      lMinusCodeRawEndpoint r (lMinusCoherentLeftSide x q) s a := by
    cases a <;> rfl
  rw [hraw]
  exact (lMinusCoherentVertexId_eq r q
    (lMinusCodeRawEndpoint r (lMinusCoherentLeftSide x q) s a)
    (lMinusCodeEndpoint_allocated x r q s ⟦a⟧)).symm

/-- Helper toward Lemma 5.5. The total canonical endpoint reader is
characterized by countably many allocated representative tests and its
original value zero outside the geometric edge carrier. -/
theorem lMinusCanonicalEndpointId_eq_iff_coherent (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (s : Bool) (e v : ℕ) :
    lMinusCanonicalEndpointId x r q s e = v ↔
      (e ∉ (lMinusCanonicalSide x r q hf).edges ∧ 0 = v) ∨
      (∃ a : ℕ, lMinusCoherentEdgeId (r, q) (.inl a) = e ∧
        lMinusCoherentVertexId (r, q)
          (lMinusCoherentRawEndpoint (r, q) s (.inl a)) = v) ∨
      ∃ b : ℕ, b ∈ (lMinusCoherentLeftSide x q).edges ∧
        lMinusCoherentEdgeId (r, q) (.inr b) = e ∧
        lMinusCoherentVertexId (r, q)
          (lMinusCoherentRawEndpoint (r, q) s (.inr b)) = v := by
  constructor
  · intro h
    by_cases he : e ∈ (lMinusCanonicalSide x r q hf).edges
    · rcases (lMinusCanonicalSide_mem_edges_iff x r q hf e).mp he with
        ⟨a, ha⟩ | ⟨b, hb, hn⟩
      · exact Or.inr (Or.inl ⟨a, ha,
          (lMinusCanonicalEndpointId_coherent_rep x r q s (.inl a)).symm.trans
            (ha.symm ▸ h)⟩)
      · exact Or.inr (Or.inr ⟨b, hb, hn,
          (lMinusCanonicalEndpointId_coherent_rep x r q s (.inr ⟨b, hb⟩)).symm.trans
            (hn.symm ▸ h)⟩)
    · refine Or.inl ⟨he, ?_⟩
      change e ∉ Set.range (lMinusCanonicalEdgeId r (lMinusCoherentLeftSide x q)) at he
      simpa only [lMinusCanonicalEndpointId, dite_eq_right he] using h
  · rintro (⟨he, hv⟩ | ⟨a, ha, hv⟩ | ⟨b, hb, hn, hv⟩)
    · change e ∉ Set.range (lMinusCanonicalEdgeId r (lMinusCoherentLeftSide x q)) at he
      simpa only [lMinusCanonicalEndpointId, dite_eq_right he] using hv
    · rw [← ha]
      exact (lMinusCanonicalEndpointId_coherent_rep x r q s (.inl a)).trans hv
    · rw [← hn]
      exact (lMinusCanonicalEndpointId_coherent_rep x r q s (.inr ⟨b, hb⟩)).trans hv

/-- Helper toward Lemma 5.5. Every whole west/east endpoint coordinate
of the canonical side is measurable on the coherent-pair domain. -/
theorem measurable_lMinusCanonicalSideOnCoherent_endpoint (x : XDP)
    (s : Bool) (e : ℕ) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      lMinusCanonicalEndpointId x z.val.1 z.val.2 s e) := by
  have hv (a : Sum ℕ ℕ) : Measurable
      (fun z : LMinusCanonicalCodingDomain x =>
        lMinusCoherentVertexId z.val (lMinusCoherentRawEndpoint z.val s a)) := by
    have hr : Measurable (fun z : LMinusCanonicalCodingDomain x =>
        lMinusCoherentRawEndpoint z.val s a) :=
      (measurable_lMinusCoherentRawEndpoint x s a).comp measurable_subtype_coe
    have hpair : Measurable (fun z : LMinusCanonicalCodingDomain x =>
        (lMinusCoherentRawEndpoint z.val s a, z.val)) :=
      hr.prodMk measurable_subtype_coe
    simpa only [Function.comp_def] using
      (measurable_lMinusCoherentVertexId_uncurry x).comp hpair
  apply measurable_to_countable'
  intro v
  change MeasurableSet {z : LMinusCanonicalCodingDomain x |
    lMinusCanonicalEndpointId x z.val.1 z.val.2 s e = v}
  have hset : {z : LMinusCanonicalCodingDomain x |
      lMinusCanonicalEndpointId x z.val.1 z.val.2 s e = v} =
      {z : LMinusCanonicalCodingDomain x |
        (e ∉ (lMinusCanonicalSideOnCoherent x z).edges ∧ 0 = v) ∨
        (∃ a : ℕ, lMinusCoherentEdgeId z.val (.inl a) = e ∧
          lMinusCoherentVertexId z.val (lMinusCoherentRawEndpoint z.val s (.inl a)) = v) ∨
        ∃ b : ℕ, b ∈ (lMinusCoherentLeftSide x z.val.2).edges ∧
          lMinusCoherentEdgeId z.val (.inr b) = e ∧
          lMinusCoherentVertexId z.val (lMinusCoherentRawEndpoint z.val s (.inr b)) = v} := by
    ext z
    exact lMinusCanonicalEndpointId_eq_iff_coherent x z.val.1 z.val.2 z.property s e v
  rw [hset]
  simp only [Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  refine ((measurableSet_lMinusCanonicalSideOnCoherent_edges x e).compl.inter
    (MeasurableSet.const (0 = v))).union ?_
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion (fun a =>
      (((measurable_lMinusCoherentEdgeId x (.inl a)).comp
        measurable_subtype_coe).eq_const e).setOf.inter ((hv (.inl a)).eq_const v).setOf)
  · exact MeasurableSet.iUnion (fun b =>
      ((measurableSet_lMinusCoherentLeftSide_edges x b).preimage
        (measurable_snd.comp measurable_subtype_coe)).inter
      ((((measurable_lMinusCoherentEdgeId x (.inr b)).comp
        measurable_subtype_coe).eq_const e).setOf.inter ((hv (.inr b)).eq_const v).setOf))

/-- Helper toward Lemma 5.5. The root coordinate is the measurable
minimal token of the original hatted root class. -/
theorem measurable_lMinusCanonicalSideOnCoherent_root (x : XDP) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      (lMinusCanonicalSideOnCoherent x z).root) := by
  have hm := (measurable_lMinusCoherentVertexId x (.inr 0)).comp
    (measurable_subtype_coe (p := fun z : LMinusSidePresentation x × Coherent x =>
      KMSWFiniteIncidence z.1.code.1))
  convert hm using 1
  funext z
  exact (lMinusCoherentVertexId_eq z.val.1 z.val.2 (.inr 0) _).symm

/-- Helper toward Lemma 5.5. Six complete canonical code fields are
jointly measurable on coherent pairs: both carriers, both total endpoint
readers, the root, and every exterior boundary dart. -/
theorem measurable_lMinusCanonicalSideOnCoherent_basicCode (x : XDP) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      let M := lMinusCanonicalSideOnCoherent x z
      ((fun n => decide (n ∈ M.vertices)), (fun n => decide (n ∈ M.edges)),
        M.west, M.east, M.root, M.boundary)) := by
  have hv (n : ℕ) : Measurable (fun z : LMinusCanonicalCodingDomain x =>
      decide (n ∈ (lMinusCanonicalSideOnCoherent x z).vertices)) := by
    apply measurable_to_bool
    change MeasurableSet {z : LMinusCanonicalCodingDomain x |
      decide (n ∈ (lMinusCanonicalSideOnCoherent x z).vertices) = true}
    simpa only [Set.preimage_ofPred_eq, Set.mem_singleton_iff, decide_eq_true_eq] using
      measurableSet_lMinusCanonicalSideOnCoherent_vertices x n
  have he (n : ℕ) : Measurable (fun z : LMinusCanonicalCodingDomain x =>
      decide (n ∈ (lMinusCanonicalSideOnCoherent x z).edges)) := by
    apply measurable_to_bool
    change MeasurableSet {z : LMinusCanonicalCodingDomain x |
      decide (n ∈ (lMinusCanonicalSideOnCoherent x z).edges) = true}
    simpa only [Set.preimage_ofPred_eq, Set.mem_singleton_iff, decide_eq_true_eq] using
      measurableSet_lMinusCanonicalSideOnCoherent_edges x n
  exact (measurable_pi_iff.mpr hv).prodMk
    ((measurable_pi_iff.mpr he).prodMk
      ((measurable_pi_iff.mpr (measurable_lMinusCanonicalSideOnCoherent_endpoint x false)).prodMk
        ((measurable_pi_iff.mpr (measurable_lMinusCanonicalSideOnCoherent_endpoint x true)).prodMk
          ((measurable_lMinusCanonicalSideOnCoherent_root x).prodMk
            (measurable_pi_iff.mpr (measurable_lMinusCanonicalSideOnCoherent_boundary x))))))

/-- Helper toward Lemma 5.5. The raw finite-chain edge closure indicator
is a.e.-measurable under the original iid source law. -/
theorem aemeasurable_lMinusRawEdgeEqvGen_source (x : XDP) (k : ℤ)
    (a b : Sum ℕ ℕ) :
    AEMeasurable (fun W : ℤ → Fin 3 => decide
      (Relation.EqvGen (lMinusRawEdgeGenerator
        (decodeLMinus x k (leftSideObsNonpos x k W),
          boundaryFutureHattedPath k W)) a b)) wholePlaneIIDCodeMeasure := by
  have hm : Measurable (fun z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) =>
      decide (Relation.EqvGen (lMinusRawEdgeGenerator z) a b)) := by
    apply measurable_to_bool
    change MeasurableSet {z : LMinusSidePresentation x × (ℕ → ℤ × ℤ) |
      decide (Relation.EqvGen (lMinusRawEdgeGenerator z) a b) = true}
    simpa only [Set.preimage_ofPred_eq, Set.mem_singleton_iff, decide_eq_true_eq] using
      measurableSet_lMinusRawEdgeEqvGen x a b
  exact hm.comp_aemeasurable
    ((aemeasurable_decodeLMinus_leftSideObsNonpos x k).prodMk
      (aemeasurable_boundaryFutureHattedPath k))

/-- Helper toward Lemma 5.5. Least raw closure IDs are also
a.e.-measurable under the source law, without any descent assertion. -/
theorem aemeasurable_lMinusRawEdgeClosureId_source (x : XDP) (k : ℤ)
    (a : Sum ℕ ℕ) :
    AEMeasurable (fun W : ℤ → Fin 3 => lMinusRawEdgeClosureId
      (decodeLMinus x k (leftSideObsNonpos x k W), boundaryFutureHattedPath k W) a)
      wholePlaneIIDCodeMeasure :=
  (measurable_lMinusRawEdgeClosureId x a).comp_aemeasurable
    ((aemeasurable_decodeLMinus_leftSideObsNonpos x k).prodMk
      (aemeasurable_boundaryFutureHattedPath k))

/-- Helper toward Lemma 5.5. Directed presence in the canonical side is
inherited from the two unchanged raw directed carriers. Missing geometric -/
theorem lMinusCanonicalSide_mem_present_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (n : ℕ) :
    n ∈ (lMinusCanonicalSide x r q hf).present ↔
      (∃ a : ℕ, (∃ m, a < (kmswMissingRootStage r.code.1 m).nextEdge ∧
        (kmswMissingRootStage r.code.1 m).present a = true) ∧
          lMinusCoherentEdgeId (r, q) (.inl a) = n) ∨
      ∃ b : ℕ, b ∈ (lMinusCoherentLeftSide x q).edges ∧
        b ∈ (lMinusCoherentLeftSide x q).present ∧
          lMinusCoherentEdgeId (r, q) (.inr b) = n := by
  constructor
  · rintro ⟨e, he, hp⟩
    rcases hp with ⟨a, ha, haeq⟩ | ⟨b, hb, hbeq⟩
    · subst e
      exact Or.inl ⟨a, ha, (lMinusCoherentEdgeId_eq r q (.inl a)).trans he⟩
    · subst e
      exact Or.inr ⟨b.val, b.property, hb,
        (lMinusCoherentEdgeId_eq r q (.inr b)).trans he⟩
  · rintro (⟨a, ha, hn⟩ | ⟨b, hb, hp, hn⟩)
    · exact ⟨⟦Sum.inl a⟧, (lMinusCoherentEdgeId_eq r q (.inl a)).symm.trans hn,
        Or.inl ⟨a, ha, rfl⟩⟩
    · exact ⟨⟦Sum.inr ⟨b, hb⟩⟧,
        (lMinusCoherentEdgeId_eq r q (.inr ⟨b, hb⟩)).symm.trans hn,
        Or.inr ⟨⟨b, hb⟩, hp, rfl⟩⟩

/-- Helper toward Lemma 5.5. Every directed-presence coordinate is
measurable on certified coherent pairs. -/
theorem measurableSet_lMinusCanonicalSideOnCoherent_present (x : XDP) (n : ℕ) :
    MeasurableSet {z : LMinusCanonicalCodingDomain x |
      n ∈ (lMinusCanonicalSideOnCoherent x z).present} := by
  have hhat (b : ℕ) : MeasurableSet {q : Coherent x |
      b ∈ (lMinusCoherentLeftSide x q).present} := by
    exact measurableSet_geometricRightSide_present x b
  simp only [lMinusCanonicalSideOnCoherent, lMinusCanonicalSide_mem_present_iff,
    Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro a
    simpa only [Set.preimage_ofPred_eq, Function.comp_def, Set.ofPred_exists,
      Set.ofPred_and, Set.preimage_iUnion, Set.preimage_inter] using
      ((measurableSet_lMinusPrimedPresent x a).preimage
      (measurable_fst.comp measurable_subtype_coe)).inter
      (((measurable_lMinusCoherentEdgeId x (.inl a)).comp
        measurable_subtype_coe).eq_const n).setOf
  · exact MeasurableSet.iUnion (fun b =>
      ((measurableSet_lMinusCoherentLeftSide_edges x b).preimage
        (measurable_snd.comp measurable_subtype_coe)).inter
      (((hhat b).preimage (measurable_snd.comp measurable_subtype_coe)).inter
        (((measurable_lMinusCoherentEdgeId x (.inr b)).comp
          measurable_subtype_coe).eq_const n).setOf))

/-- Helper toward Lemma 5.5. The entire canonical geodesic-seam dart
coordinate is measurable on the certified coherent-pair domain. -/
theorem measurable_lMinusCanonicalSideOnCoherent_seam (x : XDP) (i : ℕ) :
    Measurable (fun z : LMinusCanonicalCodingDomain x =>
      (lMinusCanonicalSideOnCoherent x z).seam i) := by
  have hs : Measurable (fun q : Coherent x =>
      (lMinusCoherentLeftSide x q).seam i) :=
    measurable_geometricRightSide_seam x i
  have hraw : Measurable (fun z : LMinusCanonicalCodingDomain x =>
      (Sum.inr ((lMinusCoherentLeftSide x z.val.2).seam i).1 : Sum ℕ ℕ)) :=
    measurable_inr.comp ((hs.comp (measurable_snd.comp measurable_subtype_coe)).fst)
  have hid := (measurable_lMinusCoherentEdgeId_uncurry x).comp
    (hraw.prodMk measurable_subtype_coe)
  convert hid.prodMk (measurable_const (a := false)) using 1
  funext z
  apply Prod.ext
  · exact (lMinusCoherentEdgeId_eq z.val.1 z.val.2
      (.inr ⟨((lMinusCoherentLeftSide x z.val.2).seam i).1,
        lMinus_hatted_seam_mem x z.val.2 i⟩)).symm
  · rfl































































































end DirectedDistances.PaperProofs.Section5
