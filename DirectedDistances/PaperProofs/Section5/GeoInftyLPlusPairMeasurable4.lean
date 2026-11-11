/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusPairMeasurable3
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSide4CrossWitness5

/-! integration remain with the sole coordinator. No numbered result is closed.
The vertex generators below record shared-edge endpoint gluing. Identification
with the full geometric vertex kernel, and assembly of a complete marked side,
remain separate obligations; neither is asserted by the raw vertex IDs. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local instance : MeasurableSpace (Option (ℕ × Bool)) := ⊤
local instance : MeasurableSpace (Option ℕ) := ⊤

/-- Helper toward Lemma 5.5. The raw three-block edge quotient retains
isolated labels; allocation to the geometric carrier is a separate test. -/
@[expose] def lPlusPairEdgeSetoid (x : XDP) (k : ℤ) (z : LPlusCodingPair x) :
    Setoid LPlusRawEdge := Relation.EqvGen.setoid (lPlusRawEdgeGenerator x k z)

/-- Helper toward Lemma 5.5. Least tokens give an injective numbering of
the actual raw edge quotient, rather than a choice of ambient source labels. -/
@[expose] noncomputable def lPlusPairQuotientEdgeId (x : XDP) (k : ℤ)
    (z : LPlusCodingPair x) : Quotient (lPlusPairEdgeSetoid x k z) → ℕ :=
  Quotient.lift (lPlusRawEdgeClosureId x k z)
    (fun a b hab => (lPlusRawEdgeClosureId_eq_iff x k z a b).mpr hab)

/-- Helper toward Lemma 5.5. Evaluation at a raw representative is the
previously proved measurable least-token ID. -/
theorem lPlusPairQuotientEdgeId_mk (x : XDP) (k : ℤ) (z : LPlusCodingPair x)
    (a : LPlusRawEdge) :
    lPlusPairQuotientEdgeId x k z ⟦a⟧ = lPlusRawEdgeClosureId x k z a := rfl

/-- Helper toward Lemma 5.5. Equality of quotient edge IDs preserves
edge identity, including distinct parallel edges. -/
theorem lPlusPairQuotientEdgeId_injective (x : XDP) (k : ℤ)
    (z : LPlusCodingPair x) : Function.Injective (lPlusPairQuotientEdgeId x k z) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro a b hab
  exact Quotient.sound ((lPlusRawEdgeClosureId_eq_iff x k z a b).mp hab)

/-- Helper toward Lemma 5.5. The complete range of the quotient
numbering is exactly the range of the measurable raw numbering. -/
theorem lPlusPairQuotientEdgeId_range (x : XDP) (k : ℤ)
    (z : LPlusCodingPair x) :
    Set.range (lPlusPairQuotientEdgeId x k z) =
      Set.range (lPlusRawEdgeClosureId x k z) := by
  ext n
  constructor
  · rintro ⟨a, ha⟩
    revert ha
    refine Quotient.inductionOn a ?_
    intro b hb
    exact ⟨b, hb⟩
  · rintro ⟨a, ha⟩
    exact ⟨⟦a⟧, ha⟩

/-- Helper toward Lemma 5.5. The primed orientation is corrected before
recording the endpoint bit of a raw dart. Prefix and hatted bits are unchanged. -/
@[expose] noncomputable def lPlusPairRawDartBit (x : XDP)
    (z : LPlusCodingPair x) (a : LPlusRawEdge × Bool) : Bool :=
  match a.1 with
  | .inl _ => a.2
  | .inr (.inl e) => a.2 ^^ lMinusCodePrimedSideFlip
      (decodeLMinus x 0 (z.1.code.2.2, z.1.code.2.1)) e
  | .inr (.inr _) => a.2

/-- Helper toward Lemma 5.5. Each corrected raw dart bit is measurable
on the raw pair space, with the missing primed root still included. -/
theorem measurable_lPlusPairRawDartBit (x : XDP) (a : LPlusRawEdge × Bool) :
    Measurable (fun z : LPlusCodingPair x => lPlusPairRawDartBit x z a) := by
  rcases a with ⟨a, b⟩
  rcases a with a | a
  · exact measurable_const
  · cases a with
    | inl e =>
      have hc : Measurable (fun z : LPlusCodingPair x => z.1.code) :=
        (measurable_lPlusSidePresentation_code x).comp measurable_fst
      exact (measurable_of_finite (fun c : Bool => b ^^ c)).comp
        ((measurable_lMinusCodePrimedSideFlip x e).comp
          ((measurable_decodeLMinus x 0).comp (hc.snd.snd.prodMk hc.snd.fst)))
    | inr e => exact measurable_const

/-- Helper toward Lemma 5.5. Canonical raw darts use the least-token
edge ID together with the corrected endpoint bit. -/
@[expose] noncomputable def lPlusPairRawDartId (x : XDP) (k : ℤ)
    (z : LPlusCodingPair x) (a : LPlusRawEdge × Bool) : ℕ × Bool :=
  (lPlusRawEdgeClosureId x k z a.1, lPlusPairRawDartBit x z a)

/-- Helper toward Lemma 5.5. Every fixed canonical raw dart coordinate
is measurable before any geometric realization is chosen. -/
theorem measurable_lPlusPairRawDartId (x : XDP) (k : ℤ)
    (a : LPlusRawEdge × Bool) :
    Measurable (fun z : LPlusCodingPair x => lPlusPairRawDartId x k z a) :=
  (measurable_lPlusRawEdgeClosureId x k a.1).prodMk
    (measurable_lPlusPairRawDartBit x a)

/-- Helper toward Lemma 5.5. The exact kernel of canonical raw dart
numbering is edge gluing together with equality of corrected endpoint bits. -/
theorem lPlusPairRawDartId_eq_iff (x : XDP) (k : ℤ) (z : LPlusCodingPair x)
    (a b : LPlusRawEdge × Bool) :
    lPlusPairRawDartId x k z a = lPlusPairRawDartId x k z b ↔
      Relation.EqvGen (lPlusRawEdgeGenerator x k z) a.1 b.1 ∧
      lPlusPairRawDartBit x z a = lPlusPairRawDartBit x z b := by
  exact Prod.ext_iff.trans
    (and_congr (lPlusRawEdgeClosureId_eq_iff x k z a.1 b.1) Iff.rfl)

/-- Helper toward Lemma 5.5. The intrinsic prefix/primed dart attachment
has equal canonical IDs, with its local orientation correction preserved. -/
theorem lPlusPairRawDartId_eq_of_prefixPrimedAttachment
    (x : XDP) (k : ℤ) (z : LPlusCodingPair x) (a b : ℕ × Bool)
    (hab : lPlusPrefixPrimedDartAttachment x k z.1 a b) :
    lPlusPairRawDartId x k z (.inl a.1, a.2) =
      lPlusPairRawDartId x k z (.inr (.inl b.1), b.2) := by
  apply (lPlusPairRawDartId_eq_iff x k z _ _).mpr
  exact ⟨Relation.EqvGen.rel _ _ hab.1, hab.2⟩

/-- Helper toward Lemma 5.5. Allocation of raw block edges is separate
from directed presence. At zero the prefix block is empty. -/
@[expose] noncomputable def lPlusPairRawEdgeAllocated (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) : LPlusRawEdge → Prop
  | .inl e => 0 < k ∧ (lPlusStoppedPrefixRotationOption k z.val.1.code.1
      (e, false)).isSome
  | .inr (.inl _) => True
  | .inr (.inr e) => e ∈ (lMinusCoherentLeftSide x
      (lPlusCertifiedCodingPairPath x z)).edges

/-- Helper toward Lemma 5.5. Fixed allocation events are measurable,
including missing geometric edges and the empty prefix at zero. -/
theorem measurableSet_lPlusPairRawEdgeAllocated (x : XDP) (k : ℤ)
    (a : LPlusRawEdge) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairRawEdgeAllocated x k z a} := by
  rcases a with a | a
  · exact (MeasurableSet.const (0 < k)).inter
      (((measurable_of_countable (fun v : Option (ℕ × Bool) => v.isSome)).comp
        (measurable_lPlusCertifiedCodingPair_prefixRotationOption x k (a, false))).eq_const
          true).setOf
  · cases a with
    | inl a => exact MeasurableSet.univ
    | inr a =>
      exact (measurableSet_lMinusCoherentLeftSide_edges x a).preimage
        (measurable_lPlusCertifiedCodingPairPath x)

/-- Helper toward Lemma 5.5. The allocated canonical edge carrier is
the image of allocated raw edges under the least-token numbering. -/
@[expose] noncomputable def lPlusPairCanonicalEdges (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) : Set ℕ :=
  {n | ∃ a : LPlusRawEdge, lPlusPairRawEdgeAllocated x k z a ∧
    lPlusRawEdgeClosureId x k z.val a = n}

/-- Helper toward Lemma 5.5. Every allocated canonical edge coordinate
is measurable by a countable union over tagged representatives. -/
theorem measurableSet_lPlusPairCanonicalEdges (x : XDP) (k : ℤ) (n : ℕ) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      n ∈ lPlusPairCanonicalEdges x k z} := by
  change MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
    ∃ a : LPlusRawEdge, lPlusPairRawEdgeAllocated x k z a ∧
      lPlusRawEdgeClosureId x k z.val a = n}
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a =>
    (measurableSet_lPlusPairRawEdgeAllocated x k a).inter
      ((measurable_lPlusCertifiedCodingPair_rawEdgeClosureId x k a).eq_const n).setOf)

/-- Helper toward Lemma 5.5. The raw prefix allocation test recovers
the source geometric edge carrier, including its empty zero endpoint. -/
theorem lPlusPairRawEdgeAllocated_prefix_iff_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k) (e : ℕ) :
    lPlusPairRawEdgeAllocated x k
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩ (.inl e) ↔
      e ∈ boundaryGluingPrefixMinusEdges s.W s.h k := by
  change (0 < k ∧ (lPlusStoppedPrefixRotationOption k r.code.1
    (e, false)).isSome = true) ↔ _
  by_cases hpos : 0 < k
  · rw [← s.prefixCode_eq, lPlusStoppedPrefixRotationOption,
      dite_eq_left (boundaryPrefixCode_mem_lPlusPrefixHitDomain s.W s.h k hk),
      lPlusPrefixHitIndex_boundaryPrefixCode s.W s.h k hk,
      lPlusFiniteRotationOption_of_prefix (boundaryPrefixCode k s.W)
        (shiftedStream s.W 0) (boundaryHitTime (shiftedStream s.W 0) s.h k - 1)
        (fun i hi => lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt s.W s.h k
          (by omega)) (e, false)]
    rw [lPlusPrefixMinusEdges_eq_previousStage hpos]
    simp only [hpos, true_and, lPlusFiniteRotationOption]
    split <;> simp_all only [Option.isSome_some, Option.isSome_none,
      Bool.false_eq_true, Set.mem_ofPred_eq, iff_self]
  · have hk0 : k = 0 := by omega
    subst k
    rw [boundaryGluingPrefixMinusEdges_zero]
    simp only [lt_irrefl, false_and, Set.mem_empty_iff_false]

/-- Helper toward Lemma 5.5. The finite prefix rotation graph in
canonical raw dart coordinates; no ambient vertex or edge labels are used. -/
@[expose] noncomputable def lPlusPairPrefixRotationGraph (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d e : ℕ × Bool) : Prop :=
  0 < k ∧ ∃ a b : ℕ × Bool,
    lPlusStoppedPrefixRotationOption k z.val.1.code.1 a = some b ∧
    lPlusPairRawDartId x k z.val (.inl a.1, a.2) = d ∧
    lPlusPairRawDartId x k z.val (.inl b.1, b.2) = e

/-- Helper toward Lemma 5.5. The prefix block graph is measurable
by countable input/output tests of the stopped finite permutation. -/
theorem measurableSet_lPlusPairPrefixRotationGraph (x : XDP) (k : ℤ)
    (d e : ℕ × Bool) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairPrefixRotationGraph x k z d e} := by
  unfold lPlusPairPrefixRotationGraph
  simp only [Set.ofPred_and, Set.ofPred_exists]
  exact (MeasurableSet.const (0 < k)).inter
    (MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
      ((measurable_lPlusCertifiedCodingPair_prefixRotationOption x k a).eq_const
        (some b)).setOf.inter
      ((((measurable_lPlusPairRawDartId x k (.inl a.1, a.2)).comp
        measurable_subtype_coe).eq_const d).setOf.inter
      (((measurable_lPlusPairRawDartId x k (.inl b.1, b.2)).comp
        measurable_subtype_coe).eq_const e).setOf))))

/-- Helper toward Lemma 5.5. The primed permutation graph retains
the complete local finite-incidence code and its corrected endpoint bits. -/
@[expose] noncomputable def lPlusPairPrimedRotationGraph (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d e : ℕ × Bool) : Prop :=
  ∃ a b : ℕ × Bool,
    kmswInfRot z.val.1.code.2.2 z.property.2.1 a = b ∧
    lPlusPairRawDartId x k z.val (.inr (.inl a.1), a.2) = d ∧
    lPlusPairRawDartId x k z.val (.inr (.inl b.1), b.2) = e

/-- Helper toward Lemma 5.5. Every fixed primed rotation graph event
is measurable through the certified future projection. -/
theorem measurableSet_lPlusPairPrimedRotationGraph (x : XDP) (k : ℤ)
    (d e : ℕ × Bool) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairPrimedRotationGraph x k z d e} := by
  have hm (a : ℕ × Bool) : Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      kmswInfRot z.val.1.code.2.2 z.property.2.1 a) :=
    (measurable_lMinusCanonicalCodingDomain_primedRotation x a).comp
      (measurable_lPlusCertifiedCodingPairFuture x)
  unfold lPlusPairPrimedRotationGraph
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
    ((hm a).eq_const b).setOf.inter
    ((((measurable_lPlusPairRawDartId x k (.inr (.inl a.1), a.2)).comp
      measurable_subtype_coe).eq_const d).setOf.inter
    (((measurable_lPlusPairRawDartId x k (.inr (.inl b.1), b.2)).comp
      measurable_subtype_coe).eq_const e).setOf)))

/-- Helper toward Lemma 5.5. The preceding primed graph is literally
an encoded permutation graph on the complete primed dart carrier. -/
theorem lPlusPairPrimedRotationGraph_iff_encoded (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d e : ℕ × Bool) :
    lPlusPairPrimedRotationGraph x k z d e ↔
      lMinusEncodedPermGraph
        (fun a : ℕ × Bool => lPlusPairRawDartId x k z.val (.inr (.inl a.1), a.2))
        (kmswInfRot z.val.1.code.2.2 z.property.2.1) d e := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    exact ⟨a, ha, hab ▸ hb⟩
  · rintro ⟨a, ha, hb⟩
    exact ⟨a, _, rfl, ha, hb⟩

/-- Helper toward Lemma 5.5. The hatted block graph restricts both
darts to their actual geometric edge carrier before canonical numbering. -/
@[expose] noncomputable def lPlusPairHattedRotationGraph (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d e : ℕ × Bool) : Prop :=
  let M := lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)
  ∃ a b : ℕ × Bool, a.1 ∈ M.edges ∧ b.1 ∈ M.edges ∧ M.rotation a b ∧
    lPlusPairRawDartId x k z.val (.inr (.inr a.1), a.2) = d ∧
    lPlusPairRawDartId x k z.val (.inr (.inr b.1), b.2) = e

/-- Helper toward Lemma 5.5. Every hatted rotation graph event is
measurable on certified pairs with the original hatted labels retained. -/
theorem measurableSet_lPlusPairHattedRotationGraph (x : XDP) (k : ℤ)
    (d e : ℕ × Bool) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairHattedRotationGraph x k z d e} := by
  unfold lPlusPairHattedRotationGraph
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
    ((measurableSet_lMinusCoherentLeftSide_edges x a.1).preimage
      (measurable_lPlusCertifiedCodingPairPath x)).inter
    (((measurableSet_lMinusCoherentLeftSide_edges x b.1).preimage
      (measurable_lPlusCertifiedCodingPairPath x)).inter
    (((measurableSet_lMinusCoherentLeftSide_rotation x a b).preimage
      (measurable_lPlusCertifiedCodingPairPath x)).inter
    ((((measurable_lPlusPairRawDartId x k (.inr (.inr a.1), a.2)).comp
      measurable_subtype_coe).eq_const d).setOf.inter
    (((measurable_lPlusPairRawDartId x k (.inr (.inr b.1), b.2)).comp
      measurable_subtype_coe).eq_const e).setOf)))))

/-- Helper toward Lemma 5.5. The hatted graph is the encoded graph
of the existing coherent hatted permutation on its geometric dart subtype. -/
theorem lPlusPairHattedRotationGraph_iff_encoded (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d e : ℕ × Bool) :
    lPlusPairHattedRotationGraph x k z d e ↔
      lMinusEncodedPermGraph
        (fun a : {a : ℕ × Bool // a.1 ∈ (lMinusCoherentLeftSide x
            (lPlusCertifiedCodingPairPath x z)).edges} =>
          lPlusPairRawDartId x k z.val (.inr (.inr a.val.1), a.val.2))
        (lMinusHattedRotation x (lPlusCertifiedCodingPairPath x z)) d e := by
  constructor
  · rintro ⟨a, b, ham, hbm, hab, ha, hb⟩
    have h := (lMinusHattedRotation_iff x (lPlusCertifiedCodingPairPath x z)
      ⟨a, ham⟩ ⟨b, hbm⟩).mp hab
    refine ⟨⟨a, ham⟩, ha, ?_⟩
    rw [h]
    exact hb
  · rintro ⟨a, ha, hb⟩
    let b := lMinusHattedRotation x (lPlusCertifiedCodingPairPath x z) a
    exact ⟨a.val, b.val, a.property, b.property,
      (lMinusHattedRotation_iff x (lPlusCertifiedCodingPairPath x z) a b).mpr rfl,
      ha, hb⟩

/-- Helper toward Lemma 5.5. A prefix dart endpoint is read at the
preceding finite stage, and is absent when the prefix never hits its level.
Allocation is checked separately by `lPlusPairRawEdgeAllocated`. -/
@[expose] noncomputable def lPlusStoppedPrefixEndpointOption (k : ℤ)
    (p : ℕ → Fin 3) (d : ℕ × Bool) : Option ℕ :=
  if hp : p ∈ lPlusPrefixHitDomain k then
    let S := kmswStage p (lPlusPrefixHitIndex k ⟨p, hp⟩ - 1)
    some (if d.2 then S.east d.1 else S.west d.1)
  else none

/-- Helper toward Lemma 5.5. Every optional prefix endpoint coordinate
is measurable by the already established stopped-stage reconstruction. -/
theorem measurable_lPlusStoppedPrefixEndpointOption (k : ℤ) (d : ℕ × Bool) :
    Measurable (fun p => lPlusStoppedPrefixEndpointOption k p d) := by
  exact ((measurable_of_countable (fun n : ℕ => some n)).comp
    (measurable_lPlusPrefixPreviousStage k
      (fun S => if d.2 then S.east d.1 else S.west d.1))).dite
        measurable_const (measurableSet_lPlusPrefixHitDomain k)

/-- Helper toward Lemma 5.5. On an aligned source, the optional endpoint
decoder reads the exact preceding stage, without choosing another source. -/
theorem lPlusStoppedPrefixEndpointOption_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k) (d : ℕ × Bool) :
    lPlusStoppedPrefixEndpointOption k r.code.1 d =
      some (if d.2 then (kmswStage (shiftedStream s.W 0)
        (boundaryHitTime (shiftedStream s.W 0) s.h k - 1)).east d.1
      else (kmswStage (shiftedStream s.W 0)
        (boundaryHitTime (shiftedStream s.W 0) s.h k - 1)).west d.1) := by
  rw [← s.prefixCode_eq, lPlusStoppedPrefixEndpointOption,
    dite_eq_left (boundaryPrefixCode_mem_lPlusPrefixHitDomain s.W s.h k hk),
    lPlusPrefixHitIndex_boundaryPrefixCode s.W s.h k hk]
  rw [kmswStage_congr (fun i hi =>
    lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt s.W s.h k (by omega))]

/-- Helper toward Lemma 5.5. Tagged raw vertex labels for all three
blocks. These are vertex labels, rather than edge-incidence encodings. -/
abbrev LPlusPairRawVertex := Sum ℕ (Sum ℕ ℕ)

/-- Helper toward Lemma 5.5. Vertex generators identify the endpoints
of shared edges, with the primed orientation correction included. -/
@[expose] noncomputable def lPlusPairRawVertexGenerator (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) :
    LPlusPairRawVertex → LPlusPairRawVertex → Prop
  | .inl u, .inr (.inl v) => ∃ a b : ℕ, ∃ t : Bool,
      lPlusPrefixPrimedEdgeAttachment x k z.val.1 a b ∧
      lPlusStoppedPrefixEndpointOption k z.val.1.code.1 (a, t) = some u ∧
      kmswLimitDartVertex z.val.1.code.2.2
        (b, t ^^ lMinusCodePrimedSideFlip
          (decodeLMinus x 0 (z.val.1.code.2.2, z.val.1.code.2.1)) b) = v
  | .inr (.inl u), .inr (.inr v) =>
      lMinusCodeVertexGluing (lPlusCertifiedCodingPairFuture x z).val.1
        (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)) (.inl u) (.inr v)
  | _, _ => False

/-- Helper toward Lemma 5.5. All raw vertex gluing events are
measurable on certified pairs by countable shared-edge endpoint tests. -/
theorem measurableSet_lPlusPairRawVertexGenerator (x : XDP) (k : ℤ)
    (u v : LPlusPairRawVertex) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairRawVertexGenerator x k z u v} := by
  rcases u with u | u <;> rcases v with v | v
  · exact MeasurableSet.empty
  · cases v with
    | inl v =>
      change MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
        ∃ a b : ℕ, ∃ t : Bool,
          lPlusPrefixPrimedEdgeAttachment x k z.val.1 a b ∧
          lPlusStoppedPrefixEndpointOption k z.val.1.code.1 (a, t) = some u ∧
          kmswLimitDartVertex z.val.1.code.2.2
            (b, t ^^ lMinusCodePrimedSideFlip
              (decodeLMinus x 0 (z.val.1.code.2.2, z.val.1.code.2.1)) b) = v}
      simp only [Set.ofPred_exists, Set.ofPred_and]
      refine MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
        MeasurableSet.iUnion (fun t => ?_)))
      have hp : Measurable (fun z : lPlusCertifiedCodingPairDomain x => z.val.1.code.1) :=
        (measurable_lPlusSidePresentation_code x).fst.comp
          (measurable_fst.comp measurable_subtype_coe)
      have hprimed := (measurable_lMinusPrimedDartEndpoint x b t).comp
        (measurable_fst.comp
          (measurable_subtype_coe.comp (measurable_lPlusCertifiedCodingPairFuture x)))
      exact (measurableSet_lPlusCertifiedCodingPair_prefixPrimedEdgeAttachment x k a b).inter
        (((((measurable_lPlusStoppedPrefixEndpointOption k (a, t)).comp hp).eq_const
          (some u)).setOf).inter ((hprimed.eq_const v).setOf))
    | inr v => exact MeasurableSet.empty
  · cases u <;> exact MeasurableSet.empty
  · cases u with
    | inl u =>
      cases v with
      | inl v => exact MeasurableSet.empty
      | inr v =>
        change MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
          lMinusCodeVertexGluing (lPlusCertifiedCodingPairFuture x z).val.1
            (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairFuture x z).val.2)
            (.inl u) (.inr v)}
        exact (measurableSet_lMinusCoherentVertexGluing x (.inl u) (.inr v)).preimage
          (measurable_subtype_coe.comp (measurable_lPlusCertifiedCodingPairFuture x))
    | inr u => cases v <;> exact MeasurableSet.empty

/-- Helper toward Lemma 5.5. Vertex equivalence has measurable
finite-chain certificates; no finite bound on chain length is assumed. -/
theorem measurableSet_lPlusPairRawVertexEqvGen (x : XDP) (k : ℤ)
    (u v : LPlusPairRawVertex) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      Relation.EqvGen (lPlusPairRawVertexGenerator x k z) u v} := by
  have hc (l : List LPlusPairRawVertex) (u v : LPlusPairRawVertex) :
      MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
        lMinusFiniteGluingChain (lPlusPairRawVertexGenerator x k z) u l v} := by
    induction l generalizing u with
    | nil => exact MeasurableSet.const (u = v)
    | cons a l ih =>
      exact ((measurableSet_lPlusPairRawVertexGenerator x k u a).union
        (measurableSet_lPlusPairRawVertexGenerator x k a u)).inter (ih a)
  have he : {z : lPlusCertifiedCodingPairDomain x |
      Relation.EqvGen (lPlusPairRawVertexGenerator x k z) u v} =
      ⋃ l : List LPlusPairRawVertex, {z |
        lMinusFiniteGluingChain (lPlusPairRawVertexGenerator x k z) u l v} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion,
      lMinusEqvGen_iff_exists_finiteGluingChain]
  rw [he]
  exact MeasurableSet.iUnion (fun l => hc l u v)

/-- Helper toward Lemma 5.5. A vertex candidate is an actual tagged
vertex representative in the generated endpoint-gluing class. -/
@[expose] noncomputable def lPlusPairRawVertexCandidate (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (u : LPlusPairRawVertex) (n : ℕ) : Prop :=
  ∃ v : LPlusPairRawVertex, lPlusRawEdgeToken v = n ∧
    Relation.EqvGen (lPlusPairRawVertexGenerator x k z) v u

/-- Helper toward Lemma 5.5. Every vertex has its own candidate,
including an isolated vertex with no incident shared edge. -/
theorem lPlusPairRawVertexCandidate_exists (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (u : LPlusPairRawVertex) :
    ∃ n, lPlusPairRawVertexCandidate x k z u n :=
  ⟨lPlusRawEdgeToken u, u, rfl, Relation.EqvGen.refl u⟩

/-- Helper toward Lemma 5.5. The least tagged vertex token of its
endpoint-gluing class is selected from a proved nonempty candidate set. -/
@[expose] noncomputable def lPlusPairRawVertexId (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (u : LPlusPairRawVertex) : ℕ :=
  Nat.find (lPlusPairRawVertexCandidate_exists x k z u)

/-- Helper toward Lemma 5.5. Every canonical raw vertex ID is
measurable through its countable finite-chain candidate predicates. -/
theorem measurable_lPlusPairRawVertexId (x : XDP) (k : ℤ) (u : LPlusPairRawVertex) :
    Measurable (fun z : lPlusCertifiedCodingPairDomain x => lPlusPairRawVertexId x k z u) := by
  apply measurable_find (fun z => lPlusPairRawVertexCandidate_exists x k z u)
  intro n
  unfold lPlusPairRawVertexCandidate
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun v => (MeasurableSet.const (lPlusRawEdgeToken v = n)).inter
    (measurableSet_lPlusPairRawVertexEqvGen x k v u))

/-- Helper toward Lemma 5.5. Equal least vertex tokens characterize
precisely the generated endpoint-gluing equivalence. -/
theorem lPlusPairRawVertexId_eq_iff (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (u v : LPlusPairRawVertex) :
    lPlusPairRawVertexId x k z u = lPlusPairRawVertexId x k z v ↔
      Relation.EqvGen (lPlusPairRawVertexGenerator x k z) u v := by
  constructor
  · intro huv
    obtain ⟨a, ha, hau⟩ := Nat.find_spec (lPlusPairRawVertexCandidate_exists x k z u)
    obtain ⟨b, hb, hbv⟩ := Nat.find_spec (lPlusPairRawVertexCandidate_exists x k z v)
    have hab := lPlusRawEdgeToken_injective (ha.trans (huv.trans hb.symm))
    subst b
    exact Relation.EqvGen.trans u a v hau.symm hbv
  · intro huv
    apply Nat.find_congr'
    intro n
    constructor
    · rintro ⟨a, ha, hau⟩
      exact ⟨a, ha, Relation.EqvGen.trans a u v hau huv⟩
    · rintro ⟨a, ha, hav⟩
      exact ⟨a, ha, Relation.EqvGen.trans a v u hav huv.symm⟩

/-- Helper toward Lemma 5.5. Prefix rotation allocation depends on the
edge label, and treats its two endpoint bits symmetrically. -/
theorem lPlusStoppedPrefixRotationOption_isSome_bit (k : ℤ) (p : ℕ → Fin 3)
    (a : ℕ × Bool) :
    (lPlusStoppedPrefixRotationOption k p a).isSome =
      (lPlusStoppedPrefixRotationOption k p (a.1, false)).isSome := by
  unfold lPlusStoppedPrefixRotationOption
  split
  · unfold lPlusFiniteRotationOption
    split <;> rfl
  · rfl

/-- Helper toward Lemma 5.5. On every positive aligned source pair,
the measurable prefix graph is exactly the encoded source prefix permutation
graph in the new least-token dart coordinates. -/
theorem lPlusPairPrefixRotationGraph_iff_encoded_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 < k) (d e : ℕ × Bool) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairPrefixRotationGraph x k z d e ↔
      lMinusEncodedPermGraph
        (fun a : LPlusPrefixDart s.W s.h k =>
          lPlusPairRawDartId x k z.val (.inl a.val.1, a.val.2))
        (lPlusPrefixRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft
          (le_of_lt hk)) d e := by
  dsimp only
  let z : lPlusCertifiedCodingPairDomain x :=
    ⟨(r, boundaryFutureHattedPath k s.W),
      LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
  constructor
  · rintro ⟨_, a, b, hab, hd, he⟩
    have halloc : lPlusPairRawEdgeAllocated x k z (.inl a.1) := by
      refine ⟨hk, ?_⟩
      change (lPlusStoppedPrefixRotationOption k r.code.1 (a.1, false)).isSome = true
      rw [← lPlusStoppedPrefixRotationOption_isSome_bit k r.code.1 a, hab]
      rfl
    have ha := (lPlusPairRawEdgeAllocated_prefix_iff_of_aligned
      x k r s (le_of_lt hk) a.1).mp halloc
    let A : LPlusPrefixDart s.W s.h k := ⟨a, ha⟩
    have hr := lPlusStoppedPrefixRotationOption_eq_prefixRotation_of_aligned x k r s hk A
    have hb := Option.some.inj (hr.symm.trans hab)
    refine ⟨A, hd, ?_⟩
    change lPlusPairRawDartId x k z.val
      (.inl (lPlusPrefixRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft
        (le_of_lt hk) A).val.1,
        (lPlusPrefixRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft
          (le_of_lt hk) A).val.2) = e
    rw [hb]
    exact he
  · rintro ⟨a, ha, hb⟩
    exact ⟨hk, a.val, _,
      lPlusStoppedPrefixRotationOption_eq_prefixRotation_of_aligned x k r s hk a,
      ha, hb⟩

/-- Helper toward Lemma 5.5. The now-proved aligned cross-witness
comparison removes the sole open premise from set-theoretic raw-pair
factorization. This does not assert measurability of the factor. -/
theorem exists_lPlusRawPairClassOption (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∃ f : LPlusCodingPair x → Option GeometricSideClass,
      (∀ z, (f z).isSome ↔ z ∈ lPlusCertifiedCodingPairDomain x) ∧
      (∀ (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r),
        f (r, boundaryFutureHattedPath k s.W) =
          some (geometricSideClass
            (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk))) ∧
      lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        f ∘ lPlusCodingPairObservation x k :=
  exists_lPlusRawPairClassOption_of_crossWitness
    lPlusCodeBlockSide4_class_eq_of_presentation_codes_eq x k hk

end DirectedDistances.PaperProofs.Section5









































































































































































/- were 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0. The final item was the temporary
axiom-probe compile. All 25 new theorems depend only on
[propext, Classical.choice, Quot.sound]. No placeholder or custom axiom
occurred in those transitive lists. All temporary #print commands were
was used, with one compile at a time. No project source outside this file -/
