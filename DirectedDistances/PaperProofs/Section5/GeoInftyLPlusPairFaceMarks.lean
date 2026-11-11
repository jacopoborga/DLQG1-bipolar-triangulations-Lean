/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusPairMeasurable5

/-! Face certificates and marking readers in the measurable three-block numbering. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local instance : MeasurableSpace (Option ℕ) := ⊤
local instance : MeasurableSpace (Option LPlusPairRawVertex) := ⊤
local instance : MeasurableSpace (Option (List ℕ)) := ⊤
local instance : MeasurableSingletonClass LPlusRawEdge where
  measurableSet_singleton a := by
    rcases a with a | (a | a) <;> simp [measurableSet_sum_iff, Set.preimage]

/-- Helper toward Lemma 5.5. Equal modes and the same path determine the
same geometric side independently of the coherence proof. -/
private theorem lPlusFaceMarks_side_eq {x y : XDP} (hxy : y = x)
    (q : ℕ → ℤ × ℤ)
    (hy : q ∈ selectedCutCoherentDomain y renewalTime renewalTime_positiveSuccessTime)
    (hx : q ∈ selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime) :
    geometricSideSubmap y renewalTime renewalTime_positiveSuccessTime .left ⟨q, hy⟩ =
      geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left ⟨q, hx⟩ := by
  cases hxy
  rfl

/-- Helper toward Lemma 5.5. Countable raw vertex evaluation preserves
measurability of the full geometric-kernel numbering. -/
theorem measurable_lPlusPairFullVertexId_eval (x : XDP) (k : ℤ)
    (a : lPlusCertifiedCodingPairDomain x → LPlusPairRawVertex) (ha : Measurable a) :
    Measurable (fun z => lPlusPairFullVertexId x k z (a z)) := by
  apply measurable_to_countable'
  intro n
  have he : {z | lPlusPairFullVertexId x k z (a z) = n} =
      ⋃ b : LPlusPairRawVertex, {z | a z = b} ∩
        {z | lPlusPairFullVertexId x k z b = n} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨a z, rfl, h⟩, fun ⟨b, hb, hn⟩ => hb ▸ hn⟩
  change MeasurableSet {z | lPlusPairFullVertexId x k z (a z) = n}
  rw [he]
  exact MeasurableSet.iUnion (fun b => ((ha.eq_const b).setOf).inter
    ((measurable_lPlusPairFullVertexId x k b).eq_const n).setOf)

/-- Helper toward Lemma 5.5. Countable raw dart evaluation preserves
measurability, including the primed orientation correction. -/
theorem measurable_lPlusPairRawDartId_eval (x : XDP) (k : ℤ)
    (a : lPlusCertifiedCodingPairDomain x → LPlusRawEdge × Bool) (ha : Measurable a) :
    Measurable (fun z => lPlusPairRawDartId x k z.val (a z)) := by
  apply measurable_to_countable'
  intro n
  have he : {z | lPlusPairRawDartId x k z.val (a z) = n} =
      ⋃ b : LPlusRawEdge × Bool, {z | a z = b} ∩
        {z | lPlusPairRawDartId x k z.val b = n} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨a z, rfl, h⟩, fun ⟨b, hb, hn⟩ => hb ▸ hn⟩
  change MeasurableSet {z | lPlusPairRawDartId x k z.val (a z) = n}
  rw [he]
  exact MeasurableSet.iUnion (fun b => ((ha.eq_const b).setOf).inter
    (((measurable_lPlusPairRawDartId x k b).comp measurable_subtype_coe).eq_const n).setOf)

/-- Helper toward Lemma 5.5. The root is the full vertex ID of the
primed root vertex, including the isolated prefix contact at index zero. -/
@[expose] noncomputable def lPlusPairRoot (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) : ℕ :=
  lPlusPairFullVertexId x k z (.inr (.inl 1))

/-- Helper toward Lemma 5.5. The exact root coordinate is measurable. -/
theorem measurable_lPlusPairRoot (x : XDP) (k : ℤ) :
    Measurable (lPlusPairRoot x k) := measurable_lPlusPairFullVertexId x k _

/-- Helper toward Lemma 5.5. The root reader has the prescribed geometric
quotient representative on every aligned witness. -/
theorem lPlusPairRoot_eq_of_aligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k) :
    lPlusPairRoot x k
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩ =
      lPlusPairGluedVertexId x k r s hk ⟦Sum.inr (Sum.inl 1)⟧ := rfl

/-- Helper toward Lemma 5.5. Indexed seams use the actual coherent hatted
path, with both the edge and its endpoint bit retained. -/
@[expose] noncomputable def lPlusPairSeam (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (i : ℕ) : ℕ × Bool :=
  let a := (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)).seam i
  lPlusPairRawDartId x k z.val (.inr (.inr a.1), a.2)

/-- Helper toward Lemma 5.5. Every indexed seam coordinate is measurable. -/
theorem measurable_lPlusPairSeam (x : XDP) (k : ℤ) (i : ℕ) :
    Measurable (fun z => lPlusPairSeam x k z i) := by
  have hs := (measurable_geometricRightSide_seam x i).comp
    (measurable_lPlusCertifiedCodingPairPath x)
  exact measurable_lPlusPairRawDartId_eval x k _
    ((measurable_inr.comp (measurable_inr.comp hs.fst)).prodMk hs.snd)

/-- Helper toward Lemma 5.5. Seam numbering agrees with the original
hatted representative of the source code-block side. -/
theorem lPlusPairSeam_eq_of_aligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r)
    (hk : 0 ≤ k) (i : ℕ) :
    lPlusPairSeam x k
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩ i =
      lPlusPairGluedDartId x k r s hk
        (s.toLPlusSidePresentationSourceWitness.gluedSeam4 x k r i) := by
  have hM : lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x
        ⟨(r, boundaryFutureHattedPath k s.W),
          LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩) =
      lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode := by
    unfold lMinusCoherentLeftSide lPlusHattedSide
    have hm : (if s.longest = true then XDP.ldp else XDP.sdp) = x := by
      cases h : s.longest <;> simpa only [h, Bool.false_eq_true, ↓reduceIte] using s.hmode
    exact (lPlusFaceMarks_side_eq hm _ _ _).symm
  change lPlusPairRawDartId x k (r, boundaryFutureHattedPath k s.W)
    (.inr (.inr ((lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩)).seam i).1),
      ((lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩)).seam i).2) = _
  rw [hM]
  rfl

/-- Helper toward Lemma 5.5. Local primed endpoints depend on a finite
prefix, before applying the orientation correction to the canonical dart. -/
theorem measurable_lPlusPairPrimedLocalEndpoint (x : XDP) (d : ℕ × Bool) :
    Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      kmswLimitDartVertex z.val.1.code.2.2 d) := by
  refine (measurable_of_factors_prefix d.1
    (fun p : ℕ → Fin 3 => kmswLimitDartVertex p d) ?_).comp
      ((measurable_lPlusSidePresentation_code x).snd.snd.comp
        (measurable_fst.comp measurable_subtype_coe))
  intro p p' hp
  simp only [kmswLimitDartVertex, edgeWest, edgeEast, kmswStage_congr hp]

/-- Helper toward Lemma 5.5. Raw endpoints are read in their own block.
The prefix reader is absent precisely when its finite hit is unavailable. -/
@[expose] noncomputable def lPlusPairRawEndpoint (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (a : LPlusRawEdge × Bool) :
    Option LPlusPairRawVertex :=
  match a.1 with
  | .inl e => (lPlusStoppedPrefixEndpointOption k z.val.1.code.1 (e, a.2)).map Sum.inl
  | .inr (.inl e) => some (.inr (.inl (kmswLimitDartVertex z.val.1.code.2.2 (e, a.2))))
  | .inr (.inr e) => some (.inr (.inr
      (if a.2 then (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)).east e
        else (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)).west e)))

/-- Helper toward Lemma 5.5. Every local raw endpoint reader is measurable. -/
theorem measurable_lPlusPairRawEndpoint (x : XDP) (k : ℤ) (a : LPlusRawEdge × Bool) :
    Measurable (fun z => lPlusPairRawEndpoint x k z a) := by
  rcases a with ⟨e, t⟩
  rcases e with e | (e | e)
  · exact (measurable_of_countable (fun o : Option ℕ => o.map
      (Sum.inl : ℕ → LPlusPairRawVertex))).comp
        ((measurable_lPlusStoppedPrefixEndpointOption k (e, t)).comp
          ((measurable_lPlusSidePresentation_code x).fst.comp
            (measurable_fst.comp measurable_subtype_coe)))
  · exact (measurable_of_countable (fun v : ℕ =>
      some (Sum.inr (Sum.inl v) : LPlusPairRawVertex))).comp
        (measurable_lPlusPairPrimedLocalEndpoint x (e, t))
  · have hm : Measurable (fun q => if t then (lMinusCoherentLeftSide x q).east e
        else (lMinusCoherentLeftSide x q).west e) := by
      apply measurable_to_countable'
      intro v
      exact measurableSet_lMinusCoherentLeftSide_incident x (e, t) v
    exact (measurable_of_countable (fun v : ℕ =>
      some (Sum.inr (Sum.inr v) : LPlusPairRawVertex))).comp
        (hm.comp (measurable_lPlusCertifiedCodingPairPath x))

/-- Helper toward Lemma 5.5. The canonical incidence graph retains its
raw geometric edge allocation and uses the full vertex kernel. -/
@[expose] noncomputable def lPlusPairIncident (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d : ℕ × Bool) (v : ℕ) : Prop :=
  ∃ a : LPlusRawEdge × Bool, ∃ u : LPlusPairRawVertex,
    lPlusPairRawEdgeAllocated x k z a.1 ∧
    lPlusPairRawDartId x k z.val a = d ∧ lPlusPairRawEndpoint x k z a = some u ∧
    lPlusPairFullVertexId x k z u = v

/-- Helper toward Lemma 5.5. West and east incidence coordinates are
measurable countable unions over allocated raw representatives. -/
theorem measurableSet_lPlusPairIncident (x : XDP) (k : ℤ) (d : ℕ × Bool) (v : ℕ) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x | lPlusPairIncident x k z d v} := by
  unfold lPlusPairIncident
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun u =>
    (measurableSet_lPlusPairRawEdgeAllocated x k a.1).inter
      ((((measurable_lPlusPairRawDartId x k a).comp measurable_subtype_coe).eq_const d).setOf.inter
        (((measurable_lPlusPairRawEndpoint x k a).eq_const (some u)).setOf.inter
          ((measurable_lPlusPairFullVertexId x k u).eq_const v).setOf))))

/-- Helper toward Lemma 5.5. A fixed-time creation certificate records the
oriented dart, rather than merely an unoriented triangle edge. -/
@[expose] def lPlusCreationDartAt (p : ℕ → Fin 3) (j : ℕ) (d : ℕ × Bool) : Prop :=
  ∃ h : p j = 0 ∨ p j = 1, d ∈ stageTriangleDartList p ⟨j, h⟩

/-- Helper toward Lemma 5.5. Fixed-time creation certificates are finite
cylinder events in the original code. -/
theorem measurableSet_lPlusCreationDartAt (j : ℕ) (d : ℕ × Bool) :
    MeasurableSet {p : ℕ → Fin 3 | lPlusCreationDartAt p j d} := by
  apply measurableSet_of_factors_prefix (j + 1)
  intro p p' hp
  have hc := hp j (Nat.lt_succ_self j)
  have hs : kmswStage p j = kmswStage p' j :=
    kmswStage_congr (fun i hi => hp i (by omega))
  constructor
  · rintro ⟨h, hd⟩
    exact ⟨hc ▸ h, by simpa only [stageTriangleDartList,
      stageTriangleDartTriple, hs, hc] using hd⟩
  · rintro ⟨h, hd⟩
    exact ⟨hc.symm ▸ h, by simpa only [stageTriangleDartList,
      stageTriangleDartTriple, hs, hc] using hd⟩

/-- Helper toward Lemma 5.5. Prefix creation darts must be created strictly
before the stopping time; the missing final edge creates no triangle. -/
@[expose] noncomputable def lPlusPrefixCreationDart (k : ℤ)
    (p : ℕ → Fin 3) (d : ℕ × Bool) : Prop :=
  ∃ hp : p ∈ lPlusPrefixHitDomain k, ∃ j : ℕ,
    j < lPlusPrefixHitIndex k ⟨p, hp⟩ ∧ lPlusCreationDartAt p j d

/-- Helper toward Lemma 5.5. Prefix creation events are measurable on the
entire code space, including codes with no finite hit. -/
theorem measurableSet_lPlusPrefixCreationDart (k : ℤ) (d : ℕ × Bool) :
    MeasurableSet {p : ℕ → Fin 3 | lPlusPrefixCreationDart k p d} := by
  have hm : MeasurableSet {p : lPlusPrefixHitDomain k | ∃ j : ℕ,
      j < lPlusPrefixHitIndex k p ∧ lPlusCreationDartAt p.val j d} := by
    simp only [Set.ofPred_exists, Set.ofPred_and]
    exact MeasurableSet.iUnion (fun j =>
      ((measurable_const.lt (measurable_lPlusPrefixHitIndex k)).setOf).inter
        ((measurableSet_lPlusCreationDartAt j d).preimage measurable_subtype_coe))
  have hi := MeasurableSet.subtype_image (measurableSet_lPlusPrefixHitDomain k) hm
  convert hi using 1
  ext p
  exact ⟨fun ⟨hp, j, hj, hd⟩ => ⟨⟨p, hp⟩, ⟨j, hj, hd⟩, rfl⟩,
    fun ⟨q, ⟨j, hj, hd⟩, hq⟩ => hq ▸ ⟨q.property, j, hj, hd⟩⟩

/-- Helper toward Lemma 5.5. The stopped code's creation certificates
recover precisely the run-zero creation times before the boundary hit. -/
theorem lPlusPrefixCreationDart_iff_of_aligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r)
    (hk : 0 ≤ k) (d : ℕ × Bool) :
    lPlusPrefixCreationDart k r.code.1 d ↔
      ∃ J : TriangleCreationTime (shiftedStream s.W 0),
        J.val < boundaryHitTime (shiftedStream s.W 0) s.h k ∧
        d ∈ stageTriangleDartList (shiftedStream s.W 0) J := by
  rw [← s.prefixCode_eq]
  have hhit := boundaryPrefixCode_mem_lPlusPrefixHitDomain s.W s.h k hk
  have ht := lPlusPrefixHitIndex_boundaryPrefixCode s.W s.h k hk
  have hcode (j : ℕ) (hj : j < boundaryHitTime (shiftedStream s.W 0) s.h k) :=
    lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt s.W s.h k hj
  constructor
  · rintro ⟨hp, j, hj, h, hd⟩
    rw [ht] at hj
    have hc := hcode j hj
    refine ⟨⟨j, hc ▸ h⟩, hj, ?_⟩
    have hs := kmswStage_congr (fun i hi => hcode i (hi.trans hj))
    simpa only [stageTriangleDartList, stageTriangleDartTriple, hc, hs] using hd
  · rintro ⟨J, hj, hd⟩
    have hc := hcode J.val hj
    refine ⟨hhit, J.val, by rw [ht]; exact hj, hc.symm ▸ J.property, ?_⟩
    have hs := kmswStage_congr (fun i hi => hcode i (hi.trans hj))
    simpa only [stageTriangleDartList, stageTriangleDartTriple, hc, hs] using hd

/-- Helper toward Lemma 5.5. A retained creation dart has a prefix,
primed, or retained hatted face certificate in the common canonical IDs. -/
@[expose] noncomputable def lPlusPairRetainedCreationDart (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d : ℕ × Bool) : Prop :=
  (∃ a : ℕ × Bool, lPlusPrefixCreationDart k z.val.1.code.1 a ∧
    lPlusPairRawDartId x k z.val (.inl a.1, a.2) = d) ∨
  (∃ a : ℕ × Bool, (∃ j : TriangleCreationTime z.val.1.code.2.2,
      a ∈ stageTriangleDartList z.val.1.code.2.2 j) ∧
    lPlusPairRawDartId x k z.val (.inr (.inl a.1), a.2) = d) ∨
  ∃ a b : ℕ × Bool,
    a.1 ∈ (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)).edges ∧
    b.1 ∈ (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)).edges ∧
    (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)).faceNext a b ∧
    lPlusPairRawDartId x k z.val (.inr (.inr a.1), a.2) = d

/-- Helper toward Lemma 5.5. The retained creation-triangle predicate is
measurable on certified pairs without choosing a source realization. -/
theorem measurableSet_lPlusPairRetainedCreationDart (x : XDP) (k : ℤ) (d : ℕ × Bool) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairRetainedCreationDart x k z d} := by
  have hid (a : LPlusRawEdge × Bool) : MeasurableSet
      {z : lPlusCertifiedCodingPairDomain x | lPlusPairRawDartId x k z.val a = d} :=
    (((measurable_lPlusPairRawDartId x k a).comp measurable_subtype_coe).eq_const d).setOf
  have hp (a : ℕ × Bool) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPrefixCreationDart k z.val.1.code.1 a} :=
    (measurableSet_lPlusPrefixCreationDart k a).preimage
    ((measurable_lPlusSidePresentation_code x).fst.comp
      (measurable_fst.comp measurable_subtype_coe))
  have ht (a : ℕ × Bool) := (measurableSet_lMinusPrimedTriangleDart x a).preimage
    (measurable_lPlusCertifiedCodingPairFuture x)
  unfold lPlusPairRetainedCreationDart
  simp only [Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  exact (MeasurableSet.iUnion (fun a => (hp a).inter (hid (.inl a.1, a.2)))).union
    ((MeasurableSet.iUnion (fun a => (ht a).inter (hid (.inr (.inl a.1), a.2)))).union
      (MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
        ((measurableSet_lMinusCoherentLeftSide_edges x a.1).preimage
          (measurable_lPlusCertifiedCodingPairPath x)).inter
        (((measurableSet_lMinusCoherentLeftSide_edges x b.1).preimage
          (measurable_lPlusCertifiedCodingPairPath x)).inter
        (((measurableSet_lMinusCoherentLeftSide_faceNext x a b).preimage
          (measurable_lPlusCertifiedCodingPairPath x)).inter
          (hid (.inr (.inr a.1), a.2))))))))

/-- Helper toward Lemma 5.5. Alignment identifies the hatted side used by
the measurable pair readers with the source's original hatted side. -/
theorem lPlusPairHattedSide_eq_of_aligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r) :
    lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩) =
      lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode := by
  unfold lMinusCoherentLeftSide lPlusHattedSide
  have hm : (if s.longest = true then XDP.ldp else XDP.sdp) = x := by
    cases h : s.longest <;> simpa only [h, Bool.false_eq_true, ↓reduceIte] using s.hmode
  exact (lPlusFaceMarks_side_eq hm _ _ _).symm

/-- Helper toward Lemma 5.5. The measurable retained-creation predicate
has exactly the run-zero geometric meaning on every aligned witness. -/
theorem lPlusPairRetainedCreationDart_iff_of_aligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r)
    (hk : 0 ≤ k) (a : LPlusGluedDart s.longest s.hqMode s.hτ) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    lPlusPairRetainedCreationDart x k z (lPlusPairGluedDartId x k r s hk a) ↔
      ∃ J : TriangleCreationTime (shiftedStream s.W 0),
        (D a).val ∈ stageTriangleDartList _ J ∧
        ∀ d ∈ stageTriangleDartList _ J,
          d.1 ∈ (m0GeodesicSide s.hp s.P .left).edges := by
  dsimp only
  let z : lPlusCertifiedCodingPairDomain x :=
    ⟨(r, boundaryFutureHattedPath k s.W),
      LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
  let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode
  have hM := lPlusPairHattedSide_eq_of_aligned x k r s
  change lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z) = M at hM
  have hc := lMinus_primed_observation_code (longest := s.longest) s.hτ
  change hatLawPrimedCodes (boundaryFutureCode k s.W) = _ at hc
  have hcode : r.code.2.2 =
      primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ :=
    s.primedCode_eq.symm.trans hc
  constructor
  · rintro (⟨b, hb, hid⟩ | ⟨b, ⟨j, hj⟩, hid⟩ | ⟨b, c, hbm, hcm, hbc, hid⟩)
    · obtain ⟨J, hJ, hbJ⟩ := (lPlusPrefixCreationDart_iff_of_aligned x k r s hk b).mp hb
      have hpos : 0 < k := by
        by_contra hn
        have hk0 : k = 0 := by omega
        subst k
        rw [boundaryHitTime_zero] at hJ
        omega
      let p : LPlusPrefixDart s.W s.h k := ⟨b, by
        rw [lPlusPrefixMinusEdges_eq_previousStage hpos]
        exact stageTriangleDartList_lt _ _ J
          (lPlus_prefix_creationTime_lt_previous _ s.h k hk J hJ) _ hbJ⟩
      have ha : (⟦Sum.inl p⟧ : LPlusGluedDart s.longest s.hqMode s.hτ) = a :=
        (lPlusPairGluedDartId_injective x k r s hk) hid
      refine ⟨J, ?_, s.toLPlusSidePresentationSourceWitness.prefix_creationTriangle_retained
        x k r hk J hJ⟩
      rw [← ha]
      exact hbJ
    · let j' : TriangleCreationTime
          (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ) :=
        ⟨j.val, by rw [← hcode]; exact j.property⟩
      have hj' : b ∈ stageTriangleDartList _ j' := by
        simpa only [stageTriangleDartList, stageTriangleDartTriple, j', hcode] using hj
      obtain ⟨J, hm, hret⟩ :=
        s.toLPlusSidePresentationSourceWitness.primed_creationTriangle_retained x k r j'
      have ha : (⟦Sum.inr (Sum.inl b)⟧ : LPlusGluedDart s.longest s.hqMode s.hτ) = a :=
        (lPlusPairGluedDartId_injective x k r s hk) hid
      refine ⟨J, ?_, hret⟩
      rw [← ha]
      exact (hm _).mpr ⟨b, hj', rfl⟩
    · have hbm' : b.1 ∈ M.edges := by rw [← hM]; exact hbm
      have hcm' : c.1 ∈ M.edges := by rw [← hM]; exact hcm
      have hbc' : M.faceNext b c := by rw [← hM]; exact hbc
      obtain ⟨J, hbJ, hret⟩ :=
        s.toLPlusSidePresentationSourceWitness.hatted_faceNext_actual_triangle x k r
          ⟨b, hbm'⟩ ⟨c, hcm'⟩ hbc'
      have ha : (⟦Sum.inr (Sum.inr (⟨b, hbm'⟩ : LPlusHattedDart M))⟧ :
          LPlusGluedDart s.longest s.hqMode s.hτ) = a :=
        (lPlusPairGluedDartId_injective x k r s hk) hid
      refine ⟨J, ?_, hret⟩
      rw [← ha]
      exact hbJ
  · rintro ⟨J, haJ, hret⟩
    have hface : (m0GeodesicSide s.hp s.P .left).faceNext (D a).val
        (kmswInfFaceSucc (shiftedStream s.W 0) (s.H.1 0) (D a).val) := by
      obtain ⟨G, hG, hb⟩ := lMinusRunZeroCreationTriangle_retained s.hp s.P J hret
      exact ⟨⟨G, hb _ haJ, hG⟩, rfl⟩
    rcases s.toLPlusSidePresentationSourceWitness.creationDart_prefix_or_future_block
        x k r J (D a).val haJ with hJ | ⟨b, j, hb, hj⟩ | ⟨b, j, hb, hj⟩
    · have hpos : 0 < k := by
        by_contra hn
        have hk0 : k = 0 := by omega
        subst k
        rw [boundaryHitTime_zero] at hJ
        omega
      let p : LPlusPrefixDart s.W s.h k := ⟨(D a).val, by
        rw [lPlusPrefixMinusEdges_eq_previousStage hpos]
        exact stageTriangleDartList_lt _ _ J
          (lPlus_prefix_creationTime_lt_previous _ s.h k hk J hJ) _ haJ⟩
      have hap : a = ⟦Sum.inl p⟧ := D.injective (Subtype.ext rfl)
      exact Or.inl ⟨(D a).val,
        (lPlusPrefixCreationDart_iff_of_aligned x k r s hk _).mpr ⟨J, hJ, haJ⟩,
        by rw [hap]; rfl⟩
    · have hab : a = ⟦Sum.inr (Sum.inl b)⟧ := D.injective (Subtype.ext hb.symm)
      let j' : TriangleCreationTime r.code.2.2 := ⟨j.val, by rw [hcode]; exact j.property⟩
      have hj' : b ∈ stageTriangleDartList _ j' := by
        simpa only [stageTriangleDartList, stageTriangleDartTriple, j', hcode] using hj
      exact Or.inr (Or.inl ⟨b, ⟨j', hj'⟩, by rw [hab]; rfl⟩)
    · have hactual : (m0GeodesicSide s.hp s.P .left).faceNext
          (boundaryGluingHatEdgeMap s.W s.h k s.hτ b.1, b.2)
          (kmswInfFaceSucc (shiftedStream s.W 0) (s.H.1 0) (D a).val) := hb ▸ hface
      have hr := s.toLPlusSidePresentationSourceWitness.hattedTriangle_retained_of_actual_faceNext
        x k r hk j b _ hj hactual
      let v := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s.W))
      have hs := boundaryGluing_decoded_stream s.W s.h k s.hτ
      let j' : TriangleCreationTime v := ⟨j.val, by
        change v j.val = 0 ∨ v j.val = 1
        dsimp only [v]
        rw [hs]
        exact j.property⟩
      have hlist : stageTriangleDartList _ j = stageTriangleDartList v j' := by
        simp only [stageTriangleDartList, stageTriangleDartTriple, j', v, hs]
      let c := kmswInfFaceSucc v (sourceAncestor_finite_incidence
        (if s.longest then XDP.ldp else XDP.sdp) renewalTime
        renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩) b
      have hcJ : c ∈ stageTriangleDartList v j' :=
        rMinusWhole_triangle_succ_mem v _ j' b (hlist ▸ hj)
      have hbc : M.faceNext b c :=
        ⟨⟨j', hlist ▸ hj, fun d hd => hr d (hlist.symm ▸ hd)⟩, rfl⟩
      let bM : LPlusHattedDart M := ⟨b, hr b hj⟩
      have hab : a = ⟦Sum.inr (Sum.inr bM)⟧ := D.injective (Subtype.ext hb.symm)
      refine Or.inr (Or.inr ⟨b, c, ?_, ?_, ?_, ?_⟩)
      · rw [hM]; exact hr b hj
      · rw [hM]; exact hr c (hlist.symm ▸ hcJ)
      · rw [hM]; exact hbc
      · rw [hab]; rfl

/-- Helper toward Lemma 5.5. A finite prefix-presence flag is only read
when the stopping stage exists. -/
@[expose] noncomputable def lPlusPairPrefixPresent (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (e : ℕ) : Prop :=
  (lPlusStoppedPrefixStage k z.val.1.code.1).map (fun F => F.present e) = some true

/-- Helper toward Lemma 5.5. Every finite prefix-presence flag is measurable. -/
theorem measurableSet_lPlusPairPrefixPresent (x : XDP) (k : ℤ) (e : ℕ) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x | lPlusPairPrefixPresent x k z e} := by
  let : MeasurableSpace (Option Bool) := ⊤
  exact (((measurable_lPlusStoppedPrefixStage_map k (fun F => F.present e)).comp
    ((measurable_lPlusSidePresentation_code x).fst.comp
      (measurable_fst.comp measurable_subtype_coe))).eq_const (some true)).setOf

/-- Helper toward Lemma 5.5. The directed edge set is the image of the
present edges in the three blocks, separately from geometric allocation. -/
@[expose] noncomputable def lPlusPairPresent (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (e : ℕ) : Prop :=
  (∃ a : ℕ, lPlusPairRawEdgeAllocated x k z (.inl a) ∧
    lPlusPairPrefixPresent x k z a ∧ lPlusRawEdgeClosureId x k z.val (.inl a) = e) ∨
  (∃ a : ℕ, (∃ n, a < (kmswMissingRootStage z.val.1.code.2.2 n).nextEdge ∧
      (kmswMissingRootStage z.val.1.code.2.2 n).present a = true) ∧
    lPlusRawEdgeClosureId x k z.val (.inr (.inl a)) = e) ∨
  ∃ a : ℕ, a ∈ (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)).present ∧
    lPlusRawEdgeClosureId x k z.val (.inr (.inr a)) = e

/-- Helper toward Lemma 5.5. Directed presence is measurable while
retaining missing geometric edges in the separate allocated carrier. -/
theorem measurableSet_lPlusPairPresent (x : XDP) (k : ℤ) (e : ℕ) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x | lPlusPairPresent x k z e} := by
  have hid (a : LPlusRawEdge) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusRawEdgeClosureId x k z.val a = e} :=
    ((measurable_lPlusCertifiedCodingPair_rawEdgeClosureId x k a).eq_const e).setOf
  have hp (a : ℕ) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      ∃ n, a < (kmswMissingRootStage z.val.1.code.2.2 n).nextEdge ∧
        (kmswMissingRootStage z.val.1.code.2.2 n).present a = true} :=
    (measurableSet_lMinusPrimedPresent x a).preimage
      (measurable_fst.comp (measurable_subtype_coe.comp (measurable_lPlusCertifiedCodingPairFuture x)))
  have hh (a : ℕ) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      a ∈ (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)).present} :=
    (measurableSet_geometricRightSide_present x a).preimage
      (measurable_lPlusCertifiedCodingPairPath x)
  unfold lPlusPairPresent
  simp only [Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  convert (MeasurableSet.iUnion (fun a =>
    (measurableSet_lPlusPairRawEdgeAllocated x k (.inl a)).inter
      ((measurableSet_lPlusPairPrefixPresent x k a).inter (hid (.inl a))))).union
    ((MeasurableSet.iUnion (fun a => (hp a).inter (hid (.inr (.inl a))))).union
      (MeasurableSet.iUnion (fun a =>
        (hh a).inter (hid (.inr (.inr a)))))) using 1
  simp only [Set.ofPred_exists, Set.ofPred_and]

/-- Helper toward Lemma 5.5. Directed orientation is directed presence
with the west endpoint bit, in the corrected canonical dart coordinates. -/
@[expose] noncomputable def lPlusPairOriented (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d : ℕ × Bool) : Prop :=
  lPlusPairPresent x k z d.1 ∧ d.2 = false

/-- Helper toward Lemma 5.5. The canonical west-oriented dart predicate
is measurable; east-oriented darts remain distinguishable. -/
theorem measurableSet_lPlusPairOriented (x : XDP) (k : ℤ) (d : ℕ × Bool) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x | lPlusPairOriented x k z d} :=
  (measurableSet_lPlusPairPresent x k d.1).inter (MeasurableSet.const (d.2 = false))

/-- Helper toward Lemma 5.5. On aligned witnesses the prefix-presence
test is exactly ambient directed presence for every allocated prefix edge. -/
theorem lPlusPairPrefixPresent_iff_of_aligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r)
    (hk : 0 ≤ k) (e : ℕ)
    (he : e ∈ boundaryGluingPrefixMinusEdges s.W s.h k) :
    lPlusPairPrefixPresent x k
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩ e ↔
      EdgePresent (shiftedStream s.W 0) e := by
  have hpos : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    subst k
    rw [boundaryGluingPrefixMinusEdges_zero] at he
    exact he.elim
  have he' : e < (kmswStage (shiftedStream s.W 0)
      (boundaryHitTime (shiftedStream s.W 0) s.h k)).nextEdge :=
    ((Set.ext_iff.mp (lPlusPrefixMinusEdges_eq_previousStage hpos) e).mp he).trans_le
      (kmswStage_nextEdge_mono _ (Nat.sub_le _ _))
  unfold lPlusPairPrefixPresent
  rw [← s.prefixCode_eq, lPlusStoppedPrefixStage_boundaryPrefixCode s.W s.h k hk]
  simp only [Option.map_some, Option.some.injEq]
  exact (lPlus_edgePresent_iff_hitStage_present _ s.h k hk e he').symm

/-- Helper toward Lemma 5.5. Every source block dart is allocated in the
pair code, including both darts of missing geometric edges. -/
theorem lPlusPairRawEdgeAllocated_of_block (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    lPlusPairRawEdgeAllocated x k
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
      (lPlusBlockDartRawLabel a).1 := by
  rcases a with a | (a | a)
  · exact (lPlusPairRawEdgeAllocated_prefix_iff_of_aligned x k r s hk a.val.1).mpr a.property
  · trivial
  · change a.val.1 ∈ (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x _)).edges
    rw [lPlusPairHattedSide_eq_of_aligned x k r s]
    exact a.property

/-- Helper toward Lemma 5.5. An allocated raw dart always has a source
block representative on aligned witnesses. -/
theorem exists_lPlusBlockDart_of_allocated (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a : LPlusRawEdge × Bool)
    (ha : lPlusPairRawEdgeAllocated x k
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩ a.1) :
    ∃ b : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode),
      lPlusBlockDartRawLabel b = a := by
  rcases a with ⟨e, t⟩
  rcases e with e | (e | e)
  · exact ⟨.inl ⟨(e, t),
      (lPlusPairRawEdgeAllocated_prefix_iff_of_aligned x k r s hk e).mp ha⟩, rfl⟩
  · exact ⟨.inr (.inl (e, t)), rfl⟩
  · change e ∈ (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x _)).edges at ha
    rw [lPlusPairHattedSide_eq_of_aligned x k r s] at ha
    exact ⟨.inr (.inr ⟨(e, t), ha⟩), rfl⟩

/-- Helper toward Lemma 5.5. Raw endpoint readers recover the exact
source block endpoint, before taking the full geometric vertex quotient. -/
theorem lPlusPairRawEndpoint_eq_of_aligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    lPlusPairRawEndpoint x k
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
      (lPlusBlockDartRawLabel a) =
      some (lPlusBlockVertexRawLabel
        (s.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r a)) := by
  rcases a with a | (a | a)
  · change (lPlusStoppedPrefixEndpointOption k r.code.1 a.val).map Sum.inl = _
    rw [lPlusStoppedPrefixEndpointOption_eq_endpoint_of_aligned x k r s hk a]
    rfl
  · have hc := lMinus_primed_observation_code (longest := s.longest) s.hτ
    change hatLawPrimedCodes (boundaryFutureCode k s.W) = _ at hc
    have hcode := s.primedCode_eq.symm.trans hc
    change some (Sum.inr (Sum.inl (kmswLimitDartVertex r.code.2.2 a)) :
      LPlusPairRawVertex) = _
    rw [hcode]
    rfl
  · change some (Sum.inr (Sum.inr (if a.val.2 then
      (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x _)).east a.val.1 else
      (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x _)).west a.val.1)) :
      LPlusPairRawVertex) = _
    rw [lPlusPairHattedSide_eq_of_aligned x k r s]
    rfl

/-- Helper toward Lemma 5.5. The measurable incidence graph is exactly
incidence in the source code-block side in the new vertex and dart IDs. -/
theorem lPlusPairIncident_iff_of_aligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode))
    (v : LPlusGluedVertex s.longest s.hqMode s.hτ) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairIncident x k z (lPlusPairGluedDartId x k r s hk ⟦a⟧)
        (lPlusPairGluedVertexId x k r s hk v) ↔
      geometricSideRelation
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) .incident
        (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inr ⟦a⟧))
        (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inl v)) := by
  dsimp only
  rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_incident_mk_iff x k r hk a v]
  let E := s.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r
  constructor
  · rintro ⟨b, u, hb, hid, hu, hv⟩
    obtain ⟨b', hbb⟩ := exists_lPlusBlockDart_of_allocated x k r s hk b hb
    subst b
    have hep := lPlusPairRawEndpoint_eq_of_aligned x k r s hk b'
    have hue : lPlusBlockVertexRawLabel (E b') = u := Option.some.inj (hep.symm.trans hu)
    have hba := (lPlusPairRawDartId_eq_iff_of_aligned x k r s hk b' a).mp hid
    have hev := (lPlusPairFullVertexId_eq_iff_of_aligned x k r s hk (E b') (E a)).mpr
      (by rw [s.toLPlusSidePresentationSourceWitness.blockEndpoint4_image,
        s.toLPlusSidePresentationSourceWitness.blockEndpoint4_image, hba])
    apply lPlusPairGluedVertexId_injective x k r s hk
    change lPlusPairFullVertexId x k _ (lPlusBlockVertexRawLabel (E a)) = _
    rw [← hev, hue]
    exact hv
  · intro h
    refine ⟨lPlusBlockDartRawLabel a, lPlusBlockVertexRawLabel (E a),
      lPlusPairRawEdgeAllocated_of_block x k r s hk a, rfl,
      lPlusPairRawEndpoint_eq_of_aligned x k r s hk a, ?_⟩
    exact congrArg (lPlusPairGluedVertexId x k r s hk) h

local instance : MeasurableSpace (Option (List ℕ × ℕ)) := ⊤
local instance : MeasurableSpace (Option (LPlusRawEdge × Bool)) := ⊤

/-- Helper toward Lemma 5.5. Exterior marks read the reversed lower word
of the deleted prefix and the length of the consumed upper-left attachment. -/
@[expose] noncomputable def lPlusPairBoundaryData (k : ℤ) (p : ℕ → Fin 3) :
    Option (List ℕ × ℕ) :=
  if hp : p ∈ lPlusPrefixHitDomain k then
    let n := lPlusPrefixHitIndex k ⟨p, hp⟩
    let F := kmswStage p (n - 1)
    some ((if 0 < k then (F.LL ++ F.LR).reverse else []),
      (kmswStage p n).UL.dropLast.length)
  else none

/-- Helper toward Lemma 5.5. All finite exterior-boundary data are
measurable by finite cylinders and the first boundary hit. -/
theorem measurable_lPlusPairBoundaryData (k : ℤ) :
    Measurable (lPlusPairBoundaryData k) := by
  have hs (n : ℕ) : Measurable (fun p : ℕ → Fin 3 =>
      some ((if 0 < k then ((kmswStage p (n - 1)).LL ++
        (kmswStage p (n - 1)).LR).reverse else []),
        (kmswStage p n).UL.dropLast.length)) := by
    apply measurable_of_factors_prefix n
    intro p p' hp
    rw [kmswStage_congr hp,
      kmswStage_congr (fun i hi => hp i (hi.trans_le (Nat.sub_le _ _)))]
  have hj : Measurable (fun q : ℕ × (ℕ → Fin 3) =>
      some ((if 0 < k then ((kmswStage q.2 (q.1 - 1)).LL ++
        (kmswStage q.2 (q.1 - 1)).LR).reverse else []),
        (kmswStage q.2 q.1).UL.dropLast.length)) :=
    measurable_from_prod_countable_right hs
  exact (hj.comp ((measurable_lPlusPrefixHitIndex k).prodMk measurable_subtype_coe)).dite
    measurable_const (measurableSet_lPlusPrefixHitDomain k)

/-- Helper toward Lemma 5.5. The indexed exterior raw dart is read from
the finite lower word followed by the unconsumed primed exterior boundary.
It is absent only when the prefix hit is unavailable. -/
@[expose] noncomputable def lPlusPairBoundaryRawOption (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (i : ℕ) : Option (LPlusRawEdge × Bool) :=
  (lPlusPairBoundaryData k z.val.1.code.1).map (fun D =>
    if hi : i < D.1.length then (.inl D.1[i], true) else
      (.inr (.inl (lMinusCodeExteriorBoundaryEdge z.val.1.code.2.2
        (D.2 + i - D.1.length))), true))

/-- Helper toward Lemma 5.5. Every indexed exterior raw dart reader is
measurable on certified pairs. -/
theorem measurable_lPlusPairBoundaryRawOption (x : XDP) (k : ℤ) (i : ℕ) :
    Measurable (fun z => lPlusPairBoundaryRawOption x k z i) := by
  have hp : Measurable (fun z : lPlusCertifiedCodingPairDomain x => z.val.1.code.1) :=
    (measurable_lPlusSidePresentation_code x).fst.comp
      (measurable_fst.comp measurable_subtype_coe)
  have hprimed : Measurable (fun z : lPlusCertifiedCodingPairDomain x => z.val.1.code.2.2) :=
    (measurable_lPlusSidePresentation_code x).snd.snd.comp
      (measurable_fst.comp measurable_subtype_coe)
  let F (o : Option (List ℕ × ℕ)) (z : lPlusCertifiedCodingPairDomain x) :=
    o.map (fun D => if hi : i < D.1.length then
      ((Sum.inl D.1[i] : LPlusRawEdge), true) else
      (.inr (.inl (lMinusCodeExteriorBoundaryEdge z.val.1.code.2.2
        (D.2 + i - D.1.length))), true))
  have hF (o : Option (List ℕ × ℕ)) : Measurable (F o) := by
    cases o with
    | none => exact measurable_const
    | some D =>
      by_cases hi : i < D.1.length
      · simpa only [F, Option.map_some, dite_eq_left hi] using
          (measurable_const : Measurable (fun _ : lPlusCertifiedCodingPairDomain x =>
            some ((Sum.inl D.1[i] : LPlusRawEdge), true)))
      · have hm := (measurable_lMinusCodeExteriorBoundaryEdge_apply
          (D.2 + i - D.1.length)).comp hprimed
        simpa only [F, Option.map_some, dite_eq_right hi, Function.comp_def] using
          (measurable_of_countable (fun e : ℕ =>
            some ((Sum.inr (Sum.inl e) : LPlusRawEdge), true))).comp hm
  have hj : Measurable (fun q : lPlusCertifiedCodingPairDomain x ×
      Option (List ℕ × ℕ) => F q.2 q.1) :=
    measurable_from_prod_countable_left hF
  exact hj.comp (measurable_id.prodMk ((measurable_lPlusPairBoundaryData k).comp hp))

/-- Helper toward Lemma 5.5. Stopped exterior data agree with the exact
source stages, retaining the empty prefix at index zero. -/
theorem lPlusPairBoundaryData_eq_of_aligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k) :
    lPlusPairBoundaryData k r.code.1 =
      some ((if 0 < k then
        ((kmswStage (shiftedStream s.W 0)
          (boundaryHitTime (shiftedStream s.W 0) s.h k - 1)).LL ++
        (kmswStage (shiftedStream s.W 0)
          (boundaryHitTime (shiftedStream s.W 0) s.h k - 1)).LR).reverse else []),
        (kmswStage (shiftedStream s.W 0)
          (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.length) := by
  rw [← s.prefixCode_eq, lPlusPairBoundaryData,
    dite_eq_left (boundaryPrefixCode_mem_lPlusPrefixHitDomain s.W s.h k hk),
    lPlusPrefixHitIndex_boundaryPrefixCode s.W s.h k hk]
  have hs := kmswStage_congr (fun i hi =>
    lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt s.W s.h k hi)
  have hf := kmswStage_congr (n := boundaryHitTime (shiftedStream s.W 0) s.h k - 1) (fun i hi =>
    lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt s.W s.h k
      (hi.trans_le (Nat.sub_le _ _)))
  dsimp only
  rw [hs, hf]

/-- Helper toward Lemma 5.5. Exterior marks retain the new canonical dart
ID and are absent on the unavailable-prefix branch. -/
@[expose] noncomputable def lPlusPairBoundaryOption (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (i : ℕ) : Option (ℕ × Bool) :=
  (lPlusPairBoundaryRawOption x k z i).map (lPlusPairRawDartId x k z.val)

local instance : MeasurableSpace (Option (ℕ × Bool)) := ⊤

/-- Helper toward Lemma 5.5. Every indexed canonical exterior mark is
measurable, with its original endpoint bit. -/
theorem measurable_lPlusPairBoundaryOption (x : XDP) (k : ℤ) (i : ℕ) :
    Measurable (fun z => lPlusPairBoundaryOption x k z i) := by
  have hF (o : Option (LPlusRawEdge × Bool)) : Measurable
      (fun z : lPlusCertifiedCodingPairDomain x => o.map (lPlusPairRawDartId x k z.val)) := by
    cases o with
    | none => exact measurable_const
    | some a =>
      exact (measurable_of_countable (fun d : ℕ × Bool => some d)).comp
        ((measurable_lPlusPairRawDartId x k a).comp measurable_subtype_coe)
  apply measurable_to_countable'
  intro n
  change MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
    lPlusPairBoundaryOption x k z i = n}
  have he : {z : lPlusCertifiedCodingPairDomain x | lPlusPairBoundaryOption x k z i = n} =
      ⋃ o : Option (LPlusRawEdge × Bool), {z | lPlusPairBoundaryRawOption x k z i = o} ∩
        {z | o.map (lPlusPairRawDartId x k z.val) = n} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨lPlusPairBoundaryRawOption x k z i, rfl, h⟩,
      fun ⟨o, ho, hn⟩ => by unfold lPlusPairBoundaryOption; rw [ho]; exact hn⟩
  rw [he]
  exact MeasurableSet.iUnion (fun o =>
    ((measurable_lPlusPairBoundaryRawOption x k i).eq_const o).setOf.inter
      ((hF o).eq_const n).setOf)

/-- Helper toward Lemma 5.5. The root tag in the code-block side is
exactly equality with the measurable pair root in the new vertex IDs. -/
theorem lPlusPairRoot_tag_iff_of_aligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (v : LPlusGluedVertex s.longest s.hqMode s.hτ) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    geometricSideRelation
      (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) .root
      (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inl v))
      (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inl v)) ↔
      lPlusPairGluedVertexId x k r s hk v = lPlusPairRoot x k z := by
  dsimp only
  rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_root_iff x k r hk,
    lPlusPairRoot_eq_of_aligned x k r s hk]
  exact Sum.inl.inj_iff.trans (lPlusPairGluedVertexId_injective x k r s hk).eq_iff.symm

/-- Helper toward Lemma 5.5. Incidence at an aligned dart determines one
numeric endpoint, even when the tested numeric vertex is not preallocated. -/
theorem lPlusPairIncident_eq_endpoint_of_aligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) (v : ℕ) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairIncident x k z (lPlusPairGluedDartId x k r s hk ⟦a⟧) v ↔
      v = lPlusPairGluedVertexId x k r s hk
        ⟦s.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r a⟧ := by
  dsimp only
  let E := s.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r
  constructor
  · rintro ⟨b, u, hb, hid, hu, hv⟩
    obtain ⟨b', hbb⟩ := exists_lPlusBlockDart_of_allocated x k r s hk b hb
    subst b
    have hep := lPlusPairRawEndpoint_eq_of_aligned x k r s hk b'
    have hue : lPlusBlockVertexRawLabel (E b') = u := Option.some.inj (hep.symm.trans hu)
    have hba := (lPlusPairRawDartId_eq_iff_of_aligned x k r s hk b' a).mp hid
    have hev := (lPlusPairFullVertexId_eq_iff_of_aligned x k r s hk (E b') (E a)).mpr
      (by rw [s.toLPlusSidePresentationSourceWitness.blockEndpoint4_image,
        s.toLPlusSidePresentationSourceWitness.blockEndpoint4_image, hba])
    exact hv.symm.trans ((congrArg (fun u => lPlusPairFullVertexId x k _ u) hue).symm.trans hev)
  · intro h
    exact ⟨lPlusBlockDartRawLabel a, lPlusBlockVertexRawLabel (E a),
      lPlusPairRawEdgeAllocated_of_block x k r s hk a, rfl,
      lPlusPairRawEndpoint_eq_of_aligned x k r s hk a, h.symm⟩

/-- Helper toward Lemma 5.5. Total endpoint coordinates select the least
incident full vertex ID, with zero on the empty incidence branch. On source
pairs the proved incidence uniqueness identifies the selected endpoint. -/
@[expose] noncomputable def lPlusPairEndpoint (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d : ℕ × Bool) : ℕ :=
  if h : ∃ v, lPlusPairIncident x k z d v then Nat.find h else 0

/-- Helper toward Lemma 5.5. All total west and east endpoint readers are
measurable countable selections, with no source-witness choice. -/
theorem measurable_lPlusPairEndpoint (x : XDP) (k : ℤ) (d : ℕ × Bool) :
    Measurable (fun z => lPlusPairEndpoint x k z d) := by
  have hA : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      ∃ v, lPlusPairIncident x k z d v} := by
    simpa only [Set.ofPred_exists] using
      MeasurableSet.iUnion (fun v => measurableSet_lPlusPairIncident x k d v)
  have hs : Measurable (fun z : {z : lPlusCertifiedCodingPairDomain x |
      ∃ v, lPlusPairIncident x k z d v} => Nat.find z.property) := by
    apply measurable_find (fun z => z.property)
    intro v
    exact (measurableSet_lPlusPairIncident x k d v).preimage measurable_subtype_coe
  exact hs.dite measurable_const hA

/-- Helper toward Lemma 5.5. Total endpoint readers recover the source
code-block endpoint at every source geometric dart, including missing edges. -/
theorem lPlusPairEndpoint_eq_of_aligned (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairEndpoint x k z (lPlusPairGluedDartId x k r s hk ⟦a⟧) =
      lPlusPairGluedVertexId x k r s hk
        ⟦s.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r a⟧ := by
  dsimp only
  have hex : ∃ v, lPlusPairIncident x k
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
      (lPlusPairGluedDartId x k r s hk ⟦a⟧) v :=
    ⟨_, (lPlusPairIncident_eq_endpoint_of_aligned x k r s hk a _).mpr rfl⟩
  rw [lPlusPairEndpoint, dite_eq_left hex]
  exact (lPlusPairIncident_eq_endpoint_of_aligned x k r s hk a _).mp (Nat.find_spec hex)

/-- Helper toward Lemma 5.5. The future block face graph records primed
creation successors and retained hatted successors in the common three-block
IDs. It does not include the finite prefix's faces. -/
@[expose] noncomputable def lPlusPairFutureFaceNext (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d e : ℕ × Bool) : Prop :=
  (∃ a b : ℕ × Bool,
    lPlusPairRawDartId x k z.val (.inr (.inl a.1), a.2) = d ∧
    lPlusPairRawDartId x k z.val (.inr (.inl b.1), b.2) = e ∧
    (∃ j : TriangleCreationTime z.val.1.code.2.2,
      a ∈ stageTriangleDartList z.val.1.code.2.2 j) ∧
    kmswInfFaceSucc z.val.1.code.2.2 z.property.2.1 a = b) ∨
  ∃ a b : ℕ × Bool,
    a.1 ∈ (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)).edges ∧
    b.1 ∈ (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)).edges ∧
    lPlusPairRawDartId x k z.val (.inr (.inr a.1), a.2) = d ∧
    lPlusPairRawDartId x k z.val (.inr (.inr b.1), b.2) = e ∧
    (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)).faceNext a b

/-- Helper toward Lemma 5.5. The future face graph is measurable before
the prefix faces or corrected rotation are assembled. -/
theorem measurableSet_lPlusPairFutureFaceNext (x : XDP) (k : ℤ) (d e : ℕ × Bool) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x | lPlusPairFutureFaceNext x k z d e} := by
  have hid (a : LPlusRawEdge × Bool) (v : ℕ × Bool) : MeasurableSet
      {z : lPlusCertifiedCodingPairDomain x | lPlusPairRawDartId x k z.val a = v} :=
    (((measurable_lPlusPairRawDartId x k a).comp measurable_subtype_coe).eq_const v).setOf
  have ht (a : ℕ × Bool) := (measurableSet_lMinusPrimedTriangleDart x a).preimage
    (measurable_lPlusCertifiedCodingPairFuture x)
  have hs (a b : ℕ × Bool) :=
    ((((measurable_lMinusCanonicalCodingDomain_primedFaceSucc x a).comp
      (measurable_lPlusCertifiedCodingPairFuture x)).eq_const b).setOf)
  unfold lPlusPairFutureFaceNext
  simp only [Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  exact (MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
    (hid (.inr (.inl a.1), a.2) d).inter ((hid (.inr (.inl b.1), b.2) e).inter
      ((ht a).inter (hs a b)))))).union
    (MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
      ((measurableSet_lMinusCoherentLeftSide_edges x a.1).preimage
        (measurable_lPlusCertifiedCodingPairPath x)).inter
      (((measurableSet_lMinusCoherentLeftSide_edges x b.1).preimage
        (measurable_lPlusCertifiedCodingPairPath x)).inter
      ((hid (.inr (.inr a.1), a.2) d).inter ((hid (.inr (.inr b.1), b.2) e).inter
      ((measurableSet_lMinusCoherentLeftSide_faceNext x a b).preimage
        (measurable_lPlusCertifiedCodingPairPath x))))))))

end DirectedDistances.PaperProofs.Section5






























































































