/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusPairMeasurable5
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusPairFaceMarks

/-! Rotation graphs in the measurable three-block dart coordinates. These coordinates
are distinguished from the whole-plane labels of `lPlusCanonicalSide4`. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

attribute [local instance] instMeasurableSpaceOptionListNat_directedDistances_1

/-- Helper toward Lemma 5.5. Composition acts first by the right graph. -/
@[expose] def lPlusPairRotationCompose (R S : (ℕ × Bool) → (ℕ × Bool) → Prop)
    (d e : ℕ × Bool) : Prop := ∃ m, S d m ∧ R m e

/-- Helper toward Lemma 5.5. Identity extension fixes only allocated darts
outside the block's input domain. -/
@[expose] def lPlusPairRotationExtend (A : Set (ℕ × Bool))
    (R : (ℕ × Bool) → (ℕ × Bool) → Prop) (d e : ℕ × Bool) : Prop :=
  R d e ∨ (d = e ∧ d ∈ A ∧ ¬ ∃ m, R d m)

/-- Helper toward Lemma 5.5. The literal swap graph, including coincident ports. -/
@[expose] def lPlusPairRotationSwap (A : Set (ℕ × Bool))
    (a b d e : ℕ × Bool) : Prop :=
  (d = a ∧ e = b) ∨ (d = b ∧ e = a) ∨
    (d ≠ a ∧ d ≠ b ∧ d = e ∧ d ∈ A)

/-- Helper toward Lemma 5.5. The common dart carrier is the union of the
three block permutation domains; no source realization is selected. -/
@[expose] noncomputable def lPlusPairRotationDomain (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) : Set (ℕ × Bool) :=
  {d | ∃ e, lPlusPairPrefixRotationGraph x k z d e ∨
    lPlusPairPrimedRotationGraph x k z d e ∨ lPlusPairHattedRotationGraph x k z d e}

/-- Helper toward Lemma 5.5. Every dart-domain coordinate is measurable. -/
theorem measurableSet_lPlusPairRotationDomain (x : XDP) (k : ℤ) (d : ℕ × Bool) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      d ∈ lPlusPairRotationDomain x k z} := by
  change MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
    ∃ e, lPlusPairPrefixRotationGraph x k z d e ∨
      lPlusPairPrimedRotationGraph x k z d e ∨ lPlusPairHattedRotationGraph x k z d e}
  simp only [Set.ofPred_exists, Set.ofPred_or]
  exact MeasurableSet.iUnion (fun e =>
    (measurableSet_lPlusPairPrefixRotationGraph x k d e).union
      ((measurableSet_lPlusPairPrimedRotationGraph x k d e).union
        (measurableSet_lPlusPairHattedRotationGraph x k d e)))

/-- Helper toward Lemma 5.5. Finite attachment corners in raw pair IDs.
The empty list contributes no port. -/
@[expose] noncomputable def lPlusPairUpperLeftRotationGraph (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d e : ℕ × Bool) : Prop :=
  ∃ es : List ℕ,
    (lPlusStoppedPrefixStage k z.val.1.code.1).map
      (fun S => S.UL.dropLast.reverse) = some es ∧
    ∃ a : Fin es.length × Bool,
      lPlusPairRawDartId x k z.val (.inl es[a.1.val], a.2) = d ∧
      lPlusPairRawDartId x k z.val
        (.inl es[(lPlusUpperLeftCornerPerm es.length a).1.val],
          (lPlusUpperLeftCornerPerm es.length a).2) = e

/-- Helper toward Lemma 5.5. The finite attachment-corner graph is measurable
by countably many fixed-list and fixed-port tests. -/
theorem measurableSet_lPlusPairUpperLeftRotationGraph (x : XDP) (k : ℤ)
    (d e : ℕ × Bool) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairUpperLeftRotationGraph x k z d e} := by
  unfold lPlusPairUpperLeftRotationGraph
  simp only [Set.ofPred_exists, Set.ofPred_and]
  refine MeasurableSet.iUnion (fun es =>
    (((measurable_lPlusCertifiedCodingPair_prefixUpperLeftList x k).eq_const
      (some es)).setOf).inter (MeasurableSet.iUnion (fun a => ?_)))
  exact ((((measurable_lPlusPairRawDartId x k (.inl es[a.1.val], a.2)).comp
    measurable_subtype_coe).eq_const d).setOf).inter
    ((((measurable_lPlusPairRawDartId x k
      (.inl es[(lPlusUpperLeftCornerPerm es.length a).1.val],
        (lPlusUpperLeftCornerPerm es.length a).2)).comp
      measurable_subtype_coe).eq_const e).setOf)

/-- Helper toward Lemma 5.5. Beta ports use the hatted boundary edge label
and retain the endpoint bit. -/
@[expose] noncomputable def lPlusPairBetaDartId (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (a : ℕ × Bool) : ℕ × Bool :=
  lPlusPairRawDartId x k z.val
    (.inr (.inr (kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode z.val.2)) a.1)), a.2)

/-- Helper toward Lemma 5.5. Indexed beta ports are measurable without
choosing a source stream. -/
theorem measurable_lPlusPairBetaEdge (x : XDP) (i : ℕ) :
    Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      kmswLeftBoundaryEdge (boltzmannKMSWStream (pathCode z.val.2)) i) := by
  exact (measurable_lMinusLeftBoundaryEdge_code i).comp
    (measurable_pathCode.comp (measurable_snd.comp measurable_subtype_coe))

/-- Helper toward Lemma 5.5. The hatted raw coordinate accepts a measurable
variable edge label through the countable product. -/
theorem measurable_lPlusPairHattedDartId_uncurry (x : XDP) (k : ℤ) (b : Bool) :
    Measurable (fun w : ℕ × lPlusCertifiedCodingPairDomain x =>
      lPlusPairRawDartId x k w.2.val (.inr (.inr w.1), b)) := by
  apply measurable_from_prod_countable_right
  intro n
  exact (measurable_lPlusPairRawDartId x k (.inr (.inr n), b)).comp
    measurable_subtype_coe

/-- Helper toward Lemma 5.5. Every beta port has a measurable canonical ID. -/
theorem measurable_lPlusPairBetaDartId (x : XDP) (k : ℤ) (a : ℕ × Bool) :
    Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      lPlusPairBetaDartId x k z a) := by
  apply measurable_to_countable'
  intro b
  change MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
    lPlusPairBetaDartId x k z a = b}
  have he : {z : lPlusCertifiedCodingPairDomain x | lPlusPairBetaDartId x k z a = b} =
      ⋃ n : ℕ, {z | kmswLeftBoundaryEdge
        (boltzmannKMSWStream (pathCode z.val.2)) a.1 = n} ∩
        {z | lPlusPairRawDartId x k z.val (.inr (.inr n), a.2) = b} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨n, hn, h⟩
      unfold lPlusPairBetaDartId
      rw [hn]
      exact h
  rw [he]
  exact MeasurableSet.iUnion (fun n =>
    ((measurable_lPlusPairBetaEdge x a.1).eq_const n).setOf.inter
      ((((measurable_lPlusPairRawDartId x k (.inr (.inr n), a.2)).comp
        measurable_subtype_coe).eq_const b).setOf))

/-- Helper toward Lemma 5.5. The infinite beta corner exchange graph. -/
@[expose] noncomputable def lPlusPairBetaRotationGraph (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d e : ℕ × Bool) : Prop :=
  ∃ a : ℕ × Bool, lPlusPairBetaDartId x k z a = d ∧
    lPlusPairBetaDartId x k z (lMinusBoundaryCornerPerm a) = e

/-- Helper toward Lemma 5.5. Every beta corner graph coordinate is measurable. -/
theorem measurableSet_lPlusPairBetaRotationGraph (x : XDP) (k : ℤ)
    (d e : ℕ × Bool) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairBetaRotationGraph x k z d e} := by
  unfold lPlusPairBetaRotationGraph
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun a =>
    ((measurable_lPlusPairBetaDartId x k a).eq_const d).setOf.inter
      ((measurable_lPlusPairBetaDartId x k (lMinusBoundaryCornerPerm a)).eq_const e).setOf)

/-- Helper toward Lemma 5.5. The five factors act in source order: prefix,
finite corner, primed, beta corner, hatted. Each acts on the common carrier. -/
@[expose] noncomputable def lPlusPairFiveFactorRotationGraph (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) : (ℕ × Bool) → (ℕ × Bool) → Prop :=
  let E := lPlusPairRotationExtend (lPlusPairRotationDomain x k z)
  lPlusPairRotationCompose (E (lPlusPairHattedRotationGraph x k z))
    (lPlusPairRotationCompose (E (lPlusPairBetaRotationGraph x k z))
      (lPlusPairRotationCompose (E (lPlusPairPrimedRotationGraph x k z))
        (lPlusPairRotationCompose (E (lPlusPairUpperLeftRotationGraph x k z))
          (E (lPlusPairPrefixRotationGraph x k z)))))

/-- Helper toward Lemma 5.5. The terminal port is absent for an empty
attachment, including index zero on aligned sources. -/
@[expose] noncomputable def lPlusPairTerminalDartGraph (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (t : ℕ × Bool) : Prop :=
  ∃ es : List ℕ,
    (lPlusStoppedPrefixStage k z.val.1.code.1).map
      (fun S => S.UL.dropLast.reverse) = some es ∧
    ∃ hn : 0 < es.length,
      lPlusPairRawDartId x k z.val
        (.inl es[es.length - 1], false) = t

/-- Helper toward Lemma 5.5. All five identity-extended factors have a
measurable composed graph on the certified pair space. -/
theorem measurableSet_lPlusPairFiveFactorRotationGraph (x : XDP) (k : ℤ)
    (d e : ℕ × Bool) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairFiveFactorRotationGraph x k z d e} := by
  let Z := lPlusCertifiedCodingPairDomain x
  let A := lPlusPairRotationDomain x k
  have hExt (R : Z → (ℕ × Bool) → (ℕ × Bool) → Prop)
      (hR : ∀ a b, MeasurableSet {z | R z a b}) (a b : ℕ × Bool) :
      MeasurableSet {z | lPlusPairRotationExtend (A z) (R z) a b} := by
    have hn : MeasurableSet {z : Z | ¬ ∃ m, R z a m} := by
      convert (MeasurableSet.iUnion (fun m => hR a m)).compl using 1
      ext z
      simp
    change MeasurableSet {z | R z a b ∨
      (a = b ∧ a ∈ A z ∧ ¬ ∃ m, R z a m)}
    simp only [Set.ofPred_or, Set.ofPred_and]
    exact (hR a b).union ((MeasurableSet.const (a = b)).inter
      ((measurableSet_lPlusPairRotationDomain x k a).inter
        hn))
  have hMul (R S : Z → (ℕ × Bool) → (ℕ × Bool) → Prop)
      (hR : ∀ a b, MeasurableSet {z | R z a b})
      (hS : ∀ a b, MeasurableSet {z | S z a b}) (a b : ℕ × Bool) :
      MeasurableSet {z | lPlusPairRotationCompose (R z) (S z) a b} := by
    change MeasurableSet {z | ∃ m, S z a m ∧ R z m b}
    simp only [Set.ofPred_exists, Set.ofPred_and]
    exact MeasurableSet.iUnion (fun m => (hS a m).inter (hR m b))
  exact hMul _ _ (hExt _ (measurableSet_lPlusPairHattedRotationGraph x k))
    (hMul _ _ (hExt _ (measurableSet_lPlusPairBetaRotationGraph x k))
      (hMul _ _ (hExt _ (measurableSet_lPlusPairPrimedRotationGraph x k))
        (hMul _ _ (hExt _ (measurableSet_lPlusPairUpperLeftRotationGraph x k))
          (hExt _ (measurableSet_lPlusPairPrefixRotationGraph x k))))) d e

/-- Helper toward Lemma 5.5. The terminal-port event is measurable. -/
theorem measurableSet_lPlusPairTerminalDartGraph (x : XDP) (k : ℤ)
    (t : ℕ × Bool) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairTerminalDartGraph x k z t} := by
  unfold lPlusPairTerminalDartGraph
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun es =>
    ((measurable_lPlusCertifiedCodingPair_prefixUpperLeftList x k).eq_const
      (some es)).setOf.inter (MeasurableSet.iUnion (fun hn =>
        (((measurable_lPlusPairRawDartId x k
          (.inl es[es.length - 1], false)).comp
            measurable_subtype_coe).eq_const t).setOf)))

/-- Helper toward Lemma 5.5. Rotation 4 adds the terminal-output swap
and the final prefix cap to the five-factor graph. -/
@[expose] noncomputable def lPlusPairCorrectedRotationGraph (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (d e : ℕ × Bool) : Prop :=
  let A := lPlusPairRotationDomain x k z
  let C := lPlusPairFiveFactorRotationGraph x k z
  let PE := lPlusPairRotationExtend A (lPlusPairPrefixRotationGraph x k z)
  let TE := lPlusPairRotationExtend A (lPlusPairPrimedRotationGraph x k z)
  (¬ (∃ t, lPlusPairTerminalDartGraph x k z t)) ∧ C d e ∨
    ∃ t pt ct tt : ℕ × Bool,
      lPlusPairTerminalDartGraph x k z t ∧ PE t pt ∧ C t ct ∧ TE t tt ∧
      lPlusPairRotationCompose (lPlusPairRotationSwap A t pt)
        (lPlusPairRotationCompose (lPlusPairRotationSwap A ct tt) C) d e

/-- Helper toward Lemma 5.5. The complete relational rotation-4 assembly,
including both terminal swaps and the empty attachment, is measurable. -/
theorem measurableSet_lPlusPairCorrectedRotationGraph (x : XDP) (k : ℤ)
    (d e : ℕ × Bool) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairCorrectedRotationGraph x k z d e} := by
  let Z := lPlusCertifiedCodingPairDomain x
  let A := lPlusPairRotationDomain x k
  have hExt (R : Z → (ℕ × Bool) → (ℕ × Bool) → Prop)
      (hR : ∀ a b, MeasurableSet {z | R z a b}) (a b : ℕ × Bool) :
      MeasurableSet {z | lPlusPairRotationExtend (A z) (R z) a b} := by
    have hn : MeasurableSet {z : Z | ¬ ∃ m, R z a m} := by
      convert (MeasurableSet.iUnion (fun m => hR a m)).compl using 1
      ext z
      simp
    change MeasurableSet {z | R z a b ∨
      (a = b ∧ a ∈ A z ∧ ¬ ∃ m, R z a m)}
    simp only [Set.ofPred_or, Set.ofPred_and]
    exact (hR a b).union ((MeasurableSet.const (a = b)).inter
      ((measurableSet_lPlusPairRotationDomain x k a).inter
        hn))
  have hMul (R S : Z → (ℕ × Bool) → (ℕ × Bool) → Prop)
      (hR : ∀ a b, MeasurableSet {z | R z a b})
      (hS : ∀ a b, MeasurableSet {z | S z a b}) (a b : ℕ × Bool) :
      MeasurableSet {z | lPlusPairRotationCompose (R z) (S z) a b} := by
    change MeasurableSet {z | ∃ m, S z a m ∧ R z m b}
    simp only [Set.ofPred_exists, Set.ofPred_and]
    exact MeasurableSet.iUnion (fun m => (hS a m).inter (hR m b))
  have hSwap (u v a b : ℕ × Bool) :
      MeasurableSet {z : Z | lPlusPairRotationSwap (A z) u v a b} := by
    change MeasurableSet {z : Z | (a = u ∧ b = v) ∨ (a = v ∧ b = u) ∨
      (a ≠ u ∧ a ≠ v ∧ a = b ∧ a ∈ A z)}
    simp only [Set.ofPred_or, Set.ofPred_and]
    exact ((MeasurableSet.const _).inter (MeasurableSet.const _)).union
      (((MeasurableSet.const _).inter (MeasurableSet.const _)).union
      ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter
        ((MeasurableSet.const _).inter (measurableSet_lPlusPairRotationDomain x k a)))))
  have hn : MeasurableSet {z : Z | ¬ ∃ t, lPlusPairTerminalDartGraph x k z t} := by
    convert (MeasurableSet.iUnion (fun t =>
      measurableSet_lPlusPairTerminalDartGraph x k t)).compl using 1
    ext z
    simp
    rfl
  unfold lPlusPairCorrectedRotationGraph
  dsimp only
  simp only [Set.ofPred_or, Set.ofPred_and, Set.ofPred_exists]
  refine (hn.inter (measurableSet_lPlusPairFiveFactorRotationGraph x k d e)).union ?_
  refine MeasurableSet.iUnion (fun t => MeasurableSet.iUnion (fun pt =>
    MeasurableSet.iUnion (fun ct => MeasurableSet.iUnion (fun tt => ?_))))
  exact (measurableSet_lPlusPairTerminalDartGraph x k t).inter
    ((hExt _ (measurableSet_lPlusPairPrefixRotationGraph x k) t pt).inter
      ((measurableSet_lPlusPairFiveFactorRotationGraph x k t ct).inter
        ((hExt _ (measurableSet_lPlusPairPrimedRotationGraph x k) t tt).inter
          (hMul _ _ (hSwap t pt)
            (hMul _ _ (hSwap ct tt)
              (measurableSet_lPlusPairFiveFactorRotationGraph x k)) d e))))

/-- Helper toward Lemma 5.5. The canonical side's rotation is exactly
corrected rotation 4 on every aligned source, at all nonnegative indices. -/
theorem lPlusCanonicalSide4_rotation_iff_corrected_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (d e : LPlusGluedDart s.longest s.hqMode s.hτ) :
    (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk).rotation
      (lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk d).val
      (lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk e).val ↔
    lPlusGluedCorrectedRotation4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk d = e :=
  lPlusCodeBlockSide4_rotation_glued_iff s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk d e

section Aligned

variable (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
  (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)

local notation "zₛ" => (Subtype.mk (r, boundaryFutureHattedPath k s.W)
  (LPlusSourceWitnessAligned.codingPair_mem_domain x k r s) :
    lPlusCertifiedCodingPairDomain x)
local notation "Fₛ" => lPlusPairGluedDartId x k r s hk
local notation "IPₛ" => lPlusPrefixGluedDart (hτ := s.hτ) (hqMode := s.hqMode)
local notation "ITₛ" => lPlusPrimedGluedDart (hτ := s.hτ) (hqMode := s.hqMode)
local notation "IHₛ" => lPlusHattedGluedDart (hτ := s.hτ) (hqMode := s.hqMode)

/-- Helper toward Lemma 5.5. The prefix graph is the exact source block
graph, including the empty prefix at zero. -/
theorem lPlusPairPrefixRotationGraph_iff_source (d e : ℕ × Bool) :
    lPlusPairPrefixRotationGraph x k zₛ d e ↔
      lMinusEncodedPermGraph (Fₛ ∘ IPₛ)
        (lPlusPrefixRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) d e := by
  by_cases hpos : 0 < k
  · exact lPlusPairPrefixRotationGraph_iff_encoded_of_aligned x k r s hpos d e
  · have hk0 : k = 0 := by omega
    constructor
    · rintro ⟨h, _⟩
      exact (hpos h).elim
    · rintro ⟨a, _, _⟩
      have ha := a.property
      have hz := (congrArg (fun j => boundaryGluingPrefixMinusEdges s.W s.h j) hk0).trans
        (boundaryGluingPrefixMinusEdges_zero s.W s.h)
      exact ((Set.ext_iff.mp hz a.val.1).mp ha).elim

/-- Helper toward Lemma 5.5. The complete primed graph agrees with the
source permutation in the orientation-corrected pair coordinates. -/
theorem lPlusPairPrimedRotationGraph_iff_source (d e : ℕ × Bool) :
    lPlusPairPrimedRotationGraph x k zₛ d e ↔
      lMinusEncodedPermGraph (Fₛ ∘ ITₛ)
        (kmswInfRot (primedCode
          (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ)
          (primedCode_finiteIncidence _ s.hτ s.hfin)) d e := by
  rw [lPlusPairPrimedRotationGraph_iff_encoded]
  have hc := lMinus_primed_observation_code (longest := s.longest) s.hτ
  change hatLawPrimedCodes (boundaryFutureCode k s.W) = _ at hc
  have hcode := s.primedCode_eq.symm.trans hc
  change lMinusEncodedPermGraph
    (fun a : ℕ × Bool => lPlusPairRawDartId x k
      (r, boundaryFutureHattedPath k s.W) (.inr (.inl a.1), a.2))
    (kmswInfRot r.code.2.2 _) d e ↔ _
  rw [kmswInfRot_congr_stream hcode]
  rfl

/-- Helper toward Lemma 5.5. The hatted rotation graph agrees with the
source retained hatted permutation, with its actual edge carrier. -/
theorem lPlusPairHattedRotationGraph_iff_source (d e : ℕ × Bool) :
    lPlusPairHattedRotationGraph x k zₛ d e ↔
      lMinusEncodedPermGraph (Fₛ ∘ IHₛ)
        (lPlusHattedRotation (if s.longest then XDP.ldp else XDP.sdp)
          ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩) d e := by
  rcases s with ⟨⟨W, h, H, hLL, longest, hτ, hp, P, hqMode, Tpath, hfin,
    hleft, hprefix, hcoherent, hprimed⟩, hmode⟩
  change (if longest then XDP.ldp else XDP.sdp) = x at hmode
  subst x
  exact lPlusPairHattedRotationGraph_iff_encoded _ k _ d e

/-- Helper toward Lemma 5.5. The finite corner graph agrees with the
source upper-left corner permutation in the pair dart coordinates. -/
theorem lPlusPairUpperLeftRotationGraph_iff_source (d e : ℕ × Bool) :
    lPlusPairUpperLeftRotationGraph x k zₛ d e ↔
      lMinusEncodedPermGraph
        (Fₛ ∘ lPlusUpperLeftGluedDart s.hτ s.hqMode s.hfin hk)
        (lPlusUpperLeftCornerPerm ((kmswStage (shiftedStream s.W 0)
          (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse.length)) d e := by
  unfold lPlusPairUpperLeftRotationGraph
  rw [lPlusStoppedPrefixStage_upperLeftList_of_aligned x k r s hk]
  constructor
  · rintro ⟨es, he, a, ha, hb⟩
    have he' := Option.some.inj he
    subst es
    exact ⟨a, ha, hb⟩
  · rintro ⟨a, ha, hb⟩
    exact ⟨_, rfl, a, ha, hb⟩

/-- Helper toward Lemma 5.5. The beta corner graph is the exact source
infinite-boundary corner permutation in pair coordinates. -/
theorem lPlusPairBetaRotationGraph_iff_source (d e : ℕ × Bool) :
    lPlusPairBetaRotationGraph x k zₛ d e ↔
      lMinusEncodedPermGraph (Fₛ ∘ lPlusBetaGluedDart s.hτ s.hqMode)
        lMinusBoundaryCornerPerm d e := by
  rfl

/-- Helper toward Lemma 5.5. The common rotation carrier is precisely the
range of the injective geometric quotient numbering. -/
theorem lPlusPairRotationDomain_iff_source (d : ℕ × Bool) :
    d ∈ lPlusPairRotationDomain x k zₛ ↔ d ∈ Set.range Fₛ := by
  constructor
  · rintro ⟨e, h | h | h⟩
    · obtain ⟨a, ha, _⟩ := (lPlusPairPrefixRotationGraph_iff_source x k r s hk d e).mp h
      exact ⟨IPₛ a, ha⟩
    · obtain ⟨a, ha, _⟩ := (lPlusPairPrimedRotationGraph_iff_source x k r s hk d e).mp h
      exact ⟨ITₛ a, ha⟩
    · obtain ⟨a, ha, _⟩ := (lPlusPairHattedRotationGraph_iff_source x k r s hk d e).mp h
      exact ⟨IHₛ a, ha⟩
  · rintro ⟨q, hq⟩
    revert hq
    refine Quotient.inductionOn q ?_
    intro a ha
    rcases a with a | (a | a)
    · refine ⟨Fₛ (IPₛ ((lPlusPrefixRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) a)), Or.inl ?_⟩
      exact (lPlusPairPrefixRotationGraph_iff_source x k r s hk _ _).mpr ⟨a, ha, rfl⟩
    · refine ⟨Fₛ (ITₛ ((kmswInfRot (primedCode
        (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ)
        (primedCode_finiteIncidence _ s.hτ s.hfin)) a)), Or.inr (Or.inl ?_)⟩
      exact (lPlusPairPrimedRotationGraph_iff_source x k r s hk _ _).mpr ⟨a, ha, rfl⟩
    · refine ⟨Fₛ (IHₛ ((lPlusHattedRotation (if s.longest then XDP.ldp else XDP.sdp)
        ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩) a)), Or.inr (Or.inr ?_)⟩
      exact (lPlusPairHattedRotationGraph_iff_source x k r s hk _ _).mpr ⟨a, ha, rfl⟩

/-- Helper toward Lemma 5.5. All five measurable factors identify with
the original corrected glued permutation in the same quotient coordinates. -/
theorem lPlusPairPrefixExtendedRotationGraph_iff_source (d e : ℕ × Bool) :
    lPlusPairRotationExtend (lPlusPairRotationDomain x k zₛ)
      (lPlusPairPrefixRotationGraph x k zₛ) d e ↔
    lMinusEncodedPermGraph Fₛ
      (lPlusPrefixExtendedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) d e := by
  rw [lPlusPrefixExtendedRotation, lMinusEncodedPermGraph_extend Fₛ
    (lPlusPairGluedDartId_injective x k r s hk)]
  simp only [lPlusPairRotationExtend, lPlusPairPrefixRotationGraph_iff_source x k r s hk,
    lPlusPairRotationDomain_iff_source x k r s hk]

/-- Helper toward Lemma 5.5. Identity extension of the primed block has
the exact encoded source graph. -/
theorem lPlusPairPrimedExtendedRotationGraph_iff_source (d e : ℕ × Bool) :
    lPlusPairRotationExtend (lPlusPairRotationDomain x k zₛ)
      (lPlusPairPrimedRotationGraph x k zₛ) d e ↔
    lMinusEncodedPermGraph Fₛ (lPlusPrimedExtendedRotation s.hτ s.hqMode s.hfin) d e := by
  rw [lPlusPrimedExtendedRotation, lMinusEncodedPermGraph_extend Fₛ
    (lPlusPairGluedDartId_injective x k r s hk)]
  simp only [lPlusPairRotationExtend, lPlusPairPrimedRotationGraph_iff_source x k r s hk,
    lPlusPairRotationDomain_iff_source x k r s hk]

/-- Helper toward Lemma 5.5. Identity extension of the hatted block has
the exact encoded source graph. -/
theorem lPlusPairHattedExtendedRotationGraph_iff_source (d e : ℕ × Bool) :
    lPlusPairRotationExtend (lPlusPairRotationDomain x k zₛ)
      (lPlusPairHattedRotationGraph x k zₛ) d e ↔
    lMinusEncodedPermGraph Fₛ (lPlusHattedExtendedRotation s.hτ s.hqMode) d e := by
  erw [lPlusHattedExtendedRotation, lMinusEncodedPermGraph_extend Fₛ
    (lPlusPairGluedDartId_injective x k r s hk) IHₛ
    (lPlusHattedGluedDart_injective (hτ := s.hτ) (hqMode := s.hqMode))
    (lPlusHattedRotation (if s.longest then XDP.ldp else XDP.sdp)
      ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩) d e]
  simp only [lPlusPairRotationExtend, lPlusPairHattedRotationGraph_iff_source x k r s hk,
    lPlusPairRotationDomain_iff_source x k r s hk]

/-- Helper toward Lemma 5.5. Identity extension of the finite corner has
the exact encoded source graph. -/
theorem lPlusPairUpperLeftExtendedRotationGraph_iff_source (d e : ℕ × Bool) :
    lPlusPairRotationExtend (lPlusPairRotationDomain x k zₛ)
      (lPlusPairUpperLeftRotationGraph x k zₛ) d e ↔
    lMinusEncodedPermGraph Fₛ (lPlusUpperLeftCornerRotation s.hτ s.hqMode s.hfin hk) d e := by
  let j := lPlusUpperLeftGluedDart s.hτ s.hqMode s.hfin hk
  let p := lPlusUpperLeftCornerPerm ((kmswStage (shiftedStream s.W 0)
    (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse.length)
  let U := lPlusUpperLeftCornerRotation s.hτ s.hqMode s.hfin hk
  have happ (a) : U (j a) = j (p a) :=
    Equiv.Perm.extendDomain_apply_image p
      (Equiv.ofInjective j (lPlusUpperLeftGluedDart_injective s.hτ s.hqMode s.hfin hk)) a
  have hfix (q) (hq : q ∉ Set.range j) : U q = q :=
    Equiv.Perm.extendDomain_apply_not_subtype p
      (Equiv.ofInjective j (lPlusUpperLeftGluedDart_injective s.hτ s.hqMode s.hfin hk)) hq
  change lPlusPairRotationExtend _ _ d e ↔ lMinusEncodedPermGraph Fₛ U d e
  simp only [lPlusPairRotationExtend, lPlusPairUpperLeftRotationGraph_iff_source x k r s hk,
    lPlusPairRotationDomain_iff_source x k r s hk]
  change (lMinusEncodedPermGraph (Fₛ ∘ j) p d e ∨
    (d = e ∧ d ∈ Set.range Fₛ ∧ ¬ ∃ m, lMinusEncodedPermGraph (Fₛ ∘ j) p d m)) ↔ _
  constructor
  · rintro (⟨a, ha, hb⟩ | ⟨rfl, ⟨q, hq⟩, hn⟩)
    · exact ⟨j a, ha, (congrArg Fₛ (happ a)).trans hb⟩
    · have hout : q ∉ Set.range j := by
        rintro ⟨a, rfl⟩
        exact hn ⟨_, a, hq, rfl⟩
      exact ⟨q, hq, (congrArg Fₛ (hfix q hout)).trans hq⟩
  · rintro ⟨q, hq, he⟩
    by_cases hmem : q ∈ Set.range j
    · obtain ⟨a, rfl⟩ := hmem
      exact Or.inl ⟨a, hq, (congrArg Fₛ (happ a)).symm.trans he⟩
    · refine Or.inr ⟨hq.symm.trans ((congrArg Fₛ (hfix q hmem)).symm.trans he), ⟨q, hq⟩, ?_⟩
      rintro ⟨m, a, ha, _⟩
      exact hmem ⟨a, (lPlusPairGluedDartId_injective x k r s hk) (ha.trans hq.symm)⟩

/-- Helper toward Lemma 5.5. Identity extension of the beta corner has
the exact encoded source graph. -/
theorem lPlusPairBetaExtendedRotationGraph_iff_source (d e : ℕ × Bool) :
    lPlusPairRotationExtend (lPlusPairRotationDomain x k zₛ)
      (lPlusPairBetaRotationGraph x k zₛ) d e ↔
    lMinusEncodedPermGraph Fₛ (lPlusBetaCornerRotation s.hτ s.hqMode) d e := by
  rw [lPlusBetaCornerRotation, lMinusEncodedPermGraph_extend Fₛ
    (lPlusPairGluedDartId_injective x k r s hk)]
  simp only [lPlusPairRotationExtend, lPlusPairBetaRotationGraph_iff_source x k r s hk,
    lPlusPairRotationDomain_iff_source x k r s hk]

/-- Helper toward Lemma 5.5. Composition of encoded graphs is multiplication
of the permutations on the injectively numbered dart carrier. -/
theorem lPlusPairRotationCompose_encoded {α : Type*} (f : α → ℕ × Bool)
    (hf : Function.Injective f) (p q : Equiv.Perm α) (d e : ℕ × Bool) :
    lPlusPairRotationCompose (lMinusEncodedPermGraph f p)
      (lMinusEncodedPermGraph f q) d e ↔ lMinusEncodedPermGraph f (p * q) d e :=
  (lMinusEncodedPermGraph_mul f hf p q d e).symm

/-- Helper toward Lemma 5.5. The full five-factor graph agrees with the
original corrected permutation before the terminal repairs. -/
theorem lPlusPairFiveFactorRotationGraph_iff_source (d e : ℕ × Bool) :
    lPlusPairFiveFactorRotationGraph x k zₛ d e ↔
      lMinusEncodedPermGraph Fₛ
        (lPlusGluedCorrectedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) d e := by
  simp only [lPlusPairFiveFactorRotationGraph, lPlusPairRotationCompose,
    lPlusPairPrefixExtendedRotationGraph_iff_source x k r s hk,
    lPlusPairPrimedExtendedRotationGraph_iff_source x k r s hk,
    lPlusPairHattedExtendedRotationGraph_iff_source x k r s hk,
    lPlusPairUpperLeftExtendedRotationGraph_iff_source x k r s hk,
    lPlusPairBetaExtendedRotationGraph_iff_source x k r s hk,
    lMinusEncodedPermGraph_mul Fₛ (lPlusPairGluedDartId_injective x k r s hk),
    mul_assoc, lPlusGluedCorrectedRotation]

/-- Helper toward Lemma 5.5. Terminal-port selection agrees exactly with
the source last upper-left port, without a default when the chain is empty. -/
theorem lPlusPairTerminalDartGraph_iff_source (t : ℕ × Bool) :
    lPlusPairTerminalDartGraph x k zₛ t ↔
      ∃ hn : 0 < ((kmswStage (shiftedStream s.W 0)
        (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse.length),
      Fₛ (lPlusUpperLeftGluedDart s.hτ s.hqMode s.hfin hk
        (⟨((kmswStage (shiftedStream s.W 0)
          (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse.length) - 1,
            by omega⟩, false)) = t := by
  unfold lPlusPairTerminalDartGraph
  rw [lPlusStoppedPrefixStage_upperLeftList_of_aligned x k r s hk]
  constructor
  · rintro ⟨es, he, hn, ht⟩
    have he' := Option.some.inj he
    subst es
    exact ⟨hn, ht⟩
  · rintro ⟨hn, ht⟩
    exact ⟨_, rfl, hn, ht⟩

/-- Helper toward Lemma 5.5. Swaps of source quotient darts are exactly
the literal measurable-coordinate swaps on the allocated carrier. -/
theorem lPlusPairRotationSwap_iff_source
    (a b : LPlusGluedDart s.longest s.hqMode s.hτ) (d e : ℕ × Bool) :
    lPlusPairRotationSwap (lPlusPairRotationDomain x k zₛ) (Fₛ a) (Fₛ b) d e ↔
      lMinusEncodedPermGraph Fₛ (Equiv.swap a b) d e := by
  rw [lMinusEncodedPermGraph_swap Fₛ (lPlusPairGluedDartId_injective x k r s hk)]
  simp only [lPlusPairRotationSwap, lPlusPairRotationDomain_iff_source x k r s hk]

/-- Helper toward Lemma 5.5. The full measurable assembly identifies with
corrected rotation 4 on every aligned nonnegative source pair. -/
theorem lPlusPairCorrectedRotationGraph_iff_source (d e : ℕ × Bool) :
    lPlusPairCorrectedRotationGraph x k zₛ d e ↔
      lMinusEncodedPermGraph Fₛ
        (lPlusGluedCorrectedRotation4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) d e := by
  let es := (kmswStage (shiftedStream s.W 0)
    (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse
  let C := lPlusGluedCorrectedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  let PE := lPlusPrefixExtendedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  let TE := lPlusPrimedExtendedRotation s.hτ s.hqMode s.hfin
  have hEval (p : Equiv.Perm (LPlusGluedDart s.longest s.hqMode s.hτ))
      (a) (b : ℕ × Bool) : lMinusEncodedPermGraph Fₛ p (Fₛ a) b ↔ Fₛ (p a) = b := by
    constructor
    · rintro ⟨q, hq, hb⟩
      have hqa := (lPlusPairGluedDartId_injective x k r s hk) hq
      exact hqa ▸ hb
    · intro hb
      exact ⟨a, rfl, hb⟩
  by_cases hn : 0 < es.length
  · let t := lPlusUpperLeftGluedDart s.hτ s.hqMode s.hfin hk
      (⟨es.length - 1, by change es.length - 1 < es.length; omega⟩, false)
    have hterm (u : ℕ × Bool) : lPlusPairTerminalDartGraph x k zₛ u ↔ Fₛ t = u := by
      rw [lPlusPairTerminalDartGraph_iff_source x k r s hk]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hn, h⟩⟩
    unfold lPlusPairCorrectedRotationGraph
    dsimp only
    simp only [hterm, lPlusPairPrefixExtendedRotationGraph_iff_source x k r s hk,
      lPlusPairPrimedExtendedRotationGraph_iff_source x k r s hk,
      lPlusPairFiveFactorRotationGraph_iff_source x k r s hk]
    suffices hgraph :
        lPlusPairRotationCompose
          (lPlusPairRotationSwap (lPlusPairRotationDomain x k zₛ) (Fₛ t) (Fₛ (PE t)))
          (lPlusPairRotationCompose
            (lPlusPairRotationSwap (lPlusPairRotationDomain x k zₛ) (Fₛ (C t)) (Fₛ (TE t)))
            (lPlusPairFiveFactorRotationGraph x k zₛ)) d e ↔
          lMinusEncodedPermGraph Fₛ
            (lPlusGluedCorrectedRotation4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) d e by
      constructor
      · rintro (⟨hno, _⟩ | ⟨u, pt, ct, tt, hu, hpt, hct, htt, h⟩)
        · exact (hno ⟨_, rfl⟩).elim
        · subst u
          have hp := (hEval PE t pt).mp hpt
          have hc := (hEval C t ct).mp hct
          have ht := (hEval TE t tt).mp htt
          subst pt
          subst ct
          subst tt
          exact hgraph.mp h
      · intro h
        exact Or.inr ⟨_, _, _, _, rfl, (hEval PE t _).mpr rfl,
          (hEval C t _).mpr rfl, (hEval TE t _).mpr rfl, hgraph.mpr h⟩
    simp only [lPlusPairRotationCompose, lPlusPairRotationSwap_iff_source x k r s hk,
      lPlusPairFiveFactorRotationGraph_iff_source x k r s hk,
      ← lMinusEncodedPermGraph_mul Fₛ (lPlusPairGluedDartId_injective x k r s hk)]
    rw [lPlusGluedCorrectedRotation4, dite_eq_left hn,
      lPlusGluedBlockRotation2, dite_eq_left hn]
  · have hterm (u : ℕ × Bool) : ¬ lPlusPairTerminalDartGraph x k zₛ u := by
      rw [lPlusPairTerminalDartGraph_iff_source x k r s hk]
      rintro ⟨h, _⟩
      exact hn h
    unfold lPlusPairCorrectedRotationGraph
    dsimp only
    simp only [hterm, exists_false, not_false_eq_true, true_and, false_and,
      or_false, lPlusPairFiveFactorRotationGraph_iff_source x k r s hk]
    rw [lPlusGluedCorrectedRotation4, dite_eq_right hn,
      lPlusGluedBlockRotation2, dite_eq_right hn]

/-- Helper toward Lemma 5.5. The measurable graph in pair IDs is precisely
the canonical side's rotation after the proved injective dart renumbering. -/
theorem lPlusPairCorrectedRotationGraph_iff_canonicalSide4
    (d e : LPlusGluedDart s.longest s.hqMode s.hτ) :
    lPlusPairCorrectedRotationGraph x k zₛ (Fₛ d) (Fₛ e) ↔
      (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk).rotation
        (lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk d).val
        (lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk e).val := by
  rw [lPlusPairCorrectedRotationGraph_iff_source x k r s hk,
    lPlusCanonicalSide4_rotation_iff_corrected_of_aligned x k r s hk]
  constructor
  · rintro ⟨a, ha, hb⟩
    have had := (lPlusPairGluedDartId_injective x k r s hk) ha
    subst a
    exact (lPlusPairGluedDartId_injective x k r s hk) hb
  · intro h
    exact ⟨d, rfl, congrArg Fₛ h⟩

end Aligned

end DirectedDistances.PaperProofs.Section5






























/- temporary `#print axioms` commands in this file, through the specified wrapper
and with the specified `-o` target. The successful probe compile exited 0.
The transitive lists contained only propext, Classical.choice, and Quot.sound
(or subsets, including the empty list). The probes were removed before the
final production compile. No custom axiom or placeholder was introduced.
Only this project source file was edited. No separate checker, independent -/
