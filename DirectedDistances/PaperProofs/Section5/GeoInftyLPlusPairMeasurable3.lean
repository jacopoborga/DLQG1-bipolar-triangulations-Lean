/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusPairMeasurable2

/-! Measurable finite stopped-prefix data from the presentation's first code.
The complete three-block class reconstruction is a separate obligation. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. Prefixes whose right coordinate reaches the
nonnegative-index boundary level. This domain asserts no source realization. -/
@[expose] def lPlusPrefixHitDomain (k : ℤ) : Set (ℕ → Fin 3) :=
  {p | ∃ n, R p n = -k}

/-- Helper toward Lemma 5.5. The finite-hit domain is measurable by a
countable union of finite-coordinate tests. -/
theorem measurableSet_lPlusPrefixHitDomain (k : ℤ) :
    MeasurableSet (lPlusPrefixHitDomain k) := by
  have hm (n : ℕ) : Measurable (fun p : ℕ → Fin 3 => R p n) :=
    measurable_of_factors_prefix n _ (fun p p' hp => R_congr hp)
  simpa only [lPlusPrefixHitDomain, Set.iUnion_ofPred] using
    MeasurableSet.iUnion (fun n => ((hm n).eq_const (-k)).setOf)

/-- Helper toward Lemma 5.5. The first right-coordinate hit is selected
only on its proved finite-hit domain. -/
@[expose] noncomputable def lPlusPrefixHitIndex (k : ℤ)
    (p : lPlusPrefixHitDomain k) : ℕ := Nat.find p.property

/-- Helper toward Lemma 5.5. Least-hit selection is measurable; it is not
a choice of a source walk or geometric realization. -/
theorem measurable_lPlusPrefixHitIndex (k : ℤ) :
    Measurable (lPlusPrefixHitIndex k) := by
  apply measurable_find (fun p => p.property)
  intro n
  exact (((measurable_of_factors_prefix n (fun p : ℕ → Fin 3 => R p n)
    (fun p p' hp => R_congr hp)).comp measurable_subtype_coe).eq_const (-k)).setOf

/-- Helper toward Lemma 5.5. The complete stopped finite KMSW stage, absent
when the encoded right-coordinate hit never occurs. -/
@[expose] noncomputable def lPlusStoppedPrefixStage (k : ℤ)
    (p : ℕ → Fin 3) : Option State :=
  if hp : p ∈ lPlusPrefixHitDomain k then
    some (kmswStage p (lPlusPrefixHitIndex k ⟨p, hp⟩))
  else none

/-- Helper toward Lemma 5.5. Every measurable-space-valued observation of
the stopped finite stage is measurable, since each fixed stage factors
through finitely many `Fin 3` coordinates. No measurability of `f` is assumed. -/
theorem measurable_lPlusStoppedPrefixStage_map (k : ℤ)
    {β : Type*} [MeasurableSpace (Option β)] (f : State → β) :
    Measurable (fun p : ℕ → Fin 3 => (lPlusStoppedPrefixStage k p).map f) := by
  have hstage (n : ℕ) : Measurable (fun p : ℕ → Fin 3 => some (f (kmswStage p n))) :=
    measurable_of_factors_prefix n _ (fun p p' hp =>
      congrArg (fun S => some (f S)) (kmswStage_congr hp))
  have hjoint : Measurable (fun z : ℕ × (ℕ → Fin 3) => some (f (kmswStage z.2 z.1))) :=
    measurable_from_prod_countable_right hstage
  have hsub : Measurable (fun p : lPlusPrefixHitDomain k =>
      some (f (kmswStage p.val (lPlusPrefixHitIndex k p)))) :=
    hjoint.comp ((measurable_lPlusPrefixHitIndex k).prodMk measurable_subtype_coe)
  convert hsub.dite (measurable_const (a := (none : Option β)))
    (measurableSet_lPlusPrefixHitDomain k) using 1
  funext p
  dsimp only [lPlusStoppedPrefixStage]
  split <;> rfl

/-- Helper toward Lemma 5.5. The stopped-prefix code reaches the same
right-coordinate boundary level as its source stream. -/
theorem boundaryPrefixCode_mem_lPlusPrefixHitDomain
    (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0))
    (k : ℤ) (hk : 0 ≤ k) :
    boundaryPrefixCode k W ∈ lPlusPrefixHitDomain k := by
  by_cases hk0 : k = 0
  · subst k
    exact ⟨0, by simp [R]⟩
  · refine ⟨boundaryHitTime (shiftedStream W 0) h k, ?_⟩
    exact (R_congr (fun i hi =>
      lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W h k hi)).trans
      (boundaryHitTime_right_spec (shiftedStream W 0) h (by omega))

/-- Helper toward Lemma 5.5. Decoding the stopped prefix recovers the
exact source stopping index, including the zero endpoint. -/
theorem lPlusPrefixHitIndex_boundaryPrefixCode
    (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0))
    (k : ℤ) (hk : 0 ≤ k) :
    lPlusPrefixHitIndex k
      ⟨boundaryPrefixCode k W, boundaryPrefixCode_mem_lPlusPrefixHitDomain W h k hk⟩ =
      boundaryHitTime (shiftedStream W 0) h k := by
  let hp : ∃ n, R (boundaryPrefixCode k W) n = -k :=
    boundaryPrefixCode_mem_lPlusPrefixHitDomain W h k hk
  change Nat.find hp = _
  by_cases hk0 : k = 0
  · subst k
    rw [boundaryHitTime_zero]
    apply Nat.eq_zero_of_le_zero
    exact Nat.find_min' hp (by simp [R])
  · have hkp : 0 < k := by omega
    let t := boundaryHitTime (shiftedStream W 0) h k
    have hhit : R (boundaryPrefixCode k W) t = -k :=
      (R_congr (fun i hi =>
        lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W h k hi)).trans
        (boundaryHitTime_right_spec (shiftedStream W 0) h (by omega))
    have hle : Nat.find hp ≤ t := Nat.find_min' hp hhit
    have hsource : R (shiftedStream W 0) (Nat.find hp) = -k := by
      rw [← R_congr (fun i hi =>
        lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W h k (hi.trans_le hle))]
      exact Nat.find_spec hp
    have htime : t = Nat.find (h.rightHit k (by omega)) := by
      simp only [t, boundaryHitTime, dite_eq_right hk0, dite_eq_left hkp]
    exact Nat.le_antisymm hle (by
      change t ≤ Nat.find hp
      rw [htime]
      exact Nat.find_min' (h.rightHit k (by omega)) hsource)

/-- Helper toward Lemma 5.5. The optional finite-stage decoder agrees
with every source witness, without using a chosen preimage. -/
theorem lPlusStoppedPrefixStage_boundaryPrefixCode
    (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0))
    (k : ℤ) (hk : 0 ≤ k) :
    lPlusStoppedPrefixStage k (boundaryPrefixCode k W) =
      some (kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)) := by
  rw [lPlusStoppedPrefixStage,
    dite_eq_left (boundaryPrefixCode_mem_lPlusPrefixHitDomain W h k hk),
    lPlusPrefixHitIndex_boundaryPrefixCode W h k hk]
  exact congrArg some (kmswStage_congr (fun i hi =>
    lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W h k hi))

/-- Helper toward Lemma 5.5. Every coordinate of the preceding finite
stage is measurable on the finite-hit domain. Its geometric identification
with the deleted prefix is used only at strictly positive indices. -/
theorem measurable_lPlusPrefixPreviousStage (k : ℤ)
    {β : Type*} [MeasurableSpace β] (f : State → β) :
    Measurable (fun p : lPlusPrefixHitDomain k =>
      f (kmswStage p.val (lPlusPrefixHitIndex k p - 1))) := by
  have hstage (n : ℕ) : Measurable (fun p : ℕ → Fin 3 =>
      f (kmswStage p (n - 1))) :=
    measurable_of_factors_prefix (n - 1) _ (fun p p' hp =>
      congrArg f (kmswStage_congr hp))
  have hjoint : Measurable (fun z : ℕ × (ℕ → Fin 3) =>
      f (kmswStage z.2 (z.1 - 1))) :=
    measurable_from_prod_countable_right hstage
  exact hjoint.comp
    ((measurable_lPlusPrefixHitIndex k).prodMk measurable_subtype_coe)

section DiscreteCoordinates

local instance : MeasurableSpace (Option (List ℕ)) := ⊤
local instance : MeasurableSpace (Option (ℕ × Bool)) := ⊤

/-- Helper toward Lemma 5.5. The ordered prefix attachment list is
measurable on the full raw pair space, with absence exactly at infinite hits. -/
theorem measurable_lPlusCodingPair_prefixUpperLeftList (x : XDP) (k : ℤ) :
    Measurable (fun z : LPlusCodingPair x =>
      (lPlusStoppedPrefixStage k z.1.code.1).map
        (fun S => S.UL.dropLast.reverse)) :=
  (measurable_lPlusStoppedPrefixStage_map k (fun S => S.UL.dropLast.reverse)).comp
    (((measurable_lPlusSidePresentation_code x).fst).comp measurable_fst)

/-- Helper toward Lemma 5.5. Restricting the ordered finite attachment
list to the certified pair domain preserves measurability. -/
theorem measurable_lPlusCertifiedCodingPair_prefixUpperLeftList (x : XDP) (k : ℤ) :
    Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      (lPlusStoppedPrefixStage k z.val.1.code.1).map
        (fun S => S.UL.dropLast.reverse)) :=
  (measurable_lPlusCodingPair_prefixUpperLeftList x k).comp measurable_subtype_coe

/-- Helper toward Lemma 5.5. The decoded ordered attachment list agrees
with every aligned source witness at every nonnegative index. -/
theorem lPlusStoppedPrefixStage_upperLeftList_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k) :
    (lPlusStoppedPrefixStage k r.code.1).map (fun S => S.UL.dropLast.reverse) =
      some ((kmswStage (shiftedStream s.W 0)
        (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse) := by
  rw [← s.prefixCode_eq, lPlusStoppedPrefixStage_boundaryPrefixCode s.W s.h k hk]
  rfl

/-- Helper toward Lemma 5.5. A finite-stage rotation coordinate is absent
precisely when its input edge is not allocated at that stage. -/
@[expose] noncomputable def lPlusFiniteRotationOption (p : ℕ → Fin 3)
    (n : ℕ) (d : ℕ × Bool) : Option (ℕ × Bool) :=
  if d.1 < (kmswStage p n).nextEdge then some (finiteRotationEntry p n d) else none

/-- Helper toward Lemma 5.5. Finite-prefix agreement preserves both
allocation and each allocated finite rotation coordinate. -/
theorem lPlusFiniteRotationOption_of_prefix (p p' : ℕ → Fin 3) (n : ℕ)
    (hp : ∀ i < n, p i = p' i) (d : ℕ × Bool) :
    lPlusFiniteRotationOption p n d = lPlusFiniteRotationOption p' n d := by
  unfold lPlusFiniteRotationOption
  rw [kmswStage_congr hp, finiteRotationEntry_of_prefix p p' n hp d]

/-- Helper toward Lemma 5.5. The preceding-stage rotation entry is
measurable on the finite-hit prefix domain, retaining both endpoint bits. -/
theorem measurable_lPlusPrefixPreviousRotationOption (k : ℤ) (d : ℕ × Bool) :
    Measurable (fun p : lPlusPrefixHitDomain k =>
      lPlusFiniteRotationOption p.val (lPlusPrefixHitIndex k p - 1) d) := by
  have hm (n : ℕ) : Measurable (fun p : ℕ → Fin 3 =>
      lPlusFiniteRotationOption p (n - 1) d) :=
    measurable_of_factors_prefix (n - 1) _ (fun p p' hp =>
      lPlusFiniteRotationOption_of_prefix p p' (n - 1) hp d)
  have hjoint : Measurable (fun z : ℕ × (ℕ → Fin 3) =>
      lPlusFiniteRotationOption z.2 (z.1 - 1) d) :=
    measurable_from_prod_countable_right hm
  exact hjoint.comp
    ((measurable_lPlusPrefixHitIndex k).prodMk measurable_subtype_coe)

/-- Helper toward Lemma 5.5. The decoded preceding-stage rotation agrees
with the exact source finite-stage rotation on every allocated dart. -/
theorem lPlusPrefixPreviousRotationOption_boundaryPrefixCode
    (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0))
    (k : ℤ) (hk : 0 ≤ k) (d : ℕ × Bool)
    (hd : d.1 < (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k - 1)).nextEdge) :
    lPlusFiniteRotationOption (boundaryPrefixCode k W)
        (lPlusPrefixHitIndex k
          ⟨boundaryPrefixCode k W,
            boundaryPrefixCode_mem_lPlusPrefixHitDomain W h k hk⟩ - 1) d =
      some (finiteRotationEntry (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k - 1) d) := by
  rw [lPlusPrefixHitIndex_boundaryPrefixCode W h k hk,
    lPlusFiniteRotationOption_of_prefix (boundaryPrefixCode k W)
      (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k - 1)
      (fun i hi => lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W h k (by omega)) d]
  exact ite_eq_left hd

/-- Helper toward Lemma 5.5. The optional finite prefix rotation decoder
is absent at infinite hits and at unallocated input darts. -/
@[expose] noncomputable def lPlusStoppedPrefixRotationOption (k : ℤ)
    (p : ℕ → Fin 3) (d : ℕ × Bool) : Option (ℕ × Bool) :=
  if hp : p ∈ lPlusPrefixHitDomain k then
    lPlusFiniteRotationOption p (lPlusPrefixHitIndex k ⟨p, hp⟩ - 1) d
  else none

/-- Helper toward Lemma 5.5. Each stopped prefix rotation coordinate is
measurable on the entire raw prefix space. -/
theorem measurable_lPlusStoppedPrefixRotationOption (k : ℤ) (d : ℕ × Bool) :
    Measurable (fun p => lPlusStoppedPrefixRotationOption k p d) :=
  (measurable_lPlusPrefixPreviousRotationOption k d).dite measurable_const
    (measurableSet_lPlusPrefixHitDomain k)

/-- Helper toward Lemma 5.5. Each stopped prefix rotation coordinate is
measurable on raw presentation/path pairs. -/
theorem measurable_lPlusCodingPair_prefixRotationOption
    (x : XDP) (k : ℤ) (d : ℕ × Bool) :
    Measurable (fun z : LPlusCodingPair x =>
      lPlusStoppedPrefixRotationOption k z.1.code.1 d) :=
  (measurable_lPlusStoppedPrefixRotationOption k d).comp
    ((measurable_lPlusSidePresentation_code x).fst.comp measurable_fst)

/-- Helper toward Lemma 5.5. Each finite prefix rotation coordinate is
measurable on the certified pair domain. -/
theorem measurable_lPlusCertifiedCodingPair_prefixRotationOption
    (x : XDP) (k : ℤ) (d : ℕ × Bool) :
    Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      lPlusStoppedPrefixRotationOption k z.val.1.code.1 d) :=
  (measurable_lPlusCodingPair_prefixRotationOption x k d).comp measurable_subtype_coe

/-- Helper toward Lemma 5.5. The measurable optional rotation decoder
recovers the actual deleted-prefix block permutation on each of its darts,
at every strictly positive index. -/
theorem lPlusStoppedPrefixRotationOption_eq_prefixRotation_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 < k)
    (a : LPlusPrefixDart s.W s.h k) :
    lPlusStoppedPrefixRotationOption k r.code.1 a.val =
      some ((lPlusPrefixRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft
        (le_of_lt hk) a).val) := by
  have ha : a.val.1 < (kmswStage (shiftedStream s.W 0)
      (boundaryHitTime (shiftedStream s.W 0) s.h k - 1)).nextEdge :=
    (Set.ext_iff.mp (lPlusPrefixMinusEdges_eq_previousStage
      (W := s.W) (h := s.h) hk) a.val.1).mp a.property
  rw [← s.prefixCode_eq, lPlusStoppedPrefixRotationOption,
    dite_eq_left (boundaryPrefixCode_mem_lPlusPrefixHitDomain s.W s.h k (le_of_lt hk)),
    lPlusPrefixPreviousRotationOption_boundaryPrefixCode s.W s.h k (le_of_lt hk) a.val ha,
    lPlusPrefixRotation_apply s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft
      (le_of_lt hk) hk a]
  simp only [finiteRotationEntry, dite_eq_left ha]
  rfl

/-- Helper toward Lemma 5.5. An intrinsic prefix/primed edge attachment
matches equally indexed entries of the stopped upper boundary and an
allocated initial primed root/LL segment. All witnesses are countable. -/
@[expose] def lPlusPrefixPrimedEdgeAttachment (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (e b : ℕ) : Prop :=
  ∃ L : List ℕ,
    (lPlusStoppedPrefixStage k r.code.1).map (fun S => S.UL.dropLast.reverse) = some L ∧
    ∃ m : ℕ,
      L.length ≤ (0 :: (kmswStage r.code.2.2 m).LL.reverse).length ∧
      ∃ i : ℕ, L[i]? = some e ∧
        ((0 :: (kmswStage r.code.2.2 m).LL.reverse).take L.length)[i]? = some b

/-- Helper toward Lemma 5.5. Every intrinsic prefix/primed edge
attachment event is measurable on the raw pair space. -/
theorem measurableSet_lPlusCodingPair_prefixPrimedEdgeAttachment
    (x : XDP) (k : ℤ) (e b : ℕ) :
    MeasurableSet {z : LPlusCodingPair x |
      lPlusPrefixPrimedEdgeAttachment x k z.1 e b} := by
  have hprimed : Measurable (fun z : LPlusCodingPair x => z.1.code.2.2) :=
    (measurable_lPlusSidePresentation_code x).snd.snd.comp measurable_fst
  have hm (L : List ℕ) (m i : ℕ) :
      MeasurableSet {z : LPlusCodingPair x |
        L.length ≤ (0 :: (kmswStage z.1.code.2.2 m).LL.reverse).length ∧
        L[i]? = some e ∧
        ((0 :: (kmswStage z.1.code.2.2 m).LL.reverse).take L.length)[i]? = some b} := by
    have ht : MeasurableSet {p : ℕ → Fin 3 |
        L.length ≤ (0 :: (kmswStage p m).LL.reverse).length ∧
        L[i]? = some e ∧
        ((0 :: (kmswStage p m).LL.reverse).take L.length)[i]? = some b} := by
      apply measurableSet_of_factors_prefix m
      intro p p' hp
      rw [kmswStage_congr hp]
    exact ht.preimage hprimed
  have he (L : List ℕ) :
      {z : LPlusCodingPair x |
        ∃ m : ℕ,
          L.length ≤ (0 :: (kmswStage z.1.code.2.2 m).LL.reverse).length ∧
          ∃ i : ℕ, L[i]? = some e ∧
            ((0 :: (kmswStage z.1.code.2.2 m).LL.reverse).take L.length)[i]? = some b} =
        ⋃ m : ℕ, ⋃ i : ℕ, {z |
          L.length ≤ (0 :: (kmswStage z.1.code.2.2 m).LL.reverse).length ∧
          L[i]? = some e ∧
          ((0 :: (kmswStage z.1.code.2.2 m).LL.reverse).take L.length)[i]? = some b} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_and_left]
  unfold lPlusPrefixPrimedEdgeAttachment
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro L
  change MeasurableSet ({z : LPlusCodingPair x |
    (lPlusStoppedPrefixStage k z.1.code.1).map (fun S => S.UL.dropLast.reverse) = some L} ∩
    {z : LPlusCodingPair x | ∃ m : ℕ,
      L.length ≤ (0 :: (kmswStage z.1.code.2.2 m).LL.reverse).length ∧
      ∃ i : ℕ, L[i]? = some e ∧
        ((0 :: (kmswStage z.1.code.2.2 m).LL.reverse).take L.length)[i]? = some b})
  apply MeasurableSet.inter
  · exact ((measurable_lPlusCodingPair_prefixUpperLeftList x k).eq_const (some L)).setOf
  · rw [he L]
    exact MeasurableSet.iUnion (fun m => MeasurableSet.iUnion (fun i => hm L m i))

/-- Helper toward Lemma 5.5. The same prefix/primed attachment events
are measurable on the certified pair domain. -/
theorem measurableSet_lPlusCertifiedCodingPair_prefixPrimedEdgeAttachment
    (x : XDP) (k : ℤ) (e b : ℕ) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPrefixPrimedEdgeAttachment x k z.val.1 e b} :=
  (measurableSet_lPlusCodingPair_prefixPrimedEdgeAttachment x k e b).preimage
    measurable_subtype_coe

/-- Helper toward Lemma 5.5. On every aligned source witness, the
intrinsic measurable attachment event is exactly equality of the geometric
prefix edge with the embedded primed edge. Edge identity is retained. -/
theorem lPlusPrefixPrimedEdgeAttachment_iff_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (e b : ℕ) (he : e ∈ boundaryGluingPrefixMinusEdges s.W s.h k) :
    lPlusPrefixPrimedEdgeAttachment x k r e b ↔
      e = boundaryGluingPrimedEdgeMap s.W s.h k s.hτ b := by
  let L := (kmswStage (shiftedStream s.W 0)
    (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse
  let p := r.code.2.2
  let f := boundaryGluingPrimedEdgeMap s.W s.h k s.hτ
  have htail : (fun i => boundaryFutureCode k s.W (i + 1)) =
      boundaryGluingFutureStream s.W s.h k := boundaryFutureCode_tail s.W s.h k
  have hhit : HasFlowLineHits (fun i => boundaryFutureCode k s.W (i + 1)) :=
    htail.symm ▸ s.hτ
  have hcongr {u v : ℕ → Fin 3} (huv : u = v)
      (hu : HasFlowLineHits u) (hv : HasFlowLineHits v) :
      primedCode (primedSimInput u) hu = primedCode (primedSimInput v) hv := by
    cases huv
    rfl
  have hobs : hatLawPrimedCodes (boundaryFutureCode k s.W) =
      primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ := by
    unfold hatLawPrimedCodes
    rw [dite_eq_left hhit]
    exact hcongr htail hhit s.hτ
  have hcode : primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ = p :=
    hobs.symm.trans s.primedCode_eq
  obtain ⟨m₀, hm₀⟩ := lPlus_prefix_primed_ordered_dart_image s.hτ
  rw [hcode] at hm₀
  have hmap : ((0 :: (kmswStage p m₀).LL.reverse).take L.length).map f = L := by
    have hh := congrArg (List.map Prod.fst) hm₀
    simpa [lPlusPrefixUpperLeftDarts_eq, List.map_map,
      lMinusPrimedDartImage, Function.comp_def, L, f] using hh
  have hlen₀ : L.length ≤ (0 :: (kmswStage p m₀).LL.reverse).length := by
    have hh := congrArg List.length hmap
    simp only [List.length_map, List.length_take] at hh
    omega
  have hword (m : ℕ) (hm : L.length ≤ (0 :: (kmswStage p m).LL.reverse).length) :
      (0 :: (kmswStage p m).LL.reverse).take L.length =
        (0 :: (kmswStage p m₀).LL.reverse).take L.length :=
    (lPlus_primed_rootLL_take_eq_of_le p m (max m m₀) L.length
      (le_max_left _ _) hm).trans
      (lPlus_primed_rootLL_take_eq_of_le p m₀ (max m m₀) L.length
        (le_max_right _ _) hlen₀).symm
  have hdecoded := lPlusStoppedPrefixStage_upperLeftList_of_aligned x k r s hk
  change (lPlusStoppedPrefixStage k r.code.1).map _ = some L at hdecoded
  constructor
  · rintro ⟨L', hL', m, hm, i, hi, hb⟩
    have hLL : L' = L := Option.some.inj (hL'.symm.trans hdecoded)
    subst L'
    change ((0 :: (kmswStage p m).LL.reverse).take L.length)[i]? = some b at hb
    rw [hword m hm] at hb
    have hh := congrArg (fun l : List ℕ => l[i]?) hmap
    rw [List.getElem?_map, hb, Option.map_some, hi] at hh
    exact (Option.some.inj hh).symm
  · intro hab
    have hu : e ∈ boundaryGluingUpperLeftEdges s.W s.h k := by
      rw [← boundaryGluingPrefixMinusEdges_inter_primedEdges s.W s.h k s.hτ s.hfin hk]
      exact ⟨he, b, hab.symm⟩
    have heL : e ∈ L := List.mem_reverse.mpr hu
    rw [← hmap] at heL
    obtain ⟨c, hc, hce⟩ := List.mem_map.mp heL
    have hcb : c = b := boundaryGluingPrimedEdgeMap_injective s.W s.h k s.hτ
      (hce.trans hab)
    subst c
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
    refine ⟨L, hdecoded, m₀, hlen₀, i, ?_, hi⟩
    have hh := congrArg (fun l : List ℕ => l[i]?) hmap
    rw [List.getElem?_map, hi, Option.map_some, hce] at hh
    exact hh.symm

/-- Helper toward Lemma 5.5. The intrinsic dart attachment retains the
code-determined primed side flip as well as the shared geometric edge. -/
@[expose] noncomputable def lPlusPrefixPrimedDartAttachment (x : XDP) (k : ℤ)
    (r : LPlusSidePresentation x) (a b : ℕ × Bool) : Prop :=
  lPlusPrefixPrimedEdgeAttachment x k r a.1 b.1 ∧
    a.2 = (b.2 ^^ lMinusCodePrimedSideFlip
      (decodeLMinus x 0 (r.code.2.2, r.code.2.1)) b.1)

/-- Helper toward Lemma 5.5. The complete prefix/primed dart attachment
event is measurable on the raw pair space. -/
theorem measurableSet_lPlusCodingPair_prefixPrimedDartAttachment
    (x : XDP) (k : ℤ) (a b : ℕ × Bool) :
    MeasurableSet {z : LPlusCodingPair x |
      lPlusPrefixPrimedDartAttachment x k z.1 a b} := by
  have hc : Measurable (fun z : LPlusCodingPair x => z.1.code) :=
    (measurable_lPlusSidePresentation_code x).comp measurable_fst
  have hf := (measurable_lMinusCodePrimedSideFlip x b.1).comp
    ((measurable_decodeLMinus x 0).comp (hc.snd.snd.prodMk hc.snd.fst))
  have hb : Measurable (fun z : LPlusCodingPair x =>
      a.2 = (b.2 ^^ lMinusCodePrimedSideFlip
        (decodeLMinus x 0 (z.1.code.2.2, z.1.code.2.1)) b.1)) :=
    (measurable_of_finite (fun c : Bool => a.2 = (b.2 ^^ c))).comp hf
  exact (measurableSet_lPlusCodingPair_prefixPrimedEdgeAttachment x k a.1 b.1).inter
    (measurableSet_setOfPred.mpr hb)

/-- Helper toward Lemma 5.5. The complete prefix/primed dart attachment
event remains measurable on certified pairs. -/
theorem measurableSet_lPlusCertifiedCodingPair_prefixPrimedDartAttachment
    (x : XDP) (k : ℤ) (a b : ℕ × Bool) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPrefixPrimedDartAttachment x k z.val.1 a b} :=
  (measurableSet_lPlusCodingPair_prefixPrimedDartAttachment x k a b).preimage
    measurable_subtype_coe

/-- Helper toward Lemma 5.5. The measurable intrinsic dart attachment is
exactly the actual prefix/primed dart identification for every aligned source
witness, including the local endpoint correction. -/
theorem lPlusPrefixPrimedDartAttachment_iff_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a b : ℕ × Bool) (ha : a.1 ∈ boundaryGluingPrefixMinusEdges s.W s.h k) :
    lPlusPrefixPrimedDartAttachment x k r a b ↔
      a = (boundaryGluingPrimedEdgeMap s.W s.h k s.hτ b.1,
        b.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream s.W s.h k) s.hτ b.1) := by
  have hf := lMinusCodePrimedSideFlip_observation
    (longest := s.longest) s.hτ s.hfin b.1
  change decide (∃ i, lMinusPrimedBoundaryEdge
    (hatLawPrimedCodes (boundaryFutureCode k s.W)) i b.1) = _ at hf
  have hflip : lMinusCodePrimedSideFlip
      (decodeLMinus x 0 (r.code.2.2, r.code.2.1)) b.1 =
      primedLimitSideFlip (boundaryGluingFutureStream s.W s.h k) s.hτ b.1 := by
    change decide (∃ i, lMinusPrimedBoundaryEdge r.code.2.2 i b.1) = _
    rw [← s.primedCode_eq]
    exact hf
  rw [lPlusPrefixPrimedDartAttachment,
    lPlusPrefixPrimedEdgeAttachment_iff_of_aligned x k r s hk a.1 b.1 ha,
    hflip, Prod.ext_iff]

end DiscreteCoordinates

/-- Helper toward Lemma 5.5. Fixed raw edge labels in the prefix, primed,
and hatted blocks, before restricting the geometric carriers. -/
abbrev LPlusRawEdge := Sum ℕ (Sum ℕ ℕ)

/-- Helper toward Lemma 5.5. Raw generators use the measurable ordered
prefix attachment and the existing measurable primed/hatted generator. -/
@[expose] def lPlusRawEdgeGenerator (x : XDP) (k : ℤ) (z : LPlusCodingPair x) :
    LPlusRawEdge → LPlusRawEdge → Prop
  | .inl a, .inr (.inl b) => lPlusPrefixPrimedEdgeAttachment x k z.1 a b
  | .inr (.inl a), .inr (.inr b) => lMinusRawCodeEdgeGluing
      (decodeLMinus x 0 (z.1.code.2.2, z.1.code.2.1)) z.2 a b
  | _, _ => False

/-- Helper toward Lemma 5.5. Each fixed raw three-block edge generator
event is measurable, without a source-witness guard. -/
theorem measurableSet_lPlusRawEdgeGenerator (x : XDP) (k : ℤ) (a b : LPlusRawEdge) :
    MeasurableSet {z : LPlusCodingPair x | lPlusRawEdgeGenerator x k z a b} := by
  have hc : Measurable (fun z : LPlusCodingPair x => z.1.code) :=
    (measurable_lPlusSidePresentation_code x).comp measurable_fst
  have hfuture : Measurable (fun z : LPlusCodingPair x =>
      (decodeLMinus x 0 (z.1.code.2.2, z.1.code.2.1), z.2)) :=
    ((measurable_decodeLMinus x 0).comp (hc.snd.snd.prodMk hc.snd.fst)).prodMk
      measurable_snd
  rcases a with a | a <;> rcases b with b | b
  · exact MeasurableSet.empty
  · cases b with
    | inl b => exact measurableSet_lPlusCodingPair_prefixPrimedEdgeAttachment x k a b
    | inr b => exact MeasurableSet.empty
  · cases a <;> exact MeasurableSet.empty
  · cases a <;> cases b
    · exact MeasurableSet.empty
    · exact (measurableSet_lMinusRawCodeEdgeGluing x _ _).preimage hfuture
    · exact MeasurableSet.empty
    · exact MeasurableSet.empty

/-- Helper toward Lemma 5.5. A fixed finite chain of raw edge gluing
generators gives a measurable event. -/
theorem measurableSet_lPlusRawFiniteGluingChain (x : XDP) (k : ℤ)
    (a b : LPlusRawEdge) (l : List LPlusRawEdge) :
    MeasurableSet {z : LPlusCodingPair x |
      lMinusFiniteGluingChain (lPlusRawEdgeGenerator x k z) a l b} := by
  induction l generalizing a with
  | nil => exact MeasurableSet.const (a = b)
  | cons c l ih =>
    exact ((measurableSet_lPlusRawEdgeGenerator x k a c).union
      (measurableSet_lPlusRawEdgeGenerator x k c a)).inter (ih c)

/-- Helper toward Lemma 5.5. Raw three-block edge equivalence is
measurable by a countable union of finite-chain certificates. -/
theorem measurableSet_lPlusRawEdgeEqvGen (x : XDP) (k : ℤ) (a b : LPlusRawEdge) :
    MeasurableSet {z : LPlusCodingPair x |
      Relation.EqvGen (lPlusRawEdgeGenerator x k z) a b} := by
  have he : {z : LPlusCodingPair x |
      Relation.EqvGen (lPlusRawEdgeGenerator x k z) a b} =
      ⋃ l : List LPlusRawEdge,
        {z | lMinusFiniteGluingChain (lPlusRawEdgeGenerator x k z) a l b} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion,
      lMinusEqvGen_iff_exists_finiteGluingChain]
  rw [he]
  exact MeasurableSet.iUnion (measurableSet_lPlusRawFiniteGluingChain x k a b)

/-- Helper toward Lemma 5.5. Numeric raw edge tokens keep all three block
tags, without changing geometric edge identity. -/
@[expose] def lPlusRawEdgeToken : LPlusRawEdge → ℕ
  | .inl a => 3 * a
  | .inr (.inl a) => 3 * a + 1
  | .inr (.inr a) => 3 * a + 2

/-- Helper toward Lemma 5.5. A candidate token represents an edge in the
same raw gluing class as the specified edge. -/
@[expose] def lPlusRawEdgeClosureCandidate (x : XDP) (k : ℤ)
    (z : LPlusCodingPair x) (a : LPlusRawEdge) (n : ℕ) : Prop :=
  ∃ b : LPlusRawEdge, lPlusRawEdgeToken b = n ∧
    Relation.EqvGen (lPlusRawEdgeGenerator x k z) b a

/-- Helper toward Lemma 5.5. Every raw edge has its own candidate,
including isolated tokens that participate in no attachment. -/
theorem lPlusRawEdgeClosureCandidate_exists (x : XDP) (k : ℤ)
    (z : LPlusCodingPair x) (a : LPlusRawEdge) :
    ∃ n, lPlusRawEdgeClosureCandidate x k z a n :=
  ⟨lPlusRawEdgeToken a, a, rfl, Relation.EqvGen.refl a⟩

/-- Helper toward Lemma 5.5. Fixed raw-edge candidate events are
measurable countable unions of gluing-equivalence tests. -/
theorem measurableSet_lPlusRawEdgeClosureCandidate (x : XDP) (k : ℤ)
    (a : LPlusRawEdge) (n : ℕ) :
    MeasurableSet {z : LPlusCodingPair x | lPlusRawEdgeClosureCandidate x k z a n} := by
  unfold lPlusRawEdgeClosureCandidate
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun b =>
    (MeasurableSet.const (lPlusRawEdgeToken b = n)).inter
      (measurableSet_lPlusRawEdgeEqvGen x k b a))

/-- Helper toward Lemma 5.5. The least raw token of a three-block edge
gluing class; this is not yet a complete marked-side decoder. -/
@[expose] noncomputable def lPlusRawEdgeClosureId (x : XDP) (k : ℤ)
    (z : LPlusCodingPair x) (a : LPlusRawEdge) : ℕ :=
  Nat.find (lPlusRawEdgeClosureCandidate_exists x k z a)

/-- Helper toward Lemma 5.5. The minimal raw edge ID is measurable for
every fixed raw edge, by minimization of measurable candidate predicates. -/
theorem measurable_lPlusRawEdgeClosureId (x : XDP) (k : ℤ) (a : LPlusRawEdge) :
    Measurable (fun z : LPlusCodingPair x => lPlusRawEdgeClosureId x k z a) :=
  measurable_find (fun z => lPlusRawEdgeClosureCandidate_exists x k z a)
    (measurableSet_lPlusRawEdgeClosureCandidate x k a)

/-- Helper toward Lemma 5.5. Minimal raw edge IDs remain measurable on
the certified pair domain. -/
theorem measurable_lPlusCertifiedCodingPair_rawEdgeClosureId
    (x : XDP) (k : ℤ) (a : LPlusRawEdge) :
    Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      lPlusRawEdgeClosureId x k z.val a) :=
  (measurable_lPlusRawEdgeClosureId x k a).comp measurable_subtype_coe

/-- Helper toward Lemma 5.5. Raw token numbers distinguish all block
labels as well as every edge within a block. -/
theorem lPlusRawEdgeToken_injective : Function.Injective lPlusRawEdgeToken := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · have h : a = b := by simp only [lPlusRawEdgeToken] at hab; omega
    exact congrArg Sum.inl h
  · cases b <;> simp only [lPlusRawEdgeToken] at hab <;> omega
  · cases a <;> simp only [lPlusRawEdgeToken] at hab <;> omega
  · cases a <;> cases b <;> simp only [lPlusRawEdgeToken] at hab
    · have h : _ = _ := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3)
        (Nat.add_right_cancel hab)
      exact congrArg (fun n => Sum.inr (Sum.inl n)) h
    · omega
    · omega
    · have h : _ = _ := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3)
        (Nat.add_right_cancel hab)
      exact congrArg (fun n => Sum.inr (Sum.inr n)) h

/-- Helper toward Lemma 5.5. The minimal raw ID is represented by an
actual raw edge in the same generated equivalence class. -/
theorem lPlusRawEdgeClosureId_spec (x : XDP) (k : ℤ)
    (z : LPlusCodingPair x) (a : LPlusRawEdge) :
    lPlusRawEdgeClosureCandidate x k z a (lPlusRawEdgeClosureId x k z a) :=
  Nat.find_spec (lPlusRawEdgeClosureCandidate_exists x k z a)

/-- Helper toward Lemma 5.5. The selected ID is no larger than the token
of any representative in the raw edge gluing class. -/
theorem lPlusRawEdgeClosureId_le (x : XDP) (k : ℤ)
    (z : LPlusCodingPair x) (a b : LPlusRawEdge)
    (hab : Relation.EqvGen (lPlusRawEdgeGenerator x k z) b a) :
    lPlusRawEdgeClosureId x k z a ≤ lPlusRawEdgeToken b :=
  Nat.find_min' (lPlusRawEdgeClosureCandidate_exists x k z a) ⟨b, rfl, hab⟩

/-- Helper toward Lemma 5.5. Minimal raw IDs agree precisely for edges
in the same generated gluing class. This characterizes the raw IDs without
claiming a complete geometric-side realization. -/
theorem lPlusRawEdgeClosureId_eq_iff (x : XDP) (k : ℤ)
    (z : LPlusCodingPair x) (a b : LPlusRawEdge) :
    lPlusRawEdgeClosureId x k z a = lPlusRawEdgeClosureId x k z b ↔
      Relation.EqvGen (lPlusRawEdgeGenerator x k z) a b := by
  constructor
  · intro hab
    obtain ⟨c, hc, hca⟩ := lPlusRawEdgeClosureId_spec x k z a
    obtain ⟨d, hd, hdb⟩ := lPlusRawEdgeClosureId_spec x k z b
    have hcd : c = d := lPlusRawEdgeToken_injective (hc.trans (hab.trans hd.symm))
    subst d
    exact Relation.EqvGen.trans a c b hca.symm hdb
  · intro hab
    apply Nat.find_congr'
    intro n
    constructor
    · rintro ⟨c, hc, hca⟩
      exact ⟨c, hc, Relation.EqvGen.trans c a b hca hab⟩
    · rintro ⟨c, hc, hcb⟩
      exact ⟨c, hc, Relation.EqvGen.trans c b a hcb hab.symm⟩

end DirectedDistances.PaperProofs.Section5



































































































































































/- 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0.
The temporary axiom-probe compile exited 0. All 34 new theorems were checked:
lPlusRawEdgeToken_injective uses [propext, Quot.sound]; the other 33 use
[propext, Classical.choice, Quot.sound]. No custom axiom or placeholder
appeared in these transitive axiom lists. The temporary commands were
was used, with one compile running at a time. The sole import is the
prescribed GeoInftyLPlusPairMeasurable2. No other file was edited. -/
