/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable12
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusActualSideIso10

/-! # Intrinsic attachment comparisons for the nonnegative left presentation

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. The primed preimage of each shared boundary
edge is determined by the primed code, rather than by its ambient edge ID. -/
theorem lPlusSourceWitnessAligned_primedBetaIndex_eq_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) (i : ℕ) :
    primedBeta0EdgeIndex (boundaryGluingFutureStream s.W s.h k) s.hτ s.hfin
        (hatBoundaryHitWitnesses _ s.hτ) s.hfin i =
      primedBeta0EdgeIndex (boundaryGluingFutureStream s'.W s'.h k) s'.hτ s'.hfin
        (hatBoundaryHitWitnesses _ s'.hτ) s'.hfin i := by
  have hc := lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq
    x k r r' s s' hr
  have hboundary (t : LPlusSourceWitnessAligned x k r) :
      lMinusPrimedBoundaryEdge
        (primedCode (primedSimInput (boundaryGluingFutureStream t.W t.h k)) t.hτ) i
        (primedBeta0EdgeIndex (boundaryGluingFutureStream t.W t.h k) t.hτ t.hfin
          (hatBoundaryHitWitnesses _ t.hτ) t.hfin i) := by
    exact ⟨primedIntervalBase (primedSimInput (boundaryGluingFutureStream t.W t.h k))
      t.hτ i + 1, fun n hn => primedBeta0EdgeIndex_UR_reverse_order _ t.hτ t.hfin
        (hatBoundaryHitWitnesses _ t.hτ) t.hfin i n hn⟩
  have hs := hboundary s
  have hs' : lMinusPrimedBoundaryEdge
      (primedCode (primedSimInput (boundaryGluingFutureStream s'.W s'.h k)) s'.hτ) i
      (primedBeta0EdgeIndex (boundaryGluingFutureStream s'.W s'.h k) s'.hτ s'.hfin
        (hatBoundaryHitWitnesses _ s'.hτ) s'.hfin i) := by
    exact ⟨primedIntervalBase (primedSimInput (boundaryGluingFutureStream s'.W s'.h k))
      s'.hτ i + 1, fun n hn => primedBeta0EdgeIndex_UR_reverse_order _ s'.hτ s'.hfin
        (hatBoundaryHitWitnesses _ s'.hτ) s'.hfin i n hn⟩
  rw [hc] at hs
  exact lMinusPrimedBoundaryEdge_unique _ i _ _ hs hs'

/-- Helper toward Lemma 5.5. The primed dart correction is code determined
on every edge, including missing geometric edges. -/
theorem lPlusSourceWitnessAligned_primedSideFlip_eq_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) (e : ℕ) :
    primedLimitSideFlip (boundaryGluingFutureStream s.W s.h k) s.hτ e =
      primedLimitSideFlip (boundaryGluingFutureStream s'.W s'.h k) s'.hτ e := by
  have hc := (lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq x k r r'
    s.toLPlusSidePresentationSourceWitness s'.toLPlusSidePresentationSourceWitness hr).2.2
  rw [← lMinusCodePrimedSideFlip_observation (longest := s.longest) s.hτ s.hfin,
    ← lMinusCodePrimedSideFlip_observation (longest := s'.longest) s'.hτ s'.hfin]
  change decide (∃ i, lMinusPrimedBoundaryEdge
      (hatLawPrimedCodes (boundaryFutureCode k s.W)) i e) =
    decide (∃ i, lMinusPrimedBoundaryEdge
      (hatLawPrimedCodes (boundaryFutureCode k s'.W)) i e)
  rw [hc]

/-- Helper toward Lemma 5.5. A mixed primed/hatted dart equality is exactly
one indexed boundary attachment, with the prescribed reversed primed bit. -/
theorem lPlus_primed_hatted_dart_eq_iff_boundary
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (a b : ℕ × Bool) :
    (boundaryGluingPrimedEdgeMap W h k hτ a.1,
        a.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ a.1) =
      (boundaryGluingHatEdgeMap W h k hτ b.1, b.2) ↔
    ∃ i, a.1 = primedBeta0EdgeIndex (boundaryGluingFutureStream W h k) hτ hfin
        (hatBoundaryHitWitnesses _ hτ) hfin i ∧
      b = (kmswLeftBoundaryEdge (hatCodes (boundaryGluingFutureStream W h k) hτ) i,
        !a.2) := by
  constructor
  · intro hab
    obtain ⟨i, hi, hb⟩ := (lMinus_cross_edge_eq_iff hτ hfin a.1 b.1).mp
      (congrArg Prod.fst hab)
    refine ⟨i, hi, Prod.ext hb ?_⟩
    have hbit := congrArg Prod.snd hab
    rw [hi, lMinusPrimedLimitSideFlip_beta hτ hfin] at hbit
    simpa only [Bool.xor_true] using hbit.symm
  · rintro ⟨i, hi, hb⟩
    apply Prod.ext
    · exact (lMinus_cross_edge_eq_iff hτ hfin a.1 b.1).mpr
        ⟨i, hi, congrArg Prod.fst hb⟩
    · change (a.2 ^^ primedLimitSideFlip _ hτ a.1) = b.2
      rw [hi, lMinusPrimedLimitSideFlip_beta hτ hfin, hb, Bool.xor_true]

/-- Helper toward Lemma 5.5. A hatted marked isomorphism preserves either
dart bit at each indexed exterior boundary edge. -/
theorem lPlusSourceWitnessAligned_markedIso_boundaryBit
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (phi : GeometricSideMarkedIso
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)
      (lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode))
    (i : ℕ) (b : Bool) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode
    phi.equiv (.inr ⟨((M.boundary i).1, b),
        lPlusSourceWitnessAligned_hattedBoundary_mem x k r s i⟩) =
      .inr ⟨((M'.boundary i).1, b),
        lPlusSourceWitnessAligned_hattedBoundary_mem x k r' s' i⟩ := by
  cases b
  · exact lPlusMarkedIso_boundaryDart phi i
      (lPlusSourceWitnessAligned_hattedBoundary_mem x k r s i)
      (lPlusSourceWitnessAligned_hattedBoundary_mem x k r' s' i)
  · exact lPlusMarkedIso_oppositeBoundaryDart phi i
      (lPlusSourceWitnessAligned_hattedBoundary_mem x k r s i)
      (lPlusSourceWitnessAligned_hattedBoundary_mem x k r' s' i)

/-- Helper toward Lemma 5.5. Under a hatted marked isomorphism, the
primed/hatted mixed dart kernel is preserved by the identity on primed IDs.
No equality between the two ambient embeddings is required. -/
theorem lPlusSourceWitnessAligned_primedHattedDartKernel_transport
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode
    ∀ (phi : GeometricSideMarkedIso M M') (a : LPlusPrimedDart)
      (b : LPlusHattedDart M) (b' : LPlusHattedDart M'),
      phi.equiv (.inr b) = .inr b' →
      (lPlusBlockDartImage (M := M) s.hτ (.inr (.inl a)) =
        lPlusBlockDartImage (M := M) s.hτ (.inr (.inr b)) ↔
      lPlusBlockDartImage (M := M') s'.hτ (.inr (.inl a)) =
        lPlusBlockDartImage (M := M') s'.hτ (.inr (.inr b'))) := by
  dsimp only
  intro phi a b b' hphi
  rw [show lPlusBlockDartImage s.hτ (.inr (.inl a)) =
      (boundaryGluingPrimedEdgeMap s.W s.h k s.hτ a.1,
        a.2 ^^ primedLimitSideFlip _ s.hτ a.1) from rfl]
  change (_, _) = (_, _) ↔ (_, _) = (_, _)
  rw [lPlus_primed_hatted_dart_eq_iff_boundary s.hτ s.hfin,
    lPlus_primed_hatted_dart_eq_iff_boundary s'.hτ s'.hfin]
  have hB := lPlusSourceWitnessAligned_primedBetaIndex_eq_of_presentation_codes_eq
    x k r r' s s' hr
  have hb (i : ℕ) :
      b.val = (kmswLeftBoundaryEdge (hatCodes (boundaryGluingFutureStream s.W s.h k)
          s.hτ) i, !a.2) ↔
      b'.val = (kmswLeftBoundaryEdge (hatCodes (boundaryGluingFutureStream s'.W s'.h k)
          s'.hτ) i, !a.2) := by
    rw [← lMinus_hatted_boundary s.hτ s.hqMode i,
      ← lMinus_hatted_boundary s'.hτ s'.hqMode i]
    let d : LPlusHattedDart (lPlusHattedSide (W := s.W) (h := s.h) (k := k)
        s.longest s.hqMode) :=
      ⟨(_, !a.2), lPlusSourceWitnessAligned_hattedBoundary_mem x k r s i⟩
    let d' : LPlusHattedDart (lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
        s'.longest s'.hqMode) :=
      ⟨(_, !a.2), lPlusSourceWitnessAligned_hattedBoundary_mem x k r' s' i⟩
    have hd : phi.equiv (.inr d) = .inr d' :=
      lPlusSourceWitnessAligned_markedIso_boundaryBit x k r r' s s' phi i (!a.2)
    constructor
    · intro h
      have he : b = d := Subtype.ext h
      exact congrArg Subtype.val (Sum.inr.inj (hphi.symm.trans ((congrArg
        phi.equiv (congrArg Sum.inr he)).trans hd)))
    · intro h
      have he : b' = d' := Subtype.ext h
      have hh : phi.equiv (.inr b) = phi.equiv (.inr d) :=
        hphi.trans ((congrArg Sum.inr he).trans hd.symm)
      exact congrArg Subtype.val (Sum.inr.inj (phi.equiv.injective hh))
  constructor
  · rintro ⟨i, hi, hbi⟩
    exact ⟨i, hi.trans (hB i), (hb i).mp hbi⟩
  · rintro ⟨i, hi, hbi⟩
    exact ⟨i, hi.trans (hB i).symm, (hb i).mpr hbi⟩

/-- Helper toward Lemma 5.5. Equal codes admit representative transports
preserving the entire primed/hatted mixed dart kernel simultaneously. -/
theorem lPlusSourceWitnessAligned_primedHattedDartCrossKernel_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode
    ∃ (phi : GeometricSideMarkedIso M M')
      (_fV : LPlusBlockVertex s.W s.h k M ≃ LPlusBlockVertex s'.W s'.h k M')
      (fD : LPlusBlockDart s.W s.h k M ≃ LPlusBlockDart s'.W s'.h k M'),
      (∀ a : LPlusPrimedDart, fD (.inr (.inl a)) = .inr (.inl a)) ∧
      (∀ b : LPlusHattedDart M, ∃ b' : LPlusHattedDart M',
        fD (.inr (.inr b)) = .inr (.inr b') ∧ phi.equiv (.inr b) = .inr b') ∧
      (∀ a : LPlusPrimedDart, ∀ b : LPlusHattedDart M,
        lPlusBlockDartImage (M := M) s.hτ (.inr (.inl a)) =
          lPlusBlockDartImage (M := M) s.hτ (.inr (.inr b)) ↔
        lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inl a))) =
          lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inr b)))) := by
  obtain ⟨phi, fV, fD, _, _, _, _, hprimed, hhatted⟩ :=
    lPlusSourceWitnessAligned_representativeEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  refine ⟨phi, fV, fD, hprimed, hhatted, ?_⟩
  intro a b
  obtain ⟨b', hb', hphi⟩ := hhatted b
  rw [hprimed a, hb']
  exact lPlusSourceWitnessAligned_primedHattedDartKernel_transport
    x k r r' s s' hr phi a b b' hphi

/-- Helper toward Lemma 5.5. Later local stages extend the reversed
lower-left stack at its end, preserving the order of earlier edge IDs. -/
private theorem lPlus_LL_reverse_prefix (p : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    (kmswStage p m).LL.reverse <+: (kmswStage p n).LL.reverse := by
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨[], List.append_nil _⟩
  | succ n _ ih =>
    apply ih.trans
    change (kmswStage p n).LL.reverse <+: (kmswStep (kmswStage p n) (p n)).LL.reverse
    unfold kmswStep
    cases hc : kmswCodeStep (p n) with
    | up => simp [kmswStepOfStep, State.addEdge]
    | down => cases hs : (kmswStage p n).UR <;>
        simp [kmswStepOfStep, hs, State.addEdge]
    | left => cases hs : (kmswStage p n).UL.dropLast.reverse <;>
        simp [kmswStepOfStep, hs, State.addEdge]

/-- Helper toward Lemma 5.5. Every already allocated initial root/LL
segment is independent of the stage at which it is read. -/
theorem lPlus_primed_rootLL_take_eq_of_le (p : ℕ → Fin 3) (m n len : ℕ)
    (hmn : m ≤ n) (hlen : len ≤ (0 :: (kmswStage p m).LL.reverse).length) :
    (0 :: (kmswStage p m).LL.reverse).take len =
      (0 :: (kmswStage p n).LL.reverse).take len := by
  obtain ⟨tail, ht⟩ := lPlus_LL_reverse_prefix p hmn
  rw [← ht, ← List.cons_append, List.take_append,
    Nat.sub_eq_zero_of_le hlen, List.take_zero, List.append_nil]

/-- Helper toward Lemma 5.5. Equal stopped-prefix codes determine the
whole stopped stage, including its ordered attachment stack. -/
theorem lPlusBoundaryHitStage_eq_of_code_eq
    (W W' : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (h' : BoundaryHitWitnesses (shiftedStream W' 0)) (k : ℤ)
    (hc : boundaryPrefixCode k W = boundaryPrefixCode k W') :
    kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k) =
      kmswStage (shiftedStream W' 0) (boundaryHitTime (shiftedStream W' 0) h' k) := by
  have ht := lPlusBoundaryHitTime_eq_of_boundaryPrefixCode_eq W W' h h' k hc
  rw [ht]
  apply kmswStage_congr
  intro i hi
  have hi' : i < boundaryHitTime (shiftedStream W 0) h k := by omega
  exact (lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W h k hi').symm.trans
    ((congrFun hc i).trans (lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W' h' k hi))

/-- Helper toward Lemma 5.5. Both witnesses attach the same ordered
primed local word to the same stopped-prefix dart word. The stage is enlarged
to a common stage of the equal primed codes. -/
theorem lPlusSourceWitnessAligned_orderedPrefixPrimedWord_common
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) :
    ∃ q : List (ℕ × Bool),
      q.map (lMinusPrimedDartImage s.hτ) =
        lPlusPrefixUpperLeftDarts (W := s.W) (h := s.h) (k := k) ∧
      q.map (lMinusPrimedDartImage s'.hτ) =
        lPlusPrefixUpperLeftDarts (W := s.W) (h := s.h) (k := k) := by
  have hc := (lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq x k r r'
    s.toLPlusSidePresentationSourceWitness s'.toLPlusSidePresentationSourceWitness hr).1
  have hstage := lPlusBoundaryHitStage_eq_of_code_eq s.W s'.W s.h s'.h k hc
  have hp : lPlusPrefixUpperLeftDarts (W := s.W) (h := s.h) (k := k) =
      lPlusPrefixUpperLeftDarts (W := s'.W) (h := s'.h) (k := k) := by
    rw [lPlusPrefixUpperLeftDarts_eq, lPlusPrefixUpperLeftDarts_eq, hstage]
  have hcode := lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq
    x k r r' s s' hr
  obtain ⟨m, hm⟩ := lPlus_prefix_primed_ordered_dart_image s.hτ
  obtain ⟨n, hn⟩ := lPlus_prefix_primed_ordered_dart_image s'.hτ
  have hmLen := congrArg List.length hm
  have hnLen := congrArg List.length hn
  simp only [List.length_map, List.length_take] at hmLen hnLen
  have hmTake := lPlus_primed_rootLL_take_eq_of_le
    (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ)
      m (max m n) (lPlusPrefixUpperLeftDarts (W := s.W) (h := s.h) (k := k)).length
      (Nat.le_max_left _ _) (by omega)
  have hnTake := lPlus_primed_rootLL_take_eq_of_le
    (primedCode (primedSimInput (boundaryGluingFutureStream s'.W s'.h k)) s'.hτ)
      n (max m n) (lPlusPrefixUpperLeftDarts (W := s'.W) (h := s'.h) (k := k)).length
      (Nat.le_max_right _ _) (by omega)
  rw [hmTake] at hm
  rw [hnTake] at hn
  rw [← hcode, ← hp] at hn
  exact ⟨_, hm, hn⟩

/-- Helper toward Lemma 5.5. The prefix/primed edge identification is
code determined. Only edge IDs on the stopped prefix are compared; ambient
IDs away from the attachment need not agree. -/
theorem lPlusSourceWitnessAligned_prefixPrimedEdgeKernel_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code)
    (e b : ℕ) (he : e ∈ boundaryGluingPrefixMinusEdges s.W s.h k) :
    e = boundaryGluingPrimedEdgeMap s.W s.h k s.hτ b ↔
      e = boundaryGluingPrimedEdgeMap s'.W s'.h k s'.hτ b := by
  obtain ⟨q, hq, hq'⟩ :=
    lPlusSourceWitnessAligned_orderedPrefixPrimedWord_common x k r r' s s' hr
  have hc := (lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq x k r r'
    s.toLPlusSidePresentationSourceWitness s'.toLPlusSidePresentationSourceWitness hr).1
  have hstage := lPlusBoundaryHitStage_eq_of_code_eq s.W s'.W s.h s'.h k hc
  have he' : e ∈ boundaryGluingPrefixMinusEdges s'.W s'.h k := by
    rw [← lPlusSourceWitnessAligned_prefixEdges_eq_of_presentation_codes_eq
      x k r r' s s' hk hr]
    exact he
  have hupper : boundaryGluingUpperLeftEdges s.W s.h k =
      boundaryGluingUpperLeftEdges s'.W s'.h k := by
    unfold boundaryGluingUpperLeftEdges
    rw [hstage]
  have hmem (hu : e ∈ boundaryGluingUpperLeftEdges s.W s.h k) :
      (e, true) ∈ lPlusPrefixUpperLeftDarts (W := s.W) (h := s.h) (k := k) := by
    rw [lPlusPrefixUpperLeftDarts_eq]
    exact List.mem_map.mpr ⟨e, List.mem_reverse.mpr hu, rfl⟩
  constructor
  · intro hab
    have hu : e ∈ boundaryGluingUpperLeftEdges s.W s.h k := by
      rw [← boundaryGluingPrefixMinusEdges_inter_primedEdges s.W s.h k s.hτ s.hfin hk]
      exact ⟨he, b, hab.symm⟩
    have hqmem := hmem hu
    rw [← hq] at hqmem
    obtain ⟨c, hcq, hcmap⟩ := List.mem_map.mp hqmem
    have hcb : c.1 = b := boundaryGluingPrimedEdgeMap_injective s.W s.h k s.hτ
      ((congrArg Prod.fst hcmap).trans hab)
    have heqmaps : lMinusPrimedDartImage s'.hτ c = (e, true) := by
      have hget := hq.trans hq'.symm
      obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hcq
      have hpos := congrArg (fun ds : List (ℕ × Bool) => ds[i]?) hget
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi, hci,
        Option.map_some] at hpos
      exact (Option.some.inj hpos).symm.trans hcmap
    have hresult := congrArg Prod.fst heqmaps
    change boundaryGluingPrimedEdgeMap s'.W s'.h k s'.hτ c.1 = e at hresult
    rw [hcb] at hresult
    exact hresult.symm
  · intro hab
    have hu' : e ∈ boundaryGluingUpperLeftEdges s'.W s'.h k := by
      rw [← boundaryGluingPrefixMinusEdges_inter_primedEdges s'.W s'.h k s'.hτ s'.hfin hk]
      exact ⟨he', b, hab.symm⟩
    have hqmem := hmem (hupper.symm ▸ hu')
    rw [← hq'] at hqmem
    obtain ⟨c, hcq, hcmap⟩ := List.mem_map.mp hqmem
    have hcb : c.1 = b := boundaryGluingPrimedEdgeMap_injective s'.W s'.h k s'.hτ
      ((congrArg Prod.fst hcmap).trans hab)
    obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hcq
    have hpos := congrArg (fun ds : List (ℕ × Bool) => ds[i]?) (hq.trans hq'.symm)
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, hci,
      Option.map_some] at hpos
    have hresult := congrArg Prod.fst ((Option.some.inj hpos).trans hcmap)
    change boundaryGluingPrimedEdgeMap s.W s.h k s.hτ c.1 = e at hresult
    rw [hcb] at hresult
    exact hresult.symm

/-- Helper toward Lemma 5.5. Prefix/primed dart equality is preserved on
the common prefix carrier and the identical local primed dart indices. -/
theorem lPlusSourceWitnessAligned_prefixPrimedDartKernel_transport
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code)
    (a : LPlusPrefixDart s.W s.h k) (a' : LPlusPrefixDart s'.W s'.h k)
    (ha : a'.val = a.val) (b : LPlusPrimedDart) :
    (a.val.1, a.val.2) = (boundaryGluingPrimedEdgeMap s.W s.h k s.hτ b.1,
        b.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream s.W s.h k) s.hτ b.1) ↔
      (a'.val.1, a'.val.2) = (boundaryGluingPrimedEdgeMap s'.W s'.h k s'.hτ b.1,
        b.2 ^^ primedLimitSideFlip (boundaryGluingFutureStream s'.W s'.h k) s'.hτ b.1) := by
  rw [ha, Prod.mk.injEq, Prod.mk.injEq,
    lPlusSourceWitnessAligned_prefixPrimedEdgeKernel_iff x k r r' s s' hk hr
      a.val.1 b.1 a.property,
    lPlusSourceWitnessAligned_primedSideFlip_eq_of_presentation_codes_eq
      x k r r' s s' hr b.1]

/-- Helper toward Lemma 5.5. The indexed beta attachment identifies the
corresponding local endpoints, with the primed dart bit reversed. -/
theorem lPlus_beta_vertex_attachment
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (i : ℕ) (b : Bool) :
    boundaryGluingPrimedVertexMap W h k hτ
        (kmswLimitDartVertex (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ)
          (primedBeta0EdgeIndex (boundaryGluingFutureStream W h k) hτ hfin
            (hatBoundaryHitWitnesses _ hτ) hfin i, !b)) =
      boundaryGluingHatVertexMap W h k hτ
        (kmswLimitDartVertex (hatCodes (boundaryGluingFutureStream W h k) hτ)
          (kmswLeftBoundaryEdge (hatCodes (boundaryGluingFutureStream W h k) hτ) i, b)) := by
  rw [← lMinusPrimedDartImage_endpoint hτ,
    lMinusPrimedDartImage_boundary hτ hfin i (!b), Bool.not_not]
  cases b
  · exact (boundaryGluing_hat_edge_endpoints W h k hτ _).1
  · exact (boundaryGluing_hat_edge_endpoints W h k hτ _).2

/-- Helper toward Lemma 5.5. The primed/hatted vertex kernel is determined
by the initial vertex and the local indexed beta endpoints. -/
theorem lPlus_primed_hatted_vertex_eq_iff_boundary
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) (a b : ℕ) :
    boundaryGluingPrimedVertexMap W h k hτ a =
      boundaryGluingHatVertexMap W h k hτ b ↔
    (a = 1 ∧ b = 0) ∨ ∃ i,
      a = kmswLimitDartVertex (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ)
        (primedBeta0EdgeIndex (boundaryGluingFutureStream W h k) hτ hfin
          (hatBoundaryHitWitnesses _ hτ) hfin i, false) ∧
      b = edgeEast (hatCodes (boundaryGluingFutureStream W h k) hτ)
        (kmswLeftBoundaryEdge (hatCodes (boundaryGluingFutureStream W h k) hτ) i) := by
  let u := boundaryGluingFutureStream W h k
  let p := primedCode (primedSimInput u) hτ
  have hinjP : Function.Injective (boundaryGluingPrimedVertexMap W h k hτ) :=
    lPlusPrimedVertexImage_injective hτ hqMode
  have hinjH := boundaryGluingHatVertexMap_injective W h k hτ
  have hroot : boundaryGluingPrimedVertexMap W h k hτ 1 =
      boundaryGluingHatVertexMap W h k hτ 0 := by
    rw [boundaryGluingHatVertexMap_zero]
    exact lPlus_primed_root_starts_at_xk hτ
  constructor
  · intro hab
    obtain ⟨e, he⟩ := geoInfty_vertex_endpoint p a
    obtain ⟨f, hf⟩ := geoInfty_vertex_endpoint (hatCodes u hτ) b
    have hp : ∃ d : ℕ × Bool, kmswLimitDartVertex p d = a := by
      rcases he with he | he
      · exact ⟨(e, false), he⟩
      · exact ⟨(e, true), he⟩
    have hh : ∃ d : ℕ × Bool, kmswLimitDartVertex (hatCodes u hτ) d = b := by
      rcases hf with hf | hf
      · exact ⟨(f, false), hf⟩
      · exact ⟨(f, true), hf⟩
    obtain ⟨pd, hpd⟩ := hp
    obtain ⟨hd, hhd⟩ := hh
    have hendH (d : ℕ × Bool) :
        kmswLimitDartVertex (shiftedStream W 0)
          (boundaryGluingHatEdgeMap W h k hτ d.1, d.2) =
        boundaryGluingHatVertexMap W h k hτ (kmswLimitDartVertex (hatCodes u hτ) d) := by
      cases d with | mk e c =>
        cases c
        · exact (boundaryGluing_hat_edge_endpoints W h k hτ e).1
        · exact (boundaryGluing_hat_edge_endpoints W h k hτ e).2
    have hv : kmswLimitDartVertex (shiftedStream W 0) (lMinusPrimedDartImage hτ pd) =
        kmswLimitDartVertex (shiftedStream W 0)
          (boundaryGluingHatEdgeMap W h k hτ hd.1, hd.2) := by
      rw [lMinusPrimedDartImage_endpoint hτ, hendH, hpd, hhd]
      exact hab
    obtain hz | ⟨i, hi⟩ := lMinus_shared_dart_endpoint_interface hτ hfin pd hd hv
    · rw [lMinusPrimedDartImage_endpoint hτ, hpd] at hz
      exact Or.inl ⟨hinjP (hz.trans hroot.symm), hinjH (hab.symm.trans hz)⟩
    · rw [lMinusPrimedDartImage_endpoint hτ, hpd,
        hendH (kmswLeftBoundaryEdge (hatCodes u hτ) i, true)] at hi
      refine Or.inr ⟨i, ?_, hinjH (hab.symm.trans hi)⟩
      apply hinjP
      exact hi.trans (lPlus_beta_vertex_attachment hτ hfin i true).symm
  · rintro (⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩)
    · exact hroot
    · exact lPlus_beta_vertex_attachment hτ hfin i true

/-- Helper toward Lemma 5.5. A marked hatted isomorphism preserves the
endpoint selected by either bit of each exterior boundary edge. -/
theorem lPlusSourceWitnessAligned_markedIso_boundaryEndpoint_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r') :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode
    ∀ (phi : GeometricSideMarkedIso M M')
      (v : LPlusHattedVertex M) (v' : LPlusHattedVertex M'),
      phi.equiv (.inl v) = .inl v' → ∀ (i : ℕ) (b : Bool),
      (if b then M.east (M.boundary i).1 else M.west (M.boundary i).1) = v.val ↔
      (if b then M'.east (M'.boundary i).1 else M'.west (M'.boundary i).1) = v'.val := by
  dsimp only
  intro phi v v' hv i b
  have hd := lPlusSourceWitnessAligned_markedIso_boundaryBit x k r r' s s' phi i b
  have hi := phi.relation_iff .incident
    (.inr ⟨(_, b), lPlusSourceWitnessAligned_hattedBoundary_mem x k r s i⟩) (.inl v)
  rw [hd, hv] at hi
  exact hi

/-- Helper toward Lemma 5.5. The primed/hatted vertex kernel is preserved
by the identity on primed local IDs and the marked hatted transport. -/
theorem lPlusSourceWitnessAligned_primedHattedVertexKernel_transport
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode
    ∀ (phi : GeometricSideMarkedIso M M') (a : ℕ)
      (b : LPlusHattedVertex M) (b' : LPlusHattedVertex M'),
      phi.equiv (.inl b) = .inl b' →
      (boundaryGluingPrimedVertexMap s.W s.h k s.hτ a =
          boundaryGluingHatVertexMap s.W s.h k s.hτ b.val ↔
        boundaryGluingPrimedVertexMap s'.W s'.h k s'.hτ a =
          boundaryGluingHatVertexMap s'.W s'.h k s'.hτ b'.val) := by
  dsimp only
  intro phi a b b' hb
  rw [lPlus_primed_hatted_vertex_eq_iff_boundary s.hτ s.hqMode s.hfin,
    lPlus_primed_hatted_vertex_eq_iff_boundary s'.hτ s'.hqMode s'.hfin]
  have hroot : b.val = 0 ↔ b'.val = 0 := by
    have hh := phi.relation_iff .root (.inl b) (.inl b)
    rw [hb] at hh
    exact hh
  have heast (i : ℕ) :
      b.val = edgeEast (hatCodes (boundaryGluingFutureStream s.W s.h k) s.hτ)
        (kmswLeftBoundaryEdge (hatCodes (boundaryGluingFutureStream s.W s.h k) s.hτ) i) ↔
      b'.val = edgeEast (hatCodes (boundaryGluingFutureStream s'.W s'.h k) s'.hτ)
        (kmswLeftBoundaryEdge (hatCodes (boundaryGluingFutureStream s'.W s'.h k) s'.hτ) i) := by
    have hh := lPlusSourceWitnessAligned_markedIso_boundaryEndpoint_iff
      x k r r' s s' phi b b' hb i true
    change edgeEast (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s.W)))
        (kmswLeftBoundaryEdge
          (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s.W))) i) = b.val ↔
      edgeEast (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s'.W)))
        (kmswLeftBoundaryEdge
          (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s'.W))) i) = b'.val at hh
    rw [boundaryGluing_decoded_stream s.W s.h k s.hτ,
      boundaryGluing_decoded_stream s'.W s'.h k s'.hτ] at hh
    exact (eq_comm.trans hh).trans eq_comm
  have hcode := lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq
    x k r r' s s' hr
  have hB := lPlusSourceWitnessAligned_primedBetaIndex_eq_of_presentation_codes_eq
    x k r r' s s' hr
  constructor
  · rintro (⟨ha, hb0⟩ | ⟨i, ha, hbi⟩)
    · exact Or.inl ⟨ha, hroot.mp hb0⟩
    · exact Or.inr ⟨i, by rw [hcode, hB i] at ha; exact ha, (heast i).mp hbi⟩
  · rintro (⟨ha, hb0⟩ | ⟨i, ha, hbi⟩)
    · exact Or.inl ⟨ha, hroot.mpr hb0⟩
    · exact Or.inr ⟨i, by rw [hcode, hB i]; exact ha, (heast i).mpr hbi⟩

/-- Helper toward Lemma 5.5. Equal prefix codes preserve the endpoint of
every prefix dart in its permanent prefix IDs. -/
theorem lPlusSourceWitnessAligned_prefixDartEndpoint_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) (d : LPlusPrefixDart s.W s.h k) :
    kmswLimitDartVertex (shiftedStream s.W 0) d.val =
      kmswLimitDartVertex (shiftedStream s'.W 0) d.val := by
  by_cases hkpos : 0 < k
  · have he : d.val.1 < (kmswStage (shiftedStream s.W 0)
        (boundaryHitTime (shiftedStream s.W 0) s.h k - 1)).nextEdge := by
      exact (Set.ext_iff.mp (lPlusPrefixMinusEdges_eq_previousStage
        (W := s.W) (h := s.h) hkpos) d.val.1).mp d.property
    have hstage := lPlusSourceWitnessAligned_prefixStage_eq_of_presentation_codes_eq
      x k r r' s s' hr
    have he' := he
    rw [hstage] at he'
    have hs := edge_endpoints_eq (shiftedStream s.W 0) he
    have hs' := edge_endpoints_eq (shiftedStream s'.W 0) he'
    cases hbit : d.val.2
    · simp only [kmswLimitDartVertex, hbit, Bool.false_eq_true, ↓reduceIte]
      rw [← hs.1, ← hs'.1, hstage]
    · simp only [kmswLimitDartVertex, hbit, ↓reduceIte]
      rw [← hs.2, ← hs'.2, hstage]
  · have hk0 : k = 0 := by omega
    subst k
    exact ((Set.ext_iff.mp (boundaryGluingPrefixMinusEdges_zero s.W s.h)
      d.val.1).mp d.property).elim

/-- Helper toward Lemma 5.5. Every positive-index prefix vertex has an
incident prefix dart, in the unchanged permanent vertex IDs. -/
theorem lPlus_prefix_vertex_endpoint_exists
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (hk : 0 < k) (v : LPlusPrefixVertex W h k) :
    ∃ d : LPlusPrefixDart W h k,
      kmswLimitDartVertex (shiftedStream W 0) d.val = v.val := by
  have hv := (Set.ext_iff.mp (boundaryGluingPrefixMinusVertices_of_pos
    (W := W) (h := h) hk) v.val).mp v.property
  obtain ⟨⟨e, b⟩, he⟩ := stageEndpoint_exists (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k - 1) v.val hv
  refine ⟨lPlusPrefixStageDart hk (e, b), ?_⟩
  have hs := edge_endpoints_eq (shiftedStream W 0) e.isLt
  cases b
  · exact hs.1.symm.trans he
  · exact hs.2.symm.trans he

/-- Helper toward Lemma 5.5. A prefix/primed shared vertex transports
through its incident ordered attachment edge, including the isolated prefix
root at index zero. -/
private theorem lPlus_prefix_primed_vertex_forward
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code)
    (a : LPlusPrefixVertex s.W s.h k) (b : ℕ) :
    a.val = boundaryGluingPrimedVertexMap s.W s.h k s.hτ b →
      a.val = boundaryGluingPrimedVertexMap s'.W s'.h k s'.hτ b := by
  intro hab
  by_cases hkpos : 0 < k
  · obtain ⟨da, hda⟩ := lPlus_prefix_vertex_endpoint_exists hkpos a
    let p := primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ
    obtain ⟨f, hf⟩ := geoInfty_vertex_endpoint p b
    have hp : ∃ db : ℕ × Bool, kmswLimitDartVertex p db = b := by
      rcases hf with hf | hf
      · exact ⟨(f, false), hf⟩
      · exact ⟨(f, true), hf⟩
    obtain ⟨db, hdb⟩ := hp
    have hincident : kmswLimitDartVertex (shiftedStream s.W 0) da.val =
        kmswLimitDartVertex (shiftedStream s.W 0) (lMinusPrimedDartImage s.hτ db) := by
      rw [lMinusPrimedDartImage_endpoint s.hτ, hdb, hda]
      exact hab
    obtain ⟨e, he, hend⟩ := lPlus_prefix_future_shared_endpoint s.hτ hk da
      (primedLimitDartMap (boundaryGluingFutureStream s.W s.h k) s.hτ db) hincident
    have heP : e ∈ boundaryGluingPrefixMinusEdges s.W s.h k :=
      ((Set.ext_iff.mp (boundaryGluingPrefixMinusEdges_inter_primedEdges
        s.W s.h k s.hτ s.hfin hk) e).mpr he).1
    obtain ⟨j, hj⟩ := boundaryGluingUpperLeftEdges_subset_primedEdges
      s.W s.h k s.hτ s.hfin he
    have hbit : ∃ c : Bool, kmswLimitDartVertex (shiftedStream s.W 0) (e, c) = a.val := by
      rcases hend with hw | ht
      · exact ⟨false, hw.trans hda⟩
      · exact ⟨true, ht.trans hda⟩
    obtain ⟨c, hc⟩ := hbit
    let d : LPlusPrefixDart s.W s.h k := ⟨(e, c), heP⟩
    let z : ℕ × Bool := (j, c ^^ primedLimitSideFlip _ s.hτ j)
    have hz : lMinusPrimedDartImage s.hτ z = d.val := by
      apply Prod.ext hj
      change ((c ^^ primedLimitSideFlip _ s.hτ j) ^^ primedLimitSideFlip _ s.hτ j) = c
      rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    have heP' : e ∈ boundaryGluingPrefixMinusEdges s'.W s'.h k := by
      exact (Set.ext_iff.mp
        (lPlusSourceWitnessAligned_prefixEdges_eq_of_presentation_codes_eq
          x k r r' s s' hk hr) e).mp heP
    let d' : LPlusPrefixDart s'.W s'.h k := ⟨(e, c), heP'⟩
    have hz' : lMinusPrimedDartImage s'.hτ z = d'.val :=
      ((lPlusSourceWitnessAligned_prefixPrimedDartKernel_transport
        x k r r' s s' hk hr d d' rfl z).mp hz.symm).symm
    have hlocal : kmswLimitDartVertex p z = b := by
      apply (show Function.Injective (boundaryGluingPrimedVertexMap s.W s.h k s.hτ)
        from lPlusPrimedVertexImage_injective s.hτ s.hqMode)
      exact (lMinusPrimedDartImage_endpoint s.hτ z).symm.trans
        ((congrArg (kmswLimitDartVertex (shiftedStream s.W 0)) hz).trans
          (hc.trans hab))
    have hcode := lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq
      x k r r' s s' hr
    have hlocal' : kmswLimitDartVertex
        (primedCode (primedSimInput (boundaryGluingFutureStream s'.W s'.h k)) s'.hτ) z = b := by
      rw [← hcode]
      exact hlocal
    calc
      a.val = kmswLimitDartVertex (shiftedStream s.W 0) d.val := hc.symm
      _ = kmswLimitDartVertex (shiftedStream s'.W 0) d'.val :=
        lPlusSourceWitnessAligned_prefixDartEndpoint_eq x k r r' s s' hk hr d
      _ = boundaryGluingPrimedVertexMap s'.W s'.h k s'.hτ b := by
        rw [← hz', lMinusPrimedDartImage_endpoint s'.hτ, hlocal']
  · have hk0 : k = 0 := by omega
    subst k
    have ha : a.val = 0 := (Set.ext_iff.mp
      (boundaryGluingPrefixMinusVertices_zero (W := s.W) (h := s.h)) a.val).mp a.property
    have hroot : boundaryGluingPrimedVertexMap s.W s.h 0 s.hτ 1 = 0 :=
      lPlus_primed_root_starts_at_xk s.hτ
    have hb : b = 1 := (show Function.Injective
      (boundaryGluingPrimedVertexMap s.W s.h 0 s.hτ) from
        lPlusPrimedVertexImage_injective s.hτ s.hqMode) (hab.symm.trans (ha.trans hroot.symm))
    rw [ha, hb]
    exact (lPlus_primed_root_starts_at_xk s'.hτ).symm

/-- Helper toward Lemma 5.5. The full prefix/primed vertex kernel
transports under equal presentation codes and unchanged prefix vertex IDs. -/
theorem lPlusSourceWitnessAligned_prefixPrimedVertexKernel_transport
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code)
    (a : LPlusPrefixVertex s.W s.h k) (a' : LPlusPrefixVertex s'.W s'.h k)
    (ha : a'.val = a.val) (b : ℕ) :
    a.val = boundaryGluingPrimedVertexMap s.W s.h k s.hτ b ↔
      a'.val = boundaryGluingPrimedVertexMap s'.W s'.h k s'.hτ b := by
  constructor
  · intro h
    rw [ha]
    exact lPlus_prefix_primed_vertex_forward x k r r' s s' hk hr a b h
  · intro h
    rw [← ha]
    exact lPlus_prefix_primed_vertex_forward x k r' r s' s hk hr.symm a' b h

/-- Helper toward Lemma 5.5. The prefix and hatted vertex blocks meet only
at the initial attachment vertex, including index zero. -/
theorem lPlusSourceWitnessAligned_prefixHattedVertex_eq_iff_root
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a : LPlusPrefixVertex s.W s.h k) (b : ℕ) :
    a.val = boundaryGluingHatVertexMap s.W s.h k s.hτ b ↔
      a.val = boundaryGluingPrimedVertexMap s.W s.h k s.hτ 1 ∧ b = 0 := by
  have hroot : boundaryGluingPrimedVertexMap s.W s.h k s.hτ 1 =
      boundaryVertex (shiftedStream s.W 0) s.h k :=
    lPlus_primed_root_starts_at_xk s.hτ
  have hhat0 := boundaryGluingHatVertexMap_zero s.hτ
  constructor
  · intro hab
    have ha : a.val = boundaryVertex (shiftedStream s.W 0) s.h k := by
      by_cases hkpos : 0 < k
      · obtain ⟨da, hda⟩ := lPlus_prefix_vertex_endpoint_exists hkpos a
        obtain ⟨e, he⟩ := geoInfty_vertex_endpoint
          (hatCodes (boundaryGluingFutureStream s.W s.h k) s.hτ) b
        have hd : ∃ d : ℕ × Bool,
            kmswLimitDartVertex (shiftedStream s.W 0)
              (boundaryGluingHatEdgeMap s.W s.h k s.hτ d.1, d.2) =
            boundaryGluingHatVertexMap s.W s.h k s.hτ b := by
          rcases he with hw | ht
          · exact ⟨(e, false), (boundaryGluing_hat_edge_endpoints
              s.W s.h k s.hτ e).1.trans (congrArg _ hw)⟩
          · exact ⟨(e, true), (boundaryGluing_hat_edge_endpoints
              s.W s.h k s.hτ e).2.trans (congrArg _ ht)⟩
        obtain ⟨d, hd⟩ := hd
        have hv := hda.trans (hab.trans hd.symm)
        exact hda.symm.trans (lPlus_prefix_hatted_shared_endpoint_initial
          (H := s.H) s.hτ s.hqMode s.hfin hk da d hv)
      · have hk0 : k = 0 := by omega
        subst k
        exact (Set.ext_iff.mp
          (boundaryGluingPrefixMinusVertices_zero (W := s.W) (h := s.h)) a.val).mp a.property
    exact ⟨ha.trans hroot.symm,
      boundaryGluingHatVertexMap_injective s.W s.h k s.hτ
        (hab.symm.trans (ha.trans hhat0.symm))⟩
  · rintro ⟨ha, rfl⟩
    exact ha.trans (hroot.trans hhat0.symm)

/-- Helper toward Lemma 5.5. The prefix/hatted vertex kernel transports
using its root characterization and the marked hatted root. -/
theorem lPlusSourceWitnessAligned_prefixHattedVertexKernel_transport
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode
    ∀ (phi : GeometricSideMarkedIso M M')
      (a : LPlusPrefixVertex s.W s.h k) (a' : LPlusPrefixVertex s'.W s'.h k)
      (b : LPlusHattedVertex M) (b' : LPlusHattedVertex M'),
      a'.val = a.val → phi.equiv (.inl b) = .inl b' →
      (a.val = boundaryGluingHatVertexMap s.W s.h k s.hτ b.val ↔
        a'.val = boundaryGluingHatVertexMap s'.W s'.h k s'.hτ b'.val) := by
  dsimp only
  intro phi a a' b b' ha hb
  rw [lPlusSourceWitnessAligned_prefixHattedVertex_eq_iff_root x k r s hk,
    lPlusSourceWitnessAligned_prefixHattedVertex_eq_iff_root x k r' s' hk,
    lPlusSourceWitnessAligned_prefixPrimedVertexKernel_transport x k r r' s s' hk hr
      a a' ha 1]
  have hh := phi.relation_iff .root (.inl b) (.inl b)
  rw [hb] at hh
  exact and_congr_right (fun _ => hh)

/-- Helper toward Lemma 5.5. Injective component embeddings reduce their
same-component kernels to equality of representatives. -/
private theorem lPlus_injective_component_kernel
    {A B C D E F : Type*} (u : A → C) (v : B → D) (f : E ≃ F)
    (i : A → E) (j : B → F) (hu : Function.Injective u) (hv : Function.Injective v)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (a b : A) (a' b' : B) (ha : f (i a) = j a') (hb : f (i b) = j b') :
    u a = u b ↔ v a' = v b' := by
  rw [hu.eq_iff, hv.eq_iff]
  constructor
  · intro h
    apply hj
    rw [← ha, ← hb, h]
  · intro h
    apply hi
    apply f.injective
    rw [ha, hb, h]

/-- Helper toward Lemma 5.5. Equality kernels on a three-component sum
are determined by their six unordered component pairs. -/
private theorem lPlus_three_component_kernel
    {A B C E F G U V : Type*}
    (p : Sum A (Sum B C) → U) (q : Sum E (Sum F G) → V)
    (f : Sum A (Sum B C) ≃ Sum E (Sum F G))
    (haa : ∀ a b : A, p (.inl a) = p (.inl b) ↔ q (f (.inl a)) = q (f (.inl b)))
    (hbb : ∀ a b : B, p (.inr (.inl a)) = p (.inr (.inl b)) ↔
      q (f (.inr (.inl a))) = q (f (.inr (.inl b))))
    (hcc : ∀ a b : C, p (.inr (.inr a)) = p (.inr (.inr b)) ↔
      q (f (.inr (.inr a))) = q (f (.inr (.inr b))))
    (hab : ∀ a : A, ∀ b : B, p (.inl a) = p (.inr (.inl b)) ↔
      q (f (.inl a)) = q (f (.inr (.inl b))))
    (hac : ∀ a : A, ∀ b : C, p (.inl a) = p (.inr (.inr b)) ↔
      q (f (.inl a)) = q (f (.inr (.inr b))))
    (hbc : ∀ a : B, ∀ b : C, p (.inr (.inl a)) = p (.inr (.inr b)) ↔
      q (f (.inr (.inl a))) = q (f (.inr (.inr b)))) :
    ∀ a b, p a = p b ↔ q (f a) = q (f b) := by
  intro a b
  rcases a with a | (a | a) <;> rcases b with b | (b | b)
  · exact haa a b
  · exact hab a b
  · exact hac a b
  · exact (eq_comm.trans (hab b a)).trans eq_comm
  · exact hbb a b
  · exact hbc a b
  · exact (eq_comm.trans (hac b a)).trans eq_comm
  · exact (eq_comm.trans (hbc b a)).trans eq_comm
  · exact hcc a b

/-- Helper toward Lemma 5.5. Equal presentation codes give simultaneous
component transports preserving both complete gluing kernels. -/
theorem lPlusSourceWitnessAligned_gluedBlockEquivs_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    ∃ (phi : GeometricSideMarkedIso M M')
      (fV : LPlusBlockVertex s.W s.h k M ≃
        LPlusBlockVertex s'.W s'.h k M')
      (fD : LPlusBlockDart s.W s.h k M ≃
        LPlusBlockDart s'.W s'.h k M'),
      (∀ v : LPlusPrefixVertex s.W s.h k,
        ∃ v' : LPlusPrefixVertex s'.W s'.h k,
          fV (.inl v) = .inl v' ∧ v'.val = v.val) ∧
      (∀ v : LPlusPrimedVertex,
        fV (.inr (.inl v)) = .inr (.inl v)) ∧
      (∀ v : LPlusHattedVertex M,
        ∃ v' : LPlusHattedVertex M',
          fV (.inr (.inr v)) = .inr (.inr v') ∧
            phi.equiv (.inl v) = .inl v') ∧
      (∀ d : LPlusPrefixDart s.W s.h k,
        ∃ d' : LPlusPrefixDart s'.W s'.h k,
          fD (.inl d) = .inl d' ∧ d'.val = d.val) ∧
      (∀ d : LPlusPrimedDart,
        fD (.inr (.inl d)) = .inr (.inl d)) ∧
      (∀ d : LPlusHattedDart M,
        ∃ d' : LPlusHattedDart M',
          fD (.inr (.inr d)) = .inr (.inr d') ∧
            phi.equiv (.inr d) = .inr d') ∧
      (∀ a b : LPlusBlockVertex s.W s.h k M,
        lPlusBlockVertexImage (M := M) s.hτ a =
          lPlusBlockVertexImage (M := M) s.hτ b ↔
        lPlusBlockVertexImage (M := M') s'.hτ (fV a) =
          lPlusBlockVertexImage (M := M') s'.hτ (fV b)) ∧
      (∀ a b : LPlusBlockDart s.W s.h k M,
        lPlusBlockDartImage (M := M) s.hτ a =
          lPlusBlockDartImage (M := M) s.hτ b ↔
        lPlusBlockDartImage (M := M') s'.hτ (fD a) =
          lPlusBlockDartImage (M := M') s'.hτ (fD b))
    := by
  let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode
  let N := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode
  obtain ⟨phi, fV, fD, hPV, hTV, hHV, hPD, hTD, hHD⟩ :=
    lPlusSourceWitnessAligned_representativeEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  refine ⟨phi, fV, fD, hPV, hTV, hHV, hPD, hTD, hHD, ?_, ?_⟩
  · apply lPlus_three_component_kernel
    · intro a b
      obtain ⟨a', ha, _⟩ := hPV a
      obtain ⟨b', hb, _⟩ := hPV b
      rw [ha, hb]
      exact lPlus_injective_component_kernel
        (fun v : LPlusPrefixVertex s.W s.h k => v.val)
        (fun v : LPlusPrefixVertex s'.W s'.h k => v.val) fV
        Sum.inl Sum.inl Subtype.val_injective Subtype.val_injective
        (fun _ _ h => Sum.inl.inj h) (fun _ _ h => Sum.inl.inj h) a b a' b' ha hb
    · intro a b
      rw [hTV a, hTV b]
      exact (lPlusPrimedVertexImage_injective s.hτ s.hqMode).eq_iff.trans
        (lPlusPrimedVertexImage_injective s'.hτ s'.hqMode).eq_iff.symm
    · intro a b
      obtain ⟨a', ha, _⟩ := hHV a
      obtain ⟨b', hb, _⟩ := hHV b
      rw [ha, hb]
      exact lPlus_injective_component_kernel
        (fun v : LPlusHattedVertex M => boundaryGluingHatVertexMap s.W s.h k s.hτ v.val)
        (fun v : LPlusHattedVertex N => boundaryGluingHatVertexMap s'.W s'.h k s'.hτ v.val)
        fV (fun v => .inr (.inr v)) (fun v => .inr (.inr v))
        (lPlusHattedVertexImage_injective s.hτ s.hqMode)
        (lPlusHattedVertexImage_injective s'.hτ s'.hqMode)
        (fun _ _ h => Sum.inr.inj (Sum.inr.inj h))
        (fun _ _ h => Sum.inr.inj (Sum.inr.inj h)) a b a' b' ha hb
    · intro a b
      obtain ⟨a', ha, hav⟩ := hPV a
      rw [ha, hTV b]
      exact lPlusSourceWitnessAligned_prefixPrimedVertexKernel_transport
        x k r r' s s' hk hr a a' hav b
    · intro a b
      obtain ⟨a', ha, hav⟩ := hPV a
      obtain ⟨b', hb, hbphi⟩ := hHV b
      rw [ha, hb]
      exact lPlusSourceWitnessAligned_prefixHattedVertexKernel_transport
        x k r r' s s' hk hr phi a a' b b' hav hbphi
    · intro a b
      obtain ⟨b', hb, hbphi⟩ := hHV b
      rw [hTV a, hb]
      exact lPlusSourceWitnessAligned_primedHattedVertexKernel_transport
        x k r r' s s' hr phi a b b' hbphi
  · apply lPlus_three_component_kernel
    · intro a b
      obtain ⟨a', ha, _⟩ := hPD a
      obtain ⟨b', hb, _⟩ := hPD b
      rw [ha, hb]
      exact lPlus_injective_component_kernel
        (fun d : LPlusPrefixDart s.W s.h k => d.val)
        (fun d : LPlusPrefixDart s'.W s'.h k => d.val) fD
        Sum.inl Sum.inl Subtype.val_injective Subtype.val_injective
        (fun _ _ h => Sum.inl.inj h) (fun _ _ h => Sum.inl.inj h) a b a' b' ha hb
    · intro a b
      rw [hTD a, hTD b]
      exact (lPlusPrimedDartImage_injective s.hτ s.hqMode).eq_iff.trans
        (lPlusPrimedDartImage_injective s'.hτ s'.hqMode).eq_iff.symm
    · intro a b
      obtain ⟨a', ha, _⟩ := hHD a
      obtain ⟨b', hb, _⟩ := hHD b
      rw [ha, hb]
      exact lPlus_injective_component_kernel
        (fun d : LPlusHattedDart M => lPlusBlockDartImage (M := M) s.hτ (.inr (.inr d)))
        (fun d : LPlusHattedDart N => lPlusBlockDartImage (M := N) s'.hτ (.inr (.inr d)))
        fD (fun d => .inr (.inr d)) (fun d => .inr (.inr d))
        (lPlusHattedDartImage_injective s.hτ s.hqMode)
        (lPlusHattedDartImage_injective s'.hτ s'.hqMode)
        (fun _ _ h => Sum.inr.inj (Sum.inr.inj h))
        (fun _ _ h => Sum.inr.inj (Sum.inr.inj h)) a b a' b' ha hb
    · intro a b
      obtain ⟨a', ha, hav⟩ := hPD a
      rw [ha, hTD b]
      exact lPlusSourceWitnessAligned_prefixPrimedDartKernel_transport
        x k r r' s s' hk hr a a' hav b
    · intro a b
      obtain ⟨a', ha, _⟩ := hPD a
      obtain ⟨b', hb, _⟩ := hHD b
      rw [ha, hb]
      obtain ⟨hsrc, htgt⟩ := lPlusSourceWitnessAligned_prefixHattedDartImage_ne
        x k r r' s s' hk
      exact ⟨fun h => (hsrc a b h).elim, fun h => (htgt a' b' h).elim⟩
    · intro a b
      obtain ⟨b', hb, hbphi⟩ := hHD b
      rw [hTD a, hb]
      exact lPlusSourceWitnessAligned_primedHattedDartKernel_transport
        x k r r' s s' hr phi a b b' hbphi

/-- Helper toward Lemma 5.5. The simultaneous component transports preserve
all six cross-component vertex and dart kernels. -/
theorem lPlusSourceWitnessAligned_crossComponentKernelCompatibility
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let M' := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    ∃ (phi : GeometricSideMarkedIso M M')
      (fV : LPlusBlockVertex s.W s.h k M ≃
        LPlusBlockVertex s'.W s'.h k M')
      (fD : LPlusBlockDart s.W s.h k M ≃
        LPlusBlockDart s'.W s'.h k M'),
      (∀ a : LPlusPrefixVertex s.W s.h k, ∀ b : LPlusPrimedVertex,
        lPlusBlockVertexImage (M := M) s.hτ (.inl a) =
          lPlusBlockVertexImage (M := M) s.hτ (.inr (.inl b)) ↔
        lPlusBlockVertexImage (M := M') s'.hτ (fV (.inl a)) =
          lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inl b)))) ∧
      (∀ a : LPlusPrefixVertex s.W s.h k, ∀ b : LPlusHattedVertex M,
        lPlusBlockVertexImage (M := M) s.hτ (.inl a) =
          lPlusBlockVertexImage (M := M) s.hτ (.inr (.inr b)) ↔
        lPlusBlockVertexImage (M := M') s'.hτ (fV (.inl a)) =
          lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inr b)))) ∧
      (∀ a : LPlusPrimedVertex, ∀ b : LPlusHattedVertex M,
        lPlusBlockVertexImage (M := M) s.hτ (.inr (.inl a)) =
          lPlusBlockVertexImage (M := M) s.hτ (.inr (.inr b)) ↔
        lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inl a))) =
          lPlusBlockVertexImage (M := M') s'.hτ (fV (.inr (.inr b)))) ∧
      (∀ a : LPlusPrefixDart s.W s.h k, ∀ b : LPlusPrimedDart,
        lPlusBlockDartImage (M := M) s.hτ (.inl a) =
          lPlusBlockDartImage (M := M) s.hτ (.inr (.inl b)) ↔
        lPlusBlockDartImage (M := M') s'.hτ (fD (.inl a)) =
          lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inl b)))) ∧
      (∀ a : LPlusPrefixDart s.W s.h k, ∀ b : LPlusHattedDart M,
        lPlusBlockDartImage (M := M) s.hτ (.inl a) =
          lPlusBlockDartImage (M := M) s.hτ (.inr (.inr b)) ↔
        lPlusBlockDartImage (M := M') s'.hτ (fD (.inl a)) =
          lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inr b)))) ∧
      (∀ a : LPlusPrimedDart, ∀ b : LPlusHattedDart M,
        lPlusBlockDartImage (M := M) s.hτ (.inr (.inl a)) =
          lPlusBlockDartImage (M := M) s.hτ (.inr (.inr b)) ↔
        lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inl a))) =
          lPlusBlockDartImage (M := M') s'.hτ (fD (.inr (.inr b))))
    := by
  obtain ⟨phi, fV, fD, _, _, _, _, _, _, hV, hD⟩ :=
    lPlusSourceWitnessAligned_gluedBlockEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  exact ⟨phi, fV, fD,
    fun a b => hV (.inl a) (.inr (.inl b)),
    fun a b => hV (.inl a) (.inr (.inr b)),
    fun a b => hV (.inr (.inl a)) (.inr (.inr b)),
    fun a b => hD (.inl a) (.inr (.inl b)),
    fun a b => hD (.inl a) (.inr (.inr b)),
    fun a b => hD (.inr (.inl a)) (.inr (.inr b))⟩

/- (1) permanent UR-stack readings identify the beta edge indices and dart-bit
    correction from the common primed code;
(2) monotonicity of the reversed LL stack puts both ordered prefix
    attachments at one common local stage;
(3) the proved shared-endpoint classifications reduce vertex kernels to
    these code-determined attachments, with a separate isolated-root case.
A rotation-orbit reconstruction was also examined, but is unnecessary here:
its naturality argument would first require the dart quotient transport.
Neither equality of ambient images nor a new geometric premise is assumed.
Both recorded targets are proved above. This file makes no assertion about -/

end DirectedDistances.PaperProofs.Section5

