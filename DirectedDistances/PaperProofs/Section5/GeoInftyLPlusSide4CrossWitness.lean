/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly8
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable13

/-! Cross-witness transport for the corrected nonnegative left decoder. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the aligned block equivalences descend to
both complete gluing quotients, with their representative actions retained. -/
theorem lPlusSourceWitnessAligned_gluedQuotientEquivs_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k)
      s.longest s.hqMode
    let N := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k)
      s'.longest s'.hqMode
    ∃ (phi : GeometricSideMarkedIso M N)
      (fV : LPlusBlockVertex s.W s.h k M ≃ LPlusBlockVertex s'.W s'.h k N)
      (fD : LPlusBlockDart s.W s.h k M ≃ LPlusBlockDart s'.W s'.h k N)
      (qV : LPlusGluedVertex s.longest s.hqMode s.hτ ≃
        LPlusGluedVertex s'.longest s'.hqMode s'.hτ)
      (qD : LPlusGluedDart s.longest s.hqMode s.hτ ≃
        LPlusGluedDart s'.longest s'.hqMode s'.hτ),
      (∀ a, qV ⟦a⟧ = ⟦fV a⟧) ∧
      (∀ a, qD ⟦a⟧ = ⟦fD a⟧) ∧
      (∀ v : LPlusPrefixVertex s.W s.h k,
        ∃ v' : LPlusPrefixVertex s'.W s'.h k,
          fV (.inl v) = .inl v' ∧ v'.val = v.val) ∧
      (∀ v : LPlusPrimedVertex, fV (.inr (.inl v)) = .inr (.inl v)) ∧
      (∀ v : LPlusHattedVertex M, ∃ v' : LPlusHattedVertex N,
        fV (.inr (.inr v)) = .inr (.inr v') ∧ phi.equiv (.inl v) = .inl v') ∧
      (∀ d : LPlusPrefixDart s.W s.h k,
        ∃ d' : LPlusPrefixDart s'.W s'.h k,
          fD (.inl d) = .inl d' ∧ d'.val = d.val) ∧
      (∀ d : LPlusPrimedDart, fD (.inr (.inl d)) = .inr (.inl d)) ∧
      (∀ d : LPlusHattedDart M, ∃ d' : LPlusHattedDart N,
        fD (.inr (.inr d)) = .inr (.inr d') ∧ phi.equiv (.inr d) = .inr d') := by
  obtain ⟨phi, fV, fD, hPV, hTV, hHV, hPD, hTD, hHD, hV, hD⟩ :=
    lPlusSourceWitnessAligned_gluedBlockEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  let qV : LPlusGluedVertex s.longest s.hqMode s.hτ ≃
      LPlusGluedVertex s'.longest s'.hqMode s'.hτ := Quotient.congr fV hV
  let qD : LPlusGluedDart s.longest s.hqMode s.hτ ≃
      LPlusGluedDart s'.longest s'.hqMode s'.hτ := Quotient.congr fD hD
  exact ⟨phi, fV, fD, qV, qD, fun _ => rfl, fun _ => rfl,
    hPV, hTV, hHV, hPD, hTD, hHD⟩

/-- Helper toward Lemma 5.5: the ordered finite attachment list is
determined by the prefix code, before either terminal correction. -/
theorem lPlusSourceWitnessAligned_upperLeftList_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r') (hr : r.code = r'.code) :
    (kmswStage (shiftedStream s.W 0) (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse =
      (kmswStage (shiftedStream s'.W 0) (boundaryHitTime (shiftedStream s'.W 0) s'.h k)).UL.dropLast.reverse := by
  have hp := (lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq
    x k r r' s.toLPlusSidePresentationSourceWitness
      s'.toLPlusSidePresentationSourceWitness hr).1
  have ht := lPlusBoundaryHitTime_eq_of_boundaryPrefixCode_eq s.W s'.W s.h s'.h k hp
  have hprefix : ∀ i < boundaryHitTime (shiftedStream s.W 0) s.h k,
      shiftedStream s.W 0 i = shiftedStream s'.W 0 i := by
    intro i hi
    have hi' : i < boundaryHitTime (shiftedStream s'.W 0) s'.h k := by omega
    exact (lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt s.W s.h k hi).symm.trans
      ((congrFun hp i).trans (lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt s'.W s'.h k hi'))
  have hs := kmswStage_eq_of_prefix _ _ _ hprefix
  exact (congrArg (fun S : State => S.UL.dropLast.reverse) hs).trans
    (congrArg (fun n => (kmswStage (shiftedStream s'.W 0) n).UL.dropLast.reverse) ht)

/-- Helper toward Lemma 5.5: equal lists have equal entries at equal indices. -/
private theorem lPlusSide4_list_get_eq {A B : List ℕ} (h : A = B)
    (i : Fin A.length) (j : Fin B.length) (hij : i.val = j.val) : A[i.val] = B[j.val] := by
  cases h
  have hi : i = j := Fin.ext hij
  cases hi
  rfl

/-- Helper toward Lemma 5.5: on quotient darts the induced equivalence
fixes prefix IDs and primed IDs and follows the hatted marked action. -/
theorem lPlusSourceWitnessAligned_gluedDartEquiv_actions
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode
    let N := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode
    ∃ (phi : GeometricSideMarkedIso M N)
      (qD : LPlusGluedDart s.longest s.hqMode s.hτ ≃
        LPlusGluedDart s'.longest s'.hqMode s'.hτ),
      (∀ (a : LPlusPrefixDart s.W s.h k) (a' : LPlusPrefixDart s'.W s'.h k),
        a'.val = a.val →
          qD (lPlusPrefixGluedDart (hτ := s.hτ) (hqMode := s.hqMode) a) =
            lPlusPrefixGluedDart (hτ := s'.hτ) (hqMode := s'.hqMode) a') ∧
      (∀ a, qD (lPlusPrimedGluedDart (hτ := s.hτ) (hqMode := s.hqMode) a) =
        lPlusPrimedGluedDart (hτ := s'.hτ) (hqMode := s'.hqMode) a) ∧
      (∀ a, qD (lPlusHattedGluedDart (hτ := s.hτ) (hqMode := s.hqMode) a) =
        lPlusHattedGluedDart (hτ := s'.hτ) (hqMode := s'.hqMode)
          (lMinusMarkedDartMap phi a)) ∧
      (∀ (a : Fin ((kmswStage (shiftedStream s.W 0)
          (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse.length) × Bool)
        (a' : Fin ((kmswStage (shiftedStream s'.W 0)
          (boundaryHitTime (shiftedStream s'.W 0) s'.h k)).UL.dropLast.reverse.length) × Bool),
        a.1.val = a'.1.val → a.2 = a'.2 →
          qD (lPlusUpperLeftGluedDart s.hτ s.hqMode s.hfin hk a) =
            lPlusUpperLeftGluedDart s'.hτ s'.hqMode s'.hfin hk a') := by
  obtain ⟨phi, fV, fD, qV, qD, _, hqD, _, _, _, hPD, hTD, hHD⟩ :=
    lPlusSourceWitnessAligned_gluedQuotientEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  refine ⟨phi, qD, ?_, ?_, ?_, ?_⟩
  · intro a a' ha'
    obtain ⟨b, hb, hba⟩ := hPD a
    have hbe : b = a' := Subtype.ext (hba.trans ha'.symm)
    change qD ⟦Sum.inl a⟧ = ⟦Sum.inl a'⟧
    rw [hqD, hb, hbe]
  · intro a
    change qD ⟦Sum.inr (Sum.inl a)⟧ = ⟦Sum.inr (Sum.inl a)⟧
    rw [hqD, hTD]
  · intro a
    obtain ⟨b, hb, hphi⟩ := hHD a
    have hbe : b = lMinusMarkedDartMap phi a := by
      exact Sum.inr.inj (hphi.symm.trans (lMinusMarkedDartMap_cell phi a))
    change qD ⟦Sum.inr (Sum.inr a)⟧ = ⟦Sum.inr (Sum.inr _)⟧
    rw [hqD, hb, hbe]

  · intro a a' ha hb
    have hAB := lPlusSourceWitnessAligned_upperLeftList_eq x k r r' s s' hr
    let p : LPlusPrefixDart s.W s.h k :=
      ⟨(_, a.2), lPlusUpperLeftEdge_mem_prefix s.hτ s.hfin hk a.1⟩
    let p' : LPlusPrefixDart s'.W s'.h k :=
      ⟨(_, a'.2), lPlusUpperLeftEdge_mem_prefix s'.hτ s'.hfin hk a'.1⟩
    obtain ⟨b, hbD, hbval⟩ := hPD p
    have hpval : p'.val = p.val :=
      Prod.ext (lPlusSide4_list_get_eq hAB a.1 a'.1 ha).symm hb.symm
    have hbe : b = p' := Subtype.ext (hbval.trans hpval.symm)
    change qD ⟦Sum.inl p⟧ = ⟦Sum.inl p'⟧
    rw [hqD, hbD, hbe]

/-- Helper toward Lemma 5.5: equality of finite input prefixes preserves
the values of the finite rotations, including both endpoint bits. -/
private theorem lPlusSide4_stageRotation_val_eq
    (u v : ℕ → Fin 3) (n m : ℕ) (hnm : n = m) (hp : ∀ i < n, u i = v i)
    (d : StageDart (kmswStage u n).nextEdge)
    (d' : StageDart (kmswStage v m).nextEdge)
    (hd : (d'.1.val, d'.2) = (d.1.val, d.2)) :
    ((stageRot u n d).1.val, (stageRot u n d).2) =
      ((stageRot v m d').1.val, (stageRot v m d').2) := by
  cases hnm
  let I := kmswStageDirectedMapIsoOfPrefix u v n hp
  have hId : I.toEquiv d = d' := by
    apply Prod.ext
    · apply Fin.ext
      exact (kmswStageDirectedMapIsoOfPrefix_val u v n hp d).1.trans
        (congrArg Prod.fst hd).symm
    · exact (kmswStageDirectedMapIsoOfPrefix_val u v n hp d).2.trans
        (congrArg Prod.snd hd).symm
  have hc := I.rot_comm d
  change I.toEquiv (stageRot u n d) = stageRot v n (I.toEquiv d) at hc
  rw [hId] at hc
  have hv := kmswStageDirectedMapIsoOfPrefix_val u v n hp (stageRot u n d)
  exact (Prod.ext hv.1 hv.2).symm.trans
    (congrArg (fun a : StageDart (kmswStage v n).nextEdge => (a.1.val, a.2)) hc)

/-- Helper toward Lemma 5.5: the finite prefix permutation is determined
by the presentation code, independently of the source witness. -/
theorem lPlusSourceWitnessAligned_prefixRotation_val_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code)
    (a : LPlusPrefixDart s.W s.h k) (a' : LPlusPrefixDart s'.W s'.h k)
    (ha : a'.val = a.val) :
    (lPlusPrefixRotation (W := s.W) (h := s.h) (k := k) (H := s.H)
      (hLL := s.hLL) (longest := s.longest) (hτ := s.hτ) (hp := s.hp)
      (P := s.P) (hqMode := s.hqMode) (Tpath := s.Tpath) (hfin := s.hfin)
      (hleft := s.hleft) hk a).val =
    (lPlusPrefixRotation (W := s'.W) (h := s'.h) (k := k) (H := s'.H)
      (hLL := s'.hLL) (longest := s'.longest) (hτ := s'.hτ) (hp := s'.hp)
      (P := s'.P) (hqMode := s'.hqMode) (Tpath := s'.Tpath) (hfin := s'.hfin)
      (hleft := s'.hleft) hk a').val := by
  by_cases hkpos : 0 < k
  · rw [lPlusPrefixRotation_apply s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk hkpos,
      lPlusPrefixRotation_apply s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk hkpos]
    have hp := (lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq
      x k r r' s.toLPlusSidePresentationSourceWitness
        s'.toLPlusSidePresentationSourceWitness hr).1
    have ht := lPlusBoundaryHitTime_eq_of_boundaryPrefixCode_eq s.W s'.W s.h s'.h k hp
    have hprefix : ∀ i < boundaryHitTime (shiftedStream s.W 0) s.h k - 1,
        shiftedStream s.W 0 i = shiftedStream s'.W 0 i := by
      intro i hi
      have hi₁ : i < boundaryHitTime (shiftedStream s.W 0) s.h k := by omega
      have hi₂ : i < boundaryHitTime (shiftedStream s'.W 0) s'.h k := by omega
      exact (lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt s.W s.h k hi₁).symm.trans
        ((congrFun hp i).trans
          (lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt s'.W s'.h k hi₂))
    exact lPlusSide4_stageRotation_val_eq _ _ _ _
      (congrArg (fun n : ℕ => n - 1) ht) hprefix
      (lPlusPrefixDartStage hkpos a) (lPlusPrefixDartStage hkpos a') ha
  · have hk0 : k = 0 := by omega
    subst k
    have he : a.val.1 ∈ (∅ : Set ℕ) :=
      (Set.ext_iff.mp (boundaryGluingPrefixMinusEdges_zero s.W s.h) a.val.1).mp a.property
    exact he.elim

/-- Helper toward Lemma 5.5: extension by the identity respects a
commuting square of injective block embeddings and permutations. -/
private theorem lPlusSide4_extendDomain_naturality
    {A B Q Q' : Type*} (E : Q ≃ Q') (F : A ≃ B)
    (i : A → Q) (j : B → Q') (hi : Function.Injective i) (hj : Function.Injective j)
    [DecidablePred (fun d => d ∈ Set.range i)]
    [DecidablePred (fun d => d ∈ Set.range j)]
    (R : Equiv.Perm A) (R' : Equiv.Perm B)
    (hij : ∀ a, E (i a) = j (F a))
    (hR : ∀ a, F (R a) = R' (F a)) (d : Q) :
    E (R.extendDomain (Equiv.ofInjective i hi) d) =
      R'.extendDomain (Equiv.ofInjective j hj) (E d) := by
  by_cases hd : d ∈ Set.range i
  · obtain ⟨a, rfl⟩ := hd
    have hs := R.extendDomain_apply_image (Equiv.ofInjective i hi) a
    change R.extendDomain (Equiv.ofInjective i hi) (i a) = i (R a) at hs
    rw [hs]
    rw [hij, hij, hR]
    have hs' := R'.extendDomain_apply_image (Equiv.ofInjective j hj) (F a)
    exact hs'.symm
  · have hd' : E d ∉ Set.range j := by
      rintro ⟨b, hb⟩
      obtain ⟨a, rfl⟩ := F.surjective b
      exact hd ⟨a, E.injective ((hij a).trans hb)⟩
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hd,
      Equiv.Perm.extendDomain_apply_not_subtype _ _ hd']

/-- Helper toward Lemma 5.5: the finite corner permutation respects
transport of its length, including the empty carrier. -/
private theorem lPlusSide4_corner_transport {n m : ℕ} (h : n = m)
    (d : Fin n × Bool) :
    (Equiv.prodCongr (finCongr h) (Equiv.refl Bool)) (lPlusUpperLeftCornerPerm n d) =
      lPlusUpperLeftCornerPerm m ((Equiv.prodCongr (finCongr h) (Equiv.refl Bool)) d) := by
  cases h
  rfl

/-- Helper toward Lemma 5.5: quotient transport intertwines the finite prefix and primed rotations. -/
theorem lPlusSide4_prefix_primed_transport
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    ∃ (phi : GeometricSideMarkedIso
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)
      (lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode))
      (E : LPlusGluedDart s.longest s.hqMode s.hτ ≃
        LPlusGluedDart s'.longest s'.hqMode s'.hτ),
      (∀ (a : LPlusPrefixDart s.W s.h k) (a' : LPlusPrefixDart s'.W s'.h k),
        a'.val = a.val →
          E (lPlusPrefixGluedDart (hτ := s.hτ) (hqMode := s.hqMode) a) =
            lPlusPrefixGluedDart (hτ := s'.hτ) (hqMode := s'.hqMode) a') ∧
      (∀ a, E (lPlusHattedGluedDart (hτ := s.hτ) (hqMode := s.hqMode) a) =
        lPlusHattedGluedDart (hτ := s'.hτ) (hqMode := s'.hqMode)
          (lMinusMarkedDartMap phi a)) ∧
      (∀ d, E (lPlusPrefixExtendedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk d) =
        lPlusPrefixExtendedRotation s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk (E d)) ∧
      (∀ d, E (lPlusPrimedExtendedRotation s.hτ s.hqMode s.hfin d) =
        lPlusPrimedExtendedRotation s'.hτ s'.hqMode s'.hfin (E d)) ∧
      (∀ (a : Fin ((kmswStage (shiftedStream s.W 0)
          (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse.length) × Bool)
        (a' : Fin ((kmswStage (shiftedStream s'.W 0)
          (boundaryHitTime (shiftedStream s'.W 0) s'.h k)).UL.dropLast.reverse.length) × Bool),
        a.1.val = a'.1.val → a.2 = a'.2 →
          E (lPlusUpperLeftGluedDart s.hτ s.hqMode s.hfin hk a) =
            lPlusUpperLeftGluedDart s'.hτ s'.hqMode s'.hfin hk a') := by
  obtain ⟨phi, E, hP, hT, hH, hPort⟩ :=
    lPlusSourceWitnessAligned_gluedDartEquiv_actions x k r r' s s' hk hr
  let IP := lPlusPrefixGluedDart (hτ := s.hτ) (hqMode := s.hqMode)
  let IP' := lPlusPrefixGluedDart (hτ := s'.hτ) (hqMode := s'.hqMode)
  let IT := lPlusPrimedGluedDart (hτ := s.hτ) (hqMode := s.hqMode)
  let IT' := lPlusPrimedGluedDart (hτ := s'.hτ) (hqMode := s'.hqMode)
  have he := lPlusSourceWitnessAligned_prefixEdges_eq_of_presentation_codes_eq
    x k r r' s s' hk hr
  let preE : LPlusPrefixDart s.W s.h k ≃ LPlusPrefixDart s'.W s'.h k :=
    { toFun := fun a => ⟨a.val, (Set.ext_iff.mp he a.val.1).mp a.property⟩
      invFun := fun a => ⟨a.val, (Set.ext_iff.mp he a.val.1).mpr a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let PR := lPlusPrefixRotation (W := s.W) (h := s.h) (k := k) (H := s.H)
    (hLL := s.hLL) (longest := s.longest) (hτ := s.hτ) (hp := s.hp)
    (P := s.P) (hqMode := s.hqMode) (Tpath := s.Tpath) (hfin := s.hfin)
    (hleft := s.hleft) hk
  let PR' := lPlusPrefixRotation (W := s'.W) (h := s'.h) (k := k) (H := s'.H)
    (hLL := s'.hLL) (longest := s'.longest) (hτ := s'.hτ) (hp := s'.hp)
    (P := s'.P) (hqMode := s'.hqMode) (Tpath := s'.Tpath) (hfin := s'.hfin)
    (hleft := s'.hleft) hk
  have hPR (a) : preE (PR a) = PR' (preE a) := by
    apply Subtype.ext
    exact lPlusSourceWitnessAligned_prefixRotation_val_eq x k r r' s s' hk hr a (preE a) rfl
  let PE := lPlusPrefixExtendedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  let PE' := lPlusPrefixExtendedRotation s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
  have hPE (d) : E (PE d) = PE' (E d) :=
    lPlusSide4_extendDomain_naturality E preE IP IP'
      (lPlusPrefixGluedDart_injective (hτ := s.hτ) (hqMode := s.hqMode))
      (lPlusPrefixGluedDart_injective (hτ := s'.hτ) (hqMode := s'.hqMode))
      PR PR' (fun a => hP a (preE a) rfl) hPR d
  let TR := kmswInfRot (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ)
    (primedCode_finiteIncidence _ s.hτ s.hfin)
  let TR' := kmswInfRot (primedCode (primedSimInput (boundaryGluingFutureStream s'.W s'.h k)) s'.hτ)
    (primedCode_finiteIncidence _ s'.hτ s'.hfin)
  have hTR : TR = TR' :=
    lPlusSourceWitnessAligned_primedRotation_eq_of_presentation_codes_eq x k r r' s s' hr
  let TE := lPlusPrimedExtendedRotation s.hτ s.hqMode s.hfin
  let TE' := lPlusPrimedExtendedRotation s'.hτ s'.hqMode s'.hfin
  have hTE (d) : E (TE d) = TE' (E d) :=
    lPlusSide4_extendDomain_naturality E (Equiv.refl _) IT IT'
      (lPlusPrimedGluedDart_injective (hτ := s.hτ) (hqMode := s.hqMode))
      (lPlusPrimedGluedDart_injective (hτ := s'.hτ) (hqMode := s'.hqMode))
      TR TR' hT (fun a => congrArg (fun R : Equiv.Perm _ => R a) hTR) d
  exact ⟨phi, E, hP, hH, hPE, hTE, hPort⟩

/-- Helper toward Lemma 5.5: quotient transport intertwines the hatted and infinite boundary factors as well. -/
theorem lPlusSide4_extended_transport
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    ∃ E : LPlusGluedDart s.longest s.hqMode s.hτ ≃
        LPlusGluedDart s'.longest s'.hqMode s'.hτ,
      (∀ (a : LPlusPrefixDart s.W s.h k) (a' : LPlusPrefixDart s'.W s'.h k),
        a'.val = a.val →
          E (lPlusPrefixGluedDart (hτ := s.hτ) (hqMode := s.hqMode) a) =
            lPlusPrefixGluedDart (hτ := s'.hτ) (hqMode := s'.hqMode) a') ∧
      (∀ d, E (lPlusPrefixExtendedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk d) =
        lPlusPrefixExtendedRotation s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk (E d)) ∧
      (∀ d, E (lPlusPrimedExtendedRotation s.hτ s.hqMode s.hfin d) =
        lPlusPrimedExtendedRotation s'.hτ s'.hqMode s'.hfin (E d)) ∧
      (∀ d, E (lPlusHattedExtendedRotation s.hτ s.hqMode d) =
        lPlusHattedExtendedRotation s'.hτ s'.hqMode (E d)) ∧
      (∀ d, E (lPlusBetaCornerRotation s.hτ s.hqMode d) =
        lPlusBetaCornerRotation s'.hτ s'.hqMode (E d)) ∧
      (∀ (a : Fin ((kmswStage (shiftedStream s.W 0)
          (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse.length) × Bool)
        (a' : Fin ((kmswStage (shiftedStream s'.W 0)
          (boundaryHitTime (shiftedStream s'.W 0) s'.h k)).UL.dropLast.reverse.length) × Bool),
        a.1.val = a'.1.val → a.2 = a'.2 →
          E (lPlusUpperLeftGluedDart s.hτ s.hqMode s.hfin hk a) =
            lPlusUpperLeftGluedDart s'.hτ s'.hqMode s'.hfin hk a') := by
  obtain ⟨phi, E, hP, hH, hPE, hTE, hPort⟩ := lPlusSide4_prefix_primed_transport x k r r' s s' hk hr
  let IH := lPlusHattedGluedDart (hτ := s.hτ) (hqMode := s.hqMode)
  let IH' := lPlusHattedGluedDart (hτ := s'.hτ) (hqMode := s'.hqMode)
  let HR := lPlusHattedRotation (if s.longest then XDP.ldp else XDP.sdp)
    ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩
  let HR' := lPlusHattedRotation (if s'.longest then XDP.ldp else XDP.sdp)
    ⟨boundaryFutureHattedPath k s'.W, s'.hqMode⟩
  let hatE := lMinusMarkedDartEquiv phi
  have hHR (a) : hatE (HR a) = HR' (hatE a) := by
    have hs := (lMinusHattedRotation_iff
      (if s.longest then XDP.ldp else XDP.sdp)
      ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩ a (HR a)).mpr rfl
    have ht := (phi.relation_iff .rotation (.inr a) (.inr (HR a))).mp hs
    rw [lMinusMarkedDartMap_cell phi a, lMinusMarkedDartMap_cell phi (HR a)] at ht
    exact ((lMinusHattedRotation_iff (if s'.longest then XDP.ldp else XDP.sdp)
      ⟨boundaryFutureHattedPath k s'.W, s'.hqMode⟩ (hatE a) (hatE (HR a))).mp ht).symm
  let HE := lPlusHattedExtendedRotation s.hτ s.hqMode
  let HE' := lPlusHattedExtendedRotation s'.hτ s'.hqMode
  have hHE (d) : E (HE d) = HE' (E d) :=
    lPlusSide4_extendDomain_naturality E hatE IH IH'
      (lPlusHattedGluedDart_injective (hτ := s.hτ) (hqMode := s.hqMode))
      (lPlusHattedGluedDart_injective (hτ := s'.hτ) (hqMode := s'.hqMode))
      HR HR' hH hHR d
  let IB := lPlusBetaGluedDart s.hτ s.hqMode
  let IB' := lPlusBetaGluedDart s'.hτ s'.hqMode
  have hIB (a) : E (IB a) = IB' a := by
    rw [show IB a = IH _ from rfl, hH]
    apply congrArg IH'
    apply Sum.inr.inj
    exact (lMinusMarkedDartMap_cell phi _).symm.trans
      (lPlusSourceWitnessAligned_markedIso_boundaryBit x k r r' s s' phi a.1 a.2)
  let BE := lPlusBetaCornerRotation s.hτ s.hqMode
  let BE' := lPlusBetaCornerRotation s'.hτ s'.hqMode
  have hBE (d) : E (BE d) = BE' (E d) :=
    lPlusSide4_extendDomain_naturality E (Equiv.refl _) IB IB'
      (lPlusBetaGluedDart_injective s.hτ s.hqMode)
      (lPlusBetaGluedDart_injective s'.hτ s'.hqMode)
      lMinusBoundaryCornerPerm lMinusBoundaryCornerPerm hIB (fun _ => rfl) d
  exact ⟨E, hP, hPE, hTE, hHE, hBE, hPort⟩

/-- Helper toward Lemma 5.5: all five extended factors commute with
the quotient transport, retaining the indexed finite attachment action. -/
theorem lPlusSide4_five_factor_transport
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    ∃ E : LPlusGluedDart s.longest s.hqMode s.hτ ≃
        LPlusGluedDart s'.longest s'.hqMode s'.hτ,
      (∀ d, E (lPlusGluedCorrectedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk d) =
        lPlusGluedCorrectedRotation s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk (E d)) ∧
      (∀ d, E (lPlusPrefixExtendedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk d) =
        lPlusPrefixExtendedRotation s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk (E d)) ∧
      (∀ d, E (lPlusPrimedExtendedRotation s.hτ s.hqMode s.hfin d) =
        lPlusPrimedExtendedRotation s'.hτ s'.hqMode s'.hfin (E d)) ∧
      (∀ (a : Fin ((kmswStage (shiftedStream s.W 0)
          (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse.length) × Bool)
        (a' : Fin ((kmswStage (shiftedStream s'.W 0)
          (boundaryHitTime (shiftedStream s'.W 0) s'.h k)).UL.dropLast.reverse.length) × Bool),
        a.1.val = a'.1.val → a.2 = a'.2 →
          E (lPlusUpperLeftGluedDart s.hτ s.hqMode s.hfin hk a) =
            lPlusUpperLeftGluedDart s'.hτ s'.hqMode s'.hfin hk a') := by
  obtain ⟨E, hP, hPE, hTE, hHE, hBE, hPort⟩ := lPlusSide4_extended_transport x k r r' s s' hk hr
  let PE := lPlusPrefixExtendedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  let PE' := lPlusPrefixExtendedRotation s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
  let TE := lPlusPrimedExtendedRotation s.hτ s.hqMode s.hfin
  let TE' := lPlusPrimedExtendedRotation s'.hτ s'.hqMode s'.hfin
  let HE := lPlusHattedExtendedRotation s.hτ s.hqMode
  let HE' := lPlusHattedExtendedRotation s'.hτ s'.hqMode
  let BE := lPlusBetaCornerRotation s.hτ s.hqMode
  let BE' := lPlusBetaCornerRotation s'.hτ s'.hqMode
  let A := (kmswStage (shiftedStream s.W 0) (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse
  let B := (kmswStage (shiftedStream s'.W 0) (boundaryHitTime (shiftedStream s'.W 0) s'.h k)).UL.dropLast.reverse
  have hAB : A = B := lPlusSourceWitnessAligned_upperLeftList_eq x k r r' s s' hr
  have hlen : A.length = B.length := congrArg List.length hAB
  let F := Equiv.prodCongr (finCongr hlen) (Equiv.refl Bool)
  let IU := lPlusUpperLeftGluedDart s.hτ s.hqMode s.hfin hk
  let IU' := lPlusUpperLeftGluedDart s'.hτ s'.hqMode s'.hfin hk
  have hIU (a : Fin A.length × Bool) : E (IU a) = IU' (F a) :=
    hPort a (F a) rfl rfl
  let UE := lPlusUpperLeftCornerRotation s.hτ s.hqMode s.hfin hk
  let UE' := lPlusUpperLeftCornerRotation s'.hτ s'.hqMode s'.hfin hk
  have hUE (d) : E (UE d) = UE' (E d) := by
    by_cases hd : d ∈ Set.range IU
    · obtain ⟨a, rfl⟩ := hd
      have hs : UE (IU a) = IU (lPlusUpperLeftCornerPerm A.length a) :=
        Equiv.Perm.extendDomain_apply_image _ _ a
      have hs' : UE' (IU' (F a)) = IU' (lPlusUpperLeftCornerPerm B.length (F a)) :=
        Equiv.Perm.extendDomain_apply_image _ _ (F a)
      rw [hs, hIU, hIU, lPlusSide4_corner_transport hlen]
      exact hs'.symm
    · have hd' : E d ∉ Set.range IU' := by
        rintro ⟨b, hb⟩
        obtain ⟨a, rfl⟩ := F.surjective b
        exact hd ⟨a, E.injective ((hIU a).trans hb)⟩
      have hs : UE d = d := Equiv.Perm.extendDomain_apply_not_subtype _ _ hd
      have hs' : UE' (E d) = E d := Equiv.Perm.extendDomain_apply_not_subtype _ _ hd'
      rw [hs, hs']
  let C := lPlusGluedCorrectedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  let C' := lPlusGluedCorrectedRotation s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
  have hC (d) : E (C d) = C' (E d) := by
    change E (HE (BE (TE (UE (PE d))))) = HE' (BE' (TE' (UE' (PE' (E d)))))
    rw [hHE, hBE, hTE, hUE, hPE]
  exact ⟨E, hC, hPE, hTE, hPort⟩

/-- Helper toward Lemma 5.5: equal presentation codes of aligned witnesses
conjugate the entire corrected rotation 4 on the glued dart carriers.
The finite corner, both terminal swaps, and the empty prefix are included. -/
theorem lPlusSourceWitnessAligned_rotation4_conjugacy_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    ∃ E : LPlusGluedDart s.longest s.hqMode s.hτ ≃
        LPlusGluedDart s'.longest s'.hqMode s'.hτ,
      ∀ d, E (lPlusGluedCorrectedRotation4 s.hτ s.hp s.P s.hqMode s.Tpath
          s.hfin s.hleft hk d) =
        lPlusGluedCorrectedRotation4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath
          s'.hfin s'.hleft hk (E d) := by
  obtain ⟨E, hC, hPE, hTE, hIU⟩ := lPlusSide4_five_factor_transport x k r r' s s' hk hr
  let PE := lPlusPrefixExtendedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  let PE' := lPlusPrefixExtendedRotation s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
  let TE := lPlusPrimedExtendedRotation s.hτ s.hqMode s.hfin
  let TE' := lPlusPrimedExtendedRotation s'.hτ s'.hqMode s'.hfin
  let C := lPlusGluedCorrectedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  let C' := lPlusGluedCorrectedRotation s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
  let A := (kmswStage (shiftedStream s.W 0) (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse
  let B := (kmswStage (shiftedStream s'.W 0) (boundaryHitTime (shiftedStream s'.W 0) s'.h k)).UL.dropLast.reverse
  have hAB : A = B := lPlusSourceWitnessAligned_upperLeftList_eq x k r r' s s' hr
  have hlen : A.length = B.length := congrArg List.length hAB
  let IU := lPlusUpperLeftGluedDart s.hτ s.hqMode s.hfin hk
  let IU' := lPlusUpperLeftGluedDart s'.hτ s'.hqMode s'.hfin hk
  let C2 := lPlusGluedBlockRotation2 s.hτ s.hqMode s.hfin hk s.hp s.P s.Tpath s.hleft
  let C2' := lPlusGluedBlockRotation2 s'.hτ s'.hqMode s'.hfin hk s'.hp s'.P s'.Tpath s'.hleft
  have hterm (hn : 0 < A.length) (hn' : 0 < B.length) :
      E (IU (⟨A.length - 1, by change A.length - 1 < A.length; omega⟩, false)) =
        IU' (⟨B.length - 1, by change B.length - 1 < B.length; omega⟩, false) := by
    apply hIU
    · change A.length - 1 = B.length - 1
      omega
    · rfl
  have hC2 (d) : E (C2 d) = C2' (E d) := by
    by_cases hn : 0 < A.length
    · have hn' : 0 < B.length := by omega
      let t := IU (⟨A.length - 1, by change A.length - 1 < A.length; omega⟩, false)
      let t' := IU' (⟨B.length - 1, by change B.length - 1 < B.length; omega⟩, false)
      have htt : E t = t' := hterm hn hn'
      change E ((if h : 0 < A.length then
        Equiv.swap (C (IU (⟨A.length - 1, by change A.length - 1 < A.length; omega⟩, false)))
          (TE (IU (⟨A.length - 1, by change A.length - 1 < A.length; omega⟩, false))) * C else C) d) = _
      rw [dite_eq_left hn]
      change E (Equiv.swap (C t) (TE t) (C d)) = C2' (E d)
      have hs := (E.injective.swap_apply (C t) (TE t) (C d)).symm
      rw [hC, hTE, hC, htt] at hs
      have hout : C2' (E d) = Equiv.swap (C' t') (TE' t') (C' (E d)) := by
        dsimp only [C2', lPlusGluedBlockRotation2]
        rw [dite_eq_left hn']
        rfl
      exact hs.trans hout.symm
    · have hn' : ¬ 0 < B.length := by omega
      change E ((if h : 0 < A.length then _ else C) d) =
        (if h : 0 < B.length then _ else C') (E d)
      rw [dite_eq_right hn, dite_eq_right hn']
      exact hC d
  refine ⟨E, ?_⟩
  intro d
  by_cases hn : 0 < A.length
  · have hn' : 0 < B.length := by omega
    let t := IU (⟨A.length - 1, by change A.length - 1 < A.length; omega⟩, false)
    let t' := IU' (⟨B.length - 1, by change B.length - 1 < B.length; omega⟩, false)
    have htt : E t = t' := hterm hn hn'
    rw [lPlusGluedCorrectedRotation4, dite_eq_left hn,
      lPlusGluedCorrectedRotation4, dite_eq_left hn']
    change E (Equiv.swap t (PE t) (C2 d)) = Equiv.swap t' (PE' t') (C2' (E d))
    have hs := (E.injective.swap_apply t (PE t) (C2 d)).symm
    rw [hPE, hC2, htt] at hs
    exact hs
  · have hn' : ¬ 0 < B.length := by omega
    rw [lPlusGluedCorrectedRotation4, dite_eq_right hn,
      lPlusGluedCorrectedRotation4, dite_eq_right hn']
    exact hC2 d


































































































































end DirectedDistances.PaperProofs.Section5

/- Validation (2026-11-06): all eight public declarations were checked with
 Every result reported exactly [propext, Classical.choice, Quot.sound].
 The probe compile exited 0; all probes were removed before the final compile.
 Development compile exits, in order (before the axiom-probe/final passes):
 0,1,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,0.
 Failures were elaboration/inference issues and default-heartbeat timeouts;
 the finite-corner transport was completed by explicit range/complement cases.
 No options, imported sources, dependency artifacts or project pins changed. -/
