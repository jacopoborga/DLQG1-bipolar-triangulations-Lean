/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSide4CrossWitness2

/-! Cross-witness transport of the corrected nonnegative left side. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: at a nonnegative boundary hit, an allocated
edge is present in the infinite run exactly when its stopped flag is true.
The upper-right list is empty and lower-left edges stay missing. -/
theorem lPlus_edgePresent_iff_hitStage_present
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (k : ℤ) (hk : 0 ≤ k)
    (e : ℕ) (he : e < (kmswStage w (boundaryHitTime w h k)).nextEdge) :
    EdgePresent w e ↔ (kmswStage w (boundaryHitTime w h k)).present e = true := by
  have hUR : (kmswStage w (boundaryHitTime w h k)).UR = [] := by
    by_cases hk0 : k = 0
    · subst k
      rw [boundaryHitTime_zero]
      rfl
    · exact boundaryHit_right_UR_empty w h (by omega)
  constructor
  · intro hp
    cases hf : (kmswStage w (boundaryHitTime w h k)).present e with
    | true => rfl
    | false =>
      have hm := (kmswStage_missing_edges_exactly_UR_append_LL
        w (boundaryHitTime w h k) e he).mp hf
      have hLL : e ∈ (kmswStage w (boundaryHitTime w h k)).LL := by
        simpa only [hUR, List.nil_append] using hm
      exact (rMinus_LL_not_present w (boundaryHitTime w h k) e hLL hp).elim
  · intro hp
    exact ⟨_, he, hp⟩

/-- Helper toward Lemma 5.5: equal aligned codes determine directed
presence on every retained prefix edge, including the empty prefix at zero. -/
theorem lPlusSourceWitnessAligned_prefixEdgePresent_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code)
    (a : LPlusPrefixDart s.W s.h k) :
    EdgePresent (shiftedStream s.W 0) a.val.1 ↔
      EdgePresent (shiftedStream s'.W 0) a.val.1 := by
  have hcodes := (lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq
    x k r r' s.toLPlusSidePresentationSourceWitness
      s'.toLPlusSidePresentationSourceWitness hr).1
  have hstage := lPlusBoundaryHitStage_eq_of_code_eq s.W s'.W s.h s'.h k hcodes
  have he : a.val.1 < (kmswStage (shiftedStream s.W 0)
      (boundaryHitTime (shiftedStream s.W 0) s.h k)).nextEdge := by
    by_cases hkpos : 0 < k
    · have ha := (Set.ext_iff.mp (lPlusPrefixMinusEdges_eq_previousStage
        (W := s.W) (h := s.h) hkpos) a.val.1).mp a.property
      exact ha.trans_le (kmswStage_nextEdge_mono _ (Nat.sub_le _ _))
    · have hk0 : k = 0 := by omega
      subst k
      have ha := (Set.ext_iff.mp (boundaryGluingPrefixMinusEdges_zero s.W s.h)
        a.val.1).mp a.property
      exact ha.elim
  have he' := he
  rw [hstage] at he'
  rw [lPlus_edgePresent_iff_hitStage_present _ s.h k hk _ he,
    lPlus_edgePresent_iff_hitStage_present _ s'.h k hk _ he', hstage]

/-- Helper toward Lemma 5.5: the quotient-to-cell equivalence reads the
entire corrected rotation, including the terminal correction and index zero. -/
theorem LPlusSidePresentationSourceWitness.codeBlockCellEquiv4_rotation_iff
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k)
    (a b : LPlusGluedDart s.longest s.hqMode s.hτ) :
    geometricSideRelation
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
        .rotation (s.codeBlockCellEquiv4 x k r hk (.inr a))
          (s.codeBlockCellEquiv4 x k r hk (.inr b)) ↔
      lPlusGluedCorrectedRotation4 s.hτ s.hp s.P s.hqMode s.Tpath
        s.hfin s.hleft hk a = b :=
  lPlusCodeBlockSide4_rotation_glued_iff s.hτ s.hp s.P s.hqMode s.Tpath
    s.hfin s.hleft hk a b

/-- Helper toward Lemma 5.5: every hatted image edge is directed, so its
orientation relation reads exactly its original forward endpoint bit. -/
theorem LPlusSidePresentationSourceWitness.codeBlockCellEquiv4_hatted_oriented_iff
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k)
    (a : LPlusHattedDart
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode))
    (v : Sum (LPlusGluedVertex s.longest s.hqMode s.hτ)
      (LPlusGluedDart s.longest s.hqMode s.hτ)) :
    geometricSideRelation
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
        .oriented (s.codeBlockCellEquiv4 x k r hk (.inr ⟦Sum.inr (Sum.inr a)⟧))
          (s.codeBlockCellEquiv4 x k r hk v) ↔ a.val.2 = false := by
  change (EdgePresent (shiftedStream s.W 0)
    (boundaryGluingHatEdgeMap s.W s.h k s.hτ a.val.1) ∧ a.val.2 = false) ↔ _
  have hp := (boundaryGluing_nonneg_right_present s.hτ s.hp s.P s.hqMode a.val.1).2
  exact ⟨And.right, fun hb => ⟨hp, hb⟩⟩

/-- Helper toward Lemma 5.5: the prefix representative's orientation is
preserved at equal permanent prefix IDs, including missing geometric edges. -/
theorem lPlusSourceWitnessAligned_codeBlockCellEquiv4_prefix_oriented_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code)
    (a : LPlusPrefixDart s.W s.h k) (a' : LPlusPrefixDart s'.W s'.h k)
    (ha : a'.val = a.val) :
    geometricSideRelation
      (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
      .oriented
      (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inr ⟦Sum.inl a⟧))
      (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inr ⟦Sum.inl a⟧)) ↔
    geometricSideRelation
      (lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk)
      .oriented
      (s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r' hk (.inr ⟦Sum.inl a'⟧))
      (s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r' hk (.inr ⟦Sum.inl a'⟧)) := by
  change (EdgePresent (shiftedStream s.W 0) a.val.1 ∧ a.val.2 = false) ↔
    (EdgePresent (shiftedStream s'.W 0) a'.val.1 ∧ a'.val.2 = false)
  rw [ha]
  exact and_congr (lPlusSourceWitnessAligned_prefixEdgePresent_iff x k r r' s s' hk hr a)
    Iff.rfl

/-- Helper toward Lemma 5.5: naturality of the block transport. -/
private theorem lPlusSide4_list_get_eq {A B : List ℕ} (h : A = B)
    (i : Fin A.length) (j : Fin B.length) (hij : i.val = j.val) : A[i.val] = B[j.val] := by
  cases h
  have hi : i = j := Fin.ext hij
  cases hi
  rfl

/-- Helper toward Lemma 5.5: the indexed seam has its hatted-block
representative, with the original forward dart bit. -/
@[expose] noncomputable def LPlusSidePresentationSourceWitness.gluedSeam4
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (i : ℕ) :
    LPlusGluedDart s.longest s.hqMode s.hτ :=
  lPlusHattedGluedDart (hτ := s.hτ) (hqMode := s.hqMode)
    ⟨(lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode).seam i,
      lMinus_hatted_seam_mem (if s.longest then XDP.ldp else XDP.sdp)
        ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩ i⟩

/-- Helper toward Lemma 5.5: the hatted seam representative is exactly
the actual marked seam in the quotient-to-cell equivalence. -/
theorem LPlusSidePresentationSourceWitness.codeBlockCellEquiv4_seam_iff
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k)
    (i : ℕ) (a : LPlusGluedDart s.longest s.hqMode s.hτ)
    (v : Sum (LPlusGluedVertex s.longest s.hqMode s.hτ)
      (LPlusGluedDart s.longest s.hqMode s.hτ)) :
    geometricSideRelation
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
        (.seam i) (s.codeBlockCellEquiv4 x k r hk (.inr a))
          (s.codeBlockCellEquiv4 x k r hk v) ↔
      s.gluedSeam4 x k r i = a := by
  let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  have hs : (D (s.gluedSeam4 x k r i)).val = m0GeodesicSeam s.P i := by
    exact congrArg (fun e : ℕ => (e, false))
      ((boundaryGluing_geodesicIdentification s.W s.h k s.hτ s.longest s.hqMode
        s.hp s.Tpath s.P s.hfin s.hleft i).symm)
  change m0GeodesicSeam s.P i = (D a).val ↔ _
  rw [← hs]
  exact ⟨fun h => D.injective (Subtype.ext h), fun h => congrArg (fun d => (D d).val) h⟩

/-- Helper toward Lemma 5.5: a retained face corner gives the rotation
from its successor to the opposite initial dart. This is the inverse-rotation
convention; the retained-face condition is still required for the converse. -/
theorem LPlusSidePresentationSourceWitness.codeBlockCellEquiv4_faceNext_imp_rotation
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k)
    (a b : LPlusGluedDart s.longest s.hqMode s.hτ)
    (hab : geometricSideRelation
      (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
      .faceNext (s.codeBlockCellEquiv4 x k r hk (.inr a))
        (s.codeBlockCellEquiv4 x k r hk (.inr b))) :
    lPlusGluedCorrectedRotation4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk b =
      lPlusSide4GluedOpposite a := by
  let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  have hop : (D (lPlusSide4GluedOpposite a)).val = ((D a).val.1, !(D a).val.2) := by
    induction a using Quotient.inductionOn with
    | h a => exact lPlusSide4BlockOpposite_image s.hτ a
  have hface : kmswInfFaceSucc (shiftedStream s.W 0) (s.H.1 0) (D a).val =
      (D b).val := hab.2
  change (kmswInfRot (shiftedStream s.W 0) (s.H.1 0)).symm
    ((D a).val.1, !(D a).val.2) = (D b).val at hface
  have hrot : (kmswInfRot (shiftedStream s.W 0) (s.H.1 0)) (D b).val =
      (D (lPlusSide4GluedOpposite a)).val := by
    rw [hop]
    exact (congrArg (kmswInfRot (shiftedStream s.W 0) (s.H.1 0)) hface).symm.trans
      ((kmswInfRot (shiftedStream s.W 0) (s.H.1 0)).apply_symm_apply _)
  apply (lPlusGluedCorrectedRotation4_rotation_iff s.hτ s.hp s.P s.hqMode s.Tpath
    s.hfin s.hleft hk b (lPlusSide4GluedOpposite a)).mpr
  refine ⟨1, by omega, ?_, ?_⟩
  · exact hrot
  · intro j hj hj1
    omega


/-- Helper toward Lemma 5.5: naturality of the block transport. -/
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

/-- Helper toward Lemma 5.5: naturality of the block transport. -/
private theorem lPlusSide4_corner_transport {n m : ℕ} (h : n = m)
    (d : Fin n × Bool) :
    (Equiv.prodCongr (finCongr h) (Equiv.refl Bool)) (lPlusUpperLeftCornerPerm n d) =
      lPlusUpperLeftCornerPerm m ((Equiv.prodCongr (finCongr h) (Equiv.refl Bool)) d) := by
  cases h
  rfl

/-- Helper toward Lemma 5.5: one common quotient transport preserves
root, both endpoints, opposite darts, the complete corrected rotation, and
the indexed seam, retaining its actions on all three source blocks. -/
theorem lPlusSourceWitnessAligned_endpointQuotient_rotation4_transport
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let M := lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode
    let N := lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode
    ∃ (fD : LPlusBlockDart s.W s.h k M ≃ LPlusBlockDart s'.W s'.h k N)
      (qV : LPlusGluedVertex s.longest s.hqMode s.hτ ≃
        LPlusGluedVertex s'.longest s'.hqMode s'.hτ)
      (qD : LPlusGluedDart s.longest s.hqMode s.hτ ≃
        LPlusGluedDart s'.longest s'.hqMode s'.hτ),
      (∀ a, qD ⟦a⟧ = ⟦fD a⟧) ∧
      qV ⟦Sum.inr (Sum.inl 1)⟧ = ⟦Sum.inr (Sum.inl 1)⟧ ∧
      (∀ a, qV ⟦s.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r a⟧ =
        ⟦s'.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r' (fD a)⟧) ∧
      (∀ a, qD (lPlusSide4GluedOpposite a) = lPlusSide4GluedOpposite (qD a)) ∧
      (∀ d, qD (lPlusGluedCorrectedRotation4 s.hτ s.hp s.P s.hqMode s.Tpath
        s.hfin s.hleft hk d) =
        lPlusGluedCorrectedRotation4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath
          s'.hfin s'.hleft hk (qD d)) ∧
      (∀ i, qD (s.toLPlusSidePresentationSourceWitness.gluedSeam4 x k r i) =
        s'.toLPlusSidePresentationSourceWitness.gluedSeam4 x k r' i) ∧
      (∀ a : LPlusPrefixDart s.W s.h k,
        ∃ a' : LPlusPrefixDart s'.W s'.h k,
          fD (.inl a) = .inl a' ∧ a'.val = a.val) ∧
      (∀ a : LPlusPrimedDart, fD (.inr (.inl a)) = .inr (.inl a)) ∧
      ∃ phi : GeometricSideMarkedIso M N,
        ∀ a : LPlusHattedDart M, ∃ a' : LPlusHattedDart N,
          fD (.inr (.inr a)) = .inr (.inr a') ∧
            phi.equiv (.inr a) = .inr a' := by
  obtain ⟨phi, fV, fD, qV, qD, hqV, hqD, hPV, hTV, hHV, hPD, hTD, hHD⟩ :=
    lPlusSourceWitnessAligned_gluedQuotientEquivs_of_presentation_codes_eq
      x k r r' s s' hk hr
  let e := s.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r
  let e' := s'.toLPlusSidePresentationSourceWitness.blockEndpoint4 x k r'
  have hendpoint (a) : fV (e a) = e' (fD a) := by
    rcases a with a | (a | a)
    · obtain ⟨a', ha, hav⟩ := hPD a
      obtain ⟨v', hv, hvv⟩ := hPV
        ⟨kmswLimitDartVertex (shiftedStream s.W 0) a.val,
          (show LPlusPrefixVertex s.W s.h k from
            (e (.inl a)).getLeft (by rfl)).property⟩
      change fV (.inl _) = _
      rw [hv, ha]
      apply congrArg Sum.inl
      apply Subtype.ext
      exact hvv.trans ((lPlusSourceWitnessAligned_prefixDartEndpoint_eq
        x k r r' s s' hk hr a).trans
          (congrArg (kmswLimitDartVertex (shiftedStream s'.W 0)) hav.symm))
    · change fV (.inr (.inl _)) = _
      rw [hTV, hTD]
      have hc := lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq
        x k r r' s s' hr
      change Sum.inr (Sum.inl (kmswLimitDartVertex _ a)) =
        Sum.inr (Sum.inl (kmswLimitDartVertex _ a))
      rw [hc]
    · obtain ⟨a', ha, hpa⟩ := hHD a
      let v := (e (.inr (.inr a))).getRight (by rfl) |>.getRight (by rfl)
      obtain ⟨v', hv, hpv⟩ := hHV v
      change fV (.inr (.inr v)) = _
      rw [hv, ha]
      have hi := (phi.relation_iff .incident (.inr a) (.inl v)).mp
        (show geometricSideRelation _ .incident (.inr a) (.inl v) from rfl)
      rw [hpa, hpv] at hi
      exact congrArg (fun v => Sum.inr (Sum.inr v)) (Subtype.ext hi.symm)
  have hblock (a) : fD (lPlusSide4BlockOpposite a) = lPlusSide4BlockOpposite (fD a) := by
    rcases a with a | (a | a)
    · obtain ⟨a', ha', hav⟩ := hPD a
      obtain ⟨b', hb', hbv⟩ := hPD ⟨(a.val.1, !a.val.2), a.property⟩
      change fD (.inl ⟨(a.val.1, !a.val.2), a.property⟩) = _
      rw [hb', ha']
      apply congrArg Sum.inl
      apply Subtype.ext
      exact hbv.trans (congrArg (fun d : ℕ × Bool => (d.1, !d.2)) hav.symm)
    · change fD (.inr (.inl (a.1, !a.2))) = _
      rw [hTD, hTD]
      rfl
    · obtain ⟨a', ha', hpa⟩ := hHD a
      obtain ⟨b', hb', hpb⟩ := hHD ⟨(a.val.1, !a.val.2), a.property⟩
      change fD (.inr (.inr ⟨(a.val.1, !a.val.2), a.property⟩)) = _
      rw [hb', ha']
      have hop := (phi.relation_iff .opposite (.inr a)
        (.inr ⟨(a.val.1, !a.val.2), a.property⟩)).mp
          (show geometricSideRelation _ .opposite _ _ from rfl)
      rw [hpa, hpb] at hop
      exact congrArg (fun d => Sum.inr (Sum.inr d)) (Subtype.ext hop.symm)
  have hRot : ∀ d, qD (lPlusGluedCorrectedRotation4 s.hτ s.hp s.P s.hqMode s.Tpath
      s.hfin s.hleft hk d) =
      lPlusGluedCorrectedRotation4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath
        s'.hfin s'.hleft hk (qD d) := by
    let E := qD
    have hP (a : LPlusPrefixDart s.W s.h k) (a' : LPlusPrefixDart s'.W s'.h k)
        (ha' : a'.val = a.val) :
        E (lPlusPrefixGluedDart (hτ := s.hτ) (hqMode := s.hqMode) a) =
          lPlusPrefixGluedDart (hτ := s'.hτ) (hqMode := s'.hqMode) a' := by
      obtain ⟨b, hb, hba⟩ := hPD a
      have hbe : b = a' := Subtype.ext (hba.trans ha'.symm)
      change qD ⟦Sum.inl a⟧ = ⟦Sum.inl a'⟧
      rw [hqD, hb, hbe]
    have hT (a : LPlusPrimedDart) :
        E (lPlusPrimedGluedDart (hτ := s.hτ) (hqMode := s.hqMode) a) =
          lPlusPrimedGluedDart (hτ := s'.hτ) (hqMode := s'.hqMode) a := by
      change qD ⟦Sum.inr (Sum.inl a)⟧ = ⟦Sum.inr (Sum.inl a)⟧
      rw [hqD, hTD]
    have hH (a : LPlusHattedDart
        (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
        E (lPlusHattedGluedDart (hτ := s.hτ) (hqMode := s.hqMode) a) =
          lPlusHattedGluedDart (hτ := s'.hτ) (hqMode := s'.hqMode)
            (lMinusMarkedDartMap phi a) := by
      obtain ⟨b, hb, hphi⟩ := hHD a
      have hbe : b = lMinusMarkedDartMap phi a := by
        exact Sum.inr.inj (hphi.symm.trans (lMinusMarkedDartMap_cell phi a))
      change qD ⟦Sum.inr (Sum.inr a)⟧ = ⟦Sum.inr (Sum.inr _)⟧
      rw [hqD, hb, hbe]
  
    have hPort
        (a : Fin ((kmswStage (shiftedStream s.W 0)
          (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.reverse.length) × Bool)
        (a' : Fin ((kmswStage (shiftedStream s'.W 0)
          (boundaryHitTime (shiftedStream s'.W 0) s'.h k)).UL.dropLast.reverse.length) × Bool)
        (ha : a.1.val = a'.1.val) (hb : a.2 = a'.2) :
        E (lPlusUpperLeftGluedDart s.hτ s.hqMode s.hfin hk a) =
          lPlusUpperLeftGluedDart s'.hτ s'.hqMode s'.hfin hk a' := by
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
    have hIUlocal (a : Fin A.length × Bool) : E (IU a) = IU' (F a) :=
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
        rw [hs, hIUlocal, hIUlocal, lPlusSide4_corner_transport hlen]
        exact hs'.symm
      · have hd' : E d ∉ Set.range IU' := by
          rintro ⟨b, hb⟩
          obtain ⟨a, rfl⟩ := F.surjective b
          exact hd ⟨a, E.injective ((hIUlocal a).trans hb)⟩
        have hs : UE d = d := Equiv.Perm.extendDomain_apply_not_subtype _ _ hd
        have hs' : UE' (E d) = E d := Equiv.Perm.extendDomain_apply_not_subtype _ _ hd'
        rw [hs, hs']
    let C := lPlusGluedCorrectedRotation s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    let C' := lPlusGluedCorrectedRotation s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
    have hC (d) : E (C d) = C' (E d) := by
      change E (HE (BE (TE (UE (PE d))))) = HE' (BE' (TE' (UE' (PE' (E d)))))
      rw [hHE, hBE, hTE, hUE, hPE]
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
      apply hPort
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
  have hSeam (i : ℕ) :
      qD (s.toLPlusSidePresentationSourceWitness.gluedSeam4 x k r i) =
        s'.toLPlusSidePresentationSourceWitness.gluedSeam4 x k r' i := by
    let a : LPlusHattedDart
        (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode) :=
      ⟨_, lMinus_hatted_seam_mem (if s.longest then XDP.ldp else XDP.sdp)
        ⟨boundaryFutureHattedPath k s.W, s.hqMode⟩ i⟩
    obtain ⟨a', ha, hphi⟩ := hHD a
    change qD ⟦Sum.inr (Sum.inr a)⟧ = ⟦Sum.inr (Sum.inr _)⟧
    rw [hqD, ha]
    apply congrArg (fun d => (⟦Sum.inr (Sum.inr d)⟧ :
      LPlusGluedDart s'.longest s'.hqMode s'.hτ))
    apply Subtype.ext
    have hs := (phi.relation_iff (.seam i) (.inr a) (.inr a)).mp
      (show geometricSideRelation _ (.seam i) (.inr a) (.inr a) from rfl)
    rw [hphi] at hs
    exact hs.symm
  refine ⟨fD, qV, qD, hqD, ?_, ?_, ?_, hRot, hSeam, hPD, hTD, phi, hHD⟩
  · rw [hqV, hTV]
  · intro a
    rw [hqV, hendpoint]
  · intro a
    induction a using Quotient.inductionOn with
    | h a =>
      change qD ⟦lPlusSide4BlockOpposite a⟧ = lPlusSide4GluedOpposite (qD ⟦a⟧)
      rw [hqD, hqD, hblock]
      rfl


/-- Helper toward Lemma 5.5: a single cell equivalence preserves vertices,
root, incidence, opposite, corrected rotation, every indexed seam, and the empty
finite target relation, throughout the nonnegative domain. The same equivalence
preserves orientation on every cell with a prefix or hatted representative.
Exclusively primed representatives are not covered by the orientation clause. -/
theorem lPlusSourceWitnessAligned_codeBlockCellEquiv4_vertex_root_incident_opposite_rotation_seam
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let B := lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    let B' := lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
    ∃ F : GeometricSideCell B ≃ GeometricSideCell B',
      (∀ t ∈ ({TruncationRelation.vertex, .root, .incident, .opposite, .rotation, .target} ∪ Set.range TruncationRelation.seam : Set TruncationRelation),
        ∀ u v, geometricSideRelation B t u v ↔
          geometricSideRelation B' t (F u) (F v)) ∧
      ∀ u v,
        ((∃ a : LPlusPrefixDart s.W s.h k,
          u = s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk
            (.inr ⟦Sum.inl a⟧)) ∨
        (∃ a : LPlusHattedDart
            (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode),
          u = s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk
            (.inr ⟦Sum.inr (Sum.inr a)⟧))) →
        (geometricSideRelation B .oriented u v ↔
          geometricSideRelation B' .oriented (F u) (F v)) := by
  obtain ⟨fD, qV, qD, hqD, hroot, he, hop, hrot, hseam, hPD, _, ⟨phi, hHD⟩⟩ :=
    lPlusSourceWitnessAligned_endpointQuotient_rotation4_transport x k r r' s s' hk hr
  let E := s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk
  let E' := s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r' hk
  let Q := Equiv.sumCongr qV qD
  let F := E.symm.trans (Q.trans E')
  have hF (a) : F (E a) = E' (Q a) := by
    change E' (Q (E.symm (E a))) = E' (Q a)
    rw [E.symm_apply_apply]
  refine ⟨F, ?_, ?_⟩
  · intro t ht u v
    obtain ⟨a, rfl⟩ := E.surjective u
    obtain ⟨b, rfl⟩ := E.surjective v
    rw [hF, hF]
    rcases ht with ht | ⟨i, rfl⟩
    · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_vertex_iff,
          s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_vertex_iff]
        cases a <;> rfl
      · rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_root_iff,
          s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_root_iff]
        have hQ : Q (.inl ⟦Sum.inr (Sum.inl 1)⟧) = .inl ⟦Sum.inr (Sum.inl 1)⟧ :=
          congrArg Sum.inl hroot
        rw [← hQ, Q.injective.eq_iff]
      · cases a with
        | inl a => rfl
        | inr a =>
          cases b with
          | inr b => rfl
          | inl b =>
            induction a using Quotient.inductionOn with
            | h a =>
              change geometricSideRelation _ .incident (E (.inr ⟦a⟧)) (E (.inl b)) ↔
                geometricSideRelation _ .incident (E' (.inr (qD ⟦a⟧))) (E' (.inl (qV b)))
              rw [hqD,
                s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_incident_mk_iff,
                s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_incident_mk_iff,
                ← he, qV.injective.eq_iff]
      · cases a with
        | inl a => rfl
        | inr a =>
          cases b with
          | inl b => rfl
          | inr b =>
            change geometricSideRelation _ .opposite (E (.inr a)) (E (.inr b)) ↔
              geometricSideRelation _ .opposite (E' (.inr (qD a))) (E' (.inr (qD b)))
            rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_opposite_iff,
              s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_opposite_iff,
              ← hop, qD.injective.eq_iff]
    
      · cases a with
        | inl a => rfl
        | inr a =>
          cases b with
          | inl b => rfl
          | inr b =>
            change geometricSideRelation _ .rotation (E (.inr a)) (E (.inr b)) ↔
              geometricSideRelation _ .rotation (E' (.inr (qD a))) (E' (.inr (qD b)))
            rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_rotation_iff,
              s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_rotation_iff,
              ← hrot, qD.injective.eq_iff]
      · cases a <;> cases b <;> rfl
    · cases a with
      | inl a => rfl
      | inr a =>
        change geometricSideRelation _ (.seam i) (E (.inr a)) (E b) ↔
          geometricSideRelation _ (.seam i) (E' (.inr (qD a))) (E' (Q b))
        rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_seam_iff,
          s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_seam_iff,
          ← hseam, qD.injective.eq_iff]
  
  · intro u v hu
    obtain ⟨b, rfl⟩ := E.surjective v
    rcases hu with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · obtain ⟨a', ha, hval⟩ := hPD a
      rw [hF, hF]
      change (EdgePresent (shiftedStream s.W 0) a.val.1 ∧ a.val.2 = false) ↔
        geometricSideRelation _ .oriented (E' (.inr (qD ⟦Sum.inl a⟧))) (E' (Q b))
      rw [hqD, ha]
      change (EdgePresent (shiftedStream s.W 0) a.val.1 ∧ a.val.2 = false) ↔
        (EdgePresent (shiftedStream s'.W 0) a'.val.1 ∧ a'.val.2 = false)
      rw [hval]
      exact and_congr
        (lPlusSourceWitnessAligned_prefixEdgePresent_iff x k r r' s s' hk hr a) Iff.rfl
    · obtain ⟨a', ha, hphi⟩ := hHD a
      rw [hF, hF]
      change geometricSideRelation _ .oriented (E (.inr ⟦Sum.inr (Sum.inr a)⟧)) (E b) ↔
        geometricSideRelation _ .oriented
          (E' (.inr (qD ⟦Sum.inr (Sum.inr a)⟧))) (E' (Q b))
      rw [hqD, ha,
        s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_hatted_oriented_iff,
        s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_hatted_oriented_iff]
      have ho := phi.relation_iff .oriented (.inr a) (.inr a)
      rw [hphi] at ho
      have hp : a.val.1 ∈
          (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode).present := by
        change EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s.W))) _
        rw [boundaryGluing_decoded_stream s.W s.h k s.hτ]
        exact hatCodes_edge_present _ s.hτ _
      have hp' : a'.val.1 ∈
          (lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode).present := by
        change EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s'.W))) _
        rw [boundaryGluing_decoded_stream s'.W s'.h k s'.hτ]
        exact hatCodes_edge_present _ s'.hτ _
      change (_ ∧ a.val.2 = false) ↔ (_ ∧ a'.val.2 = false) at ho
      simpa only [hp, hp', true_and] using ho
















































































end DirectedDistances.PaperProofs.Section5








