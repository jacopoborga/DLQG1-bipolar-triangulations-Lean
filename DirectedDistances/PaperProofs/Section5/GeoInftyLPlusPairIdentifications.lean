/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusPairRotation

/-! Identifications of the measurable pair readers with aligned source geometry. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. Every exterior reader has the exact source
geometric dart, including the finite lower word and the shifted primed tail. -/
theorem lPlusPairBoundaryRawOption_identification
    (x : XDP) (k : ℤ) (hk : 0 ≤ k)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r) (i : ℕ) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    ∃ b : LPlusBlockDart s.W s.h k
        (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode),
      lPlusPairBoundaryRawOption x k z i = some (lPlusBlockDartRawLabel b) ∧
      lPlusBlockDartImage s.hτ b =
        m0GeodesicBoundaryDart (shiftedStream s.W 0) s.h k .left i := by
  dsimp only
  rw [lPlusPairBoundaryRawOption, lPlusPairBoundaryData_eq_of_aligned x k r s hk,
    Option.map_some]
  have hc := lMinus_primed_observation_code (longest := s.longest) s.hτ
  change hatLawPrimedCodes (boundaryFutureCode k s.W) = _ at hc
  have hcode := s.primedCode_eq.symm.trans hc
  by_cases hk0 : k = 0
  · subst k
    simp only [lt_self_iff_false, ↓reduceIte, List.length_nil, boundaryHitTime_zero,
      kmswStage, kmswInit, List.dropLast_singleton, zero_add, Nat.sub_zero,
      not_lt_zero]
    refine ⟨.inr (.inl (lMinusCodeExteriorBoundaryEdge r.code.2.2 i, true)), rfl, ?_⟩
    have hh := s.toLPlusSidePresentationSourceWitness.primedExteriorDart_tail_image
      x 0 r i (by rw [boundaryHitTime_zero]; change 0 ≤ i; omega)
    rw [← hcode] at hh
    simp only [boundaryHitTime_zero, kmswStage, kmswInit, List.length_nil,
      List.dropLast_singleton, zero_add, Nat.sub_zero] at hh
    have hidx : -(i : ℤ) - 1 = (0 : ℤ) - 1 - (i : ℤ) := by omega
    rw [hidx] at hh
    exact hh
  have hkpos : 0 < k := by omega
  simp only [hkpos, ↓reduceIte]
  let G := kmswStage (shiftedStream s.W 0) (boundaryHitTime (shiftedStream s.W 0) s.h k)
  let F := kmswStage (shiftedStream s.W 0) (boundaryHitTime (shiftedStream s.W 0) s.h k - 1)
  by_cases hi : i < (F.LL ++ F.LR).reverse.length
  · rw [dite_eq_left hi]
    let e := (F.LL ++ F.LR).reverse[i]
    have halloc : e < F.nextEdge := by
      have hm : e ∈ F.LL ++ F.LR := List.mem_reverse.mp (List.getElem_mem hi)
      apply (kmswStage_boundary_ids_lt_nextEdge (shiftedStream s.W 0)
        (boundaryHitTime (shiftedStream s.W 0) s.h k - 1)).2
      simp only [List.mem_append] at hm ⊢
      tauto
    have hpref : e ∈ boundaryGluingPrefixMinusEdges s.W s.h k := by
      rw [lPlusPrefixMinusEdges_eq_previousStage hkpos]
      exact halloc
    refine ⟨.inl ⟨(e, true), hpref⟩, rfl, ?_⟩
    exact congrArg (fun e => (e, true))
      (Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans
        (lPlus_previous_lower_reverse_get _ s.h k hkpos i hi)))
  · rw [dite_eq_right hi]
    let j := G.UL.dropLast.length + i - (F.LL ++ F.LR).reverse.length
    have hj : G.UL.dropLast.length ≤ j := by dsimp only [j]; omega
    refine ⟨.inr (.inl (lMinusCodeExteriorBoundaryEdge r.code.2.2 j, true)), rfl, ?_⟩
    have hLR : (F.LR.length : ℤ) = k := lPlus_previous_LR_length _ s.h k hkpos
    have hLL : G.LL = F.LL := by
      obtain ⟨m, hm, hstep, hur⟩ := lPlus_positive_hit_fresh _ s.h hkpos
      dsimp only [G, F]
      rw [hm]
      simp only [Nat.add_sub_cancel, kmswStage, kmswStep, hstep, kmswCodeStep,
        kmswStepOfStep, hur, State.addEdge]
      rfl
    have hindex : -((G.LL.length + j - G.UL.dropLast.length : ℕ) : ℤ) - 1 =
        k - 1 - (i : ℤ) := by
      rw [hLL]
      dsimp only [j]
      simp only [List.length_reverse, List.length_append] at hi ⊢
      omega
    have hh := s.toLPlusSidePresentationSourceWitness.primedExteriorDart_tail_image
      x k r j hj
    rw [← hcode] at hh
    change lMinusPrimedDartImage s.hτ (lMinusCodeExteriorBoundaryEdge r.code.2.2 j, true) =
      (boundaryOuterEdge (shiftedStream s.W 0) s.h
        (-((G.LL.length + j - G.UL.dropLast.length : ℕ) : ℤ) - 1), true) at hh
    rw [hindex] at hh
    exact hh

/-- Helper toward Lemma 5.5. Directed presence in the measurable edge
quotient is exactly ambient presence, including shared prefix and beta edges. -/
theorem lPlusPairPresent_identification
    (x : XDP) (k : ℤ) (hk : 0 ≤ k)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r)
    (a : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairPresent x k z (lPlusPairGluedDartId x k r s hk ⟦a⟧).1 ↔
      EdgePresent (shiftedStream s.W 0) (lPlusBlockDartImage s.hτ a).1 := by
  dsimp only
  let z : lPlusCertifiedCodingPairDomain x :=
    ⟨(r, boundaryFutureHattedPath k s.W),
      LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
  change lPlusPairPresent x k z
    (lPlusRawEdgeClosureId x k z.val (lPlusBlockDartRawLabel a).1) ↔ _
  have hlabel : (lPlusBlockDartRawLabel a).1 = lPlusBlockDartRawEdgeLabel a := by
    rcases a with a | (a | a) <;> rfl
  rw [hlabel]
  have hc := lMinus_primed_observation_code (longest := s.longest) s.hτ
  change hatLawPrimedCodes (boundaryFutureCode k s.W) = _ at hc
  have hcode := s.primedCode_eq.symm.trans hc
  have hpcode (e : ℕ) :
      (∃ n, e < (kmswMissingRootStage r.code.2.2 n).nextEdge ∧
        (kmswMissingRootStage r.code.2.2 n).present e = true) ↔
      PrimedEdgePresent (boundaryGluingFutureStream s.W s.h k) s.hτ e := by
    rw [hcode]
    rfl
  have hsound (b : LPlusRawEdge)
      (hb : lPlusRawEdgeClosureId x k z.val b =
        lPlusRawEdgeClosureId x k z.val (lPlusBlockDartRawEdgeLabel a)) :
      lPlusPairRawEdgeImage s.hτ b = (lPlusBlockDartImage s.hτ a).1 := by
    have hh := lPlusRawEdgeEqvGen_sound_of_aligned x k r s hk b _
      ((lPlusRawEdgeClosureId_eq_iff x k z.val b _).mp hb)
    have ha : lPlusPairRawEdgeImage s.hτ (lPlusBlockDartRawEdgeLabel a) =
        (lPlusBlockDartImage s.hτ a).1 := by
      rcases a with a | (a | a) <;> rfl
    exact hh.trans ha
  have hprefix (e : ℕ) (he : e ∈ boundaryGluingPrefixMinusEdges s.W s.h k)
      (hp : EdgePresent (shiftedStream s.W 0) e)
      (heq : e = (lPlusBlockDartImage s.hτ a).1) :
      lPlusPairPresent x k z
        (lPlusRawEdgeClosureId x k z.val (lPlusBlockDartRawEdgeLabel a)) := by
    let b : LPlusBlockDart s.W s.h k
        (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode) :=
      .inl ⟨(e, false), he⟩
    exact Or.inl ⟨e,
      (lPlusPairRawEdgeAllocated_prefix_iff_of_aligned x k r s hk e).mpr he,
      (lPlusPairPrefixPresent_iff_of_aligned x k r s hk e he).mpr hp,
      (lPlusRawEdgeClosureId_eq_iff_of_aligned x k r s hk b a).mpr heq⟩
  constructor
  · rintro (⟨e, he, hp, hid⟩ | ⟨e, hp, hid⟩ | ⟨e, hp, hid⟩)
    · have he' := (lPlusPairRawEdgeAllocated_prefix_iff_of_aligned x k r s hk e).mp he
      have hp' := (lPlusPairPrefixPresent_iff_of_aligned x k r s hk e he').mp hp
      exact (hsound (.inl e) hid) ▸ hp'
    · have hp' := ((primedLimitEdgeMap_present_iff _ s.hτ e).mp
        ((hpcode e).mp hp)).1
      obtain ⟨n, hn, hpres⟩ := hp'
      have hp'' : EdgePresent (shiftedStream s.W 0)
          (boundaryGluingPrimedEdgeMap s.W s.h k s.hτ e) := by
        rw [boundaryGluingPrimedEdgeMap, Function.comp_apply, boundaryGluingEdgeMap,
          kmswWindowEdgeMapInf_eq_stage _ _ n _ hn]
        exact ⟨_, (kmswWindowPatchData_rel _ _ n).edge_bound _ hn,
          (kmswWindowPatchData_rel _ _ n).present _ hn hpres⟩
      exact (hsound (.inr (.inl e)) hid) ▸ hp''
    · have hp' := (boundaryGluing_nonneg_right_present s.hτ s.hp s.P s.hqMode e).2
      exact (hsound (.inr (.inr e)) hid) ▸ hp'
  · intro hp
    rcases a with a | (a | a)
    · exact hprefix a.val.1 a.property hp rfl
    · let e := boundaryGluingPrimedEdgeMap s.W s.h k s.hτ a.1
      by_cases he : e ∈ boundaryGluingPrefixMinusEdges s.W s.h k
      · exact hprefix e he hp rfl
      · have hUL : e ∉ boundaryGluingUpperLeftEdges s.W s.h k := by
          intro hu
          rw [← boundaryGluingPrefixMinusEdges_inter_primedEdges
            s.W s.h k s.hτ s.hfin hk] at hu
          exact he hu.1
        have hfuture := (lPlus_future_present_iff_of_not_upperLeft s.hτ
          (primedLimitEdgeMap _ s.hτ a.1) hUL).mpr hp
        rcases (s.toLPlusSidePresentationSourceWitness.primedFuturePresent_iff
          x k r a.1).mp hfuture with hprimed | ⟨i, hi⟩
        · exact Or.inr (Or.inl ⟨a.1, (hpcode a.1).mpr hprimed, rfl⟩)
        · let b := kmswLeftBoundaryEdge
            (hatCodes (boundaryGluingFutureStream s.W s.h k) s.hτ) i
          have hbe : boundaryGluingPrimedEdgeMap s.W s.h k s.hτ a.1 =
              boundaryGluingHatEdgeMap s.W s.h k s.hτ b := by
            rw [hi]
            exact (boundaryGluingBeta_edge_primed s.W s.h k s.hτ s.hfin i).1.symm
          have hrel := (lPlusPairPrimedHattedEdgeGluing_iff_of_aligned
            x k r s a.1 b).mpr hbe
          have hid := (lPlusRawEdgeClosureId_eq_iff x k z.val
            (.inr (.inl a.1)) (.inr (.inr b))).mpr (Relation.EqvGen.rel _ _ hrel)
          exact Or.inr (Or.inr ⟨b,
            lMinus_hatted_present x (lPlusCertifiedCodingPairPath x z) b, hid.symm⟩)
    · exact Or.inr (Or.inr ⟨a.val.1,
        lMinus_hatted_present x (lPlusCertifiedCodingPairPath x z) a.val.1, rfl⟩)

/-- Helper toward Lemma 5.5. The directed dart predicate agrees with
the full source orientation relation on every geometric block dart. -/
theorem lPlusPairOriented_identification
    (x : XDP) (k : ℤ) (hk : 0 ≤ k)
    (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r)
    (a : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairOriented x k z (lPlusPairGluedDartId x k r s hk ⟦a⟧) ↔
      geometricSideRelation
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) .oriented
        (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inr ⟦a⟧))
        (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk (.inr ⟦a⟧)) := by
  dsimp only
  have hp := lPlusPairPresent_identification x k hk r s a
  dsimp only at hp
  rw [lPlusPairOriented, hp]
  have hbit : (lPlusPairGluedDartId x k r s hk ⟦a⟧).2 =
      (lPlusBlockDartImage s.hτ a).2 :=
    lPlusPairRawDartBit_eq_of_aligned x k r s a
  rw [hbit]
  rfl

end DirectedDistances.PaperProofs.Section5













































