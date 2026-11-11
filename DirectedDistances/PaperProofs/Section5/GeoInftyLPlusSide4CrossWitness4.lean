/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSide4CrossWitness3

/-! Presence and retained-face reductions for the aligned nonnegative left side. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the entire primed presence predicate is read
from the equal primed codes, including the missing root. -/
theorem lPlusSourceWitnessAligned_primedEdgePresent_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) (e : ℕ) :
    PrimedEdgePresent (boundaryGluingFutureStream s.W s.h k) s.hτ e ↔
      PrimedEdgePresent (boundaryGluingFutureStream s'.W s'.h k) s'.hτ e := by
  unfold PrimedEdgePresent
  rw [lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq x k r r' s s' hr]

/-- Helper toward Lemma 5.5: future presence reflects ambient presence away
from the finite upper-left attachment. This retains that attachment at positive
indices instead of applying the nonpositive-only presence theorem. -/
theorem lPlus_future_present_iff_of_not_upperLeft
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (e : ℕ)
    (hne : boundaryGluingEdgeMap W h k e ∉ boundaryGluingUpperLeftEdges W h k) :
    EdgePresent (boundaryGluingFutureStream W h k) e ↔
      EdgePresent (shiftedStream W 0) (boundaryGluingEdgeMap W h k e) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let U := boundaryGluingFutureStream W h k
  constructor
  · rintro ⟨n, he, hp⟩
    rw [boundaryGluingEdgeMap, kmswWindowEdgeMapInf_eq_stage w t n e he]
    exact ⟨t + n, (kmswWindowPatchData_rel w t n).edge_bound e he,
      (kmswWindowPatchData_rel w t n).present e he hp⟩
  · intro hp
    by_contra hn
    obtain ⟨N, hN⟩ := (m0Cut_not_present_iff_eventually_LL U
      (hatBoundaryHitWitnesses U hτ) e).mp hn
    apply ((m0Cut_not_present_iff_eventually_LL w h
      (boundaryGluingEdgeMap W h k e)).mpr ?_) hp
    refine ⟨t + N, fun n hn => ?_⟩
    let m := n - t
    have hm : N ≤ m := by dsimp [m]; omega
    have ht : t + m = n := by dsimp [m]; omega
    let D := kmswWindowPatchData w t m
    have hr := kmswWindowPatchData_rel w t m
    change KMSWWindowPatchRel (kmswStage w t) (kmswStage w (t + m))
      (kmswStage U m) D.φ D.A D.B D.YL D.YR D.XL D.XR at hr
    have healloc : e < (kmswStage U m).nextEdge :=
      (kmswStage_boundary_ids_lt_nextEdge U m).2 e (by
        simp only [List.mem_append]
        exact Or.inl (Or.inr (hN m hm)))
    have he : e ∈ D.XL := by
      have he := hN m hm
      rw [hr.ll_split] at he
      rcases List.mem_append.mp he with he | he
      · exact he
      · exfalso
        apply hne
        change boundaryGluingEdgeMap W h k e ∈ (kmswStage w t).UL.dropLast
        rw [boundaryGluingEdgeMap, kmswWindowEdgeMapInf_eq_stage w t m e healloc,
          hr.left_residual]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩)
    rw [← ht, boundaryGluingEdgeMap, kmswWindowEdgeMapInf_eq_stage w t m e healloc, hr.ll]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩)

/-- Helper toward Lemma 5.5: primed image presence in the future run is
exactly local directed presence or membership in the shared beta boundary. -/
theorem LPlusSidePresentationSourceWitness.primedFuturePresent_iff
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (e : ℕ) :
    EdgePresent (boundaryGluingFutureStream s.W s.h k)
      (primedLimitEdgeMap (boundaryGluingFutureStream s.W s.h k) s.hτ e) ↔
      PrimedEdgePresent (boundaryGluingFutureStream s.W s.h k) s.hτ e ∨
        ∃ i, e = primedBeta0EdgeIndex (boundaryGluingFutureStream s.W s.h k)
          s.hτ s.hfin (hatBoundaryHitWitnesses _ s.hτ) s.hfin i := by
  let U := boundaryGluingFutureStream s.W s.h k
  constructor
  · intro hp
    by_cases hg : MhatGeometricEdge U (primedLimitEdgeMap U s.hτ e)
    · obtain ⟨a, ha⟩ := (hatLimitEdgeMap_geometric_range_iff U s.hτ _).mpr hg
      have hab : boundaryGluingPrimedEdgeMap s.W s.h k s.hτ e =
          boundaryGluingHatEdgeMap s.W s.h k s.hτ a :=
        congrArg (boundaryGluingEdgeMap s.W s.h k) ha.symm
      obtain ⟨i, hi, _⟩ := (lMinus_cross_edge_eq_iff s.hτ s.hfin e a).mp hab
      exact Or.inr ⟨i, hi⟩
    · exact Or.inl ((primedLimitEdgeMap_present_iff U s.hτ e).mpr ⟨hp, hg⟩)
  · rintro (hp | ⟨i, rfl⟩)
    · exact ((primedLimitEdgeMap_present_iff U s.hτ e).mp hp).1
    · have he := (boundaryGluingBeta_edge_primed s.W s.h k s.hτ s.hfin i).1
      have he' := boundaryGluingEdgeMap_injective s.W s.h k he
      rw [← he']
      exact (hatLimit_edge_incidence (hatLimitExplicitInput U s.hτ)
        (hatCodes_edge_present U s.hτ _)).1

/-- Helper toward Lemma 5.5: equal aligned codes preserve presence of every
primed image in its future run, even when local primed presence is false. -/
theorem lPlusSourceWitnessAligned_primedFuturePresent_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) (e : ℕ) :
    EdgePresent (boundaryGluingFutureStream s.W s.h k)
      (primedLimitEdgeMap (boundaryGluingFutureStream s.W s.h k) s.hτ e) ↔
    EdgePresent (boundaryGluingFutureStream s'.W s'.h k)
      (primedLimitEdgeMap (boundaryGluingFutureStream s'.W s'.h k) s'.hτ e) := by
  rw [s.toLPlusSidePresentationSourceWitness.primedFuturePresent_iff,
    s'.toLPlusSidePresentationSourceWitness.primedFuturePresent_iff,
    lPlusSourceWitnessAligned_primedEdgePresent_iff x k r r' s s' hr]
  apply or_congr Iff.rfl
  apply exists_congr
  intro i
  rw [lPlusSourceWitnessAligned_primedBetaIndex_eq_of_presentation_codes_eq
    x k r r' s s' hr i]

/-- Helper toward Lemma 5.5: ambient directed presence of a primed image
is determined by the three aligned presentation codes, including attachment
edges whose ambient presence differs from future presence. -/
theorem lPlusSourceWitnessAligned_primedAmbientPresent_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) (e : ℕ) :
    EdgePresent (shiftedStream s.W 0) (boundaryGluingPrimedEdgeMap s.W s.h k s.hτ e) ↔
    EdgePresent (shiftedStream s'.W 0) (boundaryGluingPrimedEdgeMap s'.W s'.h k s'.hτ e) := by
  let a := boundaryGluingPrimedEdgeMap s.W s.h k s.hτ e
  let a' := boundaryGluingPrimedEdgeMap s'.W s'.h k s'.hτ e
  have hpref := lPlusSourceWitnessAligned_prefixEdges_eq_of_presentation_codes_eq
    x k r r' s s' hk hr
  have hmem : a ∈ boundaryGluingPrefixMinusEdges s.W s.h k ↔
      a' ∈ boundaryGluingPrefixMinusEdges s'.W s'.h k := by
    constructor
    · intro ha
      have heq := (lPlusSourceWitnessAligned_prefixPrimedEdgeKernel_iff
        x k r r' s s' hk hr a e ha).mp rfl
      change a = a' at heq
      rw [← heq, ← hpref]
      exact ha
    · intro ha'
      have ha : a' ∈ boundaryGluingPrefixMinusEdges s.W s.h k := by
        rw [hpref]; exact ha'
      have heq := (lPlusSourceWitnessAligned_prefixPrimedEdgeKernel_iff
        x k r r' s s' hk hr a' e ha).mpr rfl
      change a' = a at heq
      rw [← heq]
      exact ha
  by_cases ha : a ∈ boundaryGluingPrefixMinusEdges s.W s.h k
  · have heq : a = a' := (lPlusSourceWitnessAligned_prefixPrimedEdgeKernel_iff
      x k r r' s s' hk hr a e ha).mp rfl
    change EdgePresent (shiftedStream s.W 0) a ↔ EdgePresent (shiftedStream s'.W 0) a'
    rw [← heq]
    exact lPlusSourceWitnessAligned_prefixEdgePresent_iff x k r r' s s' hk hr
      ⟨(a, false), ha⟩
  · have ha' := fun hh => ha (hmem.mpr hh)
    have hUL : a ∉ boundaryGluingUpperLeftEdges s.W s.h k := by
      intro hu
      rw [← boundaryGluingPrefixMinusEdges_inter_primedEdges s.W s.h k s.hτ s.hfin hk] at hu
      exact ha hu.1
    have hUL' : a' ∉ boundaryGluingUpperLeftEdges s'.W s'.h k := by
      intro hu
      rw [← boundaryGluingPrefixMinusEdges_inter_primedEdges s'.W s'.h k s'.hτ s'.hfin hk] at hu
      exact ha' hu.1
    exact (lPlus_future_present_iff_of_not_upperLeft s.hτ _ hUL).symm.trans
      ((lPlusSourceWitnessAligned_primedFuturePresent_iff x k r r' s s' hr e).trans
        (lPlus_future_present_iff_of_not_upperLeft s'.hτ _ hUL'))

/-- Helper toward Lemma 5.5: primed orientation transports on every primed
representative, including those identified with a directed prefix or hatted edge. -/
theorem lPlusSourceWitnessAligned_codeBlockCellEquiv4_primed_oriented_iff
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) (a : LPlusPrimedDart)
    (v : Sum (LPlusGluedVertex s.longest s.hqMode s.hτ)
      (LPlusGluedDart s.longest s.hqMode s.hτ))
    (v' : Sum (LPlusGluedVertex s'.longest s'.hqMode s'.hτ)
      (LPlusGluedDart s'.longest s'.hqMode s'.hτ)) :
    geometricSideRelation
      (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
      .oriented
      (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk
        (.inr ⟦Sum.inr (Sum.inl a)⟧))
      (s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk v) ↔
    geometricSideRelation
      (lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk)
      .oriented
      (s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r' hk
        (.inr ⟦Sum.inr (Sum.inl a)⟧))
      (s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r' hk v') := by
  change (EdgePresent (shiftedStream s.W 0)
      (boundaryGluingPrimedEdgeMap s.W s.h k s.hτ a.1) ∧
        (a.2 ^^ primedLimitSideFlip _ s.hτ a.1) = false) ↔
    (EdgePresent (shiftedStream s'.W 0)
      (boundaryGluingPrimedEdgeMap s'.W s'.h k s'.hτ a.1) ∧
        (a.2 ^^ primedLimitSideFlip _ s'.hτ a.1) = false)
  rw [lPlusSourceWitnessAligned_primedAmbientPresent_iff x k r r' s s' hk hr,
    lPlusSourceWitnessAligned_primedSideFlip_eq_of_presentation_codes_eq x k r r' s s' hr]

/-- Helper toward Lemma 5.5: face succession is exactly a retained run-zero
creation triangle together with the corrected inverse-rotation corner equation.
The triangle clause is explicit; rotation and opposition alone do not replace it. -/
theorem LPlusSidePresentationSourceWitness.codeBlockCellEquiv4_faceNext_iff_triangle
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (hk : 0 ≤ k)
    (a b : LPlusGluedDart s.longest s.hqMode s.hτ) :
    let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    geometricSideRelation
      (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
      .faceNext (s.codeBlockCellEquiv4 x k r hk (.inr a))
        (s.codeBlockCellEquiv4 x k r hk (.inr b)) ↔
    (∃ J : TriangleCreationTime (shiftedStream s.W 0),
      (D a).val ∈ stageTriangleDartList (shiftedStream s.W 0) J ∧
      ∀ d ∈ stageTriangleDartList (shiftedStream s.W 0) J,
        d.1 ∈ (m0GeodesicSide s.hp s.P .left).edges) ∧
    lPlusGluedCorrectedRotation4 s.hτ s.hp s.P s.hqMode s.Tpath
      s.hfin s.hleft hk b = lPlusSide4GluedOpposite a := by
  let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
  constructor
  · intro hab
    exact ⟨lMinusActualFaceNext_triangle s.hp s.P (D a).val (D b).val hab,
      s.codeBlockCellEquiv4_faceNext_imp_rotation x k r hk a b hab⟩
  · rintro ⟨⟨J, ha, hall⟩, hrot⟩
    obtain ⟨G, hG, hb⟩ := lMinusRunZeroCreationTriangle_retained s.hp s.P J hall
    have hsucc := rMinusWhole_triangle_succ_mem (shiftedStream s.W 0) (s.H.1 0) J _ ha
    let d : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide s.hp s.P .left).edges} :=
      ⟨kmswInfFaceSucc (shiftedStream s.W 0) (s.H.1 0) (D a).val, hall _ hsucc⟩
    let c := D.symm d
    have hc : (D c).val = d.val := congrArg Subtype.val (D.apply_symm_apply d)
    have hac : geometricSideRelation
        (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)
        .faceNext (s.codeBlockCellEquiv4 x k r hk (.inr a))
          (s.codeBlockCellEquiv4 x k r hk (.inr c)) := by
      change (m0GeodesicSide s.hp s.P .left).faceNext (D a).val (D c).val
      exact ⟨⟨G, hb _ ha, hG⟩, hc.symm⟩
    have hcorner := s.codeBlockCellEquiv4_faceNext_imp_rotation x k r hk a c hac
    have hcb : c = b :=
      (lPlusGluedCorrectedRotation4 s.hτ s.hp s.P s.hqMode s.Tpath
        s.hfin s.hleft hk).injective (hcorner.trans hrot.symm)
    exact hcb ▸ hac

/-- Helper toward Lemma 5.5: beyond the finite upper-left attachment, a
future missing-boundary index has its exact ambient negative boundary label.
The offset retains both the old lower-left word and the consumed attachment. -/
theorem lPlus_future_LL_tail_index
    {W : ℤ → Fin 3} (h : BoundaryHitWitnesses (shiftedStream W 0))
    (k : ℤ) (n i e : ℕ)
    (hi : (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k)).UL.dropLast.length ≤ i)
    (he : (kmswStage (boundaryGluingFutureStream W h k) n).LL.reverse[i]? = some e) :
    boundaryGluingEdgeMap W h k e =
      boundaryOuterEdge (shiftedStream W 0) h
        (-(((kmswStage (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h k)).LL.length + i -
          (kmswStage (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h k)).UL.dropLast.length : ℕ) : ℤ) - 1) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let U := boundaryGluingFutureStream W h k
  let D := kmswWindowPatchData w t n
  have hr := kmswWindowPatchData_rel w t n
  change KMSWWindowPatchRel (kmswStage w t) (kmswStage w (t + n))
    (kmswStage U n) D.φ D.A D.B D.YL D.YR D.XL D.XR at hr
  have hib := (List.getElem?_eq_some_iff.mp he).1
  change i < (kmswStage U n).LL.reverse.length at hib
  have hA : D.A = [] := by
    by_contra ha
    have hxl := hr.xl_nil ha
    have hlen := congrArg List.length hr.ll_split
    have hres := congrArg List.length hr.left_residual
    simp only [List.length_append, List.length_map, List.length_reverse] at hlen hres hib
    rw [hxl] at hlen
    simp only [List.length_nil, zero_add] at hlen
    change (kmswStage w t).UL.dropLast.length ≤ i at hi
    omega
  have hlen : D.YL.length = (kmswStage w t).UL.dropLast.length := by
    have hh := congrArg List.length hr.left_residual
    simpa only [hA, List.nil_append, List.length_map] using hh.symm
  have heX : D.XL.reverse[i - D.YL.length]? = some e := by
    rw [hr.ll_split, List.reverse_append,
      List.getElem?_append_right (by rw [List.length_reverse, hlen]; exact hi),
      List.length_reverse] at he
    exact he
  have hb : e < (kmswStage U n).nextEdge :=
    (kmswStageFrontierChain_all U n).LL_missing_bounded e
      (List.mem_reverse.mp (List.mem_of_getElem? he)) |>.2
  have hG : (kmswStage w (t + n)).LL.reverse[
      (kmswStage w t).LL.length + (i - D.YL.length)]? =
        some (boundaryGluingEdgeMap W h k e) := by
    rw [hr.ll, List.reverse_append, ← List.map_reverse,
      List.getElem?_append_right (by simp only [List.length_reverse]; omega),
      List.length_reverse, Nat.add_sub_cancel_left, List.getElem?_map, heX,
      Option.map_some, boundaryGluingEdgeMap,
      kmswWindowEdgeMapInf_eq_stage w t n e hb]
  have hlabel := lMinus_LL_reverse_boundary w h (t + n)
    ((kmswStage w t).LL.length + (i - D.YL.length))
    (List.getElem?_eq_some_iff.mp hG).1
  rw [hlabel] at hG
  have hidx : (kmswStage w t).LL.length + (i - D.YL.length) =
      (kmswStage w t).LL.length + i - (kmswStage w t).UL.dropLast.length := by
    rw [hlen]
    change (kmswStage w t).UL.dropLast.length ≤ i at hi
    omega
  have hout := (Option.some.inj hG).symm
  rw [hidx] at hout
  simpa only [neg_add, sub_eq_add_neg] using hout

/-- Helper toward Lemma 5.5: every primed exterior index beyond the
attachment has its exact ambient exterior dart, including the reversed bit. -/
theorem LPlusSidePresentationSourceWitness.primedExteriorDart_tail_image
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSidePresentationSourceWitness x k r) (i : ℕ)
    (hi : (kmswStage (shiftedStream s.W 0)
      (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.length ≤ i) :
    lMinusPrimedDartImage s.hτ
      (lMinusCodeExteriorBoundaryEdge
        (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ) i, true) =
      (boundaryOuterEdge (shiftedStream s.W 0) s.h
        (-(((kmswStage (shiftedStream s.W 0)
          (boundaryHitTime (shiftedStream s.W 0) s.h k)).LL.length + i -
          (kmswStage (shiftedStream s.W 0)
            (boundaryHitTime (shiftedStream s.W 0) s.h k)).UL.dropLast.length : ℕ) : ℤ) - 1),
        true) := by
  let U := boundaryGluingFutureStream s.W s.h k
  let p := primedCode (primedSimInput U) s.hτ
  let a := lMinusCodeExteriorBoundaryEdge p i
  obtain ⟨m, hm⟩ := lMinus_primed_exterior_index_exists U s.hτ i
  have ha := lMinusCodeExteriorBoundaryEdge_stage p m i hm
  have hw := lPlus_primed_LL_dart_word U s.hτ m
  have hlen := congrArg List.length hw
  simp only [List.length_map] at hlen
  have hib : i < (kmswStage U (primedStageTime U s.hτ m)).LL.reverse.length := by omega
  let e := (kmswStage U (primedStageTime U s.hτ m)).LL.reverse[i]
  have he : (kmswStage U (primedStageTime U s.hτ m)).LL.reverse[i]? = some e :=
    List.getElem?_eq_getElem hib
  have hget := congrArg (fun l : List (ℕ × Bool) => l[i]?) hw
  rw [List.getElem?_map, List.getElem?_map, ha, he, Option.map_some, Option.map_some] at hget
  have hd := congrArg (fun d : ℕ × Bool => (boundaryGluingEdgeMap s.W s.h k d.1, d.2))
    (Option.some.inj hget)
  change lMinusPrimedDartImage s.hτ (a, true) =
    (boundaryGluingEdgeMap s.W s.h k e, true) at hd
  exact hd.trans (congrArg (fun b : ℕ => (b, true))
    (lPlus_future_LL_tail_index s.h k _ i e hi he))

/-- Helper toward Lemma 5.5: the deleted prefix has exactly k present
lower-right boundary edges before a positive hit. -/
theorem lPlus_previous_LR_length (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (k : ℤ) (hk : 0 < k) :
    ((kmswStage w (boundaryHitTime w h k - 1)).LR.length : ℤ) = k := by
  let t := boundaryHitTime w h k
  have hUR := boundaryHit_right_UR_empty w h (by omega : 1 ≤ k)
  have hu := kmswStage_UR_length w t
  have hR := boundaryHitTime_right_spec w h (by omega : 1 ≤ k)
  have hl := kmswStage_LR_length w t
  change (kmswStage w t).UR = [] at hUR
  rw [hUR] at hu
  simp only [List.length_nil, Nat.cast_zero] at hu
  change R w t = -k at hR
  obtain ⟨m, hm, hc, hur⟩ := lPlus_positive_hit_fresh w h hk
  have hlen : ((kmswStage w t).LR.length : ℤ) = k + 1 := by omega
  dsimp only [t] at hlen
  rw [hm] at hlen ⊢
  simp only [Nat.add_sub_cancel]
  have hstep : (kmswStage w (m + 1)).LR =
      (kmswStage w m).LR ++ [(kmswStage w m).nextEdge] := by
    simp only [kmswStage, kmswStep, hc, kmswCodeStep, kmswStepOfStep, hur, State.addEdge]
    rfl
  rw [hstep, List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one] at hlen
  omega

/-- Helper toward Lemma 5.5: the entire finite lower word, read backwards,
is the initial segment of the actual indexed left exterior boundary. -/
theorem lPlus_previous_lower_reverse_get
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (k : ℤ) (hk : 0 < k)
    (i : ℕ) (hi : i < ((kmswStage w (boundaryHitTime w h k - 1)).LL ++
      (kmswStage w (boundaryHitTime w h k - 1)).LR).reverse.length) :
    ((kmswStage w (boundaryHitTime w h k - 1)).LL ++
      (kmswStage w (boundaryHitTime w h k - 1)).LR).reverse[i]? =
        some (boundaryOuterEdge w h (k - 1 - (i : ℤ))) := by
  let n := boundaryHitTime w h k - 1
  have hlen := lPlus_previous_LR_length w h k hk
  change ((kmswStage w n).LR.length : ℤ) = k at hlen
  change ((kmswStage w n).LL ++ (kmswStage w n).LR).reverse[i]? = _
  rw [List.reverse_append]
  by_cases hiR : i < (kmswStage w n).LR.length
  · have hj : (kmswStage w n).LR.length - 1 - i < (kmswStage w n).LR.length := by omega
    have he := rMinusWhole_LR_get w h n ((kmswStage w n).LR.length - 1 - i) hj
    have hidx : k - 1 - (i : ℤ) = (((kmswStage w n).LR.length - 1 - i : ℕ) : ℤ) := by omega
    have hb : boundaryOuterEdge w h (k - 1 - (i : ℤ)) =
        kmswRightBoundaryEdge w ((kmswStage w n).LR.length - 1 - i) := by
      rw [hidx]
      by_cases hz : (kmswStage w n).LR.length - 1 - i = 0
      · rw [hz, Nat.cast_zero, boundaryOuterEdge_zero, kmswRightBoundaryEdge_zero]
      · rw [boundaryOuterEdge_of_positive w h (by omega), Int.toNat_natCast]
    rw [List.getElem?_append_left (by simpa only [List.length_reverse] using hiR), hb,
      List.getElem?_eq_getElem (by simpa only [List.length_reverse] using hiR),
      List.getElem_reverse]
    exact congrArg some he
  · have hiL : i - (kmswStage w n).LR.length < (kmswStage w n).LL.reverse.length := by
      change i < ((kmswStage w n).LL ++ (kmswStage w n).LR).reverse.length at hi
      simp only [List.length_reverse, List.length_append] at hi ⊢
      omega
    rw [List.getElem?_append_right (by simp only [List.length_reverse]; omega),
      List.length_reverse, lMinus_LL_reverse_boundary w h n _ hiL]
    congr 2
    omega

/-- Helper toward Lemma 5.5: every exterior mark has corresponding prefix
representatives with equal IDs, or the very same primed representative, in
both aligned realizations. This includes every negative exterior index. -/
theorem lPlusSourceWitnessAligned_boundary_representatives
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) (i : ℕ) :
    (∃ (a : LPlusPrefixDart s.W s.h k) (a' : LPlusPrefixDart s'.W s'.h k),
      a.val = a'.val ∧ a.val = m0GeodesicBoundaryDart (shiftedStream s.W 0) s.h k .left i ∧
      a'.val = m0GeodesicBoundaryDart (shiftedStream s'.W 0) s'.h k .left i) ∨
    (∃ a : LPlusPrimedDart,
      lMinusPrimedDartImage s.hτ a =
        m0GeodesicBoundaryDart (shiftedStream s.W 0) s.h k .left i ∧
      lMinusPrimedDartImage s'.hτ a =
        m0GeodesicBoundaryDart (shiftedStream s'.W 0) s'.h k .left i) := by
  have hc := (lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq x k r r'
    s.toLPlusSidePresentationSourceWitness s'.toLPlusSidePresentationSourceWitness hr).1
  have hstage := lPlusBoundaryHitStage_eq_of_code_eq s.W s'.W s.h s'.h k hc
  have hprev := lPlusSourceWitnessAligned_prefixStage_eq_of_presentation_codes_eq
    x k r r' s s' hr
  have hpcode := lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq
    x k r r' s s' hr
  let G := kmswStage (shiftedStream s.W 0) (boundaryHitTime (shiftedStream s.W 0) s.h k)
  let F := kmswStage (shiftedStream s.W 0) (boundaryHitTime (shiftedStream s.W 0) s.h k - 1)
  by_cases hk0 : k = 0
  · subst k
    right
    let a := (lMinusCodeExteriorBoundaryEdge
      (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h 0)) s.hτ) i, true)
    refine ⟨a, ?_, ?_⟩
    · have hh := s.toLPlusSidePresentationSourceWitness.primedExteriorDart_tail_image
        x 0 r i (by rw [boundaryHitTime_zero]; change 0 ≤ i; omega)
      simp only [boundaryHitTime_zero, kmswStage, kmswInit, List.length_nil,
        List.dropLast_singleton, zero_add, Nat.sub_zero] at hh
      have hidx : -(i : ℤ) - 1 = (0 : ℤ) - 1 - (i : ℤ) := by omega
      rw [hidx] at hh
      exact hh
    · have hh := s'.toLPlusSidePresentationSourceWitness.primedExteriorDart_tail_image
        x 0 r' i (by rw [boundaryHitTime_zero]; change 0 ≤ i; omega)
      rw [← hpcode] at hh
      simp only [boundaryHitTime_zero, kmswStage, kmswInit, List.length_nil,
        List.dropLast_singleton, zero_add, Nat.sub_zero] at hh
      have hidx : -(i : ℤ) - 1 = (0 : ℤ) - 1 - (i : ℤ) := by omega
      rw [hidx] at hh
      exact hh
  have hkpos : 0 < k := by omega
  have hLR : (F.LR.length : ℤ) = k := lPlus_previous_LR_length _ s.h k hkpos
  have hLL : G.LL = F.LL := by
    obtain ⟨m, hm, hcode, hur⟩ := lPlus_positive_hit_fresh _ s.h hkpos
    dsimp only [G, F]
    rw [hm]
    simp only [Nat.add_sub_cancel]
    simp only [kmswStage, kmswStep, hcode, kmswCodeStep, kmswStepOfStep, hur, State.addEdge]
    rfl
  by_cases hi : i < (F.LL ++ F.LR).reverse.length
  · left
    let e := (F.LL ++ F.LR).reverse[i]
    have he : e = boundaryOuterEdge (shiftedStream s.W 0) s.h (k - 1 - (i : ℤ)) :=
      Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans
        (lPlus_previous_lower_reverse_get _ s.h k hkpos i hi))
    have he' : e = boundaryOuterEdge (shiftedStream s'.W 0) s'.h (k - 1 - (i : ℤ)) := by
      have hh := lPlus_previous_lower_reverse_get (shiftedStream s'.W 0) s'.h k hkpos i
      rw [← hprev] at hh
      exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans (hh hi))
    have halloc : e < F.nextEdge := by
      have hm : e ∈ F.LL ++ F.LR := List.mem_reverse.mp (List.getElem_mem hi)
      apply (kmswStage_boundary_ids_lt_nextEdge (shiftedStream s.W 0)
        (boundaryHitTime (shiftedStream s.W 0) s.h k - 1)).2
      simp only [List.mem_append] at hm ⊢
      tauto
    have hpref : e ∈ boundaryGluingPrefixMinusEdges s.W s.h k := by
      rw [lPlusPrefixMinusEdges_eq_previousStage hkpos]
      exact halloc
    have hpref' : e ∈ boundaryGluingPrefixMinusEdges s'.W s'.h k := by
      rw [← lPlusSourceWitnessAligned_prefixEdges_eq_of_presentation_codes_eq
        x k r r' s s' hk hr]
      exact hpref
    exact ⟨⟨(e, true), hpref⟩, ⟨(e, true), hpref'⟩, rfl,
      congrArg (fun e => (e, true)) he, congrArg (fun e => (e, true)) he'⟩
  · right
    let j := G.UL.dropLast.length + i - (F.LL.length + F.LR.length)
    have hj : G.UL.dropLast.length ≤ j := by
      simp only [List.length_reverse, List.length_append] at hi
      dsimp only [j]
      omega
    have hindex : -((G.LL.length + j - G.UL.dropLast.length : ℕ) : ℤ) - 1 =
        k - 1 - (i : ℤ) := by
      rw [hLL]
      dsimp only [j]
      simp only [List.length_reverse, List.length_append] at hi
      omega
    let a := (lMinusCodeExteriorBoundaryEdge
      (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ) j, true)
    refine ⟨a, ?_, ?_⟩
    · have hh := s.toLPlusSidePresentationSourceWitness.primedExteriorDart_tail_image
        x k r j hj
      change lMinusPrimedDartImage s.hτ a =
        (boundaryOuterEdge (shiftedStream s.W 0) s.h
          (-((G.LL.length + j - G.UL.dropLast.length : ℕ) : ℤ) - 1), true) at hh
      rw [hindex] at hh
      exact hh
    · have hj' : (kmswStage (shiftedStream s'.W 0)
          (boundaryHitTime (shiftedStream s'.W 0) s'.h k)).UL.dropLast.length ≤ j := by
        rw [← hstage]; exact hj
      have hh := s'.toLPlusSidePresentationSourceWitness.primedExteriorDart_tail_image
        x k r' j hj'
      rw [← hpcode, ← hstage] at hh
      change lMinusPrimedDartImage s'.hτ a =
        (boundaryOuterEdge (shiftedStream s'.W 0) s'.h
          (-((G.LL.length + j - G.UL.dropLast.length : ℕ) : ℤ) - 1), true) at hh
      rw [hindex] at hh
      exact hh

/-- Helper toward Lemma 5.5: one common cell equivalence preserves every
tag except retained face succession, including all indexed exterior marks. -/
theorem lPlusSourceWitnessAligned_codeBlockCellEquiv4_all_except_faceNext
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let B := lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    let B' := lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
    ∃ F : GeometricSideCell B ≃ GeometricSideCell B',
      (∀ t ∈ ({TruncationRelation.vertex, .root, .incident, .opposite, .rotation, .target} ∪
          Set.range TruncationRelation.seam ∪ Set.range TruncationRelation.boundary : Set TruncationRelation),
        ∀ u v, geometricSideRelation B t u v ↔ geometricSideRelation B' t (F u) (F v)) ∧
      (∀ u v, geometricSideRelation B .oriented u v ↔
        geometricSideRelation B' .oriented (F u) (F v)) := by
  obtain ⟨fD, qV, qD, hqD, hroot, he, hop, hrot, hseam, hPD, hTD, ⟨phi, hHD⟩⟩ :=
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
    rcases ht with (ht | ⟨i, rfl⟩) | ⟨i, rfl⟩
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
    · cases a with
      | inl a => rfl
      | inr a =>
        let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
        let D' := lPlusGluedDartEquivNonneg s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
        have htransport (dB : LPlusGluedDart s.longest s.hqMode s.hτ)
            (dB' : LPlusGluedDart s'.longest s'.hqMode s'.hτ)
            (hq : qD dB = dB')
            (hb : (D dB).val = m0GeodesicBoundaryDart (shiftedStream s.W 0) s.h k .left i)
            (hb' : (D' dB').val = m0GeodesicBoundaryDart (shiftedStream s'.W 0) s'.h k .left i) :
            geometricSideRelation _ (.boundary i) (E (.inr a)) (E b) ↔
              geometricSideRelation _ (.boundary i) (E' (.inr (qD a))) (E' (Q b)) := by
          change m0GeodesicBoundaryDart (shiftedStream s.W 0) s.h k .left i = (D a).val ↔
            m0GeodesicBoundaryDart (shiftedStream s'.W 0) s'.h k .left i = (D' (qD a)).val
          rw [← hb, ← hb']
          constructor
          · intro hh
            have hd : dB = a := D.injective (Subtype.ext hh)
            exact congrArg (fun d => (D' d).val) (hq.symm.trans (congrArg qD hd))
          · intro hh
            have hd : dB' = qD a := D'.injective (Subtype.ext hh)
            exact congrArg (fun d => (D d).val) (qD.injective (hq.trans hd))
        rcases lPlusSourceWitnessAligned_boundary_representatives x k r r' s s' hk hr i with
          ⟨p, p', hval, hp, hp'⟩ | ⟨p, hp, hp'⟩
        · obtain ⟨p'', hpp, hppval⟩ := hPD p
          have hpp' : p'' = p' := Subtype.ext (hppval.trans hval)
          apply htransport ⟦Sum.inl p⟧ ⟦Sum.inl p'⟧
          · rw [hqD, hpp, hpp']
          · exact hp
          · exact hp'
        · apply htransport ⟦Sum.inr (Sum.inl p)⟧ ⟦Sum.inr (Sum.inl p)⟧
          · rw [hqD, hTD]
          · exact hp
          · exact hp'
  · intro u v
    obtain ⟨a, rfl⟩ := E.surjective u
    obtain ⟨b, rfl⟩ := E.surjective v
    rw [hF, hF]
    cases a with
    | inl a => rfl
    | inr a =>
      induction a using Quotient.inductionOn with
      | h a =>
        change geometricSideRelation _ .oriented (E (.inr ⟦a⟧)) (E b) ↔
          geometricSideRelation _ .oriented (E' (.inr (qD ⟦a⟧))) (E' (Q b))
        rw [hqD]
        rcases a with a | (a | a)
        · obtain ⟨a', ha, hval⟩ := hPD a
          rw [ha]
          change (EdgePresent (shiftedStream s.W 0) a.val.1 ∧ a.val.2 = false) ↔
            (EdgePresent (shiftedStream s'.W 0) a'.val.1 ∧ a'.val.2 = false)
          rw [hval]
          exact and_congr
            (lPlusSourceWitnessAligned_prefixEdgePresent_iff x k r r' s s' hk hr a) Iff.rfl
        · rw [hTD]
          exact lPlusSourceWitnessAligned_codeBlockCellEquiv4_primed_oriented_iff
            x k r r' s s' hk hr a b (Q b)
        · obtain ⟨a', ha, hphi⟩ := hHD a
          rw [ha,
            s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_hatted_oriented_iff,
            s'.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_hatted_oriented_iff]
          have ho := phi.relation_iff .oriented (.inr a) (.inr a)
          rw [hphi] at ho
          have hp : a.val.1 ∈
              (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode).present := by
            change EdgePresent (boltzmannKMSWStream
              (pathCode (boundaryFutureHattedPath k s.W))) _
            rw [boundaryGluing_decoded_stream s.W s.h k s.hτ]
            exact hatCodes_edge_present _ s.hτ _
          have hp' : a'.val.1 ∈
              (lPlusHattedSide (W := s'.W) (h := s'.h) (k := k) s'.longest s'.hqMode).present := by
            change EdgePresent (boltzmannKMSWStream
              (pathCode (boundaryFutureHattedPath k s'.W))) _
            rw [boundaryGluing_decoded_stream s'.W s'.h k s'.hτ]
            exact hatCodes_edge_present _ s'.hτ _
          change (_ ∧ a.val.2 = false) ↔ (_ ∧ a'.val.2 = false) at ho
          simpa only [hp, hp', true_and] using ho


/-- Helper toward Lemma 5.5: the aligned comparison preserves every
relation other than retained face succession, on one common cell equivalence. -/
theorem lPlusCodeBlockSide4_relationEquiv_except_faceNext_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    let B := lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
    let B' := lPlusCodeBlockSide4 s'.hτ s'.hp s'.P s'.hqMode s'.Tpath s'.hfin s'.hleft hk
    ∃ F : GeometricSideCell B ≃ GeometricSideCell B',
      ∀ t : TruncationRelation, t ≠ .faceNext → ∀ u v,
        geometricSideRelation B t u v ↔ geometricSideRelation B' t (F u) (F v) := by
  obtain ⟨F, htags, horiented⟩ :=
    lPlusSourceWitnessAligned_codeBlockCellEquiv4_all_except_faceNext x k r r' s s' hk hr
  refine ⟨F, ?_⟩
  intro t ht u v
  cases t <;> first
    | exact (ht rfl).elim
    | exact horiented u v
    | exact htags _ (by simp) u v

















































































end DirectedDistances.PaperProofs.Section5
