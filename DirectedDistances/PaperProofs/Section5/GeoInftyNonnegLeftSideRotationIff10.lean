/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff7

/-! Helper toward Lemma 5.5: the initial upper-left attachment port. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W} {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hk : 0 ≤ k)

local notation "w" => shiftedStream W 0
local notation "U" => boundaryGluingFutureStream W h k
local notation "ULedges" => (List.reverse (List.dropLast (State.UL
  (kmswStage w (boundaryHitTime w h k)))))

/-- Helper toward Lemma 5.5: the initial attachment dart is precisely the
retained primed root, with the same endpoint bit. -/
theorem lPlusUpperLeftGluedDart_initial_eq_primed_root
    (hn : 0 < (ULedges).length) :
    lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨0, hn⟩, true) =
      lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (0, true) := by
  obtain ⟨m, hm⟩ := lPlus_prefix_primed_ordered_dart_image hτ
  rw [lPlusPrefixUpperLeftDarts_eq] at hm
  have he := congrArg (fun ds : List (ℕ × Bool) => ds[0]?) hm
  simp only [List.length_map, List.getElem?_map,
    List.getElem?_take_of_lt hn, List.getElem?_cons_zero,
    Option.map_some, List.getElem?_eq_getElem hn] at he
  apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mpr
  exact (Option.some.inj he).symm

/-- Helper toward Lemma 5.5: the initial edge of the finite attachment is
the active edge just before the positive stopping step. -/
theorem lPlus_upperLeft_initial_eq_previous_active
    (hkpos : 0 < k) (hn : 0 < (ULedges).length) :
    ULedges[0] = (kmswStage w (boundaryHitTime w h k - 1)).active := by
  have heq := lPlus_attachment_upperLeft_eq_previous (W := W) (h := h) hkpos
  have hzero := congrArg (fun es : List ℕ => es[0]?) heq
  obtain ⟨es, hes⟩ := kmswStage_UL_last w (boundaryHitTime w h k - 1)
  rw [hes, List.reverse_append] at hzero
  simp only [List.reverse_singleton, List.singleton_append,
    List.getElem?_cons_zero, List.getElem?_eq_getElem hn] at hzero
  exact Option.some.inj hzero

/-- Helper toward Lemma 5.5: the primed root's east dart rotates to the
initial permanent upper-right dart. This is the initial exterior corner. -/
theorem lPlusPrimedRotation_initial_root_corner :
    kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin) (0, true) =
        (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin 0, true) := by
  let u := primedCode (primedSimInput U) hτ
  let a := primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin 0
  have hf : kmswInfFaceSucc u (primedCode_finiteIncidence U hτ hfin)
      (a, false) = (0, true) := by
    apply kmswInfFaceSucc_eq_of_stages
    refine ⟨1, fun n hn => ?_⟩
    have hlast := primedBeta0EdgeIndex_UR_reverse_order U hτ hfin
      (hatBoundaryHitWitnesses U hτ) hfin 0 n
      (by simpa only [primedIntervalBase_zero, Nat.zero_add] using hn)
    have hlen : 0 < (kmswStage u n).UR.length := by
      have hh := (List.getElem?_eq_some_iff.mp hlast).1
      simpa only [List.length_reverse] using hh
    rw [List.getElem?_reverse (by omega)] at hlast
    have hword : (stageOuterWordVal u n)[(kmswStage u n).UL.length +
        ((kmswStage u n).UR.length - 1)]? = some (a, false) := by
      rw [stageOuterWordVal_eq_runs]
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_map, List.length_reverse]
        omega), List.getElem?_append_left
        (by
          simp only [List.length_append, List.length_map]
          omega),
        List.getElem?_append_right (by
          simp only [List.length_map]
          omega)]
      simp only [List.length_map, Nat.add_sub_cancel_left, List.getElem?_map]
      simpa only [Nat.sub_zero, Option.map_some] using
        congrArg (Option.map (fun e => (e, false))) hlast
    have hnext : (stageOuterWordVal u n)[(kmswStage u n).UL.length +
        ((kmswStage u n).UR.length - 1) + 1]? = some (0, true) := by
      rw [stageOuterWordVal_eq_runs, primedStage_LR_eq_root]
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_map, List.length_reverse,
          List.length_singleton]
        omega),
        List.getElem?_append_right (by
        simp only [List.length_append, List.length_map]
        omega)]
      simp only [List.length_append, List.length_map, List.reverse_singleton]
      have hidx : (kmswStage u n).UL.length + ((kmswStage u n).UR.length - 1) + 1 -
          ((kmswStage u n).UL.length + (kmswStage u n).UR.length) = 0 := by omega
      rw [hidx]
      rfl
    obtain ⟨d, e, hd, he, hde⟩ := outer_faceSucc_exists u n
      (stageOuterWord_faceSucc u n)
      ((kmswStage u n).UL.length + ((kmswStage u n).UR.length - 1))
      (List.getElem?_eq_some_iff.mp hword).1
    rw [Nat.mod_eq_of_lt (List.getElem?_eq_some_iff.mp hnext).1] at he
    exact ⟨d, e, Option.some.inj (hd.symm.trans hword),
      Option.some.inj (he.symm.trans hnext), hde⟩
  change (kmswInfRot u (primedCode_finiteIncidence U hτ hfin)).symm
    (a, true) = (0, true) at hf
  have hr := congrArg (kmswInfRot u (primedCode_finiteIncidence U hτ hfin)) hf
  rw [Equiv.apply_symm_apply] at hr
  exact hr.symm

include H in
/-- Helper toward Lemma 5.5: window embeddings preserve the actual
successor across each triangle corner, including missing geometric sides. -/
private theorem lPlus_window_triangle_faceSucc
    (j : TriangleCreationTime U) (a b : ℕ × Bool)
    (ha : a ∈ stageTriangleDartList U j)
    (hab : kmswInfFaceSucc U hfin a = b) :
    kmswInfFaceSucc w (H.1 0)
        (boundaryGluingEdgeMap W h k a.1, a.2) =
      (boundaryGluingEdgeMap W h k b.1, b.2) := by
  let t := boundaryHitTime w h k
  obtain ⟨N, hN⟩ := kmswInfFaceSucc_eventually_eq_stage U hfin a
  apply kmswInfFaceSucc_eq_of_stages
  refine ⟨t + max N (j.val + 1), fun n hn => ?_⟩
  let m := n - t
  have htm : t + m = n := by omega
  have hjm : j.val < m := by omega
  obtain ⟨ha', heq⟩ := hN m (by omega)
  let x : StageDart (kmswStage U m).nextEdge := (⟨a.1, ha'⟩, a.2)
  have hx : (x.1.val, x.2) ∈ stageTriangleDartsVal U m :=
    List.mem_flatMap.mpr ⟨j, (mem_stageTriangleTimes U m j).mpr hjm, ha⟩
  have hmap := kmswWindowDartMap_faceSucc w t m x hx
  have hb : ((kmswMap U m).faceSucc x).1.val = b.1 ∧
      ((kmswMap U m).faceSucc x).2 = b.2 := by
    have hh := heq.symm.trans hab
    exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  have hbb : b.1 < (kmswStage U m).nextEdge := by
    rw [← hb.1]
    exact ((kmswMap U m).faceSucc x).1.isLt
  have hvalA : ((kmswWindowDartMap w t m x).1.val,
      (kmswWindowDartMap w t m x).2) =
        (boundaryGluingEdgeMap W h k a.1, a.2) := by
    apply Prod.ext
    · exact (kmswWindowEdgeMapInf_eq_stage w t m a.1 ha').symm
    · rfl
  have hvalB : ((kmswWindowDartMap w t m ((kmswMap U m).faceSucc x)).1.val,
      (kmswWindowDartMap w t m ((kmswMap U m).faceSucc x)).2) =
        (boundaryGluingEdgeMap W h k b.1, b.2) := by
    apply Prod.ext
    · change (kmswWindowPatchData w t m).φ _ = _
      rw [hb.1]
      exact (kmswWindowEdgeMapInf_eq_stage w t m b.1 hbb).symm
    · exact hb.2
  rw [← htm]
  exact ⟨_, _, hvalA, hvalB, hmap⟩

include H hfin hqMode hk in
/-- Helper toward Lemma 5.5: the first future-exit triangle makes the
initial beta dart immediately precede the initial upper-left east dart in
the ambient rotation. No return or separation premise is used. -/
theorem lPlus_upperLeft_initial_beta_successor (hn : 0 < (ULedges).length) :
    kmswInfRot w (H.1 0)
        (boundaryGluingHatEdgeMap W h k hτ
          (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) =
      (ULedges[0], true) := by
  let t := sourceFlowNL U hτ 0
  have hc : U (t - 1) = 0 := by
    dsimp only [t]
    rw [sourceFlowNL_eq_walkNL]
    exact walkNL_previous_code U hτ 0
  obtain ⟨hbase, hnext, _⟩ := sourceFlow_firstLeftExit_triangle U hτ
  have hUL : (kmswStage U (t - 1)).UL.dropLast.reverse = [] := hbase.2.2.2.1
  let j : TriangleCreationTime U := ⟨t - 1, Or.inl hc⟩
  let e := (kmswStage U (t - 1)).nextEdge + 1
  have hm : kmswLLCreatedEdge U (walkNL U hτ 0) = e := by
    rw [← sourceFlowNL_eq_walkNL]
    change kmswLLCreatedEdge U t = e
    dsimp only [kmswLLCreatedEdge, e]
    change (kmswStage U t).nextEdge = (kmswStage U (t - 1)).nextEdge + 2 at hnext
    omega
  have hcycle := kmswInfFaceSucc_stageTriangle_cycle U hfin j
  rw [stageTriangleDartTriple_left_fresh U j hc hUL] at hcycle
  have hface : kmswInfFaceSucc U hfin (e, false) = (act U (t - 1), false) :=
    hcycle.2.2.1
  have hfaceW := lPlus_window_triangle_faceSucc (H := H) hfin j
    (e, false) (act U (t - 1), false)
    (by
      rw [stageTriangleDartList, stageTriangleDartTriple_left_fresh U j hc hUL]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) hface
  change (kmswInfRot w (H.1 0)).symm
    (boundaryGluingEdgeMap W h k e, true) =
      (boundaryGluingEdgeMap W h k (act U (t - 1)), false) at hfaceW
  have hr := congrArg (kmswInfRot w (H.1 0)) hfaceW
  rw [Equiv.apply_symm_apply] at hr
  have hbeta : hatLimitEdgeMap U hτ (kmswLeftBoundaryEdge (hatCodes U hτ) 0) =
      act U (t - 1) := by
    rw [hattedLeftBoundaryBeta0EdgeCorrespondence_proved U hτ hfin
      (hatBoundaryHitWitnesses U hτ) 0,
      beta0_westBoundary_stream_eq_left_exit U hfin (hatBoundaryHitWitnesses U hτ) hτ 0]
  have hroot := lPlusUpperLeftGluedDart_initial_eq_primed_root hτ hqMode hfin hk hn
  have hrootval := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp hroot
  change (ULedges[0], true) = lMinusPrimedDartImage hτ (0, true) at hrootval
  rw [hrootval]
  change kmswInfRot w (H.1 0) _ =
    (boundaryGluingEdgeMap W h k (primedLimitEdgeMap U hτ 0),
      true ^^ primedLimitSideFlip U hτ 0)
  rw [primedLimitEdgeMap_zero, hm, primedLimitSideFlip_zero, Bool.xor_false]
  change kmswInfRot w (H.1 0)
    (boundaryGluingEdgeMap W h k
      (hatLimitEdgeMap U hτ (kmswLeftBoundaryEdge (hatCodes U hτ) 0)), false) = _
  rw [hbeta]
  exact hr.symm

/-- Helper toward Lemma 5.5: the primed factor at the initial east port
lands at the initial beta port in the glued carrier. -/
theorem lPlusPrimedExtendedRotation_initial_east
    (hn : 0 < (ULedges).length) :
    lPlusPrimedExtendedRotation hτ hqMode hfin
        (lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨0, hn⟩, true)) =
      lPlusBetaGluedDart hτ hqMode (0, false) := by
  rw [lPlusUpperLeftGluedDart_initial_eq_primed_root hτ hqMode hfin hk hn]
  let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)
  have he := TR.extendDomain_apply_image
    (Equiv.ofInjective _ (lPlusPrimedGluedDart_injective
      (hτ := hτ) (hqMode := hqMode))) (0, true)
  change lPlusPrimedExtendedRotation hτ hqMode hfin
    (lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (0, true)) =
    lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode) (TR (0, true)) at he
  rw [he, show TR (0, true) = _ from lPlusPrimedRotation_initial_root_corner hτ hfin]
  apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mpr
  change lMinusPrimedDartImage hτ
      (primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin 0, true) =
    (boundaryGluingHatEdgeMap W h k hτ
      ((lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode).boundary 0).1, false)
  rw [lMinusPrimedDartImage_boundary hτ hfin]
  change (boundaryGluingHatEdgeMap W h k hτ
      (kmswLeftBoundaryEdge (hatCodes U hτ) 0), false) =
    (boundaryGluingHatEdgeMap W h k hτ
      (kmswLeftBoundaryEdge (boltzmannKMSWStream
        (pathCode (boundaryFutureHattedPath k W))) 0), false)
  rw [boundaryGluing_decoded_stream W h k hτ]

variable {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (Tpath : InfinitePresentPath (shiftedStream W 0) (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)

local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "MH" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "F" => lPlusBlockDartImage (M := MH) hτ

include hp P Tpath hleft hk in
/-- Helper toward Lemma 5.5: the initial beta port first returns to the
initial upper-left east port in one ambient step, excluding all three blocks
vacuously in the open interval. -/
theorem lPlus_initial_beta_upperLeft_firstReturn (hn : 0 < (ULedges).length) :
    let a := lPlusBetaGluedDart hτ hqMode (0, false)
    let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨0, hn⟩, true)
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (D a).val = (D d).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (D a).val ∉ Set.range F := by
  refine ⟨1, Nat.zero_lt_one, ?_, fun j hj hjn => by omega⟩
  change kmswInfRot w (H.1 0)
      (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary 0).1, false) =
    (ULedges[0], true)
  have hb : ((MH).boundary 0).1 = kmswLeftBoundaryEdge (hatCodes U hτ) 0 := by
    change kmswLeftBoundaryEdge (boltzmannKMSWStream
      (pathCode (boundaryFutureHattedPath k W))) 0 = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  rw [hb]
  exact lPlus_upperLeft_initial_beta_successor (H := H) hτ hqMode hfin hk hn

include H hfin hk in
/-- Helper toward Lemma 5.5: from the initial upper-left east port, the
first return to the two future blocks is the hatted successor of the initial
beta port. The finite prefix is not included in this return set. -/
theorem lPlus_upperLeft_initial_east_future_firstReturn
    (hn : 0 < (ULedges).length) :
    let c : LPlusHattedDart MH :=
      ⟨(((MH).boundary 0).1, false),
        lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
    let J : LPlusHattedDart MH → ℕ × Bool :=
      fun d => (boundaryGluingHatEdgeMap W h k hτ d.val.1, d.val.2)
    let HR := lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
      ⟨boundaryFutureHattedPath k W, hqMode⟩
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (ULedges[0], true) = J (HR c) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (ULedges[0], true) ∉
          Set.range (lMinusPrimedDartImage hτ) ∪ Set.range J := by
  dsimp only
  let c : LPlusHattedDart MH :=
    ⟨(((MH).boundary 0).1, false),
      lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
  let J : LPlusHattedDart MH → ℕ × Bool :=
    fun d => (boundaryGluingHatEdgeMap W h k hτ d.val.1, d.val.2)
  let HR := lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
    ⟨boundaryFutureHattedPath k W, hqMode⟩
  let σ := kmswInfRot w (H.1 0)
  let x : ℕ × Bool := (ULedges[0], true)
  have hb : ((MH).boundary 0).1 = kmswLeftBoundaryEdge (hatCodes U hτ) 0 := by
    change kmswLeftBoundaryEdge (boltzmannKMSWStream
      (pathCode (boundaryFutureHattedPath k W))) 0 = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  have hcx : σ (J c) = x := by
    change kmswInfRot w (H.1 0)
      (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary 0).1, false) = _
    rw [hb]
    exact lPlus_upperLeft_initial_beta_successor (H := H) hτ hqMode hfin hk hn
  have hx : lMinusPrimedDartImage hτ (0, true) = x := by
    have he := lPlusUpperLeftGluedDart_initial_eq_primed_root hτ hqMode hfin hk hn
    exact ((lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp he).symm
  have hxnot : x ∉ Set.range J := by
    rintro ⟨d, hd⟩
    have he : boundaryGluingHatEdgeMap W h k hτ d.val.1 = ULedges[0] :=
      congrArg Prod.fst hd
    have hm : ULedges[0] ∈ boundaryGluingPrefixMinusEdges W h k ∩
        Set.range (boundaryGluingHatEdgeMap W h k hτ) :=
      ⟨lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩, ⟨d.val.1, he⟩⟩
    exact (Set.ext_iff.mp
      (boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk) _).mp hm
  obtain ⟨p, hp, hpret, hpgap⟩ := lMinusPrimedDartImage_firstReturn
    (H := H) hτ hfin (0, true)
  rw [hx, lPlusPrimedRotation_initial_root_corner hτ hfin,
    lMinusPrimedDartImage_boundary hτ hfin, ← hb] at hpret
  change (σ : _ → _)^[p] x = J c at hpret
  rw [hx] at hpgap
  change ∀ j : ℕ, 0 < j → j < p →
    (σ : _ → _)^[j] x ∉ Set.range (lMinusPrimedDartImage hτ) at hpgap
  obtain ⟨t, ht, htret, htgap⟩ := lPlusHattedDartImage_firstReturn
    (H := H) hτ hqMode hfin c
  change (σ : _ → _)^[t] (J c) = J (HR c) at htret
  change ∀ j : ℕ, 0 < j → j < t →
    (σ : _ → _)^[j] (J c) ∉ Set.range J at htgap
  have htone : 1 < t := by
    by_contra hh
    have he : t = 1 := by omega
    rw [he, Function.iterate_one, hcx] at htret
    exact hxnot ⟨HR c, htret.symm⟩
  have hperiod : (σ : _ → _)^[p + 1] (J c) = J c := by
    rw [Function.iterate_succ_apply, hcx, hpret]
  have htbound : t ≤ p + 1 := by
    by_contra hh
    exact htgap (p + 1) (by omega) (by omega) ⟨c, hperiod.symm⟩
  have hshift (j : ℕ) : (σ : _ → _)^[j] x = (σ : _ → _)^[j + 1] (J c) := by
    rw [Function.iterate_succ_apply, hcx]
  refine ⟨t - 1, by omega, ?_, ?_⟩
  · change (σ : _ → _)^[t - 1] x = J (HR c)
    rw [hshift, Nat.sub_add_cancel (by omega)]
    exact htret
  · intro j hj hjn
    rintro (hP | hH)
    · exact hpgap j hj (by omega) hP
    · apply htgap (j + 1) (by omega) (by omega)
      rw [← hshift]
      exact hH





































































































end DirectedDistances.PaperProofs.Section5
