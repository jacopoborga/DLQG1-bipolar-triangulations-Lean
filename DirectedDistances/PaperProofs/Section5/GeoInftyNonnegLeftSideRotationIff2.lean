/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundaryOrder5
import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideInterior2

/-! Helper toward Lemma 5.5: geometric rotation of the nonnegative left side. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: every newly allocated edge has its endpoints
on the original upper frontier or at vertices allocated since the cutoff.
This includes missing geometric edges. -/
theorem lPlus_late_edge_endpoints_frontier (w : ℕ → Fin 3) (t n : ℕ)
    (htn : t ≤ n) (e : ℕ)
    (he : (kmswStage w t).nextEdge ≤ e)
    (hen : e < (kmswStage w n).nextEdge) :
    UpperFrontierEndpoint (kmswStage w t) (edgeWest w e) ∧
      UpperFrontierEndpoint (kmswStage w t) (edgeEast w e) := by
  induction n, htn using Nat.le_induction with
  | base => omega
  | succ n htn ih =>
    by_cases hold : e < (kmswStage w n).nextEdge
    · exact ih hold
    have hnew : (kmswStage w n).nextEdge ≤ e := by omega
    let s := kmswStage w n
    have hactive := kmswStage_act_endpoint_since w htn (Nat.lt_succ_self n)
    have hfresh : UpperFrontierEndpoint (kmswStage w t) s.nextVertex :=
      Or.inr (CutConverse.nextVertex_mono w htn)
    have hends := edge_endpoints_eq w hen
    rw [← hends.1, ← hends.2]
    change UpperFrontierEndpoint _ ((kmswStep s (w n)).west e) ∧
      UpperFrontierEndpoint _ ((kmswStep s (w n)).east e)
    change e < (kmswStep s (w n)).nextEdge at hen
    change s.nextEdge ≤ e at hnew
    change UpperFrontierEndpoint _ (s.west s.active) ∧
      UpperFrontierEndpoint _ (s.east s.active) at hactive
    cases hc : kmswCodeStep (w n) with
    | up =>
      have hid : e = s.nextEdge ∨ e = s.nextEdge + 1 := by
        simp only [kmswStep, hc, kmswStepOfStep, State.addEdge] at hen
        omega
      rcases hid with rfl | rfl
      · simpa [kmswStep, hc, kmswStepOfStep, State.addEdge] using
          (show UpperFrontierEndpoint (kmswStage w t) (s.west s.active) ∧
            UpperFrontierEndpoint (kmswStage w t) s.nextVertex from ⟨hactive.1, hfresh⟩)
      · simpa [kmswStep, hc, kmswStepOfStep, State.addEdge] using
          (show UpperFrontierEndpoint (kmswStage w t) s.nextVertex ∧
            UpperFrontierEndpoint (kmswStage w t) (s.east s.active) from ⟨hfresh, hactive.2⟩)
    | down =>
      cases hs : s.UR with
      | nil =>
        have hid : e = s.nextEdge := by
          simp only [kmswStep, hc, kmswStepOfStep, hs, State.addEdge] at hen
          omega
        subst e
        simpa [kmswStep, hc, kmswStepOfStep, hs, State.addEdge] using
          (show UpperFrontierEndpoint (kmswStage w t) (s.east s.active) ∧
            UpperFrontierEndpoint (kmswStage w t) s.nextVertex from
            ⟨hactive.2, hfresh⟩)
      | cons a as =>
        simp only [kmswStep, hc, kmswStepOfStep, hs] at hen
        omega
    | left =>
      cases hs : s.UL.dropLast.reverse with
      | nil =>
        have hid : e = s.nextEdge ∨ e = s.nextEdge + 1 := by
          simp only [kmswStep, hc, kmswStepOfStep, hs, State.addEdge] at hen
          omega
        rcases hid with rfl | rfl
        · simpa [kmswStep, hc, kmswStepOfStep, hs, State.addEdge] using
            (show UpperFrontierEndpoint (kmswStage w t) s.nextVertex ∧
              UpperFrontierEndpoint (kmswStage w t) (s.east s.active) from
              ⟨hfresh, hactive.2⟩)
        · simpa [kmswStep, hc, kmswStepOfStep, hs, State.addEdge] using
            (show UpperFrontierEndpoint (kmswStage w t) s.nextVertex ∧
              UpperFrontierEndpoint (kmswStage w t) (s.west s.active) from
              ⟨hfresh, hactive.1⟩)
      | cons a as =>
        have hid : e = s.nextEdge := by
          simp only [kmswStep, hc, kmswStepOfStep, hs, State.addEdge] at hen
          omega
        subst e
        have ha : a ∈ s.UL := List.mem_of_mem_dropLast
          (List.mem_reverse.mp (by rw [hs]; exact List.mem_cons_self))
        have hfront := kmswStage_upperFrontier_endpoints w t n htn a
          (List.mem_append_left _ ha)
        simpa [kmswStep, hc, kmswStepOfStep, hs, State.addEdge] using
          (show UpperFrontierEndpoint (kmswStage w t) (s.west a) ∧
            UpperFrontierEndpoint (kmswStage w t) (s.east s.active) from
            ⟨hfront.1, hactive.2⟩)

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}

/-- Helper toward Lemma 5.5: a positive boundary hit is a fresh down step
from an empty upper-right list. -/
theorem lPlus_positive_hit_fresh (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {k : ℤ} (hk : 0 < k) :
    ∃ m, boundaryHitTime w h k = m + 1 ∧ w m = 2 ∧
      (kmswStage w m).UR = [] := by
  have ht : boundaryHitTime w h k = Nat.find (h.rightHit k (by omega)) := by
    simp only [boundaryHitTime, dite_eq_right (by omega : k ≠ 0),
      dite_eq_left hk]
  have hmin (j : ℕ) (hj : j < boundaryHitTime w h k) : R w j ≠ -k := by
    rw [ht] at hj
    exact Nat.find_min (h.rightHit k (by omega)) hj
  have hstrict (j : ℕ) : j < boundaryHitTime w h k → -k < R w j := by
    induction j with
    | zero => simp only [R, Finset.sum_range_zero]; omega
    | succ j ih =>
      intro hj
      have hp := ih (by omega)
      have hs : R w (j + 1) = R w j + (lazyTwoDimensionalStep (w j)).2 :=
        Finset.sum_range_succ _ _
      have hl : -1 ≤ (lazyTwoDimensionalStep (w j)).2 := by
        unfold lazyTwoDimensionalStep
        split_ifs <;> omega
      have hn := hmin (j + 1) hj
      omega
  have hhit := boundaryHitTime_right_spec w h (by omega : 1 ≤ k)
  have hpos : 0 < boundaryHitTime w h k := by
    by_contra hn
    have hz : boundaryHitTime w h k = 0 := by omega
    rw [hz] at hhit
    simp only [R, Finset.sum_range_zero] at hhit
    omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : boundaryHitTime w h k ≠ 0)
  change boundaryHitTime w h k = m + 1 at hm
  have hp := hstrict m (by omega)
  have hs : R w (m + 1) = R w m + (lazyTwoDimensionalStep (w m)).2 :=
    Finset.sum_range_succ _ _
  rw [hm] at hhit
  have hc : w m = 2 := by
    apply Fin.ext
    have hb := (w m).isLt
    unfold lazyTwoDimensionalStep at hs
    split_ifs at hs <;> omega
  have hprev : R w m = -k + 1 := by
    rw [hc, lazyTwoDimensionalStep_two] at hs
    dsimp only at hs
    omega
  have hrecord : minR w m = R w m := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (R w) m
    have hb := hstrict j (by omega)
    have hl := runningMin_le (R w) m m le_rfl
    change minR w m = R w j at he
    change minR w m ≤ R w m at hl
    omega
  refine ⟨m, hm, hc, ?_⟩
  have hlen := kmswStage_UR_length w m
  rw [hrecord] at hlen
  exact List.length_eq_zero_iff.mp (by omega)

/-- Helper toward Lemma 5.5: every future dart is based on the stopped
upper frontier or at a vertex allocated after that stage. -/
theorem lPlus_future_dart_endpoint_frontier
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) (a : ℕ × Bool) :
    UpperFrontierEndpoint
      (kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k))
      (kmswLimitDartVertex (shiftedStream W 0)
        (boundaryGluingEdgeMap W h k a.1, a.2)) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let e := boundaryGluingEdgeMap W h k a.1
  by_cases he : e < (kmswStage w t).nextEdge
  · have hmem : e ∈ boundaryGluingPrefixEdges W h k ∩
        Set.range (boundaryGluingEdgeMap W h k) := ⟨he, ⟨a.1, rfl⟩⟩
    rw [boundaryGluingPrefixEdges_inter_futureRange W h k hτ] at hmem
    have hupper : e ∈ (kmswStage w t).UL ++ (kmswStage w t).UR := by
      rcases hmem with hl | hr
      · exact List.mem_append_left _ (List.mem_of_mem_dropLast hl)
      · rcases hr with hr | hr
        · have hid : e = act w t := hr
          rw [hid]
          obtain ⟨xs, hxs⟩ := kmswStage_UL_last w t
          apply List.mem_append_left
          rw [hxs]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · exact List.mem_append_right _ hr
    have hends := edge_endpoints_eq w he
    apply Or.inl
    refine ⟨e, hupper, ?_⟩
    cases hb : a.2
    · exact Or.inl (by simpa only [kmswLimitDartVertex, hb, Bool.false_eq_true,
        ↓reduceIte] using hends.1)
    · exact Or.inr (by simpa only [kmswLimitDartVertex, hb, ↓reduceIte] using hends.2)
  · have hends := lPlus_late_edge_endpoints_frontier w t (max t e)
      (Nat.le_max_left _ _) e (by omega)
      (kmsw_nextEdge_unbounded w e (max t e) (Nat.le_max_right _ _))
    cases hb : a.2
    · exact hends.1
    · exact hends.2

/-- Helper toward Lemma 5.5: a vertex shared by the deleted prefix and
the future is an endpoint of the upper-left attachment, also at index zero. -/
theorem lPlus_prefix_future_shared_endpoint
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) (hk : 0 ≤ k)
    (a : LPlusPrefixDart W h k) (b : ℕ × Bool)
    (hv : kmswLimitDartVertex (shiftedStream W 0) a.val =
      kmswLimitDartVertex (shiftedStream W 0)
        (boundaryGluingEdgeMap W h k b.1, b.2)) :
    ∃ e ∈ boundaryGluingUpperLeftEdges W h k,
      kmswLimitDartVertex (shiftedStream W 0) (e, false) =
          kmswLimitDartVertex (shiftedStream W 0) a.val ∨
        kmswLimitDartVertex (shiftedStream W 0) (e, true) =
          kmswLimitDartVertex (shiftedStream W 0) a.val := by
  by_cases hk0 : k = 0
  · subst k
    exact ((Set.ext_iff.mp (lPlusPrefixMinusEdges_zero (W := W) (h := h))
      a.val.1).mp a.property).elim
  have hkpos : 0 < k := by omega
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  obtain ⟨m, hm, hc, hUR⟩ := lPlus_positive_hit_fresh w h hkpos
  let s := kmswStage w m
  change s.UR = [] at hUR
  have hstage : kmswStage w t = kmswStepOfStep s .down := by
    change kmswStage w (boundaryHitTime w h k) = _
    rw [hm]
    change kmswStep s (w m) = _
    rw [hc]
    rfl
  have ha : a.val.1 < s.nextEdge := by
    have ha := (Set.ext_iff.mp
      (lPlusPrefixMinusEdges_eq_previousStage (W := W) (h := h) hkpos)
        a.val.1).mp a.property
    change a.val.1 < (kmswStage w (boundaryHitTime w h k - 1)).nextEdge at ha
    simpa only [hm, Nat.add_sub_cancel] using ha
  have habound := kmswStage_endpoints_lt_nextVertex w m a.val.1 ha
  have haends := edge_endpoints_eq w ha
  have hvbound : kmswLimitDartVertex w a.val < s.nextVertex := by
    cases hb : a.val.2
    · simpa only [kmswLimitDartVertex, hb, Bool.false_eq_true, ↓reduceIte,
        ← haends.1] using habound.1
    · simpa only [kmswLimitDartVertex, hb, ↓reduceIte,
        ← haends.2] using habound.2
  have hf := lPlus_future_dart_endpoint_frontier hτ b
  rw [← hv] at hf
  change UpperFrontierEndpoint (kmswStage w t) (kmswLimitDartVertex w a.val) at hf
  rcases hf with ⟨e, he, hend⟩ | hfresh
  · have he' : e ∈ s.UL ∨ e = s.nextEdge := by
      simpa only [hstage, kmswStepOfStep, hUR, State.addEdge,
        List.append_nil, List.mem_append, List.mem_singleton] using he
    rcases he' with heold | rfl
    · have heb : e < s.nextEdge := by
        exact (kmswStage_boundary_ids_lt_nextEdge w m).2 e
          (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ heold)))
      have heends := edge_endpoints_eq w (heb.trans_le
        (kmswStage_nextEdge_mono w (by omega : m ≤ t)))
      refine ⟨e, ?_, ?_⟩
      · change e ∈ (kmswStage w t).UL.dropLast
        simpa only [hstage, kmswStepOfStep, hUR, State.addEdge,
          List.dropLast_concat] using heold
      · rw [heends.1, heends.2] at hend
        exact hend
    · have hinc : s.east s.active = kmswLimitDartVertex w a.val := by
        rcases hend with hw | he
        · simpa only [hstage, kmswStepOfStep, hUR, State.addEdge, ↓reduceIte] using hw
        · have hbad : s.nextVertex = kmswLimitDartVertex w a.val := by
            simpa only [hstage, kmswStepOfStep, hUR, State.addEdge, ↓reduceIte] using he
          omega
      have hac := (kmswStage_boundary_ids_lt_nextEdge w m).1
      have heac := (edge_endpoints_eq w hac).2
      refine ⟨s.active, ?_, Or.inr (heac.symm.trans hinc)⟩
      change s.active ∈ (kmswStage w t).UL.dropLast
      rw [hstage]
      simp only [kmswStepOfStep, hUR, State.addEdge, List.dropLast_concat]
      obtain ⟨xs, hxs⟩ := kmswStage_UL_last w m
      rw [hxs]
      exact List.mem_append_right _ (List.mem_singleton_self _)
  · have hh : s.nextVertex + 1 ≤ kmswLimitDartVertex w a.val := by
      simpa only [hstage, kmswStepOfStep, hUR, State.addEdge] using hfresh
    omega

variable {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : 0 ≤ k)

local notation "w" => shiftedStream W 0
local notation "U" => boundaryGluingFutureStream W h k
local notation "MH" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "F" => lPlusBlockDartImage (M := MH) hτ
local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "R" => lPlusGluedSplicedRotation (hτ := hτ) (hp := hp) (P := P)
  (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) (hk := hk)
local notation "B" => (Set.ofPred fun v : ℕ => ∃ e : ℕ,
  e ∈ boundaryGluingUpperLeftEdges W h k ∪ boundaryGluingBetaEdges W h k hτ ∧
  (kmswLimitDartVertex w (e, false) = v ∨ kmswLimitDartVertex w (e, true) = v))

include hqMode hfin in
/-- Helper toward Lemma 5.5: every vertex shared by primed and hatted
darts is on the beta attachment, including its initial vertex. -/
theorem lPlus_primed_hatted_shared_endpoint (p d : ℕ × Bool)
    (hv : kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) =
      kmswLimitDartVertex w (boundaryGluingHatEdgeMap W h k hτ d.1, d.2)) :
    ∃ e ∈ boundaryGluingBetaEdges W h k hτ,
      kmswLimitDartVertex w (e, false) =
          kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) ∨
        kmswLimitDartVertex w (e, true) =
          kmswLimitDartVertex w (lMinusPrimedDartImage hτ p) := by
  obtain hz | ⟨i, hi⟩ := lMinus_shared_dart_endpoint_interface hτ hfin p d hv
  · let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    let M := geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime .left q
    have hbdy : ((M).boundary 0).1 = kmswLeftBoundaryEdge (hatCodes U hτ) 0 := by
      change kmswLeftBoundaryEdge
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) 0 = _
      rw [boundaryGluing_decoded_stream W h k hτ]
    refine ⟨boundaryGluingHatEdgeMap W h k hτ
      (kmswLeftBoundaryEdge (hatCodes U hτ) 0), ⟨0, rfl⟩, Or.inl ?_⟩
    rw [← hbdy, lMinus_hatted_dart_endpoint hτ (((M).boundary 0).1, false),
      (lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩]
    exact hz.symm
  · exact ⟨_, ⟨i, rfl⟩, Or.inr hi.symm⟩

include Tpath hfin hleft in
/-- Helper toward Lemma 5.5: the positive prefix permutation evaluates as
the previous stage rotation under the exact stage-dart correspondence. -/
theorem lPlusPrefixRotation_apply (hkpos : 0 < k) (a : LPlusPrefixDart W h k) :
    lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
      (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
      (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk a =
    lPlusPrefixStageDart hkpos
      (stageRot w (boundaryHitTime w h k - 1) (lPlusPrefixDartStage hkpos a)) := by
  let f := lPlusPrefixDartStage (W := W) (h := h) hkpos
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun d : StageDart _ => (d.1.val, d.2)) hab
  have hf : Function.Bijective f := ⟨hinj, fun d =>
    ⟨lPlusPrefixStageDart hkpos d, rfl⟩⟩
  have hrot : lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
      (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
      (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk =
      Equiv.permCongr (Equiv.ofBijective f hf).symm
        (stageRot w (boundaryHitTime w h k - 1)) := by
    unfold lPlusPrefixRotation
    rw [dite_eq_left hkpos]
  rw [hrot]
  simp only [Equiv.permCongr_apply, Equiv.symm_symm]
  apply hinj
  exact (Equiv.ofBijective f hf).apply_symm_apply _

include hk in
/-- Helper toward Lemma 5.5: a vertex common to the prefix and either
future block belongs to the specified gluing boundary. -/
theorem lPlus_prefix_other_shared_endpoint
    (a : LPlusPrefixDart W h k) (b : Sum LPlusPrimedDart (LPlusHattedDart MH))
    (hv : kmswLimitDartVertex w a.val = kmswLimitDartVertex w (F (.inr b))) :
    kmswLimitDartVertex w a.val ∈ B := by
  have hf : ∃ c : ℕ × Bool,
      F (.inr b) = (boundaryGluingEdgeMap W h k c.1, c.2) := by
    cases b with
    | inl p => exact ⟨primedLimitDartMap U hτ p, rfl⟩
    | inr d => exact ⟨(hatLimitEdgeMap U hτ d.val.1, d.val.2), rfl⟩
  obtain ⟨c, hc⟩ := hf
  rw [hc] at hv
  obtain ⟨e, he, hend⟩ := lPlus_prefix_future_shared_endpoint hτ hk a c hv
  exact ⟨e, Or.inl he, hend⟩

include hfin in
/-- Helper toward Lemma 5.5: a vertex common to the primed and hatted
blocks belongs to the specified gluing boundary. -/
theorem lPlus_primed_hatted_shared_endpoint_mem
    (p : LPlusPrimedDart) (d : LPlusHattedDart MH)
    (hv : kmswLimitDartVertex w (F (.inr (.inl p))) =
      kmswLimitDartVertex w (F (.inr (.inr d)))) :
    kmswLimitDartVertex w (F (.inr (.inl p))) ∈ B := by
  obtain ⟨e, he, hend⟩ := lPlus_primed_hatted_shared_endpoint hτ hqMode hfin p d.val hv
  exact ⟨e, Or.inr he, hend⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: away from the attachment vertices, the
prefix's own first return is its first return in the complete left side. -/
theorem lPlus_prefix_interior_side_rotation
    (a : LPlusPrefixDart W h k) (hd : kmswLimitDartVertex w a.val ∉ B) :
    (S).rotation a.val
      (lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
        (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
        (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk a).val := by
  have hkpos : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    have ha : a.val.1 ∈ boundaryGluingPrefixMinusEdges W h 0 := hk0 ▸ a.property
    exact ((Set.ext_iff.mp (lPlusPrefixMinusEdges_zero (W := W) (h := h))
      a.val.1).mp ha).elim
  rw [lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk hkpos]
  obtain ⟨n, hn, hret, hgap⟩ := lPlusPrefixDartImage_firstReturn
    (H := H) hτ longest hqMode hkpos a
  refine ⟨n, hn, hret, ?_⟩
  intro j hj hjn hs
  have hs' : ((kmswInfRot w (H.1 0) : _ → _)^[j] a.val) ∈ Set.range F := by
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    exact hs
  obtain ⟨b, hb⟩ := hs'
  cases b with
  | inl b => exact hgap j hj hjn ⟨b, hb⟩
  | inr b =>
    have hv : kmswLimitDartVertex w a.val = kmswLimitDartVertex w (F (.inr b)) := by
      have hpow := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
        a.val ((kmswInfRot w (H.1 0) : _ → _)^[j] a.val)).mp
          ⟨j, by simp only [Equiv.Perm.coe_pow]⟩
      exact hpow.trans (congrArg (kmswLimitDartVertex w) hb.symm)
    exact hd (lPlus_prefix_other_shared_endpoint hτ hqMode hk a b hv)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: outside the attachments, the primed block
return has no intervening dart from the prefix or hatted block. -/
theorem lPlus_primed_interior_side_rotation (p : LPlusPrimedDart)
    (hd : kmswLimitDartVertex w (F (.inr (.inl p))) ∉ B) :
    (S).rotation (F (.inr (.inl p)))
      (F (.inr (.inl (kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) p)))) := by
  obtain ⟨n, hn, hret, hgap⟩ := lPlusPrimedDartImage_firstReturn
    (H := H) hτ hqMode hfin p
  refine ⟨n, hn, hret, ?_⟩
  intro j hj hjn hs
  have hs' : ((kmswInfRot w (H.1 0) : _ → _)^[j] (F (.inr (.inl p)))) ∈
      Set.range F := by
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    exact hs
  obtain ⟨b, hb⟩ := hs'
  have hvb : kmswLimitDartVertex w (F b) =
      kmswLimitDartVertex w (F (.inr (.inl p))) := by
    have hpow := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
      (F (.inr (.inl p))) ((kmswInfRot w (H.1 0) : _ → _)^[j]
        (F (.inr (.inl p))))).mp ⟨j, by simp only [Equiv.Perm.coe_pow]⟩
    exact (congrArg (kmswLimitDartVertex w) hb).trans hpow.symm
  cases b with
  | inl a => exact hd (hvb ▸ lPlus_prefix_other_shared_endpoint hτ hqMode hk a (.inl p) hvb)
  | inr b =>
    cases b with
    | inl b => exact hgap j hj hjn ⟨b, hb⟩
    | inr d => exact hd (lPlus_primed_hatted_shared_endpoint_mem hτ hqMode hfin p d hvb.symm)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: outside the attachments, the hatted block
return has no intervening dart from the prefix or primed block. -/
theorem lPlus_hatted_interior_side_rotation (d : LPlusHattedDart MH)
    (hd : kmswLimitDartVertex w (F (.inr (.inr d))) ∉ B) :
    (S).rotation (F (.inr (.inr d)))
      (F (.inr (.inr (lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
        ⟨boundaryFutureHattedPath k W, hqMode⟩ d)))) := by
  obtain ⟨n, hn, hret, hgap⟩ := lPlusHattedDartImage_firstReturn
    (H := H) hτ hqMode hfin d
  refine ⟨n, hn, hret, ?_⟩
  intro j hj hjn hs
  have hs' : ((kmswInfRot w (H.1 0) : _ → _)^[j] (F (.inr (.inr d)))) ∈
      Set.range F := by
    rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
    exact hs
  obtain ⟨b, hb⟩ := hs'
  have hvb : kmswLimitDartVertex w (F b) =
      kmswLimitDartVertex w (F (.inr (.inr d))) := by
    have hpow := (kmswInfRot_exists_pow_iff_endpoint w (H.1 0)
      (F (.inr (.inr d))) ((kmswInfRot w (H.1 0) : _ → _)^[j]
        (F (.inr (.inr d))))).mp ⟨j, by simp only [Equiv.Perm.coe_pow]⟩
    exact (congrArg (kmswLimitDartVertex w) hb).trans hpow.symm
  cases b with
  | inl a => exact hd (hvb ▸ lPlus_prefix_other_shared_endpoint hτ hqMode hk a (.inr d) hvb)
  | inr b =>
    cases b with
    | inl p => exact hd (hvb ▸ lPlus_primed_hatted_shared_endpoint_mem hτ hqMode hfin p d hvb)
    | inr b => exact hgap j hj hjn ⟨b, hb⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: away from both gluing boundaries, the
three-block splice agrees in both directions with geometric side rotation. -/
theorem lPlusGluedSplicedRotation_interior (d : Q)
    (hd : kmswLimitDartVertex w (D d).val ∉ B) :
    ∀ e : Q, (R d = e) ↔ (S).rotation (D d).val (D e).val := by
  let IP := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let IT := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
  let IH := lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
  let EP := Equiv.ofInjective IP (lPlusPrefixGluedDart_injective
    (hτ := hτ) (hqMode := hqMode))
  let ET := Equiv.ofInjective IT (lPlusPrimedGluedDart_injective
    (hτ := hτ) (hqMode := hqMode))
  let EH := Equiv.ofInjective IH (lPlusHattedGluedDart_injective
    (hτ := hτ) (hqMode := hqMode))
  let PR : Equiv.Perm (LPlusPrefixDart W h k) :=
    lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
    (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
    (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)
  let HR : Equiv.Perm (LPlusHattedDart MH) :=
    lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
    ⟨boundaryFutureHattedPath k W, hqMode⟩
  have hPF (a : LPlusPrefixDart W h k)
      (b : Sum LPlusPrimedDart (LPlusHattedDart MH))
      (he : IP a = (⟦Sum.inr b⟧ : Q)) : kmswLimitDartVertex w a.val ∈ B := by
    exact lPlus_prefix_other_shared_endpoint hτ hqMode hk a b
      (congrArg (kmswLimitDartVertex w)
        ((lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) (.inl a) (.inr b)).mp he))
  have hTH (p : LPlusPrimedDart) (a : LPlusHattedDart MH)
      (he : IT p = IH a) : kmswLimitDartVertex w (F (.inr (.inl p))) ∈ B := by
    exact lPlus_primed_hatted_shared_endpoint_mem hτ hqMode hfin p a
      (congrArg (kmswLimitDartVertex w)
        ((lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
          (.inr (.inl p)) (.inr (.inr a))).mp he))
  have hPnot (a : LPlusPrefixDart W h k) (ha : kmswLimitDartVertex w a.val ∉ B) :
      IP a ∉ Set.range IT ∧ IP a ∉ Set.range IH := by
    constructor
    · rintro ⟨p, hp⟩
      exact ha (hPF a (.inl p) hp.symm)
    · rintro ⟨p, hp⟩
      exact ha (hPF a (.inr p) hp.symm)
  have hTnot (p : LPlusPrimedDart)
      (ha : kmswLimitDartVertex w (F (.inr (.inl p))) ∉ B) :
      IT p ∉ Set.range IP ∧ IT p ∉ Set.range IH := by
    constructor
    · rintro ⟨a, he⟩
      have hv := congrArg (fun q : Q => kmswLimitDartVertex w (D q).val) he
      exact ha (hv ▸ hPF a (.inl p) he)
    · rintro ⟨a, he⟩
      exact ha (hTH p a he.symm)
  have hHnot (a : LPlusHattedDart MH)
      (ha : kmswLimitDartVertex w (F (.inr (.inr a))) ∉ B) :
      IH a ∉ Set.range IP ∧ IH a ∉ Set.range IT := by
    constructor
    · rintro ⟨p, he⟩
      have hv := congrArg (fun q : Q => kmswLimitDartVertex w (D q).val) he
      exact ha (hv ▸ hPF p (.inr a) he)
    · rintro ⟨p, he⟩
      have hv := congrArg (fun q : Q => kmswLimitDartVertex w (D q).val) he
      exact ha (hv ▸ hTH p a he)
  have hr : (S).rotation (D d).val (D (R d)).val := by
    revert hd
    induction d using Quotient.inductionOn with
    | h a =>
      intro hd
      cases a with
      | inl a =>
        have ha : kmswLimitDartVertex w a.val ∉ B := hd
        have hrot := lPlus_prefix_interior_side_rotation
          hτ hp P hqMode Tpath hfin hleft hk a ha
        obtain ⟨hT, hH⟩ := hPnot a ha
        have hR : R (IP a) = IP (PR a) := by
          change PR.extendDomain EP (TR.extendDomain ET (HR.extendDomain EH (IP a))) = _
          rw [Equiv.Perm.extendDomain_apply_not_subtype _ EH hH,
            Equiv.Perm.extendDomain_apply_not_subtype _ ET hT]
          exact PR.extendDomain_apply_image EP a
        change (S).rotation (D (IP a)).val (D (R (IP a))).val
        rw [hR]
        exact hrot
      | inr a =>
        cases a with
        | inl p =>
          have ha : kmswLimitDartVertex w (F (.inr (.inl p))) ∉ B := hd
          have hrot := lPlus_primed_interior_side_rotation
            hτ hp P hqMode Tpath hfin hleft hk p ha
          have hv : kmswLimitDartVertex w (F (.inr (.inl (TR p)))) =
              kmswLimitDartVertex w (F (.inr (.inl p))) := by
            obtain ⟨n, _, hn, _⟩ := hrot
            exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
              ⟨n, by simpa only [Equiv.Perm.coe_pow] using hn⟩).symm
          have hP := (hTnot (TR p) (hv ▸ ha)).1
          have hH := (hTnot p ha).2
          have hR : R (IT p) = IT (TR p) := by
            change PR.extendDomain EP (TR.extendDomain ET (HR.extendDomain EH (IT p))) = _
            rw [Equiv.Perm.extendDomain_apply_not_subtype _ EH hH]
            have hT := TR.extendDomain_apply_image ET p
            change TR.extendDomain ET (IT p) = IT (TR p) at hT
            rw [hT, Equiv.Perm.extendDomain_apply_not_subtype _ EP hP]
          change (S).rotation (D (IT p)).val (D (R (IT p))).val
          rw [hR]
          exact hrot
        | inr a =>
          have ha : kmswLimitDartVertex w (F (.inr (.inr a))) ∉ B := hd
          have hrot := lPlus_hatted_interior_side_rotation
            hτ hp P hqMode Tpath hfin hleft hk a ha
          have hv : kmswLimitDartVertex w (F (.inr (.inr (HR a)))) =
              kmswLimitDartVertex w (F (.inr (.inr a))) := by
            obtain ⟨n, _, hn, _⟩ := hrot
            change (kmswInfRot w (H.1 0) : _ → _)^[n] (F (.inr (.inr a))) =
              F (.inr (.inr (HR a))) at hn
            exact ((kmswInfRot_exists_pow_iff_endpoint w (H.1 0) _ _).mp
              ⟨n, by simpa only [Equiv.Perm.coe_pow] using hn⟩).symm
          obtain ⟨hP, hT⟩ := hHnot (HR a) (hv ▸ ha)
          have hR : R (IH a) = IH (HR a) := by
            change PR.extendDomain EP (TR.extendDomain ET (HR.extendDomain EH (IH a))) = _
            have hH := HR.extendDomain_apply_image EH a
            change HR.extendDomain EH (IH a) = IH (HR a) at hH
            rw [hH, Equiv.Perm.extendDomain_apply_not_subtype _ ET hT,
              Equiv.Perm.extendDomain_apply_not_subtype _ EP hP]
          change (S).rotation (D (IH a)).val (D (R (IH a))).val
          rw [hR]
          exact hrot
  intro e
  constructor
  · rintro rfl
    exact hr
  · intro he
    apply (D).injective
    apply Subtype.ext
    obtain ⟨n, hn, hne, hngap⟩ := hr
    obtain ⟨m, hm, hme, hmgap⟩ := he
    have hnm : n = m := by
      apply Nat.le_antisymm
      · by_contra hnot
        exact hngap m hm (by omega) (hme.symm ▸ (D e).property)
      · by_contra hnot
        exact hmgap n hn (by omega) (hne.symm ▸ (D (R d)).property)
    exact hne.symm.trans (hnm ▸ hme)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the unadjusted three-factor candidate fixes
every positive outgoing beta port. This records its boundary behavior without
identifying that behavior with the geometric successor. -/
theorem lPlusGluedSplicedRotation_beta_outgoing_fixed (i : ℕ) :
    let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    let b : LPlusHattedDart MH := ⟨(((MH).boundary (i + 1)).1, false),
      lMinus_hatted_boundary_mem _ q (i + 1)⟩
    R (lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode) b) =
      lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode) b := by
  dsimp only
  let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  let a : LPlusHattedDart MH := ⟨(((MH).boundary i).1, true),
    lMinus_hatted_boundary_mem _ q i⟩
  let b : LPlusHattedDart MH := ⟨(((MH).boundary (i + 1)).1, false),
    lMinus_hatted_boundary_mem _ q (i + 1)⟩
  let IP := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let IT := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
  let IH := lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
  let EP := Equiv.ofInjective IP (lPlusPrefixGluedDart_injective
    (hτ := hτ) (hqMode := hqMode))
  let ET := Equiv.ofInjective IT (lPlusPrimedGluedDart_injective
    (hτ := hτ) (hqMode := hqMode))
  let EH := Equiv.ofInjective IH (lPlusHattedGluedDart_injective
    (hτ := hτ) (hqMode := hqMode))
  let PR : Equiv.Perm (LPlusPrefixDart W h k) :=
    lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H) (hLL := hLL)
      (longest := longest) (hτ := hτ) (hp := hp) (P := P) (hqMode := hqMode)
      (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  let TR := kmswInfRot (primedCode (primedSimInput U) hτ)
    (primedCode_finiteIncidence U hτ hfin)
  let HR : Equiv.Perm (LPlusHattedDart MH) :=
    lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp) q
  let Bidx := primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin
  have hbdy (j : ℕ) : ((MH).boundary j).1 = kmswLeftBoundaryEdge (hatCodes U hτ) j := by
    change kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) j = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  have hH : HR b = a := lMinusHattedRotation_boundary_corner _ q i
  have hPa : IT (Bidx i, false) = IH a := by
    apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
      (.inr (.inl (Bidx i, false))) (.inr (.inr a))).mpr
    change lMinusPrimedDartImage hτ (Bidx i, false) =
      (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary i).1, true)
    rw [lMinusPrimedDartImage_boundary hτ hfin i false, hbdy i]
    rfl
  have hPb : IT (Bidx (i + 1), true) = IH b := by
    apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
      (.inr (.inl (Bidx (i + 1), true))) (.inr (.inr b))).mpr
    change lMinusPrimedDartImage hτ (Bidx (i + 1), true) =
      (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary (i + 1)).1, false)
    rw [lMinusPrimedDartImage_boundary hτ hfin (i + 1) true, hbdy (i + 1)]
    rfl
  have hP : IH b ∉ Set.range IP := by
    rintro ⟨c, hc⟩
    have he := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode)
      (.inl c) (.inr (.inr b))).mp hc
    have he' := congrArg Prod.fst he
    change c.val.1 = boundaryGluingHatEdgeMap W h k hτ b.val.1 at he'
    have hm : boundaryGluingHatEdgeMap W h k hτ b.val.1 ∈
        boundaryGluingPrefixMinusEdges W h k ∩
          Set.range (boundaryGluingHatEdgeMap W h k hτ) :=
      ⟨he' ▸ c.property, ⟨b.val.1, rfl⟩⟩
    exact (Set.ext_iff.mp
      (boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk) _).mp hm
  change PR.extendDomain EP (TR.extendDomain ET (HR.extendDomain EH (IH b))) = IH b
  have hEH := HR.extendDomain_apply_image EH b
  change HR.extendDomain EH (IH b) = IH (HR b) at hEH
  rw [hEH, hH, ← hPa]
  have hET := TR.extendDomain_apply_image ET (Bidx i, false)
  change TR.extendDomain ET (IT (Bidx i, false)) = IT (TR (Bidx i, false)) at hET
  rw [hET]
  have hT : TR (Bidx i, false) = (Bidx (i + 1), true) :=
    lMinusPrimedRotation_boundary_corner hτ hfin i
  rw [hT, hPb, Equiv.Perm.extendDomain_apply_not_subtype _ EP hP]

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a positive outgoing beta port cannot be its
own geometric side successor. Its hatted return reaches a distinct reverse
port before any return to itself. -/
theorem lPlus_beta_outgoing_not_self_rotation (i : ℕ) :
    let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    let b : LPlusHattedDart MH := ⟨(((MH).boundary (i + 1)).1, false),
      lMinus_hatted_boundary_mem _ q (i + 1)⟩
    ¬ (S).rotation (F (.inr (.inr b))) (F (.inr (.inr b))) := by
  dsimp only
  let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  let a : LPlusHattedDart MH := ⟨(((MH).boundary i).1, true),
    lMinus_hatted_boundary_mem _ q i⟩
  let b : LPlusHattedDart MH := ⟨(((MH).boundary (i + 1)).1, false),
    lMinus_hatted_boundary_mem _ q (i + 1)⟩
  have hcorner : lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp) q b = a :=
    lMinusHattedRotation_boundary_corner _ q i
  obtain ⟨t, ht, hte, htgap⟩ := lPlusHattedDartImage_firstReturn
    (H := H) hτ hqMode hfin b
  change (kmswInfRot w (H.1 0) : _ → _)^[t] (F (.inr (.inr b))) =
    F (.inr (.inr (lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp) q b))) at hte
  rw [hcorner] at hte
  intro hself
  obtain ⟨n, hn, hne, hngap⟩ := hself
  rcases lt_trichotomy t n with htn | heq | hnt
  · apply hngap t ht htn
    rw [hte]
    exact lPlusBlockDartImage_mem hτ hp P hqMode Tpath hfin hleft hk (.inr (.inr a))
  · have he : F (.inr (.inr a)) = F (.inr (.inr b)) := hte.symm.trans (heq ▸ hne)
    have hb := congrArg Prod.snd he
    change true = false at hb
    cases hb
  · apply htgap n hn hnt
    exact ⟨b, hne.symm⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the unadjusted candidate has a certified
boundary obstruction. The outgoing beta port is fixed by the candidate and
is not its own geometric successor, for every nonnegative index. -/
theorem lPlusGluedSplicedRotation_boundary_obstruction :
    ∃ d : Q, kmswLimitDartVertex w (D d).val ∈ B ∧
      ¬ (S).rotation (D d).val (D (R d)).val := by
  let q := (⟨boundaryFutureHattedPath k W, hqMode⟩ :
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  let b : LPlusHattedDart MH := ⟨(((MH).boundary 1).1, false),
    lMinus_hatted_boundary_mem _ q 1⟩
  let d := lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode) b
  have hbdy : ((MH).boundary 1).1 = kmswLeftBoundaryEdge (hatCodes U hτ) 1 := by
    change kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) 1 = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  refine ⟨d, ?_, ?_⟩
  · refine ⟨boundaryGluingHatEdgeMap W h k hτ ((MH).boundary 1).1,
      Or.inr ⟨1, congrArg (boundaryGluingHatEdgeMap W h k hτ) hbdy.symm⟩, Or.inl rfl⟩
  · have hfix := lPlusGluedSplicedRotation_beta_outgoing_fixed
      hτ hp P hqMode Tpath hfin hleft hk 0
    change R d = d at hfix
    rw [hfix]
    exact lPlus_beta_outgoing_not_self_rotation hτ hp P hqMode Tpath hfin hleft hk 0

































































end DirectedDistances.PaperProofs.Section5
