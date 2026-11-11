/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRootStar2

/-! Helper toward Lemma 5.5: the old-incoming branch at the stopped root. -/

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the terminal endpoints of a finite boundary
chain are distinct, including the endpoints of missing geometric edges. -/
private theorem lPlus_chain_east_injective (u : ℕ → Fin 3) (n : ℕ)
    (es : List ℕ) (hc : WestEastChain (kmswStage u n) es)
    (hb : ∀ e ∈ es, e < (kmswStage u n).nextEdge) :
    Set.InjOn (kmswStage u n).east {e | e ∈ es} := by
  let s := kmswStage u n
  let r := kmswStageRank u n
  have hp : (es.map (fun e => r (s.east e))).Pairwise (· < ·) := by
    induction es with
    | nil => exact .nil
    | cons a tail ih =>
      cases tail with
      | nil => simp only [List.map_cons, List.map_nil, List.pairwise_singleton]
      | cons b bs =>
        have ht := ih hc.tail (fun e he => hb e (List.mem_cons_of_mem a he))
        have hab : s.east a = s.west b := hc.rel_head? (by simp)
        have hr := kmswStageRank_strict u n b (hb b (by simp))
        rw [← hab] at hr
        simpa only [List.map_cons, List.pairwise_cons_cons_iff_of_trans] using
          (show r (s.east a) < r (s.east b) ∧
            ((b :: bs).map (fun e => r (s.east e))).Pairwise (· < ·) from ⟨hr, ht⟩)
  have hn : (es.map s.east).Nodup := by
    have hp' : ((es.map s.east).map r).Pairwise (· < ·) := by
      simpa only [List.map_map, Function.comp_def] using hp
    exact (List.pairwise_map.mp hp').imp
      (fun h he => (ne_of_lt h) (congrArg r he))
  exact fun _ ha _ hb he => List.inj_on_of_nodup_map hn ha hb he

/-- Helper toward Lemma 5.5: the active east endpoint immediately before
a positive boundary hit is the boundary root. -/
theorem lPlus_previous_active_east_eq_boundary_root
    (u : ℕ → Fin 3) (h : BoundaryHitWitnesses u) {k : ℤ} (hk : 0 < k) :
    (kmswStage u (boundaryHitTime u h k - 1)).east
      (kmswStage u (boundaryHitTime u h k - 1)).active = boundaryVertex u h k := by
  obtain ⟨m, hm, hc, hur⟩ := lPlus_positive_hit_fresh u h hk
  have hv : boundaryVertex u h k = activeInitial u (boundaryHitTime u h k) := by
    exact boundaryVertex_right_hit_eq u h (by omega)
  rw [hm] at hv ⊢
  simp only [Nat.add_sub_cancel]
  rw [CutConverse.activeInitial_eq] at hv
  simpa [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hur,
    State.addEdge, act] using hv.symm

/-- Helper toward Lemma 5.5: a corner enclosed by an old triangle has its
permanent successor already in the finite stage. -/
private theorem lPlus_old_triangle_successor (u : ℕ → Fin 3)
    (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage u n).nextEdge ∧
      ((kmswStage u n).west e = v ∨ (kmswStage u n).east e = v)}.Finite)
    (n : ℕ) (x : StageDart (kmswStage u n).nextEdge)
    (j : TriangleCreationTime u) (hj : j.val < n)
    (hx : (x.1.val, x.2) ∈ stageTriangleDartList u j) :
    kmswInfRot u hf (x.1.val, x.2) =
      ((stageRot u n x).1.val, (stageRot u n x).2) := by
  let a := stageTriangleDart₁ u n j hj
  let b := stageTriangleDart₂ u n j hj
  let c := stageTriangleDart₃ u n j hj
  have hs := stageTriangle_isFace u j n hj
  have hi := kmswInfFaceSucc_stageTriangle_cycle u hf j
  have corner (d e : StageDart (kmswStage u n).nextEdge)
      (hs : (kmswMap u n).faceSucc d = e)
      (hi : kmswInfFaceSucc u hf (d.1.val, d.2) = (e.1.val, e.2)) :
      kmswInfRot u hf (e.1.val, e.2) =
        ((stageRot u n e).1.val, (stageRot u n e).2) := by
    change (stageRot u n).symm (edgeFlip _ d) = e at hs
    have hs' := congrArg (stageRot u n) hs
    rw [Equiv.apply_symm_apply] at hs'
    change (kmswInfRot u hf).symm (d.1.val, !d.2) = (e.1.val, e.2) at hi
    have hi' := congrArg (kmswInfRot u hf) hi
    rw [Equiv.apply_symm_apply] at hi'
    rw [← hs']
    exact hi'.symm
  have hinj : Function.Injective
      (fun d : StageDart (kmswStage u n).nextEdge => (d.1.val, d.2)) := by
    intro d e he
    exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) he))
      (congrArg (fun z : ℕ × Bool => z.2) he)
  have hx' : x = a ∨ x = b ∨ x = c := by
    simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx
    · exact Or.inl (hinj hx)
    · exact Or.inr (Or.inl (hinj hx))
    · exact Or.inr (Or.inr (hinj hx))
  rcases hx' with rfl | rfl | rfl
  · exact corner c a hs.2.2.1 hi.2.2.1
  · exact corner a b hs.1 hi.1
  · exact corner b c hs.2.1 hi.2.1

/-- Helper toward Lemma 5.5: at the stopped root, every finite-prefix
successor is either the active east port or the immediate ambient successor.
This follows from the stage face partition and ordered boundary chains. -/
theorem lPlus_previous_root_rotation_dichotomy
    (u : ℕ → Fin 3) (h : BoundaryHitWitnesses u) {k : ℤ} (hk : 0 < k)
    (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage u n).nextEdge ∧
      ((kmswStage u n).west e = v ∨ (kmswStage u n).east e = v)}.Finite)
    (x : StageDart (kmswStage u (boundaryHitTime u h k - 1)).nextEdge)
    (hx : stageEndpoint (kmswStage u (boundaryHitTime u h k - 1)) x =
      boundaryVertex u h k) :
    stageRot u (boundaryHitTime u h k - 1) x =
        (⟨(kmswStage u (boundaryHitTime u h k - 1)).active,
          act_lt_nextEdge u le_rfl⟩, true) ∨
      kmswInfRot u hf (x.1.val, x.2) =
        ((stageRot u (boundaryHitTime u h k - 1) x).1.val,
          (stageRot u (boundaryHitTime u h k - 1) x).2) := by
  let n := boundaryHitTime u h k - 1
  let s := kmswStage u n
  have hn : n < boundaryHitTime u h k := by
    obtain ⟨m, hm, _, _⟩ := lPlus_positive_hit_fresh u h hk
    dsimp [n]
    omega
  have hur : s.UR = [] := by
    obtain ⟨m, hm, _, hur⟩ := lPlus_positive_hit_fresh u h hk
    simpa only [s, n, hm, Nat.add_sub_cancel] using hur
  have root_bool (d : StageDart s.nextEdge)
      (hd : stageEndpoint s d = boundaryVertex u h k) : d.2 = true := by
    cases hb : d.2 with
    | true => rfl
    | false =>
      have hv : edgeWest u d.1.val = boundaryVertex u h k :=
        (edge_endpoints_eq u d.1.isLt).1.symm.trans
          (by simpa only [stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte] using hd)
      exact False.elim (lPlus_before_hit_west_ne_boundary_root u h hk n hn
        d.1.val d.1.isLt hv)
  rcases stage_dart_partition u n x with ho | ⟨j, ⟨hj, hxj⟩, _⟩
  · left
    let r := stageRot u n x
    have hr : stageEndpoint s r = boundaryVertex u h k :=
      ((stageRot_sameCycle_iff_endpoint_eq u n x r).mp ⟨1, rfl⟩).symm.trans hx
    have hrb : r.2 = true := root_bool r hr
    let p := (stageOuterWord u n).formPerm.symm x
    have hp : p ∈ stageOuterWord u n := by
      apply List.mem_of_formPerm_apply_mem
      simpa only [p, Equiv.apply_symm_apply] using ho
    have hface : (kmswMap u n).faceSucc p = x := by
      rw [stageOuterWord_faceSucc u n p hp]
      exact (stageOuterWord u n).formPerm.apply_symm_apply x
    have hrot : r = edgeFlip _ p := by
      change (stageRot u n).symm (edgeFlip _ p) = x at hface
      exact ((stageRot u n).symm_apply_eq.mp hface).symm
    have hpb : p.2 = false := by
      have hb := congrArg Prod.snd hrot
      change r.2 = !p.2 at hb
      rw [hrb] at hb
      cases hp' : p.2 with
      | false => rfl
      | true => rw [hp'] at hb; cases hb
    have hpUL : p.1.val ∈ s.UL := by
      have hp' := (stageOuterWord_mem_iff u n p).mp hp
      change (p.2 = false ∧ (p.1.val ∈ s.UL ∨ p.1.val ∈ s.UR)) ∨
        (p.2 = true ∧ (p.1.val ∈ s.LR ∨ p.1.val ∈ s.LL)) at hp'
      simpa only [hpb, Bool.false_eq_true, true_and, false_and, or_false,
        hur, List.not_mem_nil, or_false] using hp'
    have hrUL : r.1.val ∈ s.UL := by
      have he := congrArg (fun d : StageDart s.nextEdge => d.1.val) hrot
      change r.1.val = p.1.val at he
      exact he ▸ hpUL
    have haUL : s.active ∈ s.UL := by
      obtain ⟨es, hes⟩ := kmswStage_UL_last u n
      rw [hes]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have he : s.east r.1.val = s.east s.active := by
      have hr' : s.east r.1.val = boundaryVertex u h k := by
        simpa only [stageEndpoint, hrb, ↓reduceIte] using hr
      exact hr'.trans (lPlus_previous_active_east_eq_boundary_root u h hk).symm
    have hid := lPlus_chain_east_injective u n s.UL
      (kmswStage_boundary_chain_invariant u n).1.left_of_append
      (stageRotation_UL_bound u n) hrUL haUL he
    exact Prod.ext (Fin.ext hid) hrb
  · right
    exact lPlus_old_triangle_successor u hf n x j hj hxj

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
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
local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "es" => (List.reverse (List.dropLast (State.UL
  (kmswStage w (boundaryHitTime w h k)))))
local notation "IP" => lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "IT" => lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "IH" => lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
local notation "F" => lPlusBlockDartImage (M := MH) hτ

include hk in
/-- Helper toward Lemma 5.5: the nonnegative prefix carrier is inhabited
only at positive boundary indices. -/
theorem lPlus_prefix_dart_pos (a : LPlusPrefixDart W h k) : 0 < k := by
  by_contra hn
  have hk0 : k = 0 := by omega
  subst k
  exact ((Set.ext_iff.mp (lPlusPrefixMinusEdges_zero (W := W) (h := h))
    a.val.1).mp a.property).elim

/-- Helper toward Lemma 5.5: a positive stopped attachment contains the
previous active edge. -/
theorem lPlus_upperLeft_length_pos_of_pos (hkpos : 0 < k) : 0 < (es).length := by
  rw [lPlus_attachment_upperLeft_eq_previous hkpos, List.length_reverse]
  exact List.length_pos_iff.mpr (kmswStage_UL_nonempty_active_last w _).1

include hτ hqMode hfin hk in
/-- Helper toward Lemma 5.5: a root-incident prefix representative shared
with the primed block is exactly the initial east attachment port. -/
theorem lPlus_prefix_root_primed_unique
    (a : LPlusPrefixDart W h k)
    (ha : kmswLimitDartVertex w a.val = boundaryVertex w h k)
    (p : LPlusPrimedDart) (hap : IP a = IT p) :
    a.val = (es[0]'(lPlus_upperLeft_length_pos_of_pos (lPlus_prefix_dart_pos hk a)),
      true) := by
  have hkpos := lPlus_prefix_dart_pos hk a
  let n := boundaryHitTime w h k - 1
  let s := kmswStage w n
  have hab := (lPlusPrefixDart_initial_vertex_old_incoming hk a ha).1
  have he := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp hap
  change a.val = lMinusPrimedDartImage hτ p at he
  have hm : a.val.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
      boundaryGluingPrimedEdges W h k hτ :=
    ⟨a.property, ⟨p.1, congrArg Prod.fst he.symm⟩⟩
  rw [boundaryGluingPrefixMinusEdges_inter_primedEdges W h k hτ hfin hk] at hm
  change a.val.1 ∈ (kmswStage w (boundaryHitTime w h k)).UL.dropLast at hm
  have hm' : a.val.1 ∈ s.UL := by
    have hmrev := List.mem_reverse.mpr hm
    rw [lPlus_attachment_upperLeft_eq_previous hkpos] at hmrev
    exact List.mem_reverse.mp hmrev
  have hactive : s.active ∈ s.UL := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
    rw [hxs]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hb := (stageRotation_UL_bound w n) _ hm'
  have haEast : s.east a.val.1 = boundaryVertex w h k := by
    have hv : edgeEast w a.val.1 = boundaryVertex w h k := by
      simpa only [kmswLimitDartVertex, hab, ↓reduceIte] using ha
    exact (edge_endpoints_eq w hb).2.trans hv
  have hid := lPlus_chain_east_injective w n s.UL
    (kmswStage_boundary_chain_invariant w n).1.left_of_append
    (stageRotation_UL_bound w n) hm' hactive
    (haEast.trans (lPlus_previous_active_east_eq_boundary_root w h hkpos).symm)
  exact Prod.ext
    (hid.trans (lPlus_upperLeft_initial_eq_previous_active hkpos
      (lPlus_upperLeft_length_pos_of_pos hkpos)).symm) hab

/-- Helper toward Lemma 5.5: stage and limit endpoints agree on the
positive stopped-prefix carrier. -/
theorem lPlusPrefixDartStage_endpoint (hkpos : 0 < k)
    (a : LPlusPrefixDart W h k) :
    stageEndpoint (kmswStage w (boundaryHitTime w h k - 1))
      (lPlusPrefixDartStage hkpos a) = kmswLimitDartVertex w a.val := by
  have hb := (lPlusPrefixDartStage hkpos a).1.isLt
  have he := edge_endpoints_eq w hb
  change (if a.val.2 then (kmswStage w (boundaryHitTime w h k - 1)).east a.val.1
    else (kmswStage w (boundaryHitTime w h k - 1)).west a.val.1) =
      (if a.val.2 then edgeEast w a.val.1 else edgeWest w a.val.1)
  cases hs : a.val.2
  · exact he.1
  · exact he.2

include hp P Tpath hleft in
/-- Helper toward Lemma 5.5: the unexchanged corrected permutation has
the complete three-block first return at every old incoming root dart. -/
theorem lPlusGluedCorrectedRotation_old_incoming_root_firstReturn
    (a : LPlusPrefixDart W h k)
    (ha : LPlusOldIncomingRootDart w h k a.val) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (D (IP a)).val =
        (D (lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
          (IP a))).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (D (IP a)).val ∉ Set.range F := by
  let hkpos := lPlus_prefix_dart_pos hk a
  let hn := lPlus_upperLeft_length_pos_of_pos (W := W) (h := h) hkpos
  let a₀ : LPlusPrefixDart W h k :=
    ⟨(es[0], true), lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩⟩
  let m := boundaryHitTime w h k - 1
  let ρ := stageRot w m
  let σ := kmswInfRot w (H.1 0)
  let x := lPlusPrefixDartStage hkpos a
  let x₀ := lPlusPrefixDartStage hkpos a₀
  let r := lPlusPrefixStageDart hkpos (ρ x)
  let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  let PR := lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H)
    (hLL := hLL) (longest := longest) (hτ := hτ) (hp := hp) (P := P)
    (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  let PE := lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
  let CU := lPlusUpperLeftCornerRotation hτ hqMode hfin hk
  let TE := lPlusPrimedExtendedRotation hτ hqMode hfin
  let CB := lPlusBetaCornerRotation hτ hqMode
  let HE := lPlusHattedExtendedRotation hτ hqMode
  let c : LPlusHattedDart MH :=
    ⟨(((MH).boundary 0).1, false),
      lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
  let J : LPlusHattedDart MH → ℕ × Bool :=
    fun d => (boundaryGluingHatEdgeMap W h k hτ d.val.1, d.val.2)
  let HR : Equiv.Perm (LPlusHattedDart MH) :=
    lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
    ⟨boundaryFutureHattedPath k W, hqMode⟩
  have hav : kmswLimitDartVertex w a.val = boundaryVertex w h k :=
    lPlusOldIncomingRootDart_vertex ha
  have hx : stageEndpoint (kmswStage w m) x = boundaryVertex w h k :=
    (lPlusPrefixDartStage_endpoint hkpos a).trans hav
  have hx₀ : x₀ = (⟨(kmswStage w m).active, act_lt_nextEdge w le_rfl⟩, true) := by
    apply Prod.ext
    · apply Fin.ext
      exact lPlus_upperLeft_initial_eq_previous_active hkpos hn
    · rfl
  have hv₀ : stageEndpoint (kmswStage w m) x₀ = boundaryVertex w h k := by
    rw [hx₀]
    exact lPlus_previous_active_east_eq_boundary_root w h hkpos
  have hrroot : kmswLimitDartVertex w r.val = boundaryVertex w h k := by
    rw [← lPlusPrefixDartStage_endpoint hkpos r]
    exact ((stageRot_sameCycle_iff_endpoint_eq w m x (ρ x)).mp ⟨1, rfl⟩).symm.trans hx
  have hnotH (b : LPlusPrefixDart W h k) : IP b ∉ Set.range IH := by
    rintro ⟨d, hd⟩
    have he := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp hd
    change J d = b.val at he
    have hm : b.val.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
        Set.range (boundaryGluingHatEdgeMap W h k hτ) :=
      ⟨b.property, ⟨d.val.1, congrArg Prod.fst he⟩⟩
    exact (Set.ext_iff.mp
      (boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk) _).mp hm
  have hnotHJ (b : LPlusPrefixDart W h k) : b.val ∉ Set.range J := by
    rintro ⟨d, hd⟩
    apply hnotH b
    refine ⟨d, ?_⟩
    exact (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mpr hd
  have hPR : PR a = r :=
    lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk hkpos a
  have hPE : PE (IP a) = IP r := by
    have he := PR.extendDomain_apply_image
      (Equiv.ofInjective IP (lPlusPrefixGluedDart_injective
        (hτ := hτ) (hqMode := hqMode))) a
    change PE (IP a) = IP (PR a) at he
    exact he.trans (congrArg IP hPR)
  have hC : C (IP a) = (if r = a₀ then IH (HR c) else IP r) := by
    change HE (CB (TE (CU (PE (IP a))))) = _
    rw [hPE]
    by_cases hra : r = a₀
    · rw [ite_eq_left hra, hra]
      have hCU : CU (IP a₀) = IP a₀ := by
        exact (lPlusUpperLeftCornerPerm (es).length).extendDomain_apply_image
          (Equiv.ofInjective _ (lPlusUpperLeftGluedDart_injective hτ hqMode hfin hk))
          (⟨0, hn⟩, true)
      rw [hCU]
      change HE (CB (TE (lPlusUpperLeftGluedDart hτ hqMode hfin hk
        (⟨0, hn⟩, true)))) = _
      rw [lPlusPrimedExtendedRotation_initial_east hτ hqMode hfin hk hn]
      have hCB : CB (lPlusBetaGluedDart hτ hqMode (0, false)) =
          lPlusBetaGluedDart hτ hqMode (0, false) := by
        exact lMinusBoundaryCornerPerm.extendDomain_apply_image
          (Equiv.ofInjective _ (lPlusBetaGluedDart_injective hτ hqMode)) (0, false)
      rw [hCB]
      exact HR.extendDomain_apply_image _ c
    · rw [ite_eq_right hra]
      have hnotT : IP r ∉ Set.range IT := by
        rintro ⟨p, hp'⟩
        apply hra
        apply Subtype.ext
        exact lPlus_prefix_root_primed_unique hτ hqMode hfin hk r hrroot p hp'.symm
      have hCU : CU (IP r) = IP r := by
        apply Equiv.Perm.extendDomain_apply_not_subtype
        rintro ⟨⟨i, b⟩, he⟩
        obtain ⟨p, _, hp'⟩ := lPlusUpperLeftGluedDart_primed_representative
          hτ hqMode hfin hk i b
        exact hnotT ⟨p, hp'.symm.trans he⟩
      have hTE : TE (IP r) = IP r :=
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotT
      have hCB : CB (IP r) = IP r := by
        apply Equiv.Perm.extendDomain_apply_not_subtype
        rintro ⟨p, hp'⟩
        exact hnotH r ⟨_, hp'⟩
      have hHE : HE (IP r) = IP r :=
        Equiv.Perm.extendDomain_apply_not_subtype _ _ (hnotH r)
      rw [hCU, hTE, hCB, hHE]
  change ∃ n : ℕ, 0 < n ∧ (σ : _ → _)^[n] a.val = (D (C (IP a))).val ∧ _
  rw [hC]
  by_cases hra : r = a₀
  · rw [ite_eq_left hra]
    have hreach : ∃ j : ℕ, (ρ : _ → _)^[j] x₀ = x := by
      obtain ⟨j, hj⟩ := ((stageRot_sameCycle_iff_endpoint_eq w m x₀ x).mpr
        (hv₀.trans hx.symm)).exists_nat_pow_eq
      exact ⟨j, by simpa only [Equiv.Perm.coe_pow] using hj⟩
    let l := Nat.find hreach
    have hl : (ρ : _ → _)^[l] x₀ = x := Nat.find_spec hreach
    have hlnoloop (i : ℕ) (hi : 0 < i) (hil : i ≤ l) :
        (ρ : _ → _)^[i] x₀ ≠ x₀ := by
      intro he
      have hsmall : (ρ : _ → _)^[l - i] x₀ = x := by
        have hadd : l = l - i + i := by omega
        rw [hadd, Function.iterate_add_apply, he] at hl
        exact hl
      exact Nat.find_min hreach (by dsimp [l] at hil ⊢; omega) hsmall
    have hstage (j : ℕ) : stageEndpoint (kmswStage w m) ((ρ : _ → _)^[j] x₀) =
        boundaryVertex w h k := by
      have hsame : ρ.SameCycle x₀ ((ρ : _ → _)^[j] x₀) :=
        ⟨(j : ℕ), by simp only [zpow_natCast, Equiv.Perm.coe_pow]⟩
      exact ((stageRot_sameCycle_iff_endpoint_eq w m _ _).mp hsame).symm.trans hv₀
    have horbit (j : ℕ) (hj : j ≤ l) :
        (σ : _ → _)^[j] a₀.val =
          (((ρ : _ → _)^[j] x₀).1.val, ((ρ : _ → _)^[j] x₀).2) := by
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply', ih (by omega)]
        have hdich := lPlus_previous_root_rotation_dichotomy w h hkpos (H.1 0)
          ((ρ : _ → _)^[j] x₀) (hstage j)
        rcases hdich with he | he
        · have he' : (ρ : _ → _)^[j + 1] x₀ = x₀ := by
            rw [Function.iterate_succ_apply']
            exact he.trans hx₀.symm
          exact False.elim (hlnoloop (j + 1) (by omega) hj he')
        · simpa only [Function.iterate_succ_apply'] using he
    have hla : (σ : _ → _)^[l] a₀.val = a.val := by
      rw [horbit l le_rfl, hl]
      rfl
    obtain ⟨n, hnpos, hnr, hngap⟩ := lPlus_upperLeft_initial_east_future_firstReturn
      (H := H) hτ hqMode hfin hk hn
    change (σ : _ → _)^[n] a₀.val = J (HR c) at hnr
    change ∀ j : ℕ, 0 < j → j < n →
      (σ : _ → _)^[j] a₀.val ∉
        Set.range (lMinusPrimedDartImage hτ) ∪ Set.range J at hngap
    have hln : l < n := by
      by_contra hh
      have hpref : (σ : _ → _)^[n] a₀.val ∈
          Set.range (fun b : LPlusPrefixDart W h k => b.val) := by
        rw [horbit n (by omega)]
        exact ⟨lPlusPrefixStageDart hkpos ((ρ : _ → _)^[n] x₀), rfl⟩
      obtain ⟨b, hb⟩ := hpref
      exact hnotHJ b ⟨HR c, hnr.symm.trans hb.symm⟩
    have hshift (j : ℕ) : (σ : _ → _)^[j] a.val =
        (σ : _ → _)^[j + l] a₀.val := by
      rw [Function.iterate_add_apply, hla]
    obtain ⟨q, hqpos, hqr, hqgap⟩ :=
      lPlusPrefixDartImage_firstReturn (H := H) hτ longest hqMode hkpos a
    change (σ : _ → _)^[q] a.val = r.val at hqr
    rw [hra] at hqr
    have hb : σ (J c) = a₀.val := by
      have hbound : ((MH).boundary 0).1 = kmswLeftBoundaryEdge (hatCodes U hτ) 0 := by
        change kmswLeftBoundaryEdge (boltzmannKMSWStream
          (pathCode (boundaryFutureHattedPath k W))) 0 = _
        rw [boundaryGluing_decoded_stream W h k hτ]
      change kmswInfRot w (H.1 0)
        (boundaryGluingHatEdgeMap W h k hτ ((MH).boundary 0).1, false) = _
      rw [hbound]
      exact lPlus_upperLeft_initial_beta_successor (H := H) hτ hqMode hfin hk hn
    have hqbeta : (σ : _ → _)^[q - 1] a.val = J c := by
      apply σ.injective
      change σ ((σ : _ → _)^[q - 1] a.val) = σ (J c)
      rw [← Function.iterate_succ_apply' (f := (σ : _ → _)) (q - 1) a.val,
        show (q - 1).succ = q by omega, hqr, hb]
    have hqone : 1 < q := by
      by_contra hh
      have hq : q = 1 := by omega
      rw [hq] at hqbeta
      exact hnotHJ a ⟨c, hqbeta.symm⟩
    have hnq : n - l < q := by
      by_contra hh
      apply hngap (q - 1 + l) (by omega) (by omega)
      rw [← hshift, hqbeta]
      exact Or.inr ⟨c, rfl⟩
    refine ⟨n - l, by omega, ?_, ?_⟩
    · change (σ : _ → _)^[n - l] a.val = J (HR c)
      rw [hshift, Nat.sub_add_cancel (by omega)]
      exact hnr
    · intro j hj hjn
      rintro ⟨b, hb'⟩
      cases b with
      | inl b =>
        exact hqgap j hj (by omega) ⟨b, hb'⟩
      | inr b =>
        change F (.inr b) = (σ : _ → _)^[j] a.val at hb'
        apply hngap (j + l) (by omega) (by omega)
        rw [← hshift, ← hb']
        cases b with
        | inl b => exact Or.inl ⟨b, rfl⟩
        | inr b => exact Or.inr ⟨b, rfl⟩
  · rw [ite_eq_right hra]
    have hs : σ a.val = r.val := by
      rcases lPlus_previous_root_rotation_dichotomy w h hkpos (H.1 0) x hx with he | he
      · apply False.elim
        apply hra
        apply Subtype.ext
        have he' := congrArg
          (fun d : StageDart (kmswStage w m).nextEdge => (d.1.val, d.2))
          (he.trans hx₀.symm)
        exact he'
      · exact he
    refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
    · exact hs
    · intro j hj hjn
      omega

include hp P Tpath hleft in
/-- Helper toward Lemma 5.5: the terminal output exchange preserves the
complete three-block return at every old incoming root dart. -/
theorem lPlusGluedCorrectedRotation2_old_incoming_root_firstReturn
    (a : LPlusPrefixDart W h k)
    (ha : LPlusOldIncomingRootDart w h k a.val) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (D (IP a)).val =
        (D (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
          (IP a))).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (D (IP a)).val ∉ Set.range F := by
  let hn := lPlus_upperLeft_length_pos_of_pos (W := W) (h := h)
    (lPlus_prefix_dart_pos hk a)
  let d := IP a
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
    (⟨(es).length - 1, by omega⟩, false)
  let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  have hdt : d ≠ t := by
    intro he
    have hv := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp he
    have hb := congrArg Prod.snd hv
    change a.val.2 = false at hb
    rw [ha.1] at hb
    cases hb
  have hmem (q : Q) : (D q).val ∈ Set.range F := by
    rw [← lPlusGluedCodeImageEquiv_val hτ hp P hqMode Tpath hfin hleft hk]
    exact (lPlusGluedCodeImageEquiv hτ hqMode q).property
  have hold := lPlusGluedCorrectedRotation_old_incoming_root_firstReturn
    hτ hp P hqMode Tpath hfin hleft hk a ha
  have hCR : C d = lPlusGluedCodeReturn (H := H) hτ hqMode d := by
    apply (D).injective
    apply Subtype.ext
    obtain ⟨n, hnpos, hend, hgap⟩ := hold
    obtain ⟨m, hmpos, hmend, hmgap⟩ :=
      lPlusGluedCodeReturn_spec hτ hp P hqMode Tpath hfin hleft hk d
    have hnm : n = m := by
      apply Nat.le_antisymm
      · by_contra hh
        apply hgap m hmpos (by omega)
        rw [hmend]
        exact hmem _
      · by_contra hh
        apply hmgap n hnpos (by omega)
        rw [hend]
        exact hmem _
    exact hend.symm.trans (hnm ▸ hmend)
  have heq : lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d =
      C d := by
    apply lPlusGluedCorrectedRotation2_eq_of_ne
      hτ hp P hqMode Tpath hfin hleft hk hn d hdt
    intro he
    exact hdt (lPlusGluedCodeReturn_injective (H := H) hτ hqMode
      (hCR.symm.trans he))
  change ∃ n : ℕ, 0 < n ∧
    (kmswInfRot w (H.1 0) : _ → _)^[n] (D d).val =
      (D (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d)).val ∧ _
  rw [heq]
  exact hold

include hp P Tpath hleft in
/-- Helper toward Lemma 5.5: on the old-incoming class at the initial
vertex, candidate 2 agrees exactly with the ambient left-side rotation. -/
theorem lPlusGluedCorrectedRotation2_old_incoming_root_rotation_iff
    (a : LPlusPrefixDart W h k)
    (ha : LPlusOldIncomingRootDart w h k a.val) :
    ∀ e : Q,
      lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk (IP a) = e ↔
        (m0GeodesicSide hp P .left).rotation (D (IP a)).val (D e).val := by
  let d := IP a
  let C := lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
  have hmem (q : Q) : (D q).val ∈ Set.range F := by
    rw [← lPlusGluedCodeImageEquiv_val hτ hp P hqMode Tpath hfin hleft hk]
    exact (lPlusGluedCodeImageEquiv hτ hqMode q).property
  have hret := lPlusGluedCorrectedRotation2_old_incoming_root_firstReturn
    hτ hp P hqMode Tpath hfin hleft hk a ha
  change ∀ e : Q, C d = e ↔
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[n] (D d).val =
        (D e).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        ((kmswInfRot w (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[j] (D d).val).1 ∉
          (m0GeodesicSide hp P .left).edges
  intro e
  constructor
  · intro he
    obtain ⟨n, hnpos, hend, hgap⟩ := hret
    refine ⟨n, hnpos, ?_, ?_⟩
    · have heD := congrArg (fun q : Q => (D q).val) he
      exact hend.trans heD
    · intro j hj hjn hs
      apply hgap j hj hjn
      rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk]
      exact hs
  · intro hside
    have hsideF : ∃ n : ℕ, 0 < n ∧
        (kmswInfRot w (H.1 0) : _ → _)^[n] (D d).val = (D e).val ∧
        ∀ j : ℕ, 0 < j → j < n →
          (kmswInfRot w (H.1 0) : _ → _)^[j] (D d).val ∉ Set.range F := by
      obtain ⟨n, hnpos, hend, hgap⟩ := hside
      refine ⟨n, hnpos, hend, ?_⟩
      intro j hj hjn hm
      rw [lPlusBlockDartImage_range_nonneg hτ hp P hqMode Tpath hfin hleft hk] at hm
      exact hgap j hj hjn hm
    apply (D).injective
    apply Subtype.ext
    obtain ⟨m, hmpos, hmend, hmgap⟩ := hret
    obtain ⟨n, hnpos, hend, hgap⟩ := hsideF
    have hmn : m = n := by
      apply Nat.le_antisymm
      · by_contra hh
        apply hmgap n hnpos (by omega)
        rw [hend]
        exact hmem e
      · by_contra hh
        apply hgap m hmpos (by omega)
        rw [hmend]
        exact hmem _
    exact hmend.symm.trans (hmn ▸ hend)


















end DirectedDistances.PaperProofs.Section5
