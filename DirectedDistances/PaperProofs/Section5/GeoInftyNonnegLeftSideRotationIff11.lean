/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideRotationIff10

/-! Helper toward Lemma 5.5: the finite prefix at the initial east port. -/

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
local notation "MH" => lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode
local notation "ULedges" => (List.reverse (List.dropLast (State.UL
  (kmswStage w (boundaryHitTime w h k)))))

include hk in
/-- Helper toward Lemma 5.5: a nonempty finite attachment forces a positive
boundary index on the nonnegative domain. -/
theorem lPlus_upperLeft_nonempty_pos (hn : 0 < (ULedges).length) : 0 < k := by
  by_contra hh
  have hk0 : k = 0 := by omega
  simp [hk0, boundaryHitTime_zero, kmswStage, kmswInit] at hn

include H hqMode in
/-- Helper toward Lemma 5.5: the finite prefix's first return from the
initial east port is its actual preceding-stage rotation, with every earlier
iterate excluded from the prefix. -/
theorem lPlus_upperLeft_initial_east_prefix_firstReturn
    (hn : 0 < (ULedges).length) :
    let hkpos := lPlus_upperLeft_nonempty_pos hk hn
    let a : LPlusPrefixDart W h k :=
      ⟨(ULedges[0], true), lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩⟩
    let r := lPlusPrefixStageDart hkpos
      (stageRot w (boundaryHitTime w h k - 1) (lPlusPrefixDartStage hkpos a))
    ∃ q : ℕ, 0 < q ∧
      (kmswInfRot w (H.1 0) : _ → _)^[q] (ULedges[0], true) = r.val ∧
      ∀ j : ℕ, 0 < j → j < q →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (ULedges[0], true) ∉
          Set.range (fun d : LPlusPrefixDart W h k => d.val) := by
  dsimp only
  let a : LPlusPrefixDart W h k :=
    ⟨(ULedges[0], true), lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩⟩
  simpa only [lPlusBlockDartImage] using
    lPlusPrefixDartImage_firstReturn (H := H) hτ longest hqMode
      (lPlus_upperLeft_nonempty_pos hk hn) a

include H in
/-- Helper toward Lemma 5.5: the complete three-block return at the initial
east port is the earlier of the finite-prefix return and the two-future-block
return. The two return times are distinct because the latter endpoint is
hatted and the prefix and hatted edge images are disjoint. -/
theorem lPlus_upperLeft_initial_east_threeBlock_firstReturn
    (hn : 0 < (ULedges).length) :
    let hkpos := lPlus_upperLeft_nonempty_pos hk hn
    let a : LPlusPrefixDart W h k :=
      ⟨(ULedges[0], true), lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩⟩
    let r := lPlusPrefixStageDart hkpos
      (stageRot w (boundaryHitTime w h k - 1) (lPlusPrefixDartStage hkpos a))
    let c : LPlusHattedDart MH :=
      ⟨(((MH).boundary 0).1, false),
        lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
    let J : LPlusHattedDart MH → ℕ × Bool :=
      fun d => (boundaryGluingHatEdgeMap W h k hτ d.val.1, d.val.2)
    let HR := lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
      ⟨boundaryFutureHattedPath k W, hqMode⟩
    let F := lPlusBlockDartImage (M := MH) hτ
    ∃ q n : ℕ, 0 < q ∧ 0 < n ∧ q ≠ n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[q] a.val = r.val ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] a.val = J (HR c) ∧
      (kmswInfRot w (H.1 0) : _ → _)^[min q n] a.val =
        (if q < n then r.val else J (HR c)) ∧
      ∀ j : ℕ, 0 < j → j < min q n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] a.val ∉ Set.range F := by
  dsimp only
  let hkpos := lPlus_upperLeft_nonempty_pos hk hn
  let a : LPlusPrefixDart W h k :=
    ⟨(ULedges[0], true), lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩⟩
  let r := lPlusPrefixStageDart hkpos
    (stageRot w (boundaryHitTime w h k - 1) (lPlusPrefixDartStage hkpos a))
  let c : LPlusHattedDart MH :=
    ⟨(((MH).boundary 0).1, false),
      lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
  let J : LPlusHattedDart MH → ℕ × Bool :=
    fun d => (boundaryGluingHatEdgeMap W h k hτ d.val.1, d.val.2)
  let HR := lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
    ⟨boundaryFutureHattedPath k W, hqMode⟩
  let σ := kmswInfRot w (H.1 0)
  obtain ⟨q, hq, hqr, hqgap⟩ := lPlus_upperLeft_initial_east_prefix_firstReturn
    (H := H) hτ hqMode hfin hk hn
  obtain ⟨n, hnpos, hnr, hngap⟩ := lPlus_upperLeft_initial_east_future_firstReturn
    (H := H) hτ hqMode hfin hk hn
  change (σ : _ → _)^[q] a.val = r.val at hqr
  change (σ : _ → _)^[n] a.val = J (HR c) at hnr
  have hne : q ≠ n := by
    intro he
    have hv : r.val = J (HR c) := hqr.symm.trans (he ▸ hnr)
    have hf := congrArg Prod.fst hv
    have hm : r.val.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
        Set.range (boundaryGluingHatEdgeMap W h k hτ) :=
      ⟨r.property, ⟨(HR c).val.1, hf.symm⟩⟩
    exact (Set.ext_iff.mp
      (boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk) _).mp hm
  refine ⟨q, n, hq, hnpos, hne, hqr, hnr, ?_, ?_⟩
  · change (σ : _ → _)^[min q n] a.val = (if q < n then r.val else J (HR c))
    by_cases hlt : q < n
    · rw [ite_eq_left hlt, min_eq_left hlt.le]
      exact hqr
    · rw [ite_eq_right hlt, min_eq_right (by omega)]
      exact hnr
  · intro j hj hjmin
    rintro ⟨b, hb⟩
    have hjq : j < q := lt_of_lt_of_le hjmin (min_le_left _ _)
    have hjn : j < n := lt_of_lt_of_le hjmin (min_le_right _ _)
    cases b with
    | inl b => exact hqgap j hj hjq ⟨b, hb⟩
    | inr b =>
      cases b with
      | inl b => exact hngap j hj hjn (Or.inl ⟨b, hb⟩)
      | inr b => exact hngap j hj hjn (Or.inr ⟨b, hb⟩)

/-- Helper toward Lemma 5.5: a corner already enclosed by an old triangle
has exactly its finite rotation successor in the ambient map. -/
private theorem lPlus_triangle_rotation_eq_stage (u : ℕ → Fin 3)
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

/-- Helper toward Lemma 5.5: an active east port is either a singleton
finite vertex or already has its permanent ambient successor in an old
triangle. This is derived from the actual stage dart partition. -/
private theorem lPlus_active_east_rotation_dichotomy (u : ℕ → Fin 3)
    (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage u n).nextEdge ∧
      ((kmswStage u n).west e = v ∨ (kmswStage u n).east e = v)}.Finite)
    (n : ℕ) :
    let x : StageDart (kmswStage u n).nextEdge :=
      (⟨(kmswStage u n).active, act_lt_nextEdge u le_rfl⟩, true)
    stageRot u n x = x ∨
      kmswInfRot u hf (x.1.val, x.2) =
        ((stageRot u n x).1.val, (stageRot u n x).2) := by
  dsimp only
  let x : StageDart (kmswStage u n).nextEdge :=
    (⟨(kmswStage u n).active, act_lt_nextEdge u le_rfl⟩, true)
  rcases stage_dart_partition u n x with hout | ⟨j, ⟨hjn, hxj⟩, _⟩
  · left
    have hLR : (kmswStage u n).active ∈ (kmswStage u n).LR := by
      have ho := (stageOuterWord_mem_iff u n x).mp hout
      simp only [x, Bool.true_eq_false, false_and, true_and, false_or] at ho
      rcases ho with he | he
      · exact he
      · have haUL : (kmswStage u n).active ∈ (kmswStage u n).UL := by
          obtain ⟨es, hes⟩ := kmswStage_UL_last u n
          rw [hes]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hp' := (kmswStageFrontierChain_all u n).UL_present _ haUL
        have hm := ((kmswStage_status u n).1 _ (act_lt_nextEdge u le_rfl)).mpr
          (Or.inr he)
        change (kmswStage u n).present (kmswStage u n).active = false at hm
        rw [hp'] at hm
        cases hm
    rw [kmswStage_LR_eq] at hLR
    obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hLR
    have heq : m = n := CutConverse.act_injective u hmn
    have hrec := (List.mem_filter.mp hm).2
    simp only [decide_eq_true_eq] at hrec
    rw [heq] at hrec
    cases n with
    | zero => rfl
    | succ n =>
      have hlen := kmswStage_UR_length u n
      have hle := runningMin_le (R u) n n le_rfl
      change minR u n ≤ R u n at hle
      obtain ⟨i, hi, he⟩ := runningMin_attained (R u) n
      change minR u n = R u i at he
      have hstep : R u (n + 1) = R u n +
          (RandomWalk.lazyTwoDimensionalStep (u n)).2 := Finset.sum_range_succ _ _
      have hdelta := hrec n (by omega)
      have hc : u n = 2 := by
        have hu := (u n).isLt
        unfold RandomWalk.lazyTwoDimensionalStep at hstep
        split_ifs at hstep <;> apply Fin.ext <;> omega
      have hmin := hrec i (by omega)
      rw [hc, RandomWalk.lazyTwoDimensionalStep_two] at hstep
      have hur : (kmswStage u n).UR = [] := by
        apply List.length_eq_zero_iff.mp
        dsimp at hstep hlen
        omega
      have hsize : (kmswStage u (n + 1)).nextEdge =
          (kmswStage u n).nextEdge + 1 := by
        simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hur, State.addEdge]
      have hact : (kmswStage u (n + 1)).active = (kmswStage u n).nextEdge := by
        simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hur, State.addEdge]
      have htab := StageRotation.step_pendant (kmswStage u n)
        (act_lt_nextEdge u le_rfl) (stageRotation_UL_bound u n) (stageRot u n)
        (u n) (by rw [hc]; rfl) hur
      change StageRotation.resize hsize (stageRot u (n + 1)) = _ at htab
      have resize_fixed {a b : ℕ} (heq : a = b)
          (r : Equiv.Perm (StageDart a)) (d : StageDart a)
          (hd : StageRotation.resize heq r
            (⟨d.1.val, by have := d.1.isLt; omega⟩, d.2) =
              (⟨d.1.val, by have := d.1.isLt; omega⟩, d.2)) : r d = d := by
        cases heq
        exact hd
      apply resize_fixed hsize
      rw [htab]
      convert (StageRotation.pendant_new (kmswStage u n).nextEdge (stageRot u n)
        (⟨(kmswStage u n).active, act_lt_nextEdge u le_rfl⟩, true)).2 using 1 <;>
        simp [StageRotation.allocation, hact]
  · right
    exact lPlus_triangle_rotation_eq_stage u hf n x j hjn hxj

include H in
/-- Helper toward Lemma 5.5: at the initial attachment port, the finite
prefix either fixes the port or supplies the immediate ambient successor. -/
theorem lPlus_upperLeft_initial_east_prefix_dichotomy
    (hn : 0 < (ULedges).length) :
    let hkpos := lPlus_upperLeft_nonempty_pos hk hn
    let a : LPlusPrefixDart W h k :=
      ⟨(ULedges[0], true), lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩⟩
    let r := lPlusPrefixStageDart hkpos
      (stageRot w (boundaryHitTime w h k - 1) (lPlusPrefixDartStage hkpos a))
    r = a ∨ kmswInfRot w (H.1 0) a.val = r.val := by
  dsimp only
  let hkpos := lPlus_upperLeft_nonempty_pos hk hn
  let a : LPlusPrefixDart W h k :=
    ⟨(ULedges[0], true), lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩⟩
  let m := boundaryHitTime w h k - 1
  let x : StageDart (kmswStage w m).nextEdge :=
    (⟨(kmswStage w m).active, act_lt_nextEdge w le_rfl⟩, true)
  have ha : lPlusPrefixDartStage hkpos a = x := by
    apply Prod.ext
    · apply Fin.ext
      exact lPlus_upperLeft_initial_eq_previous_active hkpos hn
    · rfl
  rcases lPlus_active_east_rotation_dichotomy w (H.1 0) m with hfix | hnext
  · left
    apply Subtype.ext
    change ((stageRot w m (lPlusPrefixDartStage hkpos a)).1.val,
      (stageRot w m (lPlusPrefixDartStage hkpos a)).2) = a.val
    rw [ha, hfix]
    exact (congrArg (fun d : StageDart (kmswStage w m).nextEdge =>
      (d.1.val, d.2)) ha).symm
  · right
    change kmswInfRot w (H.1 0) a.val =
      ((stageRot w m (lPlusPrefixDartStage hkpos a)).1.val,
        (stageRot w m (lPlusPrefixDartStage hkpos a)).2)
    rw [ha]
    have hav : a.val = (x.1.val, x.2) := congrArg
      (fun d : StageDart (kmswStage w m).nextEdge => (d.1.val, d.2)) ha
    rw [hav]
    exact hnext

include H in
/-- Helper toward Lemma 5.5: the prefix contribution at the initial east
port is explicit. A nontrivial prefix successor is the next ambient dart;
if the prefix fixes the port, the hatted successor of beta is the first
three-block return, and its open arc contains no retained prefix dart. -/
theorem lPlus_upperLeft_initial_east_firstReturn_piecewise
    (hn : 0 < (ULedges).length) :
    let hkpos := lPlus_upperLeft_nonempty_pos hk hn
    let a : LPlusPrefixDart W h k :=
      ⟨(ULedges[0], true), lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩⟩
    let r := lPlusPrefixStageDart hkpos
      (stageRot w (boundaryHitTime w h k - 1) (lPlusPrefixDartStage hkpos a))
    let c : LPlusHattedDart MH :=
      ⟨(((MH).boundary 0).1, false),
        lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
    let J : LPlusHattedDart MH → ℕ × Bool :=
      fun d => (boundaryGluingHatEdgeMap W h k hτ d.val.1, d.val.2)
    let HR := lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
      ⟨boundaryFutureHattedPath k W, hqMode⟩
    let F := lPlusBlockDartImage (M := MH) hτ
    ∃ t : ℕ, 0 < t ∧
      (kmswInfRot w (H.1 0) : _ → _)^[t] a.val =
        (if r = a then J (HR c) else r.val) ∧
      ∀ j : ℕ, 0 < j → j < t →
        (kmswInfRot w (H.1 0) : _ → _)^[j] a.val ∉ Set.range F := by
  dsimp only
  let hkpos := lPlus_upperLeft_nonempty_pos hk hn
  let a : LPlusPrefixDart W h k :=
    ⟨(ULedges[0], true), lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩⟩
  let r := lPlusPrefixStageDart hkpos
    (stageRot w (boundaryHitTime w h k - 1) (lPlusPrefixDartStage hkpos a))
  let c : LPlusHattedDart MH :=
    ⟨(((MH).boundary 0).1, false),
      lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
  let J : LPlusHattedDart MH → ℕ × Bool :=
    fun d => (boundaryGluingHatEdgeMap W h k hτ d.val.1, d.val.2)
  let HR := lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
    ⟨boundaryFutureHattedPath k W, hqMode⟩
  let σ := kmswInfRot w (H.1 0)
  change ∃ t : ℕ, 0 < t ∧ (σ : _ → _)^[t] a.val =
    (if r = a then J (HR c) else r.val) ∧ _
  obtain ⟨q, hq, hqr, hqgap⟩ := lPlus_upperLeft_initial_east_prefix_firstReturn
    (H := H) hτ hqMode hfin hk hn
  obtain ⟨n, hnpos, hnr, hngap⟩ := lPlus_upperLeft_initial_east_future_firstReturn
    (H := H) hτ hqMode hfin hk hn
  change (σ : _ → _)^[q] a.val = r.val at hqr
  change (σ : _ → _)^[n] a.val = J (HR c) at hnr
  have hnotH (b : LPlusPrefixDart W h k) : b.val ∉ Set.range J := by
    rintro ⟨d, hd⟩
    have hm : b.val.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
        Set.range (boundaryGluingHatEdgeMap W h k hτ) :=
      ⟨b.property, ⟨d.val.1, congrArg Prod.fst hd⟩⟩
    exact (Set.ext_iff.mp
      (boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk) _).mp hm
  by_cases hfix : r = a
  · have hxT : a.val ∈ Set.range (lMinusPrimedDartImage hτ) := by
      refine ⟨(0, true), ?_⟩
      have he := lPlusUpperLeftGluedDart_initial_eq_primed_root hτ hqMode hfin hk hn
      exact ((lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp he).symm
    have hnq : n < q := by
      have hle : n ≤ q := by
        by_contra hh
        apply hngap q hq (by omega)
        rw [show (σ : _ → _)^[q] a.val = a.val from hqr.trans (congrArg Subtype.val hfix)]
        exact Or.inl hxT
      have hne : n ≠ q := by
        intro he
        apply hnotH a
        refine ⟨HR c, ?_⟩
        exact hnr.symm.trans ((he ▸ hqr).trans (congrArg Subtype.val hfix))
      omega
    refine ⟨n, hnpos, ?_, ?_⟩
    · rw [ite_eq_left hfix]
      exact hnr
    · intro j hj hjn
      rintro ⟨b, hb⟩
      cases b with
      | inl b => exact hqgap j hj (by omega) ⟨b, hb⟩
      | inr b =>
        cases b with
        | inl b => exact hngap j hj hjn (Or.inl ⟨b, hb⟩)
        | inr b => exact hngap j hj hjn (Or.inr ⟨b, hb⟩)
  · have hs : σ a.val = r.val :=
      (lPlus_upperLeft_initial_east_prefix_dichotomy (H := H) hτ hfin hk hn).resolve_left hfix
    refine ⟨1, Nat.zero_lt_one, ?_, fun j hj hjn => by omega⟩
    rw [ite_eq_right hfix, Function.iterate_one]
    exact hs

variable {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)

local notation "Q" => LPlusGluedDart longest hqMode hτ
local notation "D" => lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
local notation "F" => lPlusBlockDartImage (M := MH) hτ

include hp P Tpath hleft in
/-- Helper toward Lemma 5.5: the candidate before the terminal exchange
has the complete three-block first return at the initial east port. -/
theorem lPlusGluedCorrectedRotation_upperLeft_initial_east_firstReturn
    (hn : 0 < (ULedges).length) :
    let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨0, hn⟩, true)
    let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot w (H.1 0) : _ → _)^[n] (D d).val = (D (C d)).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (D d).val ∉ Set.range F := by
  dsimp only
  let hkpos := lPlus_upperLeft_nonempty_pos hk hn
  let a : LPlusPrefixDart W h k :=
    ⟨(ULedges[0], true), lPlusUpperLeftEdge_mem_prefix hτ hfin hk ⟨0, hn⟩⟩
  let r := lPlusPrefixStageDart hkpos
    (stageRot w (boundaryHitTime w h k - 1) (lPlusPrefixDartStage hkpos a))
  let c : LPlusHattedDart MH :=
    ⟨(((MH).boundary 0).1, false),
      lMinus_hatted_boundary_mem _ ⟨boundaryFutureHattedPath k W, hqMode⟩ 0⟩
  let J : LPlusHattedDart MH → ℕ × Bool :=
    fun d => (boundaryGluingHatEdgeMap W h k hτ d.val.1, d.val.2)
  let HR := lPlusHattedRotation (if longest then XDP.ldp else XDP.sdp)
    ⟨boundaryFutureHattedPath k W, hqMode⟩
  let IP := lPlusPrefixGluedDart (hτ := hτ) (hqMode := hqMode)
  let IT := lPlusPrimedGluedDart (hτ := hτ) (hqMode := hqMode)
  let IH := lPlusHattedGluedDart (hτ := hτ) (hqMode := hqMode)
  let UL := lPlusUpperLeftGluedDart hτ hqMode hfin hk
  let PE := lPlusPrefixExtendedRotation hτ hp P hqMode Tpath hfin hleft hk
  let CU := lPlusUpperLeftCornerRotation hτ hqMode hfin hk
  let TE := lPlusPrimedExtendedRotation hτ hqMode hfin
  let CB := lPlusBetaCornerRotation hτ hqMode
  let HE := lPlusHattedExtendedRotation hτ hqMode
  let PR := lPlusPrefixRotation (W := W) (h := h) (k := k) (H := H)
    (hLL := hLL) (longest := longest) (hτ := hτ) (hp := hp) (P := P)
    (hqMode := hqMode) (Tpath := Tpath) (hfin := hfin) (hleft := hleft) hk
  have hPR : PR a = r :=
    lPlusPrefixRotation_apply hτ hp P hqMode Tpath hfin hleft hk hkpos a
  have hPE : PE (UL (⟨0, hn⟩, true)) = IP r := by
    have he := PR.extendDomain_apply_image
      (Equiv.ofInjective IP (lPlusPrefixGluedDart_injective
        (hτ := hτ) (hqMode := hqMode))) a
    change PE (IP a) = IP (PR a) at he
    exact he.trans (congrArg IP hPR)
  have hnotH : IP r ∉ Set.range IH := by
    rintro ⟨b, hb⟩
    have he := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp hb
    change J b = r.val at he
    have hm : r.val.1 ∈ boundaryGluingPrefixMinusEdges W h k ∩
        Set.range (boundaryGluingHatEdgeMap W h k hτ) :=
      ⟨r.property, ⟨b.val.1, congrArg Prod.fst he⟩⟩
    exact (Set.ext_iff.mp
      (boundaryGluingPrefixMinusEdges_inter_hatRange W h k hτ hk) _).mp hm
  have hC : lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
      (UL (⟨0, hn⟩, true)) = (if r = a then IH (HR c) else IP r) := by
    change HE (CB (TE (CU (PE (UL (⟨0, hn⟩, true)))))) = _
    rw [hPE]
    by_cases hfix : r = a
    · rw [ite_eq_left hfix, hfix]
      have hCU : CU (UL (⟨0, hn⟩, true)) = UL (⟨0, hn⟩, true) := by
        exact (lPlusUpperLeftCornerPerm (ULedges).length).extendDomain_apply_image
          (Equiv.ofInjective UL (lPlusUpperLeftGluedDart_injective hτ hqMode hfin hk))
          (⟨0, hn⟩, true)
      change HE (CB (TE (CU (UL (⟨0, hn⟩, true))))) = _
      rw [hCU, lPlusPrimedExtendedRotation_initial_east hτ hqMode hfin hk hn]
      have hCB : CB (lPlusBetaGluedDart hτ hqMode (0, false)) =
          lPlusBetaGluedDart hτ hqMode (0, false) := by
        exact lMinusBoundaryCornerPerm.extendDomain_apply_image
          (Equiv.ofInjective _ (lPlusBetaGluedDart_injective hτ hqMode)) (0, false)
      rw [hCB]
      exact HR.extendDomain_apply_image _ c
    · rw [ite_eq_right hfix]
      have hs : kmswInfRot w (H.1 0) a.val = r.val :=
        (lPlus_upperLeft_initial_east_prefix_dichotomy (H := H) hτ hfin hk hn).resolve_left hfix
      obtain ⟨n, hnpos, hnr, hngap⟩ := lPlus_upperLeft_initial_east_future_firstReturn
        (H := H) hτ hqMode hfin hk hn
      have hnone : 1 < n := by
        by_contra hh
        have hn1 : n = 1 := by omega
        rw [hn1, Function.iterate_one, hs] at hnr
        apply hnotH
        refine ⟨HR c, ?_⟩
        apply (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mpr
        exact hnr.symm
      have hnotT : IP r ∉ Set.range IT := by
        rintro ⟨p, hp'⟩
        have he := (lPlusGluedDart_eq_iff (hτ := hτ) (hqMode := hqMode) _ _).mp hp'
        change lMinusPrimedDartImage hτ p = r.val at he
        apply hngap 1 Nat.zero_lt_one hnone
        rw [Function.iterate_one, hs]
        exact Or.inl ⟨p, he⟩
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
        exact hnotH ⟨_, hp'⟩
      have hHE : HE (IP r) = IP r :=
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hnotH
      rw [hCU, hTE, hCB, hHE]
  obtain ⟨n, hnpos, hnr, hngap⟩ := lPlus_upperLeft_initial_east_firstReturn_piecewise
    (H := H) hτ hqMode hfin hk hn
  refine ⟨n, hnpos, ?_, hngap⟩
  rw [hC]
  by_cases hfix : r = a
  · rw [ite_eq_left hfix]
    change (kmswInfRot w (H.1 0) : _ → _)^[n] a.val = J (HR c)
    exact (show (kmswInfRot w (H.1 0) : _ → _)^[n] a.val =
      (if r = a then J (HR c) else r.val) from hnr).trans (ite_eq_left hfix)
  · rw [ite_eq_right hfix]
    change (kmswInfRot w (H.1 0) : _ → _)^[n] a.val = r.val
    exact (show (kmswInfRot w (H.1 0) : _ → _)^[n] a.val =
      (if r = a then J (HR c) else r.val) from hnr).trans (ite_eq_right hfix)

end DirectedDistances.PaperProofs.Section5

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the terminal output exchange preserves the
complete three-block first return at the initial east attachment port. -/
theorem lPlusGluedCorrectedRotation2_upperLeft_initial_east_firstReturn
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k)
    (hn : 0 < (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length) :
    let D := lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
    let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨0, hn⟩, true)
    let C := lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
    let F := lPlusBlockDartImage
      (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n] (D d).val =
        (D (C d)).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j] (D d).val ∉
          Set.range F := by
  dsimp only
  let Q := LPlusGluedDart longest hqMode hτ
  let D := lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
  let F := lPlusBlockDartImage
    (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ
  let es := (kmswStage (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k)).UL.dropLast.reverse
  let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (⟨0, hn⟩, true)
  let t := lPlusUpperLeftGluedDart hτ hqMode hfin hk
    (⟨es.length - 1, by dsimp [es]; omega⟩, false)
  let C := lPlusGluedCorrectedRotation hτ hp P hqMode Tpath hfin hleft hk
  have hdt : d ≠ t := by
    intro he
    have hh := lPlusUpperLeftGluedDart_injective hτ hqMode hfin hk he
    exact Bool.noConfusion (congrArg Prod.snd hh)
  have hmem (q : Q) : (D q).val ∈ Set.range F := by
    rw [← lPlusGluedCodeImageEquiv_val hτ hp P hqMode Tpath hfin hleft hk]
    exact (lPlusGluedCodeImageEquiv hτ hqMode q).property
  have hold := lPlusGluedCorrectedRotation_upperLeft_initial_east_firstReturn
    (hτ := hτ) (hqMode := hqMode) (hfin := hfin) (hk := hk)
    (hp := hp) (P := P) (Tpath := Tpath) (hleft := hleft) hn
  have hCR : C d = lPlusGluedCodeReturn (H := H) hτ hqMode d := by
    apply D.injective
    apply Subtype.ext
    obtain ⟨n, hnpos, hnr, hngap⟩ := hold
    obtain ⟨m, hmpos, hmr, hmgap⟩ :=
      lPlusGluedCodeReturn_spec hτ hp P hqMode Tpath hfin hleft hk d
    have hnm : n = m := by
      apply Nat.le_antisymm
      · by_contra hh
        apply hngap m hmpos (by omega)
        rw [hmr]
        exact hmem _
      · by_contra hh
        apply hmgap n hnpos (by omega)
        rw [hnr]
        exact hmem _
    exact hnr.symm.trans (hnm ▸ hmr)
  have heq : lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d = C d := by
    apply lPlusGluedCorrectedRotation2_eq_of_ne
      hτ hp P hqMode Tpath hfin hleft hk hn d hdt
    intro he
    exact hdt (lPlusGluedCodeReturn_injective (H := H) hτ hqMode (hCR.symm.trans he))
  change ∃ n : ℕ, 0 < n ∧
    (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n] (D d).val =
      (D (lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk d)).val ∧ _
  rw [heq]
  exact hold

/-- Helper toward Lemma 5.5: every dart of the finite upper-left attachment
has the complete first-return characterization for candidate 2, including
the initial east port and the repaired terminal west port. -/
theorem lPlusGluedCorrectedRotation2_upperLeft_firstReturn
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {H : WholePlaneRotationHypothesis W}
    {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
    {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k)
    (i : Fin (List.reverse (List.dropLast (State.UL
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k))))).length)
    (b : Bool) :
    let D := lPlusGluedDartEquivNonneg hτ hp P hqMode Tpath hfin hleft hk
    let d := lPlusUpperLeftGluedDart hτ hqMode hfin hk (i, b)
    let C := lPlusGluedCorrectedRotation2 hτ hp P hqMode Tpath hfin hleft hk
    let F := lPlusBlockDartImage
      (M := lPlusHattedSide (W := W) (h := h) (k := k) longest hqMode) hτ
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n] (D d).val =
        (D (C d)).val ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j] (D d).val ∉
          Set.range F := by
  let es := (kmswStage (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k)).UL.dropLast.reverse
  have hi_lt : i.val < es.length := i.isLt
  have hn : 0 < es.length := by omega
  have hkpos := lPlus_upperLeft_nonempty_pos hk hn
  cases b with
  | false =>
    by_cases hi : i.val + 1 < es.length
    · exact lPlusGluedCorrectedRotation2_upperLeft_interior_west_firstReturn
        hτ hp P hqMode Tpath hfin hleft hk hkpos i hi
    · have hiend : i = (⟨es.length - 1, by omega⟩ : Fin es.length) := by
        apply Fin.ext
        change i.val = es.length - 1
        omega
      rw [hiend]
      exact lPlusGluedCorrectedRotation2_terminal_firstReturn
        hτ hp P hqMode Tpath hfin hleft hk hn
  | true =>
    by_cases hi : i.val = 0
    · have hi0 : i = (⟨0, hn⟩ : Fin es.length) := Fin.ext hi
      rw [hi0]
      exact lPlusGluedCorrectedRotation2_upperLeft_initial_east_firstReturn
        hτ hp P hqMode Tpath hfin hleft hk hn
    · let j : Fin es.length := ⟨i.val - 1, by omega⟩
      have hj : j.val + 1 < es.length := by dsimp [j]; omega
      have hji : (⟨j.val + 1, hj⟩ : Fin es.length) = i := by
        apply Fin.ext
        dsimp [j]
        omega
      have hr := lPlusGluedCorrectedRotation2_upperLeft_interior_east_firstReturn
        hτ hp P hqMode Tpath hfin hleft hk hkpos j hj
      rw [hji] at hr
      exact hr






























































end DirectedDistances.PaperProofs.Section5
