/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSide




public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- level without taking that level first. -/
private theorem lPlus_exists_coordinate_eq_of_le (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) {n : ℕ} (hn : f n ≤ a) :
    ∃ m ≤ n, f m = a := by
  let m := Nat.find (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hma : f m ≤ a := Nat.find_spec (⟨n, hn⟩ : ∃ j, f j ≤ a)
  have hmn : m ≤ n := Nat.find_min' (⟨n, hn⟩ : ∃ j, f j ≤ a) hn
  by_cases hm0 : m = 0
  · rw [hm0, hzero] at hma
    omega
  · obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have hprev : a < f p := by
      have hnot := Nat.find_min (⟨n, hn⟩ : ∃ j, f j ≤ a) (by omega : p < m)
      omega
    refine ⟨m, hmn, ?_⟩
    rw [hp] at hma ⊢
    have hnext := hstep p
    omega

/-- Helper toward Lemma 5.5: the previous stopped stage consists exactly of
the deleted prefix edges at a positive boundary index. -/
theorem lPlusPrefixMinusEdges_eq_previousStage
    {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ}
    (hk : 0 < k) :
    boundaryGluingPrefixMinusEdges W h k =
      {e | e < (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k - 1)).nextEdge} := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  have hkpos : 1 ≤ k := by omega
  have hfind : t = Nat.find (h.rightHit k hkpos) := by
    dsimp [t]
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : k ≠ 0), dite_eq_left (by omega : 0 < k)]
  have hhit : R w t = -k := boundaryHitTime_right_spec w h hkpos
  have hstep : ∀ n, R w n - 1 ≤ R w (n + 1) := by
    intro n
    have hR : R w (n + 1) = R w n +
        (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
    have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by
      unfold RandomWalk.lazyTwoDimensionalStep
      split_ifs <;> omega
    rw [hR]
    omega
  have hstrict : ∀ j < t, -(k : ℤ) < R w j := by
    intro j hj
    rw [hfind] at hj
    by_contra hnot
    have hjle : R w j ≤ -(k : ℤ) := by omega
    obtain ⟨m, hmj, hmk⟩ := lPlus_exists_coordinate_eq_of_le (R w) hstep
      (by simp [R]) (by omega : -k < 0) hjle
    exact (Nat.find_min (h.rightHit k hkpos) (hmj.trans_lt hj)) hmk
  have htpos : 0 < t := by
    by_contra ht
    have ht0 : t = 0 := by omega
    rw [ht0] at hhit
    have hR0 : R w 0 = 0 := by simp [R]
    omega
  let m := t - 1
  have htm : t = m + 1 := by dsimp [m]; omega
  have hprevlo : -k + 1 ≤ R w m := by
    have hs := hstrict m (by omega)
    omega
  have hRstep : R w t = R w m +
      (RandomWalk.lazyTwoDimensionalStep (w m)).2 := by
    rw [htm]
    exact Finset.sum_range_succ _ _
  have hprev : R w m = -(k : ℤ) + 1 := by
    have hstepLower : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w m)).2 := by
      unfold RandomWalk.lazyTwoDimensionalStep
      split_ifs <;> omega
    rw [hRstep] at hhit
    omega
  have hmin : minR w m = R w m := by
    obtain ⟨i, him, hmi⟩ := runningMin_attained (R w) m
    change minR w m = R w i at hmi
    have hle : minR w m ≤ R w m := runningMin_le (R w) m m le_rfl
    have hlow : R w m ≤ R w i := by
      have hs := hstrict i (by omega)
      rw [hprev]
      omega
    have hupper : R w i ≤ R w m := by rw [← hmi]; exact hle
    rw [hmi]
    exact le_antisymm hupper hlow
  have hUR : (kmswStage w m).UR = [] := by
    apply (kmswStage_UR_eq_nil_iff_record w m).2
    exact hmin.symm
  have hw : w m = 2 := by
    have hdelta : (RandomWalk.lazyTwoDimensionalStep (w m)).2 = -1 := by
      rw [hRstep, hprev] at hhit
      omega
    have hval : (w m).val = 2 := by
      have hb := (w m).isLt
      unfold RandomWalk.lazyTwoDimensionalStep at hdelta
      split_ifs at hdelta; omega
    exact Fin.ext hval
  have hstage : kmswStage w (m + 1) = kmswStepOfStep (kmswStage w m) .down := by
    change kmswStep (kmswStage w m) (w m) = _
    rw [hw]
    simp [kmswStep, kmswCodeStep]
  have hnext : (kmswStage w (m + 1)).nextEdge = (kmswStage w m).nextEdge + 1 := by
    rw [hstage]
    simp [kmswStepOfStep, hUR, State.addEdge]
  have hactive : act w (m + 1) = (kmswStage w m).nextEdge := by
    change (kmswStage w (m + 1)).active = _
    rw [hstage]
    simp [kmswStepOfStep, hUR, State.addEdge]
  ext e
  change (e < (kmswStage w t).nextEdge ∧ e ≠ act w t) ↔
    e < (kmswStage w (t - 1)).nextEdge
  rw [htm, hnext, hactive]
  simp only [Nat.add_sub_cancel]
  omega

/-- Helper toward Lemma 5.5: at index zero the deleted prefix is empty. -/
theorem lPlusPrefixMinusEdges_zero
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)} :
    boundaryGluingPrefixMinusEdges W h 0 = ∅ :=
  boundaryGluingPrefixMinusEdges_zero W h

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (longest : Bool)
  (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)

/-- Helper toward Lemma 5.5: a dart of the deleted positive prefix, viewed
as a dart of the preceding KMSW stage. -/
@[expose] def lPlusPrefixStageDart (hk : 0 < k)
    (d : StageDart (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k - 1)).nextEdge) :
    LPlusPrefixDart W h k :=
  ⟨(d.1.val, d.2), by
    rw [lPlusPrefixMinusEdges_eq_previousStage (W := W) (h := h) (k := k) hk]
    exact d.1.isLt⟩

/-- Helper toward Lemma 5.5: a deleted-prefix dart, read as a dart of the
preceding KMSW stage. -/
@[expose] def lPlusPrefixDartStage (hk : 0 < k)
    (d : LPlusPrefixDart W h k) :
    StageDart (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k - 1)).nextEdge := by
  have hcarrier := lPlusPrefixMinusEdges_eq_previousStage
    (W := W) (h := h) (k := k) hk
  have hmem := (Set.ext_iff.mp hcarrier d.val.1).mp d.property
  change d.val.1 < (kmswStage (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k - 1)).nextEdge at hmem
  exact (⟨d.val.1, hmem⟩, d.val.2)

/-- Helper toward Lemma 5.5: the positive deleted-prefix embedding is a first
return of the run-zero rotation to its geometric darts. Its induced rotation
is the finite KMSW stage rotation on `M_{0,τ_k-1}`. -/
theorem lPlusPrefixDartImage_firstReturn (hk : 0 < k)
    (d : LPlusPrefixDart W h k) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n]
          (lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
            longest hqMode) hτ (.inl d)) =
        lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
          longest hqMode) hτ
          (.inl (lPlusPrefixStageDart (W := W) (h := h) (k := k)
            hk
            (stageRot (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h k - 1)
              (lPlusPrefixDartStage (W := W) (h := h) (k := k) hk d)))) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
          (lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
            longest hqMode) hτ (.inl d)) ∉
            Set.range (fun e : LPlusPrefixDart W h k =>
              lPlusBlockDartImage (M := lPlusHattedSide (W := W) (h := h) (k := k)
                longest hqMode) hτ (.inl e)) := by
  let w := shiftedStream W 0
  let m := boundaryHitTime w h k - 1
  let D : StageDart (kmswStage w m).nextEdge :=
    lPlusPrefixDartStage (W := W) (h := h) (k := k) hk d
  have hD : (D.1.val, D.2) = d.val := by
    apply Prod.ext
    · rfl
    · rfl
  obtain ⟨n, hn, hret, hgap⟩ := kmswInfRot_firstReturn_stage w (H.1 0) m D
  refine ⟨n, hn, ?_, ?_⟩
  · change (kmswInfRot w (H.1 0) : _ → _)^[n] d.val =
      ((stageRot w m D).1.val, (stageRot w m D).2)
    calc
      _ = (kmswInfRot w (H.1 0) : _ → _)^[n] (D.1.val, D.2) :=
        congrArg ((kmswInfRot w (H.1 0) : _ → _)^[n]) hD.symm
      _ = _ := by simpa only [Equiv.Perm.coe_pow] using hret
  · intro j hj hjn hmem
    obtain ⟨e, he⟩ := hmem
    have heBound : e.val.1 < (kmswStage w m).nextEdge := by
      have hcarrier := lPlusPrefixMinusEdges_eq_previousStage
        (W := W) (h := h) (k := k) hk
      have heMem := (Set.ext_iff.mp hcarrier e.val.1).mp e.property
      change e.val.1 < (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k - 1)).nextEdge at heMem
      simpa [w, m] using heMem
    have hgapj := hgap j hj hjn
    have he' : (kmswInfRot w (H.1 0) : _ → _)^[j] (D.1.val, D.2) = e.val := by
      calc
        _ = (kmswInfRot w (H.1 0) : _ → _)^[j] d.val :=
          congrArg ((kmswInfRot w (H.1 0) : _ → _)^[j]) hD
        _ = _ := by simpa only [lPlusBlockDartImage,
          Equiv.Perm.coe_pow] using he.symm
    have hgapj' : (kmswStage w m).nextEdge ≤
        ((kmswInfRot w (H.1 0) : _ → _)^[j] (D.1.val, D.2)).1 := by
      simpa only [Equiv.Perm.coe_pow] using hgapj
    rw [he'] at hgapj'
    exact (Nat.not_lt_of_ge hgapj') heBound
































end DirectedDistances.PaperProofs.Section5
end
