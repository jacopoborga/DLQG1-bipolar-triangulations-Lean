/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIBOTBoundaryAssembly

/-! # Persistence of hit-indexed lower-left boundary edges

The missing lower-left edge at a negative coordinate hit stays in the LL
boundary at every later finite stage. -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open scoped Classical

private theorem stage_LL_mem_mono_local (w : ℕ → Fin 3) {n m f : ℕ}
    (hnm : n ≤ m) (hf : f ∈ (kmswStage w n).LL) :
    f ∈ (kmswStage w m).LL := by
  induction m, hnm using Nat.le_induction with
  | base => exact hf
  | succ m hm ih =>
    change f ∈ (kmswStep (kmswStage w m) (w m)).LL
    unfold kmswStep
    cases hc : kmswCodeStep (w m) with
    | down =>
      cases hs : (kmswStage w m).UR <;>
        simpa [kmswStepOfStep, hs, State.addEdge] using ih
    | up => simpa only [kmswStepOfStep, State.addEdge] using ih
    | left =>
      cases hs : (kmswStage w m).UL.dropLast.reverse with
      | cons a as => simpa only [kmswStepOfStep, hs, State.addEdge] using ih
      | nil =>
        simpa only [kmswStepOfStep, hs, State.addEdge, List.mem_cons] using
          (Or.inr ih)

private theorem boundaryHitTime_left_record_local (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ j, j < boundaryHitTime w h k → k < L w j := by
  let τ := boundaryHitTime w h k
  have hfind : τ = Nat.find (h.leftHit k hk) := by
    dsimp only [τ, boundaryHitTime]
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_right (by omega : ¬ 0 < k)]
  have hstepAbs : ∀ i,
      |(RandomWalk.lazyTwoDimensionalStep (w i)).1| ≤ 1 := by
    intro i
    change |((w i).val : ℤ) - 1| ≤ 1
    have hb := (w i).isLt
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hstep : ∀ i, L w i - 1 ≤ L w (i + 1) := by
    intro i
    have hsum : L w (i + 1) = L w i +
        (RandomWalk.lazyTwoDimensionalStep (w i)).1 := Finset.sum_range_succ _ _
    rw [hsum]
    have hlow := (abs_le.mp (hstepAbs i)).1
    omega
  have hzero : L w 0 = 0 := by simp [L]
  have hrecord : ∀ j, j < τ → k < L w j := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [hzero]
      omega
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hnot : ¬ L w (j + 1) = k := by
        have hjfind : j + 1 < Nat.find (h.leftHit k hk) := by
          simpa only [hfind, τ] using hj
        exact Nat.find_min (h.leftHit k hk) hjfind
      have hlow := hstep j
      omega
  intro j hj
  exact hrecord j (by simpa only [τ] using hj)

/-- Persistence of the left-boundary missing LL edge: for each `k ≤ -1`, the
edge created at its first hit remains in the LL list with `present = false`
and the same west/east endpoints at every later stage. This is the
left-boundary (missing LL edges) clause of `lem-uibot-bdy`
with hit-indexed `x_k`. The identification with the leftmost path of
`m_{-∞,∞}` is not proved here. -/
theorem boundary_left_edge_persistent (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    let e := kmswLLCreatedEdge w (boundaryHitTime w h k)
    e < (kmswStage w (boundaryHitTime w h k)).nextEdge ∧
      ∀ n, boundaryHitTime w h k ≤ n →
        e ∈ (kmswStage w n).LL ∧
        (kmswStage w n).present e = false ∧
        (kmswStage w n).west e = boundaryVertex w h k ∧
        (kmswStage w n).east e = boundaryVertex w h (k + 1) := by
  let τ := boundaryHitTime w h k
  let e := kmswLLCreatedEdge w τ
  change e < (kmswStage w τ).nextEdge ∧ ∀ n, τ ≤ n →
    e ∈ (kmswStage w n).LL ∧
    (kmswStage w n).present e = false ∧
    (kmswStage w n).west e = boundaryVertex w h k ∧
    (kmswStage w n).east e = boundaryVertex w h (k + 1)
  have hτpos : 0 < τ := by
    have hhit := boundaryHitTime_left_spec w h hk
    change L w τ = k at hhit
    have hzero : L w 0 = 0 := by simp [L]
    by_contra hnot
    have hτzero : τ = 0 := by omega
    rw [hτzero, hzero] at hhit
    omega
  have hbound : e < (kmswStage w τ).nextEdge := by
    have hmono := kmswStage_nextEdge_mono w (m := 0) (n := τ) (Nat.zero_le _)
    have hinitial : (kmswStage w 0).nextEdge = 1 := by
      simp [kmswStage, kmswInit]
    rw [hinitial] at hmono
    dsimp [e, kmswLLCreatedEdge]
    omega
  have hmiss := boundaryVertex_left_missing_edge w h hk
  change (kmswStage w τ).west e = boundaryVertex w h k ∧
    (kmswStage w τ).east e = boundaryVertex w h (k + 1) ∧
    (kmswStage w τ).present e = false at hmiss
  have hstrict : ∀ j < τ, L w τ < L w j := by
    intro j hj
    have hleft := boundaryHitTime_left_record_local w h hk j hj
    change L w (boundaryHitTime w h k) < L w j
    rw [boundaryHitTime_left_spec w h hk]
    exact hleft
  have hmem : e ∈ (kmswStage w τ).LL := by
    rw [kmswStage_LL_eq]
    apply List.mem_map.mpr
    refine ⟨τ, List.mem_reverse.mpr ?_, rfl⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (by omega),
      decide_eq_true ⟨hτpos, hstrict⟩⟩
  refine ⟨hbound, ?_⟩
  intro n hτn
  have hmemN := stage_LL_mem_mono_local w hτn hmem
  have hboundN : e < (kmswStage w n).nextEdge :=
    hbound.trans_le (kmswStage_nextEdge_mono w hτn)
  have hmissing := ((kmswStage_status w n).1 e hboundN).mpr (Or.inr hmemN)
  have hends := kmswStage_endpoints_stable w hτn hbound
  exact ⟨hmemN, hmissing,
    hends.1.trans hmiss.1,
    hends.2.trans hmiss.2.1⟩

/-- A hit-indexed negative boundary edge is never a directed edge, since its
missing status persists after its creation (`lem-uibot-bdy`, -/
theorem boundary_left_edge_not_present (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    let e := kmswLLCreatedEdge w (boundaryHitTime w h k)
    ¬ EdgePresent w e := by
  let τ := boundaryHitTime w h k
  let e := kmswLLCreatedEdge w τ
  change ¬ EdgePresent w e
  intro he
  obtain ⟨N, hpersist⟩ := he.eventually_present
  let n := max τ N
  have hfalse := (boundary_left_edge_persistent w h hk).2 n
    (le_max_left _ _)
  have htrue := (hpersist n (le_max_right _ _)).2
  rw [hfalse.2.1] at htrue
  contradiction

/-- Almost surely, one common hit witness gives persistence of every
negative-index lower-left missing edge for the iid one-sided map.
The path identification in `lem-uibot-bdy` remains outside this combinatorial -/
theorem iidCodes_ae_boundary_left_edge_persistent :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ h : BoundaryHitWitnesses w,
        ∀ k : ℤ, k ≤ -1 →
          let e := kmswLLCreatedEdge w (boundaryHitTime w h k)
          e < (kmswStage w (boundaryHitTime w h k)).nextEdge ∧
            ∀ n, boundaryHitTime w h k ≤ n →
              e ∈ (kmswStage w n).LL ∧
              (kmswStage w n).present e = false ∧
              (kmswStage w n).west e = boundaryVertex w h k ∧
              (kmswStage w n).east e = boundaryVertex w h (k + 1) := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω h
  exact ⟨h, fun k hk => boundary_left_edge_persistent
    (fun i => ω (i + 1)) h hk⟩

end DirectedDistances.KMSW
