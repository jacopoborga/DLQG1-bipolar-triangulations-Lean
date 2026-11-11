module

public import DirectedDistances.PaperProofs.Section7.CellLDPUpperBoundaryMerge
public import DirectedDistances.KMSW.RunBoundaryVertexLabels
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.KMSW.KMSWShift
import DirectedDistances.KMSW.KMSWWindowPatchRelation

/-! Supporting lemmas for paper labels `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/










public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW

private theorem edgeMerge_R_shift_add (w : ℕ → Fin 3) (n m : ℕ) :
    R w (n + m) = R w n + R (fun i => w (n + i)) m := by
  induction m with
  | zero => simp [R]
  | succ m ih =>
    have hg : R w (n + m + 1) = R w (n + m) +
        (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w (n + m))).2 :=
      Finset.sum_range_succ _ _
    have hf : R (fun i => w (n + i)) (m + 1) =
        R (fun i => w (n + i)) m +
          (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w (n + m))).2 :=
      Finset.sum_range_succ _ _
    rw [Nat.add_succ, hg, hf, ih]
    omega

private theorem edgeMerge_hit_eq_find (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {a : ℤ} (ha : 1 ≤ a) :
    boundaryHitTime w h a = Nat.find (h.rightHit a ha) := by
  unfold boundaryHitTime
  simp only [dite_eq_right (by omega : a ≠ 0), dite_eq_left (by omega : 0 < a)]

private theorem edgeMerge_hit_shift (w : ℕ → Fin 3) (n a b : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hbelow : -(a : ℤ) < minR w n) (hlevel : (b : ℤ) = (a : ℤ) + R w n) :
    boundaryHitTime w h0 (a : ℤ) =
      n + boundaryHitTime (fun i => w (n + i)) hn (b : ℤ) := by
  let u := fun i => w (n + i)
  let t0 := boundaryHitTime w h0 (a : ℤ)
  let tn := boundaryHitTime u hn (b : ℤ)
  have haZ : 1 ≤ (a : ℤ) := by omega
  have hbZ : 1 ≤ (b : ℤ) := by omega
  have h0R : R w t0 = -(a : ℤ) := boundaryHitTime_right_spec w h0 haZ
  have hnR : R u tn = -(b : ℤ) := boundaryHitTime_right_spec u hn hbZ
  have hnt : n ≤ t0 := by
    by_contra hlt
    have hmin := runningMin_le (R w) n t0 (by omega)
    change minR w n ≤ R w t0 at hmin
    omega
  have hcand0 : R w (n + tn) = -(a : ℤ) := by
    have hs := edgeMerge_R_shift_add w n tn
    change R w (n + tn) = R w n + R u tn at hs
    omega
  have h0le : t0 ≤ n + tn := by
    dsimp [t0]
    rw [edgeMerge_hit_eq_find w h0 haZ]
    exact Nat.find_min' (h0.rightHit _ haZ) hcand0
  have hcandn : R u (t0 - n) = -(b : ℤ) := by
    have hs := edgeMerge_R_shift_add w n (t0 - n)
    rw [Nat.add_sub_of_le hnt] at hs
    change R w t0 = R w n + R u (t0 - n) at hs
    omega
  have hnle : tn ≤ t0 - n := by
    dsimp [tn]
    rw [edgeMerge_hit_eq_find u hn hbZ]
    exact Nat.find_min' (hn.rightHit _ hbZ) hcandn
  change t0 = n + tn
  omega





theorem rightBoundary_tail_hitTime_shift (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i))) (j : ℕ) :
    boundaryHitTime w h0 ((j + (kmswStage w n).LR.length : ℕ) : ℤ) =
      n + boundaryHitTime (fun i => w (n + i)) hn
        ((j + ((kmswStage w n).UR.length + 1) : ℕ) : ℤ) := by
  have hLR := kmswStage_LR_length w n
  have hUR := kmswStage_UR_length w n
  have hmin := runningMin_le (R w) n 0 (by omega)
  change minR w n ≤ R w 0 at hmin
  have hzero : R w 0 = 0 := by simp [R]
  apply edgeMerge_hit_shift w n _ _ h0 hn
  · omega
  · omega
  · push_cast
    omega
  · push_cast
    omega

private theorem edgeMerge_window_active (w : ℕ → Fin 3) (n t : ℕ) :
    kmswWindowEdgeMapInf w n (act (fun i => w (n + i)) t) = act w (n + t) := by
  rw [kmswWindowEdgeMapInf_eq_stage w n t _ (act_lt_nextEdge _ le_rfl)]
  exact (kmswWindowPatchData_rel w n t).active




theorem rightBoundary_edge_merge_explicit (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i))) (j : ℕ) :
    kmswRightBoundaryEdge w (j + (kmswStage w n).LR.length) =
      kmswWindowEdgeMapInf w n
        (kmswRightBoundaryEdge (fun i => w (n + i))
          (j + ((kmswStage w n).UR.length + 1))) := by
  have hLR := kmswStage_LR_length w n
  have hmin := runningMin_le (R w) n 0 (by omega)
  change minR w n ≤ R w 0 at hmin
  have hzero : R w 0 = 0 := by simp [R]
  have ha : 1 ≤ j + (kmswStage w n).LR.length := by omega
  have hb : 1 ≤ j + ((kmswStage w n).UR.length + 1) := by omega
  rw [← boundaryHitTime_right_edge_eq_rightBoundaryEdge w h0 ha,
    ← boundaryHitTime_right_edge_eq_rightBoundaryEdge (fun i => w (n + i)) hn hb,
    edgeMerge_window_active, rightBoundary_tail_hitTime_shift w n h0 hn j]




theorem exists_rightBoundary_edge_merge (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i))) :
    ∃ σ0 σn : ℕ, ∀ k : ℕ, 1 ≤ k →
      kmswRightBoundaryEdge w (k - 1 + σ0) =
        kmswWindowEdgeMapInf w n
          (kmswRightBoundaryEdge (fun i => w (n + i)) (k - 1 + σn)) := by
  refine ⟨(kmswStage w n).LR.length, (kmswStage w n).UR.length + 1, ?_⟩
  intro k _hk
  exact rightBoundary_edge_merge_explicit w n h0 hn (k - 1)

end DirectedDistances.PaperProofs.Section7
