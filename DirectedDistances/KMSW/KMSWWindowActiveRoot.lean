module

public import DirectedDistances.KMSW.KMSWWindowPatchVertex
public import DirectedDistances.KMSW.CutEquivalence
public import DirectedDistances.RandomWalk.IIDVectorWalk
import DirectedDistances.KMSW.MeasurableCutEvents

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk



theorem kmswWindowPatchVertexMap_activeInitial (u w : ℕ → Fin 3) (s m : ℕ)
    (hcode : ∀ i < m, w (s + i) = u i) :
    kmswWindowPatchVertexMap w s m (activeInitial u m) = activeInitial w (s + m) := by
  let v : ℕ → Fin 3 := fun i => w (s + i)
  have hstage : kmswStage v m = kmswStage u m := by
    apply kmswStage_congr
    intro i hi
    exact hcode i hi
  have huRoot : activeInitial u m =
      (kmswStage u m).west (kmswStage u m).active := by
    unfold activeInitial act
    exact (edge_endpoints_eq u (act_lt_nextEdge u (Nat.le_refl m))).1.symm
  have hglobalRoot : (kmswStage w (s + m)).west (kmswStage w (s + m)).active =
      activeInitial w (s + m) := by
    unfold activeInitial act
    exact (edge_endpoints_eq w
      (act_lt_nextEdge w (Nat.le_refl (s + m)))).1
  have hpatch := kmswWindowPatchVertexMap_rel w s m
  have hpatchActive := (kmswWindowPatchData_rel w s m).active
  have hbound : (kmswStage v m).active < (kmswStage v m).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge v m).1
  calc
    kmswWindowPatchVertexMap w s m (activeInitial u m) =
        kmswWindowPatchVertexMap w s m
          ((kmswStage v m).west (kmswStage v m).active) := by
            rw [huRoot, ← hstage]
    _ = (kmswStage w (s + m)).west
          ((kmswWindowPatchData w s m).φ (kmswStage v m).active) :=
            hpatch.west_endpoint _ hbound
    _ = (kmswStage w (s + m)).west (kmswStage w (s + m)).active := by
          rw [hpatchActive]
    _ = activeInitial w (s + m) := hglobalRoot



theorem L_shift_eq_codeWalk_fst (ω : ℕ → Fin 3) (j : ℕ) :
    L (fun i => ω (i + 1)) j = (codeWalk ω j).1 := by
  simp only [codeWalk, L, Prod.fst_sum]

private theorem L_shift_add_activeRoot (w : ℕ → Fin 3) (t n : ℕ) :
    L w (t + n) = L w t + L (fun i => w (t + i)) n := by
  induction n with
  | zero => simp [L]
  | succ n ih =>
      have hg : L w (t + n + 1) = L w (t + n) +
          (lazyTwoDimensionalStep (w (t + n))).1 := Finset.sum_range_succ _ _
      have hs : L (fun i => w (t + i)) (n + 1) =
          L (fun i => w (t + i)) n + (lazyTwoDimensionalStep (w (t + n))).1 :=
        Finset.sum_range_succ _ _
      rw [Nat.add_succ, hg, hs, ih]
      omega

private theorem L_window_code_eq_activeRoot (u w : ℕ → Fin 3) (s m i : ℕ)
    (hi : i ≤ m) (hcode : ∀ j < m, w (s + j) = u j) :
    L (fun j => w (s + j)) i = L u i := by
  unfold L
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (fun c => (lazyTwoDimensionalStep c).1)
  exact hcode j ((Finset.mem_range.mp hj).trans_le hi)



theorem L_window_additivity (u w : ℕ → Fin 3) (s m i : ℕ) (hi : i ≤ m)
    (hcode : ∀ j < m, w (s + j) = u j) :
    L w (s + i) - L w s = L u i := by
  rw [L_shift_add_activeRoot, L_window_code_eq_activeRoot u w s m i hi hcode]
  omega

end DirectedDistances.KMSW
