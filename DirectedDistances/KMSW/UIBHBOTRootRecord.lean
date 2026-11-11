module
public import DirectedDistances.KMSW.UIBHBOTWholePlaneWord
public import DirectedDistances.RandomWalk.ExcursionWordSupport
import Mathlib.Algebra.BigOperators.Intervals


public section
namespace DirectedDistances.KMSW
open DirectedDistances.RandomWalk
private abbrev firstSum (v : List (Fin 3)) : ℤ := ((v.map lazyTwoDimensionalStep).sum).1
private theorem cast_list (xs : List ℕ) :
    (Nat.cast <$> xs : List ℤ) = xs.map (fun i : ℕ => (i : ℤ)) := rfl
private theorem reversed_neg (v : List (Fin 3)) (hv : IsStoppedExcursionWord v)
    (n : ℕ) (hn : 0 < n) : firstSum (v.reverse.take n) < 0 := by
  have he : firstSum (v.take (v.length - n)) + firstSum (v.reverse.take n) = -1 := by
    rw [List.take_reverse]
    have h := congrArg (fun xs => firstSum xs) (List.take_append_drop (v.length - n) v)
    simpa only [firstSum, List.map_append, List.sum_append, Prod.fst_add,
      List.map_reverse, List.sum_reverse, hv.2.1] using h
  have hp := hv.2.2 (v.length - n) (by have := hv.1; omega)
  change -1 < firstSum (v.take (v.length - n)) at hp; omega
private theorem blocks_bound (f : ℕ → List (Fin 3)) (xs : List ℕ)
    (h : ∀ k ∈ xs, IsStoppedExcursionWord (f k)) (n : ℕ) :
    firstSum ((xs.flatMap fun k => (f k).reverse).take n) ≤ 0 ∧
      (0 < n → xs ≠ [] → firstSum ((xs.flatMap fun k => (f k).reverse).take n) < 0) := by
  induction xs generalizing n with
  | nil => simp [firstSum]
  | cons a xs ih =>
    have hb := (ih (fun k hk => h k (List.mem_cons_of_mem a hk)) (n - (f a).length)).1
    by_cases hn : n = 0
    · simp [hn, firstSum]
    have ha := reversed_neg (f a) (h a List.mem_cons_self) n (by omega)
    have he : firstSum (((a :: xs).flatMap fun k => (f k).reverse).take n) =
        firstSum ((f a).reverse.take n) +
          firstSum ((xs.flatMap fun k => (f k).reverse).take (n - (f a).length)) := by
      simp [firstSum, List.take_append]
    rw [he]; exact ⟨by omega, by intros; omega⟩
private theorem range_fst (f : ℕ → ℤ × ℤ) (n : ℕ) :
    ((List.range n).map f).sum.1 = ∑ i ∈ Finset.range n, (f i).1 := by
  induction n with | zero => simp | succ n ih =>
    simp [List.range_succ, Finset.sum_range_succ, ih]
private theorem window_integral (W : ℤ → Fin 3) (N j : ℕ) (hj : j < N) :
    L (shiftedStream W N) N + (wholePlaneWordIntegral W ((j : ℤ) - N)).1 =
      L (shiftedStream W N) j := by
  have hd : ((j : ℤ) - N) < 0 := by omega
  have hc : (-((j : ℤ) - N)).toNat = N - j := by omega
  simp only [wholePlaneWordIntegral, ite_eq_right (not_le.mpr hd), Prod.fst_neg, hc,
    bind_pure_comp, cast_list, List.map_map, Function.comp_def, range_fst]
  have he := Finset.sum_range_add
    (fun i => (lazyTwoDimensionalStep (shiftedStream W N i)).1) j (N - j)
  have ht : (∑ i ∈ Finset.range (N - j),
      (lazyTwoDimensionalStep (shiftedStream W N (j + i))).1) =
      ∑ i ∈ Finset.range (N - j), (lazyTwoDimensionalStep (W (-(i : ℤ) - 1))).1 := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl; intro i hi; have hi' := Finset.mem_range.mp hi
    congr 2; unfold shiftedStream; congr 1; omega
  rw [show j + (N - j) = N by omega, ht] at he
  change L (shiftedStream W N) N = L (shiftedStream W N) j + _ at he
  omega


theorem uibhbotCode_strictRecord (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) :
    ∀ N, 1 ≤ N → ∀ j < N,
      L (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) N <
        L (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) j := by
  intro N _ j hj
  have hd : 0 < N - j := by omega
  have hp := (blocks_bound (fun k => w (-(k : ℤ) - 1)) (List.range (N - j))
    (fun k _ => hw _) (N - j)).2 hd (by simpa using hd.ne')
  have ht : ((j : ℤ) - N) < 0 := by omega
  have hc : (-((j : ℤ) - N)).toNat = N - j := by omega
  have hz : 0 < (uibhbotConcatWalk w ((j : ℤ) - N)).1 := by
    simpa only [uibhbotConcatWalk, ite_eq_right (not_le.mpr ht), hc, Prod.fst_neg,
      bind_pure_comp, cast_list, List.flatMap_map, Function.comp_def] using neg_pos.mpr hp
  have he := window_integral (uibhbotCodeWord w (fun k => (hw k).1)) N j hj
  rw [wholePlaneWordIntegral_uibhbotCodeWord] at he; omega


theorem uibhbotRootEdge_eq_window_of_stopped (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) (N : ℕ) (hN : 1 ≤ N) :
    uibhbotRootEdge (uibhbotCodeWord w (fun k => (hw k).1)) =
      wholePlaneEdgeι (uibhbotCodeWord w (fun k => (hw k).1)) N
        (kmswLLCreatedEdge (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) N) :=
  uibhbotRootEdge_eq_window _ N hN (uibhbotCode_strictRecord w hw N hN)


theorem uibhbotRootEdge_window_independent_of_stopped (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M) :
    wholePlaneEdgeι (uibhbotCodeWord w (fun k => (hw k).1)) N
      (kmswLLCreatedEdge (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) N) =
    wholePlaneEdgeι (uibhbotCodeWord w (fun k => (hw k).1)) M
      (kmswLLCreatedEdge (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) M) M) :=
  (uibhbotRootEdge_eq_window_of_stopped w hw N hN).symm.trans
    (uibhbotRootEdge_eq_window_of_stopped w hw M hM)
end DirectedDistances.KMSW
