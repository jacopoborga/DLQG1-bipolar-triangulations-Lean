module

public import DirectedDistances.RandomWalk.UIBHBOTEncodingWalk
public import DirectedDistances.KMSW.KMSWWholePlaneColimit
public import DirectedDistances.KMSW.BoundaryRecordsMissing

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk

private theorem concat_length_ge (f : ℕ → List (Fin 3))
    (hf : ∀ k, 1 ≤ (f k).length) (n : ℕ) :
    n ≤ ((List.range n).flatMap f).length := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
      have := hf n
      omega

/-- Helper toward prop-disk-bs-conv / Proposition 5.16 and Definition 5.8
letter `n` in a sequence of nonempty blocks. The first `n + 1` blocks already
contain this letter, so no default letter is used. Not the paper result. -/
@[expose] def uibhbotBlockLetter (f : ℕ → List (Fin 3))
    (hf : ∀ k, 1 ≤ (f k).length) (n : ℕ) : Fin 3 :=
  ((List.range (n + 1)).flatMap f)[n]'(by
    have := concat_length_ge f hf (n + 1)
    omega)

private theorem blockLetter_prefix (f : ℕ → List (Fin 3))
    (hf : ∀ k, 1 ≤ (f k).length) (n : ℕ) :
    (List.range n).map (uibhbotBlockLetter f hf) = ((List.range n).flatMap f).take n := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take]
    exact (Nat.min_eq_left (concat_length_ge f hf n)).symm
  · intro i hi hj
    have hin : i < n := by simpa only [List.length_map, List.length_range] using hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, uibhbotBlockLetter]
    have hn : n = (i + 1) + (n - (i + 1)) := by omega
    have hp : (List.range (i + 1)).flatMap f <+: (List.range n).flatMap f := by
      conv_rhs => rw [hn, List.range_add, List.flatMap_append]
      exact List.prefix_append _ _
    exact hp.getElem (by have := concat_length_ge f hf (i + 1); omega)

/-- Helper toward prop-disk-bs-conv / Proposition 5.16 and Definition 5.8
letters of the concatenated nonempty excursion blocks. `W t` codes the transition
from time `t` to time `t + 1`. On the negative half-line the preceding words are
read nearest first, with their letters reversed. The letters themselves are not negated;
backward integration negates the increments. Not the paper result. -/
@[expose] def uibhbotCodeWord (w : ℤ → List (Fin 3))
    (hwords : ∀ k : ℤ, 1 ≤ (w k).length) (t : ℤ) : Fin 3 :=
  if 0 ≤ t then
    uibhbotBlockLetter (fun k => w (k : ℤ)) (fun k => hwords (k : ℤ)) t.toNat
  else
    uibhbotBlockLetter (fun k => (w (-(k : ℤ) - 1)).reverse)
      (fun k => by simpa only [List.length_reverse] using hwords (-(k : ℤ) - 1))
      (-t - 1).toNat

/-- Helper toward prop-disk-bs-conv / Proposition 5.16 and Definition 5.8
integration from zero, summing `W 0, ..., W (t-1)` for nonnegative `t`, and
negating the sum of `W (-1), ..., W t` for negative `t`. Not the paper result. -/
@[expose] def wholePlaneWordIntegral (W : ℤ → Fin 3) (t : ℤ) : ℤ × ℤ :=
  if 0 ≤ t then
    ((List.range t.toNat).map (fun i => lazyTwoDimensionalStep (W (i : ℤ)))).sum
  else
    -((List.range (-t).toNat).map
      (fun i => lazyTwoDimensionalStep (W (-(i : ℤ) - 1)))).sum






theorem wholePlaneWordIntegral_uibhbotCodeWord
    (w : ℤ → List (Fin 3)) (hwords : ∀ k : ℤ, 1 ≤ (w k).length) (t : ℤ) :
    wholePlaneWordIntegral (uibhbotCodeWord w hwords) t = uibhbotConcatWalk w t := by
  have hforward (i : ℕ) : uibhbotCodeWord w hwords (i : ℤ) =
      uibhbotBlockLetter (fun k => w (k : ℤ)) (fun k => hwords (k : ℤ)) i := by
    simp [uibhbotCodeWord]
  have hbackward (i : ℕ) : uibhbotCodeWord w hwords (-(i : ℤ) - 1) =
      uibhbotBlockLetter (fun k => (w (-(k : ℤ) - 1)).reverse)
        (fun k => by simpa only [List.length_reverse] using hwords (-(k : ℤ) - 1))
        i := by
    have hneg : ¬ 0 ≤ -(i : ℤ) - 1 := by omega
    have hnat : (-(-(i : ℤ) - 1) - 1).toNat = i := by omega
    simp only [uibhbotCodeWord, ite_eq_right hneg, hnat]
  have hcast (xs : List ℕ) :
      (Nat.cast <$> xs : List ℤ) = xs.map (fun i : ℕ => (i : ℤ)) := rfl
  by_cases ht : 0 ≤ t
  · simp only [wholePlaneWordIntegral, uibhbotConcatWalk, ite_eq_left ht,
      bind_pure_comp, hcast, List.map_map, List.flatMap_map, Function.comp_def]
    have hm := congrArg (fun f : ℕ → Fin 3 =>
      ((List.range t.toNat).map (fun i => lazyTwoDimensionalStep (f i))).sum)
      (funext hforward)
    have hp := congrArg (fun xs : List (Fin 3) =>
      (xs.map lazyTwoDimensionalStep).sum) (blockLetter_prefix
        (fun k => w (k : ℤ)) (fun k => hwords (k : ℤ)) t.toNat)
    exact hm.trans (by simpa only [List.map_map, Function.comp_def] using hp)
  · simp only [wholePlaneWordIntegral, uibhbotConcatWalk, ite_eq_right ht,
      bind_pure_comp, hcast, List.map_map, List.flatMap_map, Function.comp_def]
    have hm := congrArg (fun f : ℕ → Fin 3 =>
      ((List.range (-t).toNat).map (fun i => lazyTwoDimensionalStep (f i))).sum)
      (funext hbackward)
    have hp := congrArg (fun xs : List (Fin 3) =>
      (xs.map lazyTwoDimensionalStep).sum) (blockLetter_prefix
        (fun k => (w (-(k : ℤ) - 1)).reverse)
        (fun k => by simpa only [List.length_reverse] using hwords (-(k : ℤ) - 1))
        (-t).toNat)
    exact congrArg Neg.neg
      (hm.trans (by simpa only [List.map_map, Function.comp_def] using hp))

/-- Helper toward prop-disk-bs-conv / Proposition 5.16 and Definition 5.8
every finite vertex set lies in one one-sided window of the colimit; not the paper result. -/
theorem finiteSet_in_one_wholePlaneVertexWindow
    (W : ℤ → Fin 3) (S : Finset (WholePlaneVertex W)) :
    ∃ N, ∀ v ∈ S, ∃ j : ℕ, wholePlaneVertexι W N j = v := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert v S _ ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨⟨M, j⟩, hj⟩ := Quotient.mk_surjective v
      refine ⟨max M N, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · refine ⟨wholePlaneVertexTrans W M (max M N) (Nat.le_max_left M N) j, ?_⟩
        exact (congrFun (wholePlaneVertexι_trans W M (max M N)
          (Nat.le_max_left M N)) j).trans hj
      · obtain ⟨k, hk⟩ := hN z hz
        refine ⟨wholePlaneVertexTrans W N (max M N) (Nat.le_max_right M N) k, ?_⟩
        exact (congrFun (wholePlaneVertexι_trans W N (max M N)
          (Nat.le_max_right M N)) k).trans hk

/-- Helper toward prop-disk-bs-conv / Proposition 5.16 and Definition 5.8
the geometric root-edge candidate, represented in the window starting at time `-1`.
Its interpretation as a missing edge requires a strict left record at absolute time zero.
No orientation is chosen; not the paper result. -/
@[expose] def uibhbotRootEdge (W : ℤ → Fin 3) : WholePlaneEdge W :=
  wholePlaneEdgeι W 1 (kmswLLCreatedEdge (shiftedStream W 1) 1)

private theorem left_record_creation (w : ℕ → Fin 3) (n : ℕ)
    (hrec : ∀ j ≤ n, L w (n + 1) < L w j) :
    w n = 0 ∧ (kmswStage w n).UL.length = 1 := by
  have hlast := hrec n le_rfl
  have hstep : L w (n + 1) =
      L w n + (lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
  have hc : w n = 0 := by
    change L w (n + 1) = L w n + ((w n : ℤ) - 1) at hstep
    apply Fin.ext
    have hv := (w n).isLt
    omega
  have hmin : minL w n = L w n := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) n
    change minL w n = L w j at he
    have hjrec := hrec j hj
    have hle := runningMin_le (L w) n n le_rfl
    change minL w n ≤ L w n at hle
    rw [hc, lazyTwoDimensionalStep_zero] at hstep
    omega
  refine ⟨hc, ?_⟩
  have hlen := kmswStage_UL_length w n
  rw [hmin] at hlen
  omega

private theorem dropLast_reverse_eq_nil_of_length_one (xs : List ℕ)
    (h : xs.length = 1) : xs.dropLast.reverse = [] := by
  have hd : xs.dropLast = [] := List.length_eq_zero_iff.mp (by
    rw [List.length_dropLast, h])
  rw [hd]
  rfl

private theorem windowMap_LL_created (w : ℕ → Fin 3) (s n : ℕ)
    (hrec : ∀ j < s + (n + 1), L w (s + (n + 1)) < L w j) :
    kmswWindowEdgeMapInf w s (kmswLLCreatedEdge (fun i => w (s + i)) (n + 1)) =
      kmswLLCreatedEdge w (s + (n + 1)) := by
  let v := fun i => w (s + i)
  let pre := kmswStage v n
  let globalPre := kmswStage w (s + n)
  let data := kmswWindowPatchData w s n
  have hcreation := left_record_creation w (s + n) (by
    intro j hj
    simpa only [Nat.add_assoc] using hrec j (by omega))
  have hcode : w (s + n) = 0 := hcreation.1
  have hglobalLen : globalPre.UL.length = 1 := hcreation.2
  have hrel := kmswWindowPatchData_rel w s n
  change KMSWWindowPatchRel (kmswStage w s) globalPre pre data.φ
    data.A data.B data.YL data.YR data.XL data.XR at hrel
  have hprePos : 0 < pre.UL.length :=
    List.length_pos_of_ne_nil (kmswStage_UL_nonempty_active_last v n).1
  have hlength := congrArg List.length hrel.ul
  simp only [List.length_append, List.length_map] at hlength
  have hALen : data.A.length = 0 := by omega
  have hA : data.A = [] := List.length_eq_zero_iff.mp hALen
  have hpreLen : pre.UL.length = 1 := by omega
  have hdrop := dropLast_reverse_eq_nil_of_length_one pre.UL hpreLen
  have hglobalDrop := dropLast_reverse_eq_nil_of_length_one globalPre.UL hglobalLen
  have hlocalCode : v n = 0 := hcode
  have hlocalNext : (kmswStage v (n + 1)).nextEdge = pre.nextEdge + 2 := by
    change (kmswStep pre (v n)).nextEdge = pre.nextEdge + 2
    rw [hlocalCode]
    simp [kmswStep, kmswStepOfStep, kmswCodeStep, hdrop, State.addEdge]
  have hglobalNext : (kmswStage w (s + (n + 1))).nextEdge =
      globalPre.nextEdge + 2 := by
    rw [← Nat.add_assoc]
    change (kmswStep globalPre (w (s + n))).nextEdge = globalPre.nextEdge + 2
    rw [hcode]
    simp [kmswStep, kmswStepOfStep, kmswCodeStep, hglobalDrop, State.addEdge]
  have hlocalId : kmswLLCreatedEdge v (n + 1) = pre.nextEdge + 1 := by
    simp only [kmswLLCreatedEdge, hlocalNext]
    omega
  have hglobalId : kmswLLCreatedEdge w (s + (n + 1)) = globalPre.nextEdge + 1 := by
    simp only [kmswLLCreatedEdge, hglobalNext]
    omega
  have he : kmswLLCreatedEdge v (n + 1) < (kmswStage v (n + 1)).nextEdge := by
    rw [hlocalId, hlocalNext]
    omega
  rw [kmswWindowEdgeMapInf_eq_stage w s (n + 1) _ he, hlocalId, hglobalId]
  change (KMSWWindowPatchData.step globalPre pre
    (kmswCodeStep (w (s + n))) data).φ (pre.nextEdge + 1) = globalPre.nextEdge + 1
  rw [hcode]
  simp [kmswCodeStep, KMSWWindowPatchData.step, hdrop, hA]







theorem uibhbotRootEdge_eq_window (W : ℤ → Fin 3) (N : ℕ) (hN : 1 ≤ N)
    (hrec : ∀ j < N, L (shiftedStream W N) N < L (shiftedStream W N) j) :
    uibhbotRootEdge W =
      wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) N) := by
  have hshift := shiftedStream_shift W 1 N hN
  have hm : N - 1 + (0 + 1) = N := by omega
  have hmap := windowMap_LL_created (shiftedStream W N) (N - 1) 0 (by
    simpa only [hm] using hrec)
  rw [hshift, hm] at hmap
  have htrans : wholePlaneEdgeTrans W 1 N hN
      (kmswLLCreatedEdge (shiftedStream W 1) 1) =
      kmswLLCreatedEdge (shiftedStream W N) N := hmap
  have hι := congrFun (wholePlaneEdgeι_trans W 1 N hN)
    (kmswLLCreatedEdge (shiftedStream W 1) 1)
  change wholePlaneEdgeι W N
    (wholePlaneEdgeTrans W 1 N hN (kmswLLCreatedEdge (shiftedStream W 1) 1)) =
      uibhbotRootEdge W at hι
  rw [htrans] at hι
  exact hι.symm






theorem uibhbotRootEdge_window_independent (W : ℤ → Fin 3) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hrecN : ∀ j < N, L (shiftedStream W N) N < L (shiftedStream W N) j)
    (hrecM : ∀ j < M, L (shiftedStream W M) M < L (shiftedStream W M) j) :
    wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) N) =
      wholePlaneEdgeι W M (kmswLLCreatedEdge (shiftedStream W M) M) :=
  (uibhbotRootEdge_eq_window W N hN hrecN).symm.trans
    (uibhbotRootEdge_eq_window W M hM hrecM)

end DirectedDistances.KMSW
