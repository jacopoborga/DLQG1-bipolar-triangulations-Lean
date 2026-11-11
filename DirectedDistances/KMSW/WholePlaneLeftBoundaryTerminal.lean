module

public import DirectedDistances.KMSW.WholePlaneLLRecordEdges
public import DirectedDistances.KMSW.WholePlaneRunBoundaryDegree
import DirectedDistances.KMSW.OutgoingInterval

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/

/-! Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
not the paper result. -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk
open scoped Classical

private theorem terminal_coordinate_succ_ge_R (w : ℕ → Fin 3) (n : ℕ) :
    R w n - 1 ≤ R w (n + 1) := by
  have hR : R w (n + 1) = R w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by
    exact Finset.sum_range_succ _ _
  have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    split_ifs <;> omega
  rw [hR]
  omega

private theorem terminal_coordinate_succ_ge_L (w : ℕ → Fin 3) (n : ℕ) :
    L w n - 1 ≤ L w (n + 1) := by
  have hL : L w (n + 1) = L w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
    exact Finset.sum_range_succ _ _
  have hs : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
    unfold RandomWalk.lazyTwoDimensionalStep
    omega
  rw [hL]
  omega

private theorem terminal_exists_coordinate_eq_of_le (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) {n : ℕ} (hn : f n ≤ a) :
    ∃ m ≤ n, f m = a := by
  classical
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

private theorem terminal_first_hit_strict_record (f : ℕ → ℤ)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (hzero : f 0 = 0)
    {a : ℤ} (ha : a < 0) (h : ∃ n, f n = a) :
    ∀ j < Nat.find h, a < f j := by
  intro j hj
  by_contra hnot
  have hjle : f j ≤ a := by omega
  obtain ⟨m, hmj, hma⟩ := terminal_exists_coordinate_eq_of_le
    f hstep hzero ha hjle
  have hmn : m < Nat.find h := hmj.trans_lt hj
  exact (Nat.find_min h hmn) hma

private theorem terminal_L_first_hit_strict_record (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ j < boundaryHitTime w h k, L w (boundaryHitTime w h k) < L w j := by
  have htime : boundaryHitTime w h k = Nat.find (h.leftHit k hk) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_right (by omega : ¬ 0 < k)]
  have hspec := Nat.find_spec (h.leftHit k hk)
  have hstrict := terminal_first_hit_strict_record (L w)
    (terminal_coordinate_succ_ge_L w) (by simp [L]) (by omega : k < 0)
    (h.leftHit k hk)
  intro j hj
  rw [htime] at hj
  rw [htime, hspec]
  exact hstrict j hj

private theorem terminal_R_shift_add (w : ℕ → Fin 3) (t n : ℕ) :
    R w (t + n) = R w t + R (fun i => w (t + i)) n := by
  induction n with
  | zero => simp [R]
  | succ n ih =>
    have hg : R w (t + n + 1) = R w (t + n) +
        (RandomWalk.lazyTwoDimensionalStep (w (t + n))).2 := by
      exact Finset.sum_range_succ _ _
    have hs : R (fun i => w (t + i)) (n + 1) =
        R (fun i => w (t + i)) n +
          (RandomWalk.lazyTwoDimensionalStep (w (t + n))).2 := by
      exact Finset.sum_range_succ _ _
    rw [Nat.add_succ, hg, hs, ih]
    omega

private theorem terminal_L_shift_add (w : ℕ → Fin 3) (t n : ℕ) :
    L w (t + n) = L w t + L (fun i => w (t + i)) n := by
  induction n with
  | zero => simp [L]
  | succ n ih =>
    have hg : L w (t + n + 1) = L w (t + n) +
        (RandomWalk.lazyTwoDimensionalStep (w (t + n))).1 := by
      exact Finset.sum_range_succ _ _
    have hs : L (fun i => w (t + i)) (n + 1) =
        L (fun i => w (t + i)) n +
          (RandomWalk.lazyTwoDimensionalStep (w (t + n))).1 := by
      exact Finset.sum_range_succ _ _
    rw [Nat.add_succ, hg, hs, ih]
    omega





theorem boundaryHitWitnesses_of_le (W : ℤ → Fin 3) {N M : ℕ} (hNM : N ≤ M)
    (hN : BoundaryHitWitnesses (shiftedStream W N)) :
    BoundaryHitWitnesses (shiftedStream W M) := by
  let d := M - N
  let wM := shiftedStream W M
  let wN := shiftedStream W N
  have hcode : (fun i => wM (d + i)) = wN := by
    dsimp [d, wM, wN]
    exact shiftedStream_shift W N M hNM
  have hRadd (i : ℕ) : R wM (d + i) = R wM d + R wN i := by
    rw [terminal_R_shift_add]
    rw [hcode]
  have hLadd (i : ℕ) : L wM (d + i) = L wM d + L wN i := by
    rw [terminal_L_shift_add]
    rw [hcode]
  have hstepR : ∀ n, R wM n - 1 ≤ R wM (n + 1) :=
    terminal_coordinate_succ_ge_R wM
  have hstepL : ∀ n, L wM n - 1 ≤ L wM (n + 1) :=
    terminal_coordinate_succ_ge_L wM
  refine ⟨?_, ?_⟩
  · intro k hk
    let a : ℤ := -k
    let q : ℤ := max 1 (R wM d - a)
    have hq : 1 ≤ q := le_max_left _ _
    obtain ⟨i, hi⟩ := hN.rightHit q hq
    have hle : R wM (d + i) ≤ a := by
      rw [hRadd, hi]
      dsimp [q, a]
      omega
    obtain ⟨m, _, hm⟩ := terminal_exists_coordinate_eq_of_le
      (R wM) hstepR (by simp [R]) (by dsimp [a]; omega) hle
    exact ⟨m, by simpa [a] using hm⟩
  · intro k hk
    let a : ℤ := k
    let q : ℤ := max 1 (L wM d - a)
    have hq : 1 ≤ q := le_max_left _ _
    obtain ⟨i, hi⟩ := hN.leftHit (-q) (by omega)
    have hle : L wM (d + i) ≤ a := by
      rw [hLadd, hi]
      dsimp [q, a]
      omega
    obtain ⟨m, _, hm⟩ := terminal_exists_coordinate_eq_of_le
      (L wM) hstepL (by simp [L]) (by dsimp [a]; omega) hle
    exact ⟨m, by simpa [a] using hm⟩





theorem wholePlane_leftBoundary_vertex_terminal (W : ℤ → Fin 3) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (k : ℤ) (hk : k ≤ 0)
    (hLLPresent : wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N)
        (boundaryHitTime (shiftedStream W N) h (k - 1))))) :
    ∃ M, N ≤ M ∧ ∃ t,
      wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k) =
        wholePlaneVertexι W M
          (edgeEast (shiftedStream W M) (act (shiftedStream W M) t)) := by
  let w := shiftedStream W N
  let n := boundaryHitTime w h (k - 1)
  let e := kmswLLCreatedEdge w n
  have hkn : k - 1 ≤ -1 := by omega
  have hrecord := terminal_L_first_hit_strict_record w h hkn
  have hn0 : 0 < n := by
    by_contra hn
    have hn' : n = 0 := by omega
    have hh : L w n = k - 1 := by
      dsimp [n]
      exact boundaryHitTime_left_spec w h hkn
    rw [hn'] at hh
    simp [L] at hh
    omega
  have hmem : e ∈ (kmswStage w n).LL := by
    rw [kmswStage_LL_eq]
    apply List.mem_map.mpr
    refine ⟨n, List.mem_reverse.mpr ?_, rfl⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (by omega),
      decide_eq_true ⟨hn0, hrecord⟩⟩
  have heBound : e < (kmswStage w n).nextEdge := by
    apply (kmswStage_boundary_ids_lt_nextEdge w n).2 e
    simp only [List.mem_append]
    tauto
  have hboundary := boundaryVertex_left_missing_edge w h hkn
  have hEast : edgeEast w e = boundaryVertex w h k := by
    have hend := (edge_endpoints_eq w heBound).2
    calc
      edgeEast w e = (kmswStage w n).east e := hend.symm
      _ = boundaryVertex w h ((k - 1) + 1) := hboundary.2.1
      _ = boundaryVertex w h k := by congr 1; omega
  have htail := (wholePlaneEdgePresent_ι W N e).mp hLLPresent
  obtain ⟨M, hNM, htail⟩ := htail
  let f := wholePlaneEdgeTrans W N M hNM e
  have hpresent := htail M le_rfl
  obtain ⟨j, hjbound, hjpresent⟩ := hpresent
  obtain ⟨t, _, hft⟩ := stagePresent_exists_active (shiftedStream W M) j f
    hjbound hjpresent
  have hι : wholePlaneEdgeι W M f = wholePlaneEdgeι W N e := by
    exact congrFun (wholePlaneEdgeι_trans W N M hNM) e
  have hEastι : wholePlaneVertexι W M (edgeEast (shiftedStream W M) f) =
      wholePlaneVertexι W N (edgeEast w e) := by
    simpa only [wholePlaneEdgeEast_ι] using congrArg (wholePlaneEdgeEast W) hι
  refine ⟨M, hNM, t, ?_⟩
  calc
    wholePlaneVertexι W N (boundaryVertex w h k) =
        wholePlaneVertexι W N (edgeEast w e) := by rw [hEast]
    _ = wholePlaneVertexι W M (edgeEast (shiftedStream W M) f) := hEastι.symm
    _ = wholePlaneVertexι W M
        (edgeEast (shiftedStream W M) (act (shiftedStream W M) t)) := by rw [hft]





theorem wholePlaneIID_ae_leftBoundary_vertex_terminal :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N : ℕ,
      ∃ h : BoundaryHitWitnesses (shiftedStream W N),
        ∀ k : ℤ, k ≤ 0 → ∃ M, N ≤ M ∧ ∃ t,
          wholePlaneVertexι W N (boundaryVertex (shiftedStream W N) h k) =
            wholePlaneVertexι W M
              (edgeEast (shiftedStream W M) (act (shiftedStream W M) t)) := by
  filter_upwards [wholePlaneIID_ae_runBoundaryDegree,
    wholePlaneIID_ae_LL_record_edges] with W hdegree hrecords
  intro N
  obtain ⟨h, _⟩ := hdegree N
  refine ⟨h, fun k hk => ?_⟩
  let w := shiftedStream W N
  let m := boundaryHitTime w h (k - 1)
  have hkn : k - 1 ≤ -1 := by omega
  have hhit : L w m = k - 1 := by
    dsimp [m]
    exact boundaryHitTime_left_spec w h hkn
  have hm : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := by omega
    rw [hm0] at hhit
    simp [L] at hhit
    omega
  have hr := terminal_L_first_hit_strict_record w h hkn
  have hLL := (hrecords N m hm hr).1
  exact wholePlane_leftBoundary_vertex_terminal W N h k hk (by
    simpa [w, m] using hLL)

end DirectedDistances.KMSW
