module

public import DirectedDistances.KMSW.WholePlaneLeftBoundaryMissing
public import DirectedDistances.KMSW.WholePlaneCofinalFreshness

/-! Helper toward F4c / Lemma 3.10 (whole-plane KMSW: run-N left-boundary edges are
whole-plane edges missing from the run-N submap); not the paper result. -/

public section
namespace DirectedDistances.KMSW
open MeasureTheory RandomWalk
open scoped Classical

/-- Helper toward F4c / Lemma 3.10 (whole-plane KMSW: run-N left-boundary edges are
whole-plane edges missing from the run-N submap); not the paper result.
Every LL edge has a positive strict L-record creation time -/
theorem kmswStage_LL_edge_created_at_record (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).LL) :
    ∃ m, 0 < m ∧ m ≤ n ∧ (∀ j < m, L w m < L w j) ∧
      e = kmswLLCreatedEdge w m := by
  rw [kmswStage_LL_eq] at he
  obtain ⟨m, hm, hme⟩ := List.mem_map.mp he
  have hf := List.mem_filter.mp (List.mem_reverse.mp hm)
  have hr := of_decide_eq_true hf.2
  exact ⟨m, hr.1, by have := List.mem_range.mp hf.1; omega, hr.2, hme.symm⟩

private theorem left_record_step (w : ℕ → Fin 3) (k : ℕ)
    (hr : ∀ j < k + 1, L w (k + 1) < L w j) :
    w k = 0 ∧ (kmswStage w k).UL.dropLast.reverse = [] := by
  have hs : L w (k + 1) = L w k + ((w k : ℤ) - 1) := by
    exact Finset.sum_range_succ _ _
  have hn := hr k (by omega)
  have hc : w k = 0 := by
    apply Fin.ext
    have hb := (w k).isLt
    omega
  have hmin : L w k = minL w k := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) k
    change minL w k = L w j at he
    have hl := hr j (by omega)
    have hb := runningMin_le (L w) k k le_rfl
    change minL w k ≤ L w k at hb
    rw [hc] at hs
    norm_num at hs
    omega
  exact ⟨hc, (kmswStage_UL_dropLast_reverse_eq_nil_iff_record w k).mpr hmin⟩

private theorem window_LL_created_present (w : ℕ → Fin 3) (s k : ℕ)
    (hc : w (s + k) = 0)
    (hsmall : (kmswStage (fun i => w (s + i)) k).UL.dropLast.reverse = [])
    (hlarge : (kmswStage w (s + k)).UL.dropLast.reverse ≠ []) :
    EdgePresent w (kmswWindowEdgeMapInf w s
      (kmswLLCreatedEdge (fun i => w (s + i)) (k + 1))) := by
  let u := fun i => w (s + i)
  let d := kmswWindowPatchData w s k
  change (kmswStage u k).UL.dropLast.reverse = [] at hsmall
  have hrel := kmswWindowPatchData_rel w s k
  have hne : (kmswStage u k).UL.map d.φ ≠ [] := by
    intro h
    exact (kmswStage_UL_nonempty_active_last u k).1 (List.map_eq_nil_iff.mp h)
  have hdrop : (kmswStage w (s + k)).UL.dropLast.reverse = d.A.reverse := by
    rw [hrel.ul, List.dropLast_append_of_ne_nil hne, ← List.map_dropLast,
      List.reverse_append, ← List.map_reverse, hsmall]
    rfl
  cases hA : d.A.reverse with
  | nil => exact (hlarge (hdrop.trans hA)).elim
  | cons q es =>
    have hG : (kmswStage w (s + k)).UL.dropLast.reverse = q :: es := hdrop.trans hA
    have hq : q ∈ (kmswStage w (s + k)).UL := by
      apply (List.dropLast_sublist _).subset
      apply List.mem_reverse.mp
      rw [hG]
      exact List.mem_cons_self
    have hb := (kmswStage_boundary_ids_lt_nextEdge w (s + k)).2 q (by
      simp only [List.mem_append]
      tauto)
    have hp := (kmswStage_status w (s + k)).2.1 q hq
    have hid : kmswLLCreatedEdge u (k + 1) = (kmswStage u k).nextEdge + 1 := by
      simp [kmswLLCreatedEdge, kmswStage, kmswStep, kmswCodeStep, u, hc,
        hsmall, kmswStepOfStep, State.addEdge]
    have he : kmswLLCreatedEdge u (k + 1) < (kmswStage u (k + 1)).nextEdge := by
      simp [hid, kmswStage, kmswStep, kmswCodeStep, u, hc,
        hsmall, kmswStepOfStep, State.addEdge]
    have hmap : kmswWindowEdgeMapInf w s (kmswLLCreatedEdge u (k + 1)) = q := by
      rw [kmswWindowEdgeMapInf_eq_stage w s (k + 1) _ he]
      change (KMSWWindowPatchData.step (kmswStage w (s + k)) (kmswStage u k)
        (kmswCodeStep (w (s + k))) d).φ (kmswLLCreatedEdge u (k + 1)) = q
      simp [KMSWWindowPatchData.step, hc, kmswCodeStep, hsmall, hA, hid]
    rw [hmap]
    exact ⟨s + k, hb, hp⟩





theorem wholePlaneLLCreatedEdge_present_of_nonrecord (W : ℤ → Fin 3)
    (N M : ℕ) (hNM : N ≤ M) (m : ℕ) (hm : 0 < m)
    (hr : ∀ j < m, L (shiftedStream W N) m < L (shiftedStream W N) j)
    (hn : ¬ ∀ j < M - N + m,
      L (shiftedStream W M) (M - N + m) < L (shiftedStream W M) j) :
    EdgePresent (shiftedStream W M)
      (wholePlaneEdgeTrans W N M hNM (kmswLLCreatedEdge (shiftedStream W N) m)) := by
  cases m with
  | zero => omega
  | succ k =>
    obtain ⟨hc, hsmall⟩ := left_record_step (shiftedStream W N) k hr
    have hcode : shiftedStream W M (M - N + k) = 0 := by
      rw [congrFun (shiftedStream_shift W N M hNM) k]
      exact hc
    have hlarge : (kmswStage (shiftedStream W M) (M - N + k)).UL.dropLast.reverse ≠
        [] := by
      intro hz
      have hmin := (kmswStage_UL_dropLast_reverse_eq_nil_iff_record _ _).mp hz
      apply hn
      intro j hj
      have hle := runningMin_le (L (shiftedStream W M)) (M - N + k) j (by omega)
      change minL (shiftedStream W M) (M - N + k) ≤ _ at hle
      have hs : L (shiftedStream W M) (M - N + k + 1) =
          L (shiftedStream W M) (M - N + k) - 1 := by
        simp only [L, Finset.sum_range_succ, hcode, lazyTwoDimensionalStep_zero,
          sub_eq_add_neg]
      have hi : M - N + (k + 1) = M - N + k + 1 := by omega
      rw [hi]
      omega
    have hsmall' :
        (kmswStage (fun i => shiftedStream W M (M - N + i)) k).UL.dropLast.reverse =
          [] := by
      rw [shiftedStream_shift W N M hNM]
      exact hsmall
    simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M hNM] using
      window_LL_created_present (shiftedStream W M) (M - N) k hcode hsmall' hlarge

/-- Helper toward F4c / Lemma 3.10 (whole-plane KMSW: run-N left-boundary edges are
whole-plane edges missing from the run-N submap); not the paper result.
The named input `hB` is fixed-time backward record escape, supplied almost surely by
`wholePlaneIID_ae_fixed_time_nonrecord`. Presence transports monotonically, so the
rotation hypothesis is unnecessary for this helper -/
theorem wholePlane_LL_edge_present_colimit_of_record_escape (W : ℤ → Fin 3)
    (hB : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream W M) k < R (shiftedStream W M) k ∧
       minL (shiftedStream W M) k < L (shiftedStream W M) k))
    (N e : ℕ) (he : e ∈ (kmswStage (shiftedStream W N) N).LL) :
    wholePlaneEdgePresent W (wholePlaneEdgeι W N e) := by
  obtain ⟨m, hm, _, hr, rfl⟩ := kmswStage_LL_edge_created_at_record
    (shiftedStream W N) N e he
  obtain ⟨M₀, hM₀⟩ := hB ((m : ℤ) - N)
  let M := max N M₀
  have hNM : N ≤ M := Nat.le_max_left _ _
  have hescape := hM₀ M (Nat.le_max_right _ _)
  have hi : ((m : ℤ) - N + (M : ℤ)).toNat = M - N + m := by omega
  have hn : ¬ ∀ j < M - N + m,
      L (shiftedStream W M) (M - N + m) < L (shiftedStream W M) j := by
    intro h
    obtain ⟨j, hj, heq⟩ := runningMin_attained (L (shiftedStream W M)) (M - N + m)
    have hl : minL (shiftedStream W M) (M - N + m) <
        L (shiftedStream W M) (M - N + m) := by
      simpa only [hi] using hescape.2.2
    change minL (shiftedStream W M) (M - N + m) = _ at heq
    have hj' : j < M - N + m := by
      by_contra hnot
      have he : j = M - N + m := by omega
      rw [he] at heq
      omega
    have hh := h j hj'
    omega
  have hp := wholePlaneLLCreatedEdge_present_of_nonrecord W N M hNM m hm hr hn
  have hcol := wholePlaneEdgePresent_ι_of_run_present W M _ hp
  have hι : wholePlaneEdgeι W M (wholePlaneEdgeTrans W N M hNM
      (kmswLLCreatedEdge (shiftedStream W N) m)) =
      wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) m) :=
    congrFun (wholePlaneEdgeι_trans W N M hNM) _
  rw [hι] at hcol
  exact hcol

/-- Helper toward F4c / Lemma 3.10 (whole-plane KMSW: run-N left-boundary edges are
whole-plane edges missing from the run-N submap); not the paper result.
All run indices and edges are simultaneous on the fixed-time backward record escape -/
theorem wholePlaneIID_ae_LL_edge_present_colimit :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N e,
      e ∈ (kmswStage (shiftedStream W N) N).LL →
        wholePlaneEdgePresent W (wholePlaneEdgeι W N e) := by
  filter_upwards [wholePlaneIID_ae_fixed_time_nonrecord] with W hB N e he
  exact wholePlane_LL_edge_present_colimit_of_record_escape W hB N e he

end DirectedDistances.KMSW
