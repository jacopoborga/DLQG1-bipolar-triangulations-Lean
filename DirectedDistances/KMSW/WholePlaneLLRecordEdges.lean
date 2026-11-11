module

public import DirectedDistances.KMSW.WholePlaneLeftBoundaryPresent

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW

open MeasureTheory RandomWalk
open scoped Classical





theorem wholePlaneLLCreatedEdge_present_of_record_escape (W : ℤ → Fin 3)
    (hB : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream W M) k < R (shiftedStream W M) k ∧
       minL (shiftedStream W M) k < L (shiftedStream W M) k))
    (N m : ℕ) (hm : 0 < m)
    (hr : ∀ j < m, L (shiftedStream W N) m < L (shiftedStream W N) j) :
    wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) m)) := by
  let t : ℤ := (m : ℤ) - N
  obtain ⟨M₀, hM₀⟩ := hB t
  let M := max N M₀
  have hNM : N ≤ M := Nat.le_max_left _ _
  have hescape := hM₀ M (Nat.le_max_right _ _)
  have hi : ((t + (M : ℤ)).toNat) = M - N + m := by
    dsimp [t]
    omega
  have hn : ¬ ∀ j < M - N + m,
      L (shiftedStream W M) (M - N + m) < L (shiftedStream W M) j := by
    intro h
    obtain ⟨j, hj, heq⟩ := runningMin_attained (L (shiftedStream W M))
      (M - N + m)
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

private theorem stage_LL_mem_mono_record (w : ℕ → Fin 3) {n m e : ℕ}
    (hnm : n ≤ m) (he : e ∈ (kmswStage w n).LL) :
    e ∈ (kmswStage w m).LL := by
  induction m, hnm using Nat.le_induction with
  | base => exact he
  | succ m hnm ih =>
    change e ∈ (kmswStep (kmswStage w m) (w m)).LL
    unfold kmswStep
    cases hc : kmswCodeStep (w m) with
    | down =>
      cases hs : (kmswStage w m).UR <;>
        simpa [kmswStepOfStep, hs, State.addEdge] using ih
    | up => simpa only [kmswStepOfStep, State.addEdge] using ih
    | left =>
      cases hs : (kmswStage w m).UL.dropLast.reverse with
      | cons a as => simpa only [kmswStepOfStep, hs, State.addEdge] using ih
      | nil => simpa only [kmswStepOfStep, hs, State.addEdge,
          List.mem_cons] using (Or.inr ih)





theorem kmswLLCreatedEdge_not_present_of_record (w : ℕ → Fin 3) (m : ℕ)
    (hm : 0 < m) (hr : ∀ j < m, L w m < L w j) :
    ¬ EdgePresent w (kmswLLCreatedEdge w m) := by
  let e := kmswLLCreatedEdge w m
  have hbound : e < (kmswStage w m).nextEdge := by
    have hmono := kmswStage_nextEdge_mono w (m := 0) (n := m) (Nat.zero_le _)
    have hinitial : (kmswStage w 0).nextEdge = 1 := by
      simp [kmswStage, kmswInit]
    rw [hinitial] at hmono
    dsimp [e, kmswLLCreatedEdge]
    omega
  have hmem : e ∈ (kmswStage w m).LL := by
    rw [kmswStage_LL_eq]
    apply List.mem_map.mpr
    refine ⟨m, List.mem_reverse.mpr ?_, rfl⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (by omega), decide_eq_true ⟨hm, hr⟩⟩
  have hmissing : (kmswStage w m).present e = false :=
    ((kmswStage_status w m).1 e hbound).mpr (Or.inr hmem)
  intro hpresent
  obtain ⟨n, hn⟩ := hpresent.eventually_present
  let k := max m n
  have hboundK : e < (kmswStage w k).nextEdge :=
    hbound.trans_le (kmswStage_nextEdge_mono w (Nat.le_max_left _ _))
  have hmemK : e ∈ (kmswStage w k).LL :=
    stage_LL_mem_mono_record w (n := m) (m := k) (Nat.le_max_left _ _) hmem
  have hmissingK : (kmswStage w k).present e = false :=
    ((kmswStage_status w k).1 e hboundK).mpr (Or.inr hmemK)
  have hpresentK : (kmswStage w k).present e = true := by
    simpa [e] using (hn k (Nat.le_max_right _ _)).2
  rw [hmissingK] at hpresentK
  contradiction




theorem wholePlaneIID_ae_LL_record_edges :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N m : ℕ, 0 < m →
      (∀ j < m, L (shiftedStream W N) m < L (shiftedStream W N) j) →
      wholePlaneEdgePresent W
        (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) m)) ∧
        ¬ EdgePresent (shiftedStream W N) (kmswLLCreatedEdge (shiftedStream W N) m) := by
  filter_upwards [wholePlaneIID_ae_fixed_time_nonrecord] with W hB N m hm hr
  exact ⟨wholePlaneLLCreatedEdge_present_of_record_escape W hB N m hm hr,
    kmswLLCreatedEdge_not_present_of_record (shiftedStream W N) m hm hr⟩

end DirectedDistances.KMSW
