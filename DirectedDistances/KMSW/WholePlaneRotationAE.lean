module

public import DirectedDistances.KMSW.WholePlaneCofinalFreshness
import DirectedDistances.KMSW.CutSeparationAnyStart
import DirectedDistances.KMSW.AllocatedVertices

/-! word; not the paper result. -/

public section
namespace DirectedDistances.KMSW
open MeasureTheory RandomWalk
open scoped Classical

private theorem initial_mem_stack (w : ℕ → Fin 3) (n : ℕ) :
    activeInitial w n ∈ CutConverse.westStack w n := by
  rw [CutConverse.activeInitial_eq]
  apply List.mem_map.mpr
  refine ⟨act w n, List.mem_reverse.mpr ?_, rfl⟩
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  simp [act, hes]

private theorem initial_level_eq (w : ℕ → Fin 3) {a n : ℕ} (han : a ≤ n)
    (heq : activeInitial w a = activeInitial w n) : L w a = L w n := by
  have hmem : activeInitial w a ∈ CutConverse.westStack w n :=
    heq.symm ▸ initial_mem_stack w n
  have habove := CutConverse.barrier_of_westStack_mem w han hmem
  let b := Nat.findGreatest (fun j => L w j = L w a) n
  have hbn : b ≤ n := Nat.findGreatest_le n
  have hab : a ≤ b := Nat.le_findGreatest han rfl
  have hb : L w b = L w a :=
    Nat.findGreatest_spec (P := fun j => L w j = L w a) han rfl
  have hrec : ∀ j, b < j → j ≤ n → L w b + 1 ≤ L w j := by
    intro j hbj hjn
    have hne : L w j ≠ L w a := Nat.findGreatest_is_greatest hbj hjn
    have hle := habove j (by omega) hjn
    omega
  have hbe : act w b ∈ (kmswStage w n).UL := by
    rw [kmswStage_UL_eq]
    exact List.mem_map.mpr ⟨b, List.mem_filter.mpr
      ⟨List.mem_range.mpr (by omega), decide_eq_true hrec⟩, rfl⟩
  have hba : activeInitial w a = activeInitial w b := by
    rw [CutConverse.activeInitial_eq, CutConverse.activeInitial_eq]
    have hstable := (kmswStage_endpoints_stable w hab
      (act_lt_nextEdge w (le_refl a))).1
    exact hstable.symm.trans (kmsw_west_act_eq_of_level w hab hb.symm
      (fun j haj hjb => habove j haj (by omega)))
  have hmap := CutConverse.westStack_nodup w n
  have hact : act w n ∈ (kmswStage w n).UL := by
    obtain ⟨es, hes⟩ := kmswStage_UL_last w n
    simp [act, hes]
  have hends : (kmswStage w n).west (act w b) =
      (kmswStage w n).west (act w n) := by
    rw [(edge_endpoints_eq w (act_lt_nextEdge w hbn)).1]
    change activeInitial w b = _
    rw [← CutConverse.activeInitial_eq]
    exact hba.symm.trans heq
  have hedges : act w b = act w n := List.inj_on_of_nodup_map hmap
    (List.mem_reverse.mpr hbe) (List.mem_reverse.mpr hact) hends
  have htime : b = n := CutConverse.act_injective w hedges
  simpa [htime] using hb.symm





theorem activeInitial_visit_after_strict_undershoot (w : ℕ → Fin 3)
    {a q m : ℕ} (ham : a ≤ m) (hqm : q ≤ m)
    (heq : activeInitial w a = activeInitial w m) (hq : L w q < L w m) :
    q < a := by
  have hlev := initial_level_eq w ham heq
  by_contra h
  have hmem : activeInitial w a ∈ CutConverse.westStack w m :=
    heq.symm ▸ initial_mem_stack w m
  have hb := CutConverse.barrier_of_westStack_mem w ham hmem q (by omega) hqm
  omega

private theorem up_nonrecord (w : ℕ → Fin 3) (k : ℕ) (hk : w k = 1) :
    KMSWNonrecordVertex w (kmswStage w k).nextVertex := by
  have hbase : 2 ≤ (kmswStage w k).nextVertex :=
    CutConverse.nextVertex_mono w (Nat.zero_le k)
  have hup : (kmswStage w (k + 1)).nextVertex =
      (kmswStage w k).nextVertex + 1 := by
    simp [kmswStage, kmswStep, kmswCodeStep, hk, kmswStepOfStep, State.addEdge]
  refine ⟨hbase, ?_⟩
  intro j hj
  have exclude (halloc : (kmswStage w j).nextVertex <
      (kmswStage w (j + 1)).nextVertex) : j = k := by
    rcases lt_trichotomy j k with h | h | h
    · have hm := CutConverse.nextVertex_mono w (Nat.succ_le_of_lt h)
      change (kmswStage w (j + 1)).nextVertex ≤ (kmswStage w k).nextVertex at hm
      omega
    · exact h
    · have hm := CutConverse.nextVertex_mono w (Nat.succ_le_of_lt h)
      change (kmswStage w (k + 1)).nextVertex ≤ (kmswStage w j).nextVertex at hm
      omega
  constructor
  · intro hd hr
    have hu := (kmswStage_UR_eq_nil_iff_record w j).mpr hr
    have he : j = k := exclude (by simp [kmswStage, kmswStep, hd, kmswStepOfStep, hu])
    subst j
    simp [kmswCodeStep, hk] at hd
  · intro hl hr
    have hu := (kmswStage_UL_dropLast_reverse_eq_nil_iff_record w j).mpr hr
    have he : j = k := exclude (by
      simp [kmswStage, kmswStep, hl, kmswStepOfStep, hu, State.addEdge])
    subst j
    simp [kmswCodeStep, hk] at hl

private theorem activeInitial_up_origin_of_interval (w : ℕ → Fin 3) (q m : ℕ)
    (hqm : q ≤ m) (hbelow : L w q < L w m)
    (hrecords : ∀ d, q ≤ d → d < m →
      minL w d < L w d ∧ minR w d < R w d) :
    ∃ k, w k = 1 ∧ activeInitial w m = (kmswStage w k).nextVertex := by
  classical
  let P := fun a => activeInitial w a = activeInitial w m
  have hex : ∃ a, P a := ⟨m, rfl⟩
  let a := Nat.find hex
  have ha : P a := Nat.find_spec hex
  have ham : a ≤ m := Nat.find_min' hex rfl
  have hqa : q < a := activeInitial_visit_after_strict_undershoot w ham hqm ha hbelow
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (show a ≠ 0 by omega)
  have hqd : q ≤ d := by omega
  have hdm : d < m := by omega
  have hnot (b : ℕ) (hb : b ≤ d) : activeInitial w b ≠ activeInitial w m := by
    intro he
    have hmin := Nat.find_min' hex he
    change a ≤ b at hmin
    omega
  have had : activeInitial w (d + 1) = activeInitial w m := by simpa [hd] using ha
  have hs := hrecords d hqd hdm
  have hUL : (kmswStage w d).UL.dropLast.reverse ≠ [] := by
    intro he
    have hr := (kmswStage_UL_dropLast_reverse_eq_nil_iff_record w d).mp he
    omega
  have hUR : (kmswStage w d).UR ≠ [] := by
    intro he
    have hr := (kmswStage_UR_eq_nil_iff_record w d).mp he
    omega
  have hav := CutConverse.activeInitial_eq w (d + 1)
  by_cases h0 : w d = 0
  · cases he : (kmswStage w d).UL.dropLast.reverse with
    | nil => exact (hUL he).elim
    | cons e es =>
      have heUL : e ∈ (kmswStage w d).UL :=
        List.dropLast_subset _ (List.mem_reverse.mp (by rw [he]; simp))
      rw [kmswStage_UL_eq] at heUL
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp heUL
      have hbd : b ≤ d := by
        have := List.mem_range.mp (List.mem_filter.mp hb).1
        omega
      have heq : activeInitial w (d + 1) = activeInitial w b := by
        rw [hav]
        simp only [act, kmswStage, kmswStep, h0, kmswCodeStep, ↓reduceIte,
          kmswStepOfStep, he, State.addEdge]
        exact (edge_endpoints_eq w (act_lt_nextEdge w hbd)).1
      exact (hnot b hbd (heq.symm.trans had)).elim
  · by_cases h1 : w d = 1
    · have heq : activeInitial w (d + 1) = activeInitial w d := by
        rw [hav, CutConverse.activeInitial_eq w d]
        simp [act, kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep,
          State.addEdge]
      exact (hnot d le_rfl (heq.symm.trans had)).elim
    · have h2 : w d = 2 := by
        apply Fin.ext
        have := (w d).isLt
        have hn0 : (w d).val ≠ 0 := fun h => h0 (Fin.ext h)
        have hn1 : (w d).val ≠ 1 := fun h => h1 (Fin.ext h)
        omega
      have heq : activeInitial w (d + 1) = (kmswStage w d).east (act w d) := by
        rw [hav]
        cases he : (kmswStage w d).UR with
        | nil => exact (hUR he).elim
        | cons e es =>
          have hc := (CutConverse.frontier_history w d).1
          simp only [CutConverse.FrontierCoherent, CutConverse.pendingVertices,
            he, List.map_cons, List.dropLast_cons_cons] at hc
          have hh := (List.cons.inj hc).1
          simpa [act, kmswStage, kmswStep, kmswCodeStep, h2, kmswStepOfStep, he]
            using hh
      have hmem : (kmswStage w d).east (act w d) ∈
          (CutConverse.pendingVertices (kmswStage w d)).dropLast := by
        cases he : (kmswStage w d).UR with
        | nil => exact (hUR he).elim
        | cons e es => simp [CutConverse.pendingVertices, he, act]
      obtain ⟨k, _, hk, hv⟩ := CutConverse.pending_interior_up_origin w d hmem
      exact ⟨k, hk, had.symm.trans (heq.trans hv)⟩

private theorem windowEdgeMapInf_act (w : ℕ → Fin 3) (s k : ℕ) :
    kmswWindowEdgeMapInf w s (act (fun i => w (s + i)) k) = act w (s + k) := by
  unfold act
  rw [kmswWindowEdgeMapInf_eq_stage w s k _
    (kmswStage_boundary_ids_lt_nextEdge (fun i => w (s + i)) k).1]
  exact (kmswWindowPatchData_rel w s k).active

private theorem initial_trans (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) (k : ℕ) :
    wholePlaneVertexTrans W N M h (activeInitial (shiftedStream W N) k) =
      activeInitial (shiftedStream W M) (M - N + k) := by
  have he : wholePlaneEdgeTrans W N M h (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
    simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M h] using
      windowEdgeMapInf_act (shiftedStream W M) (M - N) k
  unfold activeInitial
  rw [← wholePlaneEdgeTrans_west, he]

private theorem shifted_L (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) (k : ℕ) :
    L (shiftedStream W M) (M - N + k) =
      L (shiftedStream W M) (M - N) + L (shiftedStream W N) k := by
  unfold L
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [congrFun (shiftedStream_shift W N M h) i]

private theorem ae_run_R_unbounded :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N : ℕ, ∀ a : ℤ,
      ∃ n, R (shiftedStream W N) n ≤ a := by
  apply ae_all_iff.2
  intro N
  have hf := ae_codeWalk_snd_unbounded_below
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath N] at hf
  have hp := ae_of_ae_map (measurable_shiftedCodePath N).aemeasurable hf
  simpa [codeWalk, shiftedCodePath, R, Prod.snd_sum] using hp

private theorem cofinal_nonrecord_of_visits (W : ℤ → Fin 3)
    (hB : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream W M) k < R (shiftedStream W M) k ∧
       minL (shiftedStream W M) k < L (shiftedStream W M) k))
    (hvisit : ∀ N v, ∃ k, activeInitial (shiftedStream W N) k = v) :
    ∀ N v, ∃ M, ∃ hNM : N ≤ M,
      KMSWNonrecordVertex (shiftedStream W M) (wholePlaneVertexTrans W N M hNM v) := by
  classical
  intro N v
  obtain ⟨k, hk⟩ := hvisit N v
  obtain ⟨A₀, hA₀⟩ := hB ((k : ℤ) - N)
  let A := max N A₀
  have hNA : N ≤ A := Nat.le_max_left _ _
  have hA := hA₀ A (Nat.le_max_right _ _)
  let n := A - N + k
  have hn : (((k : ℤ) - N + (A : ℤ)).toNat) = n := by dsimp [n]; omega
  have hmin : minL (shiftedStream W A) n < L (shiftedStream W A) n := by
    simpa only [hn] using hA.2.2
  obtain ⟨q, hqn, heq⟩ := runningMin_attained (L (shiftedStream W A)) n
  have hbelow : L (shiftedStream W A) q < L (shiftedStream W A) n := by
    change minL (shiftedStream W A) n = _ at heq
    omega
  let J := Finset.Icc q n
  let f : ℕ → ℕ := fun j => Classical.choose (hB ((j : ℤ) - A))
  let M := max A (J.sup f)
  have hAM : A ≤ M := Nat.le_max_left _ _
  have hNM : N ≤ M := hNA.trans hAM
  have hsup : J.sup f ≤ M := Nat.le_max_right _ _
  have hbelowM : L (shiftedStream W M) (M - A + q) <
      L (shiftedStream W M) (M - A + n) := by
    rw [shifted_L W A M hAM, shifted_L W A M hAM]
    omega
  have hrecords : ∀ d, M - A + q ≤ d → d < M - A + n →
      minL (shiftedStream W M) d < L (shiftedStream W M) d ∧
      minR (shiftedStream W M) d < R (shiftedStream W M) d := by
    intro d hqd hdn
    let j := d - (M - A)
    have hj : j ∈ J := Finset.mem_Icc.mpr (by dsimp [j]; constructor <;> omega)
    have hle : f j ≤ M := (Finset.le_sup hj).trans hsup
    have hb := Classical.choose_spec (hB ((j : ℤ) - A)) M hle
    have hd : ((j : ℤ) - A + (M : ℤ)).toNat = d := by dsimp [j]; omega
    simpa only [hd] using hb.2.symm
  obtain ⟨i, hi, hv⟩ := activeInitial_up_origin_of_interval (shiftedStream W M)
    (M - A + q) (M - A + n) (by omega) hbelowM hrecords
  have hnM : M - A + n = M - N + k := by dsimp [n]; omega
  have hvM : wholePlaneVertexTrans W N M hNM v =
      (kmswStage (shiftedStream W M) i).nextVertex := by
    rw [← hk, initial_trans, ← hnM, hv]
  exact ⟨M, hNM, hvM ▸ up_nonrecord (shiftedStream W M) i hi⟩




theorem wholePlaneIID_ae_cofinalFreshness :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ N v, ∃ M, ∃ hNM : N ≤ M,
      ∀ M' (hMM' : M ≤ M'),
        wholePlaneFresh W M M' hMM' (wholePlaneVertexTrans W N M hNM v) := by
  filter_upwards [wholePlaneIID_ae_fixed_time_nonrecord,
    wholePlaneIID_ae_finite_incidence, ae_run_R_unbounded] with W hB hfin hR
  apply wholePlaneCofinalFreshness_of_nonrecord W
  apply cofinal_nonrecord_of_visits W hB
  intro N v
  apply allocated_vertex_eventually_activeInitial_of_R_unbounded
    (shiftedStream W N) (hR N) v
  exact kmsw_vertex_allocated_of_finite_incidence (shiftedStream W N) (hfin N) v



theorem wholePlaneIID_ae_rotationHypothesis :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, WholePlaneRotationHypothesis W := by
  filter_upwards [wholePlaneIID_ae_finite_incidence,
    wholePlaneIID_ae_cofinalFreshness] with W hfin hfresh
  exact ⟨hfin, hfresh⟩

end DirectedDistances.KMSW


