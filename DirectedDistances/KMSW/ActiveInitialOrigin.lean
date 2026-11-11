module

public import DirectedDistances.KMSW.CutEquivalence
public import DirectedDistances.KMSW.WholePlaneCofinalFreshness




public section
namespace DirectedDistances.KMSW
open scoped Classical

private theorem initial_mem_stack (w : ℕ → Fin 3) (n : ℕ) :
    activeInitial w n ∈ CutConverse.westStack w n := by
  rw [CutConverse.activeInitial_eq]
  apply List.mem_map.mpr
  refine ⟨act w n, List.mem_reverse.mpr ?_, rfl⟩
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  simp [act, hes]




theorem activeInitial_level_eq (w : ℕ → Fin 3) {a n : ℕ} (han : a ≤ n)
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




theorem activeInitial_origin_dichotomy (w : ℕ → Fin 3) {a m : ℕ}
    (ha : 0 < a) (ham : a ≤ m)
    (hfirst : ∀ b, b < a → activeInitial w b ≠ activeInitial w m)
    (hprev : activeInitial w (a - 1) ≠ activeInitial w m)
    (heq : activeInitial w a = activeInitial w m)
    (hrecords : ∀ d, a - 1 ≤ d → d < m → minR w d < R w d) :
    (∃ k, w k = 1 ∧ activeInitial w m = (kmswStage w k).nextVertex) ∨
      (∃ d, d < m ∧ w d = 0 ∧ minL w d = L w d ∧
        activeInitial w m = (kmswStage w d).nextVertex) := by
  classical
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (show a ≠ 0 by omega)
  have hda : d = a - 1 := by omega
  have hdm : d < m := by omega
  have hprevD : activeInitial w d ≠ activeInitial w m := by
    simpa [hda] using hprev
  have hR := hrecords d (by omega) hdm
  have hUR : (kmswStage w d).UR ≠ [] := by
    intro he
    have hr := (kmswStage_UR_eq_nil_iff_record w d).mp he
    omega
  have had : activeInitial w (d + 1) = activeInitial w m := by
    simpa [hd] using heq
  have hav := CutConverse.activeInitial_eq w (d + 1)
  by_cases h0 : w d = 0
  · cases he : (kmswStage w d).UL.dropLast.reverse with
    | nil =>
      have hL := (kmswStage_UL_dropLast_reverse_eq_nil_iff_record w d).mp he
      have hnew : activeInitial w (d + 1) = (kmswStage w d).nextVertex := by
        rw [hav]
        simp [act, kmswStage, kmswStep, h0, kmswCodeStep,
          kmswStepOfStep, he, State.addEdge]
      exact Or.inr ⟨d, hdm, h0, hL.symm, had.symm.trans hnew⟩
    | cons e es =>
      have heUL : e ∈ (kmswStage w d).UL :=
        List.dropLast_subset _ (List.mem_reverse.mp (by rw [he]; simp))
      rw [kmswStage_UL_eq] at heUL
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp heUL
      have hbd : b ≤ d := by
        have := List.mem_range.mp (List.mem_filter.mp hb).1
        omega
      have heq' : activeInitial w (d + 1) = activeInitial w b := by
        rw [hav]
        simp only [act, kmswStage, kmswStep, h0, kmswCodeStep,
          ↓reduceIte, kmswStepOfStep, he, State.addEdge]
        exact (edge_endpoints_eq w (act_lt_nextEdge w hbd)).1
      have hbm : b < a := by omega
      exact (hfirst b hbm (heq'.symm.trans had)).elim
  · by_cases h1 : w d = 1
    · have heq' : activeInitial w (d + 1) = activeInitial w d := by
        rw [hav, CutConverse.activeInitial_eq w d]
        simp [act, kmswStage, kmswStep, kmswCodeStep, h1,
          kmswStepOfStep, State.addEdge]
      exact (hprevD (heq'.symm.trans had)).elim
    · have h2 : w d = 2 := by
        apply Fin.ext
        have := (w d).isLt
        have hn0 : (w d).val ≠ 0 := fun h => h0 (Fin.ext h)
        have hn1 : (w d).val ≠ 1 := fun h => h1 (Fin.ext h)
        omega
      have heq' : activeInitial w (d + 1) =
          (kmswStage w d).east (act w d) := by
        rw [hav]
        cases he : (kmswStage w d).UR with
        | nil => exact (hUR he).elim
        | cons e es =>
          have hc := (CutConverse.frontier_history w d).1
          simp only [CutConverse.FrontierCoherent, CutConverse.pendingVertices,
            he, List.map_cons, List.dropLast_cons_cons] at hc
          have hh := (List.cons.inj hc).1
          simpa [act, kmswStage, kmswStep, kmswCodeStep, h2,
            kmswStepOfStep, he] using hh
      have hmem : (kmswStage w d).east (act w d) ∈
          (CutConverse.pendingVertices (kmswStage w d)).dropLast := by
        cases he : (kmswStage w d).UR with
        | nil => exact (hUR he).elim
        | cons e es => simp [CutConverse.pendingVertices, he, act]
      obtain ⟨k, _, hk, hv⟩ := CutConverse.pending_interior_up_origin w d hmem
      exact Or.inl ⟨k, hk, had.symm.trans (heq'.trans hv)⟩

end DirectedDistances.KMSW
