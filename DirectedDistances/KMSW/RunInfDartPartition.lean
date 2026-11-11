module

public import DirectedDistances.KMSW.InfiniteBoundary
public import DirectedDistances.KMSW.StageTriangleDarts
import DirectedDistances.KMSW.BoundaryRecordsMissing













public section
namespace DirectedDistances.KMSW

open scoped Classical

private theorem run_LL_mem_mono (w : ℕ → Fin 3) {n m e : ℕ}
    (hnm : n ≤ m) (he : e ∈ (kmswStage w n).LL) :
    e ∈ (kmswStage w m).LL := by
  induction m, hnm using Nat.le_induction with
  | base => exact he
  | succ m _ ih =>
    change e ∈ (kmswStep (kmswStage w m) (w m)).LL
    unfold kmswStep
    cases kmswCodeStep (w m) with
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

private theorem run_LR_mem_mono (w : ℕ → Fin 3) {n m e : ℕ}
    (hnm : n ≤ m) (he : e ∈ (kmswStage w n).LR) :
    e ∈ (kmswStage w m).LR := by
  induction m, hnm using Nat.le_induction with
  | base => exact he
  | succ m _ ih =>
    obtain ⟨t, ht⟩ := kmswStage_LR_succ_eq_append w m
    rw [ht]
    exact List.mem_append_left _ ih

private theorem run_outer_mem_iff (w : ℕ → Fin 3) (n : ℕ) (d : ℕ × Bool) :
    d ∈ stageOuterWordVal w n ↔
      (d.2 = false ∧ (d.1 ∈ (kmswStage w n).UL ∨ d.1 ∈ (kmswStage w n).UR)) ∨
      (d.2 = true ∧ (d.1 ∈ (kmswStage w n).LR ∨ d.1 ∈ (kmswStage w n).LL)) := by
  rcases d with ⟨e, b⟩
  cases b <;> simp [stageOuterWordVal_eq_runs]

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
of the infinite two-sided run map are exactly the eventual LL/LR stack darts;
not the paper result. The unbounded-below premise `hL` makes every fixed edge
permanently absent from UL after some finite stage. -/
theorem kmswRun_UL_eventually_absent (w : ℕ → Fin 3)
    (hL : ∀ a : ℤ, ∃ n, L w n ≤ a) (e : ℕ) :
    ∃ N, ∀ n ≥ N, e ∉ (kmswStage w n).UL := by
  classical
  by_cases hex : ∃ n, e ∈ (kmswStage w n).UL
  · obtain ⟨n₀, hn₀⟩ := hex
    rw [kmswStage_UL_eq] at hn₀
    obtain ⟨m, _, hme⟩ := List.mem_map.mp hn₀
    obtain ⟨t, ht⟩ := hL (minL w m - 1)
    have hmt : m < t := by
      by_contra h
      have hmin := runningMin_le (L w) m t (by omega)
      change minL w m ≤ L w t at hmin
      omega
    have hmin := runningMin_le (L w) m m le_rfl
    change minL w m ≤ L w m at hmin
    refine ⟨t, fun n hn he => ?_⟩
    rw [kmswStage_UL_eq] at he
    obtain ⟨m', hm', hm'e⟩ := List.mem_map.mp he
    have hmm : m' = m := CutConverse.act_injective w (hm'e.trans hme.symm)
    subst m'
    have hrecord := of_decide_eq_true (List.mem_filter.mp hm').2
    have hbad := hrecord t hmt hn
    omega
  · exact ⟨0, fun n _ he => hex ⟨n, he⟩⟩

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
of the infinite two-sided run map are exactly the eventual LL/LR stack darts;
not the paper result. The unbounded-below premise `hR` makes every fixed edge
permanently absent from UR after some finite stage. -/
theorem kmswRun_UR_eventually_absent (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (e : ℕ) :
    ∃ N, ∀ n ≥ N, e ∉ (kmswStage w n).UR := by
  classical
  obtain ⟨t, ht⟩ := hR (minR w e - 1)
  have het : e < t := by
    by_contra h
    have hmin := runningMin_le (R w) e t (by omega)
    change minR w e ≤ R w t at hmin
    omega
  refine ⟨t, fun n hn he => ?_⟩
  rw [kmswStage_UR_eq] at he
  obtain ⟨m, hm, hme⟩ := List.mem_map.mp he
  have halloc := kmsw_edge_allocated_by_self w m
  have hme' : (kmswStage w m).nextEdge - 1 = e := hme
  have hme_le : m ≤ e := by omega
  have hrecord := of_decide_eq_true (List.mem_filter.mp (List.mem_reverse.mp hm)).2
  have hbad := hrecord.2.2 t (by omega) hn
  have hmin := runningMin_le (R w) e (m - 1) (by omega)
  change minR w e ≤ R w (m - 1) at hmin
  omega

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
of the infinite two-sided run map are exactly the eventual LL/LR stack darts;
not the paper result. The fixed side of both lower stacks is `true`. -/
theorem kmswRunInfDart_eventually_outer_iff (w : ℕ → Fin 3)
    (hL : ∀ a : ℤ, ∃ n, L w n ≤ a)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (d : ℕ × Bool) :
    (∃ N, ∀ n ≥ N, d ∈ stageOuterWordVal w n) ↔
      (∃ e, (∃ N, ∀ n ≥ N, e ∈ (kmswStage w n).LL) ∧ d = (e, true)) ∨
      (∃ e, (∃ N, ∀ n ≥ N, e ∈ (kmswStage w n).LR) ∧ d = (e, true)) := by
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨NUL, hUL⟩ := kmswRun_UL_eventually_absent w hL d.1
    obtain ⟨NUR, hUR⟩ := kmswRun_UR_eventually_absent w hR d.1
    let n := max N (max NUL NUR)
    have hn : N ≤ n := by dsimp [n]; omega
    have hnUL : NUL ≤ n := by dsimp [n]; omega
    have hnUR : NUR ≤ n := by dsimp [n]; omega
    rcases (run_outer_mem_iff w n d).mp (hN n hn) with ⟨_, he⟩ | ⟨hb, he⟩
    · rcases he with he | he
      · exact (hUL n hnUL he).elim
      · exact (hUR n hnUR he).elim
    · have hd : d = (d.1, true) := Prod.ext rfl hb
      rcases he with he | he
      · exact Or.inr ⟨d.1, ⟨n, fun m hm => run_LR_mem_mono w hm he⟩, hd⟩
      · exact Or.inl ⟨d.1, ⟨n, fun m hm => run_LL_mem_mono w hm he⟩, hd⟩
  · rintro (⟨e, ⟨N, hN⟩, rfl⟩ | ⟨e, ⟨N, hN⟩, rfl⟩)
    · exact ⟨N, fun n hn => (run_outer_mem_iff w n (e, true)).mpr
        (Or.inr ⟨rfl, Or.inr (hN n hn)⟩)⟩
    · exact ⟨N, fun n hn => (run_outer_mem_iff w n (e, true)).mpr
        (Or.inr ⟨rfl, Or.inl (hN n hn)⟩)⟩

private theorem run_triangle_unique (w : ℕ → Fin 3) (d : ℕ × Bool)
    (j : TriangleCreationTime w) (hdj : d ∈ stageTriangleDartList w j) :
    ∃! k : TriangleCreationTime w, d ∈ stageTriangleDartList w k := by
  refine ⟨j, hdj, ?_⟩
  intro k hkd
  by_contra hkj
  let n := max (j.val + 1) (k.val + 1)
  have hjn : j.val < n := by dsimp [n]; omega
  have hkn : k.val < n := by dsimp [n]; omega
  have hdisj := stageTriangleDartLists_disjoint w n j k hjn hkn
    (fun hjk => hkj hjk.symm)
  exact List.disjoint_left.mp hdisj hdj hkd

private theorem run_outer_or_triangle (w : ℕ → Fin 3) (d : ℕ × Bool) :
    (∃ N, ∀ n ≥ N, d ∈ stageOuterWordVal w n) ∨
      ∃! j : TriangleCreationTime w, d ∈ stageTriangleDartList w j := by
  classical
  by_cases ht : ∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j
  · obtain ⟨j, hj⟩ := ht
    exact Or.inr (run_triangle_unique w d j hj)
  · left
    refine ⟨d.1, fun n hn => ?_⟩
    have ha := (kmsw_edge_allocated_by_self w d.1).trans_le
      (kmswStage_nextEdge_mono w hn)
    let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, ha⟩, d.2)
    rcases stage_dart_partition w n x with ho | ⟨j, ⟨_, hj⟩, _⟩
    · exact (stageOuterWord_mem_val w n x).mp ho
    · exact (ht ⟨j, hj⟩).elim

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
of the infinite two-sided run map are exactly the eventual LL/LR stack darts;
not the paper result. Finite incidence `hfin` is retained for the limiting-map
interface; this dart partition needs only `hL` and `hR`. Missing LL edges remain
geometric edges, with outer side `true`. -/
theorem kmswRunInfDart_partition (w : ℕ → Fin 3)
    (_hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ a : ℤ, ∃ n, L w n ≤ a)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (d : ℕ × Bool) :
    (∃ e, (∃ N, ∀ n ≥ N, e ∈ (kmswStage w n).LL) ∧ d = (e, true)) ∨
      (∃ e, (∃ N, ∀ n ≥ N, e ∈ (kmswStage w n).LR) ∧ d = (e, true)) ∨
      ∃! j : TriangleCreationTime w, d ∈ stageTriangleDartList w j := by
  rcases run_outer_or_triangle w d with ho | ht
  · rcases (kmswRunInfDart_eventually_outer_iff w hL hR d).mp ho with hLL | hLR
    · exact Or.inl hLL
    · exact Or.inr (Or.inl hLR)
  · exact Or.inr (Or.inr ht)

/-- Helper toward F4c / Lemma 3.10 (lem-uibot-bdy,
of the infinite two-sided run map are exactly the eventual LL/LR stack darts;
not the paper result. This equivalence also excludes every recorded triangle
from the persistent outer boundary. -/
theorem kmswRunInfDart_boundary_iff_not_triangle (w : ℕ → Fin 3)
    (hL : ∀ a : ℤ, ∃ n, L w n ≤ a)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (d : ℕ × Bool) :
    ((∃ e, (∃ N, ∀ n ≥ N, e ∈ (kmswStage w n).LL) ∧ d = (e, true)) ∨
      (∃ e, (∃ N, ∀ n ≥ N, e ∈ (kmswStage w n).LR) ∧ d = (e, true))) ↔
      ¬ ∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j := by
  constructor
  · intro hb ht
    obtain ⟨N, hN⟩ := (kmswRunInfDart_eventually_outer_iff w hL hR d).mpr hb
    obtain ⟨j, hj⟩ := ht
    let n := max N (max d.1 (j.val + 1))
    have hNn : N ≤ n := by dsimp [n]; omega
    have hdn : d.1 ≤ n := by dsimp [n]; omega
    have hjn : j.val < n := by dsimp [n]; omega
    have ha := (kmsw_edge_allocated_by_self w d.1).trans_le
      (kmswStage_nextEdge_mono w hdn)
    let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, ha⟩, d.2)
    exact stageTriangleDart_not_outer w n j hjn x hj
      ((stageOuterWord_mem_val w n x).mpr (hN n hNn))
  · intro ht
    rcases run_outer_or_triangle w d with ho | ⟨j, hj, _⟩
    · exact (kmswRunInfDart_eventually_outer_iff w hL hR d).mp ho
    · exact (ht ⟨j, hj⟩).elim

end DirectedDistances.KMSW
