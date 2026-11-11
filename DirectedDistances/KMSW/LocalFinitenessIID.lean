module

public import DirectedDistances.KMSW.LocalFiniteness
public import DirectedDistances.RandomWalk.PitmanCodes
public import DirectedDistances.RandomWalk.IIDCodeRelabel
import DirectedDistances.KMSW.StageIncidence

/-! # Finite geometric incidence for unconditioned KMSW walks

Helpers for the one-sided maps in the setup of Section 5, -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open scoped Classical

private theorem initial_mem_stack (w : ℕ → Fin 3) (n : ℕ) :
    activeInitial w n ∈ CutConverse.westStack w n := by
  rw [CutConverse.activeInitial_eq]
  apply List.mem_map.mpr
  refine ⟨act w n, List.mem_reverse.mpr ?_, rfl⟩
  obtain ⟨es, hes⟩ := kmswStage_UL_last w n
  simp [act, hes]

-- A strict descent below a past minimum removes every old west-stack
-- vertex, including its bottom vertex in the left-fresh branch.
private theorem initial_eventually_ne (w : ℕ → Fin 3)
    (hLb : ∀ a : ℤ, ∃ n, L w n ≤ a) (v : ℕ) :
    ∃ N, ∀ n, N ≤ n → activeInitial w n ≠ v := by
  by_cases hv : ∃ a, activeInitial w a = v
  · obtain ⟨a, ha⟩ := hv
    obtain ⟨q, hq⟩ := hLb (minL w a - 1)
    have hmin := runningMin_le (L w) a a (le_refl a)
    change minL w a ≤ L w a at hmin
    have haq : a < q := by
      by_contra hnot
      have hqa : q ≤ a := by omega
      have hlow := runningMin_le (L w) a q hqa
      change minL w a ≤ L w q at hlow
      omega
    refine ⟨q, fun n hqn he => ?_⟩
    have hmem : activeInitial w a ∈ CutConverse.westStack w n :=
      (ha.trans he.symm).symm ▸ initial_mem_stack w n
    have hb := CutConverse.barrier_of_westStack_mem w
      (show a ≤ n by omega) hmem q (by omega) hqn
    omega
  · exact ⟨0, fun n _ he => hv ⟨n, he⟩⟩

private theorem pending_step_mem (w : ℕ → Fin 3) (n : ℕ) {v : ℕ}
    (hv : v ∈ CutConverse.pendingVertices (kmswStage w (n + 1))) :
    v = (kmswStage w n).nextVertex ∨
      v ∈ CutConverse.pendingVertices (kmswStage w n) := by
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  have hmap : s.UR.map t.east = s.UR.map s.east := by
    apply List.map_congr_left
    intro e he
    have he' : e < s.nextEdge :=
      (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
        simp only [List.mem_append]
        tauto)
    exact (kmswStage_endpoints_stable w (Nat.le_succ n) he').2
  change v = s.nextVertex ∨ v ∈ CutConverse.pendingVertices s
  change v ∈ CutConverse.pendingVertices t at hv
  have ht : t = kmswStep s (w n) := rfl
  by_cases h0 : w n = 0
  · have hUR : t.UR = s.UR := by
      rw [ht, h0]
      cases hs : s.UL.dropLast.reverse <;>
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
    have hEast : t.east t.active = s.east s.active := by
      rw [ht, h0]
      cases hs : s.UL.dropLast.reverse <;>
        simp [kmswStep, kmswCodeStep, kmswStepOfStep, hs, State.addEdge]
    right
    simpa only [CutConverse.pendingVertices, hUR, hEast, hmap] using hv
  · by_cases h1 : w n = 1
    · have hUR : t.UR = (s.nextEdge + 1) :: s.UR := by
        simp [ht, h1, kmswStep, kmswCodeStep, kmswStepOfStep]
      have hEast : t.east t.active = s.nextVertex := by
        simp [ht, h1, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
      have hNew : t.east (s.nextEdge + 1) = s.east s.active := by
        simp [ht, h1, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
      simpa only [CutConverse.pendingVertices, hUR, List.map_cons, hEast, hNew,
        hmap, List.mem_cons] using hv
    · have h2 : w n = 2 := by
        apply Fin.ext
        have := (w n).isLt
        have hn0 : (w n).val ≠ 0 := fun he => h0 (Fin.ext he)
        have hn1 : (w n).val ≠ 1 := fun he => h1 (Fin.ext he)
        omega
      cases hs : s.UR with
      | nil =>
        left
        simpa [ht, h2, CutConverse.pendingVertices, kmswStep, kmswCodeStep,
          kmswStepOfStep, hs, State.addEdge] using hv
      | cons e es =>
        right
        have hv' : v ∈ s.east e :: es.map s.east := by
          simpa [ht, h2, CutConverse.pendingVertices, kmswStep, kmswCodeStep,
            kmswStepOfStep, hs] using hv
        exact List.mem_cons_of_mem _ (by simpa [hs] using hv')

private theorem east_eventually_ne (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) {v n : ℕ}
    (hv : v < (kmswStage w n).nextVertex) :
    ∃ N, n ≤ N ∧ ∀ m, N ≤ m →
      (kmswStage w m).east (act w m) ≠ v := by
  obtain ⟨k, hnk, h2, hempty⟩ := exists_empty_ur_down_after w hR n
  have hvk : v < (kmswStage w k).nextVertex :=
    hv.trans_le (CutConverse.nextVertex_mono w hnk)
  have hbase : v ∉ CutConverse.pendingVertices (kmswStage w (k + 1)) := by
    simpa [CutConverse.pendingVertices, kmswStage, kmswStep, kmswCodeStep,
      h2, kmswStepOfStep, hempty, State.addEdge] using (Nat.ne_of_lt hvk)
  have htail : ∀ m, k + 1 ≤ m →
      v ∉ CutConverse.pendingVertices (kmswStage w m) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hbase
    | succ m hm ih =>
      intro hmem
      rcases pending_step_mem w m hmem with hfresh | hold
      · have hmono := CutConverse.nextVertex_mono w (show k ≤ m by omega)
        omega
      · exact ih hold
  refine ⟨k + 1, by omega, fun m hm he => ?_⟩
  exact htail m hm (List.mem_cons.mpr (Or.inl he.symm))

private theorem step_no_new_incidence (s : State) (c : Fin 3) (v : ℕ)
    (hW : s.west s.active ≠ v)
    (hW' : (kmswStep s c).west (kmswStep s c).active ≠ v)
    (hE : s.east s.active ≠ v) (hV : s.nextVertex ≠ v)
    {e : ℕ} (he : s.nextEdge ≤ e) (he' : e < (kmswStep s c).nextEdge) :
    (kmswStep s c).west e ≠ v ∧ (kmswStep s c).east e ≠ v := by
  unfold kmswStep at *
  cases hc : kmswCodeStep c with
  | down =>
    cases hs : s.UR with
    | nil =>
      have heq : e = s.nextEdge := by
        simp only [hc, kmswStepOfStep, hs, State.addEdge] at he'
        omega
      subst e
      simpa [hc, kmswStepOfStep, hs, State.addEdge] using And.intro hE hV
    | cons f fs =>
      simp only [hc, kmswStepOfStep, hs] at he'
      omega
  | left =>
    cases hs : s.UL.dropLast.reverse with
    | nil =>
      have hbound : e < s.nextEdge + 2 := by
        simpa [hc, kmswStepOfStep, hs, State.addEdge, Nat.add_assoc] using he'
      have heq : e = s.nextEdge ∨ e = s.nextEdge + 1 := by omega
      rcases heq with rfl | rfl
      · simpa [hc, kmswStepOfStep, hs, State.addEdge] using And.intro hV hE
      · simpa [hc, kmswStepOfStep, hs, State.addEdge] using And.intro hV hW
    | cons f fs =>
      have heq : e = s.nextEdge := by
        simp only [hc, kmswStepOfStep, hs, State.addEdge] at he'
        omega
      subst e
      have hF : s.west f ≠ v := by
        simpa [hc, kmswStepOfStep, hs, State.addEdge] using hW'
      simpa [hc, kmswStepOfStep, hs, State.addEdge] using And.intro hF hE
  | up =>
    have hbound : e < s.nextEdge + 2 := by
      simpa [hc, kmswStepOfStep, State.addEdge, Nat.add_assoc] using he'
    have heq : e = s.nextEdge ∨ e = s.nextEdge + 1 := by omega
    rcases heq with rfl | rfl
    · simpa [hc, kmswStepOfStep, State.addEdge] using And.intro hW hV
    · simpa [hc, kmswStepOfStep, State.addEdge] using And.intro hV hE

/-- Every vertex has finite geometric incidence when both coordinates are
unbounded below. This includes missing boundary edges in the one-sided KMSW -/
theorem kmsw_finite_incident_edges_of_unbounded_below (w : ℕ → Fin 3)
    (hLb : ∀ a : ℤ, ∃ n, L w n ≤ a)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ) :
    {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite := by
  classical
  by_cases hv : ∃ n, v < (kmswStage w n).nextVertex
  · obtain ⟨n, hv⟩ := hv
    obtain ⟨A, hA⟩ := initial_eventually_ne w hLb v
    obtain ⟨B, hnB, hB⟩ := east_eventually_ne w hR hv
    let N := max A B
    have hnew (m : ℕ) (hm : N ≤ m) {e : ℕ}
        (he : (kmswStage w m).nextEdge ≤ e)
        (he' : e < (kmswStage w (m + 1)).nextEdge) :
        (kmswStage w (m + 1)).west e ≠ v ∧
          (kmswStage w (m + 1)).east e ≠ v := by
      have hmA : A ≤ m := (le_max_left A B).trans hm
      have hmB : B ≤ m := (le_max_right A B).trans hm
      have hW : (kmswStage w m).west (kmswStage w m).active ≠ v := by
        change (kmswStage w m).west (act w m) ≠ v
        rw [← CutConverse.activeInitial_eq]
        exact hA m hmA
      have hW' : (kmswStage w (m + 1)).west (kmswStage w (m + 1)).active ≠ v := by
        change (kmswStage w (m + 1)).west (act w (m + 1)) ≠ v
        rw [← CutConverse.activeInitial_eq]
        exact hA (m + 1) (by omega)
      have hV : (kmswStage w m).nextVertex ≠ v := by
        have hmono := CutConverse.nextVertex_mono w (hnB.trans hmB)
        omega
      exact step_no_new_incidence (kmswStage w m) (w m) v hW hW'
        (hB m hmB) hV he he'
    have htail : ∀ m, N ≤ m → ∀ e, e < (kmswStage w m).nextEdge →
        ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v) →
        e < (kmswStage w N).nextEdge := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact fun _ he _ => he
      | succ m hm ih =>
        intro e he hinc
        by_cases hold : e < (kmswStage w m).nextEdge
        · have hs := kmswStage_endpoints_stable w (Nat.le_succ m) hold
          rw [hs.1, hs.2] at hinc
          exact ih e hold hinc
        · have hn := hnew m hm (Nat.le_of_not_gt hold) he
          exact (hinc.elim hn.1 hn.2).elim
    apply (Set.finite_lt_nat (kmswStage w N).nextEdge).subset
    rintro e ⟨m, he, hinc⟩
    rcases le_total m N with hm | hm
    · exact he.trans_le (kmswStage_nextEdge_mono w hm)
    · exact htail m hm e he hinc
  · apply Set.finite_empty.subset
    rintro e ⟨n, he, hinc⟩
    have hb := kmswStage_endpoints_lt_nextVertex w n e he
    rcases hinc with heq | heq
    · exact (hv ⟨n, heq ▸ hb.1⟩).elim
    · exact (hv ⟨n, heq ▸ hb.2⟩).elim

/-- Simultaneously every vertex has finite geometric incidence for the iid
(Section 5 setup), including its missing boundary edges. -/
theorem iidCodes_ae_finite_incident_edges :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, ∀ v : ℕ,
      let w := fun i => ω (i + 1)
      {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite := by
  filter_upwards [RandomWalk.ae_codeWalk_fst_unbounded_below,
    RandomWalk.ae_codeWalk_snd_unbounded_below] with ω hL hR v
  intro w
  apply kmsw_finite_incident_edges_of_unbounded_below w ?_ ?_ v
  · intro a
    obtain ⟨n, hn⟩ := hL a
    refine ⟨n, ?_⟩
    rw [RandomWalk.kmsw_L_eq]
    exact hn
  · intro a
    obtain ⟨n, hn⟩ := hR a
    refine ⟨n, ?_⟩
    rw [RandomWalk.kmsw_R_eq]
    exact hn

end DirectedDistances.KMSW
