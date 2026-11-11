module

public import DirectedDistances.KMSW.StageSubgraph
public import DirectedDistances.KMSW.RunBoundaryVertexLabels
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
import DirectedDistances.KMSW.StageOuterCycle
import DirectedDistances.PaperProofs.Section7.LongPathStageVertices
import DirectedDistances.PaperProofs.Section7.LongPathBoundarySegment

/-! Supporting lemmas for paper labels `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW
open scoped Classical

private def stageLift (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    Prefunctor (StagePresentVertex w m) (StagePresentVertex w n) where
  obj v := ⟨v.id⟩
  map {_ _} e :=
    ⟨e.val, (present_mono w e.property.1 e.property.2.1 n hmn).1,
      (present_mono w e.property.1 e.property.2.1 n hmn).2,
      ((present_endpoints_stable w e.property.1 e.property.2.1 hmn).1).trans
        e.property.2.2.1,
      ((present_endpoints_stable w e.property.1 e.property.2.1 hmn).2).trans
        e.property.2.2.2⟩

private theorem fresh_left_label (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (n : ℕ) (hc : w n = 0) (hu : (kmswStage w n).UL.dropLast.reverse = []) :
    ∃ k : ℤ, k ≤ -1 ∧ boundaryHitTime w h k = n + 1 ∧
      boundaryVertex w h k = (kmswStage w n).nextVertex := by
  have hlen := kmswStage_UL_length w n
  have hdrop := congrArg List.length hu
  simp only [List.length_reverse, List.length_dropLast, List.length_nil] at hdrop
  have hne := (kmswStage_UL_nonempty_active_last w n).1
  have hpos : 0 < (kmswStage w n).UL.length := List.length_pos_iff.mpr hne
  have hmin : L w n = minL w n := by omega
  have hs : L w (n + 1) = L w n - 1 := by
    have hs : L w (n + 1) = L w n +
        (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w n)).1 :=
      Finset.sum_range_succ _ _
    rw [hc] at hs
    exact hs
  have hzero : L w 0 = 0 := rfl
  have hminzero := runningMin_le (L w) n 0 (Nat.zero_le n)
  have hk : L w (n + 1) ≤ -1 := by
    change minL w n ≤ L w 0 at hminzero
    omega
  have hrec : ∀ j ≤ n, L w (n + 1) < L w j := by
    intro j hj
    have hh := runningMin_le (L w) n j hj
    change minL w n ≤ L w j at hh
    omega
  have htime : boundaryHitTime w h (L w (n + 1)) = n + 1 := by
    have hfind : boundaryHitTime w h (L w (n + 1)) =
        Nat.find (h.leftHit (L w (n + 1)) hk) := by
      simp only [boundaryHitTime, dite_eq_right (by omega : L w (n + 1) ≠ 0),
        dite_eq_right (by omega : ¬ 0 < L w (n + 1))]
    have hle : boundaryHitTime w h (L w (n + 1)) ≤ n + 1 := by
      rw [hfind]
      exact Nat.find_min' _ rfl
    have hspec := boundaryHitTime_left_spec w h hk
    have hnle : ¬ boundaryHitTime w h (L w (n + 1)) ≤ n := by
      intro hnle
      have hh := hrec _ hnle
      omega
    omega
  refine ⟨L w (n + 1), hk, htime, ?_⟩
  rw [boundaryVertex_eq_activeInitial w h (by omega) (by omega), htime,
    CutConverse.activeInitial_eq]
  simp only [kmswStage, act, kmswStep, hc, kmswCodeStep, ↓reduceIte,
    kmswStepOfStep, hu, State.addEdge, ite_self]

private theorem new_vertex_input (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (n v : ℕ) (hv : v < (kmswStage w (n + 1)).nextVertex)
    (hold : ¬ v < (kmswStage w n).nextVertex) :
    (∃ k : ℤ, k ≤ -1 ∧ boundaryHitTime w h k = n + 1 ∧
      boundaryVertex w h k = v) ∨
    (∃ a : ℕ, a < (kmswStage w n).nextVertex ∧
      Nonempty ((⟨a⟩ : StagePresentVertex w (n + 1)) ⟶ ⟨v⟩)) := by
  have hends := kmswStage_endpoints_lt_nextVertex w n (act w n)
    (act_lt_nextEdge w le_rfl)
  by_cases hc : w n = 0
  · cases hu : (kmswStage w n).UL.dropLast.reverse with
    | nil =>
      have hV : v = (kmswStage w n).nextVertex := by
        simp [kmswStage, kmswStep, hc, kmswCodeStep,
          kmswStepOfStep, hu] at hv
        omega
      obtain ⟨k, hk, ht, heq⟩ := fresh_left_label w h n hc hu
      exact Or.inl ⟨k, hk, ht, heq.trans hV.symm⟩
    | cons e es =>
      simp [kmswStage, kmswStep, hc, kmswCodeStep,
        kmswStepOfStep, hu, State.addEdge] at hv
      exact (hold hv).elim
  · by_cases hc1 : w n = 1
    · have hV : v = (kmswStage w n).nextVertex := by
        simp [kmswStage, kmswStep, hc1, kmswCodeStep,
          kmswStepOfStep] at hv
        omega
      subst v
      refine Or.inr ⟨(kmswStage w n).west (act w n), hends.1, ⟨?_⟩⟩
      refine ⟨(kmswStage w n).nextEdge, ?_, ?_, ?_, ?_⟩
      all_goals simp [kmswStage, kmswStep, hc1, kmswCodeStep, kmswStepOfStep,
        State.addEdge, act]
    · have hc2 : w n = 2 := by
        apply Fin.ext
        have := (w n).isLt
        have h0 : (w n).val ≠ 0 := fun hh => hc (Fin.ext hh)
        have h1 : (w n).val ≠ 1 := fun hh => hc1 (Fin.ext hh)
        omega
      cases hu : (kmswStage w n).UR with
      | cons e es =>
        simp [kmswStage, kmswStep, hc2, kmswCodeStep,
          kmswStepOfStep, hu] at hv
        exact (hold hv).elim
      | nil =>
        have hV : v = (kmswStage w n).nextVertex := by
          simp [kmswStage, kmswStep, hc2, kmswCodeStep,
            kmswStepOfStep, hu] at hv
          omega
        subst v
        refine Or.inr ⟨(kmswStage w n).east (act w n), hends.2, ⟨?_⟩⟩
        refine ⟨(kmswStage w n).nextEdge, ?_, ?_, ?_, ?_⟩
        all_goals simp [kmswStage, kmswStep, hc2, kmswCodeStep, kmswStepOfStep,
          hu, State.addEdge, act]

private theorem lower_route_core (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (n : ℕ) (v : ℕ) (hv : v < (kmswStage w n).nextVertex) :
    ∃ k : ℤ, k ≤ 0 ∧ boundaryHitTime w h k ≤ n ∧
      Nonempty (Path (⟨boundaryVertex w h k⟩ : StagePresentVertex w n) ⟨v⟩) := by
  induction n generalizing v with
  | zero =>
    have hv' : v = 0 ∨ v = 1 := by change v < 2 at hv; omega
    refine ⟨0, le_rfl, ?_, ?_⟩
    · rw [boundaryHitTime_zero]
    · rw [boundaryVertex_zero]
      rcases hv' with rfl | rfl
      · exact ⟨Path.nil⟩
      · exact ⟨(initialEdgeArrow w 0).toPath⟩
  | succ n ih =>
    have lift_old : ∀ a, a < (kmswStage w n).nextVertex →
        ∃ k : ℤ, k ≤ 0 ∧ boundaryHitTime w h k ≤ n + 1 ∧
          Nonempty (Path (⟨boundaryVertex w h k⟩ : StagePresentVertex w (n + 1))
            ⟨a⟩) := by
      intro a ha
      obtain ⟨k, hk, ht, ⟨p⟩⟩ := ih a ha
      exact ⟨k, hk, by omega, ⟨(stageLift w (Nat.le_succ n)).mapPath p⟩⟩
    by_cases hold : v < (kmswStage w n).nextVertex
    · exact lift_old v hold
    · rcases new_vertex_input w h n v hv hold with ⟨k, hk, ht, heq⟩ | ⟨a, ha, ⟨e⟩⟩
      · refine ⟨k, by omega, by omega, ?_⟩
        rw [heq]
        exact ⟨Path.nil⟩
      · obtain ⟨k, hk, ht, ⟨p⟩⟩ := lift_old a ha
        exact ⟨k, hk, ht, ⟨p.comp e.toPath⟩⟩

private theorem root_mem_lowerRight (w : ℕ → Fin 3) (n : ℕ) :
    0 ∈ (kmswStage w n).LR := by
  induction n with
  | zero => exact List.mem_cons_self
  | succ n ih =>
    obtain ⟨t, ht⟩ := kmswStage_LR_succ_eq_append w n
    rw [ht]
    exact List.mem_append_left t ih




theorem stage_cell_lower_boundary_route (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (n : ℕ) (x : StagePresentVertex w n) (hx : x.id < (kmswStage w n).nextVertex) :
    ∃ k : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ k ∧
      k ≤ ((kmswStage w n).LR.length : ℤ) ∧
      boundaryVertex w h k < (kmswStage w n).nextVertex ∧
      (∃ e, (e ∈ (kmswStage w n).LL ∨ e ∈ (kmswStage w n).LR) ∧
        ((kmswStage w n).west e = boundaryVertex w h k ∨
          (kmswStage w n).east e = boundaryVertex w h k)) ∧
      Nonempty (Path (⟨boundaryVertex w h k⟩ : StagePresentVertex w n) x) := by
  obtain ⟨k, hk, ht, hp⟩ := lower_route_core w h n x.id hx
  have hmin : minL w n ≤ k := by
    by_cases hk0 : k = 0
    · subst k
      exact runningMin_le (L w) n 0 (Nat.zero_le n)
    · have hs := boundaryHitTime_left_spec w h (show k ≤ -1 by omega)
      have hm := runningMin_le (L w) n (boundaryHitTime w h k) ht
      change minL w n ≤ L w (boundaryHitTime w h k) at hm
      omega
  have hlen := kmswStage_LL_length w n
  refine ⟨k, by omega, by omega, boundaryVertex_lt_stageNextVertex w h k n ht, ?_, ?_⟩
  · by_cases hk0 : k = 0
    · subst k
      exact ⟨0, Or.inr (root_mem_lowerRight w n), Or.inl (by
        rw [(initial_edge_endpoints w n).1, boundaryVertex_zero])⟩
    · have he := (boundary_left_edge_persistent w h (show k ≤ -1 by omega)).2 n ht
      exact ⟨_, Or.inl he.1, Or.inl he.2.2.1⟩
  · cases x
    exact hp

end DirectedDistances.PaperProofs.Section7
