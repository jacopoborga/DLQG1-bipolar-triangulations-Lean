module

public import DirectedDistances.KMSW.QuadKMSWHat
import DirectedDistances.KMSW.FlowLineStageInvariant
import DirectedDistances.KMSW.StageIncidenceChains
import DirectedDistances.KMSW.StageSubgraph
meta import Lean.Elab.Tactic.Omega

/-! # Unreachability during left flow-line phases

Deterministic helpers for `lem-flow-line-times`, -/

public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory
open scoped Classical

private theorem prefix_reachable (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v ∈ stageReachableVertices w n) :
    Reachable (⟨0⟩ : PresentVertex w) ⟨v⟩ := by
  have hm := (mem_stageReachableVertices_iff w n v).1 hv
  rcases hm with rfl | ⟨p, _⟩
  · exact Reachable.refl _
  · exact ⟨p⟩

private theorem prefix_lt_nextVertex (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v ∈ stageReachableVertices w n) :
    v < (kmswStage w n).nextVertex := by
  induction n with
  | zero =>
      simp only [stageReachableVertices, Finset.mem_singleton] at hv
      subst v
      change 0 < 2
      omega
  | succ n ih =>
      rw [stageReachableVertices_succ] at hv
      split at hv
      · rcases Finset.mem_insert.mp hv with rfl | hv
        · exact ((kmswStage_endpoints_lt_nextVertex w n (act w n)
            (act_lt_nextEdge w le_rfl)).2).trans_le
              (CutConverse.nextVertex_mono w (Nat.le_succ n))
        · exact (ih hv).trans_le (CutConverse.nextVertex_mono w (Nat.le_succ n))
      · exact (ih hv).trans_le (CutConverse.nextVertex_mono w (Nat.le_succ n))

private theorem activeWest_mem_iff (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).west (act w n) ∈ stageReachableVertices w n ↔
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w n).west (act w n)⟩ :=
  (mem_stageReachableVertices_iff w n _).trans
    (actReachableBefore_activeWest_iff w n)

private theorem prefix_frozen_step (w : ℕ → Fin 3) (n : ℕ)
    (hn : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩) :
    stageReachableVertices w (n + 1) = stageReachableVertices w n := by
  have hmem : (kmswStage w n).west (act w n) ∉ stageReachableVertices w n :=
    fun hm => hn ((activeWest_mem_iff w n).1 hm)
  rw [stageReachableVertices_succ, ite_eq_right hmem]

private theorem predecessor_east (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hp : (kmswStage w n).UL.dropLast.reverse = e :: es) :
    (kmswStage w n).east e = (kmswStage w n).west (act w n) := by
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hr : xs.reverse = e :: es := by simpa [hxs] using hp
  have hxs' : xs = es.reverse ++ [e] := by
    have h := congrArg List.reverse hr
    simpa using h
  have hc := (kmswStage_boundary_chain_invariant w n).1.left_of_append
  have hc' : List.IsChain
      (fun a b => (kmswStage w n).east a = (kmswStage w n).west b)
      (es.reverse ++ [e, act w n]) := by
    simpa [hxs, hxs', List.append_assoc, act] using hc
  exact (List.isChain_append_cons_cons.mp hc').2.1

private theorem left_preserves_unreachable (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 0)
    (hn : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩) :
    ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩ := by
  intro hnext
  have hm := (stageReachableVertices_left_activeWest_iff w n hc).1
    ((activeWest_mem_iff w (n + 1)).2 hnext)
  cases hp : (kmswStage w n).UL.dropLast.reverse with
  | nil => simp [hp] at hm
  | cons e es =>
      have hmem : (kmswStage w n).west e ∈ stageReachableVertices w n := by
        simpa [hp] using hm
      have heUL : e ∈ (kmswStage w n).UL :=
        List.dropLast_subset _ (List.mem_reverse.mp (by rw [hp]; simp))
      have hb : e < (kmswStage w n).nextEdge :=
        (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by simp [heUL])
      have hends := edge_endpoints_eq w hb
      have heast := predecessor_east w n e es hp
      have hpresent := (kmswStage_status w n).2.1 e heUL
      obtain ⟨p⟩ := prefix_reachable w n _ hmem
      apply hn
      exact ⟨p.cons ⟨e, EdgePresent.of_stage_present hb hpresent,
        hends.1.symm, hends.2.symm.trans heast⟩⟩

private theorem up_preserves_unreachable (w : ℕ → Fin 3) (n : ℕ)
    (hc : w n = 1)
    (hn : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩) :
    ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩ := by
  have hw : (kmswStage w (n + 1)).west (act w (n + 1)) =
      (kmswStage w n).west (act w n) := by
    simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]
  rw [hw]
  exact hn

private def eastStack (w : ℕ → Fin 3) (n : ℕ) : List ℕ :=
  (kmswStage w n).east (act w n) ::
    (kmswStage w n).UR.map (kmswStage w n).east

private theorem old_east_map (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).UR.map (kmswStage w (n + 1)).east =
      (kmswStage w n).UR.map (kmswStage w n).east := by
  apply List.map_congr_left
  intro e he
  have hb : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by simp [he])
  exact (kmswStage_endpoints_stable w (Nat.le_succ n) hb).2

private theorem eastStack_left (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 0) :
    eastStack w (n + 1) = eastStack w n := by
  have hUR : (kmswStage w (n + 1)).UR = (kmswStage w n).UR := by
    cases hp : (kmswStage w n).UL.dropLast.reverse <;>
      simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hp,
        State.addEdge]
  have he : (kmswStage w (n + 1)).east (act w (n + 1)) =
      (kmswStage w n).east (act w n) := by
    cases hp : (kmswStage w n).UL.dropLast.reverse <;>
      simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hp,
        State.addEdge]
  simp only [eastStack, hUR, he, old_east_map]

private theorem eastStack_up (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 1) :
    eastStack w (n + 1) = (kmswStage w n).nextVertex :: eastStack w n := by
  have hUR : (kmswStage w (n + 1)).UR =
      ((kmswStage w n).nextEdge + 1) :: (kmswStage w n).UR := by
    simp [kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]
  have he : (kmswStage w (n + 1)).east (act w (n + 1)) =
      (kmswStage w n).nextVertex := by
    simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]
  have hm : (kmswStage w (n + 1)).east ((kmswStage w n).nextEdge + 1) =
      (kmswStage w n).east (act w n) := by
    simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, State.addEdge]
  simp only [eastStack, hUR, he, List.map_cons, hm, old_east_map]

private theorem eastStack_down (w : ℕ → Fin 3) (n e : ℕ) (es : List ℕ)
    (hc : w n = 2) (hUR : (kmswStage w n).UR = e :: es) :
    eastStack w (n + 1) = (eastStack w n).tail := by
  simp [eastStack, act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUR]

private theorem down_west (w : ℕ → Fin 3) (n : ℕ) (hc : w n = 2) :
    (kmswStage w (n + 1)).west (act w (n + 1)) =
      (kmswStage w n).east (act w n) := by
  cases hUR : (kmswStage w n).UR with
  | nil =>
      simp [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUR,
        State.addEdge]
  | cons e es =>
      have hh := (kmswStage_boundary_chain_invariant w n).2.2.2.2.2.1 e es hUR
      simpa [act, kmswStage, kmswStep, kmswCodeStep, hc, kmswStepOfStep, hUR] using hh

private theorem R_step (w : ℕ → Fin 3) (n : ℕ) :
    R w (n + 1) = R w n + (RandomWalk.lazyTwoDimensionalStep (w n)).2 :=
  Finset.sum_range_succ _ _

private theorem L_step (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 :=
  Finset.sum_range_succ _ _

private theorem left_interval_invariant (w : ℕ → Fin 3) (a n : ℕ)
    (han : a ≤ n)
    (habove : ∀ j, a ≤ j → j ≤ n → R w a ≤ R w j)
    (ha : ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w a).west (act w a)⟩) :
    (¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩) ∧
    stageReachableVertices w n = stageReachableVertices w a ∧
    ∀ v ∈ (eastStack w n).take (R w n - R w a).toNat,
      (kmswStage w a).nextVertex ≤ v := by
  induction n, han using Nat.le_induction with
  | base =>
      refine ⟨ha, rfl, ?_⟩
      simp
  | succ n han ih =>
      obtain ⟨hn, hset, hfresh⟩ := ih (fun j haj hjn => habove j haj (by omega))
      have hfreeze := prefix_frozen_step w n hn
      have hsetnext := hfreeze.trans hset
      have hprev := habove n han (by omega)
      have hnext := habove (n + 1) (by omega) le_rfl
      have hstep := R_step w n
      by_cases h0 : w n = 0
      · have hR : R w (n + 1) = R w n := by
          simpa [h0, RandomWalk.lazyTwoDimensionalStep] using hstep
        refine ⟨left_preserves_unreachable w n h0 hn, hsetnext, ?_⟩
        rw [eastStack_left w n h0, hR]
        exact hfresh
      · by_cases h1 : w n = 1
        · have hR : R w (n + 1) = R w n + 1 := by
            simpa [h1, RandomWalk.lazyTwoDimensionalStep] using hstep
          have hidx : (R w (n + 1) - R w a).toNat =
              (R w n - R w a).toNat + 1 := by omega
          refine ⟨up_preserves_unreachable w n h1 hn, hsetnext, ?_⟩
          rw [eastStack_up w n h1, hidx, List.take_succ_cons]
          intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact CutConverse.nextVertex_mono w han
          · exact hfresh v hv
        · have h2 : w n = 2 := by
            apply Fin.ext
            have := (w n).isLt
            have hz : (w n).val ≠ 0 := fun h => h0 (Fin.ext h)
            have ho : (w n).val ≠ 1 := fun h => h1 (Fin.ext h)
            omega
          have hR : R w (n + 1) = R w n - 1 := by
            simpa [h2, RandomWalk.lazyTwoDimensionalStep, sub_eq_add_neg] using hstep
          have hidx : (R w n - R w a).toNat =
              (R w (n + 1) - R w a).toNat + 1 := by omega
          have hhead : (kmswStage w n).east (act w n) ∈
              (eastStack w n).take (R w n - R w a).toNat := by
            rw [hidx]
            simp [eastStack]
          have hbound := hfresh _ hhead
          have hnotMem : (kmswStage w n).east (act w n) ∉
              stageReachableVertices w a := by
            intro hm
            have hb := prefix_lt_nextVertex w a _ hm
            omega
          have hnotNext : ¬ Reachable (⟨0⟩ : PresentVertex w)
              ⟨(kmswStage w (n + 1)).west (act w (n + 1))⟩ := by
            intro hr
            have hm := (activeWest_mem_iff w (n + 1)).2 hr
            rw [hsetnext, down_west w n h2] at hm
            exact hnotMem hm
          refine ⟨hnotNext, hsetnext, ?_⟩
          have hmin := runningMin_le (R w) n a han
          change minR w n ≤ R w a at hmin
          have hlen := kmswStage_UR_length w n
          cases hUR : (kmswStage w n).UR with
          | nil =>
              rw [hUR] at hlen
              simp only [List.length_nil, Nat.cast_zero] at hlen
              omega
          | cons e es =>
              rw [eastStack_down w n e es h2 hUR]
              intro v hv
              apply hfresh v
              rw [hidx]
              simpa only [eastStack, List.tail_cons, List.take_succ_cons,
                List.mem_cons] using Or.inr hv

private theorem coordinate_floor (f : ℕ → ℤ)
    (hstep : ∀ j, f j - 1 ≤ f (j + 1)) (a b n : ℕ)
    (han : a ≤ n) (hnb : n < b)
    (havoid : ∀ j, a < j → j < b → f j ≠ f a - 1) :
    f a ≤ f n := by
  induction n, han using Nat.le_induction with
  | base => exact le_rfl
  | succ n han ih =>
      have hprev := ih (by omega)
      have hs := hstep n
      have hne := havoid (n + 1) (by omega) hnb
      omega

private theorem L_floor (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (a n : ℕ) (han : a ≤ n) (hn : n < firstFlowLHit w h a) :
    L w a ≤ L w n := by
  have hstep : ∀ j, L w j - 1 ≤ L w (j + 1) := by
    intro j
    rw [L_step]
    have hb : (-1 : ℤ) ≤ (RandomWalk.lazyTwoDimensionalStep (w j)).1 := by
      change (-1 : ℤ) ≤ (w j : ℤ) - 1
      omega
    omega
  apply coordinate_floor (L w) hstep a (firstFlowLHit w h a) n han hn
  intro j haj hj he
  change j < Nat.find (h.1 a) at hj
  exact Nat.find_min (h.1 a) hj ⟨by omega, he⟩

private theorem R_floor (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (a n : ℕ) (han : a ≤ n) (hn : n < firstFlowRHit w h a) :
    R w a ≤ R w n := by
  have hstep : ∀ j, R w j - 1 ≤ R w (j + 1) := by
    intro j
    rw [R_step]
    have hb : (-1 : ℤ) ≤ (RandomWalk.lazyTwoDimensionalStep (w j)).2 := by
      change (-1 : ℤ) ≤ if w j = 0 then 0 else if w j = 1 then 1 else -1
      split
      · omega
      · split <;> omega
    omega
  apply coordinate_floor (R w) hstep a (firstFlowRHit w h a) n han hn
  intro j haj hj he
  change j < Nat.find (h.2 a) at hj
  exact Nat.find_min (h.2 a) hj ⟨by omega, he⟩

private theorem walkNL_eq_firstL (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    walkNL w h k = firstFlowLHit w h (walkNR w h k) := by
  cases k <;> rfl

private theorem lPhase_R_floor (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k n : ℕ) (hle : walkNL w h k ≤ n) (hlt : n < walkNR w h (k + 1)) :
    R w (walkNL w h k) ≤ R w n :=
  R_floor w h (walkNL w h k) n hle hlt

/-- A later left entrance returns to the active west vertex immediately before
its preceding right entrance. This is the horizontal excursion used in the
induction in `lem-flow-line-times` -/
theorem walkNL_succ_activeWest_eq_previous_walkNR (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    (kmswStage w (walkNL w h (k + 1))).west (act w (walkNL w h (k + 1))) =
      (kmswStage w (walkNR w h (k + 1) - 1)).west
        (act w (walkNR w h (k + 1) - 1)) := by
  let r := walkNR w h (k + 1)
  let a := r - 1
  let b := walkNL w h (k + 1)
  have hRspec := walkNR_succ_spec w h k
  have hLspec := walkNL_spec w h (k + 1)
  have hapos : a + 1 = r := by dsimp [a, r]; omega
  have hab : a ≤ b := by dsimp [a, b, r]; omega
  have hdelta := congrArg Prod.fst (walkNR_succ_previous_step w h k)
  change L w r - L w a = 1 at hdelta
  have hLlevel : L w b = L w r - 1 := hLspec.2
  have hlev : L w a = L w b := by omega
  have habove : ∀ j, a ≤ j → j ≤ b → L w a ≤ L w j := by
    intro j haj hjb
    by_cases hja : j = a
    · rw [hja]
    · by_cases hjbEq : j = b
      · rw [hjbEq, hlev]
      · have hrj : r ≤ j := by omega
        have hjhit : j < firstFlowLHit w h r := by
          rw [← walkNL_eq_firstL w h (k + 1)]
          change j < b
          omega
        have hjfloor := L_floor w h r j hrj hjhit
        omega
  have heq := kmsw_west_act_eq_of_level w hab hlev habove
  have hstable := (kmswStage_endpoints_stable w hab
    (act_lt_nextEdge w (le_rfl : a ≤ a))).1
  exact heq.symm.trans hstable

/-- At every left-phase entrance the active west vertex is unreachable from
the root (`lem-flow-line-times`, -/
theorem walkNL_activeWest_unreachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k : ℕ) :
    ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w (walkNL w h k)).west (act w (walkNL w h k))⟩ := by
  induction k with
  | zero => exact quadrantFirstR_exit_activeWest_unreachable w h
  | succ k ih =>
      rw [walkNL_succ_activeWest_eq_previous_walkNR w h k]
      have hspec := walkNR_succ_spec w h k
      have hle : walkNL w h k ≤ walkNR w h (k + 1) - 1 := by omega
      apply (left_interval_invariant w (walkNL w h k)
        (walkNR w h (k + 1) - 1) hle ?_ ih).1
      intro j haj hjn
      exact lPhase_R_floor w h k j haj (by omega)

/-- Throughout a left phase, including its entrance and excluding the next
right entrance, the active west vertex is unreachable from the root -/
theorem lPhase_activeWest_unreachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ)
    (hle : walkNL w h k ≤ n) (hlt : n < walkNR w h (k + 1)) :
    ¬ Reachable (⟨0⟩ : PresentVertex w)
      ⟨(kmswStage w n).west (act w n)⟩ := by
  apply (left_interval_invariant w (walkNL w h k) n hle ?_
    (walkNL_activeWest_unreachable w h k)).1
  intro j haj hjn
  exact lPhase_R_floor w h k j haj (by omega)

/-- The strict activation-prefix reachable set is constant throughout each
left phase (`lem-flow-line-times`, -/
theorem lPhase_actReachableBefore_eq (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ)
    (hle : walkNL w h k ≤ n) (hlt : n < walkNR w h (k + 1)) :
    actReachableBefore w n = actReachableBefore w (walkNL w h k) := by
  have hf := (left_interval_invariant w (walkNL w h k) n hle
    (fun j haj hjn => lPhase_R_floor w h k j haj (by omega))
    (walkNL_activeWest_unreachable w h k)).2.1
  ext v
  rw [← mem_stageReachableVertices_iff w n v,
    ← mem_stageReachableVertices_iff w (walkNL w h k) v, hf]

/-- Almost surely, the active west vertex is unreachable simultaneously at
every time in every left phase (`lem-flow-line-times`, -/
theorem iidCodes_ae_lPhase_activeWest_unreachable :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : HasFlowLineHits (fun i => ω (i + 1)),
        ∀ k n, walkNL (fun i => ω (i + 1)) h k ≤ n →
          n < walkNR (fun i => ω (i + 1)) h (k + 1) →
          ¬ Reachable (⟨0⟩ : PresentVertex (fun i => ω (i + 1)))
            ⟨(kmswStage (fun i => ω (i + 1)) n).west
              (act (fun i => ω (i + 1)) n)⟩ := by
  filter_upwards [ae_hasFlowLineHits] with ω hω
  exact ⟨hω, fun k n hle hlt => lPhase_activeWest_unreachable _ hω k n hle hlt⟩

private def lPhaseSampleCode (n : ℕ) : Fin 3 :=
  if n = 0 then 0 else if n = 1 then 1 else 2

-- The active east endpoint returns to the old reachable endpoint at level zero.
-- Only the prefix above the starting R-level consists of fresh vertices.
private theorem lPhaseSample_eastStack_values :
    eastStack lPhaseSampleCode 1 = [1] ∧
      eastStack lPhaseSampleCode 2 = [3, 1] ∧
      eastStack lPhaseSampleCode 3 = [1] := by decide

private theorem lPhaseSample_east_reachable_at_start :
    (kmswStage lPhaseSampleCode 1).east (act lPhaseSampleCode 1) ∈
      stageReachableVertices lPhaseSampleCode 1 := by decide

end DirectedDistances.KMSW
