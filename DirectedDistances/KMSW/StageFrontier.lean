module

public import DirectedDistances.KMSW.DirectedContain
public import DirectedDistances.KMSW.StageIncidenceChains
public import DirectedDistances.KMSW.OutgoingInterval
import DirectedDistances.KMSW.WalkRecordCounts

/-! # Finite-stage upper-frontier persistence

Combinatorial helpers toward the path-containment part of -/

public section
namespace DirectedDistances.KMSW

open Quiver

/-- A vertex is on the initial upper frontier or was allocated after its
upper-frontier updates are the cases of `def-kmsw`, -/
@[expose] def UpperFrontierEndpoint (s : State) (v : ℕ) : Prop :=
  (∃ e, e ∈ s.UL ++ s.UR ∧ (s.west e = v ∨ s.east e = v)) ∨
    s.nextVertex ≤ v

private theorem kmswStep_old_endpoints (s : State) (c : Fin 3) {e : ℕ}
    (he : e < s.nextEdge) :
    (kmswStep s c).west e = s.west e ∧
      (kmswStep s c).east e = s.east e := by
  have h0 : e ≠ s.nextEdge := by omega
  have h1 : e ≠ s.nextEdge + 1 := by omega
  unfold kmswStep
  cases kmswCodeStep c with
  | down => cases hu : s.UR <;> simp [kmswStepOfStep, hu, State.addEdge, h0]
  | left => cases hu : s.UL.dropLast.reverse <;>
      simp [kmswStepOfStep, hu, State.addEdge, h0, h1]
  | up => simp [kmswStepOfStep, State.addEdge, h0, h1]

/-- One KMSW step preserves the initial-frontier-or-fresh endpoint -/
private theorem upperFrontierEndpoint_step (s₀ s : State)
    (hbound : ∀ e ∈ s.UL ++ s.UR,
      UpperFrontierEndpoint s₀ (s.west e) ∧
        UpperFrontierEndpoint s₀ (s.east e))
    (hfresh : s₀.nextVertex ≤ s.nextVertex)
    (hactive : s.active ∈ s.UL)
    (hids : ∀ e ∈ s.UL ++ s.UR, e < s.nextEdge)
    (c : Fin 3) :
    ∀ e ∈ (kmswStep s c).UL ++ (kmswStep s c).UR,
      UpperFrontierEndpoint s₀ ((kmswStep s c).west e) ∧
        UpperFrontierEndpoint s₀ ((kmswStep s c).east e) := by
  intro e he
  have hold (f : ℕ) (hf : f ∈ s.UL ++ s.UR) :
      UpperFrontierEndpoint s₀ ((kmswStep s c).west f) ∧
        UpperFrontierEndpoint s₀ ((kmswStep s c).east f) := by
    have heold := kmswStep_old_endpoints s c (hids f hf)
    rw [heold.1, heold.2]
    exact hbound f hf
  have hactiveBound := hbound s.active (List.mem_append_left _ hactive)
  cases hc : kmswCodeStep c with
  | down =>
    cases hu : s.UR with
    | nil =>
      have hmem : e ∈ s.UL ++ [s.nextEdge] := by
        simpa [kmswStep, hc, kmswStepOfStep, hu, State.addEdge] using he
      rcases List.mem_append.mp hmem with holdMem | hnew
      · exact hold e (List.mem_append_left _ holdMem)
      · have heq : e = s.nextEdge := List.mem_singleton.mp hnew
        subst e
        constructor
        · simpa [kmswStep, hc, kmswStepOfStep, hu, State.addEdge] using
            hactiveBound.2
        · right
          simpa [kmswStep, hc, kmswStepOfStep, hu, State.addEdge] using hfresh
    | cons f fs =>
      have hmem : e ∈ s.UL ++ s.UR := by
        simpa [kmswStep, hc, kmswStepOfStep, hu, List.append_assoc] using he
      exact hold e hmem
  | left =>
    cases hu : s.UL.dropLast.reverse with
    | nil =>
      have hmem : e ∈ [s.nextEdge] ++ s.UR := by
        simpa [kmswStep, hc, kmswStepOfStep, hu, State.addEdge] using he
      rcases List.mem_append.mp hmem with hnew | holdMem
      · have heq : e = s.nextEdge := List.mem_singleton.mp hnew
        subst e
        constructor
        · right
          simpa [kmswStep, hc, kmswStepOfStep, hu, State.addEdge] using hfresh
        · simpa [kmswStep, hc, kmswStepOfStep, hu, State.addEdge] using
            hactiveBound.2
      · exact hold e (List.mem_append_right _ holdMem)
    | cons f fs =>
      have hmem : e ∈ fs.reverse ++ [s.nextEdge] ++ s.UR := by
        simpa [kmswStep, hc, kmswStepOfStep, hu, State.addEdge,
          List.append_assoc] using he
      rcases List.mem_append.mp hmem with hleft | hright
      · rcases List.mem_append.mp hleft with hrest | hnew
        · have hrestUL : e ∈ s.UL := by
            apply List.dropLast_subset
            have hrev : e ∈ s.UL.dropLast.reverse := by
              rw [hu]
              exact List.mem_cons_of_mem _ (List.mem_reverse.mp hrest)
            exact List.mem_reverse.mp hrev
          exact hold e (List.mem_append_left _ hrestUL)
        · have heq : e = s.nextEdge := List.mem_singleton.mp hnew
          subst e
          have hfUL : f ∈ s.UL := by
            apply List.dropLast_subset
            exact List.mem_reverse.mp (by rw [hu]; exact List.mem_cons_self)
          have hfBound := hbound f (List.mem_append_left _ hfUL)
          constructor
          · simpa [kmswStep, hc, kmswStepOfStep, hu, State.addEdge] using
              hfBound.1
          · simpa [kmswStep, hc, kmswStepOfStep, hu, State.addEdge] using
              hactiveBound.2
      · exact hold e (List.mem_append_right _ hright)
  | up =>
    have hmem : e ∈ (s.UL.dropLast ++ [s.nextEdge]) ++
        ((s.nextEdge + 1) :: s.UR) := by
      simpa [kmswStep, hc, kmswStepOfStep, State.addEdge,
        List.append_assoc] using he
    rcases List.mem_append.mp hmem with hupper | hright
    · rcases List.mem_append.mp hupper with hrest | hnew
      · exact hold e (List.mem_append_left _ (List.dropLast_subset _ hrest))
      · have heq : e = s.nextEdge := List.mem_singleton.mp hnew
        subst e
        constructor
        · simpa [kmswStep, hc, kmswStepOfStep, State.addEdge] using
            hactiveBound.1
        · right
          simpa [kmswStep, hc, kmswStepOfStep, State.addEdge] using hfresh
    · rcases List.mem_cons.mp hright with hnew | holdMem
      · have heq : e = s.nextEdge + 1 := hnew
        subst e
        constructor
        · right
          simpa [kmswStep, hc, kmswStepOfStep, State.addEdge] using hfresh
        · simpa [kmswStep, hc, kmswStepOfStep, State.addEdge] using
            hactiveBound.2
      · exact hold e (List.mem_append_right _ holdMem)

/-- At every later stage, endpoints of every `UL` or `UR` edge come either
from the stage's original upper frontier or from a vertex allocated since -/
theorem kmswStage_upperFrontier_endpoints (w : ℕ → Fin 3) :
    ∀ t m, t ≤ m → ∀ e ∈ (kmswStage w m).UL ++ (kmswStage w m).UR,
      UpperFrontierEndpoint (kmswStage w t) ((kmswStage w m).west e) ∧
        UpperFrontierEndpoint (kmswStage w t) ((kmswStage w m).east e) := by
  intro t m
  induction m generalizing t with
  | zero =>
    intro htm e he
    have ht : t = 0 := by omega
    subst t
    exact ⟨Or.inl ⟨e, he, Or.inl rfl⟩, Or.inl ⟨e, he, Or.inr rfl⟩⟩
  | succ m ih =>
    intro htm
    by_cases htm' : t ≤ m
    · have hprev := ih t htm'
      have hactive : (kmswStage w m).active ∈ (kmswStage w m).UL := by
        obtain ⟨xs, hxs⟩ := kmswStage_UL_last w m
        rw [hxs]
        simp
      have hids : ∀ e ∈ (kmswStage w m).UL ++ (kmswStage w m).UR,
          e < (kmswStage w m).nextEdge := by
        intro e he
        apply (kmswStage_boundary_ids_lt_nextEdge w m).2
        simp only [List.mem_append] at he ⊢
        tauto
      have hfresh := CutConverse.nextVertex_mono w htm'
      simpa only [kmswStage] using
        (upperFrontierEndpoint_step (kmswStage w t) (kmswStage w m)
          hprev hfresh hactive hids (w m))
    · have ht : t = m + 1 := by omega
      subst t
      intro e he
      exact ⟨Or.inl ⟨e, he, Or.inl rfl⟩, Or.inl ⟨e, he, Or.inr rfl⟩⟩

/-- The active edge created or activated by any step in `[t,m)` has both
endpoints in the original upper frontier or among vertices allocated since -/
theorem kmswStage_act_endpoint_since (w : ℕ → Fin 3) {t m n : ℕ}
    (htn : t ≤ n) (_hnm : n < m) :
    UpperFrontierEndpoint (kmswStage w t)
        ((kmswStage w n).west (act w n)) ∧
      UpperFrontierEndpoint (kmswStage w t)
        ((kmswStage w n).east (act w n)) := by
  have hactive : act w n ∈ (kmswStage w n).UL := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
    rw [hxs]
    simp [act]
  exact kmswStage_upperFrontier_endpoints w t n htn (act w n)
    (List.mem_append_left _ hactive)

/-- One code step changes either coordinate by at most one, as used to read
the first hit as a strict record (`lem-directed-contain`, -/
private theorem rightCoordinate_step_abs (w : ℕ → Fin 3) (n : ℕ) :
    |R w (n + 1) - R w n| ≤ 1 := by
  have hsum : R w (n + 1) = R w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).2 := Finset.sum_range_succ _ _
  rw [hsum]
  have hstep : |(RandomWalk.lazyTwoDimensionalStep (w n)).2| ≤ 1 := by
    have hc : w n = 0 ∨ w n = 1 ∨ w n = 2 := by
      have := (w n).isLt
      omega
    rcases hc with h0 | h1 | h2
    · rw [h0]
      norm_num [RandomWalk.lazyTwoDimensionalStep]
    · rw [h1]
      norm_num [RandomWalk.lazyTwoDimensionalStep]
    · rw [h2]
      norm_num [RandomWalk.lazyTwoDimensionalStep]
  simpa only [add_sub_cancel_left] using hstep

/-- The first right-coordinate hit is a strict running minimum -/
private theorem boundaryHitTime_right_strict_record (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    ∀ j < boundaryHitTime w h k,
      R w (boundaryHitTime w h k) < R w j := by
  let τ := boundaryHitTime w h k
  have hfind : τ = Nat.find (h.rightHit k hk) := by
    dsimp [τ, boundaryHitTime]
    simp only [dif_neg (by omega : k ≠ 0), dif_pos (by omega : 0 < k)]
  have hzero : R w 0 = 0 := by simp [R]
  have hchar := (strict_running_minimum_iff_first_hit (R w) hzero
    (rightCoordinate_step_abs w) τ τ (-k) (by omega) (h.rightHit k hk)).2
      ⟨le_rfl, boundaryHitTime_right_spec w h hk, hfind⟩
  intro j hj
  exact (Finset.mem_filter.mp hchar.1).2 j hj

/-- At the first hit of a negative right-coordinate level, the stage's UR
list is empty (`eqn-bdy-vertex-kmsw`, `lem-directed-contain`, -/
theorem boundaryHit_right_UR_empty (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    (kmswStage w (boundaryHitTime w h k)).UR = [] := by
  let τ := boundaryHitTime w h k
  have hstrict := boundaryHitTime_right_strict_record w h hk
  have hmin : minR w τ = R w τ := by
    obtain ⟨i, hi, heq⟩ := runningMin_attained (R w) τ
    have hle := runningMin_le (R w) τ τ le_rfl
    change minR w τ ≤ R w τ at hle
    change minR w τ = R w i at heq
    by_cases hiτ : i = τ
    · simpa [hiτ] using heq
    · have hrec := hstrict i (by omega)
      change R w τ < R w i at hrec
      rw [← heq] at hrec
      omega
  have hlen := kmswStage_UR_length w τ
  have hzero : ((kmswStage w τ).UR.length : ℤ) = 0 := by
    rw [hlen, hmin]
    ring
  have hlen0 : (kmswStage w τ).UR.length = 0 := by exact_mod_cast hzero
  exact List.length_eq_zero_iff.mp hlen0

/-- At a strict new right minimum, the immediately preceding active edge
ends at the hit vertex and the hit edge ends at the newly allocated vertex
(`def-kmsw`, `lem-directed-contain`, -/
private theorem rightHit_previousStage (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    ∃ r, boundaryHitTime w h k = r + 1 ∧
      (kmswStage w r).UR = [] ∧
      boundaryVertex w h k = (kmswStage w r).east (act w r) ∧
      (kmswStage w (r + 1)).east (act w (r + 1)) =
        (kmswStage w r).nextVertex := by
  let τ := boundaryHitTime w h k
  have hτpos : 0 < τ := by
    by_contra hnot
    have hτ0 : τ = 0 := by omega
    have hspec := boundaryHitTime_right_spec w h hk
    change R w τ = -k at hspec
    rw [hτ0] at hspec
    simp [R] at hspec
    omega
  have hstrict := boundaryHitTime_right_strict_record w h hk
  let r := τ - 1
  have hτ : τ = r + 1 := by dsimp [r]; omega
  have hrplus : R w τ = R w r - 1 := by
    have hsum : R w (r + 1) = R w r +
        (RandomWalk.lazyTwoDimensionalStep (w r)).2 := Finset.sum_range_succ _ _
    have hdown : -1 ≤ (RandomWalk.lazyTwoDimensionalStep (w r)).2 ∧
        (RandomWalk.lazyTwoDimensionalStep (w r)).2 ≤ 1 := by
      have hstep : |(RandomWalk.lazyTwoDimensionalStep (w r)).2| ≤ 1 := by
          have hc : w r = 0 ∨ w r = 1 ∨ w r = 2 := by
            have := (w r).isLt
            omega
          rcases hc with h0 | h1 | h2
          · rw [h0]
            norm_num [RandomWalk.lazyTwoDimensionalStep]
          · rw [h1]
            norm_num [RandomWalk.lazyTwoDimensionalStep]
          · rw [h2]
            norm_num [RandomWalk.lazyTwoDimensionalStep]
      exact abs_le.mp hstep
    rw [← hτ] at hsum
    have hrec := hstrict r (by omega)
    rw [hsum] at hrec
    omega
  have hminr : minR w r = R w r := by
    obtain ⟨i, hi, heq⟩ := runningMin_attained (R w) r
    have hle := runningMin_le (R w) r r le_rfl
    change minR w r ≤ R w r at hle
    change minR w r = R w i at heq
    have hri : R w r ≤ R w i := by
      by_cases hir : i = r
      · subst i
        exact le_rfl
      · have hirτ : i < τ := by omega
        have hrec := hstrict i hirτ
        change R w τ < R w i at hrec
        rw [hrplus] at hrec
        omega
    omega
  have hlen := kmswStage_UR_length w r
  have hzero : ((kmswStage w r).UR.length : ℤ) = 0 := by
    rw [hlen, hminr]
    ring
  have hURlen : (kmswStage w r).UR.length = 0 := by exact_mod_cast hzero
  have hUR : (kmswStage w r).UR = [] := List.length_eq_zero_iff.mp hURlen
  have hstepY : (RandomWalk.lazyTwoDimensionalStep (w r)).2 = -1 := by
    have hsum : R w (r + 1) = R w r +
        (RandomWalk.lazyTwoDimensionalStep (w r)).2 := Finset.sum_range_succ _ _
    rw [← hτ, hrplus] at hsum
    omega
  have hw : w r = 2 := by
    have hc : w r = 0 ∨ w r = 1 ∨ w r = 2 := by
      have := (w r).isLt
      omega
    rcases hc with h0 | h1 | h2
    · rw [h0] at hstepY
      norm_num [RandomWalk.lazyTwoDimensionalStep] at hstepY
    · rw [h1] at hstepY
      norm_num [RandomWalk.lazyTwoDimensionalStep] at hstepY
    · exact h2
  have hstage : kmswStage w τ = kmswStepOfStep (kmswStage w r) .down := by
    rw [hτ]
    change kmswStep (kmswStage w r) (w r) = _
    rw [hw]
    simp [kmswStep, kmswCodeStep, kmswStepOfStep, hUR]
  have hact : act w τ = (kmswStage w r).nextEdge := by
    change (kmswStage w τ).active = _
    rw [hstage]
    simp [kmswStepOfStep, hUR, State.addEdge]
  have hvertex : boundaryVertex w h k = (kmswStage w r).east (act w r) := by
    calc
      boundaryVertex w h k = activeInitial w τ := by
        simpa [τ] using boundaryVertex_right_hit_eq w h hk
      _ = (kmswStage w τ).west (act w τ) := CutConverse.activeInitial_eq w τ
      _ = (kmswStage w r).east (act w r) := by
        rw [hstage, hact]
        simp [kmswStepOfStep, hUR, State.addEdge, act]
  have heast : (kmswStage w (r + 1)).east (act w (r + 1)) =
      (kmswStage w r).nextVertex := by
    rw [← hτ, hstage]
    rw [hact]
    simp [kmswStepOfStep, hUR, State.addEdge]
  exact ⟨r, hτ, hUR, hvertex, heast⟩

/-- One code step changes either coordinate by at most one, as used to read
the first hit as a strict record (`lem-directed-contain`, -/
private theorem leftCoordinate_step_abs (w : ℕ → Fin 3) (n : ℕ) :
    |L w (n + 1) - L w n| ≤ 1 := by
  have hsum : L w (n + 1) = L w n +
      (RandomWalk.lazyTwoDimensionalStep (w n)).1 := Finset.sum_range_succ _ _
  rw [hsum]
  have hstep : |(RandomWalk.lazyTwoDimensionalStep (w n)).1| ≤ 1 := by
    have hc : w n = 0 ∨ w n = 1 ∨ w n = 2 := by
      have := (w n).isLt
      omega
    rcases hc with h0 | h1 | h2
    · rw [h0]
      norm_num [RandomWalk.lazyTwoDimensionalStep]
    · rw [h1]
      norm_num [RandomWalk.lazyTwoDimensionalStep]
    · rw [h2]
      norm_num [RandomWalk.lazyTwoDimensionalStep]
  simpa only [add_sub_cancel_left] using hstep

/-- The first left-coordinate hit is a strict running minimum -/
private theorem boundaryHitTime_left_strict_record (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ j < boundaryHitTime w h k,
      L w (boundaryHitTime w h k) < L w j := by
  let τ := boundaryHitTime w h k
  have hfind : τ = Nat.find (h.leftHit k hk) := by
    dsimp [τ, boundaryHitTime]
    simp only [dif_neg (by omega : k ≠ 0), dif_neg (by omega : ¬ 0 < k)]
  have hzero : L w 0 = 0 := by simp [L]
  have hchar := (strict_running_minimum_iff_first_hit (L w) hzero
    (leftCoordinate_step_abs w) τ τ k (by omega) (h.leftHit k hk)).2
      ⟨le_rfl, boundaryHitTime_left_spec w h hk, hfind⟩
  intro j hj
  exact (Finset.mem_filter.mp hchar.1).2 j hj

/-- A first left-coordinate hit is made by a fresh left step; its initial
vertex is the newly allocated vertex (`eqn-bdy-vertex-kmsw`, -/
private theorem leftHit_previousStage (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∃ r, boundaryHitTime w h k = r + 1 ∧
      w r = 0 ∧
      (kmswStage w r).UL = [(kmswStage w r).active] ∧
      boundaryVertex w h k = (kmswStage w r).nextVertex ∧
      (kmswStage w (r + 1)).west (act w (r + 1)) =
        (kmswStage w r).nextVertex ∧
      (kmswStage w (r + 1)).nextVertex = (kmswStage w r).nextVertex + 1 ∧
      (kmswStage w (r + 1)).UL = [act w (r + 1)] := by
  let τ := boundaryHitTime w h k
  have hτpos : 0 < τ := by
    by_contra hnot
    have hτ0 : τ = 0 := by omega
    have hspec := boundaryHitTime_left_spec w h hk
    change L w τ = k at hspec
    rw [hτ0] at hspec
    simp [L] at hspec
    omega
  have hstrict := boundaryHitTime_left_strict_record w h hk
  let r := τ - 1
  have hτ : τ = r + 1 := by dsimp [r]; omega
  have hlplus : L w τ = L w r - 1 := by
    have hsum : L w (r + 1) = L w r +
        (RandomWalk.lazyTwoDimensionalStep (w r)).1 := Finset.sum_range_succ _ _
    have hstep : |(RandomWalk.lazyTwoDimensionalStep (w r)).1| ≤ 1 := by
      have hc : w r = 0 ∨ w r = 1 ∨ w r = 2 := by
        have := (w r).isLt
        omega
      rcases hc with h0 | h1 | h2
      · rw [h0]
        norm_num [RandomWalk.lazyTwoDimensionalStep]
      · rw [h1]
        norm_num [RandomWalk.lazyTwoDimensionalStep]
      · rw [h2]
        norm_num [RandomWalk.lazyTwoDimensionalStep]
    rw [← hτ] at hsum
    have hrec := hstrict r (by omega)
    rw [hsum] at hrec
    have hstep' := abs_le.mp hstep
    omega
  have hminr : minL w r = L w r := by
    obtain ⟨i, hi, heq⟩ := runningMin_attained (L w) r
    have hle := runningMin_le (L w) r r le_rfl
    change minL w r ≤ L w r at hle
    change minL w r = L w i at heq
    have hri : L w r ≤ L w i := by
      by_cases hir : i = r
      · subst i
        exact le_rfl
      · have hirτ : i < τ := by omega
        have hrec := hstrict i hirτ
        change L w τ < L w i at hrec
        rw [hlplus] at hrec
        omega
    omega
  have hlen := kmswStage_UL_length w r
  have hone : ((kmswStage w r).UL.length : ℤ) = 1 := by
    rw [hlen, hminr]
    ring
  have hlenNat : (kmswStage w r).UL.length = 1 := by exact_mod_cast hone
  obtain ⟨xs, hULlast⟩ := kmswStage_UL_last w r
  have hxslen : xs.length + 1 = 1 := by
    rw [hULlast] at hlenNat
    simpa using hlenNat
  have hxs : xs = [] := List.length_eq_zero_iff.mp (by omega)
  have hULr : (kmswStage w r).UL = [(kmswStage w r).active] := by
    rw [hULlast, hxs]
    rfl
  have hdrop : (kmswStage w r).UL.dropLast.reverse = [] := by
    rw [hULr]
    rfl
  have hstepX : (RandomWalk.lazyTwoDimensionalStep (w r)).1 = -1 := by
    have hsum : L w (r + 1) = L w r +
        (RandomWalk.lazyTwoDimensionalStep (w r)).1 := Finset.sum_range_succ _ _
    rw [← hτ, hlplus] at hsum
    omega
  have hw : w r = 0 := by
    have hc : w r = 0 ∨ w r = 1 ∨ w r = 2 := by
      have := (w r).isLt
      omega
    rcases hc with h0 | h1 | h2
    · exact h0
    · rw [h1] at hstepX
      norm_num [RandomWalk.lazyTwoDimensionalStep] at hstepX
    · rw [h2] at hstepX
      norm_num [RandomWalk.lazyTwoDimensionalStep] at hstepX
  have hstage : kmswStage w τ = kmswStepOfStep (kmswStage w r) .left := by
    rw [hτ]
    change kmswStep (kmswStage w r) (w r) = _
    rw [hw]
    simp [kmswStep, kmswCodeStep, kmswStepOfStep, hdrop]
  have hact : act w τ = (kmswStage w r).nextEdge := by
    change (kmswStage w τ).active = _
    rw [hstage]
    simp [kmswStepOfStep, hdrop, State.addEdge]
  have hvertex : boundaryVertex w h k = (kmswStage w r).nextVertex := by
    calc
      boundaryVertex w h k = activeInitial w τ := by
        simpa [τ] using boundaryVertex_left_hit_eq w h hk
      _ = (kmswStage w τ).west (act w τ) := CutConverse.activeInitial_eq w τ
      _ = (kmswStage w r).nextVertex := by
        rw [hstage, hact]
        simp [kmswStepOfStep, hdrop, State.addEdge]
  have hwest : (kmswStage w τ).west (act w τ) =
      (kmswStage w r).nextVertex := by
    rw [hstage, hact]
    simp [kmswStepOfStep, hdrop, State.addEdge]
  have hnextVertex : (kmswStage w τ).nextVertex =
      (kmswStage w r).nextVertex + 1 := by
    rw [hstage]
    simp [kmswStepOfStep, hdrop, State.addEdge]
  have hULτ : (kmswStage w τ).UL = [act w τ] := by
    rw [hstage, hact]
    simp [kmswStepOfStep, hdrop, State.addEdge]
  exact ⟨r, hτ, hw, hULr, hvertex, by simpa [τ, hτ] using hwest,
    by simpa [τ, hτ] using hnextVertex, by simpa [τ, hτ] using hULτ⟩



private theorem UR_endpoint_mem_pending (s : State)
    (hcoh : CutConverse.FrontierCoherent s) {e : ℕ}
    (he : e ∈ s.UR) :
    s.west e ∈ CutConverse.pendingVertices s ∧
      s.east e ∈ CutConverse.pendingVertices s := by
  have hwest : s.west e ∈ s.UR.map s.west :=
    List.mem_map.mpr ⟨e, he, rfl⟩
  rw [hcoh] at hwest
  constructor
  · exact List.dropLast_subset _ hwest
  · change s.east e ∈ s.east s.active :: s.UR.map s.east
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e, he, rfl⟩)

/-- At a first left-coordinate hit, every old upper-frontier endpoint is
either the fresh source itself or has no outgoing edge at that stage -/
private theorem leftHit_frontier_endpoint_pending_or_source (s : State)
    (hUL : s.UL = [s.active])
    (hcoh : CutConverse.FrontierCoherent s) (v : ℕ)
    (hv : UpperFrontierEndpoint s v) (hvlt : v < s.nextVertex) :
    v = s.west s.active ∨ v ∈ CutConverse.pendingVertices s := by
  rcases hv with ⟨e, he, hend⟩ | hfresh
  · rcases List.mem_append.mp he with heUL | heUR
    · have heq : e = s.active := by
        simpa [hUL] using heUL
      subst e
      rcases hend with hwest | heast
      · exact Or.inl hwest.symm
      · right
        rw [← heast]
        simp [CutConverse.pendingVertices]
    · have hends := UR_endpoint_mem_pending s hcoh heUR
      rcases hend with hwest | heast
      · exact Or.inr (hwest ▸ hends.1)
      · exact Or.inr (heast ▸ hends.2)
  · omega

/-- The stage rank of an already allocated vertex is unchanged at later stages -/
private theorem stageRank_stable_oldVertex (w : ℕ → Fin 3)
    {t m v : ℕ} (htm : t ≤ m)
    (hv : v < (kmswStage w t).nextVertex) :
    kmswStageRank w m v = kmswStageRank w t v := by
  induction m, htm using Nat.le_induction with
  | base => rfl
  | @succ m htm ih =>
    have hbound : v < (kmswStage w m).nextVertex := by
      exact hv.trans_le (CutConverse.nextVertex_mono w htm)
    have hne : v ≠ (kmswStage w m).nextVertex := by omega
    change (if v = (kmswStage w m).nextVertex then _ else
      kmswStageRank w m v) = kmswStageRank w t v
    rw [if_neg hne]
    exact ih

/-- Strict edge ranks along a chain order every prefix endpoint before its
terminal vertex (`lem-directed-contain`, -/
private theorem upperPrefix_rank_east (s : State) (ρ : ℕ → ℚ)
    (xs : List ℕ) (f : ℕ)
    (hc : List.IsChain (fun e g => s.east e = s.west g) (xs ++ [f]))
    (hstrict : ∀ e ∈ xs ++ [f],
      ρ (s.west e) < ρ (s.east e)) :
    ∀ e ∈ xs,
      ρ (s.east e) < ρ (s.west f) ∨
        s.east e = s.west f := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    intro e he
    rcases List.mem_cons.mp he with hea | heas
    · subst e
      cases as with
      | nil =>
        have hrel' : s.east a = s.west f := by
          simpa using (hc.rel_head? (by simp))
        exact Or.inr hrel'
      | cons b bs =>
        have hrel' : s.east a = s.west b := by
          simpa using (hc.rel_head? (by simp))
        have htail : List.IsChain (fun e g => s.east e = s.west g)
            ((b :: bs) ++ [f]) := hc.tail
        have hstrictTail : ∀ e ∈ (b :: bs) ++ [f],
            ρ (s.west e) < ρ (s.east e) := by
          intro e he
          exact hstrict e (List.mem_cons_of_mem a he)
        have hb := ih htail hstrictTail b (by simp)
        have hstrictB := hstrict b (List.mem_cons_of_mem a List.mem_cons_self)
        have hlt : ρ (s.west b) < ρ (s.west f) := by
          rcases hb with hbe | heq
          · exact hstrictB.trans hbe
          · rw [← heq]
            exact hstrictB
        exact Or.inl (by rw [hrel']; exact hlt)
    · cases as with
      | nil => simp at heas
      | cons b bs =>
        have htail : List.IsChain (fun e g => s.east e = s.west g)
            ((b :: bs) ++ [f]) := hc.tail
        have hstrictTail : ∀ e ∈ (b :: bs) ++ [f],
            ρ (s.west e) < ρ (s.east e) := by
          intro e he
          exact hstrict e (List.mem_cons_of_mem a he)
        exact ih htail hstrictTail e (by simpa using heas)

/-- Endpoints on the stage's upper-left chain lie strictly west in stage rank,
except for the active edge's two endpoints (`def-kmsw`, -/
private theorem upperLeft_endpoint_rankClass (w : ℕ → Fin 3) (n : ℕ)
    (hUR : (kmswStage w n).UR = []) :
    ∀ v, (∃ e, e ∈ (kmswStage w n).UL ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)) →
      v = (kmswStage w n).west (act w n) ∨
        kmswStageRank w n v <
          kmswStageRank w n ((kmswStage w n).west (act w n)) ∨
        v = (kmswStage w n).east (act w n) := by
  intro v hv
  obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
  obtain ⟨e, he, hv⟩ := hv
  have hchain : List.IsChain (fun e f =>
      (kmswStage w n).east e = (kmswStage w n).west f)
      (xs ++ [act w n]) := by
    have hu := (kmswStage_boundary_chain_invariant w n).1
    change List.IsChain (fun e f =>
      (kmswStage w n).east e = (kmswStage w n).west f)
      ((kmswStage w n).UL ++ (kmswStage w n).UR) at hu
    rw [hUR, List.append_nil, hUL] at hu
    simpa [act] using hu
  have hstrict : ∀ e ∈ xs ++ [act w n],
      kmswStageRank w n ((kmswStage w n).west e) <
        kmswStageRank w n ((kmswStage w n).east e) := by
    intro e he
    have heUL : e ∈ (kmswStage w n).UL := by rw [hUL]; exact he
    have heid := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl heUL)))
    exact kmswStageRank_strict w n e heid
  have hprefix : ∀ e ∈ xs,
      kmswStageRank w n ((kmswStage w n).east e) <
          kmswStageRank w n ((kmswStage w n).west (act w n)) ∨
        (kmswStage w n).east e = (kmswStage w n).west (act w n) := by
    simpa only [act] using upperPrefix_rank_east (kmswStage w n)
      (kmswStageRank w n) xs (act w n) hchain (by
        intro e he
        simpa only [act] using hstrict e he)
  rw [hUL] at he
  rcases List.mem_append.mp he with hexs | hlast
  · rcases hv with hvw | hve
    · have hwest := hstrict e (List.mem_append_left _ hexs)
      have heast := hprefix e hexs
      rcases heast with heast | heast
      · exact Or.inr (Or.inl (by rw [← hvw]; exact hwest.trans heast))
      · have hwest' := hwest
        rw [heast] at hwest'
        exact Or.inr (Or.inl (by rw [← hvw]; exact hwest'))
    · rcases hprefix e hexs with heast | heast
      · exact Or.inr (Or.inl (by rw [← hve]; exact heast))
      · exact Or.inl (by rw [← hve]; exact heast)
  · have heq : e = act w n := List.mem_singleton.mp hlast
    subst e
    rcases hv with hvw | hve
    · exact Or.inl hvw.symm
    · exact Or.inr (Or.inr hve.symm)

/-- A finite present-edge path strictly increases the common stage rank
once all its edges are allocated (`lem-directed-contain`, -/
private theorem presentPath_rank_eventually {w : ℕ → Fin 3}
    {u v : PresentVertex w} (p : Path u v) :
    ∃ N, ∀ m, N ≤ m →
      kmswStageRank w m u.id ≤ kmswStageRank w m v.id ∧
        (0 < p.length → kmswStageRank w m u.id < kmswStageRank w m v.id) := by
  induction p with
  | nil => exact ⟨0, fun _ _ => ⟨le_rfl, by simp⟩⟩
  | @cons a b p e ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨Ne, he, _⟩ := e.property.1
    refine ⟨max N Ne, fun m hm => ?_⟩
    have he' : e.val < (kmswStage w m).nextEdge :=
      he.trans_le (kmswStage_nextEdge_mono w (by omega : Ne ≤ m))
    have hstrict := kmswStageRank_strict w m e.val he'
    have hends := edge_endpoints_eq w he'
    rw [hends.1, hends.2, e.property.2.1, e.property.2.2] at hstrict
    have hprev := (hN m (by omega)).1
    exact ⟨hprev.trans hstrict.le,
      fun _ => hprev.trans_lt hstrict⟩

/-- Presence of an allocated edge persists at every later finite stage -/
private theorem kmswStage_present_mono (w : ℕ → Fin 3) {j m e : ℕ}
    (hjm : j ≤ m) (he : e < (kmswStage w j).nextEdge)
    (hp : (kmswStage w j).present e = true) :
    (kmswStage w m).present e = true := by
  induction m, hjm using Nat.le_induction with
  | base => exact hp
  | @succ m hjm ih =>
    have he' : e < (kmswStage w m).nextEdge :=
      he.trans_le (kmswStage_nextEdge_mono w hjm)
    change (kmswStep (kmswStage w m) (w m)).present e = true
    rw [kmswStep_present_existing _ _ he']
    split_ifs
    · rfl
    · exact ih

/-- Every arrow on a finite present-edge path from the hit vertex is indexed
by an active edge at or after its first right-coordinate hit -/
private theorem rightHit_path_frontier_and_edges (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    ∀ {v : PresentVertex w}
      (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) v),
      (∀ e ∈ pathEdgeList p,
        ∃ n, boundaryHitTime w h k ≤ n ∧ e = act w n) ∧
      (∀ z ∈ p.vertices,
        UpperFrontierEndpoint (kmswStage w (boundaryHitTime w h k)) z.id) := by
  let τ := boundaryHitTime w h k
  obtain ⟨r, hτ, hURr, hstartR, hfresh⟩ := rightHit_previousStage w h hk
  have hURτ : (kmswStage w τ).UR = [] := by
    simpa [τ] using boundaryHit_right_UR_empty w h hk
  have hstartActive : boundaryVertex w h k =
      (kmswStage w τ).west (act w τ) := by
    calc
      boundaryVertex w h k = activeInitial w τ := by
        simpa [τ] using boundaryVertex_right_hit_eq w h hk
      _ = (kmswStage w τ).west (act w τ) := CutConverse.activeInitial_eq w τ
  have hactUL : act w τ ∈ (kmswStage w τ).UL := by
    obtain ⟨xs, hUL⟩ := kmswStage_UL_last w τ
    rw [hUL]
    simp [act]
  have hstartFront : UpperFrontierEndpoint (kmswStage w τ)
      (boundaryVertex w h k) := by
    rw [hstartActive]
    exact Or.inl ⟨act w τ, List.mem_append_left _ hactUL, Or.inl rfl⟩
  have hstartOld : boundaryVertex w h k < (kmswStage w τ).nextVertex := by
    rw [hstartActive]
    exact (kmswStage_endpoints_lt_nextVertex w τ (act w τ)
      (act_lt_nextEdge w le_rfl)).1
  have hsource_old (j : ℕ) (hjτ : j < τ) {a : PresentVertex w}
      {e : ℕ} (heq : e = act w j)
      (hsrc : edgeWest w e = a.id) :
      a.id < (kmswStage w τ).nextVertex := by
    have hjτ' : j < boundaryHitTime w h k := by simpa [τ] using hjτ
    have hjr : j ≤ r := by rw [hτ] at hjτ'; omega
    have halloc := act_lt_nextEdge w (Nat.le_refl j)
    have hb := kmswStage_endpoints_lt_nextVertex w j (act w j) halloc
    have hstage := edge_endpoints_eq w halloc
    have hval : a.id = (kmswStage w j).west (act w j) := by
      calc
        a.id = edgeWest w e := hsrc.symm
        _ = edgeWest w (act w j) := by rw [heq]
        _ = (kmswStage w j).west (act w j) := hstage.1.symm
    rw [hval]
    exact hb.1.trans_le (CutConverse.nextVertex_mono w (Nat.le_of_lt hjτ))
  have hactivePresentAtPrevious (j : ℕ) (hjr : j ≤ r) :
      (kmswStage w r).present (act w j) = true := by
    have hactULj : act w j ∈ (kmswStage w j).UL := by
      obtain ⟨xs, hUL⟩ := kmswStage_UL_last w j
      rw [hUL]
      simp [act]
    have hpresent := (kmswStage_status w j).2.1 (act w j) hactULj
    exact kmswStage_present_mono w hjr (act_lt_nextEdge w le_rfl) hpresent
  have hstartStageR : boundaryVertex w h k =
      (kmswStage w r).east (act w r) := hstartR
  have hfreshHit : (kmswStage w τ).east (act w τ) =
      (kmswStage w r).nextVertex := by simpa [τ, hτ] using hfresh
  have hInd : ∀ {v : PresentVertex w}
      (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) v),
      (∀ e ∈ pathEdgeList p,
        ∃ n, τ ≤ n ∧ e = act w n) ∧
      (∀ z ∈ p.vertices, UpperFrontierEndpoint (kmswStage w τ) z.id) := by
    intro v p
    induction p with
    | nil =>
      constructor
      · simp [pathEdgeList]
      · intro z hz
        have hzEq : z = (⟨boundaryVertex w h k⟩ : PresentVertex w) := by
          simpa using hz
        subst z
        simpa using hstartFront
    | @cons a b p e ih =>
      obtain ⟨N, heN, hpN⟩ := e.property.1
      obtain ⟨j, hjN, hje⟩ := stagePresent_exists_active w N e.val heN hpN
      have hjτ : τ ≤ j := by
        by_contra hjnot
        have hjlt : j < τ := by omega
        exfalso
        have hsourceSafe := ih.2 a p.end_mem_vertices
        have hsourceOld := hsource_old j hjlt hje e.property.2.1
        obtain ⟨Nr, hrank⟩ := presentPath_rank_eventually p
        let M := max Nr τ
        have hpathRank := (hrank M (Nat.le_max_left _ _)).1
        have hstartRankStable := stageRank_stable_oldVertex w
          (Nat.le_max_right Nr τ) hstartOld
        have hsourceRankStable := stageRank_stable_oldVertex w
          (Nat.le_max_right Nr τ) hsourceOld
        have hrankSource : kmswStageRank w τ
            (boundaryVertex w h k) ≤ kmswStageRank w τ a.id := by
          rw [← hstartRankStable, ← hsourceRankStable]
          exact hpathRank
        rcases hsourceSafe with ⟨f₀, hf₀, hsourceEnds⟩ | hfreshSource
        · have hf₀UL : f₀ ∈ (kmswStage w τ).UL := by
            simpa [hURτ] using hf₀
          rcases upperLeft_endpoint_rankClass w τ hURτ a.id
              ⟨f₀, hf₀UL, hsourceEnds⟩ with hstart | hbelow | heast
          · have hsrcStart : a.id = boundaryVertex w h k := by
              calc
                a.id = (kmswStage w τ).west (act w τ) := hstart
                _ = boundaryVertex w h k := hstartActive.symm
            have hpresent := hactivePresentAtPrevious j (by omega)
            have heprev : e.val < (kmswStage w r).nextEdge := by
              rw [hje]
              exact act_lt_nextEdge w (by omega)
            have hpresentE : (kmswStage w r).present e.val = true := by
              rw [hje]
              exact hpresent
            have hout := stageOutgoing_frontier_empty w r e.val heprev hpresentE
            have hwest : (kmswStage w r).west e.val =
                (kmswStage w r).east (act w r) := by
              calc
                (kmswStage w r).west e.val = edgeWest w e.val :=
                  (edge_endpoints_eq w heprev).1
                _ = a.id := e.property.2.1
                _ = boundaryVertex w h k := hsrcStart
                _ = (kmswStage w r).east (act w r) := hstartStageR
            apply hout
            rw [hwest]
            simp [CutConverse.pendingVertices, act]
          · have hrankSource' : kmswStageRank w τ
                ((kmswStage w τ).west (act w τ)) ≤ kmswStageRank w τ a.id := by
              rw [← hstartActive]
              exact hrankSource
            exact (not_lt_of_ge hrankSource' hbelow).elim
          · have hsrcFresh : a.id = (kmswStage w r).nextVertex := by
              calc
                a.id = (kmswStage w τ).east (act w τ) := heast
                _ = (kmswStage w r).nextVertex := hfreshHit
            have heprev : e.val < (kmswStage w r).nextEdge := by
              rw [hje]
              exact act_lt_nextEdge w (by omega)
            have hb := kmswStage_endpoints_lt_nextVertex w r e.val heprev
            have hstageW := (edge_endpoints_eq w heprev).1
            have hsourceBound : a.id < (kmswStage w r).nextVertex := by
              calc
                a.id = edgeWest w e.val := e.property.2.1.symm
                _ = (kmswStage w r).west e.val := hstageW.symm
                _ < (kmswStage w r).nextVertex := hb.1
            omega
        · have : (kmswStage w τ).nextVertex ≤ a.id := hfreshSource
          omega
      constructor
      · intro f hf
        have hf' : f ∈ pathEdgeList p ++ [e.val] := by
          simpa only [pathEdgeList] using hf
        rcases List.mem_append.mp hf' with hprev | hlast
        · exact ih.1 f hprev
        · have hfe : f = e.val := List.mem_singleton.mp hlast
          subst f
          exact ⟨j, hjτ, hje⟩
      · intro z hz
        rcases (Path.mem_vertices_cons p e).mp hz with hz | hz
        · exact ih.2 z hz
        · subst z
          have hfront := kmswStage_act_endpoint_since w hjτ
            (Nat.lt_succ_self j)
          have halloc := act_lt_nextEdge w (Nat.le_refl j)
          have hends := edge_endpoints_eq w halloc
          have htargetEq : (kmswStage w j).east (act w j) = b.id := by
            calc
              (kmswStage w j).east (act w j) = edgeEast w (act w j) := hends.2
              _ = edgeEast w e.val := by rw [hje]
              _ = b.id := e.property.2.2
          exact htargetEq ▸ hfront.2
  intro v p
  rcases hInd p with ⟨hedges, hvertices⟩
  constructor
  · simpa [τ] using hedges
  · simpa [τ] using hvertices

/-- Every edge ID along a finite directed path from the hit-indexed vertex
for `k ≥ 1` is an active edge at or after the right-coordinate hit -/
theorem directedPath_edges_from_boundaryVertex_right (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k)
    {v : PresentVertex w}
    (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) v) :
    ∀ e ∈ pathEdgeList p,
      ∃ n, boundaryHitTime w h k ≤ n ∧ e = act w n :=
  rightHit_path_frontier_and_edges w h hk p |>.1

private theorem leftHit_path_frontier_and_edges (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∀ {v : PresentVertex w}
      (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) v),
      (∀ e ∈ pathEdgeList p,
        ∃ n, boundaryHitTime w h k ≤ n ∧ e = act w n) ∧
      (∀ z ∈ p.vertices,
        UpperFrontierEndpoint (kmswStage w (boundaryHitTime w h k)) z.id) := by
  let τ := boundaryHitTime w h k
  obtain ⟨r, hτ, hw, hULr, hvertex, hwestHit, hnextVertex, hULτ⟩ :=
    leftHit_previousStage w h hk
  have hstartActive : boundaryVertex w h k =
      (kmswStage w τ).west (act w τ) := by
    calc
      boundaryVertex w h k = activeInitial w τ := by
        simpa [τ] using boundaryVertex_left_hit_eq w h hk
      _ = (kmswStage w τ).west (act w τ) := CutConverse.activeInitial_eq w τ
  have hULτ' : (kmswStage w τ).UL = [act w τ] := by
    simpa [τ, hτ] using hULτ
  have hULτActive : (kmswStage w τ).UL = [(kmswStage w τ).active] := by
    simpa [act] using hULτ'
  have hnextVertexτ : (kmswStage w τ).nextVertex =
      (kmswStage w r).nextVertex + 1 := by
    simpa [τ, hτ] using hnextVertex
  have hstartFront : UpperFrontierEndpoint (kmswStage w τ)
      (boundaryVertex w h k) := by
    rw [hstartActive]
    exact Or.inl ⟨act w τ, List.mem_append_left _ (by rw [hULτ']; simp), Or.inl rfl⟩
  have hstartOld : boundaryVertex w h k < (kmswStage w τ).nextVertex := by
    rw [hvertex]
    rw [hnextVertexτ]
    exact Nat.lt_succ_of_le (Nat.le_refl _)
  have hsource_old (j : ℕ) (hjτ : j < τ) {a : PresentVertex w}
      {e : ℕ} (heq : e = act w j)
      (hsrc : edgeWest w e = a.id) :
      a.id < (kmswStage w r).nextVertex := by
    have hjτ' : j < boundaryHitTime w h k := by simpa [τ] using hjτ
    have hjr : j ≤ r := by rw [hτ] at hjτ'; omega
    have halloc := act_lt_nextEdge w (Nat.le_refl j)
    have hb := kmswStage_endpoints_lt_nextVertex w j (act w j) halloc
    have hstage := edge_endpoints_eq w halloc
    have hval : a.id = (kmswStage w j).west (act w j) := by
      calc
        a.id = edgeWest w e := hsrc.symm
        _ = edgeWest w (act w j) := by rw [heq]
        _ = (kmswStage w j).west (act w j) := hstage.1.symm
    rw [hval]
    exact hb.1.trans_le (CutConverse.nextVertex_mono w hjr)
  have hcohτ := (CutConverse.frontier_history w τ).1
  have hInd : ∀ {v : PresentVertex w}
      (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) v),
      (∀ e ∈ pathEdgeList p,
        ∃ n, τ ≤ n ∧ e = act w n) ∧
      (∀ z ∈ p.vertices, UpperFrontierEndpoint (kmswStage w τ) z.id) := by
    intro v p
    induction p with
    | nil =>
      constructor
      · simp [pathEdgeList]
      · intro z hz
        have hzEq : z = (⟨boundaryVertex w h k⟩ : PresentVertex w) := by
          simpa using hz
        subst z
        simpa using hstartFront
    | @cons a b p e ih =>
      obtain ⟨N, heN, hpN⟩ := e.property.1
      obtain ⟨j, hjN, hje⟩ := stagePresent_exists_active w N e.val heN hpN
      have hjτ : τ ≤ j := by
        by_contra hjnot
        have hjlt : j < τ := by omega
        exfalso
        have hsourceSafe := ih.2 a p.end_mem_vertices
        have hsourceOldR := hsource_old j hjlt hje e.property.2.1
        have hrτ : r ≤ τ := by
          change r ≤ boundaryHitTime w h k
          rw [hτ]
          omega
        have hsourceOldτ : a.id < (kmswStage w τ).nextVertex :=
          hsourceOldR.trans_le (CutConverse.nextVertex_mono w hrτ)
        rcases leftHit_frontier_endpoint_pending_or_source
            (kmswStage w τ) hULτActive hcohτ a.id hsourceSafe hsourceOldτ with
          hsourceFresh | hsourcePending
        · have hsrcFresh : a.id = (kmswStage w r).nextVertex := by
            calc
              a.id = (kmswStage w τ).west (act w τ) := hsourceFresh
              _ = (kmswStage w r).nextVertex := by simpa [τ, hτ] using hwestHit
          omega
        · have hjτ' : j ≤ τ := by omega
          have heτ : e.val < (kmswStage w τ).nextEdge := by
            rw [hje]
            exact act_lt_nextEdge w hjτ'
          have hpτ : (kmswStage w τ).present e.val = true := by
            rw [hje]
            have hactULj : act w j ∈ (kmswStage w j).UL := by
              obtain ⟨xs, hUL⟩ := kmswStage_UL_last w j
              rw [hUL]
              simp [act]
            have hpj := (kmswStage_status w j).2.1 (act w j) hactULj
            exact kmswStage_present_mono w hjτ' (act_lt_nextEdge w le_rfl) hpj
          have hout := stageOutgoing_frontier_empty w τ e.val heτ hpτ
          have hwestPending : (kmswStage w τ).west e.val ∈
              CutConverse.pendingVertices (kmswStage w τ) := by
            rw [(edge_endpoints_eq w heτ).1, e.property.2.1]
            exact hsourcePending
          exact hout hwestPending
      constructor
      · intro f hf
        have hf' : f ∈ pathEdgeList p ++ [e.val] := by
          simpa only [pathEdgeList] using hf
        rcases List.mem_append.mp hf' with hprev | hlast
        · exact ih.1 f hprev
        · have hfe : f = e.val := List.mem_singleton.mp hlast
          subst f
          exact ⟨j, hjτ, hje⟩
      · intro z hz
        rcases (Path.mem_vertices_cons p e).mp hz with hz | hz
        · exact ih.2 z hz
        · subst z
          have hfront := kmswStage_act_endpoint_since w hjτ
            (Nat.lt_succ_self j)
          have halloc := act_lt_nextEdge w (Nat.le_refl j)
          have hends := edge_endpoints_eq w halloc
          have htargetEq : (kmswStage w j).east (act w j) = b.id := by
            calc
              (kmswStage w j).east (act w j) = edgeEast w (act w j) := hends.2
              _ = edgeEast w e.val := by rw [hje]
              _ = b.id := e.property.2.2
          exact htargetEq ▸ hfront.2
  intro v p
  rcases hInd p with ⟨hedges, hvertices⟩
  constructor
  · simpa [τ] using hedges
  · simpa [τ] using hvertices

/-- Every edge ID along a finite directed path from the hit-indexed vertex
for `k ≤ -1` is an active edge at or after the left-coordinate hit -/
theorem directedPath_edges_from_boundaryVertex_left (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1)
    {v : PresentVertex w}
    (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) v) :
    ∀ e ∈ pathEdgeList p,
      ∃ n, boundaryHitTime w h k ≤ n ∧ e = act w n :=
  leftHit_path_frontier_and_edges w h hk p |>.1

/-- For the source vertex `x₀=0`, every edge along a finite present-edge path
is active at a nonnegative time (`lem-directed-contain`, -/
theorem directedPath_edges_from_boundaryVertex_zero (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {v : PresentVertex w}
    (p : Path (⟨boundaryVertex w h 0⟩ : PresentVertex w) v) :
    ∀ e ∈ pathEdgeList p,
      ∃ n, boundaryHitTime w h 0 ≤ n ∧ e = act w n := by
  intro e he
  induction p with
  | nil => simp [pathEdgeList] at he
  | @cons a b p f ih =>
    have hmem : e ∈ pathEdgeList p ++ [f.val] := by
      simpa only [pathEdgeList] using he
    rcases List.mem_append.mp hmem with hp | hf
    · exact ih hp
    · have heq : e = f.val := List.mem_singleton.mp hf
      subst e
      obtain ⟨N, hlt, hpres⟩ := f.property.1
      obtain ⟨n, _, hact⟩ := stagePresent_exists_active w N f.val hlt hpres
      exact ⟨n, by rw [boundaryHitTime_zero]; omega, hact⟩

/-- Every finite present-edge path from any hit-indexed boundary vertex uses
only active edges at or after its hit time (`lem-directed-contain`, -/
theorem directedPath_edges_from_boundaryVertex (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) {v : PresentVertex w}
    (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) v) :
    ∀ e ∈ pathEdgeList p,
      ∃ n, boundaryHitTime w h k ≤ n ∧ e = act w n := by
  by_cases hk0 : k = 0
  · subst k
    exact directedPath_edges_from_boundaryVertex_zero w h p
  · by_cases hkpos : 1 ≤ k
    · exact directedPath_edges_from_boundaryVertex_right w h hkpos p
    · have hkneg : k ≤ -1 := by omega
      exact directedPath_edges_from_boundaryVertex_left w h hkneg p

end DirectedDistances.KMSW
