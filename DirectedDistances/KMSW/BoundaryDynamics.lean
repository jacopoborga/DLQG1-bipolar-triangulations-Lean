module

public import DirectedDistances.KMSW.Walk
public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefix
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FinCases

/-! Supporting lemmas for paper labels `def-kmsw`, `lem-kmsw-bdy` (see CORRESPONDENCE.md). -/

/-! # Deterministic KMSW boundary bookkeeping

These lists are bookkeeping boundaries; identifying them with the external face
of a combinatorial map is a separate obligation. No planarity claim is made here. -/

public section
namespace DirectedDistances.KMSW
open scoped BigOperators

/-- Exactly the IDs below `nextVertex` and `nextEdge` exist. Endpoint and status
functions are meaningful only below `nextEdge`. Missing edges have geometric
west/east endpoints, with no directed orientation. `UL`, `LL`, and `LR` are
ordered west to east. `UR` starts at the terminal vertex of the active edge
and runs towards the terminal vertex of `LR`; its head is immediately east
of the active edge. Triangle triples list old active, new active, third side.
The structure itself imposes no geometric invariant on arbitrary states. -/
structure State where
  nextVertex : ℕ
  nextEdge : ℕ
  west : ℕ → ℕ
  east : ℕ → ℕ
  present : ℕ → Bool
  triangles : List (ℕ × ℕ × ℕ)
  active : ℕ
  UL : List ℕ
  UR : List ℕ
  LL : List ℕ
  LR : List ℕ

 
@[expose] def kmswInit : State where
  nextVertex := 2
  nextEdge := 1
  west := fun _ => 0
  east := fun _ => 1
  present := fun _ => true
  triangles := []
  active := 0
  UL := [0]
  UR := []
  LL := []
  LR := [0]



@[expose] def State.addEdge (s : State) (a b : ℕ) (p : Bool) : State :=
  { s with
    nextEdge := s.nextEdge + 1
    west := fun e => if e = s.nextEdge then a else s.west e
    east := fun e => if e = s.nextEdge then b else s.east e
    present := fun e => if e = s.nextEdge then p else s.present e }



@[expose] def kmswCodeStep (c : Fin 3) : Step :=
  if c = 0 then .left else if c = 1 then .up else .down



theorem kmswCodeStep_coordinates (c : Fin 3) :
    ((kmswCodeStep c).dx, (kmswCodeStep c).dy) =
      RandomWalk.lazyTwoDimensionalStep c := by
  fin_cases c <;> rfl








@[expose] def kmswStepOfStep (s : State) : Step → State
  | .down =>
    match s.UR with
    | e :: es =>
      { s with
        present := fun f => if f = e then true else s.present f
        active := e
        UL := s.UL ++ [e]
        UR := es }
    | [] =>
      let t := s.addEdge (s.east s.active) s.nextVertex true
      { t with
        nextVertex := s.nextVertex + 1
        active := s.nextEdge
        UL := s.UL ++ [s.nextEdge]
        LR := s.LR ++ [s.nextEdge] }
  | .left =>
    match s.UL.dropLast.reverse with
    | e :: es =>
      let t := s.addEdge (s.west e) (s.east s.active) true
      { t with
        active := s.nextEdge
        triangles := s.triangles ++ [(s.active, s.nextEdge, e)]
        UL := es.reverse ++ [s.nextEdge] }
    | [] =>
      let t := s.addEdge s.nextVertex (s.east s.active) true
      let u := t.addEdge s.nextVertex (s.west s.active) false
      { u with
        nextVertex := s.nextVertex + 1
        active := s.nextEdge
        triangles := s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)]
        UL := [s.nextEdge]
        LL := (s.nextEdge + 1) :: s.LL }
  | .up =>
    let t := s.addEdge (s.west s.active) s.nextVertex true
    let u := t.addEdge s.nextVertex (s.east s.active) false
    { u with
      nextVertex := s.nextVertex + 1
      active := s.nextEdge
      triangles := s.triangles ++ [(s.active, s.nextEdge, s.nextEdge + 1)]
      UL := s.UL.dropLast ++ [s.nextEdge]
      UR := (s.nextEdge + 1) :: s.UR }

 
@[expose] def kmswStep (s : State) (c : Fin 3) : State :=
  kmswStepOfStep s (kmswCodeStep c)

 
@[expose] def kmswStage (w : ℕ → Fin 3) : ℕ → State
  | 0 => kmswInit
  | n + 1 => kmswStep (kmswStage w n) (w n)



@[expose] def L (w : ℕ → Fin 3) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, (RandomWalk.lazyTwoDimensionalStep (w i)).1



@[expose] def R (w : ℕ → Fin 3) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, (RandomWalk.lazyTwoDimensionalStep (w i)).2



@[expose] def runningMin (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => f 0
  | n + 1 => min (runningMin f n) (f (n + 1))

 
@[expose] def minL (w : ℕ → Fin 3) (n : ℕ) : ℤ := runningMin (L w) n

 
@[expose] def minR (w : ℕ → Fin 3) (n : ℕ) : ℤ := runningMin (R w) n



theorem runningMin_le (f : ℕ → ℤ) (n j : ℕ) (hj : j ≤ n) :
    runningMin f n ≤ f j := by
  induction n with
  | zero =>
    have : j = 0 := by omega
    subst j
    exact le_refl _
  | succ n ih =>
    by_cases h : j ≤ n
    · exact (min_le_left _ _).trans (ih h)
    · have : j = n + 1 := by omega
      subst j
      exact min_le_right _ _



theorem runningMin_attained (f : ℕ → ℤ) (n : ℕ) :
    ∃ j ≤ n, runningMin f n = f j := by
  induction n with
  | zero => exact ⟨0, le_refl _, rfl⟩
  | succ n ih =>
    obtain ⟨j, hj, he⟩ := ih
    by_cases h : runningMin f n ≤ f (n + 1)
    · exact ⟨j, by omega, (min_eq_left h).trans he⟩
    · exact ⟨n + 1, le_refl _, min_eq_right (by omega)⟩

private theorem step_UL_last (s : State) (c : Fin 3) :
    ∃ es, (kmswStep s c).UL = es ++ [(kmswStep s c).active] := by
  unfold kmswStep
  cases kmswCodeStep c with
  | left =>
    dsimp only [kmswStepOfStep]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨[], rfl⟩
  | up => exact ⟨s.UL.dropLast, rfl⟩
  | down =>
    dsimp only [kmswStepOfStep]
    split <;> exact ⟨_, rfl⟩



theorem kmswStage_UL_last (w : ℕ → Fin 3) (n : ℕ) :
    ∃ es, (kmswStage w n).UL = es ++ [(kmswStage w n).active] := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ n => exact step_UL_last _ _

private theorem L_succ (w : ℕ → Fin 3) (n : ℕ) :
    L w (n + 1) = L w n + (RandomWalk.lazyTwoDimensionalStep (w n)).1 := by
  exact Finset.sum_range_succ _ _

private theorem R_succ (w : ℕ → Fin 3) (n : ℕ) :
    R w (n + 1) = R w n + (RandomWalk.lazyTwoDimensionalStep (w n)).2 := by
  exact Finset.sum_range_succ _ _

private theorem stage_lengths (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswStage w n).UL.length : ℤ) = L w n - minL w n + 1 ∧
    ((kmswStage w n).UR.length : ℤ) = R w n - minR w n ∧
    ((kmswStage w n).LL.length : ℤ) = - minL w n ∧
    ((kmswStage w n).LR.length : ℤ) = - minR w n + 1 := by
  induction n with
  | zero =>
    simp [kmswStage, kmswInit, L, R, minL, minR, runningMin]
  | succ n ih =>
    obtain ⟨hu, hr, hl, hd⟩ := ih
    have hL := runningMin_le (L w) n n (le_refl _)
    have hR := runningMin_le (R w) n n (le_refl _)
    change minL w n ≤ L w n at hL
    change minR w n ≤ R w n at hR
    obtain ⟨es, hes⟩ := kmswStage_UL_last w n
    have hpos : 0 < (kmswStage w n).UL.length := by
      rw [hes]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [show minL w (n + 1) = min (minL w n) (L w (n + 1)) from rfl,
      show minR w (n + 1) = min (minR w n) (R w (n + 1)) from rfl,
      L_succ, R_succ]
    rw [kmswStage]
    by_cases hc : w n = 0
    · rw [hc]
      change (↑(kmswStepOfStep (kmswStage w n) .left).UL.length : ℤ) = _ ∧
        (↑(kmswStepOfStep (kmswStage w n) .left).UR.length : ℤ) = _ ∧
        (↑(kmswStepOfStep (kmswStage w n) .left).LL.length : ℤ) = _ ∧
        (↑(kmswStepOfStep (kmswStage w n) .left).LR.length : ℤ) = _
      simp only [RandomWalk.lazyTwoDimensionalStep_zero, kmswStepOfStep]
      split at *
      next e rest he =>
        have he_len := congrArg List.length he
        simp only [List.length_reverse, List.length_dropLast,
          List.length_cons] at he_len
        simp only [State.addEdge, List.length_append, List.length_reverse,
          List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one,
          add_zero, min_def]
        split_ifs <;> omega
      next he =>
        have he_len := congrArg List.length he
        simp only [List.length_reverse, List.length_dropLast,
          List.length_nil] at he_len
        simp only [State.addEdge, List.length_cons, List.length_nil,
          Nat.cast_add, Nat.cast_one, Nat.cast_zero, 
          add_zero, min_def]
        split_ifs <;> omega
    · by_cases hc' : w n = 1
      · rw [hc']
        change (↑(kmswStepOfStep (kmswStage w n) .up).UL.length : ℤ) = _ ∧
          (↑(kmswStepOfStep (kmswStage w n) .up).UR.length : ℤ) = _ ∧
          (↑(kmswStepOfStep (kmswStage w n) .up).LL.length : ℤ) = _ ∧
          (↑(kmswStepOfStep (kmswStage w n) .up).LR.length : ℤ) = _
        simp only [RandomWalk.lazyTwoDimensionalStep_one, kmswStepOfStep,
          State.addEdge, List.length_append, List.length_dropLast,
          List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one,
          Nat.cast_zero, add_zero, min_def]
        split_ifs <;> omega
      · have hc2 : w n = 2 := by
          apply Fin.ext
          have hb := (w n).isLt
          have hn0 : (w n).val ≠ 0 := by intro h; exact hc (Fin.ext h)
          have hn1 : (w n).val ≠ 1 := by intro h; exact hc' (Fin.ext h)
          omega
        rw [hc2]
        change (↑(kmswStepOfStep (kmswStage w n) .down).UL.length : ℤ) = _ ∧
          (↑(kmswStepOfStep (kmswStage w n) .down).UR.length : ℤ) = _ ∧
          (↑(kmswStepOfStep (kmswStage w n) .down).LL.length : ℤ) = _ ∧
          (↑(kmswStepOfStep (kmswStage w n) .down).LR.length : ℤ) = _
        simp only [RandomWalk.lazyTwoDimensionalStep_two, kmswStepOfStep]
        split at *
        next e rest he =>
          have he_len := congrArg List.length he
          simp only [List.length_cons] at he_len
          simp only [List.length_append, List.length_cons, List.length_nil,
            Nat.cast_add, Nat.cast_one, min_def]
          split_ifs <;> omega
        next he =>
          have he_len := congrArg List.length he
          simp only [List.length_nil] at he_len
          simp only [State.addEdge, List.length_append, List.length_cons,
            List.length_nil, Nat.cast_add, Nat.cast_one,
            min_def]
          split_ifs <;> omega

/-- Upper-left bookkeeping count in `eqn-kmsw-bdy`, -/
theorem kmswStage_UL_length (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswStage w n).UL.length : ℤ) = L w n - minL w n + 1 :=
  (stage_lengths w n).1

/-- Upper-right bookkeeping count in `eqn-kmsw-bdy`, -/
theorem kmswStage_UR_length (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswStage w n).UR.length : ℤ) = R w n - minR w n :=
  (stage_lengths w n).2.1

/-- Lower-left bookkeeping count in `eqn-kmsw-bdy`, -/
theorem kmswStage_LL_length (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswStage w n).LL.length : ℤ) = - minL w n :=
  (stage_lengths w n).2.2.1

/-- Lower-right bookkeeping count in `eqn-kmsw-bdy`, -/
theorem kmswStage_LR_length (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswStage w n).LR.length : ℤ) = - minR w n + 1 :=
  (stage_lengths w n).2.2.2

/-- First-hitting bookkeeping characterization from `lem-kmsw-bdy`(ii),
hits `-k` is exactly the first stage with `k+1` lower-right edges. This
includes `k = 0`, when the initial edge is already present at time zero. -/
theorem kmswStage_LR_first_hitting (w : ℕ → Fin 3) (k n : ℕ) :
    (R w n = -(k : ℤ) ∧ ∀ j < n, -(k : ℤ) < R w j) ↔
      ((kmswStage w n).LR.length = k + 1 ∧
        ∀ j < n, (kmswStage w j).LR.length ≤ k) := by
  constructor
  · rintro ⟨hn, hprior⟩
    have hmin : minR w n = -(k : ℤ) := by
      obtain ⟨j, hj, he⟩ := runningMin_attained (R w) n
      change minR w n = R w j at he
      have hle := runningMin_le (R w) n n (le_refl _)
      change minR w n ≤ R w n at hle
      by_cases hjn : j = n
      · rw [hjn, hn] at he
        exact he
      · have hp := hprior j (by omega)
        omega
    constructor
    · have h := kmswStage_LR_length w n
      omega
    · intro j hj
      obtain ⟨i, hi, he⟩ := runningMin_attained (R w) j
      change minR w j = R w i at he
      have hp := hprior i (by omega)
      have h := kmswStage_LR_length w j
      omega
  · rintro ⟨hn, hprior⟩
    have h := kmswStage_LR_length w n
    have hmin : minR w n = -(k : ℤ) := by omega
    constructor
    · obtain ⟨j, hj, he⟩ := runningMin_attained (R w) n
      change minR w n = R w j at he
      by_cases hjn : j = n
      · rw [hjn] at he
        omega
      · have hp := hprior j (by omega)
        have hlen := kmswStage_LR_length w j
        have hle := runningMin_le (R w) j j (le_refl _)
        change minR w j ≤ R w j at hle
        omega
    · intro j hj
      have hp := hprior j hj
      have hlen := kmswStage_LR_length w j
      have hle := runningMin_le (R w) j j (le_refl _)
      change minR w j ≤ R w j at hle
      omega

end DirectedDistances.KMSW
