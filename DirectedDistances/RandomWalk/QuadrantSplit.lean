/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.RandomWalk.IIDCodeRelabel

/-! # Deterministic splitting of the quadrant-walk codes

The two code streams and their alternating interleaving implement the walk
decomposition in the proof of `lem-quadrant-walk` -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- The active phase in the deterministic split of the source codes. -/
inductive QuadrantPhase where
  | r
  | l
  deriving DecidableEq, Repr

/-- Finite state for reading a code stream by alternating new-minimum phases.
The `r` stream switches when its first coordinate makes a new minimum; the
`l` stream switches when its second coordinate makes a new minimum. -/
structure QuadrantSplitState where
  phase : QuadrantPhase
  rCount : ℕ
  lCount : ℕ
  rWalk : ℤ × ℤ
  lWalk : ℤ × ℤ
  rLMin : ℤ
  lRMin : ℤ
  deriving Repr

/-- The initial state for the two alternating code streams. -/
@[expose] def quadrantSplitStart : QuadrantSplitState where
  phase := .r
  rCount := 0
  lCount := 0
  rWalk := (0, 0)
  lWalk := (0, 0)
  rLMin := 0
  lRMin := 0

/-- Consume one code in the active phase, switching after a new minimum is
reached. The switching code is included in the phase that it terminates. -/
@[expose] def quadrantSplitAdvance (s : QuadrantSplitState) (c : Fin 3) :
    QuadrantSplitState :=
  match s.phase with
  | .r =>
      let w := s.rWalk + lazyTwoDimensionalStep c
      let hit := w.1 < s.rLMin
      { s with
        phase := if hit then .l else .r
        rCount := s.rCount + 1
        rWalk := w
        rLMin := if hit then w.1 else s.rLMin }
  | .l =>
      let w := s.lWalk + lazyTwoDimensionalStep c
      let hit := w.2 < s.lRMin
      { s with
        phase := if hit then .r else .l
        lCount := s.lCount + 1
        lWalk := w
        lRMin := if hit then w.2 else s.lRMin }

 
theorem quadrantSplitAdvance_counts (s : QuadrantSplitState) (c : Fin 3) :
    (quadrantSplitAdvance s c).rCount + (quadrantSplitAdvance s c).lCount =
      s.rCount + s.lCount + 1 := by
  cases h : s.phase <;> simp [quadrantSplitAdvance, h] <;> omega

/-- The number of consumed `r` codes changes by one exactly in an `r` phase. -/
theorem quadrantSplitAdvance_rCount (s : QuadrantSplitState) (c : Fin 3) :
    (quadrantSplitAdvance s c).rCount =
      if s.phase = .r then s.rCount + 1 else s.rCount := by
  cases h : s.phase <;> simp [quadrantSplitAdvance, h]

/-- The number of consumed `l` codes changes by one exactly in an `l` phase. -/
theorem quadrantSplitAdvance_lCount (s : QuadrantSplitState) (c : Fin 3) :
    (quadrantSplitAdvance s c).lCount =
      if s.phase = .l then s.lCount + 1 else s.lCount := by
  cases h : s.phase <;> simp [quadrantSplitAdvance, h]

/-- State after reading the first `n` codes of a source stream. Code zero is
the fixed dummy coordinate and is not consumed. -/
@[expose] def quadrantSplitState (ω : ℕ → Fin 3) : ℕ → QuadrantSplitState
  | 0 => quadrantSplitStart
  | n + 1 => quadrantSplitAdvance (quadrantSplitState ω n) (ω (n + 1))

/-- After `n` source steps, the two streams have consumed exactly `n` codes
between them. -/
theorem quadrantSplitState_counts (ω : ℕ → Fin 3) (n : ℕ) :
    (quadrantSplitState ω n).rCount + (quadrantSplitState ω n).lCount = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [quadrantSplitState]
      rw [quadrantSplitAdvance_counts, ih]

/-- The `r` count never decreases while a source stream is read. -/
theorem quadrantSplitState_rCount_succ_ge (ω : ℕ → Fin 3) (n : ℕ) :
    (quadrantSplitState ω n).rCount ≤ (quadrantSplitState ω (n + 1)).rCount := by
  rw [quadrantSplitState, quadrantSplitAdvance_rCount]
  split <;> omega

/-- The `l` count never decreases while a source stream is read. -/
theorem quadrantSplitState_lCount_succ_ge (ω : ℕ → Fin 3) (n : ℕ) :
    (quadrantSplitState ω n).lCount ≤ (quadrantSplitState ω (n + 1)).lCount := by
  rw [quadrantSplitState, quadrantSplitAdvance_lCount]
  split <;> omega

/-- The `r` count is monotone in the number of source codes read. -/
theorem quadrantSplitState_rCount_mono (ω : ℕ → Fin 3) : ∀ n m, n ≤ m →
    (quadrantSplitState ω n).rCount ≤ (quadrantSplitState ω m).rCount := by
  intro n m
  induction m with
  | zero =>
      intro h
      have hn : n = 0 := by omega
      subst n
      rfl
  | succ m ih =>
      intro h
      by_cases hnm : n ≤ m
      · exact le_trans (ih hnm) (quadrantSplitState_rCount_succ_ge ω m)
      · have hn : n = m + 1 := by omega
        subst n
        exact le_rfl

/-- The `l` count is monotone in the number of source codes read. -/
theorem quadrantSplitState_lCount_mono (ω : ℕ → Fin 3) : ∀ n m, n ≤ m →
    (quadrantSplitState ω n).lCount ≤ (quadrantSplitState ω m).lCount := by
  intro n m
  induction m with
  | zero =>
      intro h
      have hn : n = 0 := by omega
      subst n
      rfl
  | succ m ih =>
      intro h
      by_cases hnm : n ≤ m
      · exact le_trans (ih hnm) (quadrantSplitState_lCount_succ_ge ω m)
      · have hn : n = m + 1 := by omega
        subst n
        exact le_rfl

/-- The code in the `r` stream at its one-based position `k + 1`, or the dummy
code zero if that position is never reached. -/
@[expose] noncomputable def quadrantRCode (ω : ℕ → Fin 3) (k : ℕ) : Fin 3 := by
  classical
  exact if h : ∃ n, (quadrantSplitState ω n).rCount = k + 1 then
    ω (Nat.find h) else 0

/-- The code in the `l` stream at its one-based position `k + 1`, or the dummy
code zero if that position is never reached. -/
@[expose] noncomputable def quadrantLCode (ω : ℕ → Fin 3) (k : ℕ) : Fin 3 := by
  classical
  exact if h : ∃ n, (quadrantSplitState ω n).lCount = k + 1 then
    ω (Nat.find h) else 0

/-- At the step that raises the `r` count, the extracted stream uses that
source code. -/
theorem quadrantRCode_at_step (ω : ℕ → Fin 3) (n : ℕ)
    (hphase : (quadrantSplitState ω n).phase = .r) :
    quadrantRCode ω (quadrantSplitState ω n).rCount = ω (n + 1) := by
  classical
  let k := (quadrantSplitState ω n).rCount
  have hstep : (quadrantSplitState ω (n + 1)).rCount = k + 1 := by
    rw [quadrantSplitState, quadrantSplitAdvance_rCount, ite_eq_left hphase]
  have hfirst : ∀ m < n + 1, (quadrantSplitState ω m).rCount ≠ k + 1 := by
    intro m hm
    have hmle : m ≤ n := by omega
    have hmono := quadrantSplitState_rCount_mono ω m n hmle
    omega
  have h : ∃ m, (quadrantSplitState ω m).rCount = k + 1 := ⟨n + 1, hstep⟩
  have hfind : Nat.find h = n + 1 := (Nat.find_eq_iff h).2 ⟨hstep, hfirst⟩
  unfold quadrantRCode
  rw [dite_eq_left h, hfind]

/-- At the step that raises the `l` count, the extracted stream uses that
source code. -/
theorem quadrantLCode_at_step (ω : ℕ → Fin 3) (n : ℕ)
    (hphase : (quadrantSplitState ω n).phase = .l) :
    quadrantLCode ω (quadrantSplitState ω n).lCount = ω (n + 1) := by
  classical
  let k := (quadrantSplitState ω n).lCount
  have hstep : (quadrantSplitState ω (n + 1)).lCount = k + 1 := by
    rw [quadrantSplitState, quadrantSplitAdvance_lCount, ite_eq_left hphase]
  have hfirst : ∀ m < n + 1, (quadrantSplitState ω m).lCount ≠ k + 1 := by
    intro m hm
    have hmle : m ≤ n := by omega
    have hmono := quadrantSplitState_lCount_mono ω m n hmle
    omega
  have h : ∃ m, (quadrantSplitState ω m).lCount = k + 1 := ⟨n + 1, hstep⟩
  have hfind : Nat.find h = n + 1 := (Nat.find_eq_iff h).2 ⟨hstep, hfirst⟩
  unfold quadrantLCode
  rw [dite_eq_left h, hfind]

/-- Split a source stream into the codes consumed during its alternating
`r` and `l` phases, retaining dummy coordinate zero in both outputs. -/
@[expose] noncomputable def phaseSplit (ω : ℕ → Fin 3) :
    (ℕ → Fin 3) × (ℕ → Fin 3) :=
  (fun i => if i = 0 then 0 else quadrantRCode ω (i - 1),
   fun i => if i = 0 then 0 else quadrantLCode ω (i - 1))

/-- The split streams carry the fixed dummy code at index zero. -/
theorem phaseSplit_zero (ω : ℕ → Fin 3) :
    ((phaseSplit ω).1 0, (phaseSplit ω).2 0) = (0, 0) := by
  simp [phaseSplit]

/-- At an `r` phase, the next code in the split stream is the next source
code. -/
theorem phaseSplit_rCode_at_step (ω : ℕ → Fin 3) (n : ℕ)
    (hphase : (quadrantSplitState ω n).phase = .r) :
    (phaseSplit ω).1 ((quadrantSplitState ω n).rCount + 1) = ω (n + 1) := by
  change quadrantRCode ω ((quadrantSplitState ω n).rCount + 1 - 1) = _
  rw [show (quadrantSplitState ω n).rCount + 1 - 1 =
      (quadrantSplitState ω n).rCount by omega]
  exact quadrantRCode_at_step ω n hphase

/-- At an `l` phase, the next code in the split stream is the next source
code. -/
theorem phaseSplit_lCode_at_step (ω : ℕ → Fin 3) (n : ℕ)
    (hphase : (quadrantSplitState ω n).phase = .l) :
    (phaseSplit ω).2 ((quadrantSplitState ω n).lCount + 1) = ω (n + 1) := by
  change quadrantLCode ω ((quadrantSplitState ω n).lCount + 1 - 1) = _
  rw [show (quadrantSplitState ω n).lCount + 1 - 1 =
      (quadrantSplitState ω n).lCount by omega]
  exact quadrantLCode_at_step ω n hphase

/-- State after consuming `n` codes from two streams by alternating at their
successive new minima. -/
@[expose] def quadrantInterleaveState (a b : ℕ → Fin 3) : ℕ → QuadrantSplitState
  | 0 => quadrantSplitStart
  | n + 1 =>
      let s := quadrantInterleaveState a b n
      let c := match s.phase with
        | .r => a (s.rCount + 1)
        | .l => b (s.lCount + 1)
      quadrantSplitAdvance s c

/-- Interleave two code streams, consuming the `r` stream until its first
coordinate reaches a new minimum, then the `l` stream until its second
coordinate reaches a new minimum, and repeating. Both streams retain their
fixed dummy code at index zero. -/
@[expose] def interleave (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) : ℕ → Fin 3 :=
  fun i => if i = 0 then 0 else
    let s := quadrantInterleaveState ab.1 ab.2 (i - 1)
    match s.phase with
    | .r => ab.1 (s.rCount + 1)
    | .l => ab.2 (s.lCount + 1)

/-- Reading an interleaved stream drives the same finite state used to create
it. -/
theorem quadrantSplitState_interleave (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ) :
    quadrantSplitState (interleave ab) n =
      quadrantInterleaveState ab.1 ab.2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [quadrantSplitState, quadrantInterleaveState]
      rw [ih]
      have hindex : n + 1 - 1 = n := by omega
      rw [show interleave ab (n + 1) =
        (match (quadrantInterleaveState ab.1 ab.2 n).phase with
        | .r => ab.1 ((quadrantInterleaveState ab.1 ab.2 n).rCount + 1)
        | .l => ab.2 ((quadrantInterleaveState ab.1 ab.2 n).lCount + 1)) by
          simp [interleave, hindex]
          rfl]
      rfl

/-- The interleaver and splitter have the same finite state when the inputs
are a stream and its own split. -/
theorem quadrantInterleaveState_phaseSplit (ω : ℕ → Fin 3) (n : ℕ) :
    quadrantInterleaveState (phaseSplit ω).1 (phaseSplit ω).2 n =
      quadrantSplitState ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [quadrantInterleaveState, quadrantSplitState]
      rw [ih]
      cases hphase : (quadrantSplitState ω n).phase with
      | r =>
          rw [phaseSplit_rCode_at_step ω n hphase]
      | l =>
          rw [phaseSplit_lCode_at_step ω n hphase]

/-- The interleaved stream carries the fixed dummy code at index zero. -/
theorem interleave_zero (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) : interleave ab 0 = 0 := by
  simp [interleave]

/-- One-step additive form of the source-walk recursion. -/
private theorem codeWalk_succ_add (ω : ℕ → Fin 3) (n : ℕ) :
    codeWalk ω (n + 1) = codeWalk ω n + lazyTwoDimensionalStep (ω (n + 1)) := by
  have h := codeWalk_succ_sub ω n
  calc
    codeWalk ω (n + 1) =
        (codeWalk ω (n + 1) - codeWalk ω n) + codeWalk ω n := by abel
    _ = lazyTwoDimensionalStep (ω (n + 1)) + codeWalk ω n := by rw [h]
    _ = codeWalk ω n + lazyTwoDimensionalStep (ω (n + 1)) := by abel

/-- The `r` phase walk is the source walk read along the `r` codes consumed
so far. -/
theorem quadrantInterleaveState_rWalk (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ) :
    (quadrantInterleaveState ab.1 ab.2 n).rWalk =
      codeWalk ab.1 (quadrantInterleaveState ab.1 ab.2 n).rCount := by
  induction n with
  | zero => simp [quadrantInterleaveState, quadrantSplitStart, codeWalk_zero]
  | succ n ih =>
      simp only [quadrantInterleaveState]
      cases hphase : (quadrantInterleaveState ab.1 ab.2 n).phase with
      | r =>
          simp only [quadrantSplitAdvance, hphase]
          rw [codeWalk_succ_add, ih]
      | l =>
          simp only [quadrantSplitAdvance, hphase, ih]

/-- The `l` phase walk is the source walk read along the `l` codes consumed
so far. -/
theorem quadrantInterleaveState_lWalk (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ) :
    (quadrantInterleaveState ab.1 ab.2 n).lWalk =
      codeWalk ab.2 (quadrantInterleaveState ab.1 ab.2 n).lCount := by
  induction n with
  | zero => simp [quadrantInterleaveState, quadrantSplitStart, codeWalk_zero]
  | succ n ih =>
      simp only [quadrantInterleaveState]
      cases hphase : (quadrantInterleaveState ab.1 ab.2 n).phase with
      | r =>
          simp only [quadrantSplitAdvance, hphase, ih]
      | l =>
          simp only [quadrantSplitAdvance, hphase]
          rw [codeWalk_succ_add, ih]

/-- The two interleaved phase counts partition the number of codes read -/
theorem quadrantInterleaveState_counts (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ) :
    (quadrantInterleaveState ab.1 ab.2 n).rCount +
      (quadrantInterleaveState ab.1 ab.2 n).lCount = n := by
  have h := quadrantSplitState_counts (interleave ab) n
  simpa only [quadrantSplitState_interleave] using h

/-- The running `r` minimum never exceeds the current `r` walk coordinate. -/
theorem quadrantInterleaveState_rLMin_le (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ) :
    (quadrantInterleaveState ab.1 ab.2 n).rLMin ≤
      (quadrantInterleaveState ab.1 ab.2 n).rWalk.1 := by
  induction n with
  | zero => simp [quadrantInterleaveState, quadrantSplitStart]
  | succ n ih =>
      simp only [quadrantInterleaveState]
      cases hphase : (quadrantInterleaveState ab.1 ab.2 n).phase with
      | r =>
          simp [quadrantSplitAdvance, hphase]
          split_ifs <;> omega
      | l =>
          simpa [quadrantSplitAdvance, hphase] using ih

/-- The running `l` minimum never exceeds the current `l` walk coordinate. -/
theorem quadrantInterleaveState_lRMin_le (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ) :
    (quadrantInterleaveState ab.1 ab.2 n).lRMin ≤
      (quadrantInterleaveState ab.1 ab.2 n).lWalk.2 := by
  induction n with
  | zero => simp [quadrantInterleaveState, quadrantSplitStart]
  | succ n ih =>
      simp only [quadrantInterleaveState]
      cases hphase : (quadrantInterleaveState ab.1 ab.2 n).phase with
      | r =>
          simpa [quadrantSplitAdvance, hphase] using ih
      | l =>
          simp [quadrantSplitAdvance, hphase]
          split_ifs <;> omega

/-- The running first-coordinate minimum bounds every point of the consumed
prefix of the `r` input (`lem-quadrant-walk`, -/
theorem quadrantInterleaveState_rLMin_le_prefix (ab : (ℕ → Fin 3) × (ℕ → Fin 3))
    (n m : ℕ) (hm : m ≤ (quadrantInterleaveState ab.1 ab.2 n).rCount) :
    (quadrantInterleaveState ab.1 ab.2 n).rLMin ≤ (codeWalk ab.1 m).1 := by
  induction n with
  | zero =>
      have hm0 : m = 0 := by simpa [quadrantInterleaveState, quadrantSplitStart] using hm
      subst m
      simp [quadrantInterleaveState, quadrantSplitStart, codeWalk_zero]
  | succ n ih =>
      cases hphase : (quadrantInterleaveState ab.1 ab.2 n).phase with
      | r =>
          let s := quadrantInterleaveState ab.1 ab.2 n
          have hsphase : s.phase = .r := hphase
          have hstate : quadrantInterleaveState ab.1 ab.2 (n + 1) =
              quadrantSplitAdvance s (ab.1 (s.rCount + 1)) := by
            simp [quadrantInterleaveState, s, hphase]
          have hcount : (quadrantInterleaveState ab.1 ab.2 (n + 1)).rCount = s.rCount + 1 := by
            rw [hstate]
            simp [quadrantSplitAdvance, hsphase]
          by_cases hmk : m ≤ s.rCount
          · have hmin : (quadrantInterleaveState ab.1 ab.2 (n + 1)).rLMin ≤ s.rLMin := by
              rw [hstate]
              simp only [quadrantSplitAdvance, hsphase]
              split_ifs <;> omega
            exact le_trans hmin (ih (by simpa [s] using hmk))
          · have hmnew : m = (quadrantInterleaveState ab.1 ab.2 (n + 1)).rCount := by
              omega
            rw [hmnew]
            have hcur := quadrantInterleaveState_rLMin_le ab (n + 1)
            rw [quadrantInterleaveState_rWalk] at hcur
            exact hcur
      | l =>
          let s := quadrantInterleaveState ab.1 ab.2 n
          have hsphase : s.phase = .l := hphase
          have hstate : quadrantInterleaveState ab.1 ab.2 (n + 1) =
              quadrantSplitAdvance s (ab.2 (s.lCount + 1)) := by
            simp [quadrantInterleaveState, s, hphase]
          have hcount : (quadrantInterleaveState ab.1 ab.2 (n + 1)).rCount = s.rCount := by
            rw [hstate]
            simp [quadrantSplitAdvance, hsphase]
          have hmin : (quadrantInterleaveState ab.1 ab.2 (n + 1)).rLMin = s.rLMin := by
            rw [hstate]
            simp [quadrantSplitAdvance, hsphase]
          rw [hmin]
          have hm' : m ≤ (quadrantInterleaveState ab.1 ab.2 n).rCount := by
            rw [← hcount]
            exact hm
          exact ih hm'

/-- The running second-coordinate minimum bounds every point of the consumed
prefix of the `l` input (`lem-quadrant-walk`, -/
theorem quadrantInterleaveState_lRMin_le_prefix (ab : (ℕ → Fin 3) × (ℕ → Fin 3))
    (n m : ℕ) (hm : m ≤ (quadrantInterleaveState ab.1 ab.2 n).lCount) :
    (quadrantInterleaveState ab.1 ab.2 n).lRMin ≤ (codeWalk ab.2 m).2 := by
  induction n with
  | zero =>
      have hm0 : m = 0 := by simpa [quadrantInterleaveState, quadrantSplitStart] using hm
      subst m
      simp [quadrantInterleaveState, quadrantSplitStart, codeWalk_zero]
  | succ n ih =>
      cases hphase : (quadrantInterleaveState ab.1 ab.2 n).phase with
      | r =>
          let s := quadrantInterleaveState ab.1 ab.2 n
          have hsphase : s.phase = .r := hphase
          have hstate : quadrantInterleaveState ab.1 ab.2 (n + 1) =
              quadrantSplitAdvance s (ab.1 (s.rCount + 1)) := by
            simp [quadrantInterleaveState, s, hphase]
          have hcount : (quadrantInterleaveState ab.1 ab.2 (n + 1)).lCount = s.lCount := by
            rw [hstate]
            simp [quadrantSplitAdvance, hsphase]
          have hmin : (quadrantInterleaveState ab.1 ab.2 (n + 1)).lRMin = s.lRMin := by
            rw [hstate]
            simp [quadrantSplitAdvance, hsphase]
          rw [hmin]
          have hm' : m ≤ (quadrantInterleaveState ab.1 ab.2 n).lCount := by
            rw [← hcount]
            exact hm
          exact ih hm'
      | l =>
          let s := quadrantInterleaveState ab.1 ab.2 n
          have hsphase : s.phase = .l := hphase
          have hstate : quadrantInterleaveState ab.1 ab.2 (n + 1) =
              quadrantSplitAdvance s (ab.2 (s.lCount + 1)) := by
            simp [quadrantInterleaveState, s, hphase]
          have hcount : (quadrantInterleaveState ab.1 ab.2 (n + 1)).lCount = s.lCount + 1 := by
            rw [hstate]
            simp [quadrantSplitAdvance, hsphase]
          by_cases hmk : m ≤ s.lCount
          · have hmin : (quadrantInterleaveState ab.1 ab.2 (n + 1)).lRMin ≤ s.lRMin := by
              rw [hstate]
              simp only [quadrantSplitAdvance, hsphase]
              split_ifs <;> omega
            exact le_trans hmin (ih (by simpa [s] using hmk))
          · have hmnew : m = (quadrantInterleaveState ab.1 ab.2 (n + 1)).lCount := by
              omega
            rw [hmnew]
            have hcur := quadrantInterleaveState_lRMin_le ab (n + 1)
            rw [quadrantInterleaveState_lWalk] at hcur
            exact hcur

private theorem quadrantInterleaveState_rPhase_finishes (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) :
    ∀ d n, (quadrantInterleaveState ab.1 ab.2 n).phase = .r →
      (codeWalk ab.1 ((quadrantInterleaveState ab.1 ab.2 n).rCount + d + 1)).1 <
        (quadrantInterleaveState ab.1 ab.2 n).rLMin →
      ∃ m, n < m ∧ (quadrantInterleaveState ab.1 ab.2 m).phase = .l := by
  intro d
  induction d with
  | zero =>
      intro n hphase hbelow
      let s := quadrantInterleaveState ab.1 ab.2 n
      have hsphase : s.phase = .r := hphase
      have hstepwalk : codeWalk ab.1 (s.rCount + 1) =
          s.rWalk + lazyTwoDimensionalStep (ab.1 (s.rCount + 1)) := by
        rw [codeWalk_succ_add]
        have hw : s.rWalk = codeWalk ab.1 s.rCount := by
          simpa [s] using quadrantInterleaveState_rWalk ab n
        rw [hw]
      have hbelow0 : (codeWalk ab.1 (s.rCount + 1)).1 < s.rLMin := by
        simpa [s, Nat.zero_add] using hbelow
      have hhit : s.rWalk.1 + (lazyTwoDimensionalStep (ab.1 (s.rCount + 1))).1 < s.rLMin := by
        rw [hstepwalk] at hbelow0
        simpa only [Prod.fst_add] using hbelow0
      have hstate : quadrantInterleaveState ab.1 ab.2 (n + 1) =
          quadrantSplitAdvance s (ab.1 (s.rCount + 1)) := by
        simp [quadrantInterleaveState, s, hphase]
      refine ⟨n + 1, by omega, ?_⟩
      rw [hstate]
      simp [quadrantSplitAdvance, hsphase, hhit]
  | succ d ih =>
      intro n hphase hbelow
      let s := quadrantInterleaveState ab.1 ab.2 n
      have hsphase : s.phase = .r := hphase
      have hstate : quadrantInterleaveState ab.1 ab.2 (n + 1) =
          quadrantSplitAdvance s (ab.1 (s.rCount + 1)) := by
        simp [quadrantInterleaveState, s, hphase]
      by_cases hhit : s.rWalk.1 + (lazyTwoDimensionalStep (ab.1 (s.rCount + 1))).1 < s.rLMin
      · refine ⟨n + 1, by omega, ?_⟩
        rw [hstate]
        simp [quadrantSplitAdvance, hsphase, hhit]
      · have hphase' : (quadrantInterleaveState ab.1 ab.2 (n + 1)).phase = .r := by
          rw [hstate]
          simp [quadrantSplitAdvance, hsphase, hhit]
        have hcount : (quadrantInterleaveState ab.1 ab.2 (n + 1)).rCount = s.rCount + 1 := by
          rw [hstate]
          simp [quadrantSplitAdvance, hsphase]
        have hmin : (quadrantInterleaveState ab.1 ab.2 (n + 1)).rLMin = s.rLMin := by
          rw [hstate]
          simp [quadrantSplitAdvance, hsphase, hhit]
        have hidx : s.rCount + (d + 1) + 1 =
            (quadrantInterleaveState ab.1 ab.2 (n + 1)).rCount + d + 1 := by
          rw [hcount]
          omega
        have hbelow' :
            (codeWalk ab.1 ((quadrantInterleaveState ab.1 ab.2 (n + 1)).rCount + d + 1)).1 <
              (quadrantInterleaveState ab.1 ab.2 (n + 1)).rLMin := by
          rw [← hidx, hmin]
          simpa [Nat.succ_eq_add_one] using hbelow
        obtain ⟨m, hnm, hphaseM⟩ := ih (n + 1) hphase' hbelow'
        exact ⟨m, by omega, hphaseM⟩

private theorem quadrantInterleaveState_lPhase_finishes (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) :
    ∀ d n, (quadrantInterleaveState ab.1 ab.2 n).phase = .l →
      (codeWalk ab.2 ((quadrantInterleaveState ab.1 ab.2 n).lCount + d + 1)).2 <
        (quadrantInterleaveState ab.1 ab.2 n).lRMin →
      ∃ m, n < m ∧ (quadrantInterleaveState ab.1 ab.2 m).phase = .r := by
  intro d
  induction d with
  | zero =>
      intro n hphase hbelow
      let s := quadrantInterleaveState ab.1 ab.2 n
      have hsphase : s.phase = .l := hphase
      have hstepwalk : codeWalk ab.2 (s.lCount + 1) =
          s.lWalk + lazyTwoDimensionalStep (ab.2 (s.lCount + 1)) := by
        rw [codeWalk_succ_add]
        have hw : s.lWalk = codeWalk ab.2 s.lCount := by
          simpa [s] using quadrantInterleaveState_lWalk ab n
        rw [hw]
      have hbelow0 : (codeWalk ab.2 (s.lCount + 1)).2 < s.lRMin := by
        simpa [s, Nat.zero_add] using hbelow
      have hhit : s.lWalk.2 + (lazyTwoDimensionalStep (ab.2 (s.lCount + 1))).2 < s.lRMin := by
        rw [hstepwalk] at hbelow0
        simpa only [Prod.snd_add] using hbelow0
      have hstate : quadrantInterleaveState ab.1 ab.2 (n + 1) =
          quadrantSplitAdvance s (ab.2 (s.lCount + 1)) := by
        simp [quadrantInterleaveState, s, hphase]
      refine ⟨n + 1, by omega, ?_⟩
      rw [hstate]
      simp [quadrantSplitAdvance, hsphase, hhit]
  | succ d ih =>
      intro n hphase hbelow
      let s := quadrantInterleaveState ab.1 ab.2 n
      have hsphase : s.phase = .l := hphase
      have hstate : quadrantInterleaveState ab.1 ab.2 (n + 1) =
          quadrantSplitAdvance s (ab.2 (s.lCount + 1)) := by
        simp [quadrantInterleaveState, s, hphase]
      by_cases hhit : s.lWalk.2 + (lazyTwoDimensionalStep (ab.2 (s.lCount + 1))).2 < s.lRMin
      · refine ⟨n + 1, by omega, ?_⟩
        rw [hstate]
        simp [quadrantSplitAdvance, hsphase, hhit]
      · have hphase' : (quadrantInterleaveState ab.1 ab.2 (n + 1)).phase = .l := by
          rw [hstate]
          simp [quadrantSplitAdvance, hsphase, hhit]
        have hcount : (quadrantInterleaveState ab.1 ab.2 (n + 1)).lCount = s.lCount + 1 := by
          rw [hstate]
          simp [quadrantSplitAdvance, hsphase]
        have hmin : (quadrantInterleaveState ab.1 ab.2 (n + 1)).lRMin = s.lRMin := by
          rw [hstate]
          simp [quadrantSplitAdvance, hsphase, hhit]
        have hidx : s.lCount + (d + 1) + 1 =
            (quadrantInterleaveState ab.1 ab.2 (n + 1)).lCount + d + 1 := by
          rw [hcount]
          omega
        have hbelow' :
            (codeWalk ab.2 ((quadrantInterleaveState ab.1 ab.2 (n + 1)).lCount + d + 1)).2 <
              (quadrantInterleaveState ab.1 ab.2 (n + 1)).lRMin := by
          rw [← hidx, hmin]
          simpa [Nat.succ_eq_add_one] using hbelow
        obtain ⟨m, hnm, hphaseM⟩ := ih (n + 1) hphase' hbelow'
        exact ⟨m, by omega, hphaseM⟩

/-- If the first input hits every integer level, every active `r` phase
terminates after finitely many input codes (`lem-quadrant-walk`, -/
theorem quadrantInterleaveState_eventually_l (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ)
    (hphase : (quadrantInterleaveState ab.1 ab.2 n).phase = .r)
    (hHit : ∀ z : ℤ, ∃ m, (codeWalk ab.1 m).1 = z) :
    ∃ m, n < m ∧ (quadrantInterleaveState ab.1 ab.2 m).phase = .l := by
  let s := quadrantInterleaveState ab.1 ab.2 n
  obtain ⟨j, hj⟩ := hHit (s.rLMin - 1)
  have hnot : ¬ j ≤ s.rCount := by
    intro hjle
    have hmin : s.rLMin ≤ (codeWalk ab.1 j).1 := by
      simpa [s] using quadrantInterleaveState_rLMin_le_prefix ab n j (by simpa [s] using hjle)
    rw [hj] at hmin
    omega
  have hjgt : s.rCount < j := by omega
  let d := j - (s.rCount + 1)
  have hd : j = s.rCount + d + 1 := by dsimp [d]; omega
  have hbelow : (codeWalk ab.1 (s.rCount + d + 1)).1 < s.rLMin := by
    rw [← hd, hj]
    omega
  have hphase' : (quadrantInterleaveState ab.1 ab.2 n).phase = .r := by
    simpa [s] using hphase
  exact quadrantInterleaveState_rPhase_finishes ab d n hphase' (by simpa [s] using hbelow)

/-- If the second input hits every integer level, every active `l` phase
terminates after finitely many input codes (`lem-quadrant-walk`, -/
theorem quadrantInterleaveState_eventually_r (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ)
    (hphase : (quadrantInterleaveState ab.1 ab.2 n).phase = .l)
    (hHit : ∀ z : ℤ, ∃ m, (codeWalk ab.2 m).2 = z) :
    ∃ m, n < m ∧ (quadrantInterleaveState ab.1 ab.2 m).phase = .r := by
  let s := quadrantInterleaveState ab.1 ab.2 n
  obtain ⟨j, hj⟩ := hHit (s.lRMin - 1)
  have hnot : ¬ j ≤ s.lCount := by
    intro hjle
    have hmin : s.lRMin ≤ (codeWalk ab.2 j).2 := by
      simpa [s] using quadrantInterleaveState_lRMin_le_prefix ab n j (by simpa [s] using hjle)
    rw [hj] at hmin
    omega
  have hjgt : s.lCount < j := by omega
  let d := j - (s.lCount + 1)
  have hd : j = s.lCount + d + 1 := by dsimp [d]; omega
  have hbelow : (codeWalk ab.2 (s.lCount + d + 1)).2 < s.lRMin := by
    rw [← hd, hj]
    omega
  exact quadrantInterleaveState_lPhase_finishes ab d n (by simpa [s] using hphase)
    (by simpa [s] using hbelow)

private theorem quadrantInterleaveState_eventually_phase_r
    (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ)
    (hHit : ∀ z : ℤ, ∃ m, (codeWalk ab.2 m).2 = z) :
    ∃ m, n ≤ m ∧ (quadrantInterleaveState ab.1 ab.2 m).phase = .r := by
  cases hphase : (quadrantInterleaveState ab.1 ab.2 n).phase with
  | r => exact ⟨n, le_rfl, hphase⟩
  | l =>
      obtain ⟨m, hnm, hm⟩ := quadrantInterleaveState_eventually_r ab n hphase hHit
      exact ⟨m, by omega, hm⟩

private theorem quadrantInterleaveState_eventually_phase_l
    (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ)
    (hHit : ∀ z : ℤ, ∃ m, (codeWalk ab.1 m).1 = z) :
    ∃ m, n ≤ m ∧ (quadrantInterleaveState ab.1 ab.2 m).phase = .l := by
  cases hphase : (quadrantInterleaveState ab.1 ab.2 n).phase with
  | r =>
      obtain ⟨m, hnm, hm⟩ := quadrantInterleaveState_eventually_l ab n hphase hHit
      exact ⟨m, by omega, hm⟩
  | l => exact ⟨n, le_rfl, hphase⟩

/-- The `r` count increases by one exactly when the next code is read in the -/
theorem quadrantInterleaveState_rCount_succ (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ) :
    (quadrantInterleaveState ab.1 ab.2 (n + 1)).rCount =
      if (quadrantInterleaveState ab.1 ab.2 n).phase = .r then
        (quadrantInterleaveState ab.1 ab.2 n).rCount + 1
      else (quadrantInterleaveState ab.1 ab.2 n).rCount := by
  change (quadrantSplitAdvance (quadrantInterleaveState ab.1 ab.2 n)
      (match (quadrantInterleaveState ab.1 ab.2 n).phase with
      | .r => ab.1 ((quadrantInterleaveState ab.1 ab.2 n).rCount + 1)
      | .l => ab.2 ((quadrantInterleaveState ab.1 ab.2 n).lCount + 1))).rCount = _
  rw [quadrantSplitAdvance_rCount]

/-- The `l` count increases by one exactly when the next code is read in the -/
theorem quadrantInterleaveState_lCount_succ (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ) :
    (quadrantInterleaveState ab.1 ab.2 (n + 1)).lCount =
      if (quadrantInterleaveState ab.1 ab.2 n).phase = .l then
        (quadrantInterleaveState ab.1 ab.2 n).lCount + 1
      else (quadrantInterleaveState ab.1 ab.2 n).lCount := by
  change (quadrantSplitAdvance (quadrantInterleaveState ab.1 ab.2 n)
      (match (quadrantInterleaveState ab.1 ab.2 n).phase with
      | .r => ab.1 ((quadrantInterleaveState ab.1 ab.2 n).rCount + 1)
      | .l => ab.2 ((quadrantInterleaveState ab.1 ab.2 n).lCount + 1))).lCount = _
  rw [quadrantSplitAdvance_lCount]

/-- The `r` phase count is unbounded when the second input's walk hits every -/
theorem quadrantInterleaveState_rCount_unbounded (ab : (ℕ → Fin 3) × (ℕ → Fin 3))
    (hHit : ∀ z : ℤ, ∃ m, (codeWalk ab.2 m).2 = z) :
    ∀ k, ∃ n, k ≤ (quadrantInterleaveState ab.1 ab.2 n).rCount := by
  intro k
  induction k with
  | zero => exact ⟨0, by simp [quadrantInterleaveState, quadrantSplitStart]⟩
  | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hnm, hphase⟩ := quadrantInterleaveState_eventually_phase_r ab n hHit
      have hmono : (quadrantInterleaveState ab.1 ab.2 n).rCount ≤
          (quadrantInterleaveState ab.1 ab.2 m).rCount := by
        have h := quadrantSplitState_rCount_mono (interleave ab) n m hnm
        simpa only [quadrantSplitState_interleave] using h
      have hnext : (quadrantInterleaveState ab.1 ab.2 (m + 1)).rCount =
          (quadrantInterleaveState ab.1 ab.2 m).rCount + 1 := by
        have h := quadrantInterleaveState_rCount_succ ab m
        simpa [hphase] using h
      refine ⟨m + 1, ?_⟩
      rw [hnext]
      omega

/-- The `l` phase count is unbounded when the first input's walk hits every -/
theorem quadrantInterleaveState_lCount_unbounded (ab : (ℕ → Fin 3) × (ℕ → Fin 3))
    (hHit : ∀ z : ℤ, ∃ m, (codeWalk ab.1 m).1 = z) :
    ∀ k, ∃ n, k ≤ (quadrantInterleaveState ab.1 ab.2 n).lCount := by
  intro k
  induction k with
  | zero => exact ⟨0, by simp [quadrantInterleaveState, quadrantSplitStart]⟩
  | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hnm, hphase⟩ := quadrantInterleaveState_eventually_phase_l ab n hHit
      have hmono : (quadrantInterleaveState ab.1 ab.2 n).lCount ≤
          (quadrantInterleaveState ab.1 ab.2 m).lCount := by
        have h := quadrantSplitState_lCount_mono (interleave ab) n m hnm
        simpa only [quadrantSplitState_interleave] using h
      have hnext : (quadrantInterleaveState ab.1 ab.2 (m + 1)).lCount =
          (quadrantInterleaveState ab.1 ab.2 m).lCount + 1 := by
        have h := quadrantInterleaveState_lCount_succ ab m
        simpa [hphase] using h
      refine ⟨m + 1, ?_⟩
      rw [hnext]
      omega

/-- Under the two level-hitting assumptions, each phase count eventually
exceeds every fixed bound (`lem-quadrant-walk`, -/
theorem quadrantInterleaveState_counts_tend_to_infinity
    (ab : (ℕ → Fin 3) × (ℕ → Fin 3))
    (hHitA : ∀ z : ℤ, ∃ m, (codeWalk ab.1 m).1 = z)
    (hHitB : ∀ z : ℤ, ∃ m, (codeWalk ab.2 m).2 = z) :
    ∀ k, ∃ N, ∀ n ≥ N,
      k ≤ (quadrantInterleaveState ab.1 ab.2 n).rCount ∧
      k ≤ (quadrantInterleaveState ab.1 ab.2 n).lCount := by
  intro k
  obtain ⟨nr, hnr⟩ := quadrantInterleaveState_rCount_unbounded ab hHitB k
  obtain ⟨nl, hnl⟩ := quadrantInterleaveState_lCount_unbounded ab hHitA k
  refine ⟨max nr nl, ?_⟩
  intro n hn
  have hnr' : nr ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnl' : nl ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hr := quadrantSplitState_rCount_mono (interleave ab) nr n hnr'
  have hl := quadrantSplitState_lCount_mono (interleave ab) nl n hnl'
  have hr' : (quadrantInterleaveState ab.1 ab.2 nr).rCount ≤
      (quadrantInterleaveState ab.1 ab.2 n).rCount := by
    simpa only [quadrantSplitState_interleave] using hr
  have hl' : (quadrantInterleaveState ab.1 ab.2 nl).lCount ≤
      (quadrantInterleaveState ab.1 ab.2 n).lCount := by
    simpa only [quadrantSplitState_interleave] using hl
  exact ⟨le_trans hnr hr', le_trans hnl hl'⟩

private theorem quadrantInterleaveState_exists_rStep
    (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (i : ℕ) (hi : 0 < i)
    (hunbounded : ∀ k, ∃ n, k ≤ (quadrantInterleaveState ab.1 ab.2 n).rCount) :
    ∃ n, (quadrantInterleaveState ab.1 ab.2 n).phase = .r ∧
      (quadrantInterleaveState ab.1 ab.2 n).rCount + 1 = i := by
  classical
  obtain ⟨N, hN⟩ := hunbounded i
  let P : ℕ → Prop := fun n => i ≤ (quadrantInterleaveState ab.1 ab.2 n).rCount
  have hP : ∃ n, P n := ⟨N, hN⟩
  let n := Nat.find hP
  have hcurr : i ≤ (quadrantInterleaveState ab.1 ab.2 n).rCount := Nat.find_spec hP
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0] at hcurr
    simp [quadrantInterleaveState, quadrantSplitStart] at hcurr
    omega
  obtain ⟨p, hp⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hprev : ¬ i ≤ (quadrantInterleaveState ab.1 ab.2 p).rCount := by
    have hp' : p < n := by omega
    have h := Nat.find_min hP hp'
    simpa [P] using h
  have hphase : (quadrantInterleaveState ab.1 ab.2 p).phase = .r := by
    have hcurr' := hcurr
    rw [hp, quadrantInterleaveState_rCount_succ] at hcurr'
    by_cases hphase : (quadrantInterleaveState ab.1 ab.2 p).phase = .r
    · exact hphase
    · simp [hphase] at hcurr'
      omega
  have hcount : (quadrantInterleaveState ab.1 ab.2 p).rCount + 1 = i := by
    have hcurr' := hcurr
    rw [hp, quadrantInterleaveState_rCount_succ] at hcurr'
    simp [hphase] at hcurr'
    omega
  exact ⟨p, hphase, hcount⟩

private theorem quadrantInterleaveState_exists_lStep
    (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (i : ℕ) (hi : 0 < i)
    (hunbounded : ∀ k, ∃ n, k ≤ (quadrantInterleaveState ab.1 ab.2 n).lCount) :
    ∃ n, (quadrantInterleaveState ab.1 ab.2 n).phase = .l ∧
      (quadrantInterleaveState ab.1 ab.2 n).lCount + 1 = i := by
  classical
  obtain ⟨N, hN⟩ := hunbounded i
  let P : ℕ → Prop := fun n => i ≤ (quadrantInterleaveState ab.1 ab.2 n).lCount
  have hP : ∃ n, P n := ⟨N, hN⟩
  let n := Nat.find hP
  have hcurr : i ≤ (quadrantInterleaveState ab.1 ab.2 n).lCount := Nat.find_spec hP
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0] at hcurr
    simp [quadrantInterleaveState, quadrantSplitStart] at hcurr
    omega
  obtain ⟨p, hp⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hprev : ¬ i ≤ (quadrantInterleaveState ab.1 ab.2 p).lCount := by
    have hp' : p < n := by omega
    have h := Nat.find_min hP hp'
    simpa [P] using h
  have hphase : (quadrantInterleaveState ab.1 ab.2 p).phase = .l := by
    have hcurr' := hcurr
    rw [hp, quadrantInterleaveState_lCount_succ] at hcurr'
    by_cases hphase : (quadrantInterleaveState ab.1 ab.2 p).phase = .l
    · exact hphase
    · simp [hphase] at hcurr'
      omega
  have hcount : (quadrantInterleaveState ab.1 ab.2 p).lCount + 1 = i := by
    have hcurr' := hcurr
    rw [hp, quadrantInterleaveState_lCount_succ] at hcurr'
    simp [hphase] at hcurr'
    omega
  exact ⟨p, hphase, hcount⟩

/-- Splitting the interleaving recovers both input streams when they start
with the dummy code and hit every integer level in the switching coordinates -/
theorem phaseSplit_interleave (ab : (ℕ → Fin 3) × (ℕ → Fin 3))
    (hzeroA : ab.1 0 = 0) (hzeroB : ab.2 0 = 0)
    (hHitA : ∀ z : ℤ, ∃ m, (codeWalk ab.1 m).1 = z)
    (hHitB : ∀ z : ℤ, ∃ m, (codeWalk ab.2 m).2 = z) :
    phaseSplit (interleave ab) = ab := by
  have hunboundedR := quadrantInterleaveState_rCount_unbounded ab hHitB
  have hunboundedL := quadrantInterleaveState_lCount_unbounded ab hHitA
  apply Prod.ext
  · funext i
    cases i with
    | zero => simp [phaseSplit, hzeroA]
    | succ k =>
        obtain ⟨n, hphase, hcount⟩ :=
          quadrantInterleaveState_exists_rStep ab (k + 1) (by omega) hunboundedR
        have hphase' : (quadrantSplitState (interleave ab) n).phase = .r := by
          simpa only [quadrantSplitState_interleave] using hphase
        have hsplit := phaseSplit_rCode_at_step (interleave ab) n hphase'
        have hsplit' : (phaseSplit (interleave ab)).1
            ((quadrantInterleaveState ab.1 ab.2 n).rCount + 1) = interleave ab (n + 1) := by
          simpa only [quadrantSplitState_interleave] using hsplit
        rw [hcount] at hsplit'
        have hout : interleave ab (n + 1) = ab.1 (k + 1) := by
          calc
            interleave ab (n + 1) = ab.1 ((quadrantInterleaveState ab.1 ab.2 n).rCount + 1) := by
              simp [interleave, hphase]
            _ = ab.1 (k + 1) := by rw [hcount]
        rw [hout] at hsplit'
        exact hsplit'
  · funext i
    cases i with
    | zero => simp [phaseSplit, hzeroB]
    | succ k =>
        obtain ⟨n, hphase, hcount⟩ :=
          quadrantInterleaveState_exists_lStep ab (k + 1) (by omega) hunboundedL
        have hphase' : (quadrantSplitState (interleave ab) n).phase = .l := by
          simpa only [quadrantSplitState_interleave] using hphase
        have hsplit := phaseSplit_lCode_at_step (interleave ab) n hphase'
        have hsplit' : (phaseSplit (interleave ab)).2
            ((quadrantInterleaveState ab.1 ab.2 n).lCount + 1) = interleave ab (n + 1) := by
          simpa only [quadrantSplitState_interleave] using hsplit
        rw [hcount] at hsplit'
        have hout : interleave ab (n + 1) = ab.2 (k + 1) := by
          calc
            interleave ab (n + 1) = ab.2 ((quadrantInterleaveState ab.1 ab.2 n).lCount + 1) := by
              simp [interleave, hphase]
            _ = ab.2 (k + 1) := by rw [hcount]
        rw [hout] at hsplit'
        exact hsplit'

private theorem quadrantSplitState_eq_of_prefix_eq (ω ν : ℕ → Fin 3) (n : ℕ)
    (h : ∀ i ≤ n, ω i = ν i) : quadrantSplitState ω n = quadrantSplitState ν n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hrec : quadrantSplitState ω n = quadrantSplitState ν n := by
        apply ih
        intro i hi
        exact h i (by omega)
      change quadrantSplitAdvance (quadrantSplitState ω n) (ω (n + 1)) =
        quadrantSplitAdvance (quadrantSplitState ν n) (ν (n + 1))
      rw [hrec, h (n + 1) (by omega)]

private theorem phaseSplit_interleave_prefix_matches
    (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (ω : ℕ → Fin 3) (n : ℕ)
    (hprefix : ∀ i ≤ n, interleave ab i = ω i) :
    (∀ i, 0 < i → i ≤ (quadrantSplitState ω n).rCount →
      (phaseSplit ω).1 i = ab.1 i) ∧
    (∀ i, 0 < i → i ≤ (quadrantSplitState ω n).lCount →
      (phaseSplit ω).2 i = ab.2 i) := by
  have hstep : ∀ j ≤ n,
      (∀ i, 0 < i → i ≤ (quadrantSplitState ω j).rCount →
        (phaseSplit ω).1 i = ab.1 i) ∧
      (∀ i, 0 < i → i ≤ (quadrantSplitState ω j).lCount →
        (phaseSplit ω).2 i = ab.2 i) := by
    intro j hj
    induction j with
    | zero =>
        constructor <;> intro i hi hcount
        · have hcount' : i ≤ 0 := by simpa [quadrantSplitState, quadrantSplitStart] using hcount
          omega
        · have hcount' : i ≤ 0 := by simpa [quadrantSplitState, quadrantSplitStart] using hcount
          omega
    | succ j ih =>
        have hstate : quadrantInterleaveState ab.1 ab.2 j = quadrantSplitState ω j := by
          calc
            quadrantInterleaveState ab.1 ab.2 j = quadrantSplitState (interleave ab) j :=
              (quadrantSplitState_interleave ab j).symm
            _ = quadrantSplitState ω j :=
              quadrantSplitState_eq_of_prefix_eq (interleave ab) ω j
                (fun i hi => hprefix i (by omega))
        cases hphase : (quadrantSplitState ω j).phase with
        | r =>
            have hcountR : (quadrantSplitState ω (j + 1)).rCount =
                (quadrantSplitState ω j).rCount + 1 := by
              rw [quadrantSplitState, quadrantSplitAdvance_rCount]
              simp [hphase]
            have hcountL : (quadrantSplitState ω (j + 1)).lCount =
                (quadrantSplitState ω j).lCount := by
              rw [quadrantSplitState, quadrantSplitAdvance_lCount]
              simp [hphase]
            have hphaseAb : (quadrantInterleaveState ab.1 ab.2 j).phase = .r := by
              rw [hstate]
              exact hphase
            have hcountAb : (quadrantInterleaveState ab.1 ab.2 j).rCount =
                (quadrantSplitState ω j).rCount := congrArg QuadrantSplitState.rCount hstate
            have hout : interleave ab (j + 1) = ω (j + 1) := hprefix (j + 1) (by omega)
            have hinput : ab.1 ((quadrantSplitState ω j).rCount + 1) = ω (j + 1) := by
              have hformula : interleave ab (j + 1) =
                  ab.1 ((quadrantSplitState ω j).rCount + 1) := by
                simp [interleave, hphaseAb, hcountAb]
              calc
                ab.1 ((quadrantSplitState ω j).rCount + 1) = interleave ab (j + 1) := hformula.symm
                _ = ω (j + 1) := hout
            have hsplit := phaseSplit_rCode_at_step ω j hphase
            have hnew : (phaseSplit ω).1 ((quadrantSplitState ω j).rCount + 1) =
                ab.1 ((quadrantSplitState ω j).rCount + 1) := hsplit.trans hinput.symm
            constructor
            · intro i hi hcount
              by_cases hold : i ≤ (quadrantSplitState ω j).rCount
              · exact (ih (by omega)).1 i hi hold
              · have hi' : i = (quadrantSplitState ω j).rCount + 1 := by omega
                rw [hi']
                exact hnew
            · intro i hi hcount
              exact (ih (by omega)).2 i hi (by simpa [hcountL] using hcount)
        | l =>
            have hcountR : (quadrantSplitState ω (j + 1)).rCount =
                (quadrantSplitState ω j).rCount := by
              rw [quadrantSplitState, quadrantSplitAdvance_rCount]
              simp [hphase]
            have hcountL : (quadrantSplitState ω (j + 1)).lCount =
                (quadrantSplitState ω j).lCount + 1 := by
              rw [quadrantSplitState, quadrantSplitAdvance_lCount]
              simp [hphase]
            have hphaseAb : (quadrantInterleaveState ab.1 ab.2 j).phase = .l := by
              rw [hstate]
              exact hphase
            have hcountAb : (quadrantInterleaveState ab.1 ab.2 j).lCount =
                (quadrantSplitState ω j).lCount := congrArg QuadrantSplitState.lCount hstate
            have hout : interleave ab (j + 1) = ω (j + 1) := hprefix (j + 1) (by omega)
            have hinput : ab.2 ((quadrantSplitState ω j).lCount + 1) = ω (j + 1) := by
              have hformula : interleave ab (j + 1) =
                  ab.2 ((quadrantSplitState ω j).lCount + 1) := by
                simp [interleave, hphaseAb, hcountAb]
              calc
                ab.2 ((quadrantSplitState ω j).lCount + 1) = interleave ab (j + 1) := hformula.symm
                _ = ω (j + 1) := hout
            have hsplit := phaseSplit_lCode_at_step ω j hphase
            have hnew : (phaseSplit ω).2 ((quadrantSplitState ω j).lCount + 1) =
                ab.2 ((quadrantSplitState ω j).lCount + 1) := hsplit.trans hinput.symm
            constructor
            · intro i hi hcount
              exact (ih (by omega)).1 i hi (by simpa [hcountR] using hcount)
            · intro i hi hcount
              by_cases hold : i ≤ (quadrantSplitState ω j).lCount
              · exact (ih (by omega)).2 i hi hold
              · have hi' : i = (quadrantSplitState ω j).lCount + 1 := by omega
                rw [hi']
                exact hnew
  exact hstep n le_rfl

private theorem interleave_prefix_eq_of_split_prefix
    (ab : (ℕ → Fin 3) × (ℕ → Fin 3)) (ω : ℕ → Fin 3) (n : ℕ)
    (hzero : ω 0 = 0)
    (hA : ∀ i, 0 < i → i ≤ (quadrantSplitState ω n).rCount →
      ab.1 i = (phaseSplit ω).1 i)
    (hB : ∀ i, 0 < i → i ≤ (quadrantSplitState ω n).lCount →
      ab.2 i = (phaseSplit ω).2 i) :
    ∀ i ≤ n, interleave ab i = ω i := by
  have hstate : ∀ j ≤ n,
      quadrantInterleaveState ab.1 ab.2 j = quadrantSplitState ω j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
        have hprev : quadrantInterleaveState ab.1 ab.2 j = quadrantSplitState ω j := ih (by omega)
        cases hphase : (quadrantSplitState ω j).phase with
        | r =>
            have hcountStep : (quadrantSplitState ω (j + 1)).rCount =
                (quadrantSplitState ω j).rCount + 1 := by
              rw [quadrantSplitState, quadrantSplitAdvance_rCount]
              simp [hphase]
            have hcountBound : (quadrantSplitState ω j).rCount + 1 ≤
                (quadrantSplitState ω n).rCount := by
              have hmono := quadrantSplitState_rCount_mono ω (j + 1) n (by omega)
              simpa [hcountStep] using hmono
            have hsplit := phaseSplit_rCode_at_step ω j hphase
            have hcode : ab.1 ((quadrantSplitState ω j).rCount + 1) = ω (j + 1) := by
              exact (hA _ (by omega) hcountBound).trans hsplit
            have hphaseAb : (quadrantInterleaveState ab.1 ab.2 j).phase = .r := by
              rw [hprev]
              exact hphase
            have hcountAb : (quadrantInterleaveState ab.1 ab.2 j).rCount =
                (quadrantSplitState ω j).rCount := congrArg QuadrantSplitState.rCount hprev
            have hcodeAb : ab.1 ((quadrantInterleaveState ab.1 ab.2 j).rCount + 1) =
                ω (j + 1) := by
              rw [hcountAb]
              exact hcode
            calc
              quadrantInterleaveState ab.1 ab.2 (j + 1) =
                  quadrantSplitAdvance (quadrantInterleaveState ab.1 ab.2 j)
                    (ab.1 ((quadrantInterleaveState ab.1 ab.2 j).rCount + 1)) := by
                simp [quadrantInterleaveState, hphaseAb]
              _ = quadrantSplitAdvance (quadrantSplitState ω j) (ω (j + 1)) := by
                rw [hcodeAb, hprev]
              _ = quadrantSplitState ω (j + 1) := by rw [quadrantSplitState]
        | l =>
            have hcountStep : (quadrantSplitState ω (j + 1)).lCount =
                (quadrantSplitState ω j).lCount + 1 := by
              rw [quadrantSplitState, quadrantSplitAdvance_lCount]
              simp [hphase]
            have hcountBound : (quadrantSplitState ω j).lCount + 1 ≤
                (quadrantSplitState ω n).lCount := by
              have hmono := quadrantSplitState_lCount_mono ω (j + 1) n (by omega)
              simpa [hcountStep] using hmono
            have hsplit := phaseSplit_lCode_at_step ω j hphase
            have hcode : ab.2 ((quadrantSplitState ω j).lCount + 1) = ω (j + 1) := by
              exact (hB _ (by omega) hcountBound).trans hsplit
            have hphaseAb : (quadrantInterleaveState ab.1 ab.2 j).phase = .l := by
              rw [hprev]
              exact hphase
            have hcountAb : (quadrantInterleaveState ab.1 ab.2 j).lCount =
                (quadrantSplitState ω j).lCount := congrArg QuadrantSplitState.lCount hprev
            have hcodeAb : ab.2 ((quadrantInterleaveState ab.1 ab.2 j).lCount + 1) =
                ω (j + 1) := by
              rw [hcountAb]
              exact hcode
            calc
              quadrantInterleaveState ab.1 ab.2 (j + 1) =
                  quadrantSplitAdvance (quadrantInterleaveState ab.1 ab.2 j)
                    (ab.2 ((quadrantInterleaveState ab.1 ab.2 j).lCount + 1)) := by
                simp [quadrantInterleaveState, hphaseAb]
              _ = quadrantSplitAdvance (quadrantSplitState ω j) (ω (j + 1)) := by
                rw [hcodeAb, hprev]
              _ = quadrantSplitState ω (j + 1) := by rw [quadrantSplitState]
  intro i hi
  cases i with
  | zero => simp [interleave_zero, hzero]
  | succ j =>
      have hs := hstate j (by omega)
      cases hphase : (quadrantSplitState ω j).phase with
      | r =>
          have hcountAb : (quadrantInterleaveState ab.1 ab.2 j).rCount =
              (quadrantSplitState ω j).rCount := congrArg QuadrantSplitState.rCount hs
          have hsplit := phaseSplit_rCode_at_step ω j hphase
          have hcode : ab.1 ((quadrantSplitState ω j).rCount + 1) = ω (j + 1) :=
            (hA _ (by omega) (by
              have hmono := quadrantSplitState_rCount_mono ω (j + 1) n (by omega)
              have hcnt : (quadrantSplitState ω (j + 1)).rCount =
                  (quadrantSplitState ω j).rCount + 1 := by
                rw [quadrantSplitState, quadrantSplitAdvance_rCount]
                simp [hphase]
              simpa [hcnt] using hmono)).trans hsplit
          have hphaseAb : (quadrantInterleaveState ab.1 ab.2 j).phase = .r := by
            rw [hs]
            exact hphase
          have hcodeAb : ab.1 ((quadrantInterleaveState ab.1 ab.2 j).rCount + 1) = ω (j + 1) := by
            rw [hcountAb]
            exact hcode
          simp [interleave, hphaseAb, hcodeAb]
      | l =>
          have hcountAb : (quadrantInterleaveState ab.1 ab.2 j).lCount =
              (quadrantSplitState ω j).lCount := congrArg QuadrantSplitState.lCount hs
          have hsplit := phaseSplit_lCode_at_step ω j hphase
          have hcode : ab.2 ((quadrantSplitState ω j).lCount + 1) = ω (j + 1) :=
            (hB _ (by omega) (by
              have hmono := quadrantSplitState_lCount_mono ω (j + 1) n (by omega)
              have hcnt : (quadrantSplitState ω (j + 1)).lCount =
                  (quadrantSplitState ω j).lCount + 1 := by
                rw [quadrantSplitState, quadrantSplitAdvance_lCount]
                simp [hphase]
              simpa [hcnt] using hmono)).trans hsplit
          have hphaseAb : (quadrantInterleaveState ab.1 ab.2 j).phase = .l := by
            rw [hs]
            exact hphase
          have hcodeAb : ab.2 ((quadrantInterleaveState ab.1 ab.2 j).lCount + 1) = ω (j + 1) := by
            rw [hcountAb]
            exact hcode
          simp [interleave, hphaseAb, hcodeAb]

private def quadrantCodePrefix (n : ℕ) (ω : ℕ → Fin 3) : Fin (n + 1) → Fin 3 :=
  fun j => ω j.val

private def quadrantCodePrefixExtend {n : ℕ} (q : Fin (n + 1) → Fin 3) : ℕ → Fin 3 :=
  fun i => if hi : i ≤ n then q ⟨i, by omega⟩ else 0

private theorem quadrantCodePrefixExtend_apply {n : ℕ} (q : Fin (n + 1) → Fin 3)
    (i : ℕ) (hi : i ≤ n) : quadrantCodePrefixExtend q i = q ⟨i, by omega⟩ := by
  simp [quadrantCodePrefixExtend, hi]

private theorem measurable_quadrantSplitState_rCount (n : ℕ) :
    Measurable (fun ω => (quadrantSplitState ω n).rCount) := by
  let pfx := fun ω : ℕ → Fin 3 => quadrantCodePrefix n ω
  let factor := fun q : Fin (n + 1) → Fin 3 =>
    (quadrantSplitState (quadrantCodePrefixExtend q) n).rCount
  have hpfx : Measurable pfx := by
    apply Measurable.of_eval
    intro j
    exact measurable_pi_apply j.val
  have hfactor : Measurable factor := measurable_of_countable factor
  have heq : (fun ω => (quadrantSplitState ω n).rCount) = factor ∘ pfx := by
    funext ω
    dsimp [factor, pfx]
    apply congrArg QuadrantSplitState.rCount
    apply quadrantSplitState_eq_of_prefix_eq
    intro i hi
    rw [quadrantCodePrefixExtend_apply _ i hi]
    rfl
  rw [heq]
  exact hfactor.comp hpfx

private theorem measurable_quadrantSplitState_lCount (n : ℕ) :
    Measurable (fun ω => (quadrantSplitState ω n).lCount) := by
  let pfx := fun ω : ℕ → Fin 3 => quadrantCodePrefix n ω
  let factor := fun q : Fin (n + 1) → Fin 3 =>
    (quadrantSplitState (quadrantCodePrefixExtend q) n).lCount
  have hpfx : Measurable pfx := by
    apply Measurable.of_eval
    intro j
    exact measurable_pi_apply j.val
  have hfactor : Measurable factor := measurable_of_countable factor
  have heq : (fun ω => (quadrantSplitState ω n).lCount) = factor ∘ pfx := by
    funext ω
    dsimp [factor, pfx]
    apply congrArg QuadrantSplitState.lCount
    apply quadrantSplitState_eq_of_prefix_eq
    intro i hi
    rw [quadrantCodePrefixExtend_apply _ i hi]
    rfl
  rw [heq]
  exact hfactor.comp hpfx

private theorem quadrantRCode_eq_iff (ω : ℕ → Fin 3) (k : ℕ) (c : Fin 3) :
    quadrantRCode ω k = c ↔
      (∃ n, (quadrantSplitState ω n).rCount = k + 1 ∧
        (∀ m < n, (quadrantSplitState ω m).rCount ≠ k + 1) ∧ ω n = c) ∨
      (c = 0 ∧ ∀ n, (quadrantSplitState ω n).rCount ≠ k + 1) := by
  classical
  unfold quadrantRCode
  by_cases h : ∃ n, (quadrantSplitState ω n).rCount = k + 1
  · rw [dite_eq_left h]
    constructor
    · intro hc
      left
      refine ⟨Nat.find h, Nat.find_spec h, ?_, hc⟩
      intro m hm
      exact Nat.find_min h hm
    · rintro (⟨n, hn, hmin, hcode⟩ | ⟨_, hno⟩)
      · have hfind : Nat.find h = n := (Nat.find_eq_iff h).2 ⟨hn, hmin⟩
        simpa [hfind] using hcode
      · exact (hno (Classical.choose h) (Classical.choose_spec h)).elim
  · rw [dite_eq_right h]
    constructor
    · intro hc
      right
      refine ⟨hc.symm, ?_⟩
      intro n hn
      exact h ⟨n, hn⟩
    · rintro (⟨n, hn, _, _⟩ | ⟨hc, _⟩)
      · exact (h ⟨n, hn⟩).elim
      · simp [hc]

private theorem quadrantLCode_eq_iff (ω : ℕ → Fin 3) (k : ℕ) (c : Fin 3) :
    quadrantLCode ω k = c ↔
      (∃ n, (quadrantSplitState ω n).lCount = k + 1 ∧
        (∀ m < n, (quadrantSplitState ω m).lCount ≠ k + 1) ∧ ω n = c) ∨
      (c = 0 ∧ ∀ n, (quadrantSplitState ω n).lCount ≠ k + 1) := by
  classical
  unfold quadrantLCode
  by_cases h : ∃ n, (quadrantSplitState ω n).lCount = k + 1
  · rw [dite_eq_left h]
    constructor
    · intro hc
      left
      refine ⟨Nat.find h, Nat.find_spec h, ?_, hc⟩
      intro m hm
      exact Nat.find_min h hm
    · rintro (⟨n, hn, hmin, hcode⟩ | ⟨_, hno⟩)
      · have hfind : Nat.find h = n := (Nat.find_eq_iff h).2 ⟨hn, hmin⟩
        simpa [hfind] using hcode
      · exact (hno (Classical.choose h) (Classical.choose_spec h)).elim
  · rw [dite_eq_right h]
    constructor
    · intro hc
      right
      refine ⟨hc.symm, ?_⟩
      intro n hn
      exact h ⟨n, hn⟩
    · rintro (⟨n, hn, _, _⟩ | ⟨hc, _⟩)
      · exact (h ⟨n, hn⟩).elim
      · simp [hc]

private theorem measurableSet_quadrantRCode_eq (k : ℕ) (c : Fin 3) :
    MeasurableSet {ω | quadrantRCode ω k = c} := by
  classical
  let firstEvent : Set (ℕ → Fin 3) := {ω | ∃ n,
    (quadrantSplitState ω n).rCount = k + 1 ∧
      (∀ m < n, (quadrantSplitState ω m).rCount ≠ k + 1) ∧ ω n = c}
  have hcountEq (n : ℕ) : MeasurableSet {ω | (quadrantSplitState ω n).rCount = k + 1} :=
    measurableSet_eq_fun (measurable_quadrantSplitState_rCount n) measurable_const
  have hprior (n : ℕ) : MeasurableSet {ω |
      ∀ m < n, (quadrantSplitState ω m).rCount ≠ k + 1} := by
    have hset : {ω | ∀ m < n, (quadrantSplitState ω m).rCount ≠ k + 1} =
        ⋂ m : Fin n, {ω | (quadrantSplitState ω m.val).rCount ≠ k + 1} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h m
        exact h m.val m.isLt
      · intro h m hm
        exact h ⟨m, hm⟩
    rw [hset]
    exact MeasurableSet.iInter fun m => (hcountEq m.val).compl
  have heval (n : ℕ) : Measurable (fun ω : ℕ → Fin 3 => ω n) :=
    measurable_pi_apply n
  have hcodeEq (n : ℕ) : MeasurableSet {ω : ℕ → Fin 3 | ω n = c} :=
    measurableSet_eq_fun (heval n) measurable_const
  have hfirst : MeasurableSet firstEvent := by
    have hset : firstEvent = ⋃ n, {ω | (quadrantSplitState ω n).rCount = k + 1 ∧
        (∀ m < n, (quadrantSplitState ω m).rCount ≠ k + 1) ∧ ω n = c} := by
      ext ω
      simp only [firstEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [hset]
    exact MeasurableSet.iUnion fun n => (hcountEq n).inter ((hprior n).inter (hcodeEq n))
  have hnoHit : MeasurableSet {ω |
      ∀ n, (quadrantSplitState ω n).rCount ≠ k + 1} := by
    have hset : {ω | ∀ n, (quadrantSplitState ω n).rCount ≠ k + 1} =
        ⋂ n : ℕ, {ω | (quadrantSplitState ω n).rCount ≠ k + 1} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter fun n => (hcountEq n).compl
  have hzeroNoHit : MeasurableSet {ω | c = 0 ∧
      ∀ n, (quadrantSplitState ω n).rCount ≠ k + 1} := by
    by_cases hc : c = 0
    · simpa [hc] using hnoHit
    · simp [hc]
  have hset : {ω | quadrantRCode ω k = c} =
      firstEvent ∪ {ω | c = 0 ∧
        ∀ n, (quadrantSplitState ω n).rCount ≠ k + 1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, firstEvent]
    exact quadrantRCode_eq_iff ω k c
  rw [hset]
  exact hfirst.union hzeroNoHit

private theorem measurableSet_quadrantLCode_eq (k : ℕ) (c : Fin 3) :
    MeasurableSet {ω | quadrantLCode ω k = c} := by
  classical
  let firstEvent : Set (ℕ → Fin 3) := {ω | ∃ n,
    (quadrantSplitState ω n).lCount = k + 1 ∧
      (∀ m < n, (quadrantSplitState ω m).lCount ≠ k + 1) ∧ ω n = c}
  have hcountEq (n : ℕ) : MeasurableSet {ω | (quadrantSplitState ω n).lCount = k + 1} :=
    measurableSet_eq_fun (measurable_quadrantSplitState_lCount n) measurable_const
  have hprior (n : ℕ) : MeasurableSet {ω |
      ∀ m < n, (quadrantSplitState ω m).lCount ≠ k + 1} := by
    have hset : {ω | ∀ m < n, (quadrantSplitState ω m).lCount ≠ k + 1} =
        ⋂ m : Fin n, {ω | (quadrantSplitState ω m.val).lCount ≠ k + 1} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h m
        exact h m.val m.isLt
      · intro h m hm
        exact h ⟨m, hm⟩
    rw [hset]
    exact MeasurableSet.iInter fun m => (hcountEq m.val).compl
  have heval (n : ℕ) : Measurable (fun ω : ℕ → Fin 3 => ω n) :=
    measurable_pi_apply n
  have hcodeEq (n : ℕ) : MeasurableSet {ω : ℕ → Fin 3 | ω n = c} :=
    measurableSet_eq_fun (heval n) measurable_const
  have hfirst : MeasurableSet firstEvent := by
    have hset : firstEvent = ⋃ n, {ω | (quadrantSplitState ω n).lCount = k + 1 ∧
        (∀ m < n, (quadrantSplitState ω m).lCount ≠ k + 1) ∧ ω n = c} := by
      ext ω
      simp only [firstEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [hset]
    exact MeasurableSet.iUnion fun n => (hcountEq n).inter ((hprior n).inter (hcodeEq n))
  have hnoHit : MeasurableSet {ω |
      ∀ n, (quadrantSplitState ω n).lCount ≠ k + 1} := by
    have hset : {ω | ∀ n, (quadrantSplitState ω n).lCount ≠ k + 1} =
        ⋂ n : ℕ, {ω | (quadrantSplitState ω n).lCount ≠ k + 1} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hset]
    exact MeasurableSet.iInter fun n => (hcountEq n).compl
  have hzeroNoHit : MeasurableSet {ω | c = 0 ∧
      ∀ n, (quadrantSplitState ω n).lCount ≠ k + 1} := by
    by_cases hc : c = 0
    · simpa [hc] using hnoHit
    · simp [hc]
  have hset : {ω | quadrantLCode ω k = c} =
      firstEvent ∪ {ω | c = 0 ∧
        ∀ n, (quadrantSplitState ω n).lCount ≠ k + 1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, firstEvent]
    exact quadrantLCode_eq_iff ω k c
  rw [hset]
  exact hfirst.union hzeroNoHit

private theorem measurable_finThree_function {α : Type*} [MeasurableSpace α]
    (f : α → Fin 3) (hf : ∀ c, MeasurableSet {x | f x = c}) : Measurable f := by
  intro s hs
  have hset : f ⁻¹' s = ⋃ c ∈ s, {x | f x = c} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨f x, hx, rfl⟩
    · rintro ⟨c, hc, hxc⟩
      rw [hxc]
      exact hc
  rw [hset]
  exact MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun _ => hf c

theorem measurable_phaseSplit : Measurable phaseSplit := by
  apply Measurable.prod
  · have hfst : Measurable (fun ω : ℕ → Fin 3 => (phaseSplit ω).1) := by
      change Measurable (fun ω => fun i =>
        if i = 0 then 0 else quadrantRCode ω (i - 1))
      apply measurable_pi_iff.mpr
      intro i
      by_cases hi : i = 0
      · simp [hi]
      · simp only [hi, ite_false]
        apply measurable_finThree_function
        intro c
        exact measurableSet_quadrantRCode_eq (i - 1) c
    exact hfst
  · have hsnd : Measurable (fun ω : ℕ → Fin 3 => (phaseSplit ω).2) := by
      change Measurable (fun ω => fun i =>
        if i = 0 then 0 else quadrantLCode ω (i - 1))
      apply measurable_pi_iff.mpr
      intro i
      by_cases hi : i = 0
      · simp [hi]
      · simp only [hi, ite_false]
        apply measurable_finThree_function
        intro c
        exact measurableSet_quadrantLCode_eq (i - 1) c
    exact hsnd

private theorem measurableSet_codeWalk_fst_hits_every_level :
    MeasurableSet {ω : ℕ → Fin 3 | ∀ z : ℤ, ∃ n, (codeWalk ω n).1 = z} := by
  have hset : {ω : ℕ → Fin 3 | ∀ z : ℤ, ∃ n, (codeWalk ω n).1 = z} =
      ⋂ z : ℤ, {ω | ∃ n, (codeWalk ω n).1 = z} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  apply MeasurableSet.iInter
  intro z
  have hset' : {ω : ℕ → Fin 3 | ∃ n, (codeWalk ω n).1 = z} =
      ⋃ n, {ω | (codeWalk ω n).1 = z} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset']
  apply MeasurableSet.iUnion
  intro n
  have hwalk : Measurable (fun ω : ℕ → Fin 3 => (codeWalk ω n).1) :=
    ((measurable_pi_apply n).comp measurable_codeWalk).fst
  exact measurableSet_eq_fun hwalk measurable_const

private theorem measurableSet_codeWalk_snd_hits_every_level :
    MeasurableSet {ω : ℕ → Fin 3 | ∀ z : ℤ, ∃ n, (codeWalk ω n).2 = z} := by
  have hset : {ω : ℕ → Fin 3 | ∀ z : ℤ, ∃ n, (codeWalk ω n).2 = z} =
      ⋂ z : ℤ, {ω | ∃ n, (codeWalk ω n).2 = z} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  apply MeasurableSet.iInter
  intro z
  have hset' : {ω : ℕ → Fin 3 | ∃ n, (codeWalk ω n).2 = z} =
      ⋃ n, {ω | (codeWalk ω n).2 = z} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset']
  apply MeasurableSet.iUnion
  intro n
  have hwalk : Measurable (fun ω : ℕ → Fin 3 => (codeWalk ω n).2) :=
    ((measurable_pi_apply n).comp measurable_codeWalk).snd
  exact measurableSet_eq_fun hwalk measurable_const

private theorem iidCodeMeasure_prod_ae_phaseSplit_conditions :
    ∀ᵐ ab ∂(iidCodeMeasure.prod iidCodeMeasure),
      ab.1 0 = 0 ∧
        (∀ z : ℤ, ∃ n, (codeWalk ab.1 n).1 = z) ∧
        ab.2 0 = 0 ∧
        (∀ z : ℤ, ∃ n, (codeWalk ab.2 n).2 = z) := by
  let goodA : Set (ℕ → Fin 3) :=
    {a | a 0 = 0 ∧ ∀ z : ℤ, ∃ n, (codeWalk a n).1 = z}
  let goodB : Set (ℕ → Fin 3) :=
    {b | b 0 = 0 ∧ ∀ z : ℤ, ∃ n, (codeWalk b n).2 = z}
  have hstart : ∀ᵐ a ∂iidCodeMeasure, a 0 = 0 := by
    filter_upwards [DirectedDistances.Probability.markovTrajectory_ae_start
      (Kernel.const (Fin 3) uniformCodeMeasure) (0 : Fin 3)] with a ha
    exact ha
  have hhitA : ∀ᵐ a ∂iidCodeMeasure,
      ∀ z : ℤ, ∃ n, (codeWalk a n).1 = z := by
    apply ae_all_iff.mpr
    intro z
    exact ae_exists_codeWalk_fst_eq_int z
  have hhitB : ∀ᵐ b ∂iidCodeMeasure,
      ∀ z : ℤ, ∃ n, (codeWalk b n).2 = z := by
    apply ae_all_iff.mpr
    intro z
    exact ae_exists_codeWalk_snd_eq_int z
  have hgoodAset : goodA = {a | a 0 = 0} ∩
      {a | ∀ z : ℤ, ∃ n, (codeWalk a n).1 = z} := by
    ext a
    simp [goodA]
  have hgoodBset : goodB = {b | b 0 = 0} ∩
      {b | ∀ z : ℤ, ∃ n, (codeWalk b n).2 = z} := by
    ext b
    simp [goodB]
  have hgoodAmeas : MeasurableSet goodA := by
    rw [hgoodAset]
    exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
      measurableSet_codeWalk_fst_hits_every_level
  have hgoodBmeas : MeasurableSet goodB := by
    rw [hgoodBset]
    exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
      measurableSet_codeWalk_snd_hits_every_level
  have hgoodAae : ∀ᵐ a ∂iidCodeMeasure, a ∈ goodA := by
    filter_upwards [hstart, hhitA] with a h0 hh
    exact ⟨h0, hh⟩
  have hgoodBae : ∀ᵐ b ∂iidCodeMeasure, b ∈ goodB := by
    filter_upwards [hstart, hhitB] with b h0 hh
    exact ⟨h0, hh⟩
  have hprodSet : MeasurableSet {ab : (ℕ → Fin 3) × (ℕ → Fin 3) |
      ab.1 ∈ goodA ∧ ab.2 ∈ goodB} := by
    exact (hgoodAmeas.preimage measurable_fst).inter
      (hgoodBmeas.preimage measurable_snd)
  have hprodAE : ∀ᵐ ab ∂(iidCodeMeasure.prod iidCodeMeasure),
      ab.1 ∈ goodA ∧ ab.2 ∈ goodB := by
    apply (Measure.ae_prod_iff_ae_ae hprodSet).2
    filter_upwards [hgoodAae] with a ha
    filter_upwards [hgoodBae] with b hb
    exact ⟨ha, hb⟩
  filter_upwards [hprodAE] with ab hab
  have hab' : (ab.1 0 = 0 ∧ ∀ z : ℤ, ∃ n, (codeWalk ab.1 n).1 = z) ∧
      (ab.2 0 = 0 ∧ ∀ z : ℤ, ∃ n, (codeWalk ab.2 n).2 = z) := by
    simpa [goodA, goodB] using hab
  rcases hab' with ⟨⟨h0A, hhitA⟩, ⟨h0B, hhitB⟩⟩
  exact ⟨h0A, hhitA, h0B, hhitB⟩

private theorem iidCodeMeasure_prod_ae_phaseSplit_interleave :
    ∀ᵐ ab ∂(iidCodeMeasure.prod iidCodeMeasure), phaseSplit (interleave ab) = ab := by
  filter_upwards [iidCodeMeasure_prod_ae_phaseSplit_conditions] with ab h
  rcases h with ⟨hzeroA, hhitA, hzeroB, hhitB⟩
  exact phaseSplit_interleave ab hzeroA hzeroB hhitA hhitB

private theorem quadrantInterleaveState_eq_of_input_prefix
    (a b c d : ℕ → Fin 3) : ∀ n,
      (∀ i ≤ n, a i = c i) → (∀ i ≤ n, b i = d i) →
      quadrantInterleaveState a b n = quadrantInterleaveState c d n := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
      intro ha hb
      have hprev : quadrantInterleaveState a b n = quadrantInterleaveState c d n := by
        apply ih
        · intro i hi
          exact ha i (by omega)
        · intro i hi
          exact hb i (by omega)
      cases hphaseA : (quadrantInterleaveState a b n).phase with
      | r =>
          have hphaseB : (quadrantInterleaveState c d n).phase = .r := by
            rw [← hprev]
            exact hphaseA
          have hcountA : (quadrantInterleaveState a b n).rCount ≤ n := by
            have h := quadrantInterleaveState_counts (a, b) n
            have hsum : (quadrantInterleaveState a b n).rCount +
                (quadrantInterleaveState a b n).lCount = n := by simpa using h
            omega
          have hcountEq : (quadrantInterleaveState a b n).rCount =
              (quadrantInterleaveState c d n).rCount := congrArg QuadrantSplitState.rCount hprev
          have hcode : a ((quadrantInterleaveState a b n).rCount + 1) =
              c ((quadrantInterleaveState c d n).rCount + 1) := by
            rw [hcountEq]
            exact ha _ (by omega)
          have hnextA : quadrantInterleaveState a b (n + 1) =
              quadrantSplitAdvance (quadrantInterleaveState a b n)
                (a ((quadrantInterleaveState a b n).rCount + 1)) := by
            simp [quadrantInterleaveState, hphaseA]
          have hnextB : quadrantInterleaveState c d (n + 1) =
              quadrantSplitAdvance (quadrantInterleaveState c d n)
                (c ((quadrantInterleaveState c d n).rCount + 1)) := by
            simp [quadrantInterleaveState, hphaseB]
          rw [hnextA, hnextB, hcode, hprev]
      | l =>
          have hphaseB : (quadrantInterleaveState c d n).phase = .l := by
            rw [← hprev]
            exact hphaseA
          have hcountA : (quadrantInterleaveState a b n).lCount ≤ n := by
            have h := quadrantInterleaveState_counts (a, b) n
            have hsum : (quadrantInterleaveState a b n).rCount +
                (quadrantInterleaveState a b n).lCount = n := by simpa using h
            omega
          have hcountEq : (quadrantInterleaveState a b n).lCount =
              (quadrantInterleaveState c d n).lCount := congrArg QuadrantSplitState.lCount hprev
          have hcode : b ((quadrantInterleaveState a b n).lCount + 1) =
              d ((quadrantInterleaveState c d n).lCount + 1) := by
            rw [hcountEq]
            exact hb _ (by omega)
          have hnextA : quadrantInterleaveState a b (n + 1) =
              quadrantSplitAdvance (quadrantInterleaveState a b n)
                (b ((quadrantInterleaveState a b n).lCount + 1)) := by
            simp [quadrantInterleaveState, hphaseA]
          have hnextB : quadrantInterleaveState c d (n + 1) =
              quadrantSplitAdvance (quadrantInterleaveState c d n)
                (d ((quadrantInterleaveState c d n).lCount + 1)) := by
            simp [quadrantInterleaveState, hphaseB]
          rw [hnextA, hnextB, hcode, hprev]

private theorem interleave_apply_eq_of_input_prefix
    (ab cd : (ℕ → Fin 3) × (ℕ → Fin 3)) (n : ℕ)
    (hA : ∀ i ≤ n, ab.1 i = cd.1 i) (hB : ∀ i ≤ n, ab.2 i = cd.2 i) :
    interleave ab n = interleave cd n := by
  cases n with
  | zero => simp [interleave_zero]
  | succ n =>
      have hstate := quadrantInterleaveState_eq_of_input_prefix ab.1 ab.2 cd.1 cd.2 n
        (fun i hi => hA i (by omega)) (fun i hi => hB i (by omega))
      cases hphase : (quadrantInterleaveState ab.1 ab.2 n).phase with
      | r =>
          have hphase' : (quadrantInterleaveState cd.1 cd.2 n).phase = .r := by
            rw [← hstate]
            exact hphase
          have hcount : (quadrantInterleaveState ab.1 ab.2 n).rCount ≤ n := by
            have h := quadrantInterleaveState_counts ab n
            omega
          have hcountEq : (quadrantInterleaveState ab.1 ab.2 n).rCount =
              (quadrantInterleaveState cd.1 cd.2 n).rCount := congrArg QuadrantSplitState.rCount hstate
          have hcode : ab.1 ((quadrantInterleaveState ab.1 ab.2 n).rCount + 1) =
              cd.1 ((quadrantInterleaveState cd.1 cd.2 n).rCount + 1) := by
            rw [hcountEq]
            exact hA _ (by omega)
          calc
            interleave ab (n + 1) =
                ab.1 ((quadrantInterleaveState ab.1 ab.2 n).rCount + 1) := by
              simp [interleave, hphase]
            _ = cd.1 ((quadrantInterleaveState cd.1 cd.2 n).rCount + 1) := hcode
            _ = interleave cd (n + 1) := by simp [interleave, hphase']
      | l =>
          have hphase' : (quadrantInterleaveState cd.1 cd.2 n).phase = .l := by
            rw [← hstate]
            exact hphase
          have hcount : (quadrantInterleaveState ab.1 ab.2 n).lCount ≤ n := by
            have h := quadrantInterleaveState_counts ab n
            omega
          have hcountEq : (quadrantInterleaveState ab.1 ab.2 n).lCount =
              (quadrantInterleaveState cd.1 cd.2 n).lCount := congrArg QuadrantSplitState.lCount hstate
          have hcode : ab.2 ((quadrantInterleaveState ab.1 ab.2 n).lCount + 1) =
              cd.2 ((quadrantInterleaveState cd.1 cd.2 n).lCount + 1) := by
            rw [hcountEq]
            exact hB _ (by omega)
          calc
            interleave ab (n + 1) =
                ab.2 ((quadrantInterleaveState ab.1 ab.2 n).lCount + 1) := by
              simp [interleave, hphase]
            _ = cd.2 ((quadrantInterleaveState cd.1 cd.2 n).lCount + 1) := hcode
            _ = interleave cd (n + 1) := by simp [interleave, hphase']

private def quadrantInterleavePrefixFactor (n : ℕ)
    (p : (Fin (n + 1) → Fin 3) × (Fin (n + 1) → Fin 3)) : Fin 3 :=
  interleave (quadrantCodePrefixExtend p.1, quadrantCodePrefixExtend p.2) n

/-- The deterministic interleaver is measurable, since each output coordinate
depends only on finite input prefixes (`lem-quadrant-walk`, -/
theorem measurable_interleave : Measurable interleave := by
  apply Measurable.of_eval
  intro n
  let pfx := fun ω : ℕ → Fin 3 => quadrantCodePrefix n ω
  let factor := quadrantInterleavePrefixFactor n
  have hpfx : Measurable pfx := by
    apply Measurable.of_eval
    intro j
    exact measurable_pi_apply j.val
  have hpair : Measurable (fun ab : (ℕ → Fin 3) × (ℕ → Fin 3) => (pfx ab.1, pfx ab.2)) := by
    fun_prop
  have hfactor : Measurable factor := measurable_of_countable factor
  have hEq : (fun ab : (ℕ → Fin 3) × (ℕ → Fin 3) => interleave ab n) = factor ∘
      (fun ab => (pfx ab.1, pfx ab.2)) := by
    funext ab
    apply interleave_apply_eq_of_input_prefix ab
      (quadrantCodePrefixExtend (pfx ab.1), quadrantCodePrefixExtend (pfx ab.2)) n
    · intro i hi
      change ab.1 i = quadrantCodePrefixExtend (quadrantCodePrefix n ab.1) i
      rw [quadrantCodePrefixExtend_apply _ i hi]
      rfl
    · intro i hi
      change ab.2 i = quadrantCodePrefixExtend (quadrantCodePrefix n ab.2) i
      rw [quadrantCodePrefixExtend_apply _ i hi]
      rfl
  rw [hEq]
  exact hfactor.comp hpair

@[expose] def quadrantCodeTailPrefix (n : ℕ) (ω : ℕ → Fin 3) : Fin n → Fin 3 :=
  fun j => ω (j.val + 1)

/-- Every prescribed block of `n` positive-time codes has iid mass -/
theorem iidCodeMeasure_tailPrefix_mass (n : ℕ) (q : Fin n → Fin 3) :
    iidCodeMeasure {ω | quadrantCodeTailPrefix n ω = q} = (1 / 3 : ENNReal) ^ n := by
  classical
  let q' : Fin (n + 1) → Fin 3 := Fin.cons 0 q
  have hZ : ∀ᵐ ω ∂iidCodeMeasure, ω 0 = 0 := by
    filter_upwards [DirectedDistances.Probability.markovTrajectory_ae_start
      (Kernel.const (Fin 3) uniformCodeMeasure) (0 : Fin 3)] with ω hω
    exact hω
  have hae : {ω | quadrantCodeTailPrefix n ω = q} =ᵐ[iidCodeMeasure]
      {ω | quadrantCodePrefix n ω = q'} := by
    filter_upwards [hZ] with ω hω
    apply propext
    constructor
    · intro h
      funext j
      refine Fin.cases ?_ ?_ j
      · simpa [quadrantCodePrefix, q'] using hω
      · intro j
        have hj := congrFun h j
        simpa [quadrantCodePrefix, quadrantCodeTailPrefix, q'] using hj
    · intro h
      funext j
      have hj := congrFun h j.succ
      simpa [quadrantCodePrefix, quadrantCodeTailPrefix, q'] using hj
  have hprefix : iidCodeMeasure {ω | quadrantCodePrefix n ω = q'} =
      (Measure.pi (fun j : Fin (n + 1) =>
        if j.val = 0 then Measure.dirac (0 : Fin 3) else uniformCodeMeasure)) {q'} := by
    rw [← iidCodeMeasure_map_prefix n,
      Measure.map_apply (by fun_prop) (measurableSet_singleton q')]
    rfl
  rw [measure_congr hae, hprefix, Measure.pi_singleton, Fin.prod_univ_succ]
  simp only [q', Fin.cons_zero, Fin.val_zero, ↓reduceIte, Fin.cons_succ, Fin.val_succ,
    Nat.add_eq_zero_iff, one_ne_zero, and_false]
  simp [uniformCodeMeasure, Measure.uniformOfFinset_apply_singleton]

private theorem iidCodeMeasure_prefix_mass (n : ℕ) (q : Fin (n + 1) → Fin 3) :
    iidCodeMeasure {ω | quadrantCodePrefix n ω = q} =
      if q 0 = 0 then (1 / 3 : ENNReal) ^ n else 0 := by
  have h := congrArg (fun μ : Measure (Fin (n + 1) → Fin 3) => μ {q})
    (iidCodeMeasure_map_prefix n)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton q)] at h
  have h' : iidCodeMeasure {ω | quadrantCodePrefix n ω = q} =
      (Measure.pi (fun j : Fin (n + 1) =>
        if j.val = 0 then Measure.dirac (0 : Fin 3) else uniformCodeMeasure)) {q} := by
    change iidCodeMeasure ((fun ω : ℕ → Fin 3 => quadrantCodePrefix n ω) ⁻¹' {q}) = _
    exact h
  rw [h', Measure.pi_singleton, Fin.prod_univ_succ]
  simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.add_eq_zero_iff,
    one_ne_zero, and_false]
  by_cases hzero : q 0 = 0
  · simp [hzero, uniformCodeMeasure, Measure.uniformOfFinset_apply_singleton]
  · simp [hzero, uniformCodeMeasure, Measure.uniformOfFinset_apply_singleton]

private theorem interleave_prefix_cylinder_preimage
    (ω : ℕ → Fin 3) (n : ℕ) (hzero : ω 0 = 0) :
    {ab : (ℕ → Fin 3) × (ℕ → Fin 3) | ∀ i ≤ n, interleave ab i = ω i} =
      ({a | ∀ i, 0 < i → i ≤ (quadrantSplitState ω n).rCount →
          a i = (phaseSplit ω).1 i} ×ˢ
       {b | ∀ i, 0 < i → i ≤ (quadrantSplitState ω n).lCount →
          b i = (phaseSplit ω).2 i}) := by
  ext ab
  simp only [Set.mem_ofPred_eq, Set.mem_prod]
  constructor
  · intro h
    have hmatch := phaseSplit_interleave_prefix_matches ab ω n h
    constructor
    · intro i hi hcount
      exact (hmatch.1 i hi hcount).symm
    · intro i hi hcount
      exact (hmatch.2 i hi hcount).symm
  · rintro ⟨hA, hB⟩
    exact interleave_prefix_eq_of_split_prefix ab ω n hzero hA hB

private theorem quadrantCodePrefixExtend_prefix (n : ℕ) (q : Fin (n + 1) → Fin 3) :
    quadrantCodePrefix n (quadrantCodePrefixExtend q) = q := by
  funext j
  change quadrantCodePrefixExtend q j.val = q j
  rw [quadrantCodePrefixExtend_apply q j.val (by omega)]

private theorem map_interleave_prefix (n : ℕ) :
    (iidCodeMeasure.prod iidCodeMeasure).map (fun ab => quadrantCodePrefix n (interleave ab)) =
      Measure.pi (fun j : Fin (n + 1) =>
        if j.val = 0 then Measure.dirac (0 : Fin 3) else uniformCodeMeasure) := by
  have hprefix : Measurable (quadrantCodePrefix n) := by
    apply Measurable.of_eval
    intro j
    exact measurable_pi_apply j.val
  have hcomp : Measurable (fun ab : (ℕ → Fin 3) × (ℕ → Fin 3) =>
      quadrantCodePrefix n (interleave ab)) := hprefix.comp measurable_interleave
  apply Measure.ext_of_singleton
  intro q
  rw [Measure.map_apply hcomp (measurableSet_singleton q)]
  change (iidCodeMeasure.prod iidCodeMeasure)
      {ab | quadrantCodePrefix n (interleave ab) = q} = _
  have hpi : (Measure.pi (fun j : Fin (n + 1) =>
      if j.val = 0 then Measure.dirac (0 : Fin 3) else uniformCodeMeasure)) {q} =
      if q 0 = 0 then (1 / 3 : ENNReal) ^ n else 0 := by
    have h := congrArg (fun μ : Measure (Fin (n + 1) → Fin 3) => μ {q})
      (iidCodeMeasure_map_prefix n)
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton q)] at h
    have h' : iidCodeMeasure {ω | quadrantCodePrefix n ω = q} =
        (Measure.pi (fun j : Fin (n + 1) =>
          if j.val = 0 then Measure.dirac (0 : Fin 3) else uniformCodeMeasure)) {q} := by
      change iidCodeMeasure ((fun ω : ℕ → Fin 3 => quadrantCodePrefix n ω) ⁻¹' {q}) = _
      exact h
    rw [← h', iidCodeMeasure_prefix_mass]
  by_cases hzero : q 0 = 0
  · let ω := quadrantCodePrefixExtend q
    have hωprefix : quadrantCodePrefix n ω = q := by
      simpa [ω] using quadrantCodePrefixExtend_prefix n q
    have hωzero : ω 0 = 0 := by
      have h := congrFun hωprefix 0
      calc
        ω 0 = q 0 := by simpa [quadrantCodePrefix] using h
        _ = 0 := hzero
    have hset : {ab : (ℕ → Fin 3) × (ℕ → Fin 3) |
        quadrantCodePrefix n (interleave ab) = q} =
        {ab | ∀ i ≤ n, interleave ab i = ω i} := by
      ext ab
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h i hi
        have hout := congrFun h ⟨i, by omega⟩
        have hω := congrFun hωprefix ⟨i, by omega⟩
        exact hout.trans hω.symm
      · intro h
        funext j
        exact (h j.val (by omega)).trans (congrFun hωprefix j)
    let nr := (quadrantSplitState ω n).rCount
    let nl := (quadrantSplitState ω n).lCount
    let A : Set (ℕ → Fin 3) := {a | ∀ i, 0 < i → i ≤ nr → a i = (phaseSplit ω).1 i}
    let B : Set (ℕ → Fin 3) := {b | ∀ i, 0 < i → i ≤ nl → b i = (phaseSplit ω).2 i}
    have hsetA : A = {a | quadrantCodeTailPrefix nr a =
        quadrantCodeTailPrefix nr (phaseSplit ω).1} := by
      ext a
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        funext j
        change a (j.val + 1) = (phaseSplit ω).1 (j.val + 1)
        exact h _ (by omega) (by omega)
      · intro h i hi hbound
        have h' := congrFun h ⟨i - 1, by omega⟩
        have hidx : i - 1 + 1 = i := by omega
        simpa [quadrantCodeTailPrefix, hidx] using h'
    have hsetB : B = {b | quadrantCodeTailPrefix nl b =
        quadrantCodeTailPrefix nl (phaseSplit ω).2} := by
      ext b
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        funext j
        change b (j.val + 1) = (phaseSplit ω).2 (j.val + 1)
        exact h _ (by omega) (by omega)
      · intro h i hi hbound
        have h' := congrFun h ⟨i - 1, by omega⟩
        have hidx : i - 1 + 1 = i := by omega
        simpa [quadrantCodeTailPrefix, hidx] using h'
    have hmassA : iidCodeMeasure A = (1 / 3 : ENNReal) ^ nr := by
      rw [hsetA, iidCodeMeasure_tailPrefix_mass]
    have hmassB : iidCodeMeasure B = (1 / 3 : ENNReal) ^ nl := by
      rw [hsetB, iidCodeMeasure_tailPrefix_mass]
    have hcounts : nr + nl = n := by
      simpa [nr, nl] using quadrantSplitState_counts ω n
    have hpow : (1 / 3 : ENNReal) ^ nr * (1 / 3 : ENNReal) ^ nl =
        (1 / 3 : ENNReal) ^ n := by
      rw [← pow_add, hcounts]
    rw [hset, interleave_prefix_cylinder_preimage ω n hωzero]
    change (iidCodeMeasure.prod iidCodeMeasure) (A ×ˢ B) = _
    calc
      (iidCodeMeasure.prod iidCodeMeasure) (A ×ˢ B) = iidCodeMeasure A * iidCodeMeasure B :=
        Measure.prod_prod A B
      _ = (1 / 3 : ENNReal) ^ nr * (1 / 3 : ENNReal) ^ nl := by rw [hmassA, hmassB]
      _ = (1 / 3 : ENNReal) ^ n := hpow
      _ = (Measure.pi (fun j : Fin (n + 1) =>
          if j.val = 0 then Measure.dirac (0 : Fin 3) else uniformCodeMeasure)) {q} := by
        rw [hpi]
        simp [hzero]
  · have hempty : {ab : (ℕ → Fin 3) × (ℕ → Fin 3) |
        quadrantCodePrefix n (interleave ab) = q} = ∅ := by
      ext ab
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hq0 := congrFun h 0
      have hout : quadrantCodePrefix n (interleave ab) 0 = 0 := by
        simp [quadrantCodePrefix, interleave_zero]
      apply hzero
      calc
        q 0 = quadrantCodePrefix n (interleave ab) 0 := hq0.symm
        _ = 0 := hout
    rw [hempty, measure_empty, hpi]
    simp [hzero]

/-- Interleaving two independent iid code streams has iid code law, by the
finite-prefix cylinder calculation for `lem-quadrant-walk` -/
theorem map_interleave_iidCodeMeasure :
    (iidCodeMeasure.prod iidCodeMeasure).map interleave = iidCodeMeasure := by
  classical
  have hrestrict : ∀ I : Finset ℕ,
      ((iidCodeMeasure.prod iidCodeMeasure).map interleave).map I.restrict =
        iidCodeMeasure.map I.restrict := by
    intro I
    let n := I.sup id
    let g : (Fin (n + 1) → Fin 3) → (I → Fin 3) := fun q i => q ⟨i.1, by
      have hi := Finset.le_sup (f := id) i.property
      change i.1 ≤ I.sup id at hi
      dsimp [n]
      omega⟩
    have hg : Measurable g := measurable_of_countable g
    have hf : Measurable (quadrantCodePrefix n) := by
      apply Measurable.of_eval
      intro j
      exact measurable_pi_apply j.val
    have hfac : (Finset.restrict (π := fun _ : ℕ => Fin 3) I) =
        g ∘ quadrantCodePrefix n := rfl
    rw [hfac, ← Measure.map_map hg hf, ← Measure.map_map hg hf]
    rw [Measure.map_map hf measurable_interleave]
    have hlaw : Measure.map (quadrantCodePrefix n ∘ interleave)
        (iidCodeMeasure.prod iidCodeMeasure) =
        Measure.pi (fun j : Fin (n + 1) =>
          if j.val = 0 then Measure.dirac (0 : Fin 3) else uniformCodeMeasure) := by
      simpa only [Function.comp_def] using map_interleave_prefix n
    rw [hlaw]
    exact congrArg (Measure.map g) (iidCodeMeasure_map_prefix n).symm
  exact (show IsProjectiveLimit ((iidCodeMeasure.prod iidCodeMeasure).map interleave)
      (fun I => iidCodeMeasure.map I.restrict) from hrestrict).unique
    (show IsProjectiveLimit iidCodeMeasure (fun I => iidCodeMeasure.map I.restrict) from
      fun I => rfl)

/-- Splitting an iid code stream has the law of two independent iid code
streams, using the almost-sure inverse on inputs whose coordinate walks hit
every integer level (`lem-quadrant-walk`, -/
theorem map_phaseSplit_iidCodeMeasure :
    iidCodeMeasure.map phaseSplit = iidCodeMeasure.prod iidCodeMeasure := by
  have hmap : (iidCodeMeasure.prod iidCodeMeasure).map interleave = iidCodeMeasure :=
    map_interleave_iidCodeMeasure
  have hcomp : phaseSplit ∘ interleave =ᵐ[iidCodeMeasure.prod iidCodeMeasure] id := by
    filter_upwards [iidCodeMeasure_prod_ae_phaseSplit_interleave] with ab hab
    simpa only [Function.comp_apply, id] using hab
  calc
    iidCodeMeasure.map phaseSplit =
        (iidCodeMeasure.prod iidCodeMeasure).map (phaseSplit ∘ interleave) := by
      calc
        iidCodeMeasure.map phaseSplit =
            ((iidCodeMeasure.prod iidCodeMeasure).map interleave).map phaseSplit :=
          congrArg (fun μ : Measure (ℕ → Fin 3) => μ.map phaseSplit) hmap.symm
        _ = (iidCodeMeasure.prod iidCodeMeasure).map (phaseSplit ∘ interleave) :=
          Measure.map_map measurable_phaseSplit measurable_interleave
    _ = iidCodeMeasure.prod iidCodeMeasure := by
      rw [Measure.map_congr hcomp, Measure.map_id]

/-- Interleaving the streams extracted from a source recovers every source
code. -/
theorem interleave_phaseSplit (ω : ℕ → Fin 3) (hzero : ω 0 = 0) :
    interleave (phaseSplit ω) = ω := by
  funext i
  cases i with
  | zero => simp [interleave, hzero]
  | succ n =>
      simp only [interleave, Nat.succ_ne_zero, ↓reduceIte]
      rw [show n + 1 - 1 = n by omega]
      rw [quadrantInterleaveState_phaseSplit]
      cases hphase : (quadrantSplitState ω n).phase with
      | r =>
          exact phaseSplit_rCode_at_step ω n hphase
      | l =>
          exact phaseSplit_lCode_at_step ω n hphase

end DirectedDistances.RandomWalk
