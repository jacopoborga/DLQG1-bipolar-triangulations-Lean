module

public import DirectedDistances.KMSW.BoundaryDynamics

/-! # KMSW initialization with a missing root

This records the C18 convention for the primed map in Lemma 5.13
but is initially missing as a directed edge. The ordinary KMSW state remains
unchanged. This is helper bookkeeping, not the map-identification result. -/

public section
namespace DirectedDistances.KMSW

/-- Initial state for the C18 missing-root convention for the primed map in
geometric edge and all its incidences are retained; only its directed-edge
presence is removed. This helper leaves ordinary KMSW initialization intact. -/
@[expose] def kmswMissingRootInit : State :=
  { kmswInit with
    present := fun e => if e = 0 then false else kmswInit.present e }

theorem kmswMissingRootInit_west (e : ℕ) :
    kmswMissingRootInit.west e = kmswInit.west e := rfl

theorem kmswMissingRootInit_east (e : ℕ) :
    kmswMissingRootInit.east e = kmswInit.east e := rfl

theorem kmswMissingRootInit_active :
    kmswMissingRootInit.active = kmswInit.active := rfl

theorem kmswMissingRootInit_nextEdge :
    kmswMissingRootInit.nextEdge = kmswInit.nextEdge := rfl

theorem kmswMissingRootInit_nextVertex :
    kmswMissingRootInit.nextVertex = kmswInit.nextVertex := rfl

theorem kmswMissingRootInit_UL :
    kmswMissingRootInit.UL = kmswInit.UL := rfl

theorem kmswMissingRootInit_UR :
    kmswMissingRootInit.UR = kmswInit.UR := rfl

theorem kmswMissingRootInit_triangles :
    kmswMissingRootInit.triangles = kmswInit.triangles := rfl

theorem kmswMissingRootInit_LL :
    kmswMissingRootInit.LL = kmswInit.LL := rfl

theorem kmswMissingRootInit_LR :
    kmswMissingRootInit.LR = kmswInit.LR := rfl

theorem kmswMissingRootInit_present_zero :
    kmswMissingRootInit.present 0 = false := by
  simp [kmswMissingRootInit, kmswInit]

/-- Stages for the C18 missing-root initialization, using the ordinary KMSW -/
@[expose] def kmswMissingRootStage (w : ℕ → Fin 3) : ℕ → State
  | 0 => kmswMissingRootInit
  | n + 1 => kmswStep (kmswMissingRootStage w n) (w n)

/-- Agreement in every state field except for the presence of geometric edge
zero. This includes endpoints, the triangle list, the active edge, all
boundaries, and presence of every nonzero edge (`def-kmsw`, -/
@[expose]
def State.AgreeOffRoot (s t : State) : Prop :=
  s.nextVertex = t.nextVertex ∧
  s.nextEdge = t.nextEdge ∧
  (∀ e, s.west e = t.west e) ∧
  (∀ e, s.east e = t.east e) ∧
  (∀ e, e ≠ 0 → s.present e = t.present e) ∧
  s.triangles = t.triangles ∧
  s.active = t.active ∧
  s.UL = t.UL ∧
  s.UR = t.UR ∧
  s.LL = t.LL ∧
  s.LR = t.LR

private theorem kmswStep_boundaryInv (s : State)
    (hnext : 0 < s.nextEdge) (hur : ∀ e ∈ s.UR, 0 < e) (c : Fin 3) :
    0 < (kmswStep s c).nextEdge ∧
      ∀ e ∈ (kmswStep s c).UR, 0 < e := by
  fin_cases c
  · change 0 < (kmswStepOfStep s .left).nextEdge ∧
      ∀ e ∈ (kmswStepOfStep s .left).UR, 0 < e
    cases hUL : s.UL.dropLast.reverse with
    | nil =>
      simp only [kmswStepOfStep, hUL]
      constructor
      · simp only [State.addEdge]
        omega
      · intro e he
        exact hur e he
    | cons a as =>
      simp only [kmswStepOfStep, hUL]
      constructor
      · simp only [State.addEdge]
        omega
      · intro e he
        exact hur e he
  · change 0 < (kmswStepOfStep s .up).nextEdge ∧
      ∀ e ∈ (kmswStepOfStep s .up).UR, 0 < e
    simp only [kmswStepOfStep]
    constructor
    · simp only [State.addEdge]
      omega
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with he | he
      · subst e
        omega
      · exact hur e he
  · change 0 < (kmswStepOfStep s .down).nextEdge ∧
      ∀ e ∈ (kmswStepOfStep s .down).UR, 0 < e
    cases hUR : s.UR with
    | nil =>
      simp only [kmswStepOfStep, hUR]
      constructor
      · simp only [State.addEdge]
        omega
      · intro e he
        exact hur e he
    | cons a as =>
      simp only [kmswStepOfStep, hUR]
      constructor
      · exact hnext
      · intro e he
        apply hur e
        rw [hUR]
        simp [he]

private theorem kmswMissingRootStage_boundaryInv (w : ℕ → Fin 3) (n : ℕ) :
    0 < (kmswMissingRootStage w n).nextEdge ∧
      ∀ e ∈ (kmswMissingRootStage w n).UR, 0 < e := by
  induction n with
  | zero => simp [kmswMissingRootStage, kmswMissingRootInit, kmswInit]
  | succ n ih =>
    rw [kmswMissingRootStage]
    exact kmswStep_boundaryInv _ ih.1 ih.2 (w n)

private theorem kmswStep_present_zero (s : State)
    (hp : s.present 0 = false) (hnext : 0 < s.nextEdge)
    (hur : ∀ e ∈ s.UR, 0 < e) (c : Fin 3) :
    (kmswStep s c).present 0 = false := by
  fin_cases c
  · change (kmswStepOfStep s .left).present 0 = false
    cases hUL : s.UL.dropLast.reverse with
    | nil =>
      simp only [kmswStepOfStep, hUL, State.addEdge]
      simp [hp]
      omega
    | cons a as =>
      simp only [kmswStepOfStep, hUL, State.addEdge]
      simp [hp]
      omega
  · change (kmswStepOfStep s .up).present 0 = false
    simp only [kmswStepOfStep, State.addEdge]
    simp [hp]
    omega
  · change (kmswStepOfStep s .down).present 0 = false
    cases hUR : s.UR with
    | nil =>
      simp only [kmswStepOfStep, hUR, State.addEdge]
      simp [hp]
      omega
    | cons a as =>
      have ha : a ≠ 0 := by
        have := hur a (by simp [hUR])
        omega
      simp only [kmswStepOfStep, hUR]
      simp [hp]
      omega

private theorem kmswStep_agreeOffRoot (s t : State)
    (h : State.AgreeOffRoot s t) (c : Fin 3) :
    State.AgreeOffRoot (kmswStep s c) (kmswStep t c) := by
  cases s with
  | mk snv sne sw se sp stri sa sul sur sll slr =>
    cases t with
    | mk tnv tne tw te tp ttri ta tul tur tll tlr =>
      simp only [State.AgreeOffRoot] at h
      rcases h with ⟨rfl, rfl, hwest, heast, hp, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hwest' : sw = tw := funext hwest
      have heast' : se = te := funext heast
      subst tw
      subst te
      cases hcode : kmswCodeStep c with
      | left =>
        cases hUL : sul.dropLast.reverse with
        | nil =>
          simp only [State.AgreeOffRoot, kmswStep, hcode,
            kmswStepOfStep, hUL, State.addEdge]
          simp only [true_and, and_true, forall_const]
          all_goals
            intro e he
            simp [hp e he]
        | cons a as =>
          simp only [State.AgreeOffRoot, kmswStep, hcode,
            kmswStepOfStep, hUL, State.addEdge]
          simp only [true_and, and_true, forall_const]
          all_goals
            intro e he
            simp [hp e he]
      | up =>
        simp only [State.AgreeOffRoot, kmswStep, hcode,
          kmswStepOfStep, State.addEdge]
        simp only [true_and, and_true, forall_const]
        all_goals
          intro e he
          simp [hp e he]
      | down =>
        cases hUR : sur with
        | nil =>
          simp only [State.AgreeOffRoot, kmswStep, hcode,
            kmswStepOfStep, State.addEdge]
          simp only [true_and, and_true, forall_const]
          all_goals
            intro e he
            simp [hp e he]
        | cons a as =>
          simp only [State.AgreeOffRoot, kmswStep, hcode,
            kmswStepOfStep]
          simp only [true_and, and_true, forall_const]
          all_goals
            intro e he
            simp [hp e he]

/-- The root remains absent through every missing-root KMSW stage -/
theorem kmswMissingRootStage_present_zero (w : ℕ → Fin 3) (n : ℕ) :
    (kmswMissingRootStage w n).present 0 = false := by
  induction n with
  | zero => exact kmswMissingRootInit_present_zero
  | succ n ih =>
    rw [kmswMissingRootStage]
    exact kmswStep_present_zero _ ih
      (kmswMissingRootStage_boundaryInv w n).1
      (kmswMissingRootStage_boundaryInv w n).2 (w n)

/-- The missing-root and ordinary KMSW stages agree on all state fields
except `present 0`; agreement includes both endpoints, the triangle list,
active and next IDs, all four boundary lists, and presence of each nonzero -/
theorem kmswMissingRootStage_agree (w : ℕ → Fin 3) (n : ℕ) :
    State.AgreeOffRoot (kmswMissingRootStage w n) (kmswStage w n) := by
  induction n with
  | zero =>
    simp [State.AgreeOffRoot, kmswMissingRootStage, kmswStage,
      kmswMissingRootInit, kmswInit]
  | succ n ih =>
    rw [kmswMissingRootStage, kmswStage]
    exact kmswStep_agreeOffRoot _ _ ih (w n)

