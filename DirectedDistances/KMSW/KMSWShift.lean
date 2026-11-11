module

public import DirectedDistances.KMSW.StageIncidence
import DirectedDistances.KMSW.CutEquivalence

/-! # Shifted finite KMSW stages

The run of the code after time `t` is a run from the global time-`t` state.
This file also records the rooted one-edge embedding at the initial shifted
stage. The source definition is `def-kmsw`, -/

public section
namespace DirectedDistances.KMSW

/-- Run a code from an arbitrary finite KMSW state, using the update cases of -/
@[expose] def kmswRun (s : State) (u : ℕ → Fin 3) : ℕ → State
  | 0 => s
  | n + 1 => kmswStep (kmswRun s u n) (u n)

/-- The shifted code run, started from the global time-`t` state, agrees at
every finite time with the corresponding global stage (`def-kmsw`,
invariant for a future-stage embedding. -/
theorem kmswRun_shift_eq_stage (w : ℕ → Fin 3) (t m : ℕ) :
    kmswRun (kmswStage w t) (fun i => w (t + i)) m = kmswStage w (t + m) := by
  induction m with
  | zero => simp [kmswRun]
  | succ m ih => simp [kmswRun, kmswStage, ih]

/-- Edge map for the initial shifted one-edge stage. It sends its root to the
global active edge at time `t` (`def-kmsw`, -/
@[expose] def kmswShiftRootEdgeMap (w : ℕ → Fin 3) (t : ℕ) :
    Fin 1 → Fin (kmswStage w t).nextEdge :=
  fun _ => ⟨act w t, act_lt_nextEdge w (Nat.le_refl t)⟩

/-- Vertex map for the initial shifted one-edge stage: its two vertices map to
the two endpoints of the global active edge at time `t` (`def-kmsw`, -/
@[expose] def kmswShiftRootVertexMap (w : ℕ → Fin 3) (t : ℕ) :
    Fin 2 → Fin (kmswStage w t).nextVertex := by
  let s := kmswStage w t
  let h := kmswStage_endpoints_lt_nextVertex w t (act w t)
    (act_lt_nextEdge w (Nat.le_refl t))
  exact fun v => if v.val = 0 then ⟨s.west s.active, h.1⟩ else ⟨s.east s.active, h.2⟩

/-- The initial shifted edge map is injective on its allocated edge set. -/
theorem kmswShiftRootEdgeMap_injective (w : ℕ → Fin 3) (t : ℕ) :
    Function.Injective (kmswShiftRootEdgeMap w t) := by
  intro a b _
  exact Subsingleton.elim a b

/-- The initial edge map sends the shifted active edge at time zero to the
global active edge at time `t` (`def-kmsw`, -/
theorem kmswShiftRoot_active (w : ℕ → Fin 3) (t : ℕ) :
    kmswShiftRootEdgeMap w t
        ⟨act (fun i => w (t + i)) 0,
          act_lt_nextEdge (fun i => w (t + i)) (Nat.le_refl 0)⟩ =
      ⟨act w (t + 0), act_lt_nextEdge w (Nat.le_add_right t 0)⟩ := by
  simp [kmswShiftRootEdgeMap, act]

/-- The two endpoints of a finite active edge are distinct, so the initial
shifted vertex map is injective. The separation follows from the active-edge -/
theorem kmswShiftRootVertexMap_injective (w : ℕ → Fin 3) (t : ℕ) :
    Function.Injective (kmswShiftRootVertexMap w t) := by
  let s := kmswStage w t
  have hact : act w t < s.nextEdge := act_lt_nextEdge w (Nat.le_refl t)
  have hwest : activeInitial w t = s.west s.active :=
    (edge_endpoints_eq w hact).1.symm
  have hne : s.east s.active ≠ s.west s.active := by
    intro h
    have hh := activeEast_ne_activeInitial w (j := t) (n := t) (Nat.le_refl t)
    apply hh
    rw [hwest]
    exact h
  intro a b hab
  have ha : a = 0 ∨ a = 1 := by
    have := a.isLt
    by_cases h : a.val = 0
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext (by omega))
  have hb : b = 0 ∨ b = 1 := by
    have := b.isLt
    by_cases h : b.val = 0
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext (by omega))
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb]
  · subst a
    subst b
    have hval := congrArg Fin.val hab
    change s.west s.active = s.east s.active at hval
    exact (hne hval.symm).elim
  · subst a
    subst b
    have hval := congrArg Fin.val hab
    change s.east s.active = s.west s.active at hval
    exact (hne hval).elim
  · rw [ha, hb]

/-- At shifted time zero, the root edge and its west/east endpoints are
preserved by the one-edge embedding (`def-kmsw`, -/
theorem kmswShiftRoot_incidence (w : ℕ → Fin 3) (t : ℕ) :
    (kmswStage w t).west (kmswShiftRootEdgeMap w t ⟨0, by omega⟩).val =
        (kmswShiftRootVertexMap w t ⟨0, by omega⟩).val ∧
      (kmswStage w t).east (kmswShiftRootEdgeMap w t ⟨0, by omega⟩).val =
        (kmswShiftRootVertexMap w t ⟨1, by omega⟩).val := by
  simp [act, kmswShiftRootEdgeMap, kmswShiftRootVertexMap]

end DirectedDistances.KMSW
