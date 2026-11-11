/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39BallOrbitComponents8
public import DirectedDistances.PlanarMap.EdgeRestrictedDrawing

/-! # Obstruction to unrestricted reversal-pair deletion

Helpers toward Proposition 5.16 (`prop-disk-bs-conv`,
deletion statement is false for a one-vertex, one-loop rotation system.
This file records that obstruction without changing the target's hypotheses. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap
namespace CombinatorialMap

/-- Helper toward Proposition 5.16: a single geometric loop has two darts,
exchanged by both edge reversal and the rotation at its sole vertex. -/
@[expose] def oneLoopDeletionCounterexample : CombinatorialMap Bool :=
  let p : Equiv.Perm Bool :=
    { toFun := Bool.not
      invFun := Bool.not
      left_inv := by decide
      right_inv := by decide }
  { edgeInv := p
    edgeInv_invol := by decide
    edgeInv_ne := by decide
    rot := p }

/-- Helper toward Proposition 5.16: the one-loop map satisfies exactly
the rotation/edge-reversal connectedness used in the insertion step. -/
theorem oneLoopDeletionCounterexample_connected (d e : Bool) :
    Relation.EqvGen
      (fun x y => oneLoopDeletionCounterexample.rot x = y ∨
        oneLoopDeletionCounterexample.edgeInv x = y) d e := by
  cases d <;> cases e
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (Or.inr rfl)
  · exact Relation.EqvGen.rel _ _ (Or.inr rfl)
  · exact Relation.EqvGen.refl _

/-- Helper toward Proposition 5.16: this connected map meets the proposed
non-tree edge-count hypothesis, with equality of edge and vertex counts. -/
theorem oneLoopDeletionCounterexample_numEdges_eq_numVertices :
    oneLoopDeletionCounterexample.numEdges =
      oneLoopDeletionCounterexample.numVertices := rfl

/-- Helper toward Proposition 5.16: every dart of the counterexample is
incident to the same rotation-cycle vertex. -/
theorem oneLoopDeletionCounterexample_same_vertex (d e : Bool) :
    oneLoopDeletionCounterexample.rot.SameCycle d e := by
  cases d <;> cases e
  · exact Equiv.Perm.SameCycle.rfl
  · exact ⟨1, rfl⟩
  · exact ⟨1, rfl⟩
  · exact Equiv.Perm.SameCycle.rfl

/-- Helper toward Proposition 5.16: the counterexample has exactly one
rotation-cycle vertex, rather than merely equal edge and vertex counts. -/
theorem oneLoopDeletionCounterexample_numVertices :
    oneLoopDeletionCounterexample.numVertices = 1 := by
  classical
  let : Unique (VertexQuotient oneLoopDeletionCounterexample) :=
    { default := Quotient.mk _ false
      uniq := by
        intro q
        induction q using Quotient.inductionOn with
        | _ d =>
          exact Quotient.sound (oneLoopDeletionCounterexample_same_vertex d false) }
  exact Fintype.card_unique

/-- Helper toward Proposition 5.16: the counterexample has exactly one
edge orbit, so it satisfies the stated non-tree inequality with equality. -/
theorem oneLoopDeletionCounterexample_numEdges :
    oneLoopDeletionCounterexample.numEdges = 1 :=
  oneLoopDeletionCounterexample_numEdges_eq_numVertices.trans
    oneLoopDeletionCounterexample_numVertices

/-- Helper toward Proposition 5.16: deleting either reversal pair in the
one-loop map leaves no dart, hence cannot retain its vertex. -/
theorem oneLoopDeletionCounterexample_no_remaining_dart (d₀ : Bool) :
    ¬ ∃ e : Bool, e ≠ d₀ ∧
      e ≠ oneLoopDeletionCounterexample.edgeInv d₀ := by
  cases d₀ <;> decide




theorem oneLoopDeletionCounterexample_no_vertex_survival :
    ¬ ∃ d₀ : Bool, ∀ d : Bool, ∃ e : Bool,
      oneLoopDeletionCounterexample.rot.SameCycle d e ∧
        e ≠ d₀ ∧ e ≠ oneLoopDeletionCounterexample.edgeInv d₀ := by
  rintro ⟨d₀, h⟩
  obtain ⟨e, _, he⟩ := h d₀
  exact oneLoopDeletionCounterexample_no_remaining_dart d₀ ⟨e, he⟩

end CombinatorialMap
end DirectedDistances.PlanarMap
end



































































