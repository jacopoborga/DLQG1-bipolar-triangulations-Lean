/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.DirectedPath.Finite

/-! # Extremal directed paths and replacement

Generic quiver infrastructure for `def-geodesic`
paths. No planar leftmost order or infinite geodesic is constructed here.

The shortest-path predicate works on every quiver. The longest-path predicate
also makes sense on every quiver but may have no witness. Its distance
characterization below is restricted to the proved finite acyclic LDP domain. -/

@[expose] public section
namespace DirectedDistances

open Quiver

universe u v
variable {V : Type u} [Quiver.{v} V] {a b c d : V}

/-- A path minimizes length among all directed paths with the same endpoints. -/
def IsShortest (p : Path a b) : Prop := ∀ q : Path a b, p.length ≤ q.length

/-- A path maximizes length among all directed paths with the same endpoints.
This predicate does not assert that such a path exists on an infinite quiver. -/
def IsLongest (p : Path a b) : Prop := ∀ q : Path a b, q.length ≤ p.length

/-- Shortest-path extremality is exactly equality with the shortest distance. -/
theorem isShortest_iff_length_eq_sdp (p : Path a b) :
    IsShortest p ↔ (p.length : ℕ∞) = sdp a b := by
  constructor
  · intro h
    apply le_antisymm
    · apply le_iInf
      intro q
      exact ENat.natCast_le_natCast.mpr (h q)
    · exact sdp_le_length p
  · intro h q
    apply ENat.natCast_le_natCast.mp
    rw [h]
    exact sdp_le_length q

/-- Reachability supplies a shortest path without any finiteness hypothesis. -/
theorem exists_isShortest (h : Reachable a b) : ∃ p : Path a b, IsShortest p := by
  obtain ⟨p, hp⟩ := exists_length_eq_sdp h
  exact ⟨p, (isShortest_iff_length_eq_sdp p).2 hp⟩

/-- A prefix of a shortest path is shortest, by replacement and cancellation. -/
theorem IsShortest.of_comp_left {p : Path a b} {q : Path b c}
    (h : IsShortest (p.comp q)) : IsShortest p := by
  intro r
  have hr := h (r.comp q)
  rw [Path.length_comp, Path.length_comp] at hr
  exact Nat.le_of_add_le_add_right hr

/-- A suffix of a shortest path is shortest. -/
theorem IsShortest.of_comp_right {p : Path a b} {q : Path b c}
    (h : IsShortest (p.comp q)) : IsShortest q := by
  intro r
  have hr := h (p.comp r)
  rw [Path.length_comp, Path.length_comp] at hr
  exact Nat.le_of_add_le_add_left hr

/-- Every middle segment of a shortest path is shortest, including empty segments. -/
theorem IsShortest.of_comp_middle {p : Path a b} {q : Path b c} {r : Path c d}
    (h : IsShortest ((p.comp q).comp r)) : IsShortest q :=
  h.of_comp_left.of_comp_right

/-- Replacing a shortest path by another path of the same length preserves
extremality. This retains the identities of all alternative parallel arrows. -/
theorem IsShortest.of_length_eq {p q : Path a b} (h : IsShortest p)
    (hpq : q.length = p.length) : IsShortest q := by
  intro r
  rw [hpq]
  exact h r

/-- A prefix of a longest path is longest; no global finiteness is needed once
an actual maximizing path is supplied. -/
theorem IsLongest.of_comp_left {p : Path a b} {q : Path b c}
    (h : IsLongest (p.comp q)) : IsLongest p := by
  intro r
  have hr := h (r.comp q)
  rw [Path.length_comp, Path.length_comp] at hr
  exact Nat.le_of_add_le_add_right hr

/-- A suffix of a longest path is longest. -/
theorem IsLongest.of_comp_right {p : Path a b} {q : Path b c}
    (h : IsLongest (p.comp q)) : IsLongest q := by
  intro r
  have hr := h (p.comp r)
  rw [Path.length_comp, Path.length_comp] at hr
  exact Nat.le_of_add_le_add_left hr

/-- Every middle segment of a longest path is longest. -/
theorem IsLongest.of_comp_middle {p : Path a b} {q : Path b c} {r : Path c d}
    (h : IsLongest ((p.comp q).comp r)) : IsLongest q :=
  h.of_comp_left.of_comp_right

/-- Equal-length replacement preserves maximality. -/
theorem IsLongest.of_length_eq {p q : Path a b} (h : IsLongest p)
    (hpq : q.length = p.length) : IsLongest q := by
  intro r
  rw [hpq]
  exact h r

/-- A shortest concatenation realizes equality in the directed triangle inequality. -/
theorem sdp_eq_add_of_isShortest_comp {p : Path a b} {q : Path b c}
    (h : IsShortest (p.comp q)) : sdp a c = sdp a b + sdp b c := by
  rw [← (isShortest_iff_length_eq_sdp _).1 h,
    ← (isShortest_iff_length_eq_sdp _).1 h.of_comp_left,
    ← (isShortest_iff_length_eq_sdp _).1 h.of_comp_right,
    Path.length_comp, ENat.natCast_add]

variable [Fintype V]

/-- On the finite acyclic domain, maximality is exactly equality with finite LDP. -/
theorem isLongest_iff_length_eq_finiteLdp (h : acyclic V) (p : Path a b) :
    IsLongest p ↔ (p.length : WithBot ℕ) = finiteLdp h a b := by
  constructor
  · intro hp
    exact le_antisymm (length_le_finiteLdp h p) (finiteLdp_le h hp)
  · intro hp q
    have hq := length_le_finiteLdp h q
    rw [← hp] at hq
    exact WithBot.coe_le_coe.mp hq

/-- Every reachable pair in a finite acyclic quiver has a longest path. -/
theorem exists_isLongest (h : acyclic V) (hr : Reachable a b) :
    ∃ p : Path a b, IsLongest p := by
  obtain ⟨p, hp⟩ := exists_length_eq_finiteLdp h hr
  exact ⟨p, (isLongest_iff_length_eq_finiteLdp h p).2 hp⟩

/-- A longest concatenation realizes equality in the reverse triangle inequality. -/
theorem finiteLdp_eq_add_of_isLongest_comp (h : acyclic V)
    {p : Path a b} {q : Path b c} (hpq : IsLongest (p.comp q)) :
    finiteLdp h a c = finiteLdp h a b + finiteLdp h b c := by
  rw [← (isLongest_iff_length_eq_finiteLdp h _).1 hpq,
    ← (isLongest_iff_length_eq_finiteLdp h _).1 hpq.of_comp_left,
    ← (isLongest_iff_length_eq_finiteLdp h _).1 hpq.of_comp_right,
    Path.length_comp]
  rfl

end DirectedDistances
