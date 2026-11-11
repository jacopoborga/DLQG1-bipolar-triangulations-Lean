/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.DirectedPath.Extremal
public import Mathlib.Algebra.Group.Int.Defs

/-! # Distance additivity at a compulsory visited vertex

Deterministic quiver infrastructure for the distance decomposition in the proof
separator property is an explicit input to these helpers, not an assumed premise
of any manuscript theorem. No random separator or Busemann function is defined.
Natural/integer cancellation below is used only after reachability proves that
the relevant SDP values are finite. -/

public section
namespace DirectedDistances

open Quiver

universe u v
variable {V : Type u} [Quiver.{v} V] {a a' b c : V}

/-- If every competitor visits the junction, concatenating two shortest pieces
is shortest. The compulsory-visit premise is exposed and consumed by splitting. -/
theorem IsShortest.comp_of_forall_mem_vertices {p : Path a b} {q : Path b c}
    (hp : IsShortest p) (hq : IsShortest q) (hb : ∀ r : Path a c, b ∈ r.vertices) :
    IsShortest (p.comp q) := by
  intro r
  obtain ⟨r₁, r₂, heq⟩ := r.exists_eq_comp_of_mem_vertices (hb r)
  rw [Path.length_comp, heq, Path.length_comp]
  exact Nat.add_le_add (hp r₁) (hq r₂)

/-- The maximizing version of compulsory-junction concatenation. No ambient
finiteness is needed once both actual maximizing pieces are supplied. -/
theorem IsLongest.comp_of_forall_mem_vertices {p : Path a b} {q : Path b c}
    (hp : IsLongest p) (hq : IsLongest q) (hb : ∀ r : Path a c, b ∈ r.vertices) :
    IsLongest (p.comp q) := by
  intro r
  obtain ⟨r₁, r₂, heq⟩ := r.exists_eq_comp_of_mem_vertices (hb r)
  rw [heq, Path.length_comp, Path.length_comp]
  exact Nat.add_le_add (hp r₁) (hq r₂)

/-- SDP is additive at a vertex visited by every path, including unreachable
cases. In particular, no subtraction at infinity appears in this theorem. -/
theorem sdp_eq_add_of_forall_mem_vertices (hb : ∀ r : Path a c, b ∈ r.vertices) :
    sdp a c = sdp a b + sdp b c := by
  apply le_antisymm (sdp_triangle a b c)
  apply le_iInf
  intro r
  obtain ⟨p, q, heq⟩ := r.exists_eq_comp_of_mem_vertices (hb r)
  calc
    sdp a b + sdp b c ≤ (p.length : ℕ∞) + (q.length : ℕ∞) :=
      add_le_add (sdp_le_length p) (sdp_le_length q)
    _ = (r.length : ℕ∞) := by rw [heq, Path.length_comp, ENat.natCast_add]

/-- On reachable legs, the additive SDP identity passes to its genuine natural
values. The two finiteness proofs are supplied before applying `toNat_add`. -/
theorem sdp_toNat_eq_add_of_forall_mem_vertices
    (hb : ∀ r : Path a c, b ∈ r.vertices) (hab : Reachable a b) (hbc : Reachable b c) :
    (sdp a c).toNat = (sdp a b).toNat + (sdp b c).toNat := by
  have hab' : sdp a b ≠ ⊤ := fun h => sdp_eq_top_iff_not_reachable.1 h hab
  have hbc' : sdp b c ≠ ⊤ := fun h => sdp_eq_top_iff_not_reachable.1 h hbc
  rw [sdp_eq_add_of_forall_mem_vertices hb, ENat.toNat_add hab' hbc']

/-- Two finite shortest-distance differences agree beyond a common compulsory
junction. This is a deterministic cancellation lemma, not a Busemann existence
or uniqueness theorem. Each required finite leg has an explicit path witness. -/
theorem sdp_difference_eq_of_common_separator
    (hb : ∀ r : Path a c, b ∈ r.vertices)
    (hb' : ∀ r : Path a' c, b ∈ r.vertices)
    (hab : Reachable a b) (ha'b : Reachable a' b) (hbc : Reachable b c) :
    ((sdp a' c).toNat : ℤ) - ((sdp a c).toNat : ℤ) =
      ((sdp a' b).toNat : ℤ) - ((sdp a b).toNat : ℤ) := by
  rw [sdp_toNat_eq_add_of_forall_mem_vertices hb hab hbc,
    sdp_toNat_eq_add_of_forall_mem_vertices hb' ha'b hbc,
    Int.natCast_add, Int.natCast_add, add_sub_add_right_eq_sub]

/-- Finite acyclic LDP has the analogous additive decomposition at a compulsory
vertex. Reachability of both legs supplies actual maximizing paths. -/
theorem finiteLdp_eq_add_of_forall_mem_vertices [Fintype V] (ha : acyclic V)
    (hb : ∀ r : Path a c, b ∈ r.vertices) (hab : Reachable a b) (hbc : Reachable b c) :
    finiteLdp ha a c = finiteLdp ha a b + finiteLdp ha b c := by
  obtain ⟨p, hp⟩ := exists_isLongest ha hab
  obtain ⟨q, hq⟩ := exists_isLongest ha hbc
  exact finiteLdp_eq_add_of_isLongest_comp ha (hp.comp_of_forall_mem_vertices hq hb)

end DirectedDistances
