/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Data.Fintype.Card

/-! # Acyclic directed paths

The predicate below means absence of nonempty directed closed paths, the
acyclicity convention in manuscript label `def-bipolar`. It does not assume a
ranking, a length bound, or any extremal-distance conclusion. Quivers may have
parallel arrows; in particular no thinness assumption is made. -/

@[expose] public section
namespace DirectedDistances

open Quiver

universe u v
variable {V : Type u} [Quiver.{v} V] {a b c : V}

/-- A quiver is acyclic when every directed closed path has length zero. -/
def acyclic (V : Type u) [Quiver.{v} V] : Prop :=
  ∀ (a : V) (p : Path a a), p.length = 0

/-- In an acyclic quiver a closed path is the empty path. -/
theorem eq_nil_of_acyclic (h : acyclic V) (p : Path a a) : p = Path.nil :=
  p.eq_nil_of_length_zero (h a p)

/-- No directed path in an acyclic quiver repeats a vertex. -/
theorem vertices_nodup_of_acyclic (h : acyclic V) (p : Path a b) : p.vertices.Nodup := by
  induction p with
  | nil => exact List.nodup_singleton _
  | @cons b c p e ih =>
    rw [Path.vertices_cons, List.nodup_concat]
    refine ⟨?_, ih⟩
    intro hc
    obtain ⟨p₁, p₂, _⟩ := p.exists_eq_comp_of_mem_vertices hc
    have hz := h c (p₂.cons e)
    exact Nat.noConfusion hz

/-- A directed path on a finite acyclic vertex type uses at most card(V)−1 arrows. -/
theorem length_lt_card_of_acyclic [Fintype V] (h : acyclic V) (p : Path a b) :
    p.length < Fintype.card V := by
  have hb := (vertices_nodup_of_acyclic h p).length_le_card
  rw [Path.vertices_length] at hb
  exact hb

/-- Concatenation remains a path without repeated vertices in an acyclic quiver.
This includes the shared junction once and rules out overlap elsewhere. -/
theorem vertices_comp_nodup_of_acyclic (h : acyclic V) (p : Path a b) (q : Path b c) :
    (p.comp q).vertices.Nodup :=
  vertices_nodup_of_acyclic h (p.comp q)

end DirectedDistances
