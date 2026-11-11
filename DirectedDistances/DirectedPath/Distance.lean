/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ENat.Basic

/-! # Shortest directed distance

Infrastructure for manuscript label `def-ldp` (Definition 1.2). Paths retain their
arrows, including parallel arrows, and include the empty path. `ℕ∞` is Mathlib's
`WithTop ℕ`; unreachable distance is `⊤`. No finiteness or acyclicity is assumed. -/

@[expose] public section

namespace DirectedDistances

open Quiver

universe u v
variable {V : Type u} [Quiver.{v} V] {a b c : V}

/-- Shortest directed distance: the infimum of all edge-path lengths, with `⊤`
for unreachable endpoints. This implements the SDP convention of `def-ldp`. -/
noncomputable def sdp (a b : V) : ℕ∞ :=
  ⨅ p : Path a b, (p.length : ℕ∞)

/-- Every directed path bounds shortest distance from above. -/
theorem sdp_le_length (p : Path a b) : sdp a b ≤ p.length :=
  iInf_le _ p

/-- Infinity is exactly the absence of a directed path. -/
@[simp] theorem sdp_eq_top_iff_not_reachable : sdp a b = ⊤ ↔ ¬ Reachable a b := by
  rw [sdp, ENat.iInf_natCast_eq_top]
  exact ⟨fun h ⟨p⟩ => h.false p, fun h => ⟨fun p => h ⟨p⟩⟩⟩

/-- The empty path gives self-distance zero. -/
@[simp] theorem sdp_self (a : V) : sdp a a = 0 :=
  le_antisymm (sdp_le_length (Path.nil : Path a a)) zero_le

/-- Whenever the endpoints are reachable, the shortest distance is attained. -/
theorem exists_length_eq_sdp (h : Reachable a b) :
    ∃ p : Path a b, (p.length : ℕ∞) = sdp a b := by
  let : Nonempty (Path a b) := h
  exact ENat.exists_eq_iInf _

/-- Zero shortest distance identifies the endpoints, even in quivers with cycles. -/
@[simp] theorem sdp_eq_zero_iff : sdp a b = 0 ↔ a = b := by
  constructor
  · intro h
    have hr : Reachable a b := by
      by_contra hn
      have ht := sdp_eq_top_iff_not_reachable.mpr hn
      rw [h] at ht
      exact ENat.zero_ne_top ht
    obtain ⟨p, hp⟩ := exists_length_eq_sdp hr
    have hz : p.length = 0 := by
      simpa only [h, Nat.cast_eq_zero] using hp
    exact p.eq_of_length_zero hz
  · rintro rfl
    exact sdp_self _

/-- Directed triangle inequality, including the cases with an unreachable leg. -/
theorem sdp_triangle (a b c : V) : sdp a c ≤ sdp a b + sdp b c := by
  classical
  by_cases hab : Reachable a b
  · by_cases hbc : Reachable b c
    · obtain ⟨p, hp⟩ := exists_length_eq_sdp hab
      obtain ⟨q, hq⟩ := exists_length_eq_sdp hbc
      calc
        sdp a c ≤ ((p.comp q).length : ℕ∞) := sdp_le_length _
        _ = sdp a b + sdp b c := by
          rw [Path.length_comp, ENat.natCast_add, hp, hq]
    · rw [sdp_eq_top_iff_not_reachable.mpr hbc]
      simp only [add_top, le_top]
  · rw [sdp_eq_top_iff_not_reachable.mpr hab]
    simp only [top_add, le_top]

end DirectedDistances
