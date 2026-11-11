/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole7

/-! Transport of the adjusted finite-prefix rotation and the resulting marked
side across streams with a common stopped prefix. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

universe u

/-- Helper toward Lemma 5.5: transport along a reflexive type equality is the
identity equivalence. This is the cast simplification needed after eliminating
the equality of finite KMSW states. -/
theorem transportEquivOfTypeEq_self {α : Type u} (h : α = α) :
    transportEquivOfTypeEq h = Equiv.refl α := by
  have hh : h = rfl := Subsingleton.elim _ _
  rw [hh]
  rfl

/-- Helper toward Lemma 5.5: the quotient-dart transport induced by a
reflexive equality of finite states is the identity. -/
theorem rMinusCodeGluedDartEquiv_identity_of_stateRefl
    (F : State) (M : GeometricSideSubmap) (h : F = F) :
    transportEquivOfTypeEq
      (congrArg (fun s : State => RMinusCodeGluedDart s M) h) = Equiv.refl _ :=
  transportEquivOfTypeEq_self _


























































end DirectedDistances.PaperProofs.Section5
