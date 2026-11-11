/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.DirectedPath.Distance

/-! # Directed distances under quiver maps

A quiver map is Mathlib's `Prefunctor`: a vertex map together with a map on each
arrow type. Paths are mapped by the existing `Prefunctor.mapPath`. No injectivity
or simplicity hypothesis is needed for shortest-distance comparison. -/

@[expose] public section

namespace DirectedDistances

open Quiver

universe u v u' v'
variable {V : Type u} [Quiver.{v} V] {W : Type u'} [Quiver.{v'} W]

/-- The existing path map preserves the number of arrows, including for empty paths. -/
@[simp] theorem length_mapPath (F : V ⥤q W) {a b : V} (p : Path a b) :
    (F.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change (F.mapPath p).length + 1 = p.length + 1
    rw [ih]

/-- An arrow-preserving quiver map cannot increase shortest directed distance. -/
theorem sdp_map_le (F : V ⥤q W) (a b : V) :
    sdp (F.obj a) (F.obj b) ≤ sdp a b := by
  apply le_iInf
  intro p
  calc
    sdp (F.obj a) (F.obj b) ≤ ((F.mapPath p).length : ℕ∞) := sdp_le_length _
    _ = (p.length : ℕ∞) := by rw [length_mapPath]

/-- Inclusion of available arrows with the vertex sets identified by an equivalence.
The embeddings retain the identities of parallel arrows. Using an explicit vertex
equivalence also permits distinct source and target quiver carriers. -/
def arrowInclusion (e : V ≃ W)
    (ι : ∀ a b : V, (a ⟶ b) ↪ (e a ⟶ e b)) : V ⥤q W where
  obj := e
  map := fun {a b} f => ι a b f

/-- Adding available arrows, without identifying vertices, cannot increase shortest
 distance. The vertex correspondence and all arrow inclusions are explicit. -/
theorem sdp_le_of_arrowInclusion (e : V ≃ W)
    (ι : ∀ a b : V, (a ⟶ b) ↪ (e a ⟶ e b)) (a b : V) :
    sdp (e a) (e b) ≤ sdp a b :=
  sdp_map_le (arrowInclusion e ι) a b

end DirectedDistances
