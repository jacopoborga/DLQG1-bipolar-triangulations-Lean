/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.Definition32SideTransport
public import DirectedDistances.PlanarMap.BoundaryPresentationData

/-! # Transport of finite boundary presentations -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

variable {V E V' E' : Type*}
variable {M : DirectedPlaneMapWithMissing V E}
variable {M' : DirectedPlaneMapWithMissing V' E'}

namespace DirectedPlaneMapWithMissing.HomeoEquiv

/-- Helper toward Definition 3.2: map a boundary dart through the edge
bijection, retaining its traversal bit. -/
@[expose] def mapDart (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (d : E × Bool) : E' × Bool := (e.drawing.drawing.σE d.1, d.2)

/-- Helper toward Definition 3.2: push forward a finite boundary presentation
through the edge bijection, retaining the cuts and all block lengths. -/
@[expose] def pushforward (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) : FiniteBoundaryPresentation M' where
  word := P.word.map e.mapDart
  c0 := P.c0
  c1 := P.c1
  c2 := P.c2
  c3 := P.c3
  c0_eq_zero := P.c0_eq_zero
  cuts_le := by simpa using P.cuts_le

@[simp] theorem pushforward_word (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) :
    (e.pushforward P).word = P.word.map e.mapDart := rfl

@[simp] theorem pushforward_cuts (e : DirectedPlaneMapWithMissing.HomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) :
    (e.pushforward P).c0 = P.c0 ∧ (e.pushforward P).c1 = P.c1 ∧
      (e.pushforward P).c2 = P.c2 ∧ (e.pushforward P).c3 = P.c3 :=
  ⟨rfl, rfl, rfl, rfl⟩

















end DirectedPlaneMapWithMissing.HomeoEquiv

end DirectedDistances.PlanarMap

end
