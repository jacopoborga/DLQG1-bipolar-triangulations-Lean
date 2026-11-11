/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesSurj

/-! # Converse winding-side obligations for Definition 3.2

closure consequence below follows directly from `LeftAtOn`. It does not give
the uniform initial wedge needed for `dartBorders`, and the exact converse
statements remain recorded with their full binders below. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval

universe uV uE uUL uUR uLR uLL

/-- Helper toward Definition 3.2: a left winding-side test implies that the
tested path point lies in the closure of the face. -/
theorem leftAtOn_mem_closure {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (s : {t : I // t ∈ openParams}) (hside : LeftAtOn F γ s) :
    γ s.1 ∈ closure F := by
  rcases hside with ⟨a, b, ha, has, hsb, hb, q, hqi, hq, hcl⟩
  let loop := (edgeSubarc γ a b (le_of_lt (lt_trans has hsb))).trans q
  have hsubset : {w : ℂ | w ∈ F ∧ HasWinding loop w 1} ⊆ F := by
    intro z hz
    exact hz.1
  exact closure_mono hsubset hcl



















































































































end DirectedDistances.PlanarMap

end
