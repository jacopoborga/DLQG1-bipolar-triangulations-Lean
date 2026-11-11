/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLChordImageHomeomorph
public import DirectedDistances.PlanarMap.D39PLPendantInsertion
public import DirectedDistances.PlanarMap.FiniteDrawingExterior

/-! # Image homeomorphisms after chord and pendant insertion -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set Topology

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)

/-- Helper toward Proposition 5.16: a finite PL drawing has closed image. -/
theorem plDrawing_image_isClosed [Finite V] (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) :
    IsClosed P.image := P.isCompact_image.isClosed

/-- Helper toward Proposition 5.16: a pendant arc meets the old drawing exactly
at its attachment point. -/
theorem image_inter_insertPendant_image
    (a : B.D) (c : ℂ) (hc : c ∉ P.image) (g : Polyline)
    (_hg : g.IsSimple) (hs : g.start = P.pos (vert a)) (hf : g.finish = c)
    (hdis : Disjoint g.interior P.image) :
    g.image ∩ P.image = {g.start} := by
  have hstartP : g.start ∈ P.image := by
    rw [hs]
    exact Or.inl ⟨vert a, rfl⟩
  have hstartG : g.start ∈ g.image := Or.inl rfl
  ext z
  constructor
  · rintro ⟨hzG, hzP⟩
    by_cases hs' : z = g.start
    · simp [hs']
    have hf' : z ≠ g.finish := by
      intro h
      have hzfinish : g.finish ∈ P.image := h.symm ▸ hzP
      exact hc (by simpa only [hf] using hzfinish)
    have hzI : z ∈ g.interior := ⟨hzG, by simp [hs', hf']⟩
    exact False.elim (Set.disjoint_left.mp hdis hzI hzP)
  · intro hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact ⟨hstartG, hstartP⟩






















































































end D39FiniteBall
end DirectedDistances.PlanarMap
end
