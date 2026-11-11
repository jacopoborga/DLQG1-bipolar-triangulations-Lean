/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLChordInsertion
public import DirectedDistances.PlanarMap.D39PLSimpleArcParam
public import DirectedDistances.PlanarMap.D39PLDrawingHomeomorph

/-! # Homeomorphisms after chord insertion -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set Topology

namespace D39FiniteBall

variable {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
  (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)

/-- Helper toward Proposition 5.16: a simple inserted chord has a
homeomorphism to its counterpart whose endpoint values agree with the old
drawing homeomorphism at both named vertices. -/
theorem exists_insertChord_arc_homeomorph
    (f : B.PLImageHomeomorph vert P P') (a b : B.D)
    (hvab : vert a ≠ vert b) (g g' : Polyline)
    (hg : g.IsSimple) (hg' : g'.IsSimple)
    (hstart : g.start = P.pos (vert a))
    (hfinish : g.finish = P.pos (vert b))
    (hstart' : g'.start = P'.pos (vert a))
    (hfinish' : g'.finish = P'.pos (vert b)) :
    ∃ h : g.image ≃ₜ g'.image,
      (h ⟨g.start, Or.inl rfl⟩ : ℂ) = g'.start ∧
      (h ⟨g.finish, by
        rw [← g.point_last_eq_finish]
        exact g.point_mem_image (by
          have hpos : 0 < g.points.length := List.length_pos_iff.mpr g.nonempty
          omega)⟩ : ℂ) = g'.finish ∧
      (h ⟨g.start, Or.inl rfl⟩ : ℂ) =
        (f.toHomeomorph ⟨P.pos (vert a), Or.inl ⟨vert a, rfl⟩⟩ : ℂ) ∧
      (h ⟨g.finish, by
        rw [← g.point_last_eq_finish]
        exact g.point_mem_image (by
          have hpos : 0 < g.points.length := List.length_pos_iff.mpr g.nonempty
          omega)⟩ : ℂ) =
        (f.toHomeomorph ⟨P.pos (vert b), Or.inl ⟨vert b, rfl⟩⟩ : ℂ) := by
  have hpne : g.start ≠ g.finish := by
    rw [hstart, hfinish]
    exact fun he => hvab (P.pos_injective he)
  have hpne' : g'.start ≠ g'.finish := by
    rw [hstart', hfinish']
    exact fun he => hvab (P'.pos_injective he)
  obtain ⟨h, hstart_h, hfinish_h⟩ :=
    Polyline.exists_image_homeomorph_endpoints g g' hg hg' hpne hpne'
  refine ⟨h, hstart_h, hfinish_h, ?_, ?_⟩
  · calc
      (h ⟨g.start, Or.inl rfl⟩ : ℂ) = g'.start := hstart_h
      _ = P'.pos (vert a) := hstart'
      _ = (f.toHomeomorph ⟨P.pos (vert a), Or.inl ⟨vert a, rfl⟩⟩ : ℂ) :=
        (f.vertex_image (vert a)).symm
  · calc
      (h ⟨g.finish, by
        rw [← g.point_last_eq_finish]
        exact g.point_mem_image (by
          have hpos : 0 < g.points.length := List.length_pos_iff.mpr g.nonempty
          omega)⟩ : ℂ) = g'.finish := hfinish_h
      _ = P'.pos (vert b) := hfinish'
      _ = (f.toHomeomorph ⟨P.pos (vert b), Or.inl ⟨vert b, rfl⟩⟩ : ℂ) :=
        (f.vertex_image (vert b)).symm

/-- Helper toward Proposition 5.16: when the chord interior avoids the old
drawing image, the chord meets that image exactly at its two endpoints. -/
theorem image_inter_insertChord_image
    (a b : B.D) (g : Polyline)
    (hstart : g.start = P.pos (vert a))
    (hfinish : g.finish = P.pos (vert b))
    (hdis : Disjoint g.interior P.image)
    (hlen : 2 ≤ g.points.length) :
    g.image ∩ P.image = {g.start, g.finish} := by
  have hstartP : g.start ∈ P.image := by
    rw [hstart]
    exact Or.inl ⟨vert a, rfl⟩
  have hfinishP : g.finish ∈ P.image := by
    rw [hfinish]
    exact Or.inl ⟨vert b, rfl⟩
  have hfinishG : g.finish ∈ g.image := by
    rw [← g.point_last_eq_finish]
    exact g.point_mem_image (by omega)
  ext z
  constructor
  · rintro ⟨hzG, hzP⟩
    by_cases hs : z = g.start
    · simp [hs]
    by_cases hf : z = g.finish
    · simp [hf]
    · have hzI : z ∈ g.interior := by
        exact ⟨hzG, by simp [hs, hf]⟩
      exact False.elim (Set.disjoint_left.mp hdis hzI hzP)
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hs | hf
    · subst z
      exact ⟨Or.inl rfl, hstartP⟩
    · subst z
      exact ⟨hfinishG, hfinishP⟩






























































end D39FiniteBall
end DirectedDistances.PlanarMap
end
