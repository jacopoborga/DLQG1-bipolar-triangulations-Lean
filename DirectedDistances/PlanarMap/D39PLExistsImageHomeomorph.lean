/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDrawingHomeomorph
public import DirectedDistances.PlanarMap.D39PLSimpleArcParam
public import DirectedDistances.PlanarMap.D39PLFaceExtension

/-! Helpers toward Proposition 5.16: construction of a drawing-image
homeomorphism from corresponding finite plane drawings. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set Topology

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: choose one dart in each two-element
edge orbit using an arbitrary finite ordering of the dart carrier. -/
@[expose] noncomputable def dartRepresentative (B : D39FiniteBall) (d : B.D) : B.D :=
  let e := Fintype.equivFin B.D
  if e d ≤ e (B.map.edgeInv d) then d else B.map.edgeInv d

/-- Helper toward Proposition 5.16: the chosen dart representative is
unchanged when the dart is reversed. -/
theorem dartRepresentative_edgeInv (B : D39FiniteBall) (d : B.D) :
    B.dartRepresentative (B.map.edgeInv d) = B.dartRepresentative d := by
  classical
  let e : B.D ≃ Fin (Fintype.card B.D) := Fintype.equivFin B.D
  change (if e (B.map.edgeInv d) ≤ e (B.map.edgeInv (B.map.edgeInv d))
      then B.map.edgeInv d else B.map.edgeInv (B.map.edgeInv d)) =
    (if e d ≤ e (B.map.edgeInv d) then d else B.map.edgeInv d)
  by_cases h : e d ≤ e (B.map.edgeInv d)
  · have h' : ¬ e (B.map.edgeInv d) ≤ e d := by
      intro hh
      have he : e (B.map.edgeInv d) = e d := le_antisymm hh h
      exact B.map.edgeInv_ne d (e.injective he)
    simp [B.map.edgeInv_invol, h, h']
  · have h' : e (B.map.edgeInv d) ≤ e d := le_of_not_ge h
    simp [B.map.edgeInv_invol, h, h']

/-- Helper toward Proposition 5.16: each dart is its chosen edge
representative or the reversal of that representative. -/
theorem dart_eq_representative_or_edgeInv (B : D39FiniteBall) (d : B.D) :
    B.dartRepresentative d = d ∨
      B.dartRepresentative d = B.map.edgeInv d := by
  classical
  unfold dartRepresentative
  by_cases h : (Fintype.equivFin B.D) d ≤ (Fintype.equivFin B.D) (B.map.edgeInv d)
  · simp [h]
  · simp [h]

/-- Helper toward Proposition 5.16: reversing a dart does not change its
geometric arc image in either drawing. -/
theorem arc_image_eq_representative (B : D39FiniteBall) {V : Type*}
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D) :
    (P.arc (B.dartRepresentative d)).image = (P.arc d).image := by
  rcases B.dart_eq_representative_or_edgeInv d with h | h
  · rw [h]
  · rw [h, P.arc_flip]
    exact ((P.arc d).reverse_preserves_simple_image_endpoints (P.arc_simple d)).2.1

/-- Helper toward Proposition 5.16: corresponding simple dart arcs admit a
homeomorphism that preserves the named initial and terminal endpoints. -/
theorem exists_dart_arc_homeomorph
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D) :
    ∃ h : (P.arc d).image ≃ₜ (P'.arc d).image,
      (h ⟨(P.arc d).start, Or.inl rfl⟩ : ℂ) = (P'.arc d).start ∧
        (h ⟨(P.arc d).finish, by
          rw [← (P.arc d).point_last_eq_finish]
          exact (P.arc d).point_mem_image (by
            have hpos : 0 < (P.arc d).points.length :=
              List.length_pos_iff.mpr (P.arc d).nonempty
            omega)⟩ : ℂ) = (P'.arc d).finish := by
  exact (P.arc d).exists_image_homeomorph_endpoints (P'.arc d)
    (P.arc_simple d) (P'.arc_simple d)
    (by rw [P.arc_start, P.arc_finish]; exact fun h => P.vert_ne_flip d (P.pos_injective h))
    (by rw [P'.arc_start, P'.arc_finish]; exact fun h => P'.vert_ne_flip d (P'.pos_injective h))

/-- Helper toward Proposition 5.16: the selected representative supplies a
single endpoint-matched homeomorphism for both orientations of each edge. -/
@[expose] noncomputable def dartArcHomeomorph {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) : (P.arc d).image ≃ₜ (P'.arc d).image := by
  let r := B.dartRepresentative d
  let h := Classical.choose (B.exists_dart_arc_homeomorph vert P P' r)
  exact (Homeomorph.setCongr (B.arc_image_eq_representative vert P d).symm).trans
    (h.trans (Homeomorph.setCongr (B.arc_image_eq_representative vert P' d)))

/-- Helper toward Proposition 5.16: the common edge homeomorphism maps
both endpoints to their correspondingly named target vertices. -/
theorem dartArcHomeomorph_endpoints {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) :
    (B.dartArcHomeomorph vert P P' d
      ⟨(P.arc d).start, Or.inl rfl⟩ : ℂ) = P'.pos (vert d) ∧
    (B.dartArcHomeomorph vert P P' d
      ⟨(P.arc d).finish, by
        rw [← (P.arc d).point_last_eq_finish]
        exact (P.arc d).point_mem_image (by
          have hpos : 0 < (P.arc d).points.length :=
            List.length_pos_iff.mpr (P.arc d).nonempty
          omega)⟩ : ℂ) = P'.pos (vert (B.map.edgeInv d)) := by
  classical
  let r := B.dartRepresentative d
  let h := Classical.choose (B.exists_dart_arc_homeomorph vert P P' r)
  have hh := Classical.choose_spec (B.exists_dart_arc_homeomorph vert P P' r)
  rcases B.dart_eq_representative_or_edgeInv d with hd | hd
  · constructor
    · simpa [dartArcHomeomorph, r, h, hd, Homeomorph.setCongr,
        Set.equivOfEq_apply, Set.equivOfEq_symm_apply, P'.arc_start] using hh.1
    · simpa [dartArcHomeomorph, r, h, hd, Homeomorph.setCongr,
        Set.equivOfEq_apply, Set.equivOfEq_symm_apply, P'.arc_finish] using hh.2
  · constructor
    · simpa [dartArcHomeomorph, r, h, hd, P.arc_flip, P'.arc_flip,
        Homeomorph.setCongr, Set.equivOfEq_apply, Set.equivOfEq_symm_apply,
        P.arc_start, P'.arc_start, Polyline.start_reverse, Polyline.finish_reverse] using hh.2
    · simpa [dartArcHomeomorph, r, h, hd, P.arc_flip, P'.arc_flip,
        Homeomorph.setCongr, Set.equivOfEq_apply, Set.equivOfEq_symm_apply,
        P.arc_finish, P'.arc_finish, Polyline.start_reverse, Polyline.finish_reverse] using hh.1





























end D39FiniteBall

end DirectedDistances.PlanarMap
end
