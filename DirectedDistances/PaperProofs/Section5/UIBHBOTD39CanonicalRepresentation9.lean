/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalRepresentation8
public import DirectedDistances.PlanarMap.D39BallOrbitComponents3

/-! Helper toward Proposition 5.16.

This module proves the locally finite frontier decomposition for the PL drawing
carrier used by the canonical assembly. The remaining frontier-incidence
transfer is recorded below with its full binders and current obstruction. -/

public section

namespace DirectedDistances.PlanarMap

open Set Metric Topology

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
variable (P : PLDrawing D V flip rot vert)

/-- Helper toward Proposition 5.16. In a locally finite PL drawing, the
frontier of a face is exactly the union of the closed arcs of the darts
bordering it. The proof uses local finiteness to show that this union is
closed, replacing the finite-carrier argument. -/
theorem frontier_face_eq_iUnion_dartBorders_arcs_of_locallyFinite
    (hvert : Function.Surjective vert) (F : P.Face) :
    frontier F.val = ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image := by
  classical
  let K : Set ℂ := ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image
  let S : D → Set ℂ := fun d =>
    if _ : P.dartBorders d F then (P.arc d).image else ∅
  have hsub : ∀ d, S d ⊆ (P.arc d).image := by
    intro d
    by_cases hd : P.dartBorders d F <;> simp [S, hd]
  have hlocal : LocallyFinite (fun d => (P.arc d).image) := by
    intro z
    refine ⟨ball z 1, ball_mem_nhds z zero_lt_one, ?_⟩
    simpa only [inter_comm] using P.locally_finite (ball z 1) isBounded_ball
  have hclosedS : IsClosed (⋃ d, S d) := by
    apply (hlocal.subset hsub).isClosed_iUnion
    intro d
    dsimp [S]
    split_ifs
    · exact (P.arc d).isCompact_image.isClosed
    · exact isClosed_empty
  have hKS : K = ⋃ d, S d := by
    ext z
    simp [K, S]
  have hclosed : IsClosed K := hKS ▸ hclosedS
  have hKmem (z : ℂ) :
      z ∈ K ↔ ∃ d, ∃ h : P.dartBorders d F, z ∈ (P.arc d).image := by
    simp [K, Set.mem_iUnion]
  apply Subset.antisymm
  · intro q hqfront
    by_contra hqK
    obtain ⟨s, hs, hsafe⟩ := Metric.mem_nhds_iff.mp
      (hclosed.isOpen_compl.mem_nhds hqK)
    have hqimage := (P.face_open_frontier_subset_image hvert F).2 hqfront
    have harc : ∃ d, q ∈ (P.arc d).image := by
      rcases hqimage with ⟨v, rfl⟩ | h
      · obtain ⟨d, rfl⟩ := hvert v
        exact ⟨d, Or.inl (P.arc_start d).symm⟩
      · exact h
    obtain ⟨d, hd⟩ := harc
    have hseg : ∃ i, i + 1 < (P.arc d).points.length ∧
        q ∈ (P.arc d).segmentAt i := by
      rcases hd with hstart | ⟨i, hi, hqi⟩
      · refine ⟨0, by have := P.arc_length d; omega, ?_⟩
        rw [hstart, Polyline.segmentAt, Polyline.point_zero_eq_start]
        exact left_mem_segment ℝ _ _
      · exact ⟨i, hi, hqi⟩
    obtain ⟨i, hi, hqi⟩ := hseg
    by_cases hqend : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1)
    · obtain ⟨x, hx, hxball, hnot⟩ := P.face_endpoint_frontier_not_vertex_mem_ball
        hvert F q d hi hqend (frontier_subset_closure hqfront) hs
      obtain ⟨e, hxe, heF⟩ :=
        P.exists_mem_arc_dartBorders_of_frontier_not_vertex hvert F hx hnot
      have hxK : x ∈ K := by
        rw [hKmem]
        exact ⟨e, heF, hxe⟩
      exact hsafe hxball hxK
    · have hqopen := mem_openSegment_of_ne_left_right
        (fun he => hqend (Or.inl he.symm)) (fun he => hqend (Or.inr he.symm)) hqi
      rcases (P.mem_closure_face_openSegment_iff_dartBorders hvert d F hi hqopen).mp
          (frontier_subset_closure hqfront) with hF | hF
      · have hqK' : q ∈ K := by
          rw [hKmem]
          exact ⟨d, hF, (P.arc d).segmentAt_subset_image hi hqi⟩
        exact hqK hqK'
      · have hqK' : q ∈ K := by
          rw [hKmem]
          refine ⟨flip d, hF, ?_⟩
          rw [P.arc_image_flip]
          exact (P.arc d).segmentAt_subset_image hi hqi
        exact hqK hqK'
  · intro q hq
    obtain ⟨d, hd, hqd⟩ := (hKmem q).mp hq
    exact P.dartBorders_arc_subset_frontier hvert d F hd hqd

end PLDrawing

end DirectedDistances.PlanarMap

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open Set Metric Topology

/-- Helper toward Proposition 5.16. The canonical assembly drawing has a
neighborhood around every plane point met by only finitely many dart arcs;
this is the assembly's `PLDrawing.locally_finite` field applied to a unit ball. -/
theorem uibhbotD39CanonicalAssembly_locallyFiniteAt
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W) (z : ℂ) :
    let G := uibhbotCcw_assemblyDrawing W D.rotation D.boundary
        D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
        (uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
          D.pastRightNonnegative D.pastFiniteIncidence)
        (uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
          D.pastRightNonnegative D.pastFiniteIncidence)
        (uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
          D.pastRightNonnegative D.pastFiniteIncidence)
        (uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary)
        (uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary)
        (uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary)
        (uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary);
    {d : WholePlaneDart W | (ball z 1 ∩ (G.arc d).image).Nonempty}.Finite := by
  dsimp only
  exact (uibhbotCcw_assemblyDrawing W D.rotation D.boundary
    D.pastLeftUnbounded D.pastRightNonnegative D.pastFiniteIncidence
    (uibhbotD39PastCanonicalDrawing W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence)
    (uibhbotD39PastCanonicalDrawing_pos W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence)
    (uibhbotD39PastCanonicalDrawing_arcImage W D.pastLeftUnbounded
      D.pastRightNonnegative D.pastFiniteIncidence)
    (uibhbotD39FutureCanonicalDrawing W D.rotation D.boundary)
    (uibhbotD39FutureCanonicalDrawing_pos W D.rotation D.boundary)
    (uibhbotD39FutureCanonicalDrawing_image W D.rotation D.boundary)
    (uibhbotD39FutureCanonicalDrawing_arcImage W D.rotation D.boundary)).locally_finite
      (ball z 1) isBounded_ball





























































end DirectedDistances.PaperProofs.Section5

end
