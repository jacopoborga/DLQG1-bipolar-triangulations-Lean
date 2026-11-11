/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BdyReverseAcyclic

/-! Supporting lemmas for paper labels `def-reverse-map`, `lem-bdy-reverse` (see CORRESPONDENCE.md). -/












public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

open BipolarTriangulationWithBoundary

private theorem mem_take_or_drop_iff {α : Type*} (xs : List α) (n : ℕ) (x : α) :
    x ∈ xs ↔ x ∈ xs.take n ∨ x ∈ xs.drop n := by
  constructor
  · intro hx
    have hx' : x ∈ xs.take n ++ xs.drop n := by
      rw [List.take_append_drop]
      exact hx
    exact List.mem_append.mp hx'
  · rintro (hx | hx)
    · exact List.mem_of_mem_take hx
    · exact List.mem_of_mem_drop hx

/-- Construct the reversed boundary carrier using the graph-level source,
sink and acyclicity results (`lem-bdy-reverse`,
inventory. -/
@[expose] noncomputable def RightPrefixBoundaryPathsData.toBoundaryChanneled
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r)
    (P : RightPrefixBoundaryPathsData B k hk hkr)
    (hbc : B.IsBoundaryChanneled) :
    BipolarTriangulationWithBoundary D (ℓ + k) (r - k) :=
  P.toBipolarTriangulationWithBoundary B k hk hkr
    (flipRightPrefix_isAcyclic B k hk hkr hbc)
    (flipRightPrefix_noIncomingAtK B k hk hkr hbc)
    (flipRightPrefix_source_unique B k hk hkr hbc)
    (flipRightPrefix_noOutgoingAtSink B k hk hkr hbc)
    (flipRightPrefix_sink_unique B k hk hkr hbc)

section RightPrefixBoundaryConclusions

variable {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
  (hk : 1 ≤ k) (hkr : k < r)
  (P : RightPrefixBoundaryPathsData B k hk hkr)
  (hbc : B.IsBoundaryChanneled)

/-- The constructed reversal has the right-prefix-flipped map. Helper; not
counted in the paper inventory. -/
@[simp] theorem toBoundaryChanneled_map :
    (P.toBoundaryChanneled B k hk hkr hbc).map = flipRightPrefix B k hk hkr := by
  rfl

/-- The reversal keeps the old sink. Helper; not counted. -/
@[simp] theorem toBoundaryChanneled_sink :
    (P.toBoundaryChanneled B k hk hkr hbc).sink = B.sink := by
  rfl

/-- The reversal preserves the set of outer boundary vertices
counted in the paper inventory. -/
theorem toBoundaryChanneled_boundaryVertices (v : MapVertex B.map) :
    v ∈ (P.toBoundaryChanneled B k hk hkr hbc).boundaryVertices ↔
      v ∈ B.boundaryVertices := by
  let NewB := P.toBoundaryChanneled B k hk hkr hbc
  change (v ∈ P.leftPath.vertices ∨ v ∈ P.rightPath.vertices) ↔
    (v ∈ B.leftPath.vertices ∨ v ∈ B.rightPath.vertices)
  rw [P.leftPath_vertices, P.rightPath_vertices]
  constructor
  · rintro (h | h)
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr (List.mem_of_mem_take (List.mem_reverse.mp h))
      · exact Or.inl (List.mem_of_mem_drop h)
    · exact Or.inr (List.mem_of_mem_drop h)
  · rintro (h | h)
    · rcases (mem_take_or_drop_iff B.leftPath.vertices 1 v).mp h with hhead | htail
      · have hpos : 0 < B.leftPath.vertices.length := by
          rw [B.leftPath.vertices_length]
          omega
        have hzero : B.leftPath.vertices[0] = B.source := by
          simpa [List.get_eq_getElem] using B.leftPath.start_vertex
        have htake : B.leftPath.vertices.take 1 = [B.source] := by
          have ht := List.take_concat_get' B.leftPath.vertices 0 hpos
          simpa [List.take_zero, hzero] using ht.symm
        have hsource : v = B.source := by
          simpa [htake] using hhead
        subst v
        have hRpos : 0 < B.rightPath.vertices.length := by
          rw [B.rightPath.vertices_length]
          omega
        have hRbound : k + 1 ≤ B.rightPath.vertices.length := by
          rw [B.rightPath.vertices_length]
          omega
        have htakepos : 0 < (B.rightPath.vertices.take (k + 1)).length := by
          rw [List.length_take]
          omega
        have hfirst : B.source ∈ B.rightPath.vertices.take (k + 1) := by
          have hmem := List.get_mem (B.rightPath.vertices.take (k + 1))
            ⟨0, htakepos⟩
          have hget : (B.rightPath.vertices.take (k + 1)).get ⟨0, htakepos⟩ =
              B.rightPath.vertices.get ⟨0, hRpos⟩ := by
            simp [List.get_eq_getElem, List.getElem_take]
          rw [hget, B.rightPath.start_vertex] at hmem
          exact hmem
        exact Or.inl (List.mem_append.mpr
          (Or.inl (List.mem_reverse.mpr hfirst)))
      · exact Or.inl (List.mem_append.mpr (Or.inr htail))
    · rcases (mem_take_or_drop_iff B.rightPath.vertices (k + 1) v).mp h
        with hpref | hsuffix
      · exact Or.inl (List.mem_append.mpr
          (Or.inl (List.mem_reverse.mpr hpref)))
      · have hsuffix' : v ∈ (B.rightPath.vertices.drop k).drop 1 := by
          simpa [List.drop_drop] using hsuffix
        exact Or.inr (List.mem_of_mem_drop hsuffix')

/-- The reversal preserves the edge orbits on the outer boundary
counted in the paper inventory. -/
theorem toBoundaryChanneled_boundaryEdge (d : D) :
    (P.toBoundaryChanneled B k hk hkr hbc).boundaryEdge d ↔ B.boundaryEdge d := by
  let NewB := P.toBoundaryChanneled B k hk hkr hbc
  change (∃ e ∈ P.leftPath.darts ++ P.rightPath.darts,
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv d e) ↔
    ∃ e ∈ B.leftPath.darts ++ B.rightPath.darts,
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv d e
  constructor
  · rintro ⟨e, he, hcycle⟩
    rw [P.leftPath_darts, P.rightPath_darts] at he
    rcases List.mem_append.mp he with hleft | hright
    · rcases List.mem_append.mp hleft with hprefix | hleft
      · rcases List.mem_map.mp hprefix with ⟨a, ha, rfl⟩
        have ha := List.mem_reverse.mp ha
        exact ⟨a, List.mem_append_right _ (List.mem_of_mem_take ha),
          Equiv.Perm.sameCycle_apply_right.mp hcycle⟩
      · exact ⟨e, List.mem_append_left _ hleft, hcycle⟩
    · exact ⟨e, List.mem_append_right _ (List.mem_of_mem_drop hright), hcycle⟩
  · rintro ⟨e, he, hcycle⟩
    rcases List.mem_append.mp he with hleft | hright
    · refine ⟨e, ?_, hcycle⟩
      rw [P.leftPath_darts]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hleft)))
    · rcases (mem_take_or_drop_iff B.rightPath.darts k e).mp hright with
        hpref | hsuffix
      · refine ⟨B.map.toCombinatorialMap.edgeInv e, ?_,
          Equiv.Perm.sameCycle_apply_right.mpr hcycle⟩
        rw [P.leftPath_darts]
        apply List.mem_append.mpr
        apply Or.inl
        apply List.mem_append.mpr
        apply Or.inl
        exact List.mem_map.mpr ⟨e, List.mem_reverse.mpr hpref, rfl⟩
      · refine ⟨e, ?_, hcycle⟩
        rw [P.rightPath_darts]
        exact List.mem_append.mpr (Or.inr hsuffix)

/-- Boundary channeling transfers to the constructed reversal using the
preserved boundary sets and the incoming-edge lemma
`P` (the open T3 goal) and `hbc`; this is a restricted helper on the
simple-boundary carrier, not Lemma 3.18, whose unrestricted form fails (simple-boundary restriction, -/
theorem toBoundaryChanneled_isBoundaryChanneled :
    (P.toBoundaryChanneled B k hk hkr hbc).IsBoundaryChanneled := by
  let NewB := P.toBoundaryChanneled B k hk hkr hbc
  intro d hmiss htail hv hvs
  have hmiss' : ¬ (flipRightPrefix B k hk hkr).missing d := by
    simpa only [toBoundaryChanneled_map, flipRightPrefix_missing] using hmiss
  have htail' : (flipRightPrefix B k hk hkr).tail d := by
    simpa only [toBoundaryChanneled_map] using htail
  have hv' : dartHeadVertex (flipRightPrefix B k hk hkr) d ∈ B.boundaryVertices :=
    (toBoundaryChanneled_boundaryVertices B k hk hkr P hbc _).mp hv
  have hvs' : dartHeadVertex (flipRightPrefix B k hk hkr) d ≠ B.sink := by
    change dartHeadVertex (flipRightPrefix B k hk hkr) d ≠ B.sink at hvs
    exact hvs
  apply (toBoundaryChanneled_boundaryEdge B k hk hkr P hbc d).2
  exact flipRightPrefix_incoming_is_boundary B k hk hkr hbc d hmiss' htail' hv' hvs'

/-- The constructed reversal belongs to the boundary-channeled class
`M^bc_{ℓ+k,r-k}` (`lem-bdy-reverse`,
inventory. -/
theorem toBoundaryChanneled_InMbc :
    InMbc (ℓ + k) (r - k) (P.toBoundaryChanneled B k hk hkr hbc) :=
  toBoundaryChanneled_isBoundaryChanneled B k hk hkr P hbc

/-- A boundary-channeled map and right-prefix path data produce an element
of `M^bc_{ℓ+k,r-k}` whose map is the right-prefix flip
`P` (the open T3 goal) and `hbc`; this is a restricted helper on the
simple-boundary carrier, not Lemma 3.18, whose unrestricted form fails (simple-boundary restriction, -/
theorem exists_boundaryChanneled_rightPrefixReversal
    (P : RightPrefixBoundaryPathsData B k hk hkr) (hbc : B.IsBoundaryChanneled) :
    ∃ B' : BipolarTriangulationWithBoundary D (ℓ + k) (r - k),
      B'.map = flipRightPrefix B k hk hkr ∧ InMbc (ℓ + k) (r - k) B' := by
  refine ⟨P.toBoundaryChanneled B k hk hkr hbc, ?_, ?_⟩
  · exact toBoundaryChanneled_map B k hk hkr P hbc
  · exact toBoundaryChanneled_InMbc B k hk hkr P hbc

end RightPrefixBoundaryConclusions
end DirectedDistances.PlanarMap
