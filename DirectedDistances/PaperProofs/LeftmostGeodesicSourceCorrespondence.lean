/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.SourceResults.LeftmostGeodesicDefinition
public import DirectedDistances.PlanarMap.FiniteBipolarThreePathSourceCorrespondence





public section
namespace DirectedDistances.PaperProofs.SourceResults

open DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}

/-- if every dart of a connector is in the three-path filled region, every one of
its vertices is there too. The initial vertex is the shared endpoint `x`; all
later vertices are heads of preceding darts. This includes the empty path. -/
private theorem simplePath_vertices_mem_threePathFilledVertices_of_darts
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map}
    {n m : ℕ} (P : SimpleDirectedDartPath B.map x y n)
    (Q : SimpleDirectedDartPath B.map x y m)
    (hdarts : ∀ d ∈ Q.darts, d ∈ B.threePathFilledDarts P) :
    ∀ v ∈ Q.vertices, v ∈ B.threePathFilledVertices P := by
  intro v hv
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  by_cases hz : i.val = 0
  · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hz
    have hvx : v = x := by
      rw [hi0] at hi
      exact hi.symm.trans Q.start_vertex
    rw [hvx]
    exact (B.mem_threePathFilledVertices_iff_incident P x).mpr (.inl rfl)
  · have hj : i.val - 1 < Q.darts.length := by
      have hiLt : i.val < m + 1 := by
        simpa only [Q.vertices_length] using i.isLt
      rw [Q.darts_length]
      omega
    let j : Fin Q.darts.length := ⟨i.val - 1, hj⟩
    let d := Q.darts.get j
    have hd : d ∈ Q.darts := List.get_mem _ _
    have hhead : dartHeadVertex B.map d = v := by
      have hjLt : j.val < m := by simpa only [Q.darts_length] using j.isLt
      have hi' : (⟨j.val + 1, by rw [Q.vertices_length]; omega⟩ :
          Fin Q.vertices.length) = i := Fin.ext (by
        dsimp [j]
        omega)
      calc
        dartHeadVertex B.map d = Q.vertices.get ⟨j.val + 1, by
            rw [Q.vertices_length]
            omega⟩ := (Q.edge_step j).2.2.2.symm
        _ = Q.vertices.get i := congrArg Q.vertices.get hi'
        _ = v := hi
    exact hhead ▸ B.dartHead_mem_threePathFilledVertices P (hdarts d hd)

/-- the provider's region-based leftmost-geodesic predicate is equivalent to
being an XDP geodesic whose every competing XDP geodesic departs weakly to its
right in the map's orientation. -/
theorem IsLeftmostXDPGeodesic_iff_weaklyRight
    (B : BipolarMapWithBoundaryBase D ℓ r) (choice : XDP)
    {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) :
    IsLeftmostXDPGeodesic B choice P ↔
      GeneralEndpointGeodesic.IsXDPGeodesic B.map B.acyclic choice
        (mapPathOfSimplePath P) ∧
      ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map x y m),
        GeneralEndpointGeodesic.IsXDPGeodesic B.map B.acyclic choice
          (mapPathOfSimplePath Q) →
        B.WeaklyRightOf P Q := by
  have hchar := (def_leftmost_geodesic_provider choice).2.1 B P
  constructor
  · intro h
    have hleft := hchar.mp h
    refine ⟨hleft.1, ?_⟩
    intro m Q hQ
    have hdarts : ∀ d ∈ Q.darts, d ∈ B.threePathFilledDarts P := hleft.2 Q hQ
    have hvertices := simplePath_vertices_mem_threePathFilledVertices_of_darts
      B P Q hdarts
    exact (B.connector_subset_threePathFilledSubmap_iff_weaklyRight P Q).mp
      ⟨hdarts, hvertices⟩
  · rintro ⟨hP, hQ⟩
    apply hchar.mpr
    refine ⟨hP, ?_⟩
    intro m Q hQg d hd
    exact ((B.connector_subset_threePathFilledSubmap_iff_weaklyRight P Q).mpr
      (hQ Q hQg)).1 d hd

end DirectedDistances.PaperProofs.SourceResults
