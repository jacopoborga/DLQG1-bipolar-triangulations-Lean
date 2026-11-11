module

public import DirectedDistances.PlanarMap.PlanarPathCutOneSided
public import DirectedDistances.PlanarMap.PlanarPathCutSeparation

/-! Supporting lemmas for paper labels `def-geodesic`, `lem-lr-ind` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}



theorem pathCut_firstStrictLeft_tail_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {m : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink m) (j : Fin m)
    (hj : Q.darts.get ⟨j.val, by rw [Q.darts_length]; exact j.isLt⟩ ∈
      pathCutLeftDarts B P \ pathCutSeamDarts B P)
    (hfirst : ∀ k : Fin m, k.val < j.val →
      Q.darts.get ⟨k.val, by rw [Q.darts_length]; exact k.isLt⟩ ∉
        pathCutLeftDarts B P \ pathCutSeamDarts B P) :
    dartTailVertex B.map
      (Q.darts.get ⟨j.val, by rw [Q.darts_length]; exact j.isLt⟩) ∈ P.vertices := by
  classical
  have hdarts := Q.darts_length
  have hvertices := Q.vertices_length
  let jq : Fin Q.darts.length := ⟨j.val, by rw [Q.darts_length]; exact j.isLt⟩
  change Q.darts.get jq ∈ pathCutLeftDarts B P \ pathCutSeamDarts B P at hj
  change dartTailVertex B.map (Q.darts.get jq) ∈ P.vertices
  have hjstep := Q.edge_step jq
  by_cases hjzero : j.val = 0
  · have htail : dartTailVertex B.map (Q.darts.get jq) = B.source := by
      calc
        dartTailVertex B.map (Q.darts.get jq) =
            Q.vertices.get ⟨jq.val, by omega⟩ := hjstep.2.2.1.symm
        _ = Q.vertices.get ⟨0, by omega⟩ := by
          congr 1
          exact Fin.ext hjzero
        _ = B.source := Q.start_vertex
    have hsource : B.source ∈ P.vertices := by
      simpa only [P.start_vertex] using
        List.get_mem P.vertices ⟨0, by rw [P.vertices_length]; omega⟩
    exact htail.symm ▸ hsource
  · by_contra hw
    let k : Fin m := ⟨j.val - 1, by omega⟩
    let kq : Fin Q.darts.length := ⟨k.val, by rw [Q.darts_length]; exact k.isLt⟩
    have hklt : k.val < j.val := by dsimp [k]; omega
    have hkstep := Q.edge_step kq
    have htouch : dartTailVertex B.map
        (B.map.toCombinatorialMap.edgeInv (Q.darts.get kq)) =
          dartTailVertex B.map (Q.darts.get jq) := by
      calc
        dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv (Q.darts.get kq)) =
            dartHeadVertex B.map (Q.darts.get kq) := rfl
        _ = Q.vertices.get ⟨kq.val + 1, by omega⟩ := hkstep.2.2.2.symm
        _ = Q.vertices.get ⟨jq.val, by omega⟩ := by
          congr 1
          apply Fin.ext
          dsimp [kq, k, jq]
          omega
        _ = dartTailVertex B.map (Q.darts.get jq) := hjstep.2.2.1
    have hinvLeft : B.map.toCombinatorialMap.edgeInv (Q.darts.get kq) ∈
        pathCutLeftDarts B P := by
      rcases pathCut_vertex_darts_one_sided B P hw with hleft | hright
      · exact hleft _ htouch
      · exact (Set.disjoint_left.mp (pathCut_offSeam_disjoint B P) hj
          ⟨hright _ rfl, hj.2⟩).elim
    have hinvNotSeam : B.map.toCombinatorialMap.edgeInv (Q.darts.get kq) ∉
        pathCutSeamDarts B P := by
      intro hseam
      have hvertex := pathCutSeamDarts_tailVertex_mem B P hseam
      exact hw (htouch ▸ hvertex)
    have hkNotSeam : Q.darts.get kq ∉ pathCutSeamDarts B P := by
      intro hseam
      exact hinvNotSeam ((pathCutSeamDarts_edgeInv_iff B P _).2 hseam)
    have hkLeft : Q.darts.get kq ∈ pathCutLeftDarts B P := by
      have h := pathCutLeft_edgeInv_mem B P hinvLeft hinvNotSeam
      simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h
    exact hfirst k hklt ⟨hkLeft, hkNotSeam⟩



theorem pathCut_firstStrictLeft_tail_mem_all
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink m) (j : Fin m),
      Q.darts.get ⟨j.val, by rw [Q.darts_length]; exact j.isLt⟩ ∈
          pathCutLeftDarts B P \ pathCutSeamDarts B P →
      (∀ k : Fin m, k.val < j.val →
        Q.darts.get ⟨k.val, by rw [Q.darts_length]; exact k.isLt⟩ ∉
          pathCutLeftDarts B P \ pathCutSeamDarts B P) →
      dartTailVertex B.map
        (Q.darts.get ⟨j.val, by rw [Q.darts_length]; exact j.isLt⟩) ∈ P.vertices := by
  intro m Q j hj hfirst
  exact pathCut_firstStrictLeft_tail_mem B P Q j hj hfirst

end DirectedDistances.PlanarMap
