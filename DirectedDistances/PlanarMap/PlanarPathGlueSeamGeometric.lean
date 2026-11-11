module

public import DirectedDistances.PlanarMap.PlanarPathGlueSeamLeftmost
public import DirectedDistances.PlanarMap.PlanarPathGlueCutRight
public import DirectedDistances.PlanarMap.PlanarPathCutLeftmostBridge

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PlanarMap

variable {DL DR : Type*} [Fintype DL] [DecidableEq DL]
  [Fintype DR] [DecidableEq DR] {ℓ s r : ℕ}
variable (BL : BipolarTriangulationWithBoundaryBase DL ℓ s)
  (BR : BipolarTriangulationWithBoundaryBase DR s r)



theorem glueSeamPathBase_eq_glueSeamPath :
    glueSeamPathBase BL BR = glueSeamPath BL BR := rfl

private abbrev vertexAt {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {u v : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M u v n) (i : Fin (n + 1)) :=
  P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩

private theorem seam_vertex (i : Fin (s + 1)) :
    vertexAt (glueSeamPath BL BR) i =
      glueDirectedVertexMap BL BR (.inl (vertexAt BL.rightPath i)) := by
  change (BL.rightPath.vertices.map (fun v => glueDirectedVertexMap BL BR (.inl v))).get _ = _
  exact List.getElem_map _

private theorem directed_vertex_eq (v w : MapVertex BL.map ⊕ MapVertex BR.map) :
    glueDirectedVertexMap BL BR v = glueDirectedVertexMap BL BR w ↔
      glueVertexMap BL BR v = glueVertexMap BL BR w := by
  cases v <;> cases w <;> rename_i v w
  all_goals
    refine Quotient.inductionOn₂ v w ?_
    intro d e
    change (Quotient.mk _ _ = Quotient.mk _ _) ↔ (Quotient.mk _ _ = Quotient.mk _ _)
    rw [Quotient.eq, Quotient.eq]
    change (glueDirectedMap BL BR).toCombinatorialMap.rot.SameCycle _ _ ↔ _
    rw [glueDirectedMap_toCombinatorialMap]
    rfl

private theorem cross (u : MapVertex BL.map) (v : MapVertex BR.map)
    (h : glueDirectedVertexMap BL BR (.inl u) = glueDirectedVertexMap BL BR (.inr v)) :
    ∃ i : Fin (s + 1), u = vertexAt BL.rightPath i ∧ v = vertexAt BR.leftPath i := by
  obtain ⟨i, hi, hj⟩ := (glueVertexMap_cross_iff BL BR u v).mp
    ((directed_vertex_eq BL BR _ _).mp h)
  exact ⟨i, hi.trans (glueLeftSeamVertexDart_vertex BL i),
    hj.trans (glueRightSeamVertexDart_vertex BR i)⟩

private theorem right_head (d : DR) :
    dartHeadVertex (glueDirectedMap BL BR) (glueIdentify BL BR (.inr d)) =
      glueDirectedVertexMap BL BR (.inr (dartHeadVertex BR.map d)) := by
  change dartTailVertex (glueDirectedMap BL BR)
    ((glueDirectedMap BL BR).toCombinatorialMap.edgeInv (glueIdentify BL BR (.inr d))) = _
  rw [glueDirectedMap_toCombinatorialMap, glueCombinatorialMap_edgeInv, glueEdgeInv_identify]
  rfl

private theorem seam_dart_right (i : Fin s) :
    ∃ d : DR, glueIdentify BL BR (.inr d) =
      (glueSeamPathBase BL BR).darts.get
        ⟨i.val, by rw [(glueSeamPathBase BL BR).darts_length]; exact i.isLt⟩ := by
  refine ⟨BR.leftPath.darts.get
    ⟨i.val, by rw [BR.leftPath.darts_length]; exact i.isLt⟩, ?_⟩
  rw [← glueIdentify_seam BL BR i]
  change glueIdentify BL BR (.inl _) =
    (BL.rightPath.darts.map (fun d => glueIdentify BL BR (.inl d))).get _
  exact (List.getElem_map (fun d => glueIdentify BL BR (.inl d))
    (l := BL.rightPath.darts) (i := i.val)).symm

private theorem right_vertex_step (x : XDP)
    (hL : IsUniqueXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath)
    (Q : SimpleDirectedDartPath (glueDirectedMap BL BR)
      (glueDirectedVertexMap BL BR (.inl BL.source))
      (glueDirectedVertexMap BL BR (.inl BL.sink)) s)
    (hQ : IsXDPGeodesicBase (glueBase BL BR) x Q) (i : Fin s)
    (u : MapVertex BR.map)
    (hu : glueDirectedVertexMap BL BR (.inr u) = vertexAt Q ⟨i.val, by omega⟩) :
    ∃ d : DR, glueIdentify BL BR (.inr d) =
      Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩ := by
  let qi : Fin Q.darts.length := ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩
  have hs := Q.edge_step qi
  cases hd : Q.darts.get qi with
  | inr d => exact ⟨d.val, glueIdentify_inr_kept BL BR d⟩
  | inl d =>
    have hc : glueDirectedVertexMap BL BR (.inl (dartTailVertex BL.map d.val)) =
        glueDirectedVertexMap BL BR (.inr u) := by
      calc
        _ = dartTailVertex (glueDirectedMap BL BR) (.inl d) := by
          rw [← glueIdentify_inl_kept BL BR d]; rfl
        _ = vertexAt Q ⟨i.val, by omega⟩ := by
          simpa only [vertexAt, qi, hd] using hs.2.2.1.symm
        _ = _ := hu.symm
    obtain ⟨j, hj, _⟩ := cross BL BR _ _ hc
    have hvj : vertexAt Q ⟨i.val, by omega⟩ =
        vertexAt (glueSeamPath BL BR) j := by
      calc
        _ = dartTailVertex (glueDirectedMap BL BR) (.inl d) := by
          simpa only [vertexAt, qi, hd] using hs.2.2.1
        _ = glueDirectedVertexMap BL BR (.inl (dartTailVertex BL.map d.val)) := by
          rw [← glueIdentify_inl_kept BL BR d]; rfl
        _ = glueDirectedVertexMap BL BR (.inl (vertexAt BL.rightPath j)) := by rw [hj]
        _ = _ := (seam_vertex BL BR j).symm
    have hij := glue_geodesic_seam_visit_index BL BR x hL.1 hR Q hQ
      ⟨i.val, by omega⟩ j hvj
    have hji : j = ⟨i.val, by omega⟩ := Fin.ext hij.symm
    rw [hji] at hvj
    by_cases he : Q.darts.get qi = (glueSeamPathBase BL BR).darts.get
        ⟨i.val, by rw [(glueSeamPathBase BL BR).darts_length]; exact i.isLt⟩
    · obtain ⟨e, he'⟩ := seam_dart_right BL BR i
      exact ⟨e, (he'.trans he.symm).trans hd⟩
    · obtain ⟨e, _, _, _, he'⟩ :=
        glue_geodesic_seam_departure_right BL BR x hL hR Q hQ i hvj he
      exact ⟨e, he'.trans hd⟩

private theorem geodesic_dart_right_image (x : XDP)
    (hL : IsUniqueXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath)
    (Q : SimpleDirectedDartPath (glueDirectedMap BL BR)
      (glueDirectedVertexMap BL BR (.inl BL.source))
      (glueDirectedVertexMap BL BR (.inl BL.sink)) s)
    (hQ : IsXDPGeodesicBase (glueBase BL BR) x Q) :
    ∀ g ∈ Q.darts, ∃ d : DR, glueIdentify BL BR (.inr d) = g := by
  have hvertices : ∀ i (hi : i ≤ s), ∃ u : MapVertex BR.map,
      glueDirectedVertexMap BL BR (.inr u) = vertexAt Q ⟨i, by omega⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨BR.source, ?_⟩
      have hp := glueVertexMap_seam BL BR ⟨0, by omega⟩
      rw [glueLeftSeamVertexDart_vertex, glueRightSeamVertexDart_vertex,
        BL.rightPath.start_vertex, BR.leftPath.start_vertex] at hp
      exact ((directed_vertex_eq BL BR _ _).mpr hp).symm.trans Q.start_vertex.symm
    | succ i ih =>
      intro hi
      obtain ⟨u, hu⟩ := ih (by omega)
      obtain ⟨d, hd⟩ := right_vertex_step BL BR x hL hR Q hQ ⟨i, by omega⟩ u hu
      refine ⟨dartHeadVertex BR.map d, ?_⟩
      rw [← right_head BL BR, hd]
      exact (Q.edge_step ⟨i, by rw [Q.darts_length]; omega⟩).2.2.2.symm
  intro g hg
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
  have his : i.val < s := by simpa only [Q.darts_length] using i.isLt
  obtain ⟨u, hu⟩ := hvertices i.val (by omega)
  obtain ⟨d, hd⟩ := right_vertex_step BL BR x hL hR Q hQ ⟨i.val, his⟩ u hu
  exact ⟨d, hd.trans hi⟩




theorem glue_geodesic_dart_right (x : XDP)
    (hL : IsUniqueXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath) {n : ℕ}
    (Q : SimpleDirectedDartPath (glueBase BL BR).map
      (glueBase BL BR).source (glueBase BL BR).sink n)
    (hQ : IsXDPGeodesicBase (glueBase BL BR) x Q) (g : GlueDart BL BR)
    (hg : g ∈ Q.darts) :
    g ∈ pathCutSeamDarts (glueBase BL BR) (glueSeamPathBase BL BR) ∨
      ∃ d : DR, glueIdentify BL BR (.inr d) = g := by
  have hn : n = s := by
    have hlen : n = xdpLengthBase (glueBase BL BR) x := by
      cases x with
      | ldp => exact (isLDPGeodesicBase_iff_length_eq (glueBase BL BR) Q).mp hQ
      | sdp => exact (isSDPGeodesicBase_iff_length_eq (glueBase BL BR) Q).mp hQ
    exact hlen.trans (glue_xdpLength BL BR x hL hR)
  subst n
  exact Or.inr (geodesic_dart_right_image BL BR x hL hR Q hQ g hg)



theorem glueSeamPathBase_isGeometricLeftmost (x : XDP)
    (hL : IsUniqueXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath) :
    IsGeometricLeftmostXDPGeodesic (glueBase BL BR) x (glueSeamPathBase BL BR) := by
  apply (isGeometricLeftmost_iff_geodesics_in_rightHalf
    (glueBase BL BR) x (glueSeamPathBase BL BR)).mpr
  refine ⟨glueSeamPathBase_isXDPGeodesic BL BR x hL.1 hR, ?_⟩
  intro n Q hQ g hg
  rcases glue_geodesic_dart_right BL BR x hL hR Q hQ g hg with hseam | ⟨d, rfl⟩
  · exact Or.inr hseam
  · exact glueIdentify_inr_mem_rightHalf BL BR d



theorem glueSeamPathBase_isLexLeftmost (x : XDP)
    (hL : IsUniqueXDPGeodesicBase BL x BL.rightPath)
    (hR : IsXDPGeodesicBase BR x BR.leftPath) :
    IsLexLeftmostXDPGeodesic (glueBase BL BR) x (glueSeamPathBase BL BR) :=
  (isLexLeftmost_iff_geometricLeftmost (glueBase BL BR) x
    (glueSeamPathBase BL BR)).mpr (glueSeamPathBase_isGeometricLeftmost BL BR x hL hR)

end DirectedDistances.PlanarMap
