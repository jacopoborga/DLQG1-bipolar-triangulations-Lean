module

public import DirectedDistances.PlanarMap.PlanarPathCutLeftHalfBase
public import DirectedDistances.PlanarMap.PlanarPathCutLeftmostBridge
public import DirectedDistances.PlanarMap.LRIndClassEquiv
public import DirectedDistances.PlanarMap.FiniteXDPLeftmostLocal

/-! Supporting lemmas for paper labels `def-geodesic`, `lem-lr-ind` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r s n m : ℕ}



@[expose] def SimpleDirectedDartPath.castLength
    {M : DirectedMapWithMissing D} {u v : MapVertex M}
    (h : n = m) (P : SimpleDirectedDartPath M u v n) :
    SimpleDirectedDartPath M u v m where
  darts := P.darts
  vertices := P.vertices
  darts_length := P.darts_length.trans h
  vertices_length := P.vertices_length.trans (congrArg (· + 1) h)
  vertices_nodup := P.vertices_nodup
  start_vertex := P.start_vertex
  end_vertex := by subst m; exact P.end_vertex
  edge_step := P.edge_step

 
@[simp] theorem SimpleDirectedDartPath.castLength_darts
    {M : DirectedMapWithMissing D} {u v : MapVertex M}
    (h : n = m) (P : SimpleDirectedDartPath M u v n) :
    (P.castLength h).darts = P.darts := rfl



@[expose] noncomputable def selectedGeodesic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    SimpleDirectedDartPath B.map B.source B.sink (xdpLengthBase B x) :=
  Classical.choose (existsUnique_lexLeftmostXDPGeodesic B x)

 
theorem selectedGeodesic_isLexLeftmost
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    IsLexLeftmostXDPGeodesic B x (selectedGeodesic B x) :=
  (Classical.choose_spec (existsUnique_lexLeftmostXDPGeodesic B x)).1



theorem selectedGeodesic_isGeometricLeftmost
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    IsGeometricLeftmostXDPGeodesic B x (selectedGeodesic B x) :=
  (isLexLeftmost_iff_geometricLeftmost B x (selectedGeodesic B x)).mp
    (selectedGeodesic_isLexLeftmost B x)



@[expose] noncomputable def selectedGeodesicOfLen
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (hR : xdpLengthBase B x = s) :
    SimpleDirectedDartPath B.map B.source B.sink s :=
  (selectedGeodesic B x).castLength hR

 
@[simp] theorem selectedGeodesicOfLen_darts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (hR : xdpLengthBase B x = s) :
    (selectedGeodesicOfLen B x hR).darts = (selectedGeodesic B x).darts :=
  SimpleDirectedDartPath.castLength_darts hR (selectedGeodesic B x)

 
theorem selectedGeodesicOfLen_isLexLeftmost
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (hR : xdpLengthBase B x = s) :
    IsLexLeftmostXDPGeodesic B x (selectedGeodesicOfLen B x hR) := by
  subst s
  exact selectedGeodesic_isLexLeftmost B x

open Classical in


@[expose] noncomputable def cutLRep {x : XDP} {ℓ s r n : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = s) :
    Σ a : ℕ, KMSWMapRep ℓ s a :=
  ⟨_, KMSWMapRep.ofBase
    (pathCutLeftHalfBase R.B (selectedGeodesicOfLen R.B x hR)) rfl⟩

open Classical in


theorem cutLRep_fst {x : XDP} {ℓ s r n : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = s) :
    (cutLRep R hR).1 =
      (pathCutLeftHalfMap R.B (selectedGeodesicOfLen R.B x hR)).numEdges :=
  pathCutLeftHalfBase_numEdges R.B (selectedGeodesicOfLen R.B x hR)

private noncomputable def lrCutTransportPath
    {D' : Type*} [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    SimpleDirectedDartPath B'.map B'.source B'.sink n where
  darts := P.darts.map I.toEquiv
  vertices := P.vertices.map I.vertexEquiv
  darts_length := by simp [P.darts_length]
  vertices_length := by simp [P.vertices_length]
  vertices_nodup := P.vertices_nodup.map I.vertexEquiv.injective
  start_vertex := by
    simpa using (congrArg I.vertexEquiv P.start_vertex).trans I.vertexEquiv_source
  end_vertex := by
    simpa using (congrArg I.vertexEquiv P.end_vertex).trans I.vertexEquiv_sink
  edge_step := by
    intro i
    have hiMap := i.isLt
    simp only [List.length_map] at hiMap
    have hi : i.val < n := by simpa [P.darts_length] using hiMap
    let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hi⟩
    let jv : Fin P.vertices.length := ⟨i.val, by
      rw [P.vertices_length]
      omega⟩
    let jv' : Fin P.vertices.length := ⟨i.val + 1, by
      rw [P.vertices_length]
      omega⟩
    have h := P.edge_step j
    have hget : (P.darts.map I.toEquiv).get i = I.toEquiv (P.darts.get j) := by
      simp [j]
    have hgetV : (P.vertices.map I.vertexEquiv).get
        ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          I.vertexEquiv (P.vertices.get jv) := by simp [jv]
    have hgetV' : (P.vertices.map I.vertexEquiv).get
        ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          I.vertexEquiv (P.vertices.get jv') := by simp [jv']
    rw [hget]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hm
      exact h.1 ((I.missing_iff _).mp hm)
    · exact (I.tail_iff _).2 h.2.1
    · calc
        (P.vertices.map I.vertexEquiv).get
            ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            I.vertexEquiv (P.vertices.get jv) := hgetV
        _ = I.vertexEquiv (dartTailVertex B.map (P.darts.get j)) :=
            congrArg I.vertexEquiv h.2.2.1
        _ = dartTailVertex B'.map (I.toEquiv (P.darts.get j)) :=
            I.vertexEquiv_dartTailVertex _
    · calc
        (P.vertices.map I.vertexEquiv).get
            ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            I.vertexEquiv (P.vertices.get jv') := hgetV'
        _ = I.vertexEquiv (dartHeadVertex B.map (P.darts.get j)) :=
            congrArg I.vertexEquiv h.2.2.2
        _ = dartHeadVertex B'.map (I.toEquiv (P.darts.get j)) :=
            I.vertexEquiv_dartHeadVertex _


private theorem lrCutTransportPath_darts
    {D' : Type*} [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') {n : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    (lrCutTransportPath I P).darts = P.darts.map I.toEquiv := rfl

private theorem lrCut_geodesic_iff_length
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {k : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink k) :
    IsXDPGeodesicBase B x P ↔ k = xdpLengthBase B x := by
  cases x with
  | ldp => exact isLDPGeodesicBase_iff_length_eq B P
  | sdp => exact isSDPGeodesicBase_iff_length_eq B P

private theorem lrCut_length_eq_of_iso
    {D' : Type*} [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (x : XDP) :
    xdpLengthBase B' x = xdpLengthBase B x := by
  cases x with
  | ldp => exact ldpLengthBase_eq_of_baseIso I
  | sdp => exact sdpLengthBase_eq_of_baseIso I

private theorem lrCut_unique_rightPath_of_iso
    {D' : Type*} [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (x : XDP)
    (h : IsUniqueXDPGeodesicBase B x B.rightPath) :
    IsUniqueXDPGeodesicBase B' x B'.rightPath := by
  have hlen := lrCut_length_eq_of_iso I x
  refine ⟨(lrCut_geodesic_iff_length B' x B'.rightPath).mpr
    (((lrCut_geodesic_iff_length B x B.rightPath).mp h.1).trans hlen.symm), ?_⟩
  intro k Q hQ
  let Q₀ := lrCutTransportPath I.symm Q
  have hQ₀ : IsXDPGeodesicBase B x Q₀ :=
    (lrCut_geodesic_iff_length B x Q₀).mpr
      (((lrCut_geodesic_iff_length B' x Q).mp hQ).trans hlen)
  have heq : Q₀.darts = B.rightPath.darts := h.2 Q₀ hQ₀
  have hmap : Q₀.darts.map I.toEquiv = Q.darts := by
    rw [lrCutTransportPath_darts]
    simp only [BipolarBoundaryBaseIso.symm, List.map_map,
      Equiv.apply_symm_apply, Function.comp_def, List.map_id']
  calc
    Q.darts = Q₀.darts.map I.toEquiv := hmap.symm
    _ = B.rightPath.darts.map I.toEquiv := congrArg (List.map I.toEquiv) heq
    _ = B'.rightPath.darts := I.rightDarts

private theorem lrCut_isMLRepresentative_ofBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (hB : B.map.toCombinatorialMap.numEdges = n) (x : XDP)
    (h : IsUniqueXDPGeodesicBase B x B.rightPath) :
    IsMLRepresentative x (KMSWMapRep.ofBase B hB) := by
  exact lrCut_unique_rightPath_of_iso (B.transportIso (Fintype.equivFin D)) x h



theorem cutLRep_ML {x : XDP} {ℓ s r n : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = s) :
    IsMLRepresentative x (cutLRep R hR).2 := by
  classical
  exact lrCut_isMLRepresentative_ofBase
    (pathCutLeftHalfBase R.B (selectedGeodesicOfLen R.B x hR)) rfl x
    (pathCutLeftHalfBase_rightPath_isUniqueXDPGeodesic R.B
      (selectedGeodesicOfLen R.B x hR) x
      (selectedGeodesicOfLen_isLexLeftmost R.B x hR))

end DirectedDistances.PlanarMap
