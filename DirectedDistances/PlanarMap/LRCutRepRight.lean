module

public import DirectedDistances.PlanarMap.PlanarPathCutRightHalfBase
public import DirectedDistances.PlanarMap.LRCutRep
public import DirectedDistances.PlanarMap.ClosedHalfEdges

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap

open Classical in


@[expose] noncomputable def cutRRep {x : XDP} {ℓ s r n : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = s) :
    Σ b : ℕ, KMSWMapRep s r b :=
  ⟨_, KMSWMapRep.ofBase
    (pathCutRightHalfBase R.B (selectedGeodesicOfLen R.B x hR)) rfl⟩

open Classical in


theorem cutRRep_fst {x : XDP} {ℓ s r n : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = s) :
    (cutRRep R hR).1 =
      (pathCutRightHalfMap R.B (selectedGeodesicOfLen R.B x hR)).numEdges :=
  pathCutRightHalfBase_numEdges R.B (selectedGeodesicOfLen R.B x hR)

private theorem lrCutRight_geodesic_leftPath_of_iso
    {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (x : XDP)
    (h : IsXDPGeodesicBase B x B.leftPath) :
    IsXDPGeodesicBase B' x B'.leftPath := by
  cases x with
  | ldp =>
    apply (isLDPGeodesicBase_iff_length_eq B' B'.leftPath).mpr
    rw [ldpLengthBase_eq_of_baseIso I]
    exact (isLDPGeodesicBase_iff_length_eq B B.leftPath).mp h
  | sdp =>
    apply (isSDPGeodesicBase_iff_length_eq B' B'.leftPath).mpr
    rw [sdpLengthBase_eq_of_baseIso I]
    exact (isSDPGeodesicBase_iff_length_eq B B.leftPath).mp h

private theorem lrCutRight_isMRRepresentative_ofBase
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (hB : B.map.toCombinatorialMap.numEdges = n) (x : XDP)
    (h : IsXDPGeodesicBase B x B.leftPath) :
    IsMRRepresentative x (KMSWMapRep.ofBase B hB) := by
  exact lrCutRight_geodesic_leftPath_of_iso (B.transportIso (Fintype.equivFin D)) x h



theorem cutRRep_MR {x : XDP} {ℓ s r n : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = s) :
    IsMRRepresentative x (cutRRep R hR).2 := by
  classical
  exact lrCutRight_isMRRepresentative_ofBase
    (pathCutRightHalfBase R.B (selectedGeodesicOfLen R.B x hR)) rfl x
    (pathCutRightHalfBase_leftPath_isXDPGeodesic R.B
      (selectedGeodesicOfLen R.B x hR) x
      (selectedGeodesicOfLen_isLexLeftmost R.B x hR).1)



theorem cutRep_edges {x : XDP} {ℓ s r n : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = s) :
    (cutLRep R hR).1 + (cutRRep R hR).1 = n + s := by
  classical
  rw [cutLRep_fst, cutRRep_fst]
  exact (pathCutHalfMaps_numEdges_sum_classical R.B
    (selectedGeodesicOfLen R.B x hR)).trans (congrArg (· + s) R.edges)

end DirectedDistances.PlanarMap
