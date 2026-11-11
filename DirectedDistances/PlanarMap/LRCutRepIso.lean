module

public import DirectedDistances.PlanarMap.LRCutRep
public import DirectedDistances.PlanarMap.PlanarPathCutLeftHalfBaseIso
public import DirectedDistances.PlanarMap.LexLeftmostBaseIso

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap



theorem cutLRep_iso {x : XDP} {ℓ s r n : ℕ}
    {R R' : KMSWMapRep ℓ r n}
    (hR : xdpLengthBase R.B x = s)
    (hR' : xdpLengthBase R'.B x = s)
    (hRR' : Nonempty (BipolarBoundaryBaseIso R.B R'.B)) :
    Nonempty (BipolarBoundaryBaseIso (cutLRep R hR).2.B (cutLRep R' hR').2.B) := by
  classical
  obtain ⟨I⟩ := hRR'
  let P := selectedGeodesicOfLen R.B x hR
  let P' := selectedGeodesicOfLen R'.B x hR'
  have hP : IsLexLeftmostXDPGeodesic R.B x P :=
    selectedGeodesicOfLen_isLexLeftmost R.B x hR
  have hP' : IsLexLeftmostXDPGeodesic R'.B x P' :=
    selectedGeodesicOfLen_isLexLeftmost R'.B x hR'
  have hDarts : P'.darts = P.darts.map I.toEquiv :=
    dartLists_eq_of_isLexLeftmostXDPGeodesic_baseIso I x P P' hP hP'
  let B := pathCutLeftHalfBase R.B P
  let B' := pathCutLeftHalfBase R'.B P'
  obtain ⟨J⟩ := pathCutLeftHalfBaseIso_nonempty I P P' hDarts
  let e : {d : Fin R.dartCount // d ∈ pathCutLeftHalfDarts R.B P} ≃
      Fin (Fintype.card {d : Fin R.dartCount // d ∈ pathCutLeftHalfDarts R.B P}) :=
    Fintype.equivFin _
  let e' : {d : Fin R'.dartCount // d ∈ pathCutLeftHalfDarts R'.B P'} ≃
      Fin (Fintype.card {d : Fin R'.dartCount // d ∈ pathCutLeftHalfDarts R'.B P'}) :=
    Fintype.equivFin _
  change Nonempty (BipolarBoundaryBaseIso
    (KMSWMapRep.ofBase B rfl).B (KMSWMapRep.ofBase B' rfl).B)
  exact ⟨(B.transportIso e).symm.trans (J.trans (B'.transportIso e'))⟩

end DirectedDistances.PlanarMap
