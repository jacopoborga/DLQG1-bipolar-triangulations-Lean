module

public import DirectedDistances.PlanarMap.LRCutRepRight
public import DirectedDistances.PlanarMap.LRCutRepIso
public import DirectedDistances.PlanarMap.PlanarPathCutHalfIsoPoles
public import DirectedDistances.PlanarMap.BipolarBoundaryBaseIsoOfRot

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap

variable {D D' : Type*} [Fintype D] [DecidableEq D]
  [Fintype D'] [DecidableEq D']
variable {ℓ r n : ℕ}

 
noncomputable def pathCutRightHalfBaseIso
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')] :
    BipolarBoundaryBaseIso (pathCutRightHalfBase B P)
      (pathCutRightHalfBase B' P') := by
  let e := halfRightCongr I P P' hP'
  refine bipolarBoundaryBaseIsoOfRot _ _ e ?_ ?_ ?_ ?_
  · intro d
    simpa only [pathCutRightHalfBase_map,
      pathCutRightHalfMarkedMap_toHalfMap] using
      (halfRightCongr_rot I P P' hP' d)
  · intro d
    change halfRightCongr I P P' hP'
        ((pathCutRightHalfDirectedMap B P).edgeInv d) =
      (pathCutRightHalfDirectedMap B' P').edgeInv
        (halfRightCongr I P P' hP' d)
    exact halfRightCongr_edgeInv I P P' hP' d
  · intro d
    simpa only [pathCutRightHalfBase_map,
      pathCutRightHalfMarkedMap_tail] using
      (halfRightCongr_tail I P P' hP' d)
  · let i : Fin (cutPathRightHalf B P).darts.length :=
      ⟨0, by
        rw [(cutPathRightHalf B P).darts_length]
        exact Nat.lt_of_lt_of_le Nat.zero_lt_one
          (pathCutRightHalf_path_length_pos B P)⟩
    let d₀ : {d : D // d ∈ pathCutRightHalfDarts B P} :=
      (cutPathRightHalf B P).darts.get i
    have hP : d₀.1 ∈ P.darts := by
      have hget : d₀.1 ∈ (cutPathRightHalf B P).darts.unattach :=
        List.mem_map.mpr ⟨d₀, List.get_mem _ _, rfl⟩
      rw [cutPathRightHalf_darts] at hget
      exact hget
    have hboundary : d₀.1 ∈ pathCutRightHalfBoundaryDarts B P :=
      Or.inr hP
    have hboundary' : I.toEquiv d₀.1 ∈
        pathCutRightHalfBoundaryDarts B' P' :=
      (pathCutRightHalfBoundaryDarts_mem_iff I P P' hP' d₀.1).mp hboundary
    have houterLeft : (pathCutRightHalfBase B P).map.IsOuter d₀ := by
      rw [pathCutRightHalfBase_map, pathCutRightHalfMarked_isOuter_iff]
      exact hboundary
    have houterRight : (pathCutRightHalfBase B' P').map.IsOuter (e d₀) := by
      have hmarked : (pathCutRightHalfMarkedMap B' P').IsOuter
          (halfRightCongr I P P' hP' d₀) :=
        (pathCutRightHalfMarked_isOuter_iff B' P' _).2 hboundary'
      simpa only [pathCutRightHalfBase_map] using hmarked
    exact ⟨d₀, houterLeft, houterRight⟩



theorem cutRRep_iso {x : XDP} {ℓ s r n : ℕ}
    {R R' : KMSWMapRep ℓ r n}
    (hR : xdpLengthBase R.B x = s)
    (hR' : xdpLengthBase R'.B x = s)
    (hRR' : Nonempty (BipolarBoundaryBaseIso R.B R'.B)) :
    Nonempty (BipolarBoundaryBaseIso (cutRRep R hR).2.B
      (cutRRep R' hR').2.B) := by
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
  let B := pathCutRightHalfBase R.B P
  let B' := pathCutRightHalfBase R'.B P'
  let J := pathCutRightHalfBaseIso I P P' hDarts
  let e : {d : Fin R.dartCount // d ∈ pathCutRightHalfDarts R.B P} ≃
      Fin (Fintype.card {d : Fin R.dartCount //
        d ∈ pathCutRightHalfDarts R.B P}) :=
    Fintype.equivFin _
  let e' : {d : Fin R'.dartCount // d ∈ pathCutRightHalfDarts R'.B P'} ≃
      Fin (Fintype.card {d : Fin R'.dartCount //
        d ∈ pathCutRightHalfDarts R'.B P'}) :=
    Fintype.equivFin _
  change Nonempty (BipolarBoundaryBaseIso
    (KMSWMapRep.ofBase B rfl).B (KMSWMapRep.ofBase B' rfl).B)
  exact ⟨(B.transportIso e).symm.trans (J.trans (B'.transportIso e'))⟩



theorem cutRep_iso {x : XDP} {ℓ s r n : ℕ}
    {R R' : KMSWMapRep ℓ r n}
    (hR : xdpLengthBase R.B x = s)
    (hR' : xdpLengthBase R'.B x = s)
    (hRR' : Nonempty (BipolarBoundaryBaseIso R.B R'.B)) :
    Nonempty (BipolarBoundaryBaseIso (cutLRep R hR).2.B
      (cutLRep R' hR').2.B) ∧
    Nonempty (BipolarBoundaryBaseIso (cutRRep R hR).2.B
      (cutRRep R' hR').2.B) := by
  exact ⟨cutLRep_iso hR hR' hRR', cutRRep_iso hR hR' hRR'⟩

end DirectedDistances.PlanarMap
