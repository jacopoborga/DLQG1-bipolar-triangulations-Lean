module

public import DirectedDistances.PlanarMap.PlanarPathCutLeftHalfBase
public import DirectedDistances.PlanarMap.PlanarPathCutHalfIsoPoles
public import DirectedDistances.PlanarMap.BipolarBoundaryBaseIsoOfRot

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap

variable {D D' : Type*} [Fintype D] [DecidableEq D]
  [Fintype D'] [DecidableEq D']
variable {ℓ r n : ℕ}

 
noncomputable def pathCutLeftHalfBaseIso
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')] :
    BipolarBoundaryBaseIso (pathCutLeftHalfBase B P)
      (pathCutLeftHalfBase B' P') := by
  let e := halfLeftCongr I P P' hP'
  refine bipolarBoundaryBaseIsoOfRot _ _ e ?_ ?_ ?_ ?_
  · intro d
    simpa only [pathCutLeftHalfBase_map,
      pathCutLeftHalfMarkedMap_toHalfMap] using
      (halfLeftCongr_rot I P P' hP' d)
  · intro d
    change halfLeftCongr I P P' hP'
        ((pathCutLeftHalfDirectedMap B P).edgeInv d) =
      (pathCutLeftHalfDirectedMap B' P').edgeInv
        (halfLeftCongr I P P' hP' d)
    exact halfLeftCongr_edgeInv I P P' hP' d
  · intro d
    simpa only [pathCutLeftHalfBase_map, pathCutLeftHalfMarkedMap_tail] using
      (halfLeftCongr_tail I P P' hP' d)
  · let i : Fin (leftPathHalf B P).darts.length :=
      ⟨0, by
        rw [(leftPathHalf B P).darts_length]
        exact Nat.lt_of_lt_of_le Nat.zero_lt_one B.left_length_pos⟩
    let d₀ : {d : D // d ∈ pathCutLeftHalfDarts B P} :=
      (leftPathHalf B P).darts.get i
    have hdleft : d₀.1 ∈ B.leftPath.darts := by
      have hget : d₀.1 ∈ (leftPathHalf B P).darts.unattach :=
        List.mem_map.mpr ⟨d₀, List.get_mem _ _, rfl⟩
      rw [leftPathHalf_darts] at hget
      exact hget
    have houter : B.map.IsOuter d₀.1 :=
      (B.outerSplit.2.2.1 _).mp hdleft |>.2.2
    have hboundary : d₀.1 ∈ pathCutLeftHalfBoundaryDarts B P :=
      Or.inl ⟨pathCutLeftHalf_leftPath_mem B P hdleft, houter⟩
    have hboundary' : I.toEquiv d₀.1 ∈
        pathCutLeftHalfBoundaryDarts B' P' :=
      (pathCutLeftHalfBoundaryDarts_mem_iff I P P' hP' d₀.1).mp hboundary
    have houterLeft : (pathCutLeftHalfBase B P).map.IsOuter d₀ := by
      rw [pathCutLeftHalfBase_map, pathCutLeftHalfMarked_isOuter_iff]
      exact hboundary
    have houterRight : (pathCutLeftHalfBase B' P').map.IsOuter (e d₀) := by
      have hmarked : (pathCutLeftHalfMarkedMap B' P').IsOuter
          (halfLeftCongr I P P' hP' d₀) :=
        (pathCutLeftHalfMarked_isOuter_iff B' P' _).2 hboundary'
      simpa only [pathCutLeftHalfBase_map] using hmarked
    exact ⟨d₀, houterLeft, houterRight⟩



theorem pathCutLeftHalfBaseIso_nonempty
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')] :
    Nonempty (BipolarBoundaryBaseIso (pathCutLeftHalfBase B P)
      (pathCutLeftHalfBase B' P')) :=
  ⟨pathCutLeftHalfBaseIso I P P' hP'⟩

end DirectedDistances.PlanarMap
