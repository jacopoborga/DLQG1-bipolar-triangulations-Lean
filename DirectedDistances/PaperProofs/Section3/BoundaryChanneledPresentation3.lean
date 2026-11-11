module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPresentation2

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: a reversed right-path dart has its
directed path head as the lower-right traversal initial vertex. -/
private theorem boundaryChanneledRightDart_initial {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) (i : Fin r) :
    boundaryDartInitial (boundaryChanneledPlaneMap R G)
        (boundaryChanneledRightDart R G i) =
      dartHeadVertex R.B.map
        (R.B.rightPath.darts.reverse.get ⟨i.val, by
          rw [List.length_reverse, R.B.rightPath.darts_length]
          exact i.isLt⟩) := by
  let M := boundaryChanneledPlaneMap R G
  let d := R.B.rightPath.darts.reverse.get
    ⟨i.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact i.isLt⟩
  let e : G.GeometricEdge := Quotient.mk G.edgeSetoid d
  have hmissing : ¬ M.toPlaneMapWithMissing.missing e := by
    simp [M, boundaryChanneledPlaneMap]
  change boundaryDartInitial M (e, !M.forward ⟨e, hmissing⟩) =
    dartHeadVertex R.B.map d
  have hmem : d ∈ R.B.rightPath.darts := List.mem_reverse.mp (List.get_mem _ _)
  have htail : R.B.map.tail d := by
    rcases List.mem_iff_get.mp hmem with ⟨k, hk⟩
    exact hk ▸ (R.B.rightPath.edge_step k).2.1
  have htail' : R.B.map.tail d := by simpa [d] using htail
  rcases G.geometricEdge_out_mk d with hout | hout
  · have hout' : e.out = d := by simpa [e] using hout
    have hforward : M.forward ⟨e, hmissing⟩ = true := by
      simp [M, boundaryChanneledPlaneMap, e, hout', htail']
    rw [boundaryDartInitial_eq]
    simp [M, boundaryChanneledPlaneMap, PLDrawing.toPlaneGraphDrawing,
      e, hout', htail', hforward]
    change dartTailVertex R.B.map (R.B.map.toCombinatorialMap.edgeInv d) =
      dartHeadVertex R.B.map d
    rfl
  · have hout' : e.out = R.B.map.toCombinatorialMap.edgeInv d := by
      simpa [e] using hout
    have hnot := (R.B.map.tail_iff d (R.B.noMissingDarts d)).mp htail'
    have hforward : M.forward ⟨e, hmissing⟩ = false := by
      simp [M, boundaryChanneledPlaneMap, e, hout', hnot]
    rw [boundaryDartInitial_eq]
    simp [M, boundaryChanneledPlaneMap, PLDrawing.toPlaneGraphDrawing,
      e, hout', htail', hnot, hforward,
      R.B.map.toCombinatorialMap.edgeInv_invol]
    change dartTailVertex R.B.map (R.B.map.toCombinatorialMap.edgeInv d) =
      dartHeadVertex R.B.map d
    rfl

/-- Helper toward Definition 3.2: a reversed right-path dart has its
directed path tail as the lower-right traversal terminal vertex. -/
private theorem boundaryChanneledRightDart_terminal {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) (i : Fin r) :
    boundaryDartTerminal (boundaryChanneledPlaneMap R G)
        (boundaryChanneledRightDart R G i) =
      dartTailVertex R.B.map
        (R.B.rightPath.darts.reverse.get ⟨i.val, by
          rw [List.length_reverse, R.B.rightPath.darts_length]
          exact i.isLt⟩) := by
  let M := boundaryChanneledPlaneMap R G
  let d := R.B.rightPath.darts.reverse.get
    ⟨i.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact i.isLt⟩
  let e : G.GeometricEdge := Quotient.mk G.edgeSetoid d
  have hmissing : ¬ M.toPlaneMapWithMissing.missing e := by
    simp [M, boundaryChanneledPlaneMap]
  change boundaryDartTerminal M (e, !M.forward ⟨e, hmissing⟩) =
    dartTailVertex R.B.map d
  have hmem : d ∈ R.B.rightPath.darts := List.mem_reverse.mp (List.get_mem _ _)
  have htail : R.B.map.tail d := by
    rcases List.mem_iff_get.mp hmem with ⟨k, hk⟩
    exact hk ▸ (R.B.rightPath.edge_step k).2.1
  have htail' : R.B.map.tail d := by simpa [d] using htail
  rcases G.geometricEdge_out_mk d with hout | hout
  · have hout' : e.out = d := by simpa [e] using hout
    have hforward : M.forward ⟨e, hmissing⟩ = true := by
      simp [M, boundaryChanneledPlaneMap, e, hout', htail']
    rw [boundaryDartTerminal_eq]
    simp [M, boundaryChanneledPlaneMap, PLDrawing.toPlaneGraphDrawing,
      e, hout', htail', hforward]
  · have hout' : e.out = R.B.map.toCombinatorialMap.edgeInv d := by
      simpa [e] using hout
    have hnot := (R.B.map.tail_iff d (R.B.noMissingDarts d)).mp htail'
    have hforward : M.forward ⟨e, hmissing⟩ = false := by
      simp [M, boundaryChanneledPlaneMap, e, hout', hnot]
    rw [boundaryDartTerminal_eq]
    simp [M, boundaryChanneledPlaneMap, PLDrawing.toPlaneGraphDrawing,
      e, hout', htail', hnot, hforward,
      R.B.map.toCombinatorialMap.edgeInv_invol]

/-- Helper toward Definition 3.2: successive lower-right darts join at their
common vertex in the reversed traversal of the source right path. -/
theorem boundaryChanneledPresentation_lowerRight_join {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (i j : Fin r)
    (hnext : (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight.next i =
      some j) :
    boundaryDartTerminal (boundaryChanneledPlaneMap R G)
        (boundaryChanneledRightDart R G i) =
      boundaryDartInitial (boundaryChanneledPlaneMap R G)
        (boundaryChanneledRightDart R G j) := by
  have hnext' : (if h : i.val + 1 < r then
      some (⟨i.val + 1, h⟩ : Fin r) else none) = some j := by
    simpa [boundaryChanneledPresentationWithJunctions] using hnext
  by_cases hi : i.val + 1 < r
  · rw [dif_pos hi] at hnext'
    have hij : (⟨i.val + 1, hi⟩ : Fin r) = j := Option.some.inj hnext'
    have hval : i.val + 1 = j.val := congrArg Fin.val hij
    let ki : Fin R.B.rightPath.darts.length :=
      ⟨r - 1 - i.val, by rw [R.B.rightPath.darts_length]; omega⟩
    let kj : Fin R.B.rightPath.darts.length :=
      ⟨r - 1 - j.val, by rw [R.B.rightPath.darts_length]; omega⟩
    have hki : ki.val = kj.val + 1 := by
      change r - 1 - i.val = (r - 1 - j.val) + 1
      omega
    have hrev_i : R.B.rightPath.darts.reverse.get
        ⟨i.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact i.isLt⟩ =
        R.B.rightPath.darts.get ki := by
      simp [ki, R.B.rightPath.darts_length]
    have hrev_j : R.B.rightPath.darts.reverse.get
        ⟨j.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact j.isLt⟩ =
        R.B.rightPath.darts.get kj := by
      simp [kj, R.B.rightPath.darts_length]
    have hstep_i := R.B.rightPath.edge_step ki
    have hstep_j := R.B.rightPath.edge_step kj
    have hki_lt : ki.val < r := by
      simpa only [R.B.rightPath.darts_length] using ki.isLt
    have hkj_lt : kj.val < r := by
      simpa only [R.B.rightPath.darts_length] using kj.isLt
    calc
      boundaryDartTerminal (boundaryChanneledPlaneMap R G)
          (boundaryChanneledRightDart R G i) =
          dartTailVertex R.B.map (R.B.rightPath.darts.get ki) := by
        rw [boundaryChanneledRightDart_terminal, hrev_i]
      _ = R.B.rightPath.vertices.get ⟨ki.val,
            by rw [R.B.rightPath.vertices_length]
               exact Nat.lt_succ_of_lt hki_lt⟩ :=
        hstep_i.2.2.1.symm
      _ = R.B.rightPath.vertices.get ⟨kj.val + 1,
            by rw [R.B.rightPath.vertices_length]
               exact Nat.succ_lt_succ hkj_lt⟩ := by
        congr 1
        apply Fin.ext
        exact hki
      _ = dartHeadVertex R.B.map (R.B.rightPath.darts.get kj) := hstep_j.2.2.2
      _ = boundaryDartInitial (boundaryChanneledPlaneMap R G)
          (boundaryChanneledRightDart R G j) := by
        rw [boundaryChanneledRightDart_initial, hrev_j]
  · rw [dif_neg hi] at hnext'
    cases hnext'

/-- Helper toward Definition 3.2: the finite successor on one side advances
exactly one integer index. -/
private theorem boundaryChanneledFiniteNext_position_iff {m : ℕ}
    (i j : Fin m) :
    (∃ h : i.val + 1 < m, (⟨i.val + 1, h⟩ : Fin m) = j) ↔
      (j.val : ℤ) = (i.val : ℤ) + 1 := by
  constructor
  · rintro ⟨_, h⟩
    have hv := congrArg Fin.val h
    exact_mod_cast hv.symm
  · intro h
    have hi : i.val + 1 < m := by omega
    refine ⟨hi, ?_⟩
    apply Fin.ext
    exact_mod_cast h.symm

/-- Helper toward Definition 3.2: the finite two-run presentation has the
integer boundary order obtained by placing UL first and LR immediately after
it. -/
theorem boundaryChanneledPresentation_positionOrder3 {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    BoundaryPositionOrder3
      (boundaryChanneledPresentationWithJunctions R G).presentation := by
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  let pos := boundaryChanneledPresentation_position R G
  refine ⟨pos, ?_⟩
  unfold IsBoundaryPositionOrder3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact boundaryChanneledPresentation_position_injective R G
  · intro i j htag
    cases i <;> cases j <;> rename_i a b
    all_goals try { first
      | (change Empty at a; cases a)
      | (change Empty at b; cases b) }
    all_goals change Fin _ at a b
    all_goals simp only [sideTag] at htag
    all_goals try { norm_num at htag }
    case upperLeft.upperLeft =>
      simp [P, pos, boundaryChanneledPresentation_position,
        boundaryChanneledPresentationWithJunctions, emptyBoundarySide,
        sideNext]
      exact boundaryChanneledFiniteNext_position_iff a b
    case lowerRight.lowerRight =>
      simp [P, pos, boundaryChanneledPresentation_position,
        boundaryChanneledPresentationWithJunctions, emptyBoundarySide,
        sideNext]
      constructor
      · intro h
        have hval := (boundaryChanneledFiniteNext_position_iff a b).1 h
        omega
      · intro h
        have hval : (b.val : ℤ) = (a.val : ℤ) + 1 := by
          omega
        exact (boundaryChanneledFiniteNext_position_iff a b).2 hval
  · intro i j z hiz hzj
    have hzlo : 0 ≤ z := by
      cases i with
      | upperLeft a => simp [pos, boundaryChanneledPresentation_position] at hiz; omega
      | upperRight a => cases a
      | lowerRight a => simp [pos, boundaryChanneledPresentation_position] at hiz; omega
      | lowerLeft a => cases a
    have hzhi : z < ((ℓ + r : ℕ) : ℤ) := by
      cases j with
      | upperLeft a => simp [pos, boundaryChanneledPresentation_position] at hzj; omega
      | upperRight a => cases a
      | lowerRight a => simp [pos, boundaryChanneledPresentation_position] at hzj; omega
      | lowerLeft a => cases a
    by_cases hleft : z < (ℓ : ℤ)
    · refine ⟨.upperLeft ⟨z.toNat, ?_⟩, ?_⟩
      · exact_mod_cast (show (z.toNat : ℤ) < (ℓ : ℤ) by
          rw [Int.toNat_of_nonneg hzlo]
          exact hleft)
      · simp [pos, boundaryChanneledPresentation_position,
          Int.toNat_of_nonneg hzlo]
    · have hbase : 0 ≤ z - (ℓ : ℤ) := by omega
      refine ⟨.lowerRight ⟨(z - (ℓ : ℤ)).toNat, ?_⟩, ?_⟩
      · exact_mod_cast (show ((z - (ℓ : ℤ)).toNat : ℤ) < (r : ℤ) by
          rw [Int.toNat_of_nonneg hbase]
          omega)
      · simp [pos, boundaryChanneledPresentation_position,
          Int.toNat_of_nonneg hbase]
        omega
  · intro i j k hij hjk hends
    cases i <;> cases j <;> cases k <;> rename_i a b c
    all_goals try { first
      | (change Empty at a; cases a)
      | (change Empty at b; cases b)
      | (change Empty at c; cases c) }
    all_goals change Fin _ at a b c
    all_goals simp [pos, boundaryChanneledPresentation_position,
      boundaryChanneledPresentationWithJunctions, emptyBoundarySide,
      sideTag] at * <;> omega
  · intro i j k hij hjk htag₁ htag₂ htag₃
    cases i <;> cases j <;> cases k <;> rename_i a b c
    all_goals try { first
      | (change Empty at a; cases a)
      | (change Empty at b; cases b)
      | (change Empty at c; cases c) }
    all_goals change Fin _ at a b c
    all_goals simp [boundaryChanneledPresentationWithJunctions,
      emptyBoundarySide, sideTag] at htag₁ htag₂ htag₃

































end DirectedDistances.PaperProofs.Section3

end
end
