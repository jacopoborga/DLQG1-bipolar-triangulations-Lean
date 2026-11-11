/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPresentation5

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the first upper-left dart has no
predecessor and starts at the source junction. -/
private theorem boundaryChanneledUpperLeft_first6 {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (i₀ : Fin ℓ) (hi₀ : i₀.val = 0) :
    (∀ j, (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft.next j ≠
      some i₀) ∧
    boundaryDartInitial (boundaryChanneledPlaneMap R G)
      ((boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft.darts i₀) =
        R.B.source := by
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  have hfirst : ∀ j : Fin ℓ, P.upperLeft.next j ≠ some i₀ := by
    intro j hj
    have hj' : (if h : j.val + 1 < ℓ then
        some (⟨j.val + 1, h⟩ : Fin ℓ) else none) = some i₀ := by
      simpa [P, boundaryChanneledPresentationWithJunctions] using hj
    by_cases h : j.val + 1 < ℓ
    · rw [dif_pos h] at hj'
      have hv := congrArg Fin.val (Option.some.inj hj')
      simp only [Fin.val_mk] at hv
      omega
    · rw [dif_neg h] at hj'
      cases hj'
  have hstart : boundaryDartInitial (boundaryChanneledPlaneMap R G)
      (boundaryChanneledLeftDart R G i₀) = R.B.source := by
    have hstep := R.B.leftPath.edge_step
      ⟨0, by rw [R.B.leftPath.darts_length]; have h := R.B.left_length_pos; omega⟩
    calc
      boundaryDartInitial (boundaryChanneledPlaneMap R G)
          (boundaryChanneledLeftDart R G i₀) =
          dartTailVertex R.B.map (boundaryPathDart R.B.leftPath i₀) :=
        boundaryChanneledLeftDart_initial R G i₀
      _ = R.B.leftPath.vertices.get
          ⟨0, by rw [R.B.leftPath.vertices_length]; omega⟩ := by
        simpa [boundaryPathDart, hi₀] using hstep.2.2.1.symm
      _ = R.B.source := R.B.leftPath.start_vertex
  constructor
  · simpa [P, boundaryChanneledPresentationWithJunctions] using hfirst
  · change boundaryDartInitial (boundaryChanneledPlaneMap R G)
      (boundaryChanneledLeftDart R G i₀) = R.B.source
    exact hstart

/-- Helper toward Definition 3.2: the last upper-left dart has no successor
and ends at the sink junction. -/
private theorem boundaryChanneledUpperLeft_last6 {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (iₗ : Fin ℓ) (hiₗ : iₗ.val + 1 = ℓ) :
    (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft.next iₗ = none ∧
    boundaryDartTerminal (boundaryChanneledPlaneMap R G)
      ((boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft.darts iₗ) =
        R.B.sink := by
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  have hnone : P.upperLeft.next iₗ = none := by
    change (if h : iₗ.val + 1 < ℓ then
      some (⟨iₗ.val + 1, h⟩ : Fin ℓ) else none) = none
    simp [hiₗ]
  have hend : boundaryDartTerminal (boundaryChanneledPlaneMap R G)
      (boundaryChanneledLeftDart R G iₗ) = R.B.sink := by
    have hstep := R.B.leftPath.edge_step
      ⟨iₗ.val, by rw [R.B.leftPath.darts_length]; exact iₗ.isLt⟩
    have hidx : (⟨iₗ.val + 1, by rw [R.B.leftPath.vertices_length]; omega⟩ :
        Fin R.B.leftPath.vertices.length) =
        ⟨ℓ, by rw [R.B.leftPath.vertices_length]; omega⟩ := by
      apply Fin.ext
      omega
    have hhead := hstep.2.2.2
    rw [hidx] at hhead
    calc
      boundaryDartTerminal (boundaryChanneledPlaneMap R G)
          (boundaryChanneledLeftDart R G iₗ) =
          dartHeadVertex R.B.map (boundaryPathDart R.B.leftPath iₗ) :=
        boundaryChanneledLeftDart_terminal R G iₗ
      _ = R.B.leftPath.vertices.get
          ⟨ℓ, by rw [R.B.leftPath.vertices_length]; omega⟩ := by
        simpa [boundaryPathDart] using hhead.symm
      _ = R.B.sink := R.B.leftPath.end_vertex
  constructor
  · simpa [P, boundaryChanneledPresentationWithJunctions] using hnone
  · change boundaryDartTerminal (boundaryChanneledPlaneMap R G)
      (boundaryChanneledLeftDart R G iₗ) = R.B.sink
    exact hend

/-- Helper toward Definition 3.2: the upper-left side has exactly its
source and sink path endpoint labels. -/
theorem boundaryChanneledPresentation_upperLeft_endpointLabels6
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) :
    BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft := by
  have hlen : 0 < ℓ := by have h := R.B.left_length_pos; omega
  let i₀ : Fin ℓ := ⟨0, hlen⟩
  let iₗ : Fin ℓ := ⟨ℓ - 1, by omega⟩
  have hi₀ : i₀.val = 0 := rfl
  have hiₗ : iₗ.val + 1 = ℓ := by simp [iₗ]; omega
  have hfirst := boundaryChanneledUpperLeft_first6 R G i₀ hi₀
  have hlast := boundaryChanneledUpperLeft_last6 R G iₗ hiₗ
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  let S := P.upperLeft
  change BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G) S
  unfold BoundarySideEndpointLabels
  refine ⟨?_, ?_⟩
  · intro v hv
    have hv' : (some R.B.source : Option (MapVertex R.B.map)) = some v := by
      simpa [S, P, boundaryChanneledPresentationWithJunctions] using hv
    have hvsource : v = R.B.source := (Option.some.inj hv').symm
    subst v
    constructor
    · intro _
      refine ⟨i₀, ?_, ?_⟩
      · exact hfirst.1
      · simpa [S, P] using hfirst.2
    · intro i hi
      change Fin ℓ at i
      have heq : i = i₀ := by
        apply Fin.ext
        change i.val = 0
        by_contra hne
        have hpos : 0 < i.val := Nat.pos_of_ne_zero hne
        let j : Fin ℓ := ⟨i.val - 1, by omega⟩
        have hjval : j.val + 1 = i.val := by simp [j]; omega
        have hj : S.next j = some i := by
          change (if h : j.val + 1 < ℓ then
            some (⟨j.val + 1, h⟩ : Fin ℓ) else none) = some i
          rw [dif_pos (by omega)]
          congr 1
          apply Fin.ext
          exact hjval
        exact (hi j) hj
      subst i
      simpa [S, P] using hfirst.2
  · constructor
    · intro v hv
      have hv' : (some R.B.sink : Option (MapVertex R.B.map)) = some v := by
        simpa [S, P, boundaryChanneledPresentationWithJunctions] using hv
      have hvsink : v = R.B.sink := (Option.some.inj hv').symm
      subst v
      constructor
      · intro _
        refine ⟨iₗ, ?_, ?_⟩
        · exact hlast.1
        · simpa [S, P] using hlast.2
      · intro i hi
        have hnone : S.next i = none := hi
        have hval : i.val + 1 = ℓ := by
          have hnone' : (if h : i.val + 1 < ℓ then
              some (⟨i.val + 1, h⟩ : Fin ℓ) else none) = none := by
            simpa [S, P, boundaryChanneledPresentationWithJunctions] using hnone
          by_cases h : i.val + 1 < ℓ
          · rw [dif_pos h] at hnone'
            cases hnone'
          · omega
        have heq : i = iₗ := by
          apply Fin.ext
          omega
        subst i
        simpa [S, P] using hlast.2
    · intro hempty v z hv hz
      exact (hempty.false i₀).elim

/-- Helper toward Definition 3.2: a reversed right-path dart starts at the
directed path head. -/
private theorem boundaryChanneledRightDart_initial6 {ℓ r n : ℕ}
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
  change boundaryDartInitial M (e, !M.forward ⟨e, hmissing⟩) = dartHeadVertex R.B.map d
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
      e, hout', htail']
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
      e, hout', hnot]
    change dartTailVertex R.B.map (R.B.map.toCombinatorialMap.edgeInv d) =
      dartHeadVertex R.B.map d
    rfl

/-- Helper toward Definition 3.2: a reversed right-path dart ends at the
directed path tail. -/
private theorem boundaryChanneledRightDart_terminal6 {ℓ r n : ℕ}
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
  change boundaryDartTerminal M (e, !M.forward ⟨e, hmissing⟩) = dartTailVertex R.B.map d
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
      e, hout', htail']
  · have hout' : e.out = R.B.map.toCombinatorialMap.edgeInv d := by
      simpa [e] using hout
    have hnot := (R.B.map.tail_iff d (R.B.noMissingDarts d)).mp htail'
    have hforward : M.forward ⟨e, hmissing⟩ = false := by
      simp [M, boundaryChanneledPlaneMap, e, hout', hnot]
    rw [boundaryDartTerminal_eq]
    simp [M, boundaryChanneledPlaneMap, PLDrawing.toPlaneGraphDrawing,
      e, hout', hnot]
    change dartTailVertex R.B.map
        (R.B.map.toCombinatorialMap.edgeInv
          (R.B.map.toCombinatorialMap.edgeInv d)) = dartTailVertex R.B.map d
    rw [R.B.map.toCombinatorialMap.edgeInv_invol]

/-- Helper toward Definition 3.2: the first lower-right dart has no
predecessor and starts at the sink junction. -/
private theorem boundaryChanneledLowerRight_first6 {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (i₀ : Fin r) (hi₀ : i₀.val = 0) :
    (∀ j, (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight.next j ≠
      some i₀) ∧
    boundaryDartInitial (boundaryChanneledPlaneMap R G)
      ((boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight.darts i₀) =
        R.B.sink := by
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  have hfirst : ∀ j : Fin r, P.lowerRight.next j ≠ some i₀ := by
    intro j hj
    have hj' : (if h : j.val + 1 < r then
        some (⟨j.val + 1, h⟩ : Fin r) else none) = some i₀ := by
      simpa [P, boundaryChanneledPresentationWithJunctions] using hj
    by_cases h : j.val + 1 < r
    · rw [dif_pos h] at hj'
      have hv := congrArg Fin.val (Option.some.inj hj')
      simp at hv
      omega
    · rw [dif_neg h] at hj'
      cases hj'
  have hstart : boundaryDartInitial (boundaryChanneledPlaneMap R G)
      (boundaryChanneledRightDart R G i₀) = R.B.sink := by
    have hlen : 0 < r := by have h := R.B.right_length_pos; omega
    let k : Fin R.B.rightPath.darts.length :=
      ⟨r - 1, by rw [R.B.rightPath.darts_length]; omega⟩
    have hrev : R.B.rightPath.darts.reverse.get
        ⟨i₀.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact i₀.isLt⟩ =
        R.B.rightPath.darts.get k := by
      simp [hi₀, k, R.B.rightPath.darts_length]
    have hstep := R.B.rightPath.edge_step k
    have hkval : k.val + 1 = r := by
      dsimp [k]
      omega
    have hidx : (⟨k.val + 1, by rw [R.B.rightPath.vertices_length]; omega⟩ :
        Fin R.B.rightPath.vertices.length) =
        ⟨r, by rw [R.B.rightPath.vertices_length]; omega⟩ := by
      apply Fin.ext
      exact hkval
    have hhead := hstep.2.2.2
    rw [hidx] at hhead
    calc
      boundaryDartInitial (boundaryChanneledPlaneMap R G)
          (boundaryChanneledRightDart R G i₀) =
          dartHeadVertex R.B.map
            (R.B.rightPath.darts.reverse.get ⟨i₀.val, by
              rw [List.length_reverse, R.B.rightPath.darts_length]
              exact i₀.isLt⟩) := boundaryChanneledRightDart_initial6 R G i₀
      _ = R.B.sink := by
        rw [hrev]
        exact hhead.symm.trans R.B.rightPath.end_vertex
  constructor
  · simpa [P, boundaryChanneledPresentationWithJunctions] using hfirst
  · change boundaryDartInitial (boundaryChanneledPlaneMap R G)
      (boundaryChanneledRightDart R G i₀) = R.B.sink
    exact hstart

/-- Helper toward Definition 3.2: the last lower-right dart has no successor
and ends at the source junction. -/
private theorem boundaryChanneledLowerRight_last6 {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (iₗ : Fin r) (hiₗ : iₗ.val + 1 = r) :
    (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight.next iₗ = none ∧
    boundaryDartTerminal (boundaryChanneledPlaneMap R G)
      ((boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight.darts iₗ) =
        R.B.source := by
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  have hnone : P.lowerRight.next iₗ = none := by
    change (if h : iₗ.val + 1 < r then
      some (⟨iₗ.val + 1, h⟩ : Fin r) else none) = none
    simp [hiₗ]
  have hend : boundaryDartTerminal (boundaryChanneledPlaneMap R G)
      (boundaryChanneledRightDart R G iₗ) = R.B.source := by
    have hlen : 0 < r := by have h := R.B.right_length_pos; omega
    let k : Fin R.B.rightPath.darts.length :=
      ⟨0, by rw [R.B.rightPath.darts_length]; omega⟩
    have hrev : R.B.rightPath.darts.reverse.get
        ⟨iₗ.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact iₗ.isLt⟩ =
        R.B.rightPath.darts.get k := by
      simp [k, hiₗ, R.B.rightPath.darts_length]
    have hstep := R.B.rightPath.edge_step k
    calc
      boundaryDartTerminal (boundaryChanneledPlaneMap R G)
          (boundaryChanneledRightDart R G iₗ) =
          dartTailVertex R.B.map
            (R.B.rightPath.darts.reverse.get ⟨iₗ.val, by
              rw [List.length_reverse, R.B.rightPath.darts_length]
              exact iₗ.isLt⟩) := boundaryChanneledRightDart_terminal6 R G iₗ
      _ = R.B.source := by
        rw [hrev]
        exact hstep.2.2.1.symm.trans R.B.rightPath.start_vertex
  constructor
  · simpa [P, boundaryChanneledPresentationWithJunctions] using hnone
  · change boundaryDartTerminal (boundaryChanneledPlaneMap R G)
      (boundaryChanneledRightDart R G iₗ) = R.B.source
    exact hend

/-- Helper toward Definition 3.2: the lower-right side has exactly its
sink and source traversal endpoint labels. -/
theorem boundaryChanneledPresentation_lowerRight_endpointLabels6
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) :
    BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight := by
  have hlen : 0 < r := by have h := R.B.right_length_pos; omega
  let i₀ : Fin r := ⟨0, hlen⟩
  let iᵣ : Fin r := ⟨r - 1, by omega⟩
  have hi₀ : i₀.val = 0 := rfl
  have hiᵣ : iᵣ.val + 1 = r := by simp [iᵣ]; omega
  have hfirst := boundaryChanneledLowerRight_first6 R G i₀ hi₀
  have hlast := boundaryChanneledLowerRight_last6 R G iᵣ hiᵣ
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  let S := P.lowerRight
  change BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G) S
  unfold BoundarySideEndpointLabels
  refine ⟨?_, ?_⟩
  · intro v hv
    have hv' : (some R.B.sink : Option (MapVertex R.B.map)) = some v := by
      simpa [S, P, boundaryChanneledPresentationWithJunctions] using hv
    have hvsink : v = R.B.sink := (Option.some.inj hv').symm
    subst v
    constructor
    · intro _
      refine ⟨i₀, ?_, ?_⟩
      · exact hfirst.1
      · simpa [S, P] using hfirst.2
    · intro i hi
      change Fin r at i
      have heq : i = i₀ := by
        apply Fin.ext
        change i.val = 0
        by_contra hne
        have hpos : 0 < i.val := Nat.pos_of_ne_zero hne
        let j : Fin r := ⟨i.val - 1, by omega⟩
        have hjval : j.val + 1 = i.val := by simp [j]; omega
        have hj : S.next j = some i := by
          change (if h : j.val + 1 < r then
            some (⟨j.val + 1, h⟩ : Fin r) else none) = some i
          rw [dif_pos (by omega)]
          congr 1
          apply Fin.ext
          exact hjval
        exact (hi j) hj
      subst i
      simpa [S, P] using hfirst.2
  · constructor
    · intro v hv
      have hv' : (some R.B.source : Option (MapVertex R.B.map)) = some v := by
        simpa [S, P, boundaryChanneledPresentationWithJunctions] using hv
      have hvsource : v = R.B.source := (Option.some.inj hv').symm
      subst v
      constructor
      · intro _
        refine ⟨iᵣ, ?_, ?_⟩
        · exact hlast.1
        · simpa [S, P] using hlast.2
      · intro i hi
        change Fin r at i
        have hnone : S.next i = none := hi
        have hval : i.val + 1 = r := by
          have hnone' : (if h : i.val + 1 < r then
              some (⟨i.val + 1, h⟩ : Fin r) else none) = none := by
            simpa [S, P, boundaryChanneledPresentationWithJunctions] using hnone
          by_cases h : i.val + 1 < r
          · rw [dif_pos h] at hnone'
            cases hnone'
          · omega
        have heq : i = iᵣ := by
          apply Fin.ext
          omega
        subst i
        simpa [S, P] using hlast.2
    · intro hempty v z hv hz
      exact (hempty.false i₀).elim

/-- Helper toward Definition 3.2: the two present-side endpoint-label
predicates hold together for the constructed finite presentation. -/
theorem boundaryChanneledPresentation_presentSide_endpointLabels6
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) :
    BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G)
        (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft ∧
      BoundarySideEndpointLabels (boundaryChanneledPlaneMap R G)
        (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight :=
  ⟨boundaryChanneledPresentation_upperLeft_endpointLabels6 R G,
    boundaryChanneledPresentation_lowerRight_endpointLabels6 R G⟩

/-- Helper toward Definition 3.2: when the empty upper-right run is skipped,
the last upper-left dart and first lower-right dart meet at the sink. -/
theorem boundaryChanneledPresentation_upperLeft_lowerRight_join6
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (i : Fin ℓ) (j : Fin r)
    (hi : i.val + 1 = ℓ) (hj : j.val = 0) :
    boundaryDartTerminal (boundaryChanneledPlaneMap R G)
        ((boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft.darts i) =
      boundaryDartInitial (boundaryChanneledPlaneMap R G)
        ((boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight.darts j) := by
  exact (boundaryChanneledUpperLeft_last6 R G i hi).2.trans
    (boundaryChanneledLowerRight_first6 R G j hj).2.symm

/-- Helper toward Definition 3.2: when the empty lower-left run is skipped,
the last lower-right dart and first upper-left dart meet at the source. -/
theorem boundaryChanneledPresentation_lowerRight_upperLeft_join6
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (i : Fin r) (j : Fin ℓ)
    (hi : i.val + 1 = r) (hj : j.val = 0) :
    boundaryDartTerminal (boundaryChanneledPlaneMap R G)
        ((boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight.darts i) =
      boundaryDartInitial (boundaryChanneledPlaneMap R G)
        ((boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft.darts j) := by
  exact (boundaryChanneledLowerRight_last6 R G i hi).2.trans
    (boundaryChanneledUpperLeft_first6 R G j hj).2.symm




























end DirectedDistances.PaperProofs.Section3

end
end
