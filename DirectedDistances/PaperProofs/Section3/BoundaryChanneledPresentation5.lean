/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPresentation4

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: the upper-left side has distinct vertex
occurrences because its dart-initial vertices and final vertex are indexed by
the self-avoiding source path's vertex list. -/
private theorem boundaryChanneledUpperLeftVertex_injective {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    Function.Injective (boundarySideVertex (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft) := by
  let B := (boundaryChanneledPresentationWithJunctions R G).presentation
  have hvertices : R.B.leftPath.vertices.length = ℓ + 1 := by
    rw [R.B.leftPath.vertices_length]
  let vindex : (B.upperLeft.Index ⊕
      {i : B.upperLeft.Index // B.upperLeft.next i = none}) →
      Fin R.B.leftPath.vertices.length := fun x =>
    match x with
    | .inl i => ⟨i.val, by
        rw [hvertices]
        omega⟩
    | .inr i => ⟨i.val.val + 1, by
        rw [hvertices]
        omega⟩
  have hlast : ∀ i : B.upperLeft.Index,
      B.upperLeft.next i = none → i.val + 1 = ℓ := by
    intro i hi
    change Fin ℓ at i
    change (if h : i.val + 1 < ℓ then
      some (⟨i.val + 1, h⟩ : Fin ℓ) else none) = none at hi
    by_cases h : i.val + 1 < ℓ
    · simp [h] at hi
    · omega
  have hrep (x : B.upperLeft.Index ⊕
      {i : B.upperLeft.Index // B.upperLeft.next i = none}) :
      boundarySideVertex (boundaryChanneledPlaneMap R G) B.upperLeft x =
        R.B.leftPath.vertices.get (vindex x) := by
    cases x with
    | inl i =>
      change Fin ℓ at i
      change boundaryDartInitial (boundaryChanneledPlaneMap R G)
          (boundaryChanneledLeftDart R G i) =
        R.B.leftPath.vertices.get ⟨i.val, by
          rw [hvertices]
          omega⟩
      rw [boundaryChanneledLeftDart_initial]
      exact (R.B.leftPath.edge_step
        ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.isLt⟩).2.2.1.symm
    | inr i =>
      cases i with
      | mk i hi =>
        change Fin ℓ at i
        change boundaryDartTerminal (boundaryChanneledPlaneMap R G)
            (boundaryChanneledLeftDart R G i) =
          R.B.leftPath.vertices.get ⟨i.val + 1, by
            rw [hvertices]
            omega⟩
        rw [boundaryChanneledLeftDart_terminal]
        exact (R.B.leftPath.edge_step
          ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.isLt⟩).2.2.2.symm
  have hindex : Function.Injective vindex := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        change Fin ℓ at i
        change Fin ℓ at j
        have hval : i.val = j.val := by
          have h := congrArg Fin.val hab
          simpa [vindex] using h
        exact congrArg Sum.inl (Fin.ext hval)
      | inr j =>
        change Fin ℓ at i
        let j' : Fin ℓ := j.val
        have hval : i.val = j'.val + 1 := by
          have h := congrArg Fin.val hab
          simpa [vindex, j'] using h
        have hj := hlast j.val j.property
        omega
    | inr i =>
      cases b with
      | inl j =>
        change Fin ℓ at j
        let i' : Fin ℓ := i.val
        have hval : i'.val + 1 = j.val := by
          have h := congrArg Fin.val hab
          simpa [vindex, i'] using h
        have hi := hlast i.val i.property
        omega
      | inr j =>
        let i' : Fin ℓ := i.val
        let j' : Fin ℓ := j.val
        have hval : i'.val + 1 = j'.val + 1 := by
          have h := congrArg Fin.val hab
          simpa [vindex, i', j'] using h
        have hij : i'.val = j'.val := by omega
        exact congrArg Sum.inr (Subtype.ext (Fin.ext hij))
  intro a b hab
  have hget : R.B.leftPath.vertices.get (vindex a) =
      R.B.leftPath.vertices.get (vindex b) := by
    calc
      R.B.leftPath.vertices.get (vindex a) =
        boundarySideVertex (boundaryChanneledPlaneMap R G) B.upperLeft a :=
        (hrep a).symm
      _ = boundarySideVertex (boundaryChanneledPlaneMap R G) B.upperLeft b := hab
      _ = R.B.leftPath.vertices.get (vindex b) := hrep b
  exact hindex (R.B.leftPath.vertices_nodup.get_inj_iff.mp hget)

/-- Helper toward Definition 3.2: the upper-left side is simple. Its vertex
occurrences are injective by the preceding path-index argument, and its finite
successor is acyclic. -/
theorem boundaryChanneledPresentation_upperLeft_simple {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    IsSimpleBoundarySide (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation.upperLeft := by
  constructor
  · exact boundaryChanneledUpperLeftVertex_injective R G
  · exact (boundaryChanneledPresentation_sides_acyclic R G).1

/-- Helper toward Definition 3.2: a reversed right-path dart's traversal
initial vertex is the directed path head. -/
private theorem boundaryChanneledRightDart_initial5 {ℓ r n : ℕ}
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

/-- Helper toward Definition 3.2: a reversed right-path dart's traversal
terminal vertex is the directed path tail. -/
private theorem boundaryChanneledRightDart_terminal5 {ℓ r n : ℕ}
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

/-- Helper toward Definition 3.2: lower-right vertex occurrences are indexed
by the source right path's vertices in reverse traversal order. -/
private theorem boundaryChanneledLowerRightVertex_injective {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    Function.Injective (boundarySideVertex (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight) := by
  let B := (boundaryChanneledPresentationWithJunctions R G).presentation
  have hvertices : R.B.rightPath.vertices.length = r + 1 := by
    rw [R.B.rightPath.vertices_length]
  let vindex : (B.lowerRight.Index ⊕
      {i : B.lowerRight.Index // B.lowerRight.next i = none}) →
      Fin R.B.rightPath.vertices.length := fun x =>
    match x with
    | .inl i => ⟨r - i.val, by rw [hvertices]; omega⟩
    | .inr i => ⟨r - 1 - i.val.val, by rw [hvertices]; omega⟩
  have hlast : ∀ i : B.lowerRight.Index,
      B.lowerRight.next i = none → i.val + 1 = r := by
    intro i hi
    change Fin r at i
    change (if h : i.val + 1 < r then
      some (⟨i.val + 1, h⟩ : Fin r) else none) = none at hi
    by_cases h : i.val + 1 < r
    · simp [h] at hi
    · omega
  have hrep (x : B.lowerRight.Index ⊕
      {i : B.lowerRight.Index // B.lowerRight.next i = none}) :
      boundarySideVertex (boundaryChanneledPlaneMap R G) B.lowerRight x =
        R.B.rightPath.vertices.get (vindex x) := by
    cases x with
    | inl i =>
      change Fin r at i
      let k : Fin R.B.rightPath.darts.length := ⟨r - 1 - i.val, by
        rw [R.B.rightPath.darts_length]
        omega⟩
      have hrev : R.B.rightPath.darts.reverse.get
          ⟨i.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact i.isLt⟩ =
          R.B.rightPath.darts.get k := by
        simp [k, R.B.rightPath.darts_length]
      change boundaryDartInitial (boundaryChanneledPlaneMap R G)
          (boundaryChanneledRightDart R G i) =
        R.B.rightPath.vertices.get ⟨r - i.val, by rw [hvertices]; omega⟩
      rw [boundaryChanneledRightDart_initial5, hrev]
      have hstep := R.B.rightPath.edge_step k
      calc
        dartHeadVertex R.B.map (R.B.rightPath.darts.get k) =
              R.B.rightPath.vertices.get ⟨k.val + 1, by
                rw [hvertices]
                have hklt : k.val < r := by
                  simpa only [R.B.rightPath.darts_length] using k.isLt
                exact Nat.succ_lt_succ hklt⟩ :=
          hstep.2.2.2.symm
        _ = R.B.rightPath.vertices.get ⟨r - i.val, by rw [hvertices]; omega⟩ := by
          congr 1
          apply Fin.ext
          dsimp [k]
          omega
    | inr i =>
      cases i with
      | mk i hi =>
        change Fin r at i
        let k : Fin R.B.rightPath.darts.length := ⟨r - 1 - i.val, by
          rw [R.B.rightPath.darts_length]
          omega⟩
        have hrev : R.B.rightPath.darts.reverse.get
            ⟨i.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact i.isLt⟩ =
            R.B.rightPath.darts.get k := by
          simp [k, R.B.rightPath.darts_length]
        have hlasti := hlast i hi
        have hk : k.val = 0 := by
          dsimp [k]
          omega
        change boundaryDartTerminal (boundaryChanneledPlaneMap R G)
            (boundaryChanneledRightDart R G i) =
          R.B.rightPath.vertices.get ⟨r - 1 - i.val, by rw [hvertices]; omega⟩
        rw [boundaryChanneledRightDart_terminal5, hrev]
        have hstep := R.B.rightPath.edge_step k
        calc
          dartTailVertex R.B.map (R.B.rightPath.darts.get k) =
              R.B.rightPath.vertices.get ⟨k.val, by rw [R.B.rightPath.vertices_length]; omega⟩ :=
            hstep.2.2.1.symm
          _ = R.B.rightPath.vertices.get ⟨r - 1 - i.val, by rw [hvertices]; omega⟩ := by
            congr 1
  have hindex : Function.Injective vindex := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        change Fin r at i
        change Fin r at j
        have hsub : r - i.val = r - j.val := by
          have h := congrArg Fin.val hab
          simpa [vindex] using h
        have hval : i.val = j.val := by omega
        exact congrArg Sum.inl (Fin.ext hval)
      | inr j =>
        change Fin r at i
        let j' : Fin r := j.val
        have hval : r - i.val = r - 1 - j'.val := by
          have h := congrArg Fin.val hab
          simpa [vindex, j'] using h
        have hj := hlast j.val j.property
        omega
    | inr i =>
      cases b with
      | inl j =>
        change Fin r at j
        let i' : Fin r := i.val
        have hval : r - 1 - i'.val = r - j.val := by
          have h := congrArg Fin.val hab
          simpa [vindex, i'] using h
        have hi := hlast i.val i.property
        omega
      | inr j =>
        let i' : Fin r := i.val
        let j' : Fin r := j.val
        have hval : r - 1 - i'.val = r - 1 - j'.val := by
          have h := congrArg Fin.val hab
          simpa [vindex, i', j'] using h
        have hij : i'.val = j'.val := by omega
        exact congrArg Sum.inr (Subtype.ext (Fin.ext hij))
  intro a b hab
  have hget : R.B.rightPath.vertices.get (vindex a) =
      R.B.rightPath.vertices.get (vindex b) := by
    calc
      R.B.rightPath.vertices.get (vindex a) =
          boundarySideVertex (boundaryChanneledPlaneMap R G) B.lowerRight a :=
        (hrep a).symm
      _ = boundarySideVertex (boundaryChanneledPlaneMap R G) B.lowerRight b := hab
      _ = R.B.rightPath.vertices.get (vindex b) := hrep b
  exact hindex (R.B.rightPath.vertices_nodup.get_inj_iff.mp hget)

/-- Helper toward Definition 3.2: the lower-right side is simple. Its vertex
occurrences are injective by the reversed path-index argument, and its finite
successor is acyclic. -/
theorem boundaryChanneledPresentation_lowerRight_simple {ℓ r n : ℕ}
    (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    IsSimpleBoundarySide (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight := by
  constructor
  · exact boundaryChanneledLowerRightVertex_injective R G
  · exact (boundaryChanneledPresentation_sides_acyclic R G).2




























end DirectedDistances.PaperProofs.Section3

end
end
