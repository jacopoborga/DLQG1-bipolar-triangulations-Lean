/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry19

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: for a dart of the source map, the bit in
the geometric-edge encoding agrees with the directed plane-map orientation. -/
theorem boundaryChanneledDartPairEquiv_forward20
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (d : Fin R.dartCount)
    (htail : R.B.map.tail d) :
    (boundaryChanneledDartPairEquiv19 G d).2 =
      (boundaryChanneledPlaneMap R G).forward
        ⟨(boundaryChanneledDartPairEquiv19 G d).1,
          by simp [boundaryChanneledPlaneMap]⟩ := by
  classical
  let e := boundaryChanneledDartPairEquiv19 G d
  let q := e.1
  have hmissing :
      ¬ (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.missing q := by
    simp [boundaryChanneledPlaneMap]
  rcases G.geometricEdge_out_mk d with hout | hout
  · have hout' : q.out = d := by
      simpa [q, e, boundaryChanneledDartPairEquiv19] using hout
    have hprop : (d = q.out) ↔ R.B.map.tail q.out := by
      rw [hout']
      constructor
      · intro _
        exact htail
      · intro _
        rfl
    simpa [e, q, boundaryChanneledDartPairEquiv19,
      boundaryChanneledPlaneMap] using hprop
  · have hout' : q.out = R.B.map.toCombinatorialMap.edgeInv d := by
      simpa [q, e, boundaryChanneledDartPairEquiv19] using hout
    have hnot := (R.B.map.tail_iff d (R.B.noMissingDarts d)).mp htail
    have hprop : (d = q.out) ↔ R.B.map.tail q.out := by
      rw [hout']
      constructor
      · intro heq
        exact False.elim ((Ne.symm (G.flip_ne d)) heq)
      · intro htailq
        exact (hnot htailq).elim
    simpa [e, q, boundaryChanneledDartPairEquiv19,
      boundaryChanneledPlaneMap] using hprop

/-- Helper toward Definition 3.2: each UL presentation dart is exactly the
encoded source dart at the same left-path index. -/
theorem boundaryChanneledLeftDart_eq_encodedPath20
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (i : Fin ℓ) :
    boundaryChanneledDartPairEquiv19 G
        (boundaryPathDart R.B.leftPath i) =
      boundaryChanneledLeftDart R G i := by
  classical
  let d := boundaryPathDart R.B.leftPath i
  have htail : R.B.map.tail d := by
    simpa [d, boundaryPathDart] using
      (R.B.leftPath.edge_step
        ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.isLt⟩).2.1
  apply Prod.ext
  · rfl
  · exact boundaryChanneledDartPairEquiv_forward20 R G d htail

/-- Helper toward Definition 3.2: each LR presentation dart is the encoded
reverse of its indexed source right-path dart. -/
theorem boundaryChanneledRightDart_eq_encodedReverse20
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (i : Fin r) :
    boundaryChanneledDartPairEquiv19 G
        (R.B.map.toCombinatorialMap.edgeInv
          (R.B.rightPath.darts.reverse.get ⟨i.val, by
            rw [List.length_reverse, R.B.rightPath.darts_length]
            exact i.isLt⟩)) =
      boundaryChanneledRightDart R G i := by
  classical
  let p := R.B.rightPath.darts.reverse.get ⟨i.val, by
    rw [List.length_reverse, R.B.rightPath.darts_length]
    exact i.isLt⟩
  have hmem : p ∈ R.B.rightPath.darts :=
    List.mem_reverse.mp (List.get_mem _ _)
  have htail : R.B.map.tail p := by
    rcases List.mem_iff_get.mp hmem with ⟨j, hj⟩
    rw [← hj]
    exact (R.B.rightPath.edge_step j).2.1
  change boundaryChanneledDartPairEquiv19 G
      (R.B.map.toCombinatorialMap.edgeInv p) =
    ((Quotient.mk G.edgeSetoid p),
      !((boundaryChanneledPlaneMap R G).forward
        ⟨Quotient.mk G.edgeSetoid p, by simp [boundaryChanneledPlaneMap]⟩))
  rw [boundaryChanneledDartPairEquiv19_flip]
  apply Prod.ext
  · rfl
  · exact congrArg (!·)
      (boundaryChanneledDartPairEquiv_forward20 R G p htail)

/-- Helper toward Definition 3.2: the source left-path darts correspond
exactly to the UL indexed dart family under the geometric-edge equivalence. -/
theorem boundaryChanneled_leftPath_iff_leftDartIndex20
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (x : G.GeometricEdge × Bool) :
    (boundaryChanneledDartPairEquiv19 G).symm x ∈ R.B.leftPath.darts ↔
      ∃ i : Fin ℓ, boundaryChanneledLeftDart R G i = x := by
  constructor
  · intro hm
    rcases List.mem_iff_get.mp hm with ⟨j, hj⟩
    let i : Fin ℓ := ⟨j.val, by
      simpa [R.B.leftPath.darts_length] using j.isLt⟩
    have hidx :
        (⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.isLt⟩ :
          Fin R.B.leftPath.darts.length) = j := by
      exact Fin.ext rfl
    have hget : boundaryPathDart R.B.leftPath i =
        (boundaryChanneledDartPairEquiv19 G).symm x := by
      unfold boundaryPathDart
      calc
        R.B.leftPath.darts.get
            ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.isLt⟩ =
          R.B.leftPath.darts.get j :=
            congrArg (fun k : Fin R.B.leftPath.darts.length =>
              R.B.leftPath.darts.get k) hidx
        _ = (boundaryChanneledDartPairEquiv19 G).symm x := hj
    have htail : R.B.map.tail (boundaryPathDart R.B.leftPath i) := by
      simpa [boundaryPathDart] using
        (R.B.leftPath.edge_step
          ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.isLt⟩).2.1
    refine ⟨i, ?_⟩
    calc
      boundaryChanneledLeftDart R G i =
          boundaryChanneledDartPairEquiv19 G (boundaryPathDart R.B.leftPath i) :=
        (boundaryChanneledLeftDart_eq_encodedPath20 R G i).symm
      _ = x := by rw [hget, Equiv.apply_symm_apply]
  · rintro ⟨i, hi⟩
    have hmem : boundaryPathDart R.B.leftPath i ∈ R.B.leftPath.darts := by
      exact List.get_mem _ _
    have htail : R.B.map.tail (boundaryPathDart R.B.leftPath i) := by
      simpa [boundaryPathDart] using
        (R.B.leftPath.edge_step
          ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.isLt⟩).2.1
    have hpair := boundaryChanneledLeftDart_eq_encodedPath20 R G i
    have hsource : (boundaryChanneledDartPairEquiv19 G).symm x =
        boundaryPathDart R.B.leftPath i := by
      rw [← hi, ← hpair]
      exact Equiv.left_inv (boundaryChanneledDartPairEquiv19 G) _
    rw [hsource]
    exact hmem

/-- Helper toward Definition 3.2: the source reversed right-path darts
correspond exactly to the LR indexed dart family under the geometric-edge
equivalence. -/
theorem boundaryChanneled_reversedRightPath_iff_rightDartIndex20
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (x : G.GeometricEdge × Bool) :
    (boundaryChanneledDartPairEquiv19 G).symm x ∈
        R.B.rightPath.darts.reverse.map R.B.map.toCombinatorialMap.edgeInv ↔
      ∃ i : Fin r, boundaryChanneledRightDart R G i = x := by
  constructor
  · intro hm
    rcases List.mem_map.mp hm with ⟨d, hd, hflip⟩
    rcases List.mem_iff_get.mp hd with ⟨j, hj⟩
    let i : Fin r := ⟨j.val, by
      simpa [List.length_reverse, R.B.rightPath.darts_length] using j.isLt⟩
    have hidx :
        (⟨i.val, by
          rw [List.length_reverse, R.B.rightPath.darts_length]
          exact i.isLt⟩ : Fin R.B.rightPath.darts.reverse.length) = j := by
      exact Fin.ext rfl
    have hget : R.B.rightPath.darts.reverse.get
        ⟨i.val, by rw [List.length_reverse, R.B.rightPath.darts_length]; exact i.isLt⟩ = d := by
      rw [hidx]
      exact hj
    have htail : R.B.map.tail d := by
      have hmem : d ∈ R.B.rightPath.darts := by
        rw [← hget]
        exact List.mem_reverse.mp (List.get_mem _ _)
      rcases List.mem_iff_get.mp hmem with ⟨k, hk⟩
      rw [← hk]
      exact (R.B.rightPath.edge_step k).2.1
    have hpair := boundaryChanneledRightDart_eq_encodedReverse20 R G i
    refine ⟨i, ?_⟩
    calc
      boundaryChanneledRightDart R G i =
          boundaryChanneledDartPairEquiv19 G
            (R.B.map.toCombinatorialMap.edgeInv
              (R.B.rightPath.darts.reverse.get
                ⟨i.val, by
                  rw [List.length_reverse, R.B.rightPath.darts_length]
                  exact i.isLt⟩)) := hpair.symm
      _ = boundaryChanneledDartPairEquiv19 G
            (R.B.map.toCombinatorialMap.edgeInv d) :=
        congrArg (fun z => boundaryChanneledDartPairEquiv19 G
          (R.B.map.toCombinatorialMap.edgeInv z)) hget
      _ = x := by rw [hflip, Equiv.apply_symm_apply]
  · rintro ⟨i, hi⟩
    let d := R.B.rightPath.darts.reverse.get ⟨i.val, by
      rw [List.length_reverse, R.B.rightPath.darts_length]
      exact i.isLt⟩
    have hmem : d ∈ R.B.rightPath.darts :=
      List.mem_reverse.mp (List.get_mem _ _)
    have hmap : R.B.map.toCombinatorialMap.edgeInv d ∈
        R.B.rightPath.darts.reverse.map R.B.map.toCombinatorialMap.edgeInv :=
      List.mem_map.mpr ⟨d, List.get_mem _ _, rfl⟩
    have hpair := boundaryChanneledRightDart_eq_encodedReverse20 R G i
    have hsource : (boundaryChanneledDartPairEquiv19 G).symm x =
        R.B.map.toCombinatorialMap.edgeInv d := by
      rw [← hi, ← hpair]
      exact Equiv.left_inv (boundaryChanneledDartPairEquiv19 G) _
    rw [hsource]
    exact hmap

/-- Helper toward Definition 3.2: source outer-face border membership is
exactly membership in the two indexed presentation dart families. -/
theorem boundaryChanneled_markedOuterFace_borders_iff_indexed20
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (x : G.GeometricEdge × Bool) :
    G.dartBorders ((boundaryChanneledDartPairEquiv19 G).symm x)
        (boundaryChanneledMarkedOuterFace R G) ↔
      (∃ i : Fin ℓ, boundaryChanneledLeftDart R G i = x) ∨
        (∃ i : Fin r, boundaryChanneledRightDart R G i = x) := by
  rw [boundaryChanneled_markedOuterFace_borders_iff_boundaryPaths]
  rw [boundaryChanneled_leftPath_iff_leftDartIndex20,
    boundaryChanneled_reversedRightPath_iff_rightDartIndex20]

/-- Helper toward Definition 3.2: for the transported drawing of Geometry19,
every unbounded-face border dart is exactly an indexed presentation dart. -/
theorem boundaryChanneled_transport_dartBorders_indexed20
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ∃ (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
      DrawsMap (boundaryChanneledPlaneMap R G) H ∧
        ∀ U : H.Face, H.IsUnbounded U → ∀ d : G.GeometricEdge × Bool,
          H.dartBorders d U ↔
            ∃ i : InfiniteBoundaryDartIndex
              (boundaryChanneledPresentationWithJunctions R G).presentation,
              InfiniteBoundaryDartIndex.dart
                (boundaryChanneledPresentationWithJunctions R G).presentation i = d := by
  obtain ⟨rot, H, hDraws, hOrientation⟩ :=
    boundaryChanneled_transport_dart_orientation19 R G
  refine ⟨rot, H, hDraws, ?_⟩
  intro U hU d
  let e := boundaryChanneledDartPairEquiv19 G
  have htransport : H.dartBorders d U ↔
      G.dartBorders (e.symm d) (boundaryChanneledMarkedOuterFace R G) := by
    constructor
    · intro hd
      have hd' : H.dartBorders (e (e.symm d)) U := by
        simpa only [Equiv.apply_symm_apply] using hd
      exact boundaryChanneled_transport_dartBorders_reverse19
        R G hOuterUnbounded rot H hDraws hOrientation U hU (e.symm d) hd'
    · intro hs
      have hout := boundaryChanneled_transport_dartBorders_forward19
        R G hOuterUnbounded rot H hDraws hOrientation U hU (e.symm d) hs
      simpa only [e, Equiv.apply_symm_apply] using hout
  calc
    H.dartBorders d U ↔
        (∃ i : Fin ℓ, boundaryChanneledLeftDart R G i = d) ∨
          (∃ i : Fin r, boundaryChanneledRightDart R G i = d) := by
      rw [htransport]
      exact boundaryChanneled_markedOuterFace_borders_iff_indexed20 R G d
    _ ↔ ∃ i : InfiniteBoundaryDartIndex
          (boundaryChanneledPresentationWithJunctions R G).presentation,
          InfiniteBoundaryDartIndex.dart
            (boundaryChanneledPresentationWithJunctions R G).presentation i = d :=
      (boundaryChanneledPresentation_indexRange_iff_leftRight16 R G d).symm

end DirectedDistances.PaperProofs.Section3

end
