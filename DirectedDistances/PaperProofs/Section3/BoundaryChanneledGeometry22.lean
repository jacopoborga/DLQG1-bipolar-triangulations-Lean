/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry21
public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledPresentation3

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Endpoint casts preserve the range of a path. -/
private theorem boundaryChanneled_pathCast_range22 {x y x' y' : ℂ}
    (γ : Path x y) (hx : x' = x) (hy : y' = y) :
    Set.range (γ.cast hx hy) = Set.range γ := by
  ext z
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by simpa only [Path.cast_coe] using ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by simpa only [Path.cast_coe] using ht⟩

/-- Helper toward Definition 3.2: the source dart's two winding tests transfer
to the map edge oriented by its directed-plane-map carrier. -/
private theorem boundaryChanneled_sourceWinding_to_mapSides22
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (d : Fin R.dartCount) (htail : R.B.map.tail d)
    (F : (Drawing (boundaryChanneledPlaneMap R G)).Face) :
    ((∀ s : {t : unitInterval // t ∈ openParams},
        LeftAtOn F.val (G.arc d).toPath s) ↔
      LeftOf (boundaryChanneledPlaneMap R G) F
        ⟨Quotient.mk G.edgeSetoid d,
          boundaryChanneledPlaneMap_noMissing R G (Quotient.mk G.edgeSetoid d)⟩) ∧
    ((∀ s : {t : unitInterval // t ∈ openParams},
        RightAtOn F.val (G.arc d).toPath s) ↔
      RightOf (boundaryChanneledPlaneMap R G) F
        ⟨Quotient.mk G.edgeSetoid d,
          boundaryChanneledPlaneMap_noMissing R G (Quotient.mk G.edgeSetoid d)⟩) := by
  classical
  let M := boundaryChanneledPlaneMap R G
  let pair := boundaryChanneledDartPairEquiv19 G d
  let q : G.GeometricEdge := pair.1
  have hq : q = Quotient.mk G.edgeSetoid d := by
    change (boundaryChanneledDartPairEquiv19 G d).1 = Quotient.mk G.edgeSetoid d
    rfl
  let e : PresentEdge M := ⟨q, boundaryChanneledPlaneMap_noMissing R G q⟩
  have hbit : pair.2 = M.forward e := by
    simpa [pair, e, q, M] using
      (boundaryChanneledDartPairEquiv_forward20 R G d htail)
  have hpairInitial : boundaryDartInitial M pair = dartTailVertex R.B.map d := by
    simpa [M, pair] using boundaryChanneledDartPairEquiv19_initial R G d
  have hinit : boundaryDartInitial M pair = M.tail e := by
    rw [boundaryDartInitial_eq]
    change (if pair.2 = true then M.src q else M.tgt q) =
      (if M.forward e = true then M.src q else M.tgt q)
    rw [hbit]
  have hpairFlip :
      boundaryChanneledDartPairEquiv19 G
          (R.B.map.toCombinatorialMap.edgeInv d) = (pair.1, !pair.2) := by
    simpa [pair, q] using boundaryChanneledDartPairEquiv19_flip G d
  have hpairTerminal : boundaryDartTerminal M pair = dartHeadVertex R.B.map d := by
    calc
      boundaryDartTerminal M pair = boundaryDartInitial M (pair.1, !pair.2) := by
        rw [boundaryDartInitial_eq, boundaryDartTerminal_eq]
        cases pair.2 <;> rfl
      _ = boundaryDartInitial M
          (boundaryChanneledDartPairEquiv19 G
            (R.B.map.toCombinatorialMap.edgeInv d)) := by rw [← hpairFlip]
      _ = dartTailVertex R.B.map (R.B.map.toCombinatorialMap.edgeInv d) :=
        boundaryChanneledDartPairEquiv19_initial R G _
      _ = dartHeadVertex R.B.map d := rfl
  have hterm : boundaryDartTerminal M pair = M.head e := by
    rw [boundaryDartTerminal_eq]
    change (if pair.2 = true then M.tgt q else M.src q) =
      (if M.forward e = true then M.tgt q else M.src q)
    rw [hbit]
  let δ := orientedArc M e
  let γ := (G.arc d).toPath
  have hx : M.toPlaneMapWithMissing.pos (M.tail e) = (G.arc d).start := by
    change G.pos (M.tail e) = (G.arc d).start
    calc
      G.pos (M.tail e) = G.pos (boundaryDartInitial M pair) :=
        congrArg G.pos hinit.symm
      _ = G.pos (dartTailVertex R.B.map d) := congrArg G.pos hpairInitial
      _ = (G.arc d).start := (G.arc_start d).symm
  have hy : M.toPlaneMapWithMissing.pos (M.head e) = (G.arc d).finish := by
    change G.pos (M.head e) = (G.arc d).finish
    calc
      G.pos (M.head e) = G.pos (boundaryDartTerminal M pair) :=
        congrArg G.pos hterm.symm
      _ = G.pos (dartHeadVertex R.B.map d) := congrArg G.pos hpairTerminal
      _ = (G.arc d).finish := (G.arc_finish d).symm
  let γ' := γ.cast hx hy
  have hγ : Function.Injective γ' := by
    intro s t hst
    apply (G.arc d).toPath_injective (G.arc_length d) (G.arc_simple d)
    simpa [γ', γ, Path.cast_coe] using hst
  have hmap : Function.Injective (M.toPlaneMapWithMissing.arc q) := by
    change Function.Injective
      ((G.arc q.out).toPath.cast (G.arc_start q.out).symm (G.arc_finish q.out).symm)
    intro s t hst
    apply (G.arc q.out).toPath_injective (G.arc_length q.out) (G.arc_simple q.out)
    simpa using hst
  have hmapSymm : Function.Injective (M.toPlaneMapWithMissing.arc q).symm :=
    hmap.comp unitInterval.symm_bijective.injective
  have hδ : Function.Injective δ := by
    have hcoe := orientedArc_coe M e
    change Function.Injective (⇑δ)
    intro s t hst
    rw [hcoe] at hst
    by_cases hf : M.forward e
    · have hst' : (M.toPlaneMapWithMissing.arc q) s =
          (M.toPlaneMapWithMissing.arc q) t := by simpa [hf] using hst
      exact hmap hst'
    · have hst' : (M.toPlaneMapWithMissing.arc q).symm s =
          (M.toPlaneMapWithMissing.arc q).symm t := by simpa [hf] using hst
      exact hmapSymm hst'
  have hrange : Set.range δ = Set.range γ' := by
    calc
      Set.range δ = Set.range (M.toPlaneMapWithMissing.arc q) := by
        have hcoe := orientedArc_coe M e
        change Set.range (⇑δ) = Set.range (⇑(M.toPlaneMapWithMissing.arc q))
        rw [hcoe]
        by_cases hf : M.forward e
        · simp only [if_pos hf]
          rfl
        · simp only [if_neg hf, Path.symm_range]
          rfl
      _ = (G.arc q.out).image := by
        change Set.range (G.toPlaneGraphDrawing.arc q) = (G.arc q.out).image
        calc
          Set.range (G.toPlaneGraphDrawing.arc q) =
              Set.range (G.toPlaneGraphDrawing.arc (Quotient.mk G.edgeSetoid q.out)) := by
                exact congrArg (fun x => Set.range (G.toPlaneGraphDrawing.arc x))
                  (Quotient.out_eq q).symm
          _ = (G.arc q.out).image := G.toPlaneGraphDrawing_arc_range q.out
      _ = (G.arc d).image := by
        rcases G.geometricEdge_out_mk d with hout | hout
        · have hout' : q.out = d := by simpa [hq] using hout
          rw [hout']
        · have hout' : q.out = R.B.map.toCombinatorialMap.edgeInv d := by
            simpa [hq] using hout
          rw [hout', G.arc_image_flip]
      _ = Set.range γ := by
        exact (Polyline.range_toPath (G.arc d)).symm
      _ = Set.range γ' := (boundaryChanneled_pathCast_range22 γ hx hy).symm
  have hleft := boundaryChanneled_leftAtOn_transfer_of_injective_range_eq
    F.val γ' δ hγ hδ hrange
  have hright := boundaryChanneled_rightAtOn_transfer_of_injective_range_eq
    F.val γ' δ hγ hδ hrange
  constructor
  · change (∀ s, LeftAtOn F.val γ s) ↔ ∀ s, LeftAtOn F.val δ s
    constructor
    · intro hs
      apply hleft.mpr
      intro s
      exact (leftAtOn_cast_iff F.val γ hx hy s).mpr (hs s)
    · intro hs
      intro s
      exact (leftAtOn_cast_iff F.val γ hx hy s).mp ((hleft.mp hs) s)
  · change (∀ s, RightAtOn F.val γ s) ↔ ∀ s, RightAtOn F.val δ s
    constructor
    · intro hs
      apply hright.mpr
      intro s
      exact (rightAtOn_cast_iff F.val γ hx hy s).mpr (hs s)
    · intro hs
      intro s
      exact (rightAtOn_cast_iff F.val γ hx hy s).mp ((hright.mp hs) s)

/-- Helper toward Definition 3.2: consecutive lower-right darts join at
their common vertex in the reversed traversal of the source right path. -/
theorem boundaryChanneledPresentation_lowerRight_successorsJoin22
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (i j : Fin r)
    (hnext : (boundaryChanneledPresentationWithJunctions R G).presentation.lowerRight.next i =
      some j) :
    boundaryDartTerminal (boundaryChanneledPlaneMap R G)
        (boundaryChanneledRightDart R G i) =
      boundaryDartInitial (boundaryChanneledPlaneMap R G)
        (boundaryChanneledRightDart R G j) := by
  exact boundaryChanneledPresentation_lowerRight_join R G i j hnext

/-- Helper toward Definition 3.2: the marked outer face's winding tests on
the indexed UL and LR paths give map-side facts for their quotient edges. -/
theorem boundaryChanneledPresentation_mapSideData22
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ∃ F : (Drawing (boundaryChanneledPlaneMap R G)).Face,
      F.val = (boundaryChanneledMarkedOuterFace R G).val ∧
      (Drawing (boundaryChanneledPlaneMap R G)).IsExternal F ∧
      (∀ i : Fin ℓ,
        LeftOf (boundaryChanneledPlaneMap R G) F
          ⟨(boundaryChanneledLeftDart R G i).1,
            boundaryChanneledPlaneMap_noMissing R G
              (boundaryChanneledLeftDart R G i).1⟩) ∧
      (∀ i : Fin r,
        RightOf (boundaryChanneledPlaneMap R G) F
          ⟨(boundaryChanneledRightDart R G i).1,
            boundaryChanneledPlaneMap_noMissing R G
              (boundaryChanneledRightDart R G i).1⟩) := by
  obtain ⟨F, hF, hFext, hleft, hright⟩ :=
    boundaryChanneledPresentation_sourceSideData21 R G hOuterUnbounded
  refine ⟨F, hF, hFext, ?_, ?_⟩
  · intro i
    let d := boundaryPathDart R.B.leftPath i
    have htail : R.B.map.tail d := by
      simpa [d, boundaryPathDart] using
        (R.B.leftPath.edge_step
          ⟨i.val, by rw [R.B.leftPath.darts_length]; exact i.is_lt⟩).2.1
    have hside := (boundaryChanneled_sourceWinding_to_mapSides22 R G d htail F).1
    have hq : (boundaryChanneledLeftDart R G i).1 =
        (Quotient.mk G.edgeSetoid d) := rfl
    simpa [hF, hq, d] using hside.mp (hleft i)
  · intro i
    let p := R.B.rightPath.darts.reverse.get
      ⟨i.val, by
        rw [List.length_reverse, R.B.rightPath.darts_length]
        exact i.is_lt⟩
    have hmem : p ∈ R.B.rightPath.darts :=
      List.mem_reverse.mp (List.get_mem _ _)
    have htail : R.B.map.tail p := by
      rcases List.mem_iff_get.mp hmem with ⟨j, hj⟩
      rw [← hj]
      exact (R.B.rightPath.edge_step j).2.1
    have hside := (boundaryChanneled_sourceWinding_to_mapSides22 R G p htail F).2
    have hq : (boundaryChanneledRightDart R G i).1 =
        (Quotient.mk G.edgeSetoid p) := rfl
    simpa [hF, hq, p] using hside.mp (hright i)

/-- Helper toward Definition 3.2: the upper-left presentation satisfies its
infinite-side orientation, external-face, left-side, and successor clauses. -/
theorem boundaryChanneledPresentation_ULOkInf22
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ULOkInf (boundaryChanneledPresentationWithJunctions R G).presentation := by
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  obtain ⟨F, _hF, hFext, hleft, _hright⟩ :=
    boundaryChanneledPresentation_mapSideData22 R G hOuterUnbounded
  apply (ULOkInf_iff P).2
  constructor
  · intro i
    obtain ⟨hp, hforward⟩ :=
      (boundaryChanneledPresentation_sideDarts_oriented21 R G).1 i
    exact ⟨hp, hforward, F, hFext, hleft i⟩
  · exact boundaryChanneledPresentation_upperLeft_successorsJoin21 R G

/-- Helper toward Definition 3.2: the lower-right presentation satisfies its
infinite-side orientation, external-face, right-side, and successor clauses. -/
theorem boundaryChanneledPresentation_LROkInf22
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    LROkInf (boundaryChanneledPresentationWithJunctions R G).presentation := by
  let P := (boundaryChanneledPresentationWithJunctions R G).presentation
  obtain ⟨F, _hF, hFext, _hleft, hright⟩ :=
    boundaryChanneledPresentation_mapSideData22 R G hOuterUnbounded
  apply (LROkInf_iff P).2
  constructor
  · intro i
    obtain ⟨hp, hbackward⟩ :=
      (boundaryChanneledPresentation_sideDarts_oriented21 R G).2 i
    exact ⟨hp, hbackward, F, hFext, hright i⟩
  · exact boundaryChanneledPresentation_lowerRight_successorsJoin22 R G

/-- Helper toward Definition 3.2: package the proved upper-left and
lower-right infinite-side clauses for the boundary-channeled presentation. -/
theorem boundaryChanneledPresentation_infiniteSideClauses22
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ULOkInf (boundaryChanneledPresentationWithJunctions R G).presentation ∧
      LROkInf (boundaryChanneledPresentationWithJunctions R G).presentation :=
  ⟨boundaryChanneledPresentation_ULOkInf22 R G hOuterUnbounded,
    boundaryChanneledPresentation_LROkInf22 R G hOuterUnbounded⟩

/- Geometry21 provides the source winding tests and external map face. This
module transfers those tests to the quotient map's oriented arcs, proves both
finite successor joins, and packages the resulting UL/LR infinite-side
clauses. These declarations establish only the stated presentation clauses;
they do not claim completion of Definition 3.2. -/

end DirectedDistances.PaperProofs.Section3

end
