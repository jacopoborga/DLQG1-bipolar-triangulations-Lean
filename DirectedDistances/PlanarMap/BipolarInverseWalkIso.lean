/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarInverseWalk
public import DirectedDistances.PlanarMap.BipolarBoundaryBaseIso

/-! # Isomorphism invariance of inverse-walk helpers

Helpers toward the inverse direction of `thm-kmsw`; not the paper result -/

public section
namespace DirectedDistances.PlanarMap

variable {D D' : Type*} [Fintype D] [DecidableEq D]
  [Fintype D'] [DecidableEq D']
variable {ℓ r : ℕ}

private theorem inverseIso_rotSymm
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (d : D) :
    I.toEquiv (B.map.toCombinatorialMap.rot.symm d) =
      B'.map.toCombinatorialMap.rot.symm (I.toEquiv d) := by
  apply B'.map.toCombinatorialMap.rot.injective
  calc
    B'.map.toCombinatorialMap.rot
        (I.toEquiv (B.map.toCombinatorialMap.rot.symm d)) =
        I.toEquiv (B.map.toCombinatorialMap.rot
          (B.map.toCombinatorialMap.rot.symm d)) := (I.rot_comm _).symm
    _ = I.toEquiv d := by simp
    _ = B'.map.toCombinatorialMap.rot
        (B'.map.toCombinatorialMap.rot.symm (I.toEquiv d)) := by simp

/-- The vertex equivalence induced by a boundary isomorphism. Helper toward
result. -/
@[expose] noncomputable def inverseIsoVertexEquiv
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') : MapVertex B.map ≃ MapVertex B'.map :=
  I.vertexEquiv

/-- The vertex equivalence induced by a boundary isomorphism preserves the
initial vertex of every dart. Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_vertexEquiv_dartTail
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (d : D) :
    inverseIsoVertexEquiv I (dartTailVertex B.map d) =
      dartTailVertex B'.map (I.toEquiv d) :=
  I.vertexEquiv_dartTailVertex d

/-- The vertex equivalence induced by a boundary isomorphism preserves the
terminal vertex of every dart. Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_vertexEquiv_dartHead
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (d : D) :
    inverseIsoVertexEquiv I (dartHeadVertex B.map d) =
      dartHeadVertex B'.map (I.toEquiv d) :=
  I.vertexEquiv_dartHeadVertex d

/-- The vertex equivalence induced by a boundary isomorphism sends source to
source. Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_vertexEquiv_source
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') :
    inverseIsoVertexEquiv I B.source = B'.source :=
  I.vertexEquiv_source

/-- The vertex equivalence induced by a boundary isomorphism sends sink to
sink. Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_vertexEquiv_sink
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') :
    inverseIsoVertexEquiv I B.sink = B'.sink :=
  I.vertexEquiv_sink

/-- The dart equivalence preserves the first right-boundary dart. Helper
paper result. -/
theorem inverseIso_rightFirstDart
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') :
    I.toEquiv (B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos)) =
      B'.rightPath.firstDart (Nat.zero_lt_of_lt B'.right_length_pos) := by
  simp only [SimpleDirectedDartPath.firstDart, List.get_eq_getElem,
    ← I.rightDarts, List.getElem_map]

/-- The canonical rightmost outgoing selector commutes with a boundary
isomorphism. Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_rightmostOutgoing
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (v : MapVertex B.map)
    (hv : v ≠ B.sink) :
    I.toEquiv (rightmostOutgoing B v hv) =
      rightmostOutgoing B' (I.vertexEquiv v)
        (by
          intro h
          exact hv (I.vertexEquiv.injective
            (h.trans (I.vertexEquiv_sink).symm))) := by
  let hv' : I.vertexEquiv v ≠ B'.sink := by
    intro h
    exact hv (I.vertexEquiv.injective (h.trans (I.vertexEquiv_sink).symm))
  by_cases hs : v = B.source
  · subst v
    have hsource : I.toEquiv
        (rightmostOutgoing B B.source hv) =
          rightmostOutgoing B' B'.source (bipolar_source_ne_sink B') := by
      calc
        I.toEquiv (rightmostOutgoing B B.source hv) =
            I.toEquiv (B.rightPath.firstDart
              (Nat.zero_lt_of_lt B.right_length_pos)) :=
          congrArg I.toEquiv (rightmostOutgoing_source_eq_firstRightDart B)
        _ = B'.rightPath.firstDart
            (Nat.zero_lt_of_lt B'.right_length_pos) := inverseIso_rightFirstDart I
        _ = rightmostOutgoing B' B'.source (bipolar_source_ne_sink B') :=
          (rightmostOutgoing_source_eq_firstRightDart B').symm
    simpa only [I.vertexEquiv_source] using hsource
  · have hs' : I.vertexEquiv v ≠ B'.source := by
      intro h
      exact hs (I.vertexEquiv.injective (h.trans (I.vertexEquiv_source).symm))
    have hrotSymm (d : D) :
        I.toEquiv (B.map.toCombinatorialMap.rot.symm d) =
          B'.map.toCombinatorialMap.rot.symm (I.toEquiv d) := by
      apply B'.map.toCombinatorialMap.rot.injective
      calc
        B'.map.toCombinatorialMap.rot
            (I.toEquiv (B.map.toCombinatorialMap.rot.symm d)) =
            I.toEquiv (B.map.toCombinatorialMap.rot
              (B.map.toCombinatorialMap.rot.symm d)) := (I.rot_comm _).symm
        _ = I.toEquiv d := by simp
        _ = B'.map.toCombinatorialMap.rot
            (B'.map.toCombinatorialMap.rot.symm (I.toEquiv d)) := by simp
    have hchar := rightmostOutgoing_internal_characterization B v hs hv
    have hchar' := rightmostOutgoing_internal_characterization B'
      (I.vertexEquiv v) hs' hv'
    apply hchar'.2.2.2 (I.toEquiv (rightmostOutgoing B v hv))
    · calc
        dartTailVertex B'.map (I.toEquiv (rightmostOutgoing B v hv)) =
            I.vertexEquiv (dartTailVertex B.map (rightmostOutgoing B v hv)) :=
              (I.vertexEquiv_dartTailVertex _).symm
        _ = I.vertexEquiv v := congrArg I.vertexEquiv hchar.1
    · exact (I.tail_iff _).2 hchar.2.1
    · rw [← hrotSymm]
      exact fun h => hchar.2.2.1 ((I.tail_iff _).mp h)

/-- The dart equivalence preserves the first and last left-boundary darts.
Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_leftBoundaryEndpoints
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') :
    I.toEquiv (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) =
        B'.leftPath.firstDart (Nat.zero_lt_of_lt B'.left_length_pos) ∧
      I.toEquiv (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos)) =
        pathLastDart B'.leftPath (Nat.zero_lt_of_lt B'.left_length_pos) := by
  constructor
  · simp only [SimpleDirectedDartPath.firstDart, List.get_eq_getElem,
      ← I.leftDarts, List.getElem_map]
  · simp only [pathLastDart, List.get_eq_getElem, ← I.leftDarts,
      List.getElem_map]

/-- The canonical leftmost incoming selector commutes with a boundary
isomorphism. Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_leftmostIncoming
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (v : MapVertex B.map)
    (hv : v ≠ B.source) :
    I.toEquiv (leftmostIncoming B v hv) =
      leftmostIncoming B' (I.vertexEquiv v)
        (by
          intro h
          exact hv (I.vertexEquiv.injective
            (h.trans (I.vertexEquiv_source).symm))) := by
  let hv' : I.vertexEquiv v ≠ B'.source := by
    intro h
    exact hv (I.vertexEquiv.injective (h.trans (I.vertexEquiv_source).symm))
  by_cases ht : v = B.sink
  · subst v
    have hboundary :
        I.toEquiv (leftmostIncoming B B.sink hv) =
          leftmostIncoming B' B'.sink (bipolar_source_ne_sink B').symm := by
      have hlast := (inverseIso_leftBoundaryEndpoints I).2
      calc
        I.toEquiv (leftmostIncoming B B.sink hv) =
            I.toEquiv (B.map.toCombinatorialMap.edgeInv
              (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos))) :=
          congrArg I.toEquiv (incomingSelectors_sink_boundary B).1
        _ = B'.map.toCombinatorialMap.edgeInv
            (I.toEquiv (pathLastDart B.leftPath
              (Nat.zero_lt_of_lt B.left_length_pos))) := I.edgeInv_comm _
        _ = B'.map.toCombinatorialMap.edgeInv
            (pathLastDart B'.leftPath (Nat.zero_lt_of_lt B'.left_length_pos)) :=
          congrArg B'.map.toCombinatorialMap.edgeInv hlast
        _ = leftmostIncoming B' B'.sink
            (bipolar_source_ne_sink B').symm :=
          (incomingSelectors_sink_boundary B').1.symm
    simpa only [I.vertexEquiv_sink] using hboundary
  · have ht' : I.vertexEquiv v ≠ B'.sink := by
      intro h
      exact ht (I.vertexEquiv.injective (h.trans (I.vertexEquiv_sink).symm))
    have hchar := leftmostIncoming_internal_characterization B v hv ht
    have hchar' := leftmostIncoming_internal_characterization B'
      (I.vertexEquiv v) hv' ht'
    apply hchar'.2.2.2 (I.toEquiv (leftmostIncoming B v hv))
    · calc
        dartTailVertex B'.map (I.toEquiv (leftmostIncoming B v hv)) =
            I.vertexEquiv (dartTailVertex B.map (leftmostIncoming B v hv)) :=
              (I.vertexEquiv_dartTailVertex _).symm
        _ = I.vertexEquiv v := congrArg I.vertexEquiv hchar.1
    · intro h
      exact hchar.2.1 ((I.tail_iff _).mp h)
    · rw [← inverseIso_rotSymm I]
      exact (I.tail_iff _).2 hchar.2.2.1

/-- The dart equivalence preserves the final right-boundary dart. Helper
paper result. -/
theorem inverseIso_rightLastDart
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') :
    I.toEquiv (pathLastDart B.rightPath (Nat.zero_lt_of_lt B.right_length_pos)) =
      pathLastDart B'.rightPath (Nat.zero_lt_of_lt B'.right_length_pos) := by
  simp only [pathLastDart, List.get_eq_getElem, ← I.rightDarts,
    List.getElem_map]

private theorem inverseIso_ulParent
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (v : MapVertex B.map) :
    I.vertexEquiv (ulParent B (canonicalULSelector B) v) =
      ulParent B' (canonicalULSelector B') (I.vertexEquiv v) := by
  by_cases hs : v = B.source
  · subst v
    simp [ulParent, I.vertexEquiv_source]
  · have hs' : I.vertexEquiv v ≠ B'.source := by
      intro h
      exact hs (I.vertexEquiv.injective (h.trans (I.vertexEquiv_source).symm))
    have hsel :
        (canonicalULSelector B' (I.vertexEquiv v) hs').val =
          I.toEquiv ((canonicalULSelector B v hs).val) := by
      calc
        (canonicalULSelector B' (I.vertexEquiv v) hs').val =
            B'.map.toCombinatorialMap.edgeInv
              (leftmostIncoming B' (I.vertexEquiv v) hs') :=
          canonicalULSelector_val B' _ _
        _ = B'.map.toCombinatorialMap.edgeInv
              (I.toEquiv (leftmostIncoming B v hs)) :=
          congrArg B'.map.toCombinatorialMap.edgeInv
            (inverseIso_leftmostIncoming I v hs).symm
        _ = I.toEquiv (B.map.toCombinatorialMap.edgeInv
              (leftmostIncoming B v hs)) := (I.edgeInv_comm _).symm
        _ = I.toEquiv ((canonicalULSelector B v hs).val) :=
          congrArg I.toEquiv (canonicalULSelector_val B _ _).symm
    simp only [ulParent, hs, hs']
    calc
      I.vertexEquiv (dartTailVertex B.map ((canonicalULSelector B v hs).val)) =
          dartTailVertex B'.map
            (I.toEquiv ((canonicalULSelector B v hs).val)) :=
        I.vertexEquiv_dartTailVertex _
      _ = dartTailVertex B'.map ((canonicalULSelector B' (I.vertexEquiv v) hs').val) :=
        congrArg (dartTailVertex B'.map) hsel.symm

private theorem inverseIso_lrParent
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (v : MapVertex B.map) :
    I.vertexEquiv (lrParent B (canonicalLRSelector B) v) =
      lrParent B' (canonicalLRSelector B') (I.vertexEquiv v) := by
  by_cases ht : v = B.sink
  · subst v
    simp [lrParent, I.vertexEquiv_sink]
  · have ht' : I.vertexEquiv v ≠ B'.sink := by
      intro h
      exact ht (I.vertexEquiv.injective (h.trans (I.vertexEquiv_sink).symm))
    have hsel :
        (canonicalLRSelector B' (I.vertexEquiv v) ht').val =
          I.toEquiv ((canonicalLRSelector B v ht).val) := by
      calc
        (canonicalLRSelector B' (I.vertexEquiv v) ht').val =
            rightmostOutgoing B' (I.vertexEquiv v) ht' :=
          canonicalLRSelector_val B' _ _
        _ = I.toEquiv (rightmostOutgoing B v ht) :=
          (inverseIso_rightmostOutgoing I v ht).symm
        _ = I.toEquiv ((canonicalLRSelector B v ht).val) :=
          congrArg I.toEquiv (canonicalLRSelector_val B _ _).symm
    simp only [lrParent, ht, ht']
    calc
      I.vertexEquiv (dartHeadVertex B.map ((canonicalLRSelector B v ht).val)) =
          dartHeadVertex B'.map
            (I.toEquiv ((canonicalLRSelector B v ht).val)) :=
        I.vertexEquiv_dartHeadVertex _
      _ = dartHeadVertex B'.map ((canonicalLRSelector B' (I.vertexEquiv v) ht').val) :=
        congrArg (dartHeadVertex B'.map) hsel.symm

/-- Canonical upper-left heights are preserved by a boundary isomorphism.
Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_canonicalULHeight
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (v : MapVertex B.map) :
    canonicalULHeight B' (I.vertexEquiv v) = canonicalULHeight B v := by
  induction hheight : canonicalULHeight B v using Nat.strong_induction_on
      generalizing v with
  | h k ih =>
      by_cases hs : v = B.source
      · subst v
        simpa only [canonicalULHeight, I.vertexEquiv_source, ulHeight_source]
          using hheight
      · have hs' : I.vertexEquiv v ≠ B'.source := by
          intro h
          exact hs (I.vertexEquiv.injective (h.trans (I.vertexEquiv_source).symm))
        have hrec := ulHeight_parent B (canonicalULSelector B) hs
        have hparentHeight :
            canonicalULHeight B (ulParent B (canonicalULSelector B) v) + 1 = k := by
          change canonicalULHeight B v =
            canonicalULHeight B (ulParent B (canonicalULSelector B) v) + 1 at hrec
          omega
        have hlt : canonicalULHeight B (ulParent B (canonicalULSelector B) v) < k := by
          omega
        have hIH := ih _ hlt (ulParent B (canonicalULSelector B) v) rfl
        have hrec' := ulHeight_parent B' (canonicalULSelector B') hs'
        calc
          canonicalULHeight B' (I.vertexEquiv v) =
              canonicalULHeight B'
                (ulParent B' (canonicalULSelector B') (I.vertexEquiv v)) + 1 := hrec'
          _ = canonicalULHeight B'
                (I.vertexEquiv (ulParent B (canonicalULSelector B) v)) + 1 := by
            rw [inverseIso_ulParent]
          _ = canonicalULHeight B (ulParent B (canonicalULSelector B) v) + 1 := by
            rw [hIH]
          _ = k := hparentHeight

/-- Canonical lower-right heights are preserved by a boundary isomorphism.
Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_canonicalLRHeight
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (v : MapVertex B.map) :
    canonicalLRHeight B' (I.vertexEquiv v) = canonicalLRHeight B v := by
  induction hheight : canonicalLRHeight B v using Nat.strong_induction_on
      generalizing v with
  | h k ih =>
      by_cases ht : v = B.sink
      · subst v
        simpa only [canonicalLRHeight, I.vertexEquiv_sink, lrHeight_sink]
          using hheight
      · have ht' : I.vertexEquiv v ≠ B'.sink := by
          intro h
          exact ht (I.vertexEquiv.injective (h.trans (I.vertexEquiv_sink).symm))
        have hrec := lrHeight_parent B (canonicalLRSelector B) ht
        have hparentHeight :
            canonicalLRHeight B (lrParent B (canonicalLRSelector B) v) + 1 = k := by
          change canonicalLRHeight B v =
            canonicalLRHeight B (lrParent B (canonicalLRSelector B) v) + 1 at hrec
          omega
        have hlt : canonicalLRHeight B (lrParent B (canonicalLRSelector B) v) < k := by
          omega
        have hIH := ih _ hlt (lrParent B (canonicalLRSelector B) v) rfl
        have hrec' := lrHeight_parent B' (canonicalLRSelector B') ht'
        calc
          canonicalLRHeight B' (I.vertexEquiv v) =
              canonicalLRHeight B'
                (lrParent B' (canonicalLRSelector B') (I.vertexEquiv v)) + 1 := hrec'
          _ = canonicalLRHeight B'
                (I.vertexEquiv (lrParent B (canonicalLRSelector B) v)) + 1 := by
            rw [inverseIso_lrParent]
          _ = canonicalLRHeight B (lrParent B (canonicalLRSelector B) v) + 1 := by
            rw [hIH]
          _ = k := hparentHeight

/-- The contour's first dart is preserved by a boundary isomorphism. Helper
toward the `thm-kmsw` inverse -/
theorem inverseIso_contourStart
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') :
    I.toEquiv (contourStart B) = contourStart B' := by
  simpa only [contourStart, I.vertexEquiv_source] using
    inverseIso_rightmostOutgoing I B.source (bipolar_source_ne_sink B)

/-- The contour successor commutes with the dart equivalence. Helper toward
result. -/
theorem inverseIso_contourNext
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (d : D) :
    I.toEquiv (contourNext B d) = contourNext B' (I.toEquiv d) := by
  by_cases hd : B.map.tail d
  · have hd' : B'.map.tail (I.toEquiv d) := (I.tail_iff d).2 hd
    let v := dartHeadVertex B.map d
    let v' := dartHeadVertex B'.map (I.toEquiv d)
    have hv : I.vertexEquiv v = v' := I.vertexEquiv_dartHeadVertex d
    have hs : v ≠ B.source := contour_forward_head_ne_source B d hd
    have hs' : v' ≠ B'.source := by
      intro h
      apply hs
      apply I.vertexEquiv.injective
      exact hv.trans h |>.trans (I.vertexEquiv_source).symm
    have hsel :
        I.toEquiv (leftmostIncoming B v hs) =
          leftmostIncoming B' v' hs' := by
      simpa only [hv] using inverseIso_leftmostIncoming I v hs
    have hinc :
        (B.map.toCombinatorialMap.edgeInv d = leftmostIncoming B v hs) ↔
          (B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) =
            leftmostIncoming B' v' hs') := by
      constructor
      · intro h
        calc
          B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) =
              I.toEquiv (B.map.toCombinatorialMap.edgeInv d) := (I.edgeInv_comm d).symm
          _ = I.toEquiv (leftmostIncoming B v hs) := congrArg I.toEquiv h
          _ = leftmostIncoming B' v' hs' := hsel
      · intro h
        apply I.toEquiv.injective
        calc
          I.toEquiv (B.map.toCombinatorialMap.edgeInv d) =
              B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) := I.edgeInv_comm d
          _ = leftmostIncoming B' v' hs' := h
          _ = I.toEquiv (leftmostIncoming B v hs) := hsel.symm
    have hsink : (v = B.sink) ↔ (v' = B'.sink) := by
      constructor
      · intro h
        calc
          v' = I.vertexEquiv v := hv.symm
          _ = I.vertexEquiv B.sink := congrArg I.vertexEquiv h
          _ = B'.sink := I.vertexEquiv_sink
      · intro h
        apply I.vertexEquiv.injective
        calc
          I.vertexEquiv v = v' := hv
          _ = B'.sink := h
          _ = I.vertexEquiv B.sink := I.vertexEquiv_sink.symm
    by_cases hIn : B.map.toCombinatorialMap.edgeInv d = leftmostIncoming B v hs
    · have hIn' : B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) =
          leftmostIncoming B' v' hs' := hinc.mp hIn
      have hInD : B.map.toCombinatorialMap.edgeInv d =
          leftmostIncoming B (dartHeadVertex B.map d)
            (contour_forward_head_ne_source B d hd) := by
        simpa only [v] using hIn
      have hInD' : B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) =
          leftmostIncoming B' (dartHeadVertex B'.map (I.toEquiv d))
            (contour_forward_head_ne_source B' (I.toEquiv d) hd') := by
        simpa only [v'] using hIn'
      by_cases hSink : v = B.sink
      · have hSink' : v' = B'.sink := hsink.mp hSink
        have hSinkD : dartHeadVertex B.map d = B.sink := by simpa only [v] using hSink
        have hSinkD' : dartHeadVertex B'.map (I.toEquiv d) = B'.sink := by
          simpa only [v'] using hSink'
        rw [contourNext, contourNext, dite_eq_left hd, dite_eq_left hd',
          ite_eq_left hInD, ite_eq_left hInD', dite_eq_left hSinkD,
          dite_eq_left hSinkD']
        exact I.edgeInv_comm d
      · have hSink' : v' ≠ B'.sink := fun h => hSink (hsink.mpr h)
        have hSinkD : ¬ dartHeadVertex B.map d = B.sink := by
          simpa only [v] using hSink
        have hSinkD' : ¬ dartHeadVertex B'.map (I.toEquiv d) = B'.sink := by
          simpa only [v'] using hSink'
        have hro : I.toEquiv (rightmostOutgoing B v hSink) =
            rightmostOutgoing B' v' hSink' := by
          simpa only [hv] using inverseIso_rightmostOutgoing I v hSink
        rw [contourNext, contourNext, dite_eq_left hd, dite_eq_left hd',
          ite_eq_left hInD, ite_eq_left hInD', dite_eq_right hSinkD,
          dite_eq_right hSinkD']
        exact hro
    · have hIn' : ¬ (B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) =
          leftmostIncoming B' v' hs') := fun h => hIn (hinc.mpr h)
      have hInD : ¬ (B.map.toCombinatorialMap.edgeInv d =
          leftmostIncoming B (dartHeadVertex B.map d)
            (contour_forward_head_ne_source B d hd)) := by
        simpa only [v] using hIn
      have hInD' : ¬ (B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) =
          leftmostIncoming B' (dartHeadVertex B'.map (I.toEquiv d))
            (contour_forward_head_ne_source B' (I.toEquiv d) hd')) := by
        simpa only [v'] using hIn'
      rw [contourNext, contourNext, dite_eq_left hd, dite_eq_left hd',
        ite_eq_right hInD, ite_eq_right hInD']
      exact I.edgeInv_comm d
  · have hd' : ¬ B'.map.tail (I.toEquiv d) := fun h => hd ((I.tail_iff d).mp h)
    rw [contourNext, contourNext, dite_eq_right hd, dite_eq_right hd']
    calc
      I.toEquiv (B.map.toCombinatorialMap.rot
          (B.map.toCombinatorialMap.edgeInv d)) =
          B'.map.toCombinatorialMap.rot
            (I.toEquiv (B.map.toCombinatorialMap.edgeInv d)) := I.rot_comm _
      _ = B'.map.toCombinatorialMap.rot
            (B'.map.toCombinatorialMap.edgeInv (I.toEquiv d)) :=
          congrArg B'.map.toCombinatorialMap.rot (I.edgeInv_comm d)

/-- The induced contour permutations are conjugate pointwise by the dart
equivalence. Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_contourPerm_apply
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (d : D) :
    I.toEquiv (contourPerm B d) = contourPerm B' (I.toEquiv d) := by
  change I.toEquiv (contourNext B d) = contourNext B' (I.toEquiv d)
  exact inverseIso_contourNext I d

/-- Isomorphic base maps have the same number of directed geometric edges.
Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_numEdges_eq
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') :
    B.map.toCombinatorialMap.numEdges = B'.map.toCombinatorialMap.numEdges :=
  I.numEdges_eq

private theorem inverseIso_contourPow
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (n : ℕ) (d : D) :
    I.toEquiv ((contourPerm B ^ n) d) =
      (contourPerm B' ^ n) (I.toEquiv d) := by
  induction n generalizing d with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply]
      exact (ih (contourPerm B d)).trans
        (congrArg (contourPerm B' ^ n) (inverseIso_contourPerm_apply I d))

/-- The first-visit dart order is carried pointwise by the dart equivalence.
Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_firstVisitOrder
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') :
    (firstVisitOrder B).map I.toEquiv = firstVisitOrder B' := by
  classical
  have hcard : Fintype.card D = Fintype.card D' := Fintype.card_congr I.toEquiv
  have hvals :
      (fun i : Fin (Fintype.card D) =>
        I.toEquiv ((contourPerm B ^ i.val) (contourStart B))) =
      (fun i : Fin (Fintype.card D) =>
        (contourPerm B' ^ i.val) (contourStart B')) := by
    funext i
    calc
      I.toEquiv ((contourPerm B ^ i.val) (contourStart B)) =
          (contourPerm B' ^ i.val) (I.toEquiv (contourStart B)) :=
        inverseIso_contourPow I i.val (contourStart B)
      _ = (contourPerm B' ^ i.val) (contourStart B') :=
        congrArg (contourPerm B' ^ i.val) (inverseIso_contourStart I)
  have hvalsComp : I.toEquiv ∘ (fun i : Fin (Fintype.card D) =>
      (contourPerm B ^ i.val) (contourStart B)) =
      fun i => (contourPerm B' ^ i.val) (contourStart B') := by
    funext i
    exact congrFun hvals i
  have hfilter : (fun d : D' =>
      decide (∃ d', decide (B.map.tail d') ∧ I.toEquiv d' = d)) =
      fun d => decide (B'.map.tail d) := by
    funext d
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨d', hd', rfl⟩
      exact (I.tail_iff d').2 hd'
    · intro hd
      obtain ⟨d', rfl⟩ := I.toEquiv.surjective d
      exact ⟨d', (I.tail_iff d').mp hd, rfl⟩
  unfold firstVisitOrder
  rw [← hcard]
  rw [List.map_filter (p := fun d : D => decide (B.map.tail d))
    I.toEquiv.injective, List.map_ofFn, hvalsComp, hfilter]

/-- The zero-based Peano dart at each edge index is preserved by the dart
equivalence. Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_peanoEdge
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (j : Fin B.map.toCombinatorialMap.numEdges) :
    peanoEdge B' (Fin.cast I.numEdges_eq j) = I.toEquiv (peanoEdge B j) := by
  have hB : j.val < (firstVisitOrder B).length := by
    simpa only [firstVisitOrder_length] using j.isLt
  have hB' : j.val < (firstVisitOrder B').length := by
    rw [firstVisitOrder_length, ← I.numEdges_eq]
    exact j.isLt
  have hmap : j.val < ((firstVisitOrder B).map I.toEquiv).length := by
    simpa only [List.length_map] using hB
  have hgetOpt := congrArg (fun xs : List D' => xs[j.val]?)
    (inverseIso_firstVisitOrder I).symm
  have hget : (firstVisitOrder B')[j.val] =
      ((firstVisitOrder B).map I.toEquiv)[j.val] := by
    apply Option.some.inj
    calc
      some (firstVisitOrder B')[j.val] = (firstVisitOrder B')[j.val]? := by simp [hB']
      _ = ((firstVisitOrder B).map I.toEquiv)[j.val]? := hgetOpt
      _ = some ((firstVisitOrder B).map I.toEquiv)[j.val] := by simp
  change (firstVisitOrder B').get ⟨j.val, hB'⟩ =
    I.toEquiv ((firstVisitOrder B).get ⟨j.val, hB⟩)
  simpa only [List.get_eq_getElem, List.getElem_map] using hget

/-- The inverse walk is invariant under a boundary isomorphism after
reindexing edges by its edge equivalence. Helper toward the `thm-kmsw` -/
theorem inverseIso_bipolarInverseWalk
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (j : Fin B.map.toCombinatorialMap.numEdges) :
    bipolarInverseWalk B' (Fin.cast I.numEdges_eq j) = bipolarInverseWalk B j := by
  simp only [bipolarInverseWalk]
  rw [inverseIso_peanoEdge I j]
  apply Prod.ext
  · rw [← I.vertexEquiv_dartTailVertex, inverseIso_canonicalULHeight]
  · rw [← I.vertexEquiv_dartHeadVertex, inverseIso_canonicalLRHeight]

/-- A representative's inverse walk depends only on its unrooted base-map
isomorphism class. Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_kmswRepInverseWalk
    (R R' : KMSWMapRep ℓ r n)
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    kmswRepInverseWalk R' = kmswRepInverseWalk R := by
  funext j
  change bipolarInverseWalk R'.B (Fin.cast R'.edges.symm j) =
    bipolarInverseWalk R.B (Fin.cast R.edges.symm j)
  have hidx :
      Fin.cast I.numEdges_eq (Fin.cast R.edges.symm j) =
        Fin.cast R'.edges.symm j := Fin.ext rfl
  rw [← hidx]
  exact inverseIso_bipolarInverseWalk I (Fin.cast R.edges.symm j)

/-- The canonical rightmost incoming selector commutes with a boundary
isomorphism. Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_rightmostIncoming
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (v : MapVertex B.map)
    (hv : v ≠ B.source) :
    I.toEquiv (rightmostIncoming B v hv) =
      rightmostIncoming B' (I.vertexEquiv v)
        (by
          intro h
          exact hv (I.vertexEquiv.injective
            (h.trans (I.vertexEquiv_source).symm))) := by
  let hv' : I.vertexEquiv v ≠ B'.source := by
    intro h
    exact hv (I.vertexEquiv.injective (h.trans (I.vertexEquiv_source).symm))
  by_cases ht : v = B.sink
  · subst v
    have hboundary :
        I.toEquiv (rightmostIncoming B B.sink hv) =
          rightmostIncoming B' B'.sink (bipolar_source_ne_sink B').symm := by
      calc
        I.toEquiv (rightmostIncoming B B.sink hv) =
            I.toEquiv (B.map.toCombinatorialMap.edgeInv
              (pathLastDart B.rightPath (Nat.zero_lt_of_lt B.right_length_pos))) :=
          congrArg I.toEquiv (incomingSelectors_sink_boundary B).2
        _ = B'.map.toCombinatorialMap.edgeInv
            (I.toEquiv (pathLastDart B.rightPath
              (Nat.zero_lt_of_lt B.right_length_pos))) := I.edgeInv_comm _
        _ = B'.map.toCombinatorialMap.edgeInv
            (pathLastDart B'.rightPath (Nat.zero_lt_of_lt B'.right_length_pos)) :=
          congrArg B'.map.toCombinatorialMap.edgeInv (inverseIso_rightLastDart I)
        _ = rightmostIncoming B' B'.sink
            (bipolar_source_ne_sink B').symm :=
          (incomingSelectors_sink_boundary B').2.symm
    simpa only [I.vertexEquiv_sink] using hboundary
  · have ht' : I.vertexEquiv v ≠ B'.sink := by
      intro h
      exact ht (I.vertexEquiv.injective (h.trans (I.vertexEquiv_sink).symm))
    have hchar := rightmostIncoming_internal_characterization B v hv ht
    have hchar' := rightmostIncoming_internal_characterization B'
      (I.vertexEquiv v) hv' ht'
    apply hchar'.2.2.2 (I.toEquiv (rightmostIncoming B v hv))
    · calc
        dartTailVertex B'.map (I.toEquiv (rightmostIncoming B v hv)) =
            I.vertexEquiv (dartTailVertex B.map (rightmostIncoming B v hv)) :=
              (I.vertexEquiv_dartTailVertex _).symm
        _ = I.vertexEquiv v := congrArg I.vertexEquiv hchar.1
    · intro h
      exact hchar.2.1 ((I.tail_iff _).mp h)
    · rw [← I.rot_comm]
      exact (I.tail_iff _).2 hchar.2.2.1

/-- The canonical leftmost outgoing selector commutes with a boundary
isomorphism. Helper toward the `thm-kmsw` inverse -/
theorem inverseIso_leftmostOutgoing
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (v : MapVertex B.map)
    (hv : v ≠ B.sink) :
    I.toEquiv (leftmostOutgoing B v hv) =
      leftmostOutgoing B' (I.vertexEquiv v)
        (by
          intro h
          exact hv (I.vertexEquiv.injective
            (h.trans (I.vertexEquiv_sink).symm))) := by
  let hv' : I.vertexEquiv v ≠ B'.sink := by
    intro h
    exact hv (I.vertexEquiv.injective (h.trans (I.vertexEquiv_sink).symm))
  by_cases hs : v = B.source
  · subst v
    have hsource : I.toEquiv
        (leftmostOutgoing B B.source hv) =
          leftmostOutgoing B' B'.source (bipolar_source_ne_sink B') := by
      calc
        I.toEquiv (leftmostOutgoing B B.source hv) =
            I.toEquiv (B.leftPath.firstDart
              (Nat.zero_lt_of_lt B.left_length_pos)) :=
          congrArg I.toEquiv (leftmostOutgoing_source_eq_firstLeftDart B)
        _ = B'.leftPath.firstDart
            (Nat.zero_lt_of_lt B'.left_length_pos) :=
          (inverseIso_leftBoundaryEndpoints I).1
        _ = leftmostOutgoing B' B'.source (bipolar_source_ne_sink B') :=
          (leftmostOutgoing_source_eq_firstLeftDart B').symm
    simpa only [I.vertexEquiv_source] using hsource
  · have hs' : I.vertexEquiv v ≠ B'.source := by
      intro h
      exact hs (I.vertexEquiv.injective (h.trans (I.vertexEquiv_source).symm))
    have hchar := leftmostOutgoing_internal_characterization B v hs hv
    have hchar' := leftmostOutgoing_internal_characterization B'
      (I.vertexEquiv v) hs' hv'
    apply hchar'.2.2.2 (I.toEquiv (leftmostOutgoing B v hv))
    · calc
        dartTailVertex B'.map (I.toEquiv (leftmostOutgoing B v hv)) =
            I.vertexEquiv (dartTailVertex B.map (leftmostOutgoing B v hv)) :=
              (I.vertexEquiv_dartTailVertex _).symm
        _ = I.vertexEquiv v := congrArg I.vertexEquiv hchar.1
    · exact (I.tail_iff _).2 hchar.2.1
    · rw [← I.rot_comm]
      exact fun h => hchar.2.2.1 ((I.tail_iff _).mp h)

/-- unrooted isomorphism classes. -/
@[expose] noncomputable def kmswClassInverseWalk
    {ℓ r n : ℕ} : KMSWMapIsoClass ℓ r n → (Fin n → ℤ × ℤ) :=
  KMSWMapIsoClass.lift kmswRepInverseWalk (by
    intro R R' h
    rcases h with ⟨I⟩
    exact (inverseIso_kmswRepInverseWalk R R' I).symm)

/-- On a representative, the class inverse walk is the representative inverse
walk. Helper toward the `thm-kmsw` inverse -/
theorem kmswClassInverseWalk_mk
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) :
    kmswClassInverseWalk (KMSWMapIsoClass.mk R) = kmswRepInverseWalk R := by
  exact KMSWMapIsoClass.lift_mk _ _ _

end DirectedDistances.PlanarMap
