/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: counterclockwise successor data transports
along a dart equivalence preserving stars and initial directions. -/
private theorem boundaryChanneledCcwSuccessorEquiv
    {D D' : Type*} {star : Set D} {star' : Set D'}
    {dir : D → ℂ} {dir' : D' → ℂ} {d r : D} {d' r' : D'}
    (e : D ≃ D')
    (hstar : ∀ x, e x ∈ star' ↔ x ∈ star)
    (hdir : ∀ x, dir' (e x) = dir x)
    (hd : d' = e d) (hr : r' = e r)
    (h : CcwSuccessor star dir d r) : CcwSuccessor star' dir' d' r' := by
  have hset : star' = e '' star := by
    ext y
    constructor
    · intro hy
      have hy' : e (e.symm y) ∈ star' := by simpa using hy
      exact ⟨e.symm y, (hstar _).mp hy', e.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hstar x).mpr hx
  rcases h with ⟨hfinite, hdmem, hrmem, hcase⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hset]
    exact hfinite.image e
  · rw [hset]
    exact ⟨d, hdmem, hd.symm⟩
  · rw [hset]
    exact ⟨r, hrmem, hr.symm⟩
  · rcases hcase with ⟨heq, hsingleton⟩ | ⟨hne, hmin⟩
    · left
      refine ⟨?_, ?_⟩
      · calc r' = e r := hr
            _ = e d := congrArg e heq
            _ = d' := hd.symm
      · ext y
        constructor
        · intro hy
          rw [hset] at hy
          rcases hy with ⟨x, hx, hxy⟩
          rw [hsingleton] at hx
          subst x
          exact hxy.symm.trans hd.symm
        · intro hy
          rw [hset]
          refine ⟨d, ?_, ?_⟩
          · rw [hsingleton]
            rfl
          · have hy' : y = d' := by simpa using hy
            exact hd.symm.trans hy'.symm
    · right
      refine ⟨?_, ?_⟩
      · intro heq
        apply hne
        apply e.injective
        calc e r = r' := hr.symm
          _ = d' := heq
          _ = e d := hd
      · intro f hf hfd
        rw [hset] at hf
        rcases hf with ⟨x, hx, hxf⟩
        have hxd : x ≠ d := by
          intro hxd
          apply hfd
          calc f = e x := hxf.symm
            _ = e d := congrArg e hxd
            _ = d' := hd.symm
        have hsource := hmin x hx hxd
        calc
          ccwTurn (dir' d') (dir' r') = ccwTurn (dir d) (dir r) := by
            rw [hd, hr, hdir d, hdir r]
          _ ≤ ccwTurn (dir d) (dir x) := hsource
          _ = ccwTurn (dir' d') (dir' f) := by
            rw [hd, ← hxf, hdir d, hdir x]

/-- Helper toward Definition 3.2: reindex every dart of a PL drawing along an
equivalence commuting with reversal, rotation, and vertex incidence. -/
private def boundaryChanneledReindexDarts
    {D D' V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V}
    (P : PLDrawing D V flip rot vert) (e : D ≃ D')
    (hflip : ∀ d, flip' (e d) = e (flip d))
    (hrot : ∀ d, rot' (e d) = e (rot d))
    (hvert : ∀ d, vert' (e d) = vert d) :
    PLDrawing D' V flip' rot' vert' := by
  let Q : PLDrawing D' V flip' rot' vert' := {
    flip_involutive := by
      intro d'
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      calc
        flip' (flip' d') = flip' (flip' (e d)) := by rw [hd]
        _ = flip' (e (flip d)) := by rw [hflip]
        _ = e (flip (flip d)) := hflip _
        _ = e d := congrArg e (P.flip_involutive d)
        _ = d' := hd
    flip_ne := by
      intro d' h
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      have heq : e (flip d) = e d := by rw [← hflip, hd, h]
      exact P.flip_ne d (e.injective heq)
    vert_rotation := by
      intro d'
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      calc
        vert' (rot' d') = vert' (e (rot d)) := congrArg vert' (by rw [← hd, hrot])
        _ = vert (rot d) := hvert (rot d)
        _ = vert d := P.vert_rotation d
        _ = vert' (e d) := (hvert d).symm
        _ = vert' d' := congrArg vert' hd
    pos := P.pos
    pos_injective := P.pos_injective
    arc := fun d' => P.arc (e.symm d')
    arc_simple := fun d' => P.arc_simple (e.symm d')
    arc_length := fun d' => P.arc_length (e.symm d')
    arc_start := by
      intro d'
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      change (P.arc (e.symm d')).start = P.pos (vert' d')
      rw [← hd, Equiv.symm_apply_apply, P.arc_start, ← hvert, hd]
    arc_finish := by
      intro d'
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      change (P.arc (e.symm d')).finish = P.pos (vert' (flip' d'))
      rw [← hd, Equiv.symm_apply_apply, P.arc_finish, hflip, ← hvert]
    arc_flip := by
      intro d'
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      change P.arc (e.symm (flip' d')) = (P.arc d).reverse
      rw [← hd, hflip, e.symm_apply_apply, P.arc_flip]
    interior_disjoint := by
      intro d' f' hne hneflip
      let d := e.symm d'
      let f := e.symm f'
      have hd : e d = d' := e.apply_symm_apply d'
      have hf : e f = f' := e.apply_symm_apply f'
      have hne' : f ≠ d := by
        intro h
        apply hne
        calc f' = e f := hf.symm
          _ = e d := congrArg e h
          _ = d' := hd
      have hneflip' : f ≠ flip d := by
        intro h
        apply hneflip
        calc f' = e f := hf.symm
          _ = e (flip d) := congrArg e h
          _ = flip' (e d) := (hflip d).symm
          _ = flip' d' := congrArg flip' hd
      simpa [d, f] using P.interior_disjoint d f hne' hneflip'
    interior_avoids_vertices := by
      intro d' v hz
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      exact P.interior_avoids_vertices d v (by simpa [d, hd] using hz)
    locally_finite := by
      intro K hK
      have hset : {d' | (K ∩ (P.arc (e.symm d')).image).Nonempty} =
          e '' {d | (K ∩ (P.arc d).image).Nonempty} := by
        ext d'
        constructor
        · intro hd'
          refine ⟨e.symm d', ?_, e.apply_symm_apply d'⟩
          simpa using hd'
        · rintro ⟨d, hd, rfl⟩
          simpa using hd
      rw [hset]
      exact (P.locally_finite K hK).image e
    initial_nonzero := fun d' => P.initial_nonzero (e.symm d')
    initial_arg_injective := by
      intro d' f' hv harg
      let d := e.symm d'
      let f := e.symm f'
      have hd : e d = d' := e.apply_symm_apply d'
      have hf : e f = f' := e.apply_symm_apply f'
      have hv' : vert d = vert f := by
        calc vert d = vert' (e d) := (hvert d).symm
          _ = vert' d' := congrArg vert' hd
          _ = vert' f' := hv
          _ = vert' (e f) := congrArg vert' hf.symm
          _ = vert f := hvert f
      have hdf : d = f := P.initial_arg_injective d f hv' harg
      calc d' = e d := hd.symm
        _ = e f := congrArg e hdf
        _ = f' := hf
    rotation_agreement := by
      intro d'
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      have hr : rot' d' = e (rot d) := by rw [← hd, hrot]
      exact boundaryChanneledCcwSuccessorEquiv e
        (star := {x | vert x = vert d})
        (star' := {x | vert' x = vert' d'})
        (dir := fun x => (P.arc x).initialDirection)
        (dir' := fun x => (P.arc (e.symm x)).initialDirection)
        (d := d) (r := rot d) (d' := d') (r' := rot' d')
        (by
          intro x
          change vert' (e x) = vert' d' ↔ vert x = vert d
          rw [← hd, hvert x, hvert d])
        (by intro x; simp)
        hd.symm hr (P.rotation_agreement d)
  }
  exact Q

/-- Helper toward Definition 3.2: the finite drawing darts are equivalent to
geometric-edge darts, with the boolean recording agreement with the quotient
representative. -/
private def boundaryChanneledDartPairEquiv
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) : D ≃ P.GeometricEdge × Bool := by
  classical
  let toPair (d : D) : P.GeometricEdge × Bool :=
    (Quotient.mk P.edgeSetoid d,
      decide (d = (Quotient.mk P.edgeSetoid d).out))
  let fromPair (q : P.GeometricEdge) (b : Bool) : D :=
    match b with
    | true => q.out
    | false => flip q.out
  refine ⟨toPair, fun x => fromPair x.1 x.2, ?_, ?_⟩
  · intro d
    dsimp [toPair, fromPair]
    by_cases h : d = (Quotient.mk P.edgeSetoid d).out
    · rw [decide_eq_true_eq.mpr h]
      exact h.symm
    · rw [decide_eq_false_iff_not.mpr h]
      have hrel : (Quotient.mk P.edgeSetoid d).out = d ∨
          (Quotient.mk P.edgeSetoid d).out = flip d := by
        exact P.geometricEdge_out_mk d
      rcases hrel with hrel | hrel
      · exact (h hrel.symm).elim
      · calc
          flip (Quotient.mk P.edgeSetoid d).out = flip (flip d) := congrArg flip hrel
          _ = d := P.flip_involutive d
  · rintro ⟨q, b⟩
    induction q using Quotient.inductionOn with
    | h d =>
      cases b <;> simp [toPair, fromPair, P.geometricEdge_flip, P.flip_ne]

/-- Helper toward Definition 3.2: reversal on the quotient-dart carrier agrees
with reversal of the finite drawing dart. -/
private theorem boundaryChanneledDartPairEquiv_flip
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) :
    boundaryChanneledDartPairEquiv P (flip d) =
      ((boundaryChanneledDartPairEquiv P d).1,
        !(boundaryChanneledDartPairEquiv P d).2) := by
  classical
  have hq : Quotient.mk P.edgeSetoid (flip d) = Quotient.mk P.edgeSetoid d :=
    P.geometricEdge_flip d
  have houtEq := congrArg Quotient.out hq
  have hbitEq : decide (flip d = (Quotient.mk P.edgeSetoid (flip d)).out) =
      ! decide (d = (Quotient.mk P.edgeSetoid d).out) := by
    rw [houtEq]
    let q := (Quotient.mk P.edgeSetoid d).out
    change decide (flip d = q) = ! decide (d = q)
    by_cases h : d = q
    · have hflip : flip d ≠ q := by
        intro hf
        exact P.flip_ne d (hf.trans h.symm)
      rw [decide_eq_false_iff_not.mpr hflip, decide_eq_true_eq.mpr h]
      rfl
    · have hout : q = flip d := by
        rcases P.geometricEdge_out_mk d with hd | hd
        · exact (h hd.symm).elim
        · exact hd
      rw [decide_eq_true_eq.mpr hout.symm,
        decide_eq_false_iff_not.mpr h]
      rfl
  apply Prod.ext
  · exact hq
  · change decide (flip d = (Quotient.mk P.edgeSetoid (flip d)).out) =
      ! decide (d = (Quotient.mk P.edgeSetoid d).out)
    exact hbitEq

/-- Helper toward Definition 3.2: the pair encoding's initial vertex is the
initial vertex of the original finite-map dart. -/
private theorem boundaryChanneledDartPairEquiv_initial
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (d : Fin R.dartCount) :
    boundaryDartInitial (boundaryChanneledPlaneMap R G)
      (boundaryChanneledDartPairEquiv G d) = dartTailVertex R.B.map d := by
  classical
  let e := boundaryChanneledDartPairEquiv G d
  let q := e.1
  rcases G.geometricEdge_out_mk d with hout | hout
  · have hout' : q.out = d := by simpa [q, e, boundaryChanneledDartPairEquiv] using hout
    rw [boundaryDartInitial_eq]
    change (if e.2 then
      (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.src q
      else (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.tgt q) = _
    have hbit : e.2 = true := by
      dsimp [e, boundaryChanneledDartPairEquiv]
      simp [hout'.symm]
    rw [hbit]
    change dartTailVertex R.B.map q.out = dartTailVertex R.B.map d
    rw [hout']
  · have hout' : q.out = R.B.map.toCombinatorialMap.edgeInv d := by
      simpa [q, e, boundaryChanneledDartPairEquiv] using hout
    have hne : d ≠ q.out := by
      intro heq
      have hfix : R.B.map.toCombinatorialMap.edgeInv d = d := by
        calc
          R.B.map.toCombinatorialMap.edgeInv d = q.out := hout'.symm
          _ = d := heq.symm
      exact G.flip_ne d hfix
    rw [boundaryDartInitial_eq]
    change (if e.2 then
      (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.src q
      else (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.tgt q) = _
    have hbit : e.2 = false := by
      dsimp [e, boundaryChanneledDartPairEquiv]
      exact decide_eq_false_iff_not.mpr hne
    rw [hbit]
    change dartTailVertex R.B.map (R.B.map.toCombinatorialMap.edgeInv q.out) =
      dartTailVertex R.B.map d
    rw [hout', R.B.map.toCombinatorialMap.edgeInv_invol]

/-- Helper toward Definition 3.2: transport the boundary-channeled drawing
onto its geometric-edge dart carrier and match every geometric edge trace. -/
theorem h_boundary_drawing_transport
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R) :
    ∃ (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
      DrawsMap (boundaryChanneledPlaneMap R G) H := by
  classical
  let e := boundaryChanneledDartPairEquiv G
  let sourceRot := R.B.map.toCombinatorialMap.rot
  let rot : Equiv.Perm (G.GeometricEdge × Bool) := {
    toFun d := e (sourceRot (e.symm d))
    invFun d := e (sourceRot.symm (e.symm d))
    left_inv d := by simp
    right_inv d := by simp
  }
  have hflip (d : Fin R.dartCount) :
      (fun x : G.GeometricEdge × Bool => (x.1, !x.2)) (e d) =
        e (R.B.map.toCombinatorialMap.edgeInv d) := by
    simpa [e] using (boundaryChanneledDartPairEquiv_flip G d).symm
  have hrot (d : Fin R.dartCount) : rot (e d) = e (sourceRot d) := by
    simp [rot]
  have hvert (d : Fin R.dartCount) :
      boundaryDartInitial (boundaryChanneledPlaneMap R G) (e d) =
        dartTailVertex R.B.map d := by
    simpa [BoundaryChanneledPLDrawing] using
      boundaryChanneledDartPairEquiv_initial R G d
  let H := boundaryChanneledReindexDarts
    (flip' := fun x : G.GeometricEdge × Bool => (x.1, !x.2))
    (rot' := rot)
    (vert' := boundaryDartInitial (boundaryChanneledPlaneMap R G))
    G e hflip hrot hvert
  refine ⟨rot, H, ?_⟩
  constructor
  · rfl
  · intro d
    rcases d with ⟨q, b⟩
    -- The transported dart arc is one of the two representatives of `q`.
    change Set.range (H.arc (q, b)).toPath =
      Set.range ((boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.arc q)
    rw [Polyline.range_toPath]
    change (G.arc (e.symm (q, b))).image = _
    have htarget : Set.range
        ((boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.arc q) =
        (G.arc q.out).image := by
      calc
        Set.range
            ((boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.arc q) =
            Set.range ((boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.arc
              (Quotient.mk G.edgeSetoid q.out)) := by
                exact congrArg (fun x => Set.range
                  ((boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.arc x))
                  (Quotient.out_eq q).symm
        _ = (G.arc q.out).image := by
          change Set.range (G.toPlaneGraphDrawing.arc
            (Quotient.mk G.edgeSetoid q.out)) = (G.arc q.out).image
          exact G.toPlaneGraphDrawing_arc_range q.out
    rw [htarget]
    -- The Boolean orientation only reverses the same geometric edge.
    have hrep : e.symm (q, b) = q.out ∨
        e.symm (q, b) = R.B.map.toCombinatorialMap.edgeInv q.out := by
      cases b <;> simp [e, boundaryChanneledDartPairEquiv]
    rcases hrep with hrep | hrep
    · rw [hrep]
    · rw [hrep]
      exact G.arc_image_flip q.out

/-- Helper toward Definition 3.2: the conditional package with drawing
transport discharged and every remaining premise kept explicit. -/
theorem exists_boundaryChanneled_bound_edges32_of_open_clauses5
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)
    (h_boundary_dart_coverage :
      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))) (U : H.Face),
        DrawsMap (boundaryChanneledPlaneMap R G) H → H.IsUnbounded U →
        ∀ d, H.dartBorders d U ↔ ∃ i : InfiniteBoundaryDartIndex
            (boundaryChanneledPresentationWithJunctions R G).presentation,
          InfiniteBoundaryDartIndex.dart
            (boundaryChanneledPresentationWithJunctions R G).presentation i = d)
    (h_boundary_geometric_successor :
      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))) (U : H.Face),
        DrawsMap (boundaryChanneledPlaneMap R G) H → H.IsUnbounded U →
        IsGeometricExternalFaceSucc H U (fun d => rot.symm (d.1, !d.2)))
    (h_boundary_order : IsBoundaryOrderOfInf (boundaryChanneledPlaneMap R G)
      (boundaryChanneledPresentationWithJunctions R G).presentation)
    (h_boundary_upperLeft_orientation :
      ULOkInf (boundaryChanneledPresentationWithJunctions R G).presentation)
    (h_boundary_lowerRight_orientation :
      LROkInf (boundaryChanneledPresentationWithJunctions R G).presentation)
    (h_boundary_finite_position_order :
      ∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
        (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
          (fun d => (d.1, !d.2)) rot
          (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
        DrawsMap (boundaryChanneledPlaneMap R G) H →
        FiniteBoundaryPositionOrder4
          (boundaryChanneledPresentationWithJunctions R G).presentation
          (fun d => rot.symm (d.1, !d.2))) :
    let M := boundaryChanneledPlaneMap R G
    ∃ (B : BoundaryPresentationWithJunctions M)
      (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot (boundaryDartInitial M))
      (U : H.Face) (S : G.GeometricEdge × Bool → G.GeometricEdge × Bool),
      B = boundaryChanneledPresentationWithJunctions R G ∧ DrawsMap M H ∧
        IsFiniteExternalFaceIntervalOrder7 M B H U S := by
  exact exists_boundaryChanneled_bound_edges32_of_open_clauses4 R G
    (h_boundary_drawing_transport R G) h_boundary_dart_coverage
    h_boundary_geometric_successor h_boundary_order
    h_boundary_upperLeft_orientation h_boundary_lowerRight_orientation
    h_boundary_finite_position_order

/- Remaining full-binder package premises:

`{ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (G : BoundaryChanneledPLDrawing R)`

* `h_boundary_dart_coverage` has binders
  `∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G))) (U : H.Face),
    DrawsMap (boundaryChanneledPlaneMap R G) H → H.IsUnbounded U →
    ∀ d, H.dartBorders d U ↔ ∃ i : InfiniteBoundaryDartIndex
      (boundaryChanneledPresentationWithJunctions R G).presentation,
      InfiniteBoundaryDartIndex.dart
        (boundaryChanneledPresentationWithJunctions R G).presentation i = d`.
* `h_boundary_geometric_successor` has binders
  `∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G))) (U : H.Face),
    DrawsMap (boundaryChanneledPlaneMap R G) H → H.IsUnbounded U →
    IsGeometricExternalFaceSucc H U (fun d => rot.symm (d.1, !d.2))`.
* `h_boundary_order` is
  `IsBoundaryOrderOfInf (boundaryChanneledPlaneMap R G)
    (boundaryChanneledPresentationWithJunctions R G).presentation`.
* `h_boundary_upperLeft_orientation` is
  `ULOkInf (boundaryChanneledPresentationWithJunctions R G).presentation`.
* `h_boundary_lowerRight_orientation` is
  `LROkInf (boundaryChanneledPresentationWithJunctions R G).presentation`.
* `h_boundary_finite_position_order` has binders
  `∀ (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
    DrawsMap (boundaryChanneledPlaneMap R G) H →
    FiniteBoundaryPositionOrder4
      (boundaryChanneledPresentationWithJunctions R G).presentation
      (fun d => rot.symm (d.1, !d.2))`.

Three approaches were assessed for dart coverage: transfer path-edge
occurrences through `DrawsMap`; use unique unbounded-face existence plus
dart-to-closure; and transfer the indexed outer-face coverage pattern from
the UIBHBOT drawing. The first still needs outer-face classification, closure
does not imply dart incidence, and UIBHBOT has different source geometry.
For geometric successor, the attempted routes were direct rotation incidence,
classification by the finite combinatorial face successor, and transfer of
the KMSW stage run-successor proof. Each needs the missing identification of
the PL unbounded face with the combinatorial outer face. For order and
position, the three routes recorded in `BoundaryChanneledPresentation2.lean`
were finite outer-word transfer, the indexed path-edge split, and a position
equivalence built from the two finite runs; all still need that successor /
external-face identification. Thus none is assumed or discharged here. -/

end DirectedDistances.PaperProofs.Section3

end
end
