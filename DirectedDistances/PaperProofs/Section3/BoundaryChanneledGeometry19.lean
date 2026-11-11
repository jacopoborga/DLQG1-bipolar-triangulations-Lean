/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry18

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Definition 3.2: encode a finite drawing dart by its
geometric edge and the bit that records whether it agrees with the selected
quotient representative. -/
@[expose] def boundaryChanneledDartPairEquiv19
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) : D ≃ P.GeometricEdge × Bool := by
  classical
  let toPair (d : D) : P.GeometricEdge × Bool :=
    (Quotient.mk P.edgeSetoid d,
      decide (d = (Quotient.mk P.edgeSetoid d).out))
  let fromPair (q : P.GeometricEdge) (b : Bool) : D :=
    if b then q.out else flip q.out
  refine ⟨toPair, fun x => fromPair x.1 x.2, ?_, ?_⟩
  · intro d
    dsimp [toPair, fromPair]
    by_cases h : d = (Quotient.mk P.edgeSetoid d).out
    · rw [decide_eq_true_eq.mpr h]
      exact h.symm
    · rw [decide_eq_false_iff_not.mpr h]
      rcases P.geometricEdge_out_mk d with hout | hout
      · exact (h hout.symm).elim
      · calc
          flip (Quotient.mk P.edgeSetoid d).out = flip (flip d) := congrArg flip hout
          _ = d := P.flip_involutive d
  · rintro ⟨q, b⟩
    induction q using Quotient.inductionOn with
    | h d => cases b <;> simp [toPair, fromPair, P.geometricEdge_flip, P.flip_ne]

/-- Helper toward Definition 3.2: the dart-pair equivalence commutes with
reversal. -/
theorem boundaryChanneledDartPairEquiv19_flip
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) :
    boundaryChanneledDartPairEquiv19 P (flip d) =
      ((boundaryChanneledDartPairEquiv19 P d).1,
        !(boundaryChanneledDartPairEquiv19 P d).2) := by
  classical
  let e := boundaryChanneledDartPairEquiv19 P
  have hq : Quotient.mk P.edgeSetoid (flip d) = Quotient.mk P.edgeSetoid d :=
    P.geometricEdge_flip d
  have houtEq := congrArg Quotient.out hq
  have hbit : decide (flip d = (Quotient.mk P.edgeSetoid (flip d)).out) =
      ! decide (d = (Quotient.mk P.edgeSetoid d).out) := by
    rw [houtEq]
    let q := (Quotient.mk P.edgeSetoid d).out
    change decide (flip d = q) = ! decide (d = q)
    by_cases h : d = q
    · have hf : flip d ≠ q := by
        intro hf
        exact P.flip_ne d (hf.trans h.symm)
      rw [decide_eq_false_iff_not.mpr hf, decide_eq_true_eq.mpr h]
      rfl
    · have hq' : q = flip d := by
        rcases P.geometricEdge_out_mk d with hd | hd
        · exact (h hd.symm).elim
        · exact hd
      rw [decide_eq_true_eq.mpr hq'.symm, decide_eq_false_iff_not.mpr h]
      rfl
  apply Prod.ext
  · exact hq
  · exact hbit

/-- Helper toward Definition 3.2: the pair encoding selects the dart
orientation whose initial vertex is the directed map tail. -/
theorem boundaryChanneledDartPairEquiv19_initial
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) (d : Fin R.dartCount) :
    boundaryDartInitial (boundaryChanneledPlaneMap R G)
      (boundaryChanneledDartPairEquiv19 G d) = dartTailVertex R.B.map d := by
  classical
  let e := boundaryChanneledDartPairEquiv19 G d
  let q := e.1
  rcases G.geometricEdge_out_mk d with hout | hout
  · have hout' : q.out = d := by
      simpa [q, e, boundaryChanneledDartPairEquiv19] using hout
    rw [boundaryDartInitial_eq]
    change (if e.2 then
      (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.src q
      else (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.toPlaneGraphDrawing.tgt q) = _
    have hb : e.2 = true := by
      dsimp [e, boundaryChanneledDartPairEquiv19]
      simp [hout'.symm]
    rw [hb]
    change dartTailVertex R.B.map q.out = dartTailVertex R.B.map d
    rw [hout']
  · have hout' : q.out = R.B.map.toCombinatorialMap.edgeInv d := by
      simpa [q, e, boundaryChanneledDartPairEquiv19] using hout
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
    have hb : e.2 = false := by
      dsimp [e, boundaryChanneledDartPairEquiv19]
      exact decide_eq_false_iff_not.mpr hne
    rw [hb]
    change dartTailVertex R.B.map
      (R.B.map.toCombinatorialMap.edgeInv q.out) = dartTailVertex R.B.map d
    rw [hout', R.B.map.toCombinatorialMap.edgeInv_invol]

/-- Helper toward Definition 3.2: counterclockwise successor data is
preserved by a dart equivalence that preserves stars and initial directions. -/
private theorem boundaryChanneledCcwSuccessorEquiv19
    {D D' : Type*} {star : Set D} {star' : Set D'}
    {dir : D → ℂ} {dir' : D' → ℂ} {d r : D} {d' r' : D'}
    (e : D ≃ D') (hstar : ∀ x, e x ∈ star' ↔ x ∈ star)
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
  · rw [hset]; exact hfinite.image e
  · rw [hset]; exact ⟨d, hdmem, hd.symm⟩
  · rw [hset]; exact ⟨r, hrmem, hr.symm⟩
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
          · rw [hsingleton]; rfl
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
        have hs := hmin x hx hxd
        calc
          ccwTurn (dir' d') (dir' r') = ccwTurn (dir d) (dir r) := by
            rw [hd, hr, hdir d, hdir r]
          _ ≤ ccwTurn (dir d) (dir x) := hs
          _ = ccwTurn (dir' d') (dir' f) := by
            rw [hd, ← hxf, hdir d, hdir x]

/-- Helper toward Definition 3.2: reindex a PL drawing along a dart
equivalence commuting with reversal, rotation, and initial vertices. -/
private def boundaryChanneledReindexDarts19
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
      exact boundaryChanneledCcwSuccessorEquiv19 e
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

/-- Helper toward Definition 3.2: the transported drawing assigns the
original arc orientation to the image of every source dart. -/
theorem boundaryChanneled_transport_dart_orientation19
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R) :
    ∃ (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
      DrawsMap (boundaryChanneledPlaneMap R G) H ∧
        ∀ d : Fin R.dartCount,
          H.arc (boundaryChanneledDartPairEquiv19 G d) = G.arc d := by
  classical
  let e := boundaryChanneledDartPairEquiv19 G
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
    simpa [e] using (boundaryChanneledDartPairEquiv19_flip G d).symm
  have hrot (d : Fin R.dartCount) : rot (e d) = e (sourceRot d) := by
    simp [rot]
  have hvert (d : Fin R.dartCount) :
      boundaryDartInitial (boundaryChanneledPlaneMap R G) (e d) =
        dartTailVertex R.B.map d := by
    simpa [BoundaryChanneledPLDrawing] using
      boundaryChanneledDartPairEquiv19_initial R G d
  let H := boundaryChanneledReindexDarts19
    (flip' := fun x : G.GeometricEdge × Bool => (x.1, !x.2))
    (rot' := rot)
    (vert' := boundaryDartInitial (boundaryChanneledPlaneMap R G))
    G e hflip hrot hvert
  refine ⟨rot, H, ?_, ?_⟩
  · constructor
    · rfl
    · intro d
      rcases d with ⟨q, b⟩
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
          _ = (G.arc q.out).image := G.toPlaneGraphDrawing_arc_range q.out
      rw [htarget]
      have hrep : e.symm (q, b) = q.out ∨
          e.symm (q, b) = R.B.map.toCombinatorialMap.edgeInv q.out := by
        cases b <;> simp [e, boundaryChanneledDartPairEquiv19]
      rcases hrep with hrep | hrep
      · rw [hrep]
      · rw [hrep]
        exact G.arc_image_flip q.out
  · intro d
    change G.arc (e.symm (e d)) = G.arc d
    rw [Equiv.symm_apply_apply]

/-- Helper toward Definition 3.2: the source border wedge transfers to the
transported dart when the unbounded component is identified. -/
theorem boundaryChanneled_transport_dartBorders_forward19
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (hDraws : DrawsMap (boundaryChanneledPlaneMap R G) H)
    (hOrientation : ∀ d : Fin R.dartCount,
      H.arc (boundaryChanneledDartPairEquiv19 G d) = G.arc d)
    (U : H.Face) (hU : H.IsUnbounded U)
    (d : Fin R.dartCount)
    (hd : G.dartBorders d (boundaryChanneledMarkedOuterFace R G)) :
    H.dartBorders (boundaryChanneledDartPairEquiv19 G d) U := by
  have hface := boundaryChanneled_transport_unboundedFace_eq_marked
    R G hOuterUnbounded rot H hDraws U hU
  change ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ, 0 < t → t < δ → 0 < ε → ε < δ →
    (H.arc (boundaryChanneledDartPairEquiv19 G d)).start +
      (t : ℂ) * ((H.arc (boundaryChanneledDartPairEquiv19 G d)).initialDirection +
        (ε : ℂ) * Complex.I * (H.arc (boundaryChanneledDartPairEquiv19 G d)).initialDirection)
        ∈ U.val
  rcases hd with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htd he hε
  have hpoint := hδ' t ε ht htd he hε
  rw [hOrientation d, hface]
  exact hpoint

/-- Helper toward Definition 3.2: the transported border wedge implies the
source border wedge for the same dart orientation. -/
theorem boundaryChanneled_transport_dartBorders_reverse19
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G))
    (rot : Equiv.Perm (G.GeometricEdge × Bool))
    (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
      (fun d => (d.1, !d.2)) rot
      (boundaryDartInitial (boundaryChanneledPlaneMap R G)))
    (hDraws : DrawsMap (boundaryChanneledPlaneMap R G) H)
    (hOrientation : ∀ d : Fin R.dartCount,
      H.arc (boundaryChanneledDartPairEquiv19 G d) = G.arc d)
    (U : H.Face) (hU : H.IsUnbounded U)
    (d : Fin R.dartCount)
    (hd : H.dartBorders (boundaryChanneledDartPairEquiv19 G d) U) :
    G.dartBorders d (boundaryChanneledMarkedOuterFace R G) := by
  have hface := boundaryChanneled_transport_unboundedFace_eq_marked
    R G hOuterUnbounded rot H hDraws U hU
  change ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ, 0 < t → t < δ → 0 < ε → ε < δ →
    (G.arc d).start + (t : ℂ) *
      ((G.arc d).initialDirection + (ε : ℂ) * Complex.I * (G.arc d).initialDirection) ∈
        (boundaryChanneledMarkedOuterFace R G).val
  rcases hd with ⟨δ, hδ, hδ'⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htd he hε
  have hpoint := hδ' t ε ht htd he hε
  rw [hOrientation d, hface] at hpoint
  exact hpoint

/-- Helper toward Definition 3.2: the specifically constructed transported
drawing has the same dart-border predicate as the source marked face, through
the orientation-preserving dart equivalence. -/
theorem boundaryChanneled_transport_dartBorders19
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ∃ (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
      DrawsMap (boundaryChanneledPlaneMap R G) H ∧
        ∀ U : H.Face, H.IsUnbounded U → ∀ d : Fin R.dartCount,
          H.dartBorders (boundaryChanneledDartPairEquiv19 G d) U ↔
            G.dartBorders d (boundaryChanneledMarkedOuterFace R G) := by
  obtain ⟨rot, H, hDraws, hOrientation⟩ :=
    boundaryChanneled_transport_dart_orientation19 R G
  refine ⟨rot, H, hDraws, ?_⟩
  intro U hU d
  constructor
  · exact boundaryChanneled_transport_dartBorders_reverse19
      R G hOuterUnbounded rot H hDraws hOrientation U hU d
  · exact boundaryChanneled_transport_dartBorders_forward19
      R G hOuterUnbounded rot H hDraws hOrientation U hU d

/- OPEN remaining target (full binders):

    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ∃ (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
      DrawsMap (boundaryChanneledPlaneMap R G) H ∧
      ∀ U : H.Face, H.IsUnbounded U →
        ∀ d, H.dartBorders d U ↔
          ∃ i : InfiniteBoundaryDartIndex
            (boundaryChanneledPresentationWithJunctions R G).presentation,
            InfiniteBoundaryDartIndex.dart
              (boundaryChanneledPresentationWithJunctions R G).presentation i = d

The constructed drawing now has an exact dartwise arc-orientation identity,
and its dart-border predicate transfers in both directions to the source
marked face. The remaining step is to identify the source outer-word dart
families, transported through `boundaryChanneledDartPairEquiv19`, with the
indexed presentation dart family. No additional geometric premise is used. -/

end DirectedDistances.PaperProofs.Section3

end
