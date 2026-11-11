/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516PLDrawingAugmentation
public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness
public import DirectedDistances.PlanarMap.D39PLDrawingUniqueness5
public import DirectedDistances.PlanarMap.D39PolygonalConnected2
public import DirectedDistances.PlanarMap.FiniteDrawingExterior

/-! # Bounded side of a star chord

Helpers toward Proposition 5.16. The triangle walk is identified with the
exact orbit boundary; selecting its bounded side remains an open step. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
open Set
namespace D39FiniteBall

/-- Helper toward Proposition 5.16: the simple period-three walk created by
a star chord is a closed polygon tracing exactly its new dart orbit boundary
in both drawings. -/
theorem exists_star_chord_step_triangle_boundary
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (a b : B.D) (hvab : vert a ≠ vert b)
    (hi : 2 < Function.minimalPeriod B.map.faceSucc b)
    (hwalk : (B.map.faceSucc : B.D → B.D)^[2] b = a)
    (hcentre : vert (B.map.faceSucc b) ≠ vert a) :
    let C := B.insertChord a b (B.chord_corners_ne vert a b hvab)
    ∃ (Q Q' : PLDrawing C.D V C.map.edgeInv C.map.rot
        (B.chordVert vert a b)),
      (∀ v, Q.pos v = P.pos v) ∧ (∀ v, Q'.pos v = P'.pos v) ∧
      (∀ d : B.D, Q.arc (.inl d) = P.arc d) ∧
      (∀ d : B.D, Q'.arc (.inl d) = P'.arc d) ∧
      Function.minimalPeriod C.map.faceSucc (.inr true) = 3 ∧
      let O : D39BallFaceCycleOrbit C :=
        ⟨{z | C.map.faceSucc.SameCycle (.inr true) z}, .inr true, rfl⟩
      let q := faceWalkPolyline C (B.chordVert vert a b) Q (.inr true) 2
      let q' := faceWalkPolyline C (B.chordVert vert a b) Q' (.inr true) 2
      q.start = q.finish ∧ q'.start = q'.finish ∧
      q.IsCyclicSimple ∧ q'.IsCyclicSimple ∧
      q.image = C.plOrbitBoundary (B.chordVert vert a b) Q O ∧
      q'.image = C.plOrbitBoundary (B.chordVert vert a b) Q' O := by
  dsimp only
  obtain ⟨Q, Q', hpos, hpos', harc, harc', hperiod, hsimple, hsimple'⟩ :=
    B.exists_star_chord_step_simple_triangle vert P P' hvert a b hvab hi hwalk hcentre
  let C := B.insertChord a b (B.chord_corners_ne vert a b hvab)
  let O : D39BallFaceCycleOrbit C :=
    ⟨{z | C.map.faceSucc.SameCycle (.inr true) z}, .inr true, rfl⟩
  have hmem : (.inr true : C.D) ∈ O.val := by
    change C.map.faceSucc.SameCycle (.inr true) (.inr true)
    exact Equiv.Perm.SameCycle.rfl
  have hclosed := C.faceWalkPolyline_fullPeriod_closed
    (B.chordVert vert a b) Q (.inr true)
  have hclosed' := C.faceWalkPolyline_fullPeriod_closed
    (B.chordVert vert a b) Q' (.inr true)
  have hboundary := C.faceWalkPolyline_image_eq_plOrbitBoundary
    (B.chordVert vert a b) Q O (.inr true) hmem
  have hboundary' := C.faceWalkPolyline_image_eq_plOrbitBoundary
    (B.chordVert vert a b) Q' O (.inr true) hmem
  have hclosedQ :
      (faceWalkPolyline C (B.chordVert vert a b) Q (.inr true) 2).start =
        (faceWalkPolyline C (B.chordVert vert a b) Q (.inr true) 2).finish := by
    rw [hperiod] at hclosed
    simpa only [Nat.reduceSub] using hclosed
  have hclosedQ' :
      (faceWalkPolyline C (B.chordVert vert a b) Q' (.inr true) 2).start =
        (faceWalkPolyline C (B.chordVert vert a b) Q' (.inr true) 2).finish := by
    rw [hperiod] at hclosed'
    simpa only [Nat.reduceSub] using hclosed'
  have hboundaryQ :
      (faceWalkPolyline C (B.chordVert vert a b) Q (.inr true) 2).image =
        C.plOrbitBoundary (B.chordVert vert a b) Q O := by
    rw [hperiod] at hboundary
    simpa only [Nat.reduceSub] using hboundary
  have hboundaryQ' :
      (faceWalkPolyline C (B.chordVert vert a b) Q' (.inr true) 2).image =
        C.plOrbitBoundary (B.chordVert vert a b) Q' O := by
    rw [hperiod] at hboundary'
    simpa only [Nat.reduceSub] using hboundary'
  refine ⟨Q, Q', hpos, hpos', harc, harc', hperiod, ?_⟩
  refine ⟨?_, ?_, hsimple, hsimple', ?_, ?_⟩
  · exact hclosedQ
  · exact hclosedQ'
  · exact hboundaryQ
  · exact hboundaryQ'

end D39FiniteBall
end DirectedDistances.PlanarMap

end

































































































