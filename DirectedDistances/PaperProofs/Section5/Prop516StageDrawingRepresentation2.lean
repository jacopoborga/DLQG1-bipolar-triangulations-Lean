/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRepresentation
public import DirectedDistances.PlanarMap.D39BallOrbitComponents12
public import DirectedDistances.PlanarMap.PLDrawingWindingSides18
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Sides
public import DirectedDistances.KMSW.KMSWStageGeometryInduction

/-! # Stage drawing representation helpers

This file makes no paper-completion claim. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16. In a certified finite KMSW stage drawing,
each missing stage dart or its reversal borders the certified unbounded face.
The outer-boundary identification comes from the stage geometry certificate;
the missing-dart-to-outer-dart implication comes from the stage map. -/
theorem kmswStage_missingDart_borders_exterior
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (G : StageGeom w n P) (d : StageDart (kmswStage w n).nextEdge)
    (hd : (kmswStageDirectedMap w n).missing d) :
    ∃ F : P.Face, P.IsUnbounded F ∧
      (P.dartBorders d F ∨ P.dartBorders (edgeFlip _ d) F) := by
  refine ⟨G.exteriorFace, G.exteriorFace_unbounded, ?_⟩
  rcases (kmswStageDirectedMap w n).missing_outer d hd with houter | houter
  · exact Or.inl ((G.dartBorders_iff d).mpr houter)
  · have houter' : (kmswStageDirectedMap w n).IsOuter (edgeFlip _ d) := by
      change CombinatorialMap.IsOuter
        (kmswStageDirectedMap w n).toCombinatorialMap
        (kmswStageDirectedMap w n).outer
        ((kmswStageDirectedMap w n).toCombinatorialMap.edgeInv d) at houter
      change CombinatorialMap.IsOuter
        (kmswStageDirectedMap w n).toCombinatorialMap
        (kmswStageDirectedMap w n).outer
        (edgeFlip _ d)
      simpa [kmswStageDirectedMap, kmswDirectedMap, kmswMap] using houter
    exact Or.inr ((G.dartBorders_iff (edgeFlip _ d)).mpr houter')



@[expose] def plFaceOrbitOfDart (B : D39FiniteBall) (d : B.D) :
    D39BallFaceCycleOrbit B :=
  ⟨{e | B.map.faceSucc.SameCycle d e}, d, rfl⟩



theorem plOrbitFaceOfDart_eq_plDartFace
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (d : B.D) :
    B.plOrbitFace vert P hvert (plFaceOrbitOfDart B d) =
      B.plDartFace vert P hvert d := by
  apply B.plOrbitFace_eq_plDartFace_of_mem
  change B.map.faceSucc.SameCycle d d
  exact Equiv.Perm.SameCycle.rfl

/-- Helper toward Proposition 5.16. The `plDartFace` correspondence satisfies
U1: equal geometric faces are exactly equal face-successor orbits. -/
theorem plDartFace_eq_iff_sameCycle
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (d e : B.D) :
    B.plDartFace vert P hvert d = B.plDartFace vert P hvert e ↔
      B.map.faceSucc.SameCycle d e := by
  constructor
  · exact B.plDartFace_sameCycle_of_eq vert P hvert hconn d e
  · exact B.plDartFace_eq_of_sameCycle vert P hvert d e



theorem plDartFace_leftAtOn
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (d : B.D)
    (s : {t : I // t ∈ openParams}) :
    LeftAtOn (B.plDartFace vert P hvert d).val (P.arc d).toPath s :=
  P.dartBorders_toPath_leftAtOn hvert d (B.plDartFace vert P hvert d)
    ((B.plDartFace_eq_iff vert P hvert d _).mp rfl) s

/-- Helper toward Proposition 5.16. The reversed dart's face satisfies the
right-side test along the original dart path. -/
theorem plDartFace_flip_rightAtOn
    {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert) (d : B.D)
    (s : {t : I // t ∈ openParams}) :
    RightAtOn (B.plDartFace vert P hvert (B.map.edgeInv d)).val
      (P.arc d).toPath s :=
  P.dartBorders_flip_toPath_rightAtOn hvert d
    (B.plDartFace vert P hvert (B.map.edgeInv d))
    ((B.plDartFace_eq_iff vert P hvert (B.map.edgeInv d) _).mp rfl) s


































































end DirectedDistances.PaperProofs.Section5

end
