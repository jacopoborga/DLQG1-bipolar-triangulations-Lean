module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso5
public import DirectedDistances.PlanarMap.D39DrawingRepresentation3Transport

/-! # Dart-level oriented transport toward Proposition 5.16

This module proves the interval transport for an individual represented dart
under a geometric ball isomorphism, and records the remaining cyclic-order
obligation for the induced ball rotation. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16. The interval parameter on a dart induced
by a geometric ball isomorphism, including the source and target dart
orientations. -/
@[expose] def d39GeomBallIsoV2DartParam
    {B C : D39DomainRootedMapV2} {r : ℕ}
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r})
    (forward : Bool) : I ≃ₜ I :=
  (d39DartParamReversal forward).trans (e.edgeParam a) |>.trans
    (d39DartParamReversal (Bool.xor forward (e.edgeFlip a)))

/-- Helper toward Proposition 5.16. The dart parameter induced by a geometric
ball isomorphism is strictly increasing after accounting for both stored
edge directions. -/
theorem d39GeomBallIsoV2DartParam_strictMono
    {B C : D39DomainRootedMapV2} {r : ℕ}
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r})
    (forward : Bool) :
    StrictMono (d39GeomBallIsoV2DartParam e a forward) := by
  unfold d39GeomBallIsoV2DartParam
  have hs : StrictAnti unitInterval.symm := unitInterval.strictAnti_symm
  cases hb : forward <;> cases hf : e.edgeFlip a
  · dsimp [d39DartParamReversal] at ⊢
    change StrictMono (fun t : I =>
      unitInterval.symm (e.edgeParam a (unitInterval.symm t)))
    intro x y hxy
    have h1 : unitInterval.symm y < unitInterval.symm x := hs hxy
    have h2 := e.edgeParam_mono a hf h1
    exact hs h2
  · dsimp [d39DartParamReversal] at ⊢
    change StrictMono (fun t : I => e.edgeParam a (unitInterval.symm t))
    intro x y hxy
    have h1 : unitInterval.symm y < unitInterval.symm x := hs hxy
    exact e.edgeParam_anti a hf h1
  · dsimp [d39DartParamReversal] at ⊢
    change StrictMono (fun t : I => e.edgeParam a t)
    exact e.edgeParam_mono a hf
  · dsimp [d39DartParamReversal] at ⊢
    change StrictMono (fun t : I => unitInterval.symm (e.edgeParam a t))
    intro x y hxy
    exact hs (e.edgeParam_anti a hf hxy)

/-- Helper toward Proposition 5.16. The plane homeomorphism maps a dart arc
to the corresponding dart arc with the increasing interval parameter above. -/
theorem d39GeomBallIsoV2_arc_map_dart
    {B C : D39DomainRootedMapV2} {r : ℕ}
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r})
    (forward : Bool) (t : I) :
    e.h (if forward then B.map.toPlaneMapWithMissing.arc a.1 t
      else (B.map.toPlaneMapWithMissing.arc a.1).symm t) =
      if Bool.xor forward (e.edgeFlip a) then
        C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1
          (d39GeomBallIsoV2DartParam e a forward t)
      else
        (C.map.toPlaneMapWithMissing.arc (e.edgeEquiv a).1).symm
          (d39GeomBallIsoV2DartParam e a forward t) := by
  cases hb : forward <;> cases hf : e.edgeFlip a <;>
    simp [d39GeomBallIsoV2DartParam, d39DartParamReversal, hf,
      e.arc_map, unitInterval.symm_symm]










































end DirectedDistances.PaperProofs.Section5

end
