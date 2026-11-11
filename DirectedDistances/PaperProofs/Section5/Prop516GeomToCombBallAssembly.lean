/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallIso16

/-! # Geometric to combinatorial ball assembly

Helpers toward Proposition 5.16. This module assembles the fields available
from the geometric ball equivalence and records the exact remaining fields.
It makes no paper-completion claim.

For `D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)`, the fields are:

* `toEquiv`: supplied by
  `d39DrawingRepresentationData3_geomBallIso_ballDartEquiv` (Iso3), using
  the ball-dart/geometric-edge characterization (Iso3).
* `rot_comm`: the first-return rotation compatibility stated below; Iso15
  proves full-star transport but Iso16 records the missing cyclic-order step.
* `edgeInv_comm`: supplied by the geometric directed-edge equivalence and
  `D39DrawingRepresentationData.dart_edgeInv` (Iso2/3).
* `missing_iff`: supplied by `D39GeomBallIsoV2.missing_map` and
  `D39DrawingRepresentationData.dart_missing` (Iso2).
* `tail_iff`: supplied on present edges by
  `D39GeomBallIsoV2.orientation_map` and
  `D39DrawingRepresentationData.dart_orientation` (Iso2); missing edges have
  no tail by the rooted-map convention.
* `root_comm`: proved below from the root clauses in Iso2.
* `original_iff`: requires identifying `e.faceEquiv` with the represented
  face assignments; the retained-face/orbit bridge is in Iso3/4, but the
  equality is not supplied by the geometric isomorphism.

The geometric radius used here is exactly `r`; the intended cylinder index
shift is handled by the caller. No rotation or face-matching assumption is
introduced. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.16: the ball-dart equivalence carries the
ordered root dart to the ordered target root dart. -/
theorem d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_root
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
        ⟨M.rootMark.dart, (d39BallDarts_root_mem M e.radius_pos).1⟩ =
      ⟨N.rootMark.dart, (d39BallDarts_root_mem N e.radius_pos).1⟩ := by
  apply Subtype.ext
  have hroot := d39GeomBallIsoV2_representation_root_dart y e
  simpa [d39DrawingRepresentationData3_geomBallIso_ballDartEquiv,
    d39GeomBallIsoV2RepresentationDartEquiv,
    d39GeomBallIsoV2DirectedEdgeEquiv, x.root_mark, y.root_mark] using hroot

/-- Helper toward Proposition 5.16: the ball-dart equivalence commutes with
the inherited edge reversal. -/
theorem d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_edgeInv
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    [DecidableEq {d : M.core.D // d ∈ d39BallDarts M r}]
    [DecidableEq {d : N.core.D // d ∈ d39BallDarts N r}]
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
        ((d39BallMap M r).edgeInv d) =
      (d39BallMap N r).edgeInv
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d) := by
  classical
  apply Subtype.ext
  apply y.dartEquiv.injective
  change y.dartEquiv
      (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
        ⟨M.core.edgeInv d.1, d39BallDarts_edgeInv_closed M r d.1 d.2⟩).1 =
    y.dartEquiv (N.core.edgeInv
      (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1)
  rw [y.dart_edgeInv]
  simp [d39DrawingRepresentationData3_geomBallIso_ballDartEquiv,
    d39GeomBallIsoV2RepresentationDartEquiv,
    d39GeomBallIsoV2DirectedEdgeEquiv, x.dart_edgeInv]

/-- Helper toward Proposition 5.16: the ball-dart equivalence preserves the
missing-edge tag, including when the root edge is missing. -/
theorem d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_missing_iff
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    d39BallMissing N r
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d) ↔
      d39BallMissing M r d := by
  let a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r} :=
    ⟨(x.dartEquiv d.1).1,
      (d39DrawingRepresentationData3_ballDarts_iff x r d.1).mp d.2⟩
  have hpair :
      y.dartEquiv
          (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 =
        ((e.edgeEquiv a).1,
          Bool.xor (x.dartEquiv d.1).2 (e.edgeFlip a)) := by
    simp [d39DrawingRepresentationData3_geomBallIso_ballDartEquiv,
      d39GeomBallIsoV2RepresentationDartEquiv,
      d39GeomBallIsoV2DirectedEdgeEquiv, a]
  change N.core.missing
      (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 ↔
    M.core.missing d.1
  calc
    N.core.missing
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 ↔
      C.map.toPlaneMapWithMissing.missing
        (y.dartEquiv
          (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1).1 :=
            (y.dart_missing _).symm
    _ ↔ C.map.toPlaneMapWithMissing.missing (e.edgeEquiv a).1 := by
      rw [hpair]
    _ ↔ B.map.toPlaneMapWithMissing.missing a.1 := e.missing_map a
    _ ↔ M.core.missing d.1 := x.dart_missing d.1

/-- Helper toward Proposition 5.16: the ball-dart equivalence preserves the
directed tail tag on present edges and the absent tag on missing edges. -/
theorem d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_tail_iff
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2} {r : ℕ}
    (x : D39DrawingRepresentationData3 M B)
    (y : D39DrawingRepresentationData3 N C)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root)
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    d39BallTail N r
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d) ↔
      d39BallTail M r d := by
  change N.core.tail
      (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 ↔
    M.core.tail d.1
  by_cases hm : M.core.missing d.1
  · have hmN :=
      (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_missing_iff
        x y e d).mpr hm
    have htm := M.core.tail_missing d.1 hm
    have htn := N.core.tail_missing
      (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 hmN
    exact ⟨fun ht => (htn ht).elim, fun ht => (htm ht).elim⟩
  · have hmN : ¬ N.core.missing
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 := by
      intro h
      exact hm ((d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_missing_iff
        x y e d).mp h)
    let a : {a : B.E // a ∈ d39GeomBallEdges B.map B.root r} :=
      ⟨(x.dartEquiv d.1).1,
        (d39DrawingRepresentationData3_ballDarts_iff x r d.1).mp d.2⟩
    have hpair :
        y.dartEquiv
            (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 =
          ((e.edgeEquiv a).1,
            Bool.xor (x.dartEquiv d.1).2 (e.edgeFlip a)) := by
      simp [d39DrawingRepresentationData3_geomBallIso_ballDartEquiv,
        d39GeomBallIsoV2RepresentationDartEquiv,
        d39GeomBallIsoV2DirectedEdgeEquiv, a]
    have hsrc : ¬ B.map.toPlaneMapWithMissing.missing a.1 := by
      simpa [a] using (x.dart_missing d.1).not.mpr hm
    have htgt : ¬ C.map.toPlaneMapWithMissing.missing (e.edgeEquiv a).1 := by
      intro h
      exact hsrc ((e.missing_map a).mp h)
    have hxs : M.core.tail d.1 ↔
        B.map.forward ⟨a.1, hsrc⟩ = (x.dartEquiv d.1).2 := by
      simpa [a] using x.dart_orientation d.1 hm
    have hys : N.core.tail
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 ↔
        C.map.forward ⟨(e.edgeEquiv a).1, htgt⟩ =
          Bool.xor (x.dartEquiv d.1).2 (e.edgeFlip a) := by
      simpa [hpair] using y.dart_orientation
        (d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d).1 hmN
    have horientation := e.orientation_map a hsrc
    rw [hys, hxs, horientation]
    cases hf : e.edgeFlip a <;> simp




















































































end DirectedDistances.PaperProofs.Section5

end
