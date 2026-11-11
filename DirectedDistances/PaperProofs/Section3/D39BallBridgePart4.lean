/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39BallBridgePart3
public import DirectedDistances.PaperProofs.Section3.D39BallBridgePart2








public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.D39BallBridge

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section5
open Set unitInterval
open scoped ENNReal

local instance d39BallBridgePart4DecidableDarts (M : D39RootedMap) (r : ℕ) :
    DecidableEq {d : M.core.D // d ∈ d39BallDarts M r} := Classical.decEq _

section Pair

variable {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
  (x : D39DrawingRepresentationData3 M B) (y : D39DrawingRepresentationData3 N C)
  (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
    M.core.edgeInv M.core.rot (d39VertexClass M))
  (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
    N.core.edgeInv N.core.rot (d39VertexClass N))
  (ha : ∀ d, ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
    ∀ t, d39DrawingDartArc B x.toD39DrawingRepresentationData d t =
      (P.arc d).toPath (φ t))
  (hb : ∀ d, ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
    ∀ t, d39DrawingDartArc C y.toD39DrawingRepresentationData d t =
      (Q.arc d).toPath (φ t))

/-- Helper toward Definition 3.8 consumers: construct the exterior-marked
combinatorial isomorphism induced by a geometric ball isomorphism, allowing
endpoint-preserving path reparameterizations in both representations. -/
@[expose] def reparam_markedIsoOfGeom (r : ℕ) (hr : 0 < r)
    (e : D39GeomBallIsoV2 r B.map B.root C.map C.root) :
    D39BallIsoWithExternal (d39FacedBallPLWithExternal M P r hr)
      (d39FacedBallPLWithExternal N Q r hr) where
  toD39BallIso := {
    toEquiv := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e
    rot_comm := d39DrawingRepresentationData3_geomBallIso_rotation_comm hr x y e
    edgeInv_comm := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_edgeInv x y e
    missing_iff := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_missing_iff x y e
    tail_iff := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_tail_iff x y e
    root_comm := d39DrawingRepresentationData3_geomBallIso_ballDartEquiv_root x y e
    original_iff := reparam_original_iff x y P Q ha hb e }
  external_iff := reparam_external_iff x y P Q ha hb r hr e

include ha hb in
/-- Helper toward Definition 3.8 consumers: the full geometric isomorphism
is equivalent to an exterior-marked combinatorial faced-ball isomorphism
on the endpoint-reparameterized representation carrier. -/
theorem reparam_geomIso_iff_markedIso (r : ℕ) (hr : 0 < r) :
    Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) ↔
      Nonempty (D39BallIsoWithExternal (d39FacedBallPLWithExternal M P r hr)
        (d39FacedBallPLWithExternal N Q r hr)) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨reparam_markedIsoOfGeom x y P Q ha hb r hr e⟩
  · rintro ⟨J⟩
    exact exteriorMarkedComparison_reparam_geomBallIso x y P Q
      (ExteriorMarkedComparison2.pos_eq_of_reparam x.toD39DrawingRepresentationData P ha)
      (ExteriorMarkedComparison2.pos_eq_of_reparam y.toD39DrawingRepresentationData Q hb)
      ha hb r hr (Quotient.sound ⟨J⟩)

include ha hb in
/-- Helper toward Definition 3.8 consumers: geometric isomorphism is
exactly equality in the exterior-marked faced-ball quotient. -/
theorem reparam_geomIso_iff_markedClass_eq (r : ℕ) (hr : 0 < r) :
    Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) ↔
      Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal M P r hr) =
        Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal N Q r hr) :=
  (reparam_geomIso_iff_markedIso x y P Q ha hb r hr).trans
    ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

include ha hb in
/-- Helper toward Definition 3.8 consumers: the installed class distance
has the exact exterior-marked dyadic ball characterization for representations
whose geometric paths agree with PL paths up to endpoint reparameterization. -/
theorem reparam_edist_le_iff_markedClass_eq (r : ℕ) (hr : 0 < r) :
    edist (PLCylinderBall.geometricClass B) (PLCylinderBall.geometricClass C) ≤
        (1 / 2 : ℝ≥0∞) ^ r ↔
      Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal M P r hr) =
        Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal N Q r hr) :=
  (d39ClassDistance_le_pow_iff_nonempty hr
    (PLCylinderBall.domainMap B) (PLCylinderBall.domainMap C)).trans
      (reparam_geomIso_iff_markedClass_eq x y P Q ha hb r hr)

include ha hb in
/-- Helper toward Definition 3.8 consumers: the exterior-marked observation
is independent of reparameterized representation within one geometric class. -/
theorem reparam_markedClass_eq_of_class_eq
    (hclass : PLCylinderBall.geometricClass B = PLCylinderBall.geometricClass C)
    (r : ℕ) (hr : 0 < r) :
    Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal M P r hr) =
      Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal N Q r hr) := by
  apply (reparam_edist_le_iff_markedClass_eq x y P Q ha hb r hr).mp
  rw [hclass, edist_self]
  exact bot_le

include ha hb in
/-- Helper toward Definition 3.8 consumers: agreement of the actual marked
balls at a larger positive radius implies agreement at any smaller positive radius. -/
theorem reparam_markedClass_restrict {s r : ℕ} (hs : 0 < s) (hsr : s ≤ r)
    (h : Quotient.mk exteriorMarkedBallSetoid
        (d39FacedBallPLWithExternal M P r (hs.trans_le hsr)) =
      Quotient.mk exteriorMarkedBallSetoid
        (d39FacedBallPLWithExternal N Q r (hs.trans_le hsr))) :
    Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal M P s hs) =
      Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal N Q s hs) := by
  obtain ⟨e⟩ := (reparam_geomIso_iff_markedClass_eq x y P Q ha hb
    r (hs.trans_le hsr)).mpr h
  exact (reparam_geomIso_iff_markedClass_eq x y P Q ha hb s hs).mp
    ⟨e.restrict hs hsr⟩

end Pair

/-- Helper toward Definition 3.8 consumers: the existing class observation
also has its complete characterization against any endpoint-reparameterized
PL representation of that class, without literal path equality. -/
theorem ballClass_eq_reparam (r : ℕ) (c : PLCylinderBall.X_PL)
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (ha : ∀ d, ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc B x.toD39DrawingRepresentationData d t =
        (P.arc d).toPath (φ t))
    (hc : PLCylinderBall.geometricClass B = c.val) :
    ballClass r c = Quotient.mk exteriorMarkedBallSetoid
      (d39FacedBallPLWithExternal M P (r + 1) (Nat.succ_pos r)) := by
  obtain ⟨R⟩ := c.property
  rw [ballClass_eq r c R]
  apply reparam_markedClass_eq_of_class_eq
    R.representation.data x R.representation.drawing P _ ha
    (R.class_eq.trans hc.symm) (r + 1) (Nat.succ_pos r)
  intro d
  exact ⟨Homeomorph.refl I, rfl, rfl, fun t => (R.representation.arc_eq d t).symm⟩
































end DirectedDistances.PaperProofs.Section3.D39BallBridge

end
