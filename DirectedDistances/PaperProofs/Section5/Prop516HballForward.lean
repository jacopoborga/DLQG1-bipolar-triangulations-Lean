/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallAssembly4
public import DirectedDistances.PaperProofs.Section5.Prop516GeometricAssembly





public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section5.PLCylinderBall
open scoped ENNReal

/-- Helper toward Proposition 5.16: the Definition 3.8 class distance at a
positive radius is bounded by the dyadic scale exactly when the chosen
geometric representatives have isomorphic rooted geometric balls. -/
theorem d39Class_edist_le_pow_iff_geomBallIso
    {c d : D39GeomRootedMapClass}
    (B C : D39DomainRootedMapV2)
    (hB : PLCylinderBall.geometricClass B = c)
    (hC : PLCylinderBall.geometricClass C = d)
    (r : ℕ) (hr : 0 < r) :
    edist c d ≤ (1 / 2 : ℝ≥0∞) ^ r ↔
      Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root) := by
  rw [← hB, ← hC]
  change edist
      (Quotient.mk d39DomainSetoid (PLCylinderBall.domainMap B))
      (Quotient.mk d39DomainSetoid (PLCylinderBall.domainMap C)) ≤
        (1 / 2 : ℝ≥0∞) ^ r ↔ _
  exact d39ClassDistance_le_pow_iff_nonempty hr
    (PLCylinderBall.domainMap B) (PLCylinderBall.domainMap C)

/-- Helper toward Proposition 5.16: the closed dyadic distance condition
implies equality of the existing candidate faced-ball classes, using
Assembly4 and only the displayed original-face field. -/
theorem b_eq_of_edist_le_pow_of_original_iff
    (horiginal :
      ∀ {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
        (x : D39DrawingRepresentationData3 M B)
        (y : D39DrawingRepresentationData3 N C)
        (r : ℕ) (hr : 0 < r)
        (e : D39GeomBallIsoV2 r B.map B.root C.map C.root),
        ∀ d : {d : M.core.D // d ∈ d39BallDarts M r},
          d39DrawingRepresentationData3_geomBallIso_ballDartEquiv x y e d ∈
              (d39FacedBall N r hr).original ↔
            d ∈ (d39FacedBall M r hr).original)
    (r : ℕ) (x y : PLCylinderBall.X_PL)
    (hxy : edist (x.val : D39GeomRootedMapClass) y.val ≤
      (1 / 2 : ℝ≥0∞) ^ (r + 1)) :
    let hGeomToCombBallIso4 :=
      fun {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
          (x : D39DrawingRepresentationData3 M B)
          (y : D39DrawingRepresentationData3 N C)
          (r : ℕ) (hr : 0 < r)
          (he : Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root)) =>
        he.elim fun e => d39BallIso_of_geomBallIsoV2_of_original_iff
          r hr x y e (horiginal x y r hr e)
    PLCylinderBall.b hGeomToCombBallIso4 r x =
      PLCylinderBall.b hGeomToCombBallIso4 r y := by
  dsimp only
  let hGeomToCombBallIso4 :=
    fun {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
        (x : D39DrawingRepresentationData3 M B)
        (y : D39DrawingRepresentationData3 N C)
        (r : ℕ) (hr : 0 < r)
        (he : Nonempty (D39GeomBallIsoV2 r B.map B.root C.map C.root)) =>
      he.elim fun e => d39BallIso_of_geomBallIsoV2_of_original_iff
        r hr x y e (horiginal x y r hr e)
  obtain ⟨R⟩ := x.property
  obtain ⟨S⟩ := y.property
  have hGeomBallIso :
      Nonempty (D39GeomBallIsoV2 (r + 1) R.geometric.map R.geometric.root
        S.geometric.map S.geometric.root) :=
    (d39Class_edist_le_pow_iff_geomBallIso R.geometric S.geometric
      R.class_eq S.class_eq (r + 1) (Nat.succ_pos r)).mp hxy
  have hBallIso :
      Nonempty (D39BallIso
        (d39FacedBall R.map (r + 1) (Nat.succ_pos r))
        (d39FacedBall S.map (r + 1) (Nat.succ_pos r))) :=
    hGeomToCombBallIso4 R.representation.data S.representation.data
      (r + 1) (Nat.succ_pos r) hGeomBallIso
  rw [PLCylinderBall.b_eq hGeomToCombBallIso4 r x R,
    PLCylinderBall.b_eq hGeomToCombBallIso4 r y S]
  exact (d39BallClass_eq_iff R.map S.map (r + 1) (Nat.succ_pos r)).2 hBallIso






















































end DirectedDistances.PaperProofs.Section5

end
