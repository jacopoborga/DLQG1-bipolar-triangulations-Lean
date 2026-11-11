/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTPeanoStageIdentification
public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitIdentification2
public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect9
public import DirectedDistances.PaperProofs.Section3.D39GeometricClassBorel

/-! # Finite geometric class map toward Proposition 3.9

The drawing and its exterior face exist for every code and stage. No cell
certificate `StageGeom` is used. The chronological root `j` is the manuscript
edge `λ_(j+1)` in the inverse procedure. A fixed choice of drawing gives a
total measurable finite class map, without a default value. Its stage dart
map is identified with every Peano-rooted representative, with geometric
edge identities, ordered endpoints, missing tags and orientations retained.
Independence under changing the drawing and full geometric representation
external kernel validation belong to the sole coordinator. -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5

/-- Helper toward Proposition 3.9: the geometric finite-stage map obtained
from its exterior face, without a `StageGeom` certificate. -/
@[expose] def uibotFiniteClassDrawingMap {w : ℕ → Fin 3} {m : ℕ}
    (P : StageDrawing w m) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d) :
    DirectedPlaneMapWithMissing (Fin (kmswStage w m).nextVertex) P.GeometricEdge :=
  (kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).map

/-- Helper toward Proposition 3.9: geometric missing tags of the exterior
construction agree with the stage tag on each individual dart orbit. -/
theorem uibotFiniteClassDrawingMap_missing_mk {w : ℕ → Fin 3} {m : ℕ}
    (P : StageDrawing w m) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (d : StageDart (kmswStage w m).nextEdge) :
    (uibotFiniteClassDrawingMap P U hU hborder).missing
      (Quotient.mk P.edgeSetoid d) ↔ (kmswStageDirectedMap w m).missing d := by
  change (kmswStageDirectedMap w m).missing (Quotient.mk P.edgeSetoid d).out ↔ _
  rcases P.geometricEdge_out_mk d with ho | ho
  · rw [ho]
  · rw [ho]
    exact ((kmswStageDirectedMap w m).missing_edgeInv d).symm

/-- Helper toward Proposition 3.9: the ordered-dart map used in the Peano
identification is exactly the drawing's dart-to-edge-and-direction equivalence.
Thus it retains all darts of parallel edges, rather than only endpoints. -/
theorem uibotFiniteClassDrawing_orderedDart_eq {w : ℕ → Fin 3} {m : ℕ}
    (P : StageDrawing w m) (d : StageDart (kmswStage w m).nextEdge) :
    uibotStageDrawingOrderedDart P d = kmswStageDrawingDartEdgeDirectionEquiv P d := by
  apply Prod.ext
  · rfl
  · change ((Quotient.mk P.edgeSetoid d).out.2 == d.2) =
      decide (d = (Quotient.mk P.edgeSetoid d).out)
    rcases P.geometricEdge_out_mk d with ho | ho
    · rw [ho]
      simp
    · have hne : d ≠ edgeFlip _ d := by
        intro heq
        have hb := congrArg Prod.snd heq
        cases hbit : d.2 <;> simp [edgeFlip, hbit] at hb
      rw [ho, decide_eq_false_iff_not.mpr hne]
      rcases d with ⟨e, b⟩
      cases b <;> rfl

/-- Helper toward Proposition 3.9: the ordered geometric dart in the
exterior construction has exactly its original stage initial vertex. -/
theorem uibotFiniteClassDrawingMap_orderedDart_initial {w : ℕ → Fin 3} {m : ℕ}
    (P : StageDrawing w m) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (d : StageDart (kmswStage w m).nextEdge) :
    d39GeomRootVertex (uibotFiniteClassDrawingMap P U hU hborder)
      (uibotStageDrawingOrderedDart P d) = stageVertex w m d := by
  change (if (Quotient.mk P.edgeSetoid d).out.2 == d.2
    then stageVertex w m (Quotient.mk P.edgeSetoid d).out
    else stageVertex w m (edgeFlip _ (Quotient.mk P.edgeSetoid d).out)) = _
  rcases P.geometricEdge_out_mk d with ho | ho
  · rw [ho]
    cases d.2 <;> rfl
  · rw [ho]
    rcases d with ⟨e, b⟩
    cases b <;> rfl

/-- Helper toward Proposition 3.9: on every present dart, geometric
orientation in the exterior construction agrees with the stage tail tag. -/
theorem uibotFiniteClassDrawingMap_orderedDart_orientation
    {w : ℕ → Fin 3} {m : ℕ}
    (P : StageDrawing w m) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (d : StageDart (kmswStage w m).nextEdge)
    (hd : ¬ (uibotFiniteClassDrawingMap P U hU hborder).missing
      (uibotStageDrawingOrderedDart P d).1) :
    (kmswStageDirectedMap w m).tail d ↔
      (uibotFiniteClassDrawingMap P U hU hborder).forward
        ⟨(uibotStageDrawingOrderedDart P d).1, hd⟩ =
          (uibotStageDrawingOrderedDart P d).2 := by
  have hm : ¬ (kmswStageDirectedMap w m).missing d :=
    fun h => hd ((uibotFiniteClassDrawingMap_missing_mk P U hU hborder d).mpr h)
  have hp : (kmswStage w m).present d.1.val = true :=
    Bool.eq_true_of_not_eq_false hm
  change ((kmswStage w m).present d.1.val = true ∧ d.2 = false) ↔
    (!(Quotient.mk P.edgeSetoid d).out.2) = ((Quotient.mk P.edgeSetoid d).out.2 == d.2)
  rw [hp]
  cases (Quotient.mk P.edgeSetoid d).out.2 <;> cases d.2 <;> decide

/-- Helper toward Proposition 3.9: every chronological active edge remains
present in the exterior-face geometric map at all later finite stages. -/
theorem uibotFiniteClassDrawingMap_root_present {w : ℕ → Fin 3} {m : ℕ}
    (P : StageDrawing w m) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (j : ℕ) (hj : j ≤ m) :
    ¬ (uibotFiniteClassDrawingMap P U hU hborder).missing
      (uibotFiniteStageGeometricRoot P j hj).1 := by
  rw [show (uibotFiniteStageGeometricRoot P j hj).1 =
    Quotient.mk P.edgeSetoid
      ((⟨act w j, act_lt_nextEdge w hj⟩, false) :
        StageDart (kmswStage w m).nextEdge) from rfl]
  rw [uibotFiniteClassDrawingMap_missing_mk]
  exact (uibotChronologicalRootedStage w m j hj).root_present

/-- Helper toward Proposition 3.9: root the exterior-face drawing at any
earlier chronological edge, retaining the Definition 3.8 geometric domain. -/
@[expose] def uibotFiniteClassDrawingRootedMap {w : ℕ → Fin 3} {m : ℕ}
    (P : StageDrawing w m) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (j : ℕ) (hj : j ≤ m) : D39DomainRootedMap where
  V := Fin (kmswStage w m).nextVertex
  E := P.GeometricEdge
  map := uibotFiniteClassDrawingMap P U hU hborder
  root := uibotFiniteStageGeometricRoot P j hj
  domain := {
    connected := (kmswStageDrawingDomainRootedMapOfExteriorFace P U hU hborder).domain.connected
    locallyFinite := fun _ => Set.toFinite _
    rootValid := Or.inr ⟨uibotFiniteClassDrawingMap_root_present P U hU hborder j hj, rfl⟩ }

/-- Helper toward Proposition 3.9: changing only the certified exterior
face and its proofs leaves the rooted geometric representative unchanged. -/
theorem uibotFiniteClassDrawingRootedMap_eq_of_exterior
    {w : ℕ → Fin 3} {m : ℕ} (P : StageDrawing w m)
    (U U' : P.Face) (hU : P.IsUnbounded U) (hU' : P.IsUnbounded U')
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
    (hborder' : ∀ d, P.dartBorders d U' ↔ (kmswStageDirectedMap w m).IsOuter d)
    (j : ℕ) (hj : j ≤ m) :
    uibotFiniteClassDrawingRootedMap P U hU hborder j hj =
      uibotFiniteClassDrawingRootedMap P U' hU' hborder' j hj := rfl

/-- Helper toward Proposition 3.9: drawing data available at every finite
stage, without the unsatisfiable general `StageGeom` requirement. -/
structure UIBOTFiniteClassDrawingData (w : ℕ → Fin 3) (m : ℕ) where
  drawing : StageDrawing w m
  exterior : drawing.Face
  unbounded : drawing.IsUnbounded exterior
  borders : ∀ d, drawing.dartBorders d exterior ↔ (kmswStageDirectedMap w m).IsOuter d

/-- Helper toward Proposition 3.9: the all-stage exterior theorem supplies
the drawing data for every word and every stage. -/
theorem uibotFiniteClassDrawingData_nonempty (w : ℕ → Fin 3) (m : ℕ) :
    Nonempty (UIBOTFiniteClassDrawingData w m) := by
  obtain ⟨P, U, hU, _, hborder⟩ :=
    kmswStageDrawing_uniqueExteriorFace_borders_iff_isOuter w m
  exact ⟨⟨P, U, hU, hborder⟩⟩

/-- Helper toward Proposition 3.9: choose existing finite-stage exterior
data. Drawing-choice independence remains the separate obligation below. -/
@[expose] def uibotFiniteClassDrawingChoice (w : ℕ → Fin 3) (m : ℕ) :
    UIBOTFiniteClassDrawingData w m :=
  Classical.choice (uibotFiniteClassDrawingData_nonempty w m)

/-- Helper toward Proposition 3.9: the geometric representative obtained
from the inverse procedure code of `q`, rooted at chronological index `j`. -/
@[expose] def uibotFiniteGeometricClassRepresentative (ℓ ρ n : ℕ)
    (_hℓ : 0 < ℓ) (_hρ : 0 < ρ) (hn : 1 ≤ n)
    (_hne : Nonempty (KMSWMapIsoClass ℓ ρ n))
    (p : KMSWMapIsoClass ℓ ρ n × Fin n) : D39DomainRootedMap :=
  let c := (kmswProcedureEquiv ℓ ρ n hn).symm p.1
  let D := uibotFiniteClassDrawingChoice (codeExtend c) (n - 1)
  uibotFiniteClassDrawingRootedMap D.drawing D.exterior D.unbounded D.borders
    p.2.val (by have := p.2.isLt; omega)

/-- Helper toward Proposition 3.9: a total finite geometric class map,
using actual stage drawings and no default value or `StageGeom` premise. -/
@[expose] def uibotFiniteGeometricClassMap (ℓ ρ n : ℕ)
    (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) :
    KMSWMapIsoClass ℓ ρ n × Fin n → D39GeomRootedMapClass :=
  fun p => Quotient.mk d39DomainSetoid
    (uibotFiniteGeometricClassRepresentative ℓ ρ n hℓ hρ hn hne p)

/-- Helper toward Proposition 3.9: the chosen finite geometric
representative belongs to the class returned by the finite map. -/
theorem uibotFiniteGeometricClassMap_represents (ℓ ρ n : ℕ)
    (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n))
    (p : KMSWMapIsoClass ℓ ρ n × Fin n) :
    uibotFiniteGeometricClassRepresentative ℓ ρ n hℓ hρ hn hne p ∈
      d39DomainRootedMapClassMembers (uibotFiniteGeometricClassMap ℓ ρ n hℓ hρ hn hne p) :=
  rfl

/-- Helper toward Proposition 3.9: the finite class map is measurable from
the top sigma-algebra to the Borel structure of the geometric class space. -/
theorem measurable_uibotFiniteGeometricClassMap (ℓ ρ n : ℕ)
    (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n)) :
    @Measurable _ _ ⊤ (borel D39GeomRootedMapClass)
      (uibotFiniteGeometricClassMap ℓ ρ n hℓ hρ hn hne) := by
  let : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  exact measurable_from_top

/-- Helper toward Proposition 3.9: for every representative of a class,
the rooted stage dart map underlying the chosen drawing is isomorphic to
its Peano rooting, at the same chronological index with no shift. -/
@[expose] def uibotFiniteGeometricClassPeanoIso {ℓ ρ n : ℕ} (hn : 1 ≤ n)
    (q : KMSWMapIsoClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = q) (j : Fin n) :
    RootedDirectedMapIso (uibotPeanoRootedAt R j)
      (uibotChronologicalRootedStage
        (codeExtend ((kmswProcedureEquiv ℓ ρ n hn).symm q)) (n - 1) j.val
          (by have := j.isLt; omega)) :=
  uibotPeanoChronologicalRootedIso hn _ R
    (hR.trans ((kmswProcedureEquiv ℓ ρ n hn).apply_symm_apply q).symm) j

/-- Helper toward Proposition 3.9: the Peano isomorphism identifies the
root and every dart's geometric missing tag, initial vertex and orientation
in the exact representative defining the finite geometric class map. -/
theorem uibotFiniteGeometricClassMap_peano_identification
    {ℓ ρ n : ℕ} (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hne : Nonempty (KMSWMapIsoClass ℓ ρ n))
    (q : KMSWMapIsoClass ℓ ρ n) (R : KMSWMapRep ℓ ρ n)
    (hR : KMSWMapIsoClass.mk R = q) (j : Fin n) :
    let c := (kmswProcedureEquiv ℓ ρ n hn).symm q
    let D := uibotFiniteClassDrawingChoice (codeExtend c) (n - 1)
    let B := uibotFiniteGeometricClassRepresentative ℓ ρ n hℓ hρ hn hne (q, j)
    let I := uibotFiniteGeometricClassPeanoIso hn q R hR j
    uibotStageDrawingOrderedDart D.drawing (I.dartEquiv (uibotPeanoRootedAt R j).root) =
        B.root ∧
      ∀ d : Fin R.dartCount,
        (B.map.missing (uibotStageDrawingOrderedDart D.drawing (I.dartEquiv d)).1 ↔
          R.B.map.missing d) ∧
        d39GeomRootVertex B.map (uibotStageDrawingOrderedDart D.drawing (I.dartEquiv d)) =
          stageVertex (codeExtend c) (n - 1) (I.dartEquiv d) ∧
        ∀ hd : ¬ B.map.missing (uibotStageDrawingOrderedDart D.drawing (I.dartEquiv d)).1,
          R.B.map.tail d ↔ B.map.forward
            ⟨(uibotStageDrawingOrderedDart D.drawing (I.dartEquiv d)).1, hd⟩ =
              (uibotStageDrawingOrderedDart D.drawing (I.dartEquiv d)).2 := by
  dsimp only
  let c := (kmswProcedureEquiv ℓ ρ n hn).symm q
  let D := uibotFiniteClassDrawingChoice (codeExtend c) (n - 1)
  let I := uibotFiniteGeometricClassPeanoIso hn q R hR j
  refine ⟨?_, ?_⟩
  · rw [I.root_comm]
    let d : StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge :=
      (⟨act (codeExtend c) j.val, act_lt_nextEdge _ (by have := j.isLt; omega)⟩, false)
    let e := Quotient.mk D.drawing.edgeSetoid d
    change (e, e.out.2 == false) = (e, !e.out.2)
    cases e.out.2 <;> rfl
  · intro d
    refine ⟨?_, uibotFiniteClassDrawingMap_orderedDart_initial
      D.drawing D.exterior D.unbounded D.borders _, ?_⟩
    · exact (uibotFiniteClassDrawingMap_missing_mk
        D.drawing D.exterior D.unbounded D.borders (I.dartEquiv d)).trans
          (I.missing_iff d).symm
    · intro hd
      exact (I.tail_iff d).trans (uibotFiniteClassDrawingMap_orderedDart_orientation
        D.drawing D.exterior D.unbounded D.borders (I.dartEquiv d) hd)

/- OPEN DRAWING INDEPENDENCE (C), with full binders.

∀ (w : ℕ → Fin 3) (m j : ℕ) (hj : j ≤ m)
  (P P' : StageDrawing w m)
  (U : P.Face) (U' : P'.Face)
  (hU : P.IsUnbounded U) (hU' : P'.IsUnbounded U')
  (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w m).IsOuter d)
  (hborder' : ∀ d, P'.dartBorders d U' ↔ (kmswStageDirectedMap w m).IsOuter d),
  let B := uibotFiniteClassDrawingRootedMap P U hU hborder j hj
  let B' := uibotFiniteClassDrawingRootedMap P' U' hU' hborder' j hj
  Nonempty (D39GeomRootedMapIsoV2 B.map B.root B'.map B'.root).

By Quotient.sound this would identify the two geometric classes. The
isomorphism must supply an orientation-preserving ambient homeomorphism,
vertex and individual-edge equivalences, monotone/antitone edge
reparameterizations, endpoint compatibility, missing tags, orientations and
the ordered root. The common stage rotation and the Peano isomorphism do not
construct that ambient homeomorphism. This is not assumed by any declaration
above. Independence of U, hU and hborder for a fixed P IS proved above.

The finite map is measurable and total for the fixed choice of drawing. Its
proved representative identification is the RootedDirectedMapIso together
with its geometric dart data, not an assertion that arbitrary drawings of a
combinatorial map define the same geometric class. The complete Data3
representation with its topological rotation and frontier fields is not
claimed here.

OPEN WHOLE-PLANE CLASS MAP AND CONVERGENCE, with full binders.

Use the existing product measurable structure on ℤ → Fin 3 and
MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass.
Construct F satisfying the following joint statement, using the SAME
H, h0, hpast and hp inside its map, root and domain witness:

∃ F : (ℤ → Fin 3) → D39GeomRootedMapClass,
  Measurable F ∧
  (∀ᵐ W ∂DirectedDistances.RandomWalk.wholePlaneIIDCodeMeasure,
    ∃ (H : WholePlaneRotationHypothesis W)
      (h0 : BoundaryHitWitnesses (shiftedStream W 0))
      (hpast : BoundaryHitWitnesses (kmswPastCode W))
      (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
      ∃ hdom : D39GeomDomain (uibotWholePlaneGeometricMap W H G hp)
          (uibotWholePlaneGeometricRoot W H G),
        F W = Quotient.mk d39DomainSetoid
          ({ V := WholePlaneVertex W, E := G.GeometricEdge,
             map := uibotWholePlaneGeometricMap W H G hp,
             root := uibotWholePlaneGeometricRoot W H G,
             domain := hdom } : D39DomainRootedMap)) ∧
  (∀ (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Filter.Tendsto ns Filter.atTop Filter.atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))
    (r : ℕ) (b : Quotient (d39GeomBallClassSetoid r)),
    Filter.Tendsto (fun k =>
      (uibotFiniteUniformSampleLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k))
        {p | d39GeomBallClassMap r
          (uibotFiniteGeometricClassMap ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) p) = b})
      Filter.atTop (nhds (DirectedDistances.RandomWalk.wholePlaneIIDCodeMeasure
        {W | d39GeomBallClassMap r (F W) = b}))).

For each k the finite law uses MeasurableSpace (KMSWMapIsoClass ℓ ρ (ns k)) := ⊤
and MeasurableSpace (Fin (ns k)) := ⊤, as in its definition. The ball-class
index r represents geometric radius r+1. Existence of the glued geometric
domain almost surely does not prove measurability of F; finite-window law
convergence does not provide the ambient geometric ball isomorphism or the
retained-face transport. No default F, extra recurrence, representation,
StageGeom or geometric-isomorphism premise is introduced. Proposition 3.9
and whole-paper completion are not claimed. -/

end DirectedDistances.PaperProofs.Section3

end
