/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTQualifierTransport
public import DirectedDistances.PaperProofs.Section3.UIBOTConsumerFactorization
public import DirectedDistances.PaperProofs.Section3.UIBOTConsumerDetermination
public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization21
public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitFinal
public import DirectedDistances.KMSW.M0CutData
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Root realization and boundary identifications toward Proposition 3.9


The optional code observable below is the glued ambient geometric map rooted
at the cut root. Its absent value records failure of the actual geometric
realization domain, and has probability zero. Its Borel factor is `some`.
This identifies the full ambient root, including the ordered endpoints
labelled 0 and 1; it does not assert Borel recovery of the cut or its other
boundary marks. The simultaneous boundary and inclusion identities below
use the same geometric realization witnesses. Remaining descent obligations
belong to the coordinator. No counted consumer is closed here. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5
open MeasureTheory Filter Set
open scoped Topology

local instance uibotCutDescentMeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}

local instance uibotCutDescentBorelSpace : BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

-- A set of optional classes is measurable exactly when its `some` preimage
-- is Borel; membership of the isolated absent value is unrestricted.
local instance uibotCutDescentOptionMeasurableSpace :
    MeasurableSpace (Option D39GeomRootedMapClass.{0}) :=
  MeasurableSpace.map some (borel D39GeomRootedMapClass.{0})

local instance uibotCutDescentBoundaryOptionMeasurableSpace :
    MeasurableSpace (Option ((ℤ → ℕ) × (ℤ → ℕ))) :=
  MeasurableSpace.map some inferInstance

/-- Helper toward Proposition 3.9: the glued ambient map rooted at the
cut's geometric root dart. This retains individual edges and the endpoint
storage correction, rather than replacing the root by an adjacent pair. -/
@[expose] def uibotCutRootClass
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (hdom : D39GeomDomain
      (uibotWholePlaneGeometricMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)
      (uibotWholePlaneGeometricRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H))) :
    D39GeomRootedMapClass.{0} :=
  Quotient.mk d39DomainSetoid
    ({ V := WholePlaneVertex W,
       E := (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H).GeometricEdge,
       map := uibotWholePlaneGeometricMap W H
         (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp,
       root := uibotWholePlaneGeometricRoot W H
         (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H),
       domain := hdom } : D39DomainRootedMap)

/-- Helper toward Proposition 3.9: an optional code-domain ambient root
observable, defined from the actual glued drawing and geometric-domain
witnesses. No inverse coding or value of the measurable class map occurs
in its definition. -/
@[expose] def uibotCutRootClassOption (W : ℤ → Fin 3) :
    Option D39GeomRootedMapClass.{0} := by
  classical
  exact if hgood : ∃ (H : WholePlaneRotationHypothesis W)
      (h0 : BoundaryHitWitnesses (shiftedStream W 0))
      (hpast : BoundaryHitWitnesses (kmswPastCode W))
      (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      D39GeomDomain
        (uibotWholePlaneGeometricMap W H
          (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)
        (uibotWholePlaneGeometricRoot W H
          (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H)) then
    some (uibotCutRootClass W hgood.choose hgood.choose_spec.choose
      hgood.choose_spec.choose_spec.choose
      hgood.choose_spec.choose_spec.choose_spec.choose
      hgood.choose_spec.choose_spec.choose_spec.choose_spec)
  else none

/-- Helper toward Proposition 3.9: every valid realization computes the
same optional root observable. All realization arguments are proofs, so
this equality requires no isomorphism or recovery assumption. -/
theorem uibotCutRootClassOption_eq_some
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (hdom : D39GeomDomain
      (uibotWholePlaneGeometricMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)
      (uibotWholePlaneGeometricRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H))) :
    uibotCutRootClassOption W = some (uibotCutRootClass W H h0 hpast hp hdom) := by
  classical
  unfold uibotCutRootClassOption
  rw [dite_eq_left ⟨H, h0, hpast, hp, hdom⟩]

/-- Helper toward Proposition 3.9: the actual code-domain root observable
has the explicit Borel factor `some` through the proved measurable class
map, on one almost-sure event. -/
theorem uibotCutRootClassOption_ae_factor :
    uibotCutRootClassOption =ᵐ[wholePlaneIIDCodeMeasure]
      (some : D39GeomRootedMapClass.{0} → Option D39GeomRootedMapClass.{0}) ∘
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved := by
  filter_upwards [uibotMeasurableWholePlaneClassMap_ae_represents_proved] with W hW
  obtain ⟨H, h0, hpast, hp, hdom, hrep⟩ := hW
  change uibotCutRootClassOption W = some
    (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W)
  rw [uibotCutRootClassOption_eq_some W H h0 hpast hp hdom]
  exact congrArg some hrep.symm

/-- Helper toward Proposition 3.9: the root factor is Borel measurable;
this is a factor of the full rooted ambient class, not code recovery. -/
theorem measurable_uibotCutRootFactor :
    Measurable (some : D39GeomRootedMapClass.{0} → Option D39GeomRootedMapClass.{0}) := by
  intro s hs
  exact hs




theorem exists_measurable_uibotCutRootClassOption_factor :
    ∃ Phi : D39GeomRootedMapClass.{0} → Option D39GeomRootedMapClass.{0},
      Measurable Phi ∧ uibotCutRootClassOption =ᵐ[wholePlaneIIDCodeMeasure]
        Phi ∘ uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved :=
  ⟨some, measurable_uibotCutRootFactor, uibotCutRootClassOption_ae_factor⟩

/-- Helper toward Proposition 3.9: both ordered geometric root endpoints
are exactly the cut labels 0 and 1, with the same edge identity as the cut
root, for every realization and every cut datum on that realization. -/
theorem uibotCutRoot_endpoints
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (D : M0CutData W H) :
    let M := uibotWholePlaneGeometricMap W H G hp
    let rho := uibotWholePlaneGeometricRoot W H G
    rho.1 = Quotient.mk G.edgeSetoid D.rootDart ∧
      d39GeomRootVertex M rho = D.x 0 ∧
      d39GeomRootOtherVertex M rho = D.x 1 := by
  dsimp only
  refine ⟨rfl, uibotWholePlaneGeometricRoot_initial W H G hp, ?_⟩
  let e := Quotient.mk G.edgeSetoid (wholePlaneEdgeι W 0 0, false)
  change (if !e.out.2 then wholePlaneDartVertex W (wholePlaneDartFlip W e.out)
    else wholePlaneDartVertex W e.out) = wholePlaneEdgeEast W (wholePlaneEdgeι W 0 0)
  rcases G.geometricEdge_out_mk (wholePlaneEdgeι W 0 0, false) with h | h
  · change e.out = _ at h
    rw [h]
    rfl
  · change e.out = _ at h
    rw [h]
    rfl

/-- Helper toward Proposition 3.9: simultaneous intrinsic boundary labels
and the actual run inclusions, for any cut datum and one common hit/presence
witness. Both extremal rays are indexed in the source's directed order. -/
theorem uibotCut_boundary_identifications
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (D : M0CutData W H) :
    (∀ (k : ℤ) (v : WholePlaneVertex W),
      m0CutBoundaryLabel W H k v ↔ v = D.x k) ∧
    (∀ k : ℤ, D.x k = wholePlaneVertexι W 0
      (boundaryVertex (shiftedStream W 0) h k)) ∧
    (∀ n : ℕ, D.betaR.vertex n = D.x ((n : ℤ) + 1)) ∧
    (∀ n : ℕ, D.betaL.vertex n = D.x (-(n : ℤ))) ∧
    D.edges = Set.range (wholePlaneEdgeι W 0) ∧
    D.darts = Set.range (wholePlaneDartι W 0) := by
  refine ⟨?_, D.x_eq h hLL, ?_, ?_, D.edges_eq h hLL, D.darts_eq h hLL⟩
  · intro k v
    rw [m0Cut_boundaryLabel_iff W H h hLL, D.x_eq h hLL]
  · intro n
    rw [m0Cut_betaR_vertices W H h D.betaR D.betaR_start, D.x_eq h hLL]
  · intro n
    rw [m0Cut_betaL_vertices W H h hLL D.betaL, D.x_eq h hLL]

/-- Helper toward Proposition 3.9: the common code-labelled boundary
observable consists of all vertex IDs and all geometric boundary edge IDs,
using one hit witness. The negative edge IDs include missing edges. Its
Borel descent is an open obligation, recorded below, not a hypothesis. -/
@[expose] def uibotCutBoundaryCodeOption (W : ℤ → Fin 3) :
    Option ((ℤ → ℕ) × (ℤ → ℕ)) := by
  classical
  exact if h : BoundaryHitWitnesses (shiftedStream W 0) then
    some (boundaryVertex (shiftedStream W 0) h,
      boundaryOuterEdge (shiftedStream W 0) h)
  else none

/-- Helper toward Proposition 3.9: the boundary observable is exactly
the joint full vertex/edge enumeration for every valid hit witness. -/
theorem uibotCutBoundaryCodeOption_eq_some (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) :
    uibotCutBoundaryCodeOption W = some
      (boundaryVertex (shiftedStream W 0) h, boundaryOuterEdge (shiftedStream W 0) h) := by
  classical
  unfold uibotCutBoundaryCodeOption
  rw [dite_eq_left h]

/-- Helper toward Proposition 3.9: under the actual run inclusions, the
joint boundary observable gives precisely the full cut vertex sequence and
geometric boundary edges. This is simultaneous equality of both sequences,
rather than separate almost-sure equalities of individual coordinates. -/
theorem uibotCutBoundaryCodeOption_map_inclusions
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (D : M0CutData W H) :
    (uibotCutBoundaryCodeOption W).map
      (fun p => ((fun k => wholePlaneVertexι W 0 (p.1 k)),
        fun k => wholePlaneEdgeι W 0 (p.2 k))) =
      some (D.x, fun k => wholePlaneEdgeι W 0
        (boundaryOuterEdge (shiftedStream W 0) h k)) := by
  rw [uibotCutBoundaryCodeOption_eq_some W h]
  exact congrArg (fun f => some (f, fun k => wholePlaneEdgeι W 0
    (boundaryOuterEdge (shiftedStream W 0) h k)))
      (funext fun k => (D.x_eq h hLL k).symm)

/-- Helper toward Proposition 3.9: the entire geometric boundary edge
enumeration agrees with the two extremal rays and the actual cut root.
The left-ray index is negative and those edges retain their identities. -/
theorem uibotCut_boundary_edge_identifications
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (D : M0CutData W H) :
    (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h 0) = D.rootDart.1) ∧
    (∀ n : ℕ, wholePlaneEdgeι W 0
      (boundaryOuterEdge (shiftedStream W 0) h ((n : ℤ) + 1)) = D.betaR.edge n) ∧
    (∀ n : ℕ, wholePlaneEdgeι W 0
      (boundaryOuterEdge (shiftedStream W 0) h (-(n : ℤ) - 1)) = D.betaL.edge n) ∧
    (∀ k : ℤ, wholePlaneEdgeWest W (wholePlaneEdgeι W 0
      (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x k ∧
      wholePlaneEdgeEast W (wholePlaneEdgeι W 0
        (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x (k + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [boundaryOuterEdge_zero]
    rfl
  · intro n
    rw [boundaryOuterEdge_of_positive _ _ (by omega),
      m0Cut_betaR_edges W H h D.betaR D.betaR_start]
    congr 2
  · intro n
    rw [boundaryOuterEdge_of_negative _ _ (by omega),
      m0Cut_betaL_edges W H h hLL D.betaL]
  · intro k
    exact (m0Cut_boundaryLabel_consecutive W H h hLL k
      (D.x_label k) (D.x_label (k + 1))).2

/-- Helper toward Proposition 3.9: a single probability-one event supplies
the geometric representative, cut root, both ordered root endpoint labels,
all integer boundary labels, both ray enumerations and the cut edge/dart
inclusions, with shared witnesses throughout. These identities do not yet
assert a Borel factor for the entire marked cut. -/
theorem uibotCut_ae_shared_root_boundary :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
        (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h0 (k - 1)))))
        (hdom : D39GeomDomain
          (uibotWholePlaneGeometricMap W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)
          (uibotWholePlaneGeometricRoot W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H))),
        let D := m0CutData W H h0 hLL
        let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
        let M := uibotWholePlaneGeometricMap W H G hp
        let rho := uibotWholePlaneGeometricRoot W H G
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W =
          uibotCutRootClass W H h0 hpast hp hdom ∧
        (rho.1 = Quotient.mk G.edgeSetoid D.rootDart ∧
          d39GeomRootVertex M rho = D.x 0 ∧
          d39GeomRootOtherVertex M rho = D.x 1) ∧
        (∀ (k : ℤ) (v : WholePlaneVertex W),
          m0CutBoundaryLabel W H k v ↔ v = D.x k) ∧
        (∀ k : ℤ, D.x k = wholePlaneVertexι W 0
          (boundaryVertex (shiftedStream W 0) h0 k)) ∧
        (∀ n : ℕ, D.betaR.vertex n = D.x ((n : ℤ) + 1)) ∧
        (∀ n : ℕ, D.betaL.vertex n = D.x (-(n : ℤ))) ∧
        D.edges = Set.range (wholePlaneEdgeι W 0) ∧
        D.darts = Set.range (wholePlaneDartι W 0) := by
  filter_upwards [uibotMeasurableWholePlaneClassMap_ae_represents_proved] with W hW
  obtain ⟨H, h0, hpast, hp, hdom, hrep⟩ := hW
  let hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h0 (k - 1)))) := fun _ _ => hp _
  refine ⟨H, h0, hpast, hp, hLL, hdom, hrep, ?_, ?_⟩
  · exact uibotCutRoot_endpoints W H
      (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp (m0CutData W H h0 hLL)
  · exact uibotCut_boundary_identifications W H h0 hLL (m0CutData W H h0 hLL)

/- EXACT REMAINING BOUNDARY DESCENT (a sufficient code-labelled route).
With F := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved,
the following statement is OPEN; it is neither a premise nor a declaration:

  ∃ Phi : D39GeomRootedMapClass.{0} → Option ((ℤ → ℕ) × (ℤ → ℕ)),
    Measurable Phi ∧
      uibotCutBoundaryCodeOption =ᵐ[wholePlaneIIDCodeMeasure] Phi ∘ F

The optional target uses `MeasurableSpace.map some inferInstance`, where the
pair of integer-indexed natural sequences has its product measurable space.
The characterization `uibotCutBoundaryCodeOption_map_inclusions` and the
boundary-edge theorem above identify exactly the labels and both ray edge
sequences this would recover. This sufficient route retains run IDs; an
intrinsic marked-geometric quotient can avoid that extra enumeration.

Even such labelled recovery does not by itself prove geometric descent of
the cut's inclusions, seam, missing tags, inverse rotation or retained faces.
One exact remaining geometric invariance statement for these marks is:

  ∀ (W W' : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis W')
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (h' : BoundaryHitWitnesses (shiftedStream W' 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hpast' : BoundaryHitWitnesses (kmswPastCode W'))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (hp' : ∀ e : WholePlaneEdge W', wholePlaneEdgePresent W' e)
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (hLL' : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W'
      (wholePlaneEdgeι W' 0 (kmswLLCreatedEdge (shiftedStream W' 0)
        (boundaryHitTime (shiftedStream W' 0) h' (k - 1))))),
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let G' := WholePlanePastGlueDrawing.glueDrawing W' h' hpast' H'
    let D := m0CutData W H h hLL
    let D' := m0CutData W' H' h' hLL'
    ∀ e : D39GeomRootedMapIsoV2
      (uibotWholePlaneGeometricMap W H G hp) (uibotWholePlaneGeometricRoot W H G)
      (uibotWholePlaneGeometricMap W' H' G' hp') (uibotWholePlaneGeometricRoot W' H' G'),
      (∀ k : ℤ, e.vertexEquiv (D.x k) = D'.x k) ∧
      (∀ n : ℕ, e.edgeEquiv (Quotient.mk G.edgeSetoid (D.betaR.edge n, false)) =
        Quotient.mk G'.edgeSetoid (D'.betaR.edge n, false)) ∧
      (∀ n : ℕ, e.edgeEquiv (Quotient.mk G.edgeSetoid (D.betaL.edge n, false)) =
        Quotient.mk G'.edgeSetoid (D'.betaL.edge n, false)) ∧
      (∀ v : WholePlaneVertex W,
        v ∈ m0CutLeftVertices W H D.seam ↔
          e.vertexEquiv v ∈ m0CutLeftVertices W' H' D'.seam) ∧
      (∀ (a : WholePlaneEdge W) (a' : WholePlaneEdge W'),
        e.edgeEquiv (Quotient.mk G.edgeSetoid (a, false)) =
          Quotient.mk G'.edgeSetoid (a', false) →
        (a ∈ D.edges ↔ a' ∈ D'.edges) ∧
        (D.seam a ↔ D'.seam a') ∧ (D.missing a ↔ D'.missing a'))

it does not assert Borel measurability or transport of every cut predicate.
The supplied a.e. representation and the forward code-to-ball comparison
alone supply neither this geometric mark transport nor Borel determination
of the marked cut. No code recovery is assumed. No attribution qualifier, -/

end DirectedDistances.PaperProofs.Section3

end
