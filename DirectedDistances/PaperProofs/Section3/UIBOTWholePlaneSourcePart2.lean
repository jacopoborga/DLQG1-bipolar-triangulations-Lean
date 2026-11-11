/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTWholePlaneSourcePart1
public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization21
public import DirectedDistances.KMSW.UIBHBOTAssemblyFaceNeighborhood
public import DirectedDistances.PlanarMap.FaceDegreeFiniteSupport
import all DirectedDistances.KMSW.KMSWWindowInfiniteMaps

/- # Triangular whole-plane realization and its local-limit law

The deterministic results use the same full witness scope as the almost-sure
realization. No recurrence or triangle premise is added to the iid statements.
The conditional source-law transport isolates the finite-carrier law identification;
its proof, and identification of the source topology, are separate obligations. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5
open MeasureTheory Filter
open scoped Topology ENNReal

local instance uibotWholePlaneSourcePart2MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotWholePlaneSourcePart2BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: each whole-plane dart belongs to a
triangle created in a one-sided run, including darts coming from the past. -/
theorem uibotWholePlane_dart_in_triangle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W)) (D : WholePlaneDart W) :
    ∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)) (d : ℕ × Bool),
      d ∈ stageTriangleDartList (shiftedStream W N) j ∧ wholePlaneDartι W N d = D := by
  rcases wholePlaneFaceSucc_runZero_or_past W H
    (WholePlanePastGlueData.past_finiteIncidence W H) hpast h0 D with
    ⟨d, rfl, ⟨j, hd⟩, _⟩ | ⟨d, rfl, ⟨j, hd⟩, _⟩
  · exact ⟨0, j, d, hd, rfl⟩
  · let N := j.val + 1
    have hjN : j.val < N := Nat.lt_succ_self _
    have hb := stageTriangleDartList_lt (kmswPastCode W) N j hjN d hd
    let x : StageDart (kmswStage (kmswPastCode W) N).nextEdge := (⟨d.1, hb⟩, d.2)
    let y := kmswRevDart (shiftedStream W N) (kmswPastCode W) N
      (kmswPastCode_rev W N) x
    obtain ⟨k, _, hword⟩ := kmswRevDart_triangle_words (shiftedStream W N)
      (kmswPastCode W) N (kmswPastCode_rev W N) j hjN
    refine ⟨N, k, reversalDartVal y, ?_, (kmswPastDart_eq_stage W N d hb).symm⟩
    exact hword.mem_iff.mp (List.mem_map.mpr ⟨d, hd, rfl⟩)

/-- Helper toward Proposition 3.9: every original geometric glued face,
without a ball-retention restriction, is a created triangle face. -/
theorem uibotWholePlane_glued_face_triangle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H).toPlaneGraphDrawing.Face) :
    ∃ (N : ℕ) (j : TriangleCreationTime (shiftedStream W N)),
      F = uibotGluedWindowTriangleFace W H h0 hpast N j := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
  let F' := G.toPlaneGraphDrawingFaceEquiv F
  obtain ⟨D, hD⟩ := WholePlaneGlueFaceCorrespondenceFull.face_bordered W h0 hpast H F'
  obtain ⟨N, j, d, hd, hι⟩ := uibotWholePlane_dart_in_triangle W H h0 hpast D
  refine ⟨N, j, ?_⟩
  apply G.toPlaneGraphDrawingFaceEquiv.injective
  apply G.dartBorders_face_unique D
  · exact hD
  · exact (uibotGluedWindowTriangleFace_border W H h0 hpast N j D).mpr ⟨d, hd, hι⟩

/-- Helper toward Proposition 3.9: every original glued face has geometric
face degree three, using neighborhood-defined multiplicities, not merely a
dart count or a relabelled combinatorial face. -/
theorem uibotWholePlane_glued_faceDegree (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (K : (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H).toPlaneGraphDrawing.Face) :
    (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H).toPlaneGraphDrawing.faceDegree K = 3 := by
  classical
  let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
  obtain ⟨N, j, hK⟩ := uibotWholePlane_glued_face_triangle W H h0 hpast K
  let t := stageTriangleDartTriple (shiftedStream W N) j
  let raw : Fin 3 → ℕ × Bool := fun i =>
    if i.val = 0 then t.1 else if i.val = 1 then t.2.1 else t.2.2
  let darts : Fin 3 → WholePlaneDart W := fun i => wholePlaneDartι W N (raw i)
  let edges : Fin 3 → G.GeometricEdge := fun i => Quotient.mk G.edgeSetoid (darts i)
  have hinj : Function.Injective edges := by
    have hc : (Finset.univ.image edges).card = (Finset.univ : Finset (Fin 3)).card := by
      simpa only [edges, darts, raw, t, Finset.card_univ, Fintype.card_fin] using
        wholePlane_stageTriangle_geometricEdges_card W H G N j
    have hi := Finset.card_image_iff.mp hc
    intro i k hik
    exact hi (Finset.mem_univ i) (Finset.mem_univ k) hik
  let K' := G.toPlaneGraphDrawingFaceEquiv K
  have hb (a : WholePlaneDart W) : G.dartBorders a K' ↔ ∃ i : Fin 3, darts i = a := by
    change G.dartBorders a (G.toPlaneGraphDrawingFaceEquiv K) ↔ _
    rw [hK, uibotGluedWindowTriangleFace_border]
    constructor
    · rintro ⟨b, hb, rfl⟩
      change b ∈ [t.1, t.2.1, t.2.2] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨raw i, ?_, rfl⟩
      fin_cases i <;> simp [raw, t, stageTriangleDartList]
  have hmult (e : G.GeometricEdge) : G.toPlaneGraphDrawing.faceMult e K =
      if ∃ i : Fin 3, edges i = e then (1 : ℕ∞) else 0 := by
    have hc : (∃ i : Fin 3, edges i = e) ↔
        G.dartBorders e.out K' ∨ G.dartBorders (wholePlaneDartFlip W e.out) K' := by
      constructor
      · rintro ⟨i, hie⟩
        have hrel : darts i = e.out ∨ darts i = wholePlaneDartFlip W e.out :=
          Quotient.exact (hie.trans (Quotient.out_eq e).symm)
        have hbi := (hb (darts i)).mpr ⟨i, rfl⟩
        rcases hrel with he | he
        · exact Or.inl (he ▸ hbi)
        · exact Or.inr (he ▸ hbi)
      · rintro (he | he)
        · obtain ⟨i, hi⟩ := (hb e.out).mp he
          exact ⟨i, (congrArg (Quotient.mk G.edgeSetoid) hi).trans (Quotient.out_eq e)⟩
        · obtain ⟨i, hi⟩ := (hb (wholePlaneDartFlip W e.out)).mp he
          exact ⟨i, (congrArg (Quotient.mk G.edgeSetoid) hi).trans
            ((G.geometricEdge_flip e.out).trans (Quotient.out_eq e))⟩
    have hn : ¬ (G.dartBorders e.out K' ∧
        G.dartBorders (wholePlaneDartFlip W e.out) K') := by
      rintro ⟨hl, hr⟩
      obtain ⟨i, hi⟩ := (hb e.out).mp hl
      obtain ⟨k, hk⟩ := (hb (wholePlaneDartFlip W e.out)).mp hr
      have heq : edges i = edges k := by
        change Quotient.mk G.edgeSetoid (darts i) = Quotient.mk G.edgeSetoid (darts k)
        rw [hi, hk, G.geometricEdge_flip]
      have hik := hinj heq
      have hd : e.out = wholePlaneDartFlip W e.out := hi.symm.trans (hik ▸ hk)
      exact G.flip_ne e.out hd.symm
    rw [G.faceMult_eq_bordering_dart_count (uibhbot_faceOrbit_dartVertex_surjective W H)]
    change (if G.dartBorders e.out K' then (1 : ℕ∞) else 0) +
      (if G.dartBorders (wholePlaneDartFlip W e.out) K' then (1 : ℕ∞) else 0) = _
    by_cases hl : G.dartBorders e.out K'
    · have hr : ¬ G.dartBorders (wholePlaneDartFlip W e.out) K' := fun hr => hn ⟨hl, hr⟩
      have he := hc.mpr (Or.inl hl)
      simp only [hl, hr, he, ite_true, ite_false, add_zero]
    · by_cases hr : G.dartBorders (wholePlaneDartFlip W e.out) K'
      · have he := hc.mpr (Or.inr hr)
        simp only [hl, hr, he, ite_true, ite_false, zero_add]
      · have he : ¬ ∃ i : Fin 3, edges i = e := fun he => (hc.mp he).elim hl hr
        simp only [hl, hr, he, ite_false, zero_add]
  exact G.toPlaneGraphDrawing.faceDegree_eq_three_of_injective K edges hinj hmult

/-- Helper toward Proposition 3.9: every whole-plane vertex has both an
incoming and an outgoing edge identity. The past construction reverses the
one-sided orientation, and the two boundary copies are glued along the seam. -/
theorem uibotWholePlane_noPoles (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W)) (v : WholePlaneVertex W) :
    (∃ e : WholePlaneEdge W, wholePlaneEdgeWest W e = v) ∧
      (∃ e : WholePlaneEdge W, wholePlaneEdgeEast W e = v) := by
  have hout (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (x : ℕ) :
      ∃ e, EdgePresent w e ∧ edgeWest w e = x :=
    uibot_allocated_vertex_outgoing w h.R_unbounded_below x
      ⟨4 * x + 1, vertex_allocated_at w x⟩
  have hout0 (x : ℕ) : ∃ e : WholePlaneEdge W,
      wholePlaneEdgeWest W e = wholePlaneVertexι W 0 x := by
    obtain ⟨e, _, he⟩ := hout _ h0 x
    exact ⟨wholePlaneEdgeι W 0 e, (wholePlaneEdgeWest_ι W 0 e).trans
      (congrArg (wholePlaneVertexι W 0) he)⟩
  have hinpast (x : ℕ) : ∃ e : WholePlaneEdge W,
      wholePlaneEdgeEast W e = kmswPastVertex W x := by
    obtain ⟨e, _, he⟩ := hout _ hpast x
    exact ⟨kmswPastEdge W e, (kmswPastEdge_east W e).trans
      (congrArg (kmswPastVertex W) he)⟩
  rcases WholePlanePastGlueData.vertex_cover W v with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · refine ⟨hout0 x, ?_⟩
    rcases allocated_stage_incoming_or_left_boundary _ h0 (4 * x + 1) x
      (vertex_allocated_at _ x) with ⟨e, _, he⟩ | ⟨k, _, hx⟩
    · exact ⟨wholePlaneEdgeι W 0 e, (wholePlaneEdgeEast_ι W 0 e).trans
        (congrArg (wholePlaneVertexι W 0) he)⟩
    · obtain ⟨e, he⟩ := hinpast (boundaryVertex (kmswPastCode W) hpast (1 - k))
      refine ⟨e, he.trans ?_⟩
      rw [WholePlanePastGlueData.seam_vertex W h0 hpast, show 1 - (1 - k) = k by omega, hx]
  · refine ⟨?_, hinpast x⟩
    rcases allocated_stage_incoming_or_left_boundary _ hpast (4 * x + 1) x
      (vertex_allocated_at _ x) with ⟨e, _, he⟩ | ⟨k, _, hx⟩
    · exact ⟨kmswPastEdge W e, (kmswPastEdge_west W e).trans
        (congrArg (kmswPastVertex W) he)⟩
    · rw [hx, WholePlanePastGlueData.seam_vertex W h0 hpast]
      exact hout0 _

/-- Helper toward Proposition 3.9: the all-present geometric realization
as an ordinary directed plane map. Presence is certified on the whole carrier. -/
@[expose] def uibotWholePlaneDirectedMap (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    DirectedPlaneMap (WholePlaneVertex W) G.GeometricEdge where
  toPlaneGraphDrawing := (uibotWholePlaneGeometricMap W H G hp).toPlaneGraphDrawing
  forward e := !e.out.2

/-- Helper toward Proposition 3.9: the glued all-present realization is an
infinite bipolar-oriented triangulation in the installed geometric carrier.
Every vertex has incoming and outgoing edges, and every face has degree three. -/
theorem uibotWholePlaneDirectedMap_bipolarTriangulation (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    Infinite (WholePlaneVertex W) ∧
      (uibotWholePlaneDirectedMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp).IsBipolarTriangulation := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
  let M := uibotWholePlaneDirectedMap W H G hp
  have hend (a : G.GeometricEdge) : M.tail a = wholePlaneEdgeWest W a.out.1 ∧
      M.head a = wholePlaneEdgeEast W a.out.1 :=
    uibotWholePlaneGeometricMap_endpoints W H G hp a
  have hinc (v : WholePlaneVertex W) : (∃ a, M.tail a = v) ∧ (∃ a, M.head a = v) := by
    obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := uibotWholePlane_noPoles W h0 hpast v
    constructor
    · refine ⟨uibotWholePlaneSourceEdgeEquiv W H G e, ?_⟩
      rw [(hend _).1, uibotWholePlaneSourceEdgeEquiv_out, he]
    · refine ⟨uibotWholePlaneSourceEdgeEquiv W H G f, ?_⟩
      rw [(hend _).2, uibotWholePlaneSourceEdgeEquiv_out, hf]
  have hacyc : M.IsAcyclic := by
    have hpath {v w : WholePlaneVertex W} (h : Relation.TransGen M.step v w) :
        Relation.TransGen (uibotWholePlaneGeometricMap W H G hp).step v w := by
      induction h with
      | single h =>
        obtain ⟨e, ht, hh⟩ := h
        exact Relation.TransGen.single ⟨⟨e, uibotWholePlaneGeometricMap_noMissing W H G hp e⟩,
          ht, hh⟩
      | tail _ h ih =>
        obtain ⟨e, ht, hh⟩ := h
        exact ih.tail ⟨⟨e, uibotWholePlaneGeometricMap_noMissing W H G hp e⟩, ht, hh⟩
    intro v hv
    exact uibotWholePlaneGeometricMap_acyclic W H G hp v (hpath hv)
  refine ⟨uibotWholePlaneSource_infinite W, ⟨hacyc, ⟨?_⟩, ⟨?_⟩⟩, ?_⟩
  · intro a b
    obtain ⟨e, he⟩ := (hinc a.val).2
    exact (a.property e he).elim
  · intro a b
    obtain ⟨e, he⟩ := (hinc a.val).1
    exact (a.property e he).elim
  · intro F _
    exact uibotWholePlane_glued_faceDegree W H h0 hpast F

/-- Helper toward Proposition 3.9: the installed source colimit realization
has the connected, locally finite rooted domain required by Definition 3.8. -/
@[expose] def uibotWholePlaneSourceDomain (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) : D39DomainRootedMap where
  V := WholePlaneVertex W
  E := WholePlaneEdge W
  map := uibotWholePlaneSourceMap W H G hp
  root := uibotWholePlaneSourceRoot W H G
  domain := (uibotWholePlaneSourceIso W H G hp).symm.toCombDartIso.domain_map
    (uibotWholePlaneGeometricMap_domain W H G hp)

/-- Helper toward Proposition 3.9: the measurable iid representative is
almost surely the class of the installed source whole-plane KMSW colimit,
with the same rotation, past gluing, edge-presence and root witnesses.
The same realization is an infinite bipolar-oriented triangulation. -/
theorem uibotMeasurableWholePlaneClassMap_ae_source :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W =
          Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H
            (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp) ∧
        Infinite (WholePlaneVertex W) ∧
        (uibotWholePlaneDirectedMap W H
          (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp).IsBipolarTriangulation := by
  filter_upwards [uibotMeasurableWholePlaneClassMap_ae_represents_proved] with W hW
  obtain ⟨H, h0, hpast, hp, hdom, heq⟩ := hW
  refine ⟨H, h0, hpast, hp, ?_,
    uibotWholePlaneDirectedMap_bipolarTriangulation W H h0 hpast hp⟩
  rw [heq]
  exact Quotient.sound ⟨(uibotWholePlaneSourceIso W H
    (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp).symm⟩





theorem uibotSourceLocalLimit_eq_iidLaw_of_finiteSourceLaw
    (ℓ ρ : ℕ) (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsize : ∀ k, 1 ≤ ns k)
    (hne : ∀ k, Nonempty (KMSWMapIsoClass ℓ ρ (ns k)))
    (sourceFinite : ℕ → ProbabilityMeasure D39GeomRootedMapClass.{0})
    (sourceLimit : ProbabilityMeasure D39GeomRootedMapClass.{0})
    (finiteSourceLaw : ∀ k, sourceFinite k =
      uibotFiniteGeometricProbabilityLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k))
    (sourceLocalLimit : Tendsto sourceFinite atTop (𝓝 sourceLimit)) :
    (sourceLimit : Measure D39GeomRootedMapClass.{0}) =
      wholePlaneIIDCodeMeasure.map
        (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved) := by
  have heq : sourceFinite = fun k =>
      uibotFiniteGeometricProbabilityLaw ℓ ρ (ns k) hℓ hρ (hsize k) (hne k) :=
    funext finiteSourceLaw
  rw [heq] at sourceLocalLimit
  have h := tendsto_nhds_unique sourceLocalLimit
    (uibotFiniteGeometricProbabilityLaw_tendsto ℓ ρ hℓ hρ ns hns hsize hne)
  exact congrArg ProbabilityMeasure.toMeasure h




































end DirectedDistances.PaperProofs.Section3
end
