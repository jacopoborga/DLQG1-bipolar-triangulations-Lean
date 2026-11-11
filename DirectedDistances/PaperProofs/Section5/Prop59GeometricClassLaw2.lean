/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59GeometricClassLaw
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! Supporting lemmas for paper labels `prop-uihbot-sym` (see CORRESPONDENCE.md). -/

/-! Helpers toward Proposition 5.9 (`prop-uihbot-sym`,
to the sole coordinator. -/

public section
noncomputable section

open MeasureTheory Filter

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open DirectedDistances.PaperProofs.SourceResults
open Prop516ExteriorAssembly6
open scoped ComplexConjugate Topology ENNReal
open Set

private theorem map_eq_of_countable_small_fibers
    {α X C : Type*} [MeasurableSpace α] [PseudoEMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace C]
    [MeasurableSingletonClass C] [Countable C]
    (μ : ProbabilityMeasure α) (F : Bool → α → X) (b : Bool → ℕ → α → C)
    (hF : ∀ i, Measurable (F i)) (hb : ∀ i r, Measurable (b i r))
    (hlaw : ∀ r, μ.map (b false r) = μ.map (b true r))
    (S : Set α) (hS : ∀ᵐ a ∂(μ : Measure α), a ∈ S)
    (hsmall : ∀ r i j a, a ∈ S → ∀ a', a' ∈ S → b i r a = b j r a' →
      edist (F i a) (F j a') ≤ (1 / 2 : ℝ≥0∞) ^ r) :
    μ.map (F false) = μ.map (F true) := by
  classical
  obtain ⟨a₀, ha₀⟩ := hS.exists
  let v (r : ℕ) (c : C) : X :=
    if h : ∃ p : Bool × α, p.2 ∈ S ∧ b p.1 r p.2 = c then
      F (Classical.choose h).1 (Classical.choose h).2 else F false a₀
  have hv (r : ℕ) (i : Bool) (a : α) (ha : a ∈ S) :
      edist (v r (b i r a)) (F i a) ≤ (1 / 2 : ℝ≥0∞) ^ r := by
    have hex : ∃ p : Bool × α, p.2 ∈ S ∧ b p.1 r p.2 = b i r a :=
      ⟨(i, a), ha, rfl⟩
    simp only [v, dite_eq_left hex]
    exact hsmall r _ _ _ (Classical.choose_spec hex).1 a ha
      (Classical.choose_spec hex).2
  have hmeas (i : Bool) (r : ℕ) : Measurable (fun a => v r (b i r a)) :=
    (measurable_of_countable (v r)).comp (hb i r)
  have hlim (i : Bool) : TendstoInDistribution
      (fun r a => v r (b i r a)) atTop (F i) (fun _ => (μ : Measure α))
      (μ : Measure α) := by
    apply tendstoInDistribution_of_ae_tendsto
      (fun r => (hmeas i r).aemeasurable) (hF i).aemeasurable
    filter_upwards [hS] with a ha
    apply EMetric.tendsto_nhds.mpr
    intro ε hε
    have ht := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (1 / 2 : ℝ≥0∞) < 1)
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with r hr
    exact (hv r i a ha).trans_lt hr
  have heq (r : ℕ) : μ.map (fun a => v r (b false r a)) =
      μ.map (fun a => v r (b true r a)) := by
    apply ProbabilityMeasure.toMeasure_injective
    change (μ : Measure α).map (v r ∘ b false r) =
      (μ : Measure α).map (v r ∘ b true r)
    rw [← Measure.map_map (measurable_of_countable (v r)) (hb false r),
      ← Measure.map_map (measurable_of_countable (v r)) (hb true r)]
    exact congrArg (fun ν : ProbabilityMeasure C => (ν : Measure C).map (v r)) (hlaw r)
  exact tendsto_nhds_unique (hlim false).tendsto
    ((hlim true).tendsto.congr' (Eventually.of_forall fun r => (heq r).symm))

private theorem conj_affineOnSegments (p : Polyline) :
    Polyline.AffineOnSegments conj p := by
  intro i hi
  exact ⟨Complex.conjCLE.toLinearMap.toAffineMap, fun _ _ => rfl⟩

private theorem initialDirection_mapPoints_conj (p : Polyline) :
    (p.mapPoints conj).initialDirection = conj p.initialDirection := by
  simp only [Polyline.initialDirection, Polyline.point_mapPoints,
    Polyline.start_mapPoints, map_sub]

private def mirrorPLDrawing (M : RootedLocallyFiniteMap)
    (P : PLDrawing M.D (RootedLocallyFiniteVertex M.D M.rot)
      M.edgeInv M.rot (d39VertexClass M.toD39RootedMap)) :
    PLDrawing M.D (RootedLocallyFiniteVertex M.D M.rot.symm)
      M.edgeInv M.rot.symm
      (d39VertexClass (mirrorRootedLocallyFiniteMap M).toD39RootedMap) := by
  let V := prop59_mirrorRotationVertexEquiv M.rot
  have hclass (d : M.D) :
      V.symm (rootedLocallyFiniteVertexClass M.rot.symm d) =
        rootedLocallyFiniteVertexClass M.rot d := rfl
  have hrot (d : M.D) :
      rootedLocallyFiniteVertexClass M.rot (M.rot.symm d) =
        rootedLocallyFiniteVertexClass M.rot d := by
    apply Quotient.sound
    exact (Equiv.Perm.sameCycle_symm_apply_left).2 Equiv.Perm.SameCycle.rfl
  refine {
    flip_involutive := M.edgeInv_invol
    flip_ne := M.edgeInv_ne
    vert_rotation := ?_
    pos := fun v => conj (P.pos (V.symm v))
    pos_injective := fun _ _ h => V.symm.injective
      (P.pos_injective (geomConj.injective h))
    arc := fun d => (P.arc d).mapPoints conj
    arc_simple := fun d => Polyline.isSimple_mapPoints conj (P.arc d)
      (conj_affineOnSegments _) geomConj.injective.injOn (P.arc_simple d)
    arc_length := fun d => by simpa only [Polyline.length_mapPoints] using P.arc_length d
    arc_start := ?_
    arc_finish := ?_
    arc_flip := ?_
    interior_disjoint := fun d e hne hflip =>
      Polyline.interior_disjoint_mapPoints conj _ _
        (conj_affineOnSegments _) (conj_affineOnSegments _)
        geomConj.injective.injOn (P.interior_disjoint d e hne hflip)
    interior_avoids_vertices := ?_
    locally_finite := ?_
    initial_nonzero := ?_
    initial_arg_injective := ?_
    rotation_agreement := ?_ }
  · intro d
    apply V.symm.injective
    exact hrot d
  · intro d
    rw [Polyline.start_mapPoints, P.arc_start]
    rfl
  · intro d
    rw [Polyline.finish_mapPoints, P.arc_finish]
    rfl
  · intro d
    rw [P.arc_flip, Polyline.mapPoints_reverse]
  · intro d v hv
    rw [Polyline.interior_mapPoints conj _ (conj_affineOnSegments _)
      geomConj.injective.injOn] at hv
    obtain ⟨z, hz, he⟩ := hv
    exact P.interior_avoids_vertices d (V.symm v) (geomConj.injective he ▸ hz)
  · intro K hK
    have hb : Bornology.IsBounded (geomConj '' closure K) :=
      (hK.isCompact_closure.image geomConj.continuous).isBounded
    apply (P.locally_finite _ hb).subset
    intro d hd
    obtain ⟨z, hzK, hz⟩ := hd
    rw [Polyline.image_mapPoints conj _ (conj_affineOnSegments _)] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, ⟨conj x, subset_closure hzK, star_star x⟩, hx⟩
  · intro d
    rw [initialDirection_mapPoints_conj]
    exact fun h => P.initial_nonzero d
      (Complex.conjCLE.injective (by
        change conj (P.arc d).initialDirection = conj 0
        rw [map_zero]
        exact h))
  · intro d e hv he
    simp only [initialDirection_mapPoints_conj] at he
    exact P.initial_arg_injective d e (congrArg V.symm hv)
      (prop59_arg_conj_injective he)
  · intro d
    have hs : {e | rootedLocallyFiniteVertexClass M.rot.symm e =
        rootedLocallyFiniteVertexClass M.rot.symm d} =
        {e | rootedLocallyFiniteVertexClass M.rot e =
          rootedLocallyFiniteVertexClass M.rot (M.rot.symm d)} := by
      ext e
      change (rootedLocallyFiniteVertexClass M.rot.symm e =
        rootedLocallyFiniteVertexClass M.rot.symm d) ↔ _
      rw [hrot d]
      exact V.symm.injective.eq_iff.symm
    simp only [initialDirection_mapPoints_conj]
    change CcwSuccessor {e | rootedLocallyFiniteVertexClass M.rot.symm e =
      rootedLocallyFiniteVertexClass M.rot.symm d}
      (fun e => conj (P.arc e).initialDirection) d (M.rot.symm d)
    rw [hs]
    have hsucc := P.rotation_agreement (M.rot.symm d)
    change CcwSuccessor {e | rootedLocallyFiniteVertexClass M.rot e =
      rootedLocallyFiniteVertexClass M.rot (M.rot.symm d)}
      (fun e => (P.arc e).initialDirection) (M.rot.symm d) (M.rot (M.rot.symm d)) at hsucc
    rw [Equiv.apply_symm_apply] at hsucc
    have hr := prop59_ccwSuccessor_conj_reverse
      (fun x (hx : rootedLocallyFiniteVertexClass M.rot x = _) y
        (hy : rootedLocallyFiniteVertexClass M.rot y = _) he =>
        P.initial_arg_injective x y (hx.trans hy.symm) he) hsucc
    simpa only [Equiv.apply_symm_apply] using hr

private theorem listPath_conj (a : ℂ) (l : List ℂ) (t : unitInterval) :
    Polyline.listPath (conj a) (l.map conj) t = conj (Polyline.listPath a l t) := by
  induction l generalizing a t with
  | nil => rfl
  | cons b l ih =>
    cases l with
    | nil =>
      change (Path.segment (conj a) (conj b)) t = conj ((Path.segment a b) t)
      simp [Path.segment_apply, AffineMap.lineMap_apply_module]
    | cons c l =>
      change ((Path.segment (conj a) (conj b)).trans
        (Polyline.listPath (conj b) ((c :: l).map conj))) t =
        conj (((Path.segment a b).trans (Polyline.listPath b (c :: l))) t)
      rw [Path.trans_apply, Path.trans_apply]
      split
      · have htwo : conj (2 : ℂ) = 2 := by
          change conj ((2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ)
          exact Complex.conj_ofReal 2
        simp [Path.segment_apply, AffineMap.lineMap_apply_module, htwo]
      · exact ih _ _

private theorem toPath_conj (p : Polyline) (t : unitInterval) :
    (p.mapPoints conj).toPath t = conj (p.toPath t) := by
  obtain ⟨l, hl⟩ := p
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons a l => exact listPath_conj a l t

private def mirrorRootedMapIso {M N : RootedLocallyFiniteMap}
    (I : D39RootedMapIso M.toD39RootedMap N.toD39RootedMap) :
    D39RootedMapIso (mirrorRootedLocallyFiniteMap M).toD39RootedMap
      (mirrorRootedLocallyFiniteMap N).toD39RootedMap where
  toEquiv := I.toEquiv
  rot_comm := by
    intro d
    change I.toEquiv (M.rot.symm d) = N.rot.symm (I.toEquiv d)
    apply N.rot.injective
    exact (I.rot_comm (M.rot.symm d)).symm.trans
      ((congrArg I.toEquiv (M.rot.apply_symm_apply d)).trans
        (N.rot.apply_symm_apply _).symm)
  edgeInv_comm := I.edgeInv_comm
  missing_iff := I.missing_iff
  tail_iff := I.tail_iff
  root_dart_comm := (I.edgeInv_comm _).trans (congrArg N.edgeInv I.root_dart_comm)

/-- Helper toward Proposition 5.9: reparameterized PL representations with
isomorphic faced balls and the same marked root side have zero geometric
distance when their root-side ambient orbits are infinite. -/
theorem represented_edist_zero_of_infinite_rootSideOrbit
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : D39DrawingRepresentationData3 M B) (y : D39DrawingRepresentationData3 N C)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (Q : PLDrawing N.core.D (RootedLocallyFiniteVertex N.core.D N.core.rot)
      N.core.edgeInv N.core.rot (d39VertexClass N))
    (hp : ∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v))
    (hq : ∀ v, Q.pos v = C.map.toPlaneMapWithMissing.pos (y.vertexEquiv v))
    (ha : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc B x.toD39DrawingRepresentationData d t =
        (P.arc d).toPath (φ t))
    (hb : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc C y.toD39DrawingRepresentationData d t =
        (Q.arc d).toPath (φ t))
    (I : D39RootedMapIso M N)
    (hM : {d | Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv)
      (M.core.edgeInv M.rootMark.dart) d}.Infinite)
    (hN : {d | Equiv.Perm.SameCycle (N.core.rot.symm * N.core.edgeInv)
      (N.core.edgeInv N.rootMark.dart) d}.Infinite) :
    edist (PLCylinderBall.geometricClass B) (PLCylinderBall.geometricClass C) = 0 := by
  change d39GeomDistanceV2 B.map B.root C.map C.root = 0
  apply d39GeomDistanceV2_eq_zero_iff.mpr
  intro r hr
  let J := I.ballIso r hr
  have hpSide := prop59_infiniteFaceOrbit_mem_restrictedExternalOrbit
    M P r hr ((d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart) hM
  have hqSide := prop59_infiniteFaceOrbit_mem_restrictedExternalOrbit
    N Q r hr ((d39FacedBall N r hr).map.edgeInv (d39FacedBall N r hr).rootDart) hN
  have hmark : plBallFaceOrbitMap J (d39FacedBallPLWithExternal M P r hr).externalOrbit =
      (d39FacedBallPLWithExternal N Q r hr).externalOrbit := by
    apply (plBallFaceOrbitMap_eq_iff_exists_common_dart J _ _).mpr
    refine ⟨_, hpSide, ?_⟩
    rw [J.edgeInv_comm, J.root_comm]
    exact hqSide
  apply exteriorMarkedComparison_reparam_geomBallIso x y P Q hp hq ha hb r hr
  apply Quotient.sound
  exact ⟨{ toD39BallIso := J
           external_iff := (plBallFaceOrbitMap_eq_iff J _ _).mp hmark }⟩

/-- Helper toward Proposition 5.9: almost-sure inseparability identifies
Borel pushforwards of almost-everywhere measurable maps. The Borel saturation
step is `Inseparable.mem_measurableSet_iff`, proved by induction on open sets,
complements and countable unions. -/
theorem map_eq_of_ae_inseparable
    {α X : Type*} [MeasurableSpace α] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure α} {f g : α → X}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ᵐ a ∂μ, Inseparable (f a) (g a)) : μ.map f = μ.map g := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply_of_aemeasurable hf hs, Measure.map_apply_of_aemeasurable hg hs]
  apply measure_congr
  filter_upwards [h] with a ha
  exact propext (ha.mem_measurableSet_iff hs)

/-- Helper toward Proposition 5.9: zero pseudo-emetric distance almost
surely identifies Borel pushforwards, without a separation assumption. -/
theorem map_eq_of_ae_edist_zero
    {α X : Type*} [MeasurableSpace α] [PseudoEMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure α} {f g : α → X}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ᵐ a ∂μ, edist (f a) (g a) = 0) : μ.map f = μ.map g := by
  apply map_eq_of_ae_inseparable hf hg
  filter_upwards [h] with a ha
  exact EMetric.inseparable_iff.mpr ha

/-- Helper toward Proposition 5.9: the probability-measure version of
almost-sure inseparability for Borel targets. -/
theorem probabilityMeasure_map_eq_of_ae_inseparable
    {α X : Type*} [MeasurableSpace α] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure α) {f g : α → X}
    (hf : AEMeasurable f (μ : Measure α)) (hg : AEMeasurable g (μ : Measure α))
    (h : ∀ᵐ a ∂(μ : Measure α), Inseparable (f a) (g a)) : μ.map f = μ.map g := by
  apply ProbabilityMeasure.toMeasure_injective
  exact map_eq_of_ae_inseparable hf hg h

/-- Helper toward Proposition 5.9: on one conull event, the reflected
canonical class has zero distance to every PL representation of the mirrored
code. Endpoint-preserving reparameterizations of the canonical assembly are
used directly; no literal canonical PL representation is assumed. -/
theorem prop59_mirror_canonical_edist_PLRepresentation_zero_ae :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (C : D39DomainRootedMapV2.{0})
        (_y : PLCylinderBall.Representation
          ((mirrorRootedLocallyFinitePlanarMap
            (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) C),
        edist (prop59GeometricClassMirror (canonicalGeometricClass W))
          (PLCylinderBall.geometricClass C) = 0 := by
  filter_upwards [prop59_mirrorRep_canonicalRepresentation_ae,
    canonicalGeometricClass_spec, uibhbotRootedPlanarMapConullEvent_spec.2.1]
    with W hw hc hW
  obtain ⟨H, h0, hL, hR, hfin, hRpos, hA, hmirror, canonical⟩ := hw
  let D : UIBHBOTD39CanonicalDomainWitness W := ⟨H, h0, hL, hR, hfin, hRpos, hA⟩
  let B := uibhbotD39CanonicalRepresentation13Domain W D
  let Bm : D39DomainRootedMapV2 :=
    ⟨B.V, B.E, B.map.geomMirror, d39GeomMirrorRoot B.root, hmirror⟩
  have hm : B.map.toPlaneMapWithMissing.missing B.root.1 :=
    hA.geomMirror_iff_missing.mp hmirror
  have he : canonicalGeometricClass W = PLCylinderBall.geometricClass B := by
    obtain ⟨hs, he⟩ := hc
    simpa only [uibhbotD39CanonicalClass_eq_some_domain W D, Option.get_some] using he
  have hem : prop59GeometricClassMirror (canonicalGeometricClass W) =
      PLCylinderBall.geometricClass Bm := by
    rw [he]
    exact prop59GeometricClassMirror_mk (PLCylinderBall.domainMap B) hm
  obtain ⟨hhit, C₀, iso, x, hp, ha⟩ :=
    exteriorMarkedComparison_canonical_reparam_data W hW D
  let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀
  let P := exteriorMarkedComparison_canonicalDrawing W D hhit C₀
  let xm := prop59_mirrorRep_data3 M B x hmirror
  let Pm := mirrorPLDrawing M P
  have hpm : ∀ v, Pm.pos v = Bm.map.toPlaneMapWithMissing.pos (xm.vertexEquiv v) := by
    intro v
    change conj (P.pos ((prop59_mirrorRotationVertexEquiv M.rot).symm v)) =
      conj (B.map.toPlaneMapWithMissing.pos
        (x.vertexEquiv ((prop59_mirrorRotationVertexEquiv M.rot).symm v)))
    exact congrArg conj (hp _)
  have ham : ∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t, d39DrawingDartArc Bm xm.toD39DrawingRepresentationData d t =
        (Pm.arc d).toPath (φ t) := by
    intro d
    obtain ⟨φ, hφ0, hφ1, hφ⟩ := ha d
    refine ⟨φ, hφ0, hφ1, ?_⟩
    intro t
    change d39DrawingDartArc Bm (prop59_mirrorRep_base M B x hmirror) d t =
      ((P.arc d).mapPoints conj).toPath (φ t)
    calc
      _ = conj (d39DrawingDartArc B x.toD39DrawingRepresentationData d t) :=
        prop59_mirrorRep_dartArc M B x hmirror d t
      _ = conj ((P.arc d).toPath (φ t)) := congrArg conj (hφ t)
      _ = _ := (toPath_conj (P.arc d) (φ t)).symm
  have hM : {d | Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv)
      (M.edgeInv M.frameEdgeDart) d}.Infinite :=
    prop59_canonical_outerOrbit_infinite W H h0 hL hR hfin hRpos
  have hMm := prop59_mirror_rootSideOrbit_infinite M hM
  have hNm := prop59_mirroredCode_rootSideOrbit_infinite
    W hW H h0 hL hR hfin hRpos
  intro C y
  rw [hem]
  exact represented_edist_zero_of_infinite_rootSideOrbit xm y.data Pm y.drawing
    hpm y.pos_eq ham
    (fun d => ⟨Homeomorph.refl unitInterval, rfl, rfl, fun t => (y.arc_eq d t).symm⟩)
    (mirrorRootedMapIso iso) hMm hNm

/-- Helper toward Proposition 5.9: the reflected canonical class and every
PL representative of its mirrored code are topologically inseparable almost
surely, simultaneously for all such representatives. -/
theorem prop59_mirror_canonical_inseparable_PLRepresentation_ae :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (C : D39DomainRootedMapV2.{0})
        (_y : PLCylinderBall.Representation
          ((mirrorRootedLocallyFinitePlanarMap
            (uibhbotRootedPlanarMapOfCode W)).toD39PlanarRootedMap.toD39RootedMap) C),
        Inseparable (prop59GeometricClassMirror (canonicalGeometricClass W))
          (PLCylinderBall.geometricClass C) := by
  filter_upwards [prop59_mirror_canonical_edist_PLRepresentation_zero_ae] with W hW
  intro C y
  exact EMetric.inseparable_iff.mpr (hW C y)

private def taggedCode (i : Bool) (W : ℤ → Fin 3) : RootedLocallyFinitePlanarMap :=
  if i then uibhbotRootedPlanarMapOfCode W
  else mirrorRootedLocallyFinitePlanarMap (uibhbotRootedPlanarMapOfCode W)

private def taggedClass (i : Bool) (W : ℤ → Fin 3) : D39GeomRootedMapClass.{0} :=
  if i then canonicalGeometricClass W
  else prop59GeometricClassMirror (canonicalGeometricClass W)

private theorem tagged_representation_ae :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ i : Bool,
      ∃ (M : RootedLocallyFiniteMap) (B : D39DomainRootedMapV2.{0})
        (x : D39DrawingRepresentationData3 M.toD39RootedMap B)
        (P : PLDrawing M.D (RootedLocallyFiniteVertex M.D M.rot)
          M.edgeInv M.rot (d39VertexClass M.toD39RootedMap))
        (_iso : D39RootedMapIso M.toD39RootedMap (taggedCode i W).toD39RootedMap),
        (∀ v, P.pos v = B.map.toPlaneMapWithMissing.pos (x.vertexEquiv v)) ∧
        (∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, φ 0 = 0 ∧ φ 1 = 1 ∧
          ∀ t, d39DrawingDartArc B x.toD39DrawingRepresentationData d t =
            (P.arc d).toPath (φ t)) ∧
        {d | Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv)
          (M.edgeInv M.frameEdgeDart) d}.Infinite ∧
        taggedClass i W = PLCylinderBall.geometricClass B := by
  filter_upwards [prop59_mirrorRep_canonicalRepresentation_ae,
    canonicalGeometricClass_spec, uibhbotRootedPlanarMapConullEvent_spec.2.1]
    with W hw hc hW
  obtain ⟨H, h0, hL, hR, hfin, hRpos, hA, hmirror, canonical⟩ := hw
  let D : UIBHBOTD39CanonicalDomainWitness W := ⟨H, h0, hL, hR, hfin, hRpos, hA⟩
  let B := uibhbotD39CanonicalRepresentation13Domain W D
  let Bm : D39DomainRootedMapV2 :=
    ⟨B.V, B.E, B.map.geomMirror, d39GeomMirrorRoot B.root, hmirror⟩
  have hm : B.map.toPlaneMapWithMissing.missing B.root.1 :=
    hA.geomMirror_iff_missing.mp hmirror
  have he : canonicalGeometricClass W = PLCylinderBall.geometricClass B := by
    obtain ⟨hs, he⟩ := hc
    simpa only [uibhbotD39CanonicalClass_eq_some_domain W D, Option.get_some] using he
  have hem : prop59GeometricClassMirror (canonicalGeometricClass W) =
      PLCylinderBall.geometricClass Bm := by
    rw [he]
    exact prop59GeometricClassMirror_mk (PLCylinderBall.domainMap B) hm
  obtain ⟨hhit, C₀, iso, x, hp, ha⟩ :=
    exteriorMarkedComparison_canonical_reparam_data W hW D
  let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀
  let P := exteriorMarkedComparison_canonicalDrawing W D hhit C₀
  have hM : {d | Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv)
      (M.edgeInv M.frameEdgeDart) d}.Infinite :=
    prop59_canonical_outerOrbit_infinite W H h0 hL hR hfin hRpos
  intro i
  cases i with
  | true => exact ⟨M, B, x, P, iso, hp, ha, hM, he⟩
  | false =>
    let xm := prop59_mirrorRep_data3 M B x hmirror
    let Pm := mirrorPLDrawing M P
    refine ⟨mirrorRootedLocallyFiniteMap M, Bm, xm, Pm,
      mirrorRootedMapIso iso, ?_, ?_,
      prop59_mirror_rootSideOrbit_infinite M hM, hem⟩
    · intro v
      change conj (P.pos ((prop59_mirrorRotationVertexEquiv M.rot).symm v)) =
        conj (B.map.toPlaneMapWithMissing.pos
          (x.vertexEquiv ((prop59_mirrorRotationVertexEquiv M.rot).symm v)))
      exact congrArg conj (hp _)
    · intro d
      obtain ⟨φ, hφ0, hφ1, hφ⟩ := ha d
      refine ⟨φ, hφ0, hφ1, ?_⟩
      intro t
      calc
        _ = conj (d39DrawingDartArc B x.toD39DrawingRepresentationData d t) :=
          prop59_mirrorRep_dartArc M B x hmirror d t
        _ = conj ((P.arc d).toPath (φ t)) := congrArg conj (hφ t)
        _ = _ := (toPath_conj (P.arc d) (φ t)).symm

section Law

local instance prop59GeometricClassLaw2_measurable :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}

local instance prop59GeometricClassLaw2_borel :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

local instance prop59GeometricClassLaw2_codeTopology :
    TopologicalSpace RootedLocallyFinitePlanarMap :=
  RootedBallSystem.bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

local instance prop59GeometricClassLaw2_codeMeasurable :
    MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap

local instance prop59GeometricClassLaw2_codeBorel :
    BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩

local instance prop59GeometricClassLaw2_ballMeasurable : MeasurableSpace D39BallClass := ⊤

private theorem measurable_taggedCode (i : Bool) : Measurable (taggedCode i) := by
  cases i with
  | false =>
    exact measurable_mirrorRootedLocallyFinitePlanarMap.comp measurable_uibhbotRootedPlanarMapOfCode
  | true => exact measurable_uibhbotRootedPlanarMapOfCode

private theorem measurable_taggedClass (i : Bool) : Measurable (taggedClass i) := by
  cases i with
  | false => exact measurable_prop59GeometricClassMirror.comp measurable_canonicalGeometricClass
  | true => exact measurable_canonicalGeometricClass





theorem prop59_sourceGeometricClassLaw_mirror_invariant :
    uibhbotSourceGeometricClassLaw.map prop59GeometricClassMirror =
      uibhbotSourceGeometricClassLaw := by
  rw [uibhbotSourceGeometricClassLaw_map_mirror_eq_codePushforward,
    uibhbotSourceGeometricClassLaw_eq_canonicalCodePushforward]
  change uibhbotCodeLawRel.map (taggedClass false) =
    uibhbotCodeLawRel.map (taggedClass true)
  let β (r : ℕ) (M : RootedLocallyFinitePlanarMap) : D39BallClass :=
    d39BallClass M.toD39RootedMap (r + 1) (Nat.succ_pos r)
  have hβ (r : ℕ) : Measurable (β r) :=
    ((measurable_into_iff_ballClass_generic d39RootedBallSystem _).mp
      measurable_toD39RootedMap r)
  obtain ⟨S, hSae, _hSmeas, hs⟩ := tagged_representation_ae.exists_measurable_mem
  refine map_eq_of_countable_small_fibers uibhbotCodeLawRel taggedClass
    (fun i r W => β r (taggedCode i W)) measurable_taggedClass
    (fun i r => (hβ r).comp (measurable_taggedCode i)) ?_ S hSae ?_
  · intro r
    apply ProbabilityMeasure.toMeasure_injective
    change (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (β r ∘ taggedCode false) =
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map (β r ∘ taggedCode true)
    rw [← Measure.map_map (hβ r) (measurable_taggedCode false),
      ← Measure.map_map (hβ r) (measurable_taggedCode true)]
    exact congrArg (fun ν : ProbabilityMeasure RootedLocallyFinitePlanarMap =>
      (ν : Measure RootedLocallyFinitePlanarMap).map (β r))
      prop59_reduction_code_pushforward_mirror_invariant
  · intro r i j W hW W' hW' hball
    obtain ⟨M, B, x, P, iso, hp, ha, hM, he⟩ := hs W hW i
    obtain ⟨N, C, y, Q, iso', hq, hb, hN, he'⟩ := hs W' hW' j
    rw [he, he']
    have hi : d39BallClass M.toD39RootedMap (r + 1) (Nat.succ_pos r) =
        β r (taggedCode i W) := Quotient.sound ⟨iso.ballIso _ _⟩
    have hi' : d39BallClass N.toD39RootedMap (r + 1) (Nat.succ_pos r) =
        β r (taggedCode j W') := Quotient.sound ⟨iso'.ballIso _ _⟩
    obtain ⟨J⟩ := Quotient.exact (hi.trans (hball.trans hi'.symm))
    have hpSide := prop59_infiniteFaceOrbit_mem_restrictedExternalOrbit
      M.toD39RootedMap P (r + 1) (Nat.succ_pos r)
      ((d39FacedBall M.toD39RootedMap (r + 1) (Nat.succ_pos r)).map.edgeInv
        (d39FacedBall M.toD39RootedMap (r + 1) (Nat.succ_pos r)).rootDart) hM
    have hqSide := prop59_infiniteFaceOrbit_mem_restrictedExternalOrbit
      N.toD39RootedMap Q (r + 1) (Nat.succ_pos r)
      ((d39FacedBall N.toD39RootedMap (r + 1) (Nat.succ_pos r)).map.edgeInv
        (d39FacedBall N.toD39RootedMap (r + 1) (Nat.succ_pos r)).rootDart) hN
    have hmark : plBallFaceOrbitMap J
        (d39FacedBallPLWithExternal M.toD39RootedMap P (r + 1) (Nat.succ_pos r)).externalOrbit =
        (d39FacedBallPLWithExternal N.toD39RootedMap Q (r + 1) (Nat.succ_pos r)).externalOrbit := by
      apply (plBallFaceOrbitMap_eq_iff_exists_common_dart J _ _).mpr
      refine ⟨_, hpSide, ?_⟩
      rw [J.edgeInv_comm, J.root_comm]
      exact hqSide
    have hmarked : Quotient.mk exteriorMarkedBallSetoid
        (d39FacedBallPLWithExternal M.toD39RootedMap P (r + 1) (Nat.succ_pos r)) =
        Quotient.mk exteriorMarkedBallSetoid
        (d39FacedBallPLWithExternal N.toD39RootedMap Q (r + 1) (Nat.succ_pos r)) := by
      apply Quotient.sound
      exact ⟨{ toD39BallIso := J
               external_iff := (plBallFaceOrbitMap_eq_iff J _ _).mp hmark }⟩
    exact ((d39ClassDistance_le_pow_iff_nonempty (Nat.succ_pos r) _ _).mpr
      (exteriorMarkedComparison_reparam_geomBallIso x y P Q hp hq ha hb
        (r + 1) (Nat.succ_pos r) hmarked)).trans
      (pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_succ r))

end Law

end DirectedDistances.PaperProofs.Section5
end
