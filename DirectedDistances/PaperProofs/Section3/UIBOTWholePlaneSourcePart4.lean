/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTWholePlaneSourcePart3
public import DirectedDistances.KMSW.UIBHBOTWholePlaneWord
public import DirectedDistances.PlanarMap.GeneralPlaneMapInvariance
import Mathlib.Probability.Independence.InfinitePi

/-! # Normalized iid walk and the rooted whole-plane source realization

The code at integer t is the transition from t to t + 1. Integration uses the
already installed `wholePlaneWordIntegral`; its zero normalization, increments,
and exact iid law are proved here. The joint almost-sure realization retains
the original whole-plane edge IDs, lambda zero, original faces and plane
orientation. No recurrence, edge-presence or triangulation premise is added -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

local instance uibotWholePlaneSourcePart4GeomMeasurable :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotWholePlaneSourcePart4GeomBorel :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: integration of every two-sided source
code has exactly the printed normalization at time zero. -/
theorem uibotSourceWalk_zero (W : ℤ → Fin 3) :
    wholePlaneWordIntegral W 0 = (0, 0) := by
  simp [wholePlaneWordIntegral, Prod.zero_eq_mk]

/-- Helper toward Proposition 3.9: at every integer time, including the
negative half-line and the transition across zero, the integrated walk has
the increment encoded by the source code at that time. -/
theorem uibotSourceWalk_increment (W : ℤ → Fin 3) (t : ℤ) :
    wholePlaneWordIntegral W (t + 1) - wholePlaneWordIntegral W t =
      lazyTwoDimensionalStep (W t) := by
  have hcast (xs : List ℕ) :
      (Nat.cast <$> xs : List ℤ) = xs.map (fun i : ℕ => (i : ℤ)) := rfl
  have hp (n : ℕ) : wholePlaneWordIntegral W (n : ℤ) =
      ((List.range n).map (fun i : ℕ => lazyTwoDimensionalStep (W (i : ℤ)))).sum := by
    simp only [wholePlaneWordIntegral, ite_eq_left (by omega : 0 ≤ (n : ℤ)),
      Int.toNat_natCast, bind_pure_comp, hcast, List.map_map, Function.comp_def]
  have hn (n : ℕ) : wholePlaneWordIntegral W (-(n : ℤ)) =
      -((List.range n).map (fun i : ℕ => lazyTwoDimensionalStep (W (-(i : ℤ) - 1)))).sum := by
    cases n with
    | zero => simp [wholePlaneWordIntegral]
    | succ n =>
      have hz : ¬ 0 ≤ -((n + 1 : ℕ) : ℤ) := by omega
      simp only [wholePlaneWordIntegral, ite_eq_right hz, neg_neg, Int.toNat_natCast,
        bind_pure_comp, hcast, List.map_map, Function.comp_def]
  by_cases ht : 0 ≤ t
  · have ht' : t = (t.toNat : ℤ) := by omega
    rw [ht']
    rw [show (t.toNat : ℤ) + 1 = ((t.toNat + 1 : ℕ) : ℤ) by omega, hp, hp]
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_sub_cancel_left]
  · let n := (-t - 1).toNat
    have ht' : t = -((n + 1 : ℕ) : ℤ) := by dsimp [n]; omega
    have ht1 : t + 1 = -(n : ℤ) := by omega
    have harg : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
    rw [ht1, ht', hn, hn]
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [harg]
    abel

/-- Helper toward Proposition 3.9: the source walk is uniquely determined
by its normalization and coded increments on all of the integers. -/
theorem uibotSourceWalk_unique (W : ℤ → Fin 3) (Z : ℤ → ℤ × ℤ)
    (hzero : Z 0 = (0, 0))
    (hstep : ∀ t : ℤ, Z (t + 1) - Z t = lazyTwoDimensionalStep (W t)) :
    Z = wholePlaneWordIntegral W := by
  funext t
  have hp : ∀ n : ℕ, Z (n : ℤ) = wholePlaneWordIntegral W (n : ℤ) := by
    intro n
    induction n with
    | zero => exact hzero.trans (uibotSourceWalk_zero W).symm
    | succ n ih =>
      have h := (hstep (n : ℤ)).trans (uibotSourceWalk_increment W (n : ℤ)).symm
      rw [ih] at h
      exact sub_left_inj.mp h
  have hn : ∀ n : ℕ, Z (-(n : ℤ)) = wholePlaneWordIntegral W (-(n : ℤ)) := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero, neg_zero] using hp 0
    | succ n ih =>
      have h := (hstep (-((n + 1 : ℕ) : ℤ))).trans
        (uibotSourceWalk_increment W (-((n + 1 : ℕ) : ℤ))).symm
      rw [show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by omega, ih] at h
      exact sub_right_inj.mp h
  rcases le_total 0 t with ht | ht
  · simpa only [Int.toNat_of_nonneg ht] using hp t.toNat
  · simpa only [Int.toNat_of_nonneg (neg_nonneg.mpr ht), neg_neg] using hn (-t).toNat

/-- Helper toward Proposition 3.9: the increments of the normalized
whole-plane walk are mutually independent over all integer times. -/
theorem uibotSourceWalk_independent_increments :
    iIndepFun (fun t (W : ℤ → Fin 3) =>
      wholePlaneWordIntegral W (t + 1) - wholePlaneWordIntegral W t)
      wholePlaneIIDCodeMeasure := by
  simp only [uibotSourceWalk_increment]
  exact iIndepFun_infinitePi (fun _ => measurable_of_countable lazyTwoDimensionalStep)

/-- Helper toward Proposition 3.9: each integer-time increment has the
exact uniform law on the three printed steps, with their signs unchanged. -/
theorem uibotSourceWalk_increment_law (t : ℤ) :
    wholePlaneIIDCodeMeasure.map (fun W =>
      wholePlaneWordIntegral W (t + 1) - wholePlaneWordIntegral W t) =
      Measure.uniformOfFinset ({(1, -1), (-1, 0), (0, 1)} : Finset (ℤ × ℤ)) := by
  simp only [uibotSourceWalk_increment]
  change wholePlaneIIDCodeMeasure.map (lazyTwoDimensionalStep ∘ (fun W => W t)) = _
  rw [← Measure.map_map (measurable_of_countable lazyTwoDimensionalStep)
    (measurable_pi_apply t), wholePlaneIIDCodeMeasure, Measure.infinitePi_map_eval,
    uniformCodeMeasure, map_uniform_lazyTwoDimensionalStep]
  congr 1
  decide

/-- Helper toward Proposition 3.9: each one-sided KMSW run used in the
whole-plane union reads precisely the increments of the normalized source
walk after its start at minus N. This fixes the time-index convention. -/
theorem uibotSourceWalk_shifted_increment (W : ℤ → Fin 3) (N j : ℕ) :
    wholePlaneWordIntegral W (((j + 1 : ℕ) : ℤ) - N) -
        wholePlaneWordIntegral W ((j : ℤ) - N) =
      lazyTwoDimensionalStep (shiftedStream W N j) := by
  rw [show ((j + 1 : ℕ) : ℤ) - N = ((j : ℤ) - N) + 1 by omega]
  exact uibotSourceWalk_increment W ((j : ℤ) - N)

/-- Helper toward Proposition 3.9: the ordinary directed realization on
the original whole-plane edge identities, with presence proved everywhere. -/
@[expose] def uibotWholePlaneSourceDirectedMap (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    DirectedPlaneMap (WholePlaneVertex W) (WholePlaneEdge W) where
  toPlaneGraphDrawing := (uibotWholePlaneSourceMap W H G hp).toPlaneGraphDrawing
  forward e := !(uibotWholePlaneSourceEdgeEquiv W H G e).out.2

/-- Helper toward Proposition 3.9: changing from original edge identities
to geometric edge orbits preserves the entire directed drawing, so geometric
face degree and bipolar triangulation structure transport to the source map. -/
@[expose] def uibotWholePlaneSourceDirectedEquiv (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    DirectedPlaneMap.HomeoEquiv (uibotWholePlaneSourceDirectedMap W H G hp)
      (uibotWholePlaneDirectedMap W H G hp) where
  drawing := {
    h := Homeomorph.refl ℂ
    σV := Equiv.refl _
    σE := uibotWholePlaneSourceEdgeEquiv W H G
    pos_map := by intro _; rfl
    src_map := by intro _; rfl
    tgt_map := by intro _; rfl
    arc_range_map := by
      intro e
      change _ = id '' _
      rw [Set.image_id]
      rfl
    openArc_map := by
      intro e
      change id '' _ = _
      rw [Set.image_id]
      rfl }
  forward_map := by intro _; rfl

/-- Helper toward Proposition 3.9: lambda zero is rooted in its directed
orientation on the original edge carrier, not merely as an unordered edge. -/
theorem uibotWholePlaneSourceDirectedMap_root (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    uibotWholePlaneSourceRoot W H G =
      (wholePlaneEdgeι W 0 0,
        (uibotWholePlaneSourceDirectedMap W H G hp).forward (wholePlaneEdgeι W 0 0)) := rfl

/-- Helper toward Proposition 3.9: the source whole-plane realization on
its original edge IDs is itself an infinite bipolar-oriented triangulation. -/
theorem uibotWholePlaneSourceDirectedMap_bipolarTriangulation (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    Infinite (WholePlaneVertex W) ∧
      (uibotWholePlaneSourceDirectedMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp).IsBipolarTriangulation := by
  obtain ⟨hinf, htri⟩ := uibotWholePlaneDirectedMap_bipolarTriangulation W H h0 hpast hp
  exact ⟨hinf, (uibotWholePlaneSourceDirectedEquiv W H
    (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp).isBipolarTriangulation_map_iff.mpr
      htri⟩

/-- Helper toward Proposition 3.9: every original face of the source
whole-plane drawing on original edge IDs has geometric degree three. -/
theorem uibotWholePlaneSourceDirectedMap_faceDegree (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (F : (uibotWholePlaneSourceDirectedMap W H
      (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp).toPlaneGraphDrawing.Face) :
    (uibotWholePlaneSourceDirectedMap W H
      (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp).toPlaneGraphDrawing.faceDegree F =
        3 := by
  rw [(uibotWholePlaneSourceDirectedEquiv W H
    (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp).drawing.faceDegree_map]
  exact uibotWholePlane_glued_faceDegree W H h0 hpast _

/-- Helper toward Proposition 3.9: one joint full-measure event identifies
the measurable glued class with the normalized walk's whole-plane KMSW
construction, its directed root lambda zero and the initial root vertex.
The same witnesses give a full rooted geometric isomorphism, infinitude,
bipolar triangulation structure, no missing edges and degree three for every
original face. No geometric or recurrence premise is imposed on the iid law. -/
theorem uibotMeasurableWholePlaneClassMap_ae_normalized_source :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      wholePlaneWordIntegral W 0 = (0, 0) ∧
      (∀ t : ℤ, wholePlaneWordIntegral W (t + 1) - wholePlaneWordIntegral W t =
        lazyTwoDimensionalStep (W t)) ∧
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
        let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W =
          Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
        Nonempty (D39GeomRootedMapIsoV2
          (uibotWholePlaneGeometricMap W H G hp) (uibotWholePlaneGeometricRoot W H G)
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)) ∧
        (uibotWholePlaneSourceRoot W H G).1 = wholePlaneEdgeι W 0 0 ∧
        d39GeomRootVertex (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) =
            wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0) ∧
        Infinite (WholePlaneVertex W) ∧
        (uibotWholePlaneDirectedMap W H G hp).IsBipolarTriangulation ∧
        (uibotWholePlaneSourceDirectedMap W H G hp).IsBipolarTriangulation ∧
        uibotWholePlaneSourceRoot W H G =
          (wholePlaneEdgeι W 0 0,
            (uibotWholePlaneSourceDirectedMap W H G hp).forward (wholePlaneEdgeι W 0 0)) ∧
        (∀ e : WholePlaneEdge W, ¬ (uibotWholePlaneSourceMap W H G hp).missing e) ∧
        (∀ v : WholePlaneVertex W,
          (∃ e : WholePlaneEdge W, wholePlaneEdgeWest W e = v) ∧
          (∃ e : WholePlaneEdge W, wholePlaneEdgeEast W e = v)) ∧
        ∀ F : G.toPlaneGraphDrawing.Face, G.toPlaneGraphDrawing.faceDegree F = 3 := by
  filter_upwards [uibotMeasurableWholePlaneClassMap_ae_source] with W hW
  obtain ⟨H, h0, hpast, hp, heq, hinf, htri⟩ := hW
  let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
  have hroot := uibotWholePlaneSourceRoot_spec W H G hp
  exact ⟨uibotSourceWalk_zero W, uibotSourceWalk_increment W,
    H, h0, hpast, hp, heq, ⟨(uibotWholePlaneSourceIso W H G hp).symm⟩,
    hroot.1, hroot.2, hinf, htri,
    (uibotWholePlaneSourceDirectedMap_bipolarTriangulation W H h0 hpast hp).2,
    uibotWholePlaneSourceDirectedMap_root W H G hp,
    uibotWholePlaneSourceMap_noMissing W H G hp,
    uibotWholePlane_noPoles W h0 hpast, uibotWholePlane_glued_faceDegree W H h0 hpast⟩



























end DirectedDistances.PaperProofs.Section3
end
