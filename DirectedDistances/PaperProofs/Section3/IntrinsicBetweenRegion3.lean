/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion2
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers54And57











public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 Set

/-- Helper toward Proposition 3.9: for graphs on a common closed half-line,
the first argument of `closedBetween` supplies the upper height bound. -/
theorem intrinsicBetween3_mem_closedBetween_graphRays
    {P R : Set ℂ} {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay P x₀ fP) (hR : IsGraphRay R x₀ fR) (z : ℂ) :
    z ∈ closedBetween P R ↔
      x₀ ≤ z.re ∧ fR z.re ≤ z.im ∧ z.im ≤ fP z.re := by
  rw [closedBetween, hP, hR]
  constructor
  · rintro ⟨⟨r, ⟨hr, hri⟩, hre, him⟩, hup⟩
    refine ⟨hre ▸ hr, ?_, ?_⟩
    · rw [hre] at hri
      exact hri ▸ him
    · exact hup ⟨z.re, fP z.re⟩ ⟨hre ▸ hr, rfl⟩ rfl
  · rintro ⟨hx, hlo, hhi⟩
    refine ⟨⟨⟨z.re, fR z.re⟩, ⟨hx, rfl⟩, rfl, hlo⟩, ?_⟩
    rintro p ⟨_, hp⟩ hpre
    rw [hp, hpre]
    exact hhi

/-- Helper toward Proposition 3.9: the proposed strict region between a
lower first graph and an upper second graph is disjoint from `closedBetween`
in that argument order, independently of any component classification. -/
theorem intrinsicBetween3_strictStrip_disjoint_closedBetween
    {P R : Set ℂ} {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay P x₀ fP) (hR : IsGraphRay R x₀ fR) :
    Disjoint {z : ℂ | x₀ < z.re ∧ fP z.re < z.im ∧ z.im < fR z.re}
      (closedBetween P R) := by
  apply Set.disjoint_left.mpr
  intro z hz hbetween
  have hb := (intrinsicBetween3_mem_closedBetween_graphRays hP hR z).mp hbetween
  exact (not_le_of_gt hz.2.2) hb.2.1

/-- Helper toward Proposition 3.9: equality with the native region forces
the second graph to be below the first on every common vertical fiber,
because the native region contains the complete first trace. -/
theorem intrinsicBetween3_height_le_of_native_eq_closedBetween
    (A : D39DomainRootedMap.{0}) (P R : ℕ → A.E)
    {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay (intrinsicEdgeRayTrace A P) x₀ fP)
    (hR : IsGraphRay (intrinsicEdgeRayTrace A R) x₀ fR)
    (heq : nativeBetween A P R =
      closedBetween (intrinsicEdgeRayTrace A P) (intrinsicEdgeRayTrace A R)) :
    ∀ x : ℝ, x₀ ≤ x → fR x ≤ fP x := by
  intro x hx
  have hp : (⟨x, fP x⟩ : ℂ) ∈ intrinsicEdgeRayTrace A P := by
    rw [hP]
    exact ⟨hx, rfl⟩
  have hn := intrinsicEdgeRayTrace_union_subset_nativeBetween A P R (Or.inl hp)
  rw [heq] at hn
  exact ((intrinsicBetween3_mem_closedBetween_graphRays hP hR _).mp hn).2.1




theorem intrinsicBetween3_native_ne_closedBetween_of_height_lt
    (A : D39DomainRootedMap.{0}) (P R : ℕ → A.E)
    {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay (intrinsicEdgeRayTrace A P) x₀ fP)
    (hR : IsGraphRay (intrinsicEdgeRayTrace A R) x₀ fR)
    (x : ℝ) (hx : x₀ ≤ x) (hlt : fP x < fR x) :
    nativeBetween A P R ≠
      closedBetween (intrinsicEdgeRayTrace A P) (intrinsicEdgeRayTrace A R) := by
  intro heq
  exact (not_le_of_gt hlt)
    (intrinsicBetween3_height_le_of_native_eq_closedBetween A P R hP hR heq x hx)

/-- Helper toward Proposition 3.9: two continuous proper graph rays from
the origin, strictly ordered after their common start, witness that the
lower-first `closedBetween` can collapse to the common start alone. These
are geometric graph sets; no source-map realization is asserted. -/
theorem intrinsicBetween3_lowerFirst_graph_counterexample :
    let P : Set ℂ := {z | 0 ≤ z.re ∧ z.im = z.re}
    let R : Set ℂ := {z | 0 ≤ z.re ∧ z.im = 2 * z.re}
    ProperGraphRay P 0 ∧ ProperGraphRay R 0 ∧
      (0 : ℂ) ∈ P ∩ R ∧
      (∀ x : ℝ, 0 < x → x < 2 * x) ∧ closedBetween P R = {0} := by
  dsimp only
  have hp : ProperGraphRay {z : ℂ | 0 ≤ z.re ∧ z.im = z.re} 0 := by
    refine ⟨⊤, fun x => x, WithTop.coe_lt_top _, continuous_id.continuousOn, ?_, ?_⟩
    · ext z
      simp only [rayDomain, WithTop.coe_lt_top, and_true, mem_ofPred_eq]
    · intro M
      refine ⟨max M 0, ⟨le_max_right _ _, WithTop.coe_lt_top _⟩, ?_⟩
      intro t _ ht
      exact (le_max_left M 0).trans ht
  have hr : ProperGraphRay {z : ℂ | 0 ≤ z.re ∧ z.im = 2 * z.re} 0 := by
    refine ⟨⊤, fun x => 2 * x, WithTop.coe_lt_top _,
      (continuous_const.mul continuous_id).continuousOn, ?_, ?_⟩
    · ext z
      simp only [rayDomain, WithTop.coe_lt_top, and_true, mem_ofPred_eq]
    · intro M
      refine ⟨max M 0, ⟨le_max_right _ _, WithTop.coe_lt_top _⟩, ?_⟩
      intro t ht hmt
      have hM : M ≤ t := (le_max_left M 0).trans hmt
      have ht0 : 0 ≤ t := ht.1
      linarith only [hM, ht0]
  refine ⟨hp, hr, by simp only [mem_inter_iff, mem_ofPred_eq, Complex.zero_re,
    Complex.zero_im, le_refl, mul_zero, and_self], ?_, ?_⟩
  · intro x hx
    linarith only [hx]
  · ext z
    rw [intrinsicBetween3_mem_closedBetween_graphRays
      (x₀ := (0 : ℝ)) (fP := fun x : ℝ => x) (fR := fun x : ℝ => 2 * x)
      rfl rfl, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hlo, hhi⟩
      apply Complex.ext
      · change z.re = 0
        linarith only [hx, hlo, hhi]
      · change z.im = 0
        linarith only [hx, hlo, hhi]
    · intro hz
      subst z
      simp only [Complex.zero_re, Complex.zero_im, mul_zero, le_refl, and_self]

/- EXACT REMAINING STATEMENTS (comments, not declarations or hypotheses).

The continuation's lower-first formulation is obstructed by the theorems
obstruction does not refute them. No qualifier is removed. The notation in
these formulas also opens DirectedDistances.PaperProofs.Section5,
DirectedDistances.PaperProofs.Section7, DirectedDistances.Paper.Section4,
DirectedDistances.RandomWalk, MeasureTheory, and Filter, with Classical scope.

(1) IntrinsicBetweenRegion2.lean:280, full binders:

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
  (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h (k - 1))))
let D := m0CutData W H h hLL
let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
∀ (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root)
  (longest : Bool) (k : ℤ)
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (T : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
  (_ : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
  (_ : T.edge = R.edge),
nativeBetween A
  (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n)))
  (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (T.edge n))) =
  I.h '' closedBetween
    (pathTrace G (fun n => wholePlaneDartι W 0 (P.codePath.edge n, false)))
    (pathTrace G (fun n => wholePlaneDartι W 0 (T.edge n, false))).

(2) IntrinsicBetweenRegion2.lean:316, full binders and shared clauses:

∀ᵐ U ∂wholePlaneIIDCodeMeasure,
  let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U
  let W := uibotRecoveredCode z
  ∃ (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
  let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (k - 1))))
  let D := m0CutData W H h hLL
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∃ s : ∀ x : XDP, M0CutGeodesicSliceWitness W x,
  z = Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
  ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
    Nonempty (D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root) ∧
    ∀ I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root,
    ∀ x : XDP,
    (if x = XDP.ldp then
      IsIntrinsicBusemannLDP A (intrinsicBusemannImageCut W H G hp D A I)
        (fun k => I.vertexEquiv (D.x k)) (identifiedLDPBusemann W)
    else IsIntrinsicBusemannSDP A (intrinsicBusemannImageCut W H G hp D A I)
        (fun k => I.vertexEquiv (D.x k)) (identifiedSDPBusemann W)) ∧
    let P := fun j => intrinsicGeodesicOfCode W H h hLL G hp A I ((s x).P j)
    (∀ k k' : ℤ, ∃ a b : ℕ, IntrinsicEdgeTailsCoalesce (P k).val (P k').val a b) ∧
    (∀ k : ℤ,
      let X := if x = XDP.ldp then identifiedLDPBusemann W else identifiedSDPBusemann W
      IntrinsicLeastEdgeCoalescence (P (k - 1)).val (P k).val
        ((s x).thetaMinus k) ((s x).theta k) ∧
      uibotGeomCoalescenceOffsets z x k = ((s x).thetaMinus k, (s x).theta k) ∧
      uibotCodeCoalescenceOffsets W x k = ((s x).thetaMinus k, (s x).theta k) ∧
      (uibotGeomSideSliceObservables z x k).2 =
        some (geometricSideClass (m0CutGeodesicSlice (hp := (s x).hp) (s x).P k
          ((s x).thetaMinus k) ((s x).theta k) ((s x).least k))) ∧
      X k - X (k - 1) = (((s x).theta k : ℕ) : ℤ) -
        (((s x).thetaMinus k : ℕ) : ℤ)) ∧
    ∀ k : ℤ,
      let S := intrinsicBusemannImageCut W H G hp D A I
      let v := I.vertexEquiv (D.x k)
      let longest := if x = XDP.ldp then true else false
      ∃ T : IntrinsicInfiniteDirectedPath A S v,
        RightmostInCut A S v T ∧
        ∀ Q : IntrinsicInfiniteXDPGeodesic A S v longest,
          IntrinsicLeftmostInRegion A S v longest Q T ↔ Q = P k.

(3) IntrinsicConsumers54And57.lean:242, full binders:

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
  (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h (k - 1))))
let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
∀ (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root)
  (longest : Bool) (k : ℤ)
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (T : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
  (_ : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
  (_ : T.edge = R.edge),
nativeBetween A
  (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n)))
  (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (T.edge n))) =
  I.h '' closedBetween
    (pathTrace G (fun n => wholePlaneDartι W 0 (P.codePath.edge n, false)))
    (pathTrace G (fun n => wholePlaneDartι W 0 (T.edge n, false))).

(4) IntrinsicConsumers54And57.lean:274, full binders:

∀ᵐ U ∂wholePlaneIIDCodeMeasure,
  let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U
  let W := uibotRecoveredCode z
  ∃ (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
  let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (k - 1))))
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∃ s : ∀ x : XDP, M0CutGeodesicSliceWitness W x,
  z = Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
  ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
    Nonempty (D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root) ∧
    ∀ I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root,
    let C := intrinsicFutureCut2Pushforward I (uibotCut2Source W H h hpast hp)
    let S := intrinsicConsumersBusemannCut C
    ∀ (x : XDP) (k : ℤ),
    let longest := if x = XDP.ldp then true else false
    let P := intrinsicConsumersGeodesicOfCode W H h hpast hp A I ((s x).P k)
    IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest P ∧
    ∀ Q : IntrinsicInfiniteXDPGeodesic A S (C.x k) longest,
      IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest Q → Q = P.

The last strengthening must retain every clause of
intrinsicConsumers54And57_sample_ae with the same H, h, hpast, hp, s.
No common-event or native-region conclusion is counted as proved here. -/

end DirectedDistances.PaperProofs.Section3
end
