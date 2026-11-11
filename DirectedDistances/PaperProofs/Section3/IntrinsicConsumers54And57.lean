/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion2
public import DirectedDistances.PaperProofs.Section3.IntrinsicGeodesicIdentification
public import DirectedDistances.PaperProofs.Section3.IntrinsicBusemannIdentification
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart6









public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section7 DirectedDistances.Paper.Section4
open DirectedDistances.RandomWalk MeasureTheory Filter
open scoped Classical

/-- Helper toward Proposition 3.9: the actual retained carriers and missing
tags of an intrinsic future cut, as used by intrinsic distances and rays. -/
@[expose] def intrinsicConsumersBusemannCut {A : D39DomainRootedMap.{0}}
    (C : IntrinsicFutureCut2 A) : IntrinsicBusemannCut A :=
  ⟨C.vertices, C.edges, C.missing⟩

section ConstructedCut

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "D" => m0CutData W H h (fun _ _ => hp _)

/- the image-cut data used in the intrinsic Busemann characterization. -/
theorem intrinsicConsumers_constructedCut_data (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root) :
    intrinsicConsumersBusemannCut
        (intrinsicFutureCut2Pushforward I (uibotCut2Source W H h hpast hp)) =
      intrinsicBusemannImageCut W H G hp D A I := rfl

/- Helper toward Proposition 3.9: every integer boundary label of the -/
theorem intrinsicConsumers_constructedCut_boundary (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root) (k : ℤ) :
    (intrinsicFutureCut2Pushforward I (uibotCut2Source W H h hpast hp)).x k =
      I.vertexEquiv ((D).x k) := rfl

/-- Helper toward Proposition 3.9: the whole intrinsic boundary sequence
agrees with the image sequence, with equality of functions. -/
theorem intrinsicConsumers_constructedCut_boundary_fun (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root) :
    (intrinsicFutureCut2Pushforward I (uibotCut2Source W H h hpast hp)).x =
      fun k => I.vertexEquiv ((D).x k) := rfl

/-- Helper toward Proposition 3.9: a code geodesic is a geodesic of the
constructed intrinsic future cut at its own intrinsic boundary label. -/
@[expose] def intrinsicConsumersGeodesicOfCode (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root) {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h (fun _ _ => hp _) k longest) :
    IntrinsicInfiniteXDPGeodesic A
      (intrinsicConsumersBusemannCut
        (intrinsicFutureCut2Pushforward I (uibotCut2Source W H h hpast hp)))
      ((intrinsicFutureCut2Pushforward I (uibotCut2Source W H h hpast hp)).x k)
      longest := by
  change IntrinsicInfiniteXDPGeodesic A
    (intrinsicBusemannImageCut W H G hp D A I) (I.vertexEquiv ((D).x k)) longest
  exact intrinsicGeodesicOfCode W H h (fun _ _ => hp _) G hp A I P

/-- Helper toward Proposition 3.9: the constructed cut geodesic keeps
each individual geometric edge, including parallel edges. -/
theorem intrinsicConsumersGeodesicOfCode_edge (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root) {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h (fun _ _ => hp _) k longest) (n : ℕ) :
    (((intrinsicConsumersGeodesicOfCode W H h hpast hp A I P).val.edge n).val) =
      I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n)) := rfl

end ConstructedCut

/-- Helper toward Proposition 3.9: reversing the order of rays reverses
the two least offsets, without shifting their zero-based edge streams. -/
theorem intrinsicConsumers_least_swap {A : D39DomainRootedMap.{0}}
    {S : IntrinsicBusemannCut A} {u v : A.V}
    {P : IntrinsicInfiniteDirectedPath A S u}
    {Q : IntrinsicInfiniteDirectedPath A S v} {a b : ℕ}
    (hab : IntrinsicLeastEdgeCoalescence P Q a b) :
    IntrinsicLeastEdgeCoalescence Q P b a := by
  refine ⟨fun n => (hab.1 n).symm, ?_⟩
  intro i j hij
  have hh := hab.2 j i (fun n => (hij n).symm)
  exact ⟨hh.2, hh.1⟩

/-- Helper toward Proposition 3.9: the Lemma 5.4 coalescence and Lemma 5.7
increment conclusions hold on one iid event for the constructed intrinsic
future cut, every representative, every produced source isomorphism, both
modes, every normalized intrinsic Busemann sequence and every least pair.
This theorem does not assert native-region leftmostness. -/
theorem intrinsicConsumers54And57_sample_ae :
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
        let C := intrinsicFutureCut2Pushforward I (uibotCut2Source W H h hpast hp)
        let S := intrinsicConsumersBusemannCut C
        (∀ k, C.x k = I.vertexEquiv (D.x k)) ∧
        ∀ x : XDP,
        let longest := if x = XDP.ldp then true else false
        let X₀ := if x = XDP.ldp then identifiedLDPBusemann W
          else identifiedSDPBusemann W
        let P : ∀ k : ℤ, IntrinsicInfiniteXDPGeodesic A S (C.x k) longest :=
          fun k => intrinsicConsumersGeodesicOfCode W H h hpast hp A I ((s x).P k)
        (if x = XDP.ldp then IsIntrinsicBusemannLDP A S C.x X₀
          else IsIntrinsicBusemannSDP A S C.x X₀) ∧
        (∀ X : ℤ → ℤ,
          (if x = XDP.ldp then IsIntrinsicBusemannLDP A S C.x X
            else IsIntrinsicBusemannSDP A S C.x X) → X = X₀) ∧
        (∀ k k' : ℤ, ∃ a b : ℕ,
          IntrinsicEdgeTailsCoalesce (P k).val (P k').val a b) ∧
        (∀ k : ℤ, ∃! q : ℕ × ℕ,
          IntrinsicLeastEdgeCoalescence (P k).val (P (k - 1)).val q.1 q.2) ∧
        (∀ k : ℤ,
          IntrinsicLeastEdgeCoalescence (P k).val (P (k - 1)).val
            ((s x).theta k) ((s x).thetaMinus k) ∧
          uibotGeomCoalescenceOffsets z x k = ((s x).thetaMinus k, (s x).theta k) ∧
          uibotCodeCoalescenceOffsets W x k = ((s x).thetaMinus k, (s x).theta k)) ∧
        ∀ X : ℤ → ℤ,
          (if x = XDP.ldp then IsIntrinsicBusemannLDP A S C.x X
            else IsIntrinsicBusemannSDP A S C.x X) →
          ∀ (k : ℤ) (theta thetaMinus : ℕ),
            IntrinsicLeastEdgeCoalescence (P k).val (P (k - 1)).val theta thetaMinus →
            X k - X (k - 1) = (theta : ℤ) - (thetaMinus : ℤ) := by
  filter_upwards [intrinsicGeodesic_sample_offsets_ae,
    intrinsicBusemann_sample_identification_ae] with U hgeo hbus
  dsimp only at hgeo hbus ⊢
  let W := uibotRecoveredCode
    (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U)
  obtain ⟨H, h, hpast, hp, s, hclass, hrep⟩ := hgeo
  obtain ⟨_, _, H', h', hpast', hp', _, hbrep⟩ := hbus
  have hH : H' = H := Subsingleton.elim _ _
  subst H'
  have hh : h' = h := Subsingleton.elim _ _
  subst h'
  have hhpast : hpast' = hpast := Subsingleton.elim _ _
  subst hpast'
  have hhp : hp' = hp := Subsingleton.elim _ _
  subst hp'
  refine ⟨H, h, hpast, hp, s, hclass, ?_⟩
  intro A hA
  refine ⟨(hrep A hA).1, ?_⟩
  intro I
  dsimp only [intrinsicConsumersGeodesicOfCode]
  simp only [intrinsicConsumers_constructedCut_data,
    intrinsicConsumers_constructedCut_boundary_fun]
  refine ⟨fun _ => True.intro, ?_⟩
  intro x
  obtain ⟨hchar, hcoal, hoff⟩ := (hrep A hA).2 I x
  let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (k - 1))))
  let D := m0CutData W H h hLL
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  have huniq : ∀ X : ℤ → ℤ,
      (if x = XDP.ldp then
        IsIntrinsicBusemannLDP A (intrinsicBusemannImageCut W H G hp D A I)
          (fun k => I.vertexEquiv (D.x k)) X
      else IsIntrinsicBusemannSDP A (intrinsicBusemannImageCut W H G hp D A I)
        (fun k => I.vertexEquiv (D.x k)) X) →
      X = (if x = XDP.ldp then identifiedLDPBusemann W else identifiedSDPBusemann W) := by
    intro X hX
    by_cases hx : x = XDP.ldp
    · simp only [hx, ite_true] at hX ⊢
      exact ((hbrep A hA).2 I).2.2 X hX
    · simp only [hx, ite_false] at hX ⊢
      exact ((hbrep A hA).2 I).1.2 X hX
  refine ⟨?_, huniq, hcoal, ?_, ?_, ?_⟩
  · by_cases hx : x = XDP.ldp
    · simpa only [hx, ite_true] using hchar
    · simpa only [hx, ite_false] using hchar
  · intro k
    have hl := intrinsicConsumers_least_swap (hoff k).1
    refine ⟨((s x).theta k, (s x).thetaMinus k), hl, ?_⟩
    intro q hq
    obtain ⟨ha, hb⟩ := intrinsicLeastEdgeCoalescence_unique hq hl
    exact Prod.ext ha hb
  · intro k
    exact ⟨intrinsicConsumers_least_swap (hoff k).1, (hoff k).2.1,
      (hoff k).2.2.1⟩
  · intro X hX k theta thetaMinus hleast
    rw [huniq X hX]
    have hl := intrinsicConsumers_least_swap (hoff k).1
    obtain ⟨ht, hm⟩ := intrinsicLeastEdgeCoalescence_unique hleast hl
    rw [ht, hm]
    exact (hoff k).2.2.2.2

/- EXACT REMAINING STATEMENTS (comments, not declarations or hypotheses).

The preceding theorem proves intrinsic segment-geodesic existence,
coalescence and the complete increment identity for the constructed cut.
It does not prove native-region leftmost existence or uniqueness.

(1) Native-region identification, the unresolved geometric obstruction:

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

This requires classifying complementary components by the four winding-side
tests and matching their closure with the source vertical-fiber region.
The coincident-ray result from s51 does not handle distinct rays.

(2) Native leftmost existence and uniqueness on the shared iid event:

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

The intended strengthening must retain all clauses of
intrinsicConsumers54And57_sample_ae with the SAME H,h,hpast,hp,s.
Neither native existence nor native uniqueness is counted here. Independent -/

end DirectedDistances.PaperProofs.Section3
end
