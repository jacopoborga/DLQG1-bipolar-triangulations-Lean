/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.ShiftedStartGeometry3
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumer52FaceOrbits
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumer52RootedClauses
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumer51Submaps










public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open MeasureTheory ProbabilityTheory
open scoped Topology





theorem intrinsicConsumers51_inherited_geometry
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root)
    (n : ℤ) (J : WholePlaneStartIso W n) (K : Set ℕ) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let S := uibotWholePlaneSourceDomain W H G hp
    let U := shiftWordInt W n
    let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι U 0 v))
    let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι U 0 e))
    let T := ShiftedStartGeometry.retainedDarts W n K
    let Q := ShiftedStartGeometry.inheritedDrawing W H G n K
    let D := fun d => intrinsicFutureDartEquiv (A := S) I
      (uibotCut2SourceDartEquiv W H h hpast hp d)
    let R := fun F : Q.Face => I.h '' F.val
    Function.Injective R ∧
      Set.range R = intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A
          (V '' intrinsicConsumer51RunVertices (shiftedStream U 0) K) (E '' K)) ∧
      (∀ F, IsOpen (R F)) ∧
      (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
      (∀ d : T, intrinsicFutureRotation A (E '' K)
        (D (drawingFirstReturnPerm G T d).val) (D d.val)) ∧
      (∀ (d : T) (F : Q.Face),
        (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔
          Q.dartBorders d F) := by
  intro G S U V E T Q D R
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F F' hFF
    apply Subtype.ext
    exact Set.image_injective.mpr I.h.injective hFF
  · exact (ShiftedStartGeometry.representative_faceRegions W H h hpast hp A I n J K).symm
  · intro F
    exact I.h.isOpenMap _ (ShiftedStartGeometry.inherited_face_isOpen W H G n K F)
  · exact ShiftedStartGeometry.representative_external W H h hpast hp A I n K
  · intro d
    have he : E '' K = I.edgeEquiv '' (lemma38StartEdgeι W n '' K) := by
      rw [Set.image_image]
      exact congrArg (fun f => f '' K) (funext fun e =>
        congrArg I.edgeEquiv (J.iota_edge e))
    rw [he]
    exact ShiftedStartGeometry.representative_rotation W H h hpast hp A I n K d
  · exact ShiftedStartGeometry.representative_face_side W H h hpast hp A I n K

/-- Helper toward Proposition 3.9: Proposition 5.1's generating laws and
both complete KMSW rooted-map certificates at every integer start, on one
event for every representative and genuine geometric source isomorphism.
The certificates retain their KMSW face coordinates; the preceding theorem
supplies actual inherited region coordinates independently of them. -/
theorem intrinsicConsumers51_laws_and_certificates :
    (∀ n : ℤ, (hatLawCodes ∘ futureMapShiftedCodePath n) ⟂ᵢ[wholePlaneIIDCodeMeasure]
      (hatLawPrimedCodes ∘ futureMapShiftedCodePath n)) ∧
    (∀ n : ℤ, wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ futureMapShiftedCodePath n) =
      iidCodeMeasure.map (fun w => pitmanCode (fun i => w (i + 1)))) ∧
    (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∀ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
        (A : D39DomainRootedMap.{0})
        (I : D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H
            (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
          (uibotWholePlaneSourceRoot W H
            (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root),
      let S := uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
      IntrinsicConsumerFutureMaps W A I.vertexEquiv I.edgeEquiv
        ((uibotCut2SourceDartEquiv W H h hpast hp).trans
          (intrinsicFutureDartEquiv (A := S) I))) := by
  refine ⟨intrinsicConsumers51_generating_laws.1,
    intrinsicConsumers51_generating_laws.2, ?_⟩
  filter_upwards [intrinsicConsumers51_sample] with W hW
  intro H h hpast hp A I S
  exact hW A I.vertexEquiv I.edgeEquiv
    ((uibotCut2SourceDartEquiv W H h hpast hp).trans
      (intrinsicFutureDartEquiv (A := S) I))

/-- Helper toward Proposition 3.9: the Proposition 5.1 certificates at every
start and all currently proved Lemma 5.2 clauses share one representative
event. The intrinsic cut, least stopping times, actual stopped rotation and
complete open complementary regions are retained. These regions are indexed
by the restricted original drawing; identifying them with compressed face
orbits remains an obligation. -/
theorem intrinsicConsumers51And52_sample_with_geometry :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root) ∧
        ∃! C : IntrinsicFutureCut2 A,
          (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
          ∀ I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
            (uibotWholePlaneSourceRoot W H G) A.map A.root,
          IntrinsicConsumerFutureMaps W A I.vertexEquiv I.edgeEquiv
            ((uibotCut2SourceDartEquiv W H h hpast hp).trans
              (intrinsicFutureDartEquiv (A := uibotWholePlaneSourceDomain W H G hp) I)) ∧
          let t := intrinsicStageBoundaryTime W H h hLL G hp A I
          t 0 = 0 ∧
          ∀ k : ℤ,
            IsLeast {n : ℕ | C.x k = intrinsicStageActiveInitial A
              (intrinsicStageActiveEdges W H G hp A I) n} (t k) ∧
            t k = boundaryHitTime (shiftedStream W 0) h k ∧
            boundaryCodeStoppingTime k (shiftedCodePath W 0) = (t k : ℕ∞) ∧
            wholePlaneIIDCodeMeasure.map (boundaryFutureCode k) =
              wholePlaneIIDCodeMeasure.map (boundaryFutureCode 0) ∧
            wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ boundaryFutureCode k) =
              iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) ∧
            (fun i => boundaryFutureCode k W (i + 1)) =
              (fun i => shiftedStream W 0 (t k + i)) ∧
            (∃ hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t k + i)),
              hatLawCodes (boundaryFutureCode k W) =
                hatCodes (fun i => shiftedStream W 0 (t k + i)) hτ) ∧
            M0CutShiftContainment W H h hLL k ∧
            boundaryFutureRootedMapClause W h k ∧
            IntrinsicStageShiftContainment W A
              (fun j => I.vertexEquiv (wholePlaneVertexι W 0 j))
              (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j))
              C.edges C.missing (C.x k) (t k) ∧
            ∃ (hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t k + i)))
              (hfin : hatLimitFiniteIncidence (fun i => shiftedStream W 0 (t k + i))),
            let u := fun i => shiftedStream W 0 (t k + i)
            let V := intrinsicConsumer52HatVertex W H G hp A I (t k) hτ
            let E := intrinsicConsumer52HatEdge W H G hp A I (t k) hτ
            let D := intrinsicConsumer52HatDart W H h hpast hp A I (t k) hτ
            let K := Set.range (intrinsicConsumer52RawHatEdge (shiftedStream W 0) (t k) hτ)
            let T := {d : ℕ × Bool | d.1 ∈ K}
            let P := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
              (monotone_family_all (shiftedStream W 0))
            let Q := restrictDrawing P T (fun _ => Iff.rfl)
            let S := uibotWholePlaneSourceDomain W H G hp
            let J := fun d => intrinsicFutureDartEquiv (A := S) I
              (uibotCut2SourceDartEquiv W H h hpast hp (wholePlaneDartι W 0 d))
            let R := fun F : Q.Face => I.h '' F.val
            hatLawCodes (boundaryFutureCode k W) = hatCodes u hτ ∧
            hatRootedMapClause u hτ hfin ∧
            Function.Injective E ∧
            E 0 = (intrinsicStageActiveEdges W H G hp A I (t k)).val ∧
            (∀ e : ℕ, ∃ he : ¬ A.map.missing (E e),
              A.map.tail ⟨E e, he⟩ = V (edgeWest (hatCodes u hτ) e) ∧
              A.map.head ⟨E e, he⟩ = V (edgeEast (hatCodes u hτ) e)) ∧
            (∀ d, intrinsicFutureRotation A (Set.range E)
              (D (kmswInfRot (hatCodes u hτ) (hatCodes_finiteIncidence u hτ hfin) d))
              (D d)) ∧
            Function.Injective R ∧
            Set.range R = intrinsicConsumer51FaceRegions
              (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
            (∀ F, IsOpen (R F)) ∧
            (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
            (∀ d : T, intrinsicFutureRotation A (Set.range E)
              (J (drawingFirstReturnPerm P T d).val) (J d.val)) ∧
            (∀ (d : T) (F : Q.Face),
              (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (J d.val)) s) ↔
                Q.dartBorders d F) ∧
            (∀ d : ℕ × Bool, ∃! U : Set ℂ,
              U ∈ intrinsicConsumer51FaceRegions
                (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
              IsOpen U ∧ ∀ s, LeftAtOn U (intrinsicFutureDartArc A (D d)) s) := by
  filter_upwards [intrinsicConsumer52_sample,
    intrinsicConsumers51_laws_and_certificates.2.2] with W hW h51
  obtain ⟨H, h, hpast, hp, hW⟩ := hW
  refine ⟨H, h, hpast, hp, ?_⟩
  intro hLL G A hA
  obtain ⟨hI, C, hC, _⟩ := hW A hA
  refine ⟨hI, C, ⟨hC.1, ?_⟩, fun C' _ => hC.1 C'⟩
  intro I
  refine ⟨h51 H h hpast hp A I, ?_⟩
  intro t
  obtain ⟨hzero, hk⟩ := hC.2 I
  refine ⟨hzero, fun k => ?_⟩
  obtain ⟨hleast, ht, hstop, hlaw, hhatlaw, hword, hhatword,
    hpath, hmap, hcontain, hτ, hfin, hcode, hclause, hinj, hroot, hinc⟩ := hk k
  refine ⟨hleast, ht, hstop, hlaw, hhatlaw, hword, hhatword, hpath, hmap, hcontain,
    hτ, hfin, ?_⟩
  dsimp only
  exact ⟨hcode, hclause, hinj, hroot, hinc,
    intrinsicConsumer52Rooted_rotation W H h hpast hp A I (t k) hτ hfin,
    (intrinsicConsumer52Rooted_geometry W H h hpast hp A I (t k) hτ hfin).1,
    (intrinsicConsumer52Rooted_geometry W H h hpast hp A I (t k) hτ hfin).2.1,
    (intrinsicConsumer52Rooted_geometry W H h hpast hp A I (t k) hτ hfin).2.2.1,
    (intrinsicConsumer52Rooted_geometry W H h hpast hp A I (t k) hτ hfin).2.2.2.1,
    (intrinsicConsumer52Rooted_geometry W H h hpast hp A I (t k) hτ hfin).2.2.2.2.1,
    (intrinsicConsumer52Rooted_geometry W H h hpast hp A I (t k) hτ hfin).2.2.2.2.2,
    intrinsicConsumer52_dart_region_existsUnique W H h hpast hp A I (t k) hτ hfin⟩

/- EXACT REMAINING PROPOSITION 5.1 COMPARISON. This is not a declaration or premise.
The theorem above only supplies the inherited drawing's region coordinates.

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∀ (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
    (uibotWholePlaneSourceRoot W H G) A.map A.root)
    (n : ℤ) (J : WholePlaneStartIso W n),
  let u := fun i => futureMapShiftedCodePath n W (i + 1)
  ∀ (hflow : HasFlowLineHits u) (hhat : hatLimitFiniteIncidence u)
    (hprime : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u)
    (K : Set ℕ),
  K = {e | MhatGeometricEdge u e} ∨ K = {e | primeGeomEdge u hprime hb e} →
  let U := shiftWordInt W n
  let S := uibotWholePlaneSourceDomain W H G hp
  let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι U 0 v))
  let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι U 0 e))
  let D := fun d => intrinsicFutureDartEquiv (A := S) I
    (uibotCut2SourceDartEquiv W H h hpast hp (J.dart (wholePlaneDartι U 0 d)))
  let P := monotoneFamilyDrawing u hhat (monotone_family_all u)
  let T := {d : ℕ × Bool | d.1 ∈ K}
  let Q := restrictDrawing P T (fun _ => Iff.rfl)
  ∃ R : Q.Face → Set ℂ,
    Function.Injective R ∧
    Set.range R = intrinsicConsumer51FaceRegions
      (intrinsicConsumer51Trace A (V '' intrinsicConsumer51RunVertices u K) (E '' K)) ∧
    (∀ F, IsOpen (R F)) ∧
    (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
    (∀ d : T, intrinsicFutureRotation A (E '' K)
      (D (drawingFirstReturnPerm P T d).val) (D d.val)) ∧
    (∀ (d : T) (F : Q.Face),
      (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F)

EXACT REMAINING LEMMA 5.2 FACE-ORBIT COMPARISON. Not a declaration or premise.
At k = 0 this is already intrinsicConsumer52_zero_sample. The missing part is
the nonzero case, including exterior identification and exhaustiveness.

∀ᵐ W ∂wholePlaneIIDCodeMeasure,
∀ (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0})
  (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
    (uibotWholePlaneSourceRoot W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root)
  (k : ℤ),
  let t := boundaryHitTime (shiftedStream W 0) h k
  let u := fun i => shiftedStream W 0 (t + i)
  ∀ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let V := intrinsicConsumer52HatVertex W H G hp A I t hτ
  let E := intrinsicConsumer52HatEdge W H G hp A I t hτ
  let D := intrinsicConsumer52HatDart W H h hpast hp A I t hτ
  ∃ R : HatFaceOrbit u hτ hfin → Set ℂ,
    Function.Injective R ∧
    Set.range R = intrinsicConsumer51FaceRegions
      (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
    (∀ q, IsOpen (R q)) ∧
    (∀ d q, (∀ s, LeftAtOn (R q) (intrinsicFutureDartArc A (D d)) s) ↔
      Quotient.mk _ d = q) ∧
    (∀ q, (¬ Bornology.IsBounded (R q)) ↔ q = Quotient.mk _ futureMapOuterDart) ∧
    (∀ d, (∀ s, LeftAtOn (R (Quotient.mk _ futureMapOuterDart))
      (intrinsicFutureDartArc A (D d)) s) ↔ limitExternalDart (hatCodes u hτ) d)

The exact desired complete Lemma 5.2 assembly, with every binder and clause,
is retained at IntrinsicConsumer52FaceOrbits.lean:419–505. Its common-witness
part is now assembled above with all actual restricted geometry available
without the open orbit comparison. No conclusion-equivalent premise is used.

comparison. Its bounded-cell homeomorphism does not establish target-face
exhaustiveness, extend over the exterior, paste with the graph, or prove
orientation preservation. The imported time-zero results stay available. -/

end DirectedDistances.PaperProofs.Section3
