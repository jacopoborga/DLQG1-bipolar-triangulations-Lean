/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.ShiftedStartClosedRegionRoute4
public import DirectedDistances.Paper.Section5.FutureMapLaw

/-! Helper toward Proposition 3.9: the common almost-sure geometric assembly
for Proposition 5.1, on every representative and at every integer start.
does not remove an intrinsic qualifier or assert whole-paper completion. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.IntrinsicConsumer51Assembly

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open ShiftedStartClosedRegionRoute4
open Set Topology MeasureTheory

/-- Helper toward Proposition 3.9: one almost-sure event supplies the global
whole-plane witnesses and every representative isomorphism, together with
the Proposition 5.1 code identities, rooted-map clauses and full geometric
comparisons for both retained edge sets at every integer start. The same
flow, finiteness and boundary witnesses occur in the codes and geometry.
Start isomorphisms exist, and the geometric conclusion holds for each one. -/
theorem ae_proposition51_assembly :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root) ∧
        ∀ (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root) (n : ℤ),
        let u := fun i => futureMapShiftedCodePath n W (i + 1)
        u = shiftedStream (fun k => W (k + n)) 0 ∧
          ∃ (hflow : HasFlowLineHits u) (hfin_hat : hatLimitFiniteIncidence u)
            (hfin_primed : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u),
          hatLawCodes (futureMapShiftedCodePath n W) = hatCodes u hflow ∧
          hatLawPrimedCodes (futureMapShiftedCodePath n W) =
            primedCode (primedSimInput u) hflow ∧
          hatRootedMapClause u hflow hfin_hat ∧
          primedRootedMapClause u hflow hfin_primed hb ∧
          Nonempty (WholePlaneStartIso W n) ∧
          ∀ (J : WholePlaneStartIso W n) (K : Set ℕ),
            K = {e | MhatGeometricEdge u e} ∨
              K = {e | primeGeomEdge u hfin_primed hb e} →
            let U := shiftWordInt W n
            let S := uibotWholePlaneSourceDomain W H G hp
            let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι U 0 v))
            let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι U 0 e))
            let D := fun d => intrinsicFutureDartEquiv (A := S) I
              (uibotCut2SourceDartEquiv W H h hpast hp
                (J.dart (wholePlaneDartι U 0 d)))
            let P := monotoneFamilyDrawing u hfin_hat (monotone_family_all u)
            let T := {d : ℕ × Bool | d.1 ∈ K}
            let Q := restrictDrawing P T (fun _ => Iff.rfl)
            ∃ R : Q.Face → Set ℂ,
              Function.Injective R ∧
              Set.range R = intrinsicConsumer51FaceRegions
                (intrinsicConsumer51Trace A
                  (V '' intrinsicConsumer51RunVertices u K) (E '' K)) ∧
              (∀ F, IsOpen (R F)) ∧
              (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
              (∀ d : T, intrinsicFutureRotation A (E '' K)
                (D (drawingFirstReturnPerm P T d).val) (D d.val)) ∧
              (∀ (d : T) (F : Q.Face),
                (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔
                  Q.dartBorders d F) := by
  filter_upwards [ae_lemma52_assembly,
    DirectedDistances.Paper.Section5.future_map_law.2.2] with W hW hlaw
  obtain ⟨H, h, hpast, hp, hW⟩ := hW
  refine ⟨H, h, hpast, hp, ?_⟩
  intro G A hA
  refine ⟨(hW A hA).1, ?_⟩
  intro I n u
  obtain ⟨hu, hflow, hhat, hprime, hb, hcode, hpcode, hhatclause, hprimeclause⟩ := hlaw n
  refine ⟨hu, hflow, hhat, hprime, hb, hcode, hpcode, hhatclause, hprimeclause,
    wholePlaneStartIso_nonempty W n, ?_⟩
  intro J K hK
  exact proposition51_geometry W H h hpast hp A I n J hflow hhat hprime hb K hK

end DirectedDistances.PaperProofs.Section3.IntrinsicConsumer51Assembly
