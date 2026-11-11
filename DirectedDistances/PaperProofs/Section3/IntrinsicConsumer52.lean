/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicStageIdentification
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart7
public import DirectedDistances.PaperProofs.Section3.UIBOTLawStatementsSections135
public import DirectedDistances.Paper.Section5.DirectedContain
public import DirectedDistances.PaperProofs.Section5.GeoInftyIndFourTuple
import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSide
import DirectedDistances.KMSW.PrimedHattedGluingBoundary














public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open MeasureTheory Quiver

section Transport

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) A.map A.root)

/-- Helper toward Proposition 3.9: the vertex map of the stopped KMSW
future, followed by the supplied representative isomorphism. -/
@[expose] def intrinsicConsumer52StoppedVertex (t : ℕ)
    (v : PresentVertex (fun i => shiftedStream W 0 (t + i))) : A.V :=
  I.vertexEquiv (wholePlaneVertexι W 0 (shiftLimitVertex (shiftedStream W 0) t v).id)

/-- Helper toward Proposition 3.9: each present stopped edge is transported
with its individual edge identity, including parallel edges. -/
@[expose] def intrinsicConsumer52StoppedEdge (t : ℕ)
    (e : {e : ℕ // EdgePresent (fun i => shiftedStream W 0 (t + i)) e}) : A.E :=
  I.edgeEquiv (wholePlaneEdgeι W 0 (shiftLimitEdge (shiftedStream W 0) t e))

/-- Helper toward Proposition 3.9: the stopped edge map is injective on
the actual directed edge carrier. -/
theorem intrinsicConsumer52StoppedEdge_injective (t : ℕ) :
    Function.Injective (intrinsicConsumer52StoppedEdge W H G hp A I t) := by
  intro e f hef
  exact shiftLimitEdge_injective (shiftedStream W 0) t
    (wholePlaneEdgeι_injective W 0 (I.edgeEquiv.injective hef))

/-- Helper toward Proposition 3.9: stopped edges retain their actual
ambient orientation and both endpoints in the representative. -/
theorem intrinsicConsumer52StoppedEdge_incidence (t : ℕ)
    (e : {e : ℕ // EdgePresent (fun i => shiftedStream W 0 (t + i)) e}) :
    let E := intrinsicConsumer52StoppedEdge W H G hp A I t e
    ∃ he : ¬ A.map.missing E,
      A.map.tail ⟨E, he⟩ = intrinsicConsumer52StoppedVertex W H G hp A I t
        ⟨edgeWest (fun i => shiftedStream W 0 (t + i)) e.val⟩ ∧
      A.map.head ⟨E, he⟩ = intrinsicConsumer52StoppedVertex W H G hp A I t
        ⟨edgeEast (fun i => shiftedStream W 0 (t + i)) e.val⟩ := by
  let f := wholePlaneEdgeι W 0 (shiftLimitEdge (shiftedStream W 0) t e)
  have he₀ : ¬ (uibotWholePlaneSourceMap W H G hp).missing f := fun hm => hm (hp f)
  have ht := intrinsicDirected_tail_map
    (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I ⟨f, he₀⟩
  have hh := intrinsicDirected_head_map
    (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I ⟨f, he₀⟩
  have hend := uibotWholePlaneSourceMap_endpoints W H G hp f
  have hshift := shiftLimitEdge_incidence (shiftedStream W 0) t e
  refine ⟨fun hm => he₀ ((I.missing_map f).mp hm), ?_, ?_⟩
  · exact ht.symm.trans ((congrArg I.vertexEquiv hend.1).trans
      (congrArg I.vertexEquiv ((wholePlaneEdgeWest_ι W 0 _).trans
        (congrArg (wholePlaneVertexι W 0) hshift.1))))
  · exact hh.symm.trans ((congrArg I.vertexEquiv hend.2).trans
      (congrArg I.vertexEquiv ((wholePlaneEdgeEast_ι W 0 _).trans
        (congrArg (wholePlaneVertexι W 0) hshift.2))))

/-- Helper toward Proposition 3.9: the stopped root edge is the transported
active edge at the same time, with no reindexing. -/
theorem intrinsicConsumer52StoppedEdge_root (t : ℕ) :
    intrinsicConsumer52StoppedEdge W H G hp A I t
      ⟨0, futureMap_root_present _⟩ =
      (intrinsicStageActiveEdges W H G hp A I t).val := by
  exact congrArg (fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e))
    (shiftLimitEdge_root (shiftedStream W 0) t (futureMap_root_present _))

/-- Helper toward Proposition 3.9: the compressed hatted vertex map,
followed by the stopped-future map into the representative. -/
@[expose] def intrinsicConsumer52HatVertex (t : ℕ)
    (hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t + i))) (v : ℕ) : A.V :=
  intrinsicConsumer52StoppedVertex W H G hp A I t
    ⟨hatLimitVertexMap (fun i => shiftedStream W 0 (t + i)) hτ v⟩

/-- Helper toward Proposition 3.9: the compressed hatted edges are
transported into the representative through their proved present-edge image. -/
@[expose] def intrinsicConsumer52HatEdge (t : ℕ)
    (hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t + i))) (e : ℕ) : A.E :=
  intrinsicConsumer52StoppedEdge W H G hp A I t
    ⟨hatLimitEdgeMap (fun i => shiftedStream W 0 (t + i)) hτ e,
      ((hatLimitEdgeMap_range_iff _ hτ _).mp ⟨e, rfl⟩).1⟩

/-- Helper toward Proposition 3.9: no two compressed hatted edges are
identified by the transported stopped-map embedding. -/
theorem intrinsicConsumer52HatEdge_injective (t : ℕ)
    (hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t + i))) :
    Function.Injective (intrinsicConsumer52HatEdge W H G hp A I t hτ) := by
  intro e f hef
  have hh := intrinsicConsumer52StoppedEdge_injective W H G hp A I t hef
  exact hatLimitEdgeMap_injective _ hτ (congrArg Subtype.val hh)

/-- Helper toward Proposition 3.9: the hatted code's edges have their
actual directed endpoints in the representative, after both embeddings. -/
theorem intrinsicConsumer52HatEdge_incidence (t : ℕ)
    (hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t + i))) (e : ℕ) :
    let u := fun i => shiftedStream W 0 (t + i)
    let E := intrinsicConsumer52HatEdge W H G hp A I t hτ e
    ∃ he : ¬ A.map.missing E,
      A.map.tail ⟨E, he⟩ = intrinsicConsumer52HatVertex W H G hp A I t hτ
        (edgeWest (hatCodes u hτ) e) ∧
      A.map.head ⟨E, he⟩ = intrinsicConsumer52HatVertex W H G hp A I t hτ
        (edgeEast (hatCodes u hτ) e) := by
  obtain ⟨he, ht, hh⟩ := intrinsicConsumer52StoppedEdge_incidence W H G hp A I t
    ⟨hatLimitEdgeMap _ hτ e, ((hatLimitEdgeMap_range_iff _ hτ _).mp ⟨e, rfl⟩).1⟩
  have halign := hatLimitEdgeMap_endpoint_alignment _ hτ e
  refine ⟨he, ?_, ?_⟩
  · rw [halign.1] at ht
    exact ht
  · rw [halign.2] at hh
    exact hh

/-- Helper toward Proposition 3.9: the hatted root edge is the same
transported active edge as the stopped raw root edge. -/
theorem intrinsicConsumer52HatEdge_root (t : ℕ)
    (hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t + i))) :
    intrinsicConsumer52HatEdge W H G hp A I t hτ 0 =
      (intrinsicStageActiveEdges W H G hp A I t).val := by
  unfold intrinsicConsumer52HatEdge
  simp only [hatLimitEdgeMap_zero]
  exact intrinsicConsumer52StoppedEdge_root W H G hp A I t

end Transport

/-- Helper toward Proposition 3.9: every finite level event of the extended
boundary time is measurable in the code past, including boundary index zero. -/
theorem intrinsicConsumer52_stopping_events (k : ℤ) (n : ℕ) :
    MeasurableSet[DirectedDistances.RandomWalk.codePast n]
      {ω | boundaryCodeStoppingTime k ω = n} :=
  measurableSet_codePast_boundaryCodeStoppingTime_eq k n

section Cut

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "D" => m0CutData W H h (fun _ _ => hp _)

/-- Helper toward Proposition 3.9: any intrinsic cut has exactly the
transported cut edges, missing flags and boundary labels; uniqueness supplies
the identification without a coordinate premise. -/
theorem intrinsicConsumer52_cut_coordinates
    (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G) A.map A.root) (C : IntrinsicFutureCut2 A) :
    C.edges = I.edgeEquiv '' (D).edges ∧
      C.missing = (fun e => (D).missing (I.edgeEquiv.symm e)) ∧
      C.x = (fun k => I.vertexEquiv ((D).x k)) := by
  obtain ⟨C', _, he, _, _, hm, _, _, hx, _⟩ :=
    uibotCut2_in_representative W H h hpast hp A I
  have hCC := uibotCut2_unique W H h hpast hp A I C' C
  subst C'
  refine ⟨he, ?_, funext hx⟩
  funext e
  exact propext (by simpa only [Equiv.apply_symm_apply] using hm (I.edgeEquiv.symm e))

/-- Helper toward Proposition 3.9: the transported time is the least
active-initial visit to the unique cut's intrinsic label, for all integers. -/
theorem intrinsicConsumer52_isLeast
    (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G) A.map A.root) (C : IntrinsicFutureCut2 A)
    (k : ℤ) :
    IsLeast {n : ℕ | C.x k = intrinsicStageActiveInitial A
      (intrinsicStageActiveEdges W H G hp A I) n}
      (intrinsicStageBoundaryTime W H h (fun _ _ => hp _) G hp A I k) := by
  rw [(intrinsicConsumer52_cut_coordinates W H h hpast hp A I C).2.2,
    intrinsicStageBoundaryTime_eq]
  exact intrinsicStage_boundaryHitTime_isLeast W H h (fun _ _ => hp _) G hp A I k

/-- Helper toward Proposition 3.9: every intrinsic finite or infinite cut
path has the edge-preserving stopped lift, using intrinsic labels and flags. -/
theorem intrinsicConsumer52_containment
    (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G) A.map A.root) (C : IntrinsicFutureCut2 A)
    (k : ℤ) :
    IntrinsicStageShiftContainment W A
      (fun j => I.vertexEquiv (wholePlaneVertexι W 0 j))
      (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j)) C.edges C.missing (C.x k)
      (intrinsicStageBoundaryTime W H h (fun _ _ => hp _) G hp A I k) := by
  obtain ⟨he, hm, hx⟩ := intrinsicConsumer52_cut_coordinates W H h hpast hp A I C
  rw [he, hm, hx]
  exact intrinsicStageShiftContainment_image W H h (fun _ _ => hp _) G hp A I k

end Cut

/-- Helper toward Proposition 3.9: on one iid conull event every
representative has a unique intrinsic cut, and every source isomorphism
identifies its least visits and full finite/infinite containment. All clauses
of the installed Lemma 5.2 anchor are retained with their common witnesses.
The rooted-map certificate remains in KMSW coordinates; the representative
stopped-edge maps above establish directed incidence, not geometric faces. -/
theorem intrinsicConsumer52_sample :
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
              hatLawCodes (boundaryFutureCode k W) =
                hatCodes (fun i => shiftedStream W 0 (t k + i)) hτ ∧
              hatRootedMapClause (fun i => shiftedStream W 0 (t k + i)) hτ hfin ∧
              Function.Injective (intrinsicConsumer52HatEdge W H G hp A I (t k) hτ) ∧
              intrinsicConsumer52HatEdge W H G hp A I (t k) hτ 0 =
                (intrinsicStageActiveEdges W H G hp A I (t k)).val ∧
              ∀ e : ℕ, ∃ he : ¬ A.map.missing
                  (intrinsicConsumer52HatEdge W H G hp A I (t k) hτ e),
                A.map.tail ⟨intrinsicConsumer52HatEdge W H G hp A I (t k) hτ e, he⟩ =
                  intrinsicConsumer52HatVertex W H G hp A I (t k) hτ
                    (edgeWest (hatCodes (fun i => shiftedStream W 0 (t k + i)) hτ) e) ∧
                A.map.head ⟨intrinsicConsumer52HatEdge W H G hp A I (t k) hτ e, he⟩ =
                  intrinsicConsumer52HatVertex W H G hp A I (t k) hτ
                    (edgeEast (hatCodes (fun i => shiftedStream W 0 (t k + i)) hτ) e) := by
  filter_upwards [uibotCut2_sample_unique_realization,
    DirectedDistances.Paper.Section5.directed_contain] with W hrep h52
  obtain ⟨H, h, hpast, hp, hrep⟩ := hrep
  obtain ⟨H', h', hLL', h52⟩ := h52
  have hH : H' = H := Subsingleton.elim _ _
  subst H'
  have hh : h' = h := Subsingleton.elim _ _
  subst h'
  let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (k - 1))))
  have hhl : hLL' = hLL := Subsingleton.elim _ _
  subst hLL'
  refine ⟨H, h, hpast, hp, ?_⟩
  dsimp only
  intro A hA
  obtain ⟨hI, C, hC, _⟩ := hrep A hA
  refine ⟨hI, C, ⟨hC.1, ?_⟩, fun C' _ => hC.1 C'⟩
  intro I
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  refine ⟨?_, fun k => ?_⟩
  · rw [intrinsicStageBoundaryTime_eq, boundaryHitTime_zero]
  · have ht := intrinsicStageBoundaryTime_eq W H h hLL G hp A I k
    obtain ⟨hlaw, hhatlaw, hword, hhatword, hpath, hmap⟩ := h52 k
    refine ⟨intrinsicConsumer52_isLeast W H h hpast hp A I C k, ht, ?_,
      hlaw, hhatlaw, ?_, ?_, hpath, hmap,
      intrinsicConsumer52_containment W H h hpast hp A I C k, ?_⟩
    · rw [ht]
      have hω : BoundaryHitWitnesses (fun i => shiftedCodePath W 0 (i + 1)) := by
        rw [shiftedCodePath_tail_eq]
        exact h
      simpa only [shiftedCodePath_tail_eq] using
        rMinus_boundaryCodeStoppingTime_eq_boundaryHitTime k (shiftedCodePath W 0) hω
    · rw [intrinsicStageBoundaryTime_eq]
      exact hword
    · rw [intrinsicStageBoundaryTime_eq]
      exact hhatword
    · rw [intrinsicStageBoundaryTime_eq]
      obtain ⟨hτ, hfin, hcode, hclause⟩ := hmap
      exact ⟨hτ, hfin, hcode, hclause,
        intrinsicConsumer52HatEdge_injective W H G hp A I _ hτ,
        intrinsicConsumer52HatEdge_root W H G hp A I _ hτ,
        intrinsicConsumer52HatEdge_incidence W H G hp A I _ hτ⟩

end DirectedDistances.PaperProofs.Section3
end
