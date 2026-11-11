/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundaryOrder2
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideGlued





public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ}

/-- Helper toward Lemma 5.5: the retained primed root preserves its local
endpoint bit. In particular the beta-boundary bit reversal is not a uniform
rule for the prefix attachment. -/
theorem lPlus_primed_root_dart_bit
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) (b : Bool) :
    (boundaryGluingPrimedEdgeMap W h k hτ 0,
      b ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ 0) =
        (boundaryGluingPrimedEdgeMap W h k hτ 0, b) := by
  rw [primedLimitSideFlip_zero]
  cases b <;> rfl

/-- Helper toward Lemma 5.5: an initial down step makes the first positive
boundary hit occur at stage one. -/
private theorem hit_one_of_first_down
    (hc : shiftedStream W 0 0 = 2) :
    boundaryHitTime (shiftedStream W 0) h 1 = 1 := by
  classical
  have hr : R (shiftedStream W 0) 1 = -1 := by
    simp [R, hc,
      DirectedDistances.RandomWalk.lazyTwoDimensionalStep]
  have hf : Nat.find (h.rightHit 1 (by omega)) = 1 := by
    apply Nat.le_antisymm
    · exact Nat.find_min' _ hr
    · have hs := Nat.find_spec (h.rightHit 1 (by omega))
      by_contra hn
      have hz : Nat.find (h.rightHit 1 (by omega)) = 0 := by omega
      rw [hz] at hs
      change (0 : ℤ) = -1 at hs
      omega
  simpa [boundaryHitTime] using hf

/-- Helper toward Lemma 5.5: after an initial down step the stopped prefix
at the first positive boundary hit has exactly the reverse root dart. -/
theorem lPlus_prefix_one_of_first_down
    (hc : shiftedStream W 0 0 = 2) :
    ((kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h 1)).UL.dropLast.reverse).map
        (fun e => (e, true)) = [(0, true)] := by
  rw [hit_one_of_first_down hc]
  simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep,
    kmswInit, State.addEdge]

/-- Helper toward Lemma 5.5: in the finite down/left configuration the
primed retained root is identified with the prefix root by the defining
window map. This is an edge computation, without an attachment premise. -/
theorem lPlus_primed_root_edge_of_down_left
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h 1))
    (hc₀ : shiftedStream W 0 0 = 2) (hc₁ : shiftedStream W 0 1 = 0) :
    boundaryGluingPrimedEdgeMap W h 1 hτ 0 = 0 := by
  let u := boundaryGluingFutureStream W h 1
  have ht := hit_one_of_first_down (h := h) hc₀
  have hu : u 0 = 0 := by
    change shiftedStream W 0 (boundaryHitTime (shiftedStream W 0) h 1 + 0) = 0
    simpa only [ht, Nat.add_zero] using hc₁
  have hn : walkNL u hτ 0 = 1 := by
    change Nat.find (hτ.1 0) = 1
    apply Nat.le_antisymm
    · apply Nat.find_min'
      refine ⟨le_rfl, ?_⟩
      change L u 1 = L u 0 - 1
      simp [L, hu,
        DirectedDistances.RandomWalk.lazyTwoDimensionalStep]
    · exact (Nat.find_spec (hτ.1 0)).1
  change boundaryGluingEdgeMap W h 1 (primedLimitEdgeMap u hτ 0) = 0
  rw [primedLimitEdgeMap_zero, hn]
  have he : kmswLLCreatedEdge u 1 = 2 := by
    simp [kmswLLCreatedEdge, kmswStage, hu, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge]
  rw [he]
  change kmswWindowEdgeMapInf (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h 1) 2 = 0
  rw [ht, kmswWindowEdgeMapInf_eq_stage (shiftedStream W 0) 1 1 2 (by
    simp [kmswStage, hc₁, kmswStep, kmswCodeStep,
      kmswStepOfStep, kmswInit, State.addEdge])]
  simp [kmswWindowPatchData, KMSWWindowPatchData.step, kmswStage,
    hc₀, hc₁, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]

/-- Helper toward Lemma 5.5: the same down/left configuration maps the
primed west root to vertex zero and its east root to `x₁ = 1`. Consequently
the outward traversal from `x₁` uses bit `true` on both sides. -/
theorem lPlus_primed_root_vertices_of_down_left
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h 1))
    (hc₀ : shiftedStream W 0 0 = 2) (hc₁ : shiftedStream W 0 1 = 0) :
    boundaryGluingPrimedVertexMap W h 1 hτ 0 = 0 ∧
      boundaryGluingPrimedVertexMap W h 1 hτ 1 = 1 := by
  let u := boundaryGluingFutureStream W h 1
  have hp := primedLimitEdgeMap_endpoint_sideflip u hτ 0
  dsimp only at hp
  rw [primedLimitSideFlip_zero] at hp
  obtain ⟨_, hw, he⟩ := hp.resolve_right (by rintro ⟨hf, _⟩; cases hf)
  have hf := boundaryGluing_future_edge_endpoints W h 1
    (primedLimitEdgeMap u hτ 0)
  have hw' := hf.1.trans (congrArg (boundaryGluingFutureVertexMap W h 1) hw)
  have he' := hf.2.trans (congrArg (boundaryGluingFutureVertexMap W h 1) he)
  change edgeWest (shiftedStream W 0) (boundaryGluingPrimedEdgeMap W h 1 hτ 0) =
    boundaryGluingPrimedVertexMap W h 1 hτ 0 at hw'
  change edgeEast (shiftedStream W 0) (boundaryGluingPrimedEdgeMap W h 1 hτ 0) =
    boundaryGluingPrimedVertexMap W h 1 hτ 1 at he'
  rw [lPlus_primed_root_edge_of_down_left hτ hc₀ hc₁] at hw' he'
  exact ⟨hw'.symm, he'.symm⟩

/-- Helper toward Lemma 5.5: in the down/left configuration, requiring the
opposite local bit on the matching first primed edge prevents that traversal
from starting at `x₁`. The corrected local traversal bit is `true`. -/
theorem lPlus_prefix_primed_opposite_bit_obstruction
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h 1))
    (hc₀ : shiftedStream W 0 0 = 2) (hc₁ : shiftedStream W 0 1 = 0) :
    ¬ ∃ (e : ℕ) (b : Bool),
      boundaryGluingPrimedEdgeMap W h 1 hτ e = 0 ∧ b = !true ∧
        boundaryGluingPrimedVertexMap W h 1 hτ
          (kmswDartEndpoint
            (primedCode (primedSimInput (boundaryGluingFutureStream W h 1)) hτ)
            (e, b)) = boundaryVertex (shiftedStream W 0) h 1 := by
  rintro ⟨e, b, he, hb, hv⟩
  have he0 : e = 0 := boundaryGluingPrimedEdgeMap_injective W h 1 hτ
    (he.trans (lPlus_primed_root_edge_of_down_left hτ hc₀ hc₁).symm)
  subst e
  subst b
  change boundaryGluingPrimedVertexMap W h 1 hτ 0 =
    boundaryVertex (shiftedStream W 0) h 1 at hv
  rw [(lPlus_primed_root_vertices_of_down_left hτ hc₀ hc₁).1,
    boundaryVertex_one] at hv
  omega




















































end DirectedDistances.PaperProofs.Section5
