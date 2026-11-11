/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart4
public import DirectedDistances.PaperProofs.Section3.UIBOTWholePlaneSourcePart2

/-! # Finite geometric enclosure for code recovery

Finite decoder support and its endpoint stars are enclosed in a finite ball.
This is a dependency of geometric local recovery, not a completion claim. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open MeasureTheory Filter

/-- Helper toward Proposition 3.9: every finite set of vertices in a
connected geometric domain lies in one finite-radius root ball. -/
theorem uibotRecovery_finite_vertices_enclosed {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (hM : D39GeomDomain M rho) (S : Finset V) :
    ∃ r : ℕ, ∀ v ∈ S, v ∈ d39GeomBallVertices M rho r := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp only [Finset.notMem_empty, false_implies, implies_true]⟩
  | @insert v S hv ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨p, hp⟩ := (hM.connected (d39GeomRootVertex M rho) v).exists_walk_length_eq_edist
    refine ⟨max r p.length, ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · change (d39GeomGraph M).edist (d39GeomRootVertex M rho) w ≤ _
      rw [← hp]
      exact_mod_cast Nat.le_max_right r p.length
    · exact D39GeomBallIsoV2.vertexBall_mono (Nat.le_max_left _ _) (hr w hw)

private theorem endpoints_edist_le_one {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (e : E) :
    (d39GeomGraph M).edist (M.src e) (M.tgt e) ≤ 1 := by
  apply SimpleGraph.edist_le_one_iff_adj_or_eq.mpr
  by_cases h : M.src e = M.tgt e
  · exact Or.inr h
  · exact Or.inl ⟨h, e, Or.inl ⟨rfl, rfl⟩⟩

/-- Helper toward Proposition 3.9: the entire geometric edge star of a
vertex at radius `r` is retained at radius `r + 1`, including edge identities
and missing edges. -/
theorem uibotRecovery_star_enclosed {V E : Type*}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (r : ℕ)
    (v : V) (hv : v ∈ d39GeomBallVertices M rho r) (e : E)
    (he : M.src e = v ∨ M.tgt e = v) :
    e ∈ d39GeomBallEdges M rho (r + 1) := by
  have hstep (a b : V) (ha : a ∈ d39GeomBallVertices M rho r)
      (hab : (d39GeomGraph M).edist a b ≤ 1) :
      b ∈ d39GeomBallVertices M rho (r + 1) := by
    change (d39GeomGraph M).edist (d39GeomRootVertex M rho) a ≤ (r : ℕ∞) at ha
    change (d39GeomGraph M).edist (d39GeomRootVertex M rho) b ≤ ((r + 1 : ℕ) : ℕ∞)
    calc
      _ ≤ (d39GeomGraph M).edist (d39GeomRootVertex M rho) a +
        (d39GeomGraph M).edist a b := (d39GeomGraph M).edist_triangle
      _ ≤ (r : ℕ∞) + 1 := add_le_add ha hab
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]
  rcases he with he | he
  · have hs : M.src e ∈ d39GeomBallVertices M rho r := he ▸ hv
    exact ⟨D39GeomBallIsoV2.vertexBall_mono (Nat.le_succ r) hs,
      hstep _ _ hs (endpoints_edist_le_one M e)⟩
  · have ht : M.tgt e ∈ d39GeomBallVertices M rho r := he ▸ hv
    refine ⟨hstep _ _ ht ?_, D39GeomBallIsoV2.vertexBall_mono (Nat.le_succ r) ht⟩
    rw [SimpleGraph.edist_comm]
    exact endpoints_edist_le_one M e

/-- Helper toward Proposition 3.9: each finite collection of whole-plane
darts has both endpoint stars inside one finite geometric ball. The endpoints
themselves lie one radius further inside, so the same interior bound is
transported by a ball isomorphism. -/
theorem uibotRecovery_finite_darts_enclosed
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (hp : ∀ e, wholePlaneEdgePresent W e)
    (S : Finset (WholePlaneDart W)) :
    ∃ r : ℕ, ∀ d ∈ S,
      wholePlaneDartVertex W d ∈ d39GeomBallVertices
        (uibotWholePlaneGeometricMap W H G hp) (uibotWholePlaneGeometricRoot W H G) r ∧
      wholePlaneDartVertex W (wholePlaneDartFlip W d) ∈ d39GeomBallVertices
        (uibotWholePlaneGeometricMap W H G hp) (uibotWholePlaneGeometricRoot W H G) r ∧
      ∀ v : WholePlaneVertex W,
        (v = wholePlaneDartVertex W d ∨ v = wholePlaneDartVertex W (wholePlaneDartFlip W d)) →
        ∀ e : G.GeometricEdge,
          (G.toPlaneGraphDrawing.src e = v ∨ G.toPlaneGraphDrawing.tgt e = v) →
          e ∈ d39GeomBallEdges (uibotWholePlaneGeometricMap W H G hp)
            (uibotWholePlaneGeometricRoot W H G) (r + 1) := by
  classical
  let T := S.image (wholePlaneDartVertex W) ∪
    S.image (fun d => wholePlaneDartVertex W (wholePlaneDartFlip W d))
  obtain ⟨r, hr⟩ := uibotRecovery_finite_vertices_enclosed
    (uibotWholePlaneGeometricMap W H G hp) (uibotWholePlaneGeometricRoot W H G)
    (uibotWholePlaneGeometricMap_domain W H G hp) T
  refine ⟨r, ?_⟩
  intro d hd
  have h1 := hr _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩))
  have h2 := hr _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩))
  refine ⟨h1, h2, ?_⟩
  intro v hv e he
  apply uibotRecovery_star_enclosed _ _ r v _ e he
  rcases hv with rfl | rfl
  · exact h1
  · exact h2

end DirectedDistances.PaperProofs.Section3
end
