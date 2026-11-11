/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTLocalLimitFinal
public import DirectedDistances.KMSW.WholePlaneGlueFaceCorrespondenceFull









public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Proposition 3.9: actual whole-plane KMSW edge identities
are equivalent to the drawing's geometric flip-orbit edges. -/
@[expose] def uibotWholePlaneSourceEdgeEquiv (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H) :
    WholePlaneEdge W ≃ G.GeometricEdge := by
  let f : WholePlaneEdge W → G.GeometricEdge := fun e =>
    Quotient.mk G.edgeSetoid (e, false)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro e e' he
    rcases Quotient.exact he with h | h
    · exact congrArg Prod.fst h
    · exact congrArg Prod.fst h
  · intro q
    refine Quotient.inductionOn q ?_
    rintro ⟨e, b⟩
    refine ⟨e, ?_⟩
    cases b
    · rfl
    · exact Quotient.sound (Or.inr rfl)

/-- Helper toward Proposition 3.9: quotient representatives preserve the
actual edge identity, irrespective of the stored endpoint order. -/
theorem uibotWholePlaneSourceEdgeEquiv_out (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (e : WholePlaneEdge W) :
    (uibotWholePlaneSourceEdgeEquiv W H G e).out.1 = e := by
  rcases G.geometricEdge_out_mk (e, false) with h | h
  · exact congrArg Prod.fst h
  · exact congrArg Prod.fst h

/-- Helper toward Proposition 3.9: the geometric realization of the installed
whole-plane KMSW colimit, on its original vertices and individual edge IDs.
The stored parameterization is inherited from the drawing; directed endpoints
are characterized below and do not depend on that storage choice. -/
@[expose] def uibotWholePlaneSourceMap (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    DirectedPlaneMapWithMissing (WholePlaneVertex W) (WholePlaneEdge W) where
  src e := G.toPlaneGraphDrawing.src (uibotWholePlaneSourceEdgeEquiv W H G e)
  tgt e := G.toPlaneGraphDrawing.tgt (uibotWholePlaneSourceEdgeEquiv W H G e)
  pos := G.pos
  pos_injective := G.pos_injective
  arc e := G.toPlaneGraphDrawing.arc (uibotWholePlaneSourceEdgeEquiv W H G e)
  arc_injOn _e := G.toPlaneGraphDrawing.arc_injOn _
  openArc_disjoint _e _f hef := G.toPlaneGraphDrawing.openArc_disjoint _ _
    (fun he => hef ((uibotWholePlaneSourceEdgeEquiv W H G).injective he))
  openArc_avoids _e v := G.toPlaneGraphDrawing.openArc_avoids _ v
  missing e := ¬ wholePlaneEdgePresent W e
  missing_on_external e he := (he (hp e)).elim
  forward e := !(uibotWholePlaneSourceEdgeEquiv W H G e.val).out.2

/-- Helper toward Proposition 3.9: the source chronological root is the
initial active edge of run zero, with its direction from west to east. -/
@[expose] def uibotWholePlaneSourceRoot (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H) :
    WholePlaneEdge W × Bool :=
  (wholePlaneEdgeι W 0 0,
    !(uibotWholePlaneSourceEdgeEquiv W H G (wholePlaneEdgeι W 0 0)).out.2)

/-- Helper toward Proposition 3.9: a full rooted geometric isomorphism
between the installed colimit realization and the glued-law carrier.
The ambient map is the identity, so all positions, arcs, faces and plane
orientation are retained, in addition to edge identities and the root. -/
@[expose] def uibotWholePlaneSourceIso (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneGeometricMap W H G hp) (uibotWholePlaneGeometricRoot W H G) where
  h := Homeomorph.refl ℂ
  orientationPreserving := orientationPreserving_refl
  vertexEquiv := Equiv.refl _
  edgeEquiv := uibotWholePlaneSourceEdgeEquiv W H G
  edgeFlip := fun _ => false
  edgeParam := fun _ => Homeomorph.refl _
  edgeParam_mono := by intro _ _; exact strictMono_id
  edgeParam_anti := by intro _ hf; cases hf
  pos_map := by intro _; rfl
  arc_map := by intro _ _; rfl
  src_map := by intro _; rfl
  tgt_map := by intro _; rfl
  missing_map := by
    intro e
    change (¬ wholePlaneEdgePresent W
      (uibotWholePlaneSourceEdgeEquiv W H G e).out.1) ↔ ¬ wholePlaneEdgePresent W e
    rw [uibotWholePlaneSourceEdgeEquiv_out]
  orientation_map := by intro _ _; exact (Bool.xor_false _).symm
  root_edge_map := rfl
  root_bool_map := (Bool.xor_false _).symm

/-- Helper toward Proposition 3.9: the source realization's oriented
endpoints are exactly the west and east endpoints of the KMSW colimit. -/
theorem uibotWholePlaneSourceMap_endpoints (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (e : WholePlaneEdge W) :
    (uibotWholePlaneSourceMap W H G hp).tail ⟨e, fun hn => hn (hp e)⟩ =
        wholePlaneEdgeWest W e ∧
      (uibotWholePlaneSourceMap W H G hp).head ⟨e, fun hn => hn (hp e)⟩ =
        wholePlaneEdgeEast W e := by
  have h := uibotWholePlaneGeometricMap_endpoints W H G hp
    (uibotWholePlaneSourceEdgeEquiv W H G e)
  dsimp only at h
  rw [uibotWholePlaneSourceEdgeEquiv_out] at h
  exact h

/-- Helper toward Proposition 3.9: the source root is the installed edge
lambda zero, and its initial vertex is that edge's west endpoint. -/
theorem uibotWholePlaneSourceRoot_spec (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    (uibotWholePlaneSourceRoot W H G).1 = wholePlaneEdgeι W 0 0 ∧
      d39GeomRootVertex (uibotWholePlaneSourceMap W H G hp)
        (uibotWholePlaneSourceRoot W H G) =
          wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0) := by
  exact ⟨rfl, uibotWholePlaneGeometricRoot_initial W H G hp⟩

/-- Helper toward Proposition 3.9: rotation orbits are exactly the installed
whole-plane vertices, without identifying distinct geometric edges. -/
@[expose] def uibotWholePlaneSourceVertexEquiv (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) :
    RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H) ≃
      WholePlaneVertex W := by
  let f : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H) →
      WholePlaneVertex W := Quotient.lift (wholePlaneDartVertex W)
    (fun d e h => (wholePlaneRotation_sameCycle_dartVertex W H d e h).symm)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro v w
    refine Quotient.inductionOn₂ v w ?_
    intro d e he
    exact Quotient.sound (wholePlaneRotation_sameVertex_sameCycle_proof W H d e he)
  · intro v
    obtain ⟨d, hd⟩ := WholePlanePastGlueData.vertex_incident W v
    exact ⟨Quotient.mk _ d, hd⟩

/-- Helper toward Proposition 3.9 (projection lemma): this conclusion is a
direct restatement of the `rotation_agreement` field of `G : WholePlaneDrawing`,
recorded only for later reference; it is not a separate result or source premise. -/
theorem uibotWholePlaneSource_rotation (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (d : WholePlaneDart W) :
    CcwSuccessor {e | wholePlaneDartVertex W e = wholePlaneDartVertex W d}
      (fun e => (G.arc e).initialDirection) d (wholePlaneRotation W H d) :=
  G.rotation_agreement d

/-- Helper toward Proposition 3.9 (projection lemma): this conclusion is a
direct restatement of `hp` via `missing := ¬ wholePlaneEdgePresent`, recorded
only for later reference; it is not a separate result or source premise. -/
theorem uibotWholePlaneSourceMap_noMissing (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (e : WholePlaneEdge W) :
    ¬ (uibotWholePlaneSourceMap W H G hp).missing e :=
  fun hn => hn (hp e)

/-- Helper toward Proposition 3.9: the source colimit is infinite already
on vertices; a whole one-sided run embeds injectively. -/
theorem uibotWholePlaneSource_infinite (W : ℤ → Fin 3) :
    Infinite (WholePlaneVertex W) :=
  Infinite.of_injective (wholePlaneVertexι W 0) (wholePlaneVertexι_injective W 0)

/-- Helper toward Proposition 3.9: the original glued geometric map has
acyclic orientation, by transferring every directed cycle to the installed
whole-plane dart system. -/
theorem uibotWholePlaneGeometricMap_acyclic (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    (uibotWholePlaneGeometricMap W H G hp).IsAcyclic := by
  let e := uibotWholePlaneSourceVertexEquiv W H
  have hstep {v w : WholePlaneVertex W}
      (h : (uibotWholePlaneGeometricMap W H G hp).step v w) :
      rootedLocallyFiniteDirectedStep (wholePlaneRotation W H) (wholePlaneDartFlip W)
        (fun d => ¬ wholePlaneEdgePresent W d.1) (wholePlaneDartTail W)
        (e.symm v) (e.symm w) := by
    obtain ⟨a, ha, hb⟩ := h
    obtain ⟨ht, hh⟩ := uibotWholePlaneGeometricMap_endpoints W H G hp a.val
    refine ⟨(a.val.out.1, false), fun hn => hn (hp _), ⟨by simp only [Bool.false_eq_true, not_false_eq_true], hp _⟩, ?_, ?_⟩
    · apply e.injective
      rw [e.apply_symm_apply]
      exact ht.symm.trans ha
    · apply e.injective
      rw [e.apply_symm_apply]
      exact hh.symm.trans hb
  have hpath {v w : WholePlaneVertex W}
      (h : Relation.TransGen (uibotWholePlaneGeometricMap W H G hp).step v w) :
      Relation.TransGen
        (rootedLocallyFiniteDirectedStep (wholePlaneRotation W H) (wholePlaneDartFlip W)
          (fun d => ¬ wholePlaneEdgePresent W d.1) (wholePlaneDartTail W))
        (e.symm v) (e.symm w) := by
    induction h with
    | single h => exact Relation.TransGen.single (hstep h)
    | tail _ h ih => exact ih.tail (hstep h)
  intro v hv
  exact wholePlaneDart_acyclic W H (e.symm v) (hpath hv)

end DirectedDistances.PaperProofs.Section3
end
