/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop59MirrorCompat9
public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization14
public import DirectedDistances.PlanarMap.PLDrawingBoundedFaces

/-! An infinite ambient face orbit forces the corresponding restricted dart side
into the selected unbounded orbit. The infinitude input is proved below for
the canonical assembly, using its distinct negative boundary edges. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 5.9. Face succession preserves the geometric
left face in any locally finite PL drawing of a local topology rooted map. -/
theorem prop59_faceSucc_border_iff
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (d : M.core.D) (F : P.Face) :
    P.dartBorders ((M.core.rot.symm * M.core.edgeInv) d) F ↔
      P.dartBorders d F := by
  have hv : Function.Surjective (d39VertexClass M) := by
    intro v
    exact ⟨Quotient.out v, Quotient.out_eq' v⟩
  have hrev : M.core.edgeInv
      (M.core.rot ((M.core.rot.symm * M.core.edgeInv) d)) = d := by
    change M.core.edgeInv (M.core.rot (M.core.rot.symm (M.core.edgeInv d))) = d
    rw [Equiv.apply_symm_apply, M.core.edgeInv_invol]
  constructor
  · intro hd
    exact hrev ▸ uibotPLDrawing_border_flip_rot P hv _ F hd
  · intro hd
    obtain ⟨K, hK⟩ := P.dartBorders_exists_of_wedge_compl
      ((M.core.rot.symm * M.core.edgeInv) d)
      (P.wedgeIn_compl_image hv _ _ (P.initial_nonzero _))
    have hdK := hrev ▸ uibotPLDrawing_border_flip_rot P hv _ K hK
    exact P.dartBorders_face_unique d K F hdK hd ▸ hK

/-- Helper toward Proposition 5.9. All darts in one ambient face orbit
border the same geometric face in any locally finite PL drawing. -/
theorem prop59_sameCycle_border_iff
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (d e : M.core.D)
    (hde : Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d e) (F : P.Face) :
    P.dartBorders d F ↔ P.dartBorders e F := by
  let f := M.core.rot.symm * M.core.edgeInv
  have hf (a : M.core.D) : P.dartBorders (f a) F ↔ P.dartBorders a F :=
    prop59_faceSucc_border_iff M P a F
  have hi (a : M.core.D) : P.dartBorders (f.symm a) F ↔ P.dartBorders a F := by
    simpa only [Equiv.apply_symm_apply] using (hf (f.symm a)).symm
  obtain ⟨k, rfl⟩ := hde
  have hpow (k : ℤ) : P.dartBorders ((f ^ k) d) F ↔ P.dartBorders d F := by
    induction k using Int.induction_on with
    | zero => exact Iff.rfl
    | succ k ih =>
      rw [add_comm (k : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply, hf, ih]
    | pred k ih =>
      rw [show -(k : ℤ) - 1 = -1 + -(k : ℤ) by omega,
        zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      exact (hi _).trans ih
  exact (hpow k).symm

/-- Helper toward Proposition 5.9. An infinite ambient face orbit cannot
border a bounded component: local finiteness would make all its darts finite.
Consequently its retained dart lies in the selected restricted exterior. -/
theorem prop59_infiniteFaceOrbit_mem_restrictedExternalOrbit
    (M : D39RootedMap)
    (P : PLDrawing M.core.D (RootedLocallyFiniteVertex M.core.D M.core.rot)
      M.core.edgeInv M.core.rot (d39VertexClass M))
    (r : ℕ) (hr : 0 < r) (d : (d39FacedBall M r hr).D)
    (hinf : {e | Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d.1 e}.Infinite) :
    d ∈ (d39FacedBallPLWithExternal M P r hr).externalOrbit.val := by
  have hv : Function.Surjective (d39VertexClass M) := by
    intro v
    exact ⟨Quotient.out v, Quotient.out_eq' v⟩
  obtain ⟨F, hdF⟩ := P.dartBorders_exists_of_wedge_compl d.1
    (P.wedgeIn_compl_image hv _ _ (P.initial_nonzero _))
  have hF : P.IsUnbounded F := by
    apply P.isUnbounded_of_infinite_borderDarts
    apply hinf.mono
    intro e he
    exact (prop59_sameCycle_border_iff M P d.1 e he F).mp hdF
  exact prop59_ambientUnboundedDartSide_mem_restrictedExternalOrbit M P r hr d F hF hdF




theorem prop59_canonical_outerOrbit_infinite
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n) :
    {d | (wholePlaneFaceSucc W H).SameCycle (uibhbotWholePlaneOuterDart W) d}.Infinite := by
  let P := uibhbotD39PastCanonicalDrawing W hL hR hfin
  let hp := uibhbotD39PastCanonicalDrawing_pos W hL hR hfin
  let ha := uibhbotD39PastCanonicalDrawing_arcImage W hL hR hfin
  let F := uibhbotD39FutureCanonicalDrawing W H h0
  let hf := uibhbotD39FutureCanonicalDrawing_pos W H h0
  let hFim := uibhbotD39FutureCanonicalDrawing_image W H h0
  let hFa := uibhbotD39FutureCanonicalDrawing_arcImage W H h0
  let G := uibhbotCcw_assemblyDrawing W H h0 hL hR hfin P hp ha F hf hFim hFa
  let A := uibhbot_assembly_faceOrbitEquiv
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  obtain ⟨U, hU, hroot, _⟩ := uibhbot_assembly_face_classification
    W H h0 hL hR hfin P hp ha F hf hFim hFa hRpos
  let b : ℕ → WholePlaneDart W := fun n =>
    (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h0 (-(n : ℤ) - 1)), true)
  have hb : Function.Injective b := by
    intro n m heq
    have he : boundaryOuterEdge (shiftedStream W 0) h0 (-(n : ℤ) - 1) =
        boundaryOuterEdge (shiftedStream W 0) h0 (-(m : ℤ) - 1) :=
      wholePlaneEdgeι_injective W 0 (congrArg Prod.fst heq)
    have hv := congrArg (edgeWest (shiftedStream W 0)) he
    rw [(boundaryOuterEdge_endpoints (shiftedStream W 0) h0 _).1,
      (boundaryOuterEdge_endpoints (shiftedStream W 0) h0 _).1] at hv
    have hi := boundaryVertex_injective (shiftedStream W 0) h0 hv
    omega
  apply Set.infinite_of_injective_forall_mem hb
  intro n
  have hborder : G.dartBorders (b n) U :=
    (uibhbot_assembly_unbounded_dartBorders_iff W H h0 hL hR hfin
      P hp ha F hf hFim hFa hRpos U hU (b n)).mpr
        ⟨rfl, uibhbot_assembly_future_negative_missing W h0 hR _ (by omega)⟩
  have heq := ((uibhbot_assembly_faceOrbitEquiv_mk_eq_iff W H h0 hL hR hfin
    P hp ha F hf hFim hFa hRpos _ U).mpr hroot).trans
      ((uibhbot_assembly_faceOrbitEquiv_mk_eq_iff W H h0 hL hR hfin
        P hp ha F hf hFim hFa hRpos _ U).mpr hborder).symm
  exact Quotient.exact (A.injective heq)

/-- Helper toward Proposition 5.9. Reversing the plane preserves infinitude
of the root-side face orbit, with the ordered missing root reversed too. -/
theorem prop59_mirror_rootSideOrbit_infinite
    (M : RootedLocallyFiniteMap)
    (hinf : {d | Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv)
      (M.edgeInv M.frameEdgeDart) d}.Infinite) :
    let N := (mirrorRootedLocallyFiniteMap M).toD39RootedMap
    {d | Equiv.Perm.SameCycle (N.core.rot.symm * N.core.edgeInv)
      (N.core.edgeInv N.rootMark.dart) d}.Infinite := by
  change {d | Equiv.Perm.SameCycle (M.rot * M.edgeInv)
    (M.edgeInv (M.edgeInv M.frameEdgeDart)) d}.Infinite
  apply (hinf.image M.edgeInv.injective.injOn).mono
  rintro d ⟨e, he, rfl⟩
  exact (prop59_mirrorFaceCycle M (M.edgeInv M.frameEdgeDart) e).mpr he

/-- Helper toward Proposition 5.9. Every PL drawing of the canonical
whole-plane map has its reverse-root side in the selected restricted
unbounded orbit, with no geometric orbit-identification assumption. -/
theorem prop59_wholePlane_rootSide_mem_external
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hL : ∀ a : ℤ, a ≤ -1 → ∃ n, L (kmswPastCode W) n = a)
    (hR : ∀ n, 0 ≤ R (kmswPastCode W) n)
    (hfin : KMSWFiniteIncidence (kmswPastCode W))
    (hRpos : ∀ n : ℕ, 0 < n → 0 < R (kmswPastCode W) n)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (P : PLDrawing
      (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).D
      (RootedLocallyFiniteVertex
        (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).D
        (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).rot)
      (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).edgeInv
      (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).rot
      (d39VertexClass (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).toD39RootedMap))
    (r : ℕ) (hr : 0 < r) :
    let M := (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).toD39RootedMap
    (d39FacedBall M r hr).map.edgeInv (d39FacedBall M r hr).rootDart ∈
      (d39FacedBallPLWithExternal M P r hr).externalOrbit.val := by
  apply prop59_infiniteFaceOrbit_mem_restrictedExternalOrbit
  exact prop59_canonical_outerOrbit_infinite W H h0 hL hR hfin hRpos

end DirectedDistances.PaperProofs.Section5

end
