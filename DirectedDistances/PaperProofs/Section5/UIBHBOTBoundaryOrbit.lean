/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTSourceChainExhaustion
public import DirectedDistances.KMSW.WholePlaneGlueFaceCorrespondenceFull

/-! Boundary darts in the marked whole-plane face orbit, toward Definition 5.8. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk




theorem uibhbotCodeLawRel_ae_sourceChainEastDarts_outerOrbit :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N),
      ∃ e : ℤ → WholePlaneEdge W,
        (∀ k : ℤ,
          wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
          wholePlaneEdgeEast W (e k) =
            (uibhbotBusemannSource (k + 1) W).id ∧
          ¬ wholePlaneEdgePresent W (e k) ∧
          ∃ N n : ℕ, 0 < n ∧
            (n : ℤ) - N = uibhbotBoundaryHitTime k W ∧
            e k = wholePlaneEdgeι W N
              (kmswLLCreatedEdge (shiftedStream W N) n)) ∧
        Function.Injective e ∧ e 0 = uibhbotRootEdge W ∧
        ∀ k : ℤ,
          Equiv.Perm.SameCycle
            ((wholePlaneRotation W H).symm * wholePlaneDartFlip W)
            (uibhbotWholePlaneOuterDart W) (e k, true) := by
  filter_upwards [uibhbotCodeLawRel_ae_wholePlaneDart_acyclic,
    uibhbotCodeLawRel_ae_boundaryHitWitnesses,
    ae_uibhbotBusemannSource_missing_edges] with W hrot hhit hsource
  obtain ⟨H, _, _⟩ := hrot
  obtain ⟨e, hedge, hinj, hroot⟩ := hsource
  refine ⟨H, hhit, e, hedge, hinj, hroot, ?_⟩
  intro k
  have hrootMissing : ¬ wholePlaneEdgePresent W (e 0) := (hedge 0).2.2.1
  have hMissing : ¬ wholePlaneEdgePresent W (e k) := (hedge k).2.2.1
  have hcycle := wholePlane_missing_east_sameCycle W H hhit (e 0) (e k)
    hrootMissing hMissing
  have houter : uibhbotWholePlaneOuterDart W = (e 0, true) := by
    change wholePlaneDartFlip W (uibhbotRootEdge W, false) = (e 0, true)
    rw [← hroot]
    rfl
  rw [houter]
  exact hcycle



private theorem missing_run_edge_boundary_label (W : ℤ → Fin 3) (N e : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N))
    (hm : ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W N e)) :
    ∃ j : ℤ, j ≤ -1 ∧ e = boundaryOuterEdge (shiftedStream W N) h j := by
  have hm' : ¬ EdgePresent (shiftedStream W N) e :=
    fun hp => hm (wholePlaneEdgePresent_ι_of_run_present W N e hp)
  have hR : ∀ a : ℤ, ∃ n, R (shiftedStream W N) n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
    exact ⟨n, by have hmax := le_max_left (-a) 1; omega⟩
  have hd := futureMap_missing_east_external (shiftedStream W N)
    hR e hm'
  obtain ⟨j, hj⟩ := (futureMap_limitExternalDart_iff_boundaryDart
    (shiftedStream W N) h (e, true)).mp hd
  have he : e = boundaryOuterEdge (shiftedStream W N) h j := congrArg Prod.fst hj
  refine ⟨j, ?_, he⟩
  by_contra hneg
  have hp := (boundaryOuterEdge_endpoints (shiftedStream W N) h j).2.2.1 (by omega)
  exact hm' (he ▸ hp)



theorem uibhbotSourceChainEastDart_faceSucc (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (e : ℤ → WholePlaneEdge W)
    (hwest : ∀ k, wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id)
    (heast : ∀ k, wholePlaneEdgeEast W (e k) =
      (uibhbotBusemannSource (k + 1) W).id)
    (hmissing : ∀ k, ¬ wholePlaneEdgePresent W (e k)) (k : ℤ) :
    wholePlaneFaceSucc W H (e k, true) = (e (k - 1), true) := by
  obtain ⟨⟨N, a⟩, ha⟩ := Quotient.exists_rep (e k)
  obtain ⟨⟨M, b⟩, hb⟩ := Quotient.exists_rep (e (k - 1))
  let K := max N M
  have hNK : N ≤ K := Nat.le_max_left N M
  have hMK : M ≤ K := Nat.le_max_right N M
  let aK := wholePlaneEdgeTrans W N K hNK a
  let bK := wholePlaneEdgeTrans W M K hMK b
  have haK : wholePlaneEdgeι W K aK = e k :=
    (congrFun (wholePlaneEdgeι_trans W N K hNK) a).trans ha
  have hbK : wholePlaneEdgeι W K bK = e (k - 1) :=
    (congrFun (wholePlaneEdgeι_trans W M K hMK) b).trans hb
  have hmissA : ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W K aK) := by
    rw [haK]
    exact hmissing k
  have hmissB : ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W K bK) := by
    rw [hbK]
    exact hmissing (k - 1)
  obtain ⟨j, hj, hja⟩ :=
    missing_run_edge_boundary_label W K aK (hhit K) hmissA
  obtain ⟨i, hi, hib⟩ :=
    missing_run_edge_boundary_label W K bK (hhit K) hmissB
  have hsourceEndpoint : wholePlaneEdgeWest W (e k) =
      wholePlaneEdgeEast W (e (k - 1)) := by
    calc
      wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id := hwest k
      _ = (uibhbotBusemannSource ((k - 1) + 1) W).id :=
        congrArg (fun z => (uibhbotBusemannSource z W).id) (by omega)
      _ = wholePlaneEdgeEast W (e (k - 1)) := (heast (k - 1)).symm
  have hlocalEndpoint : edgeWest (shiftedStream W K) aK =
      edgeEast (shiftedStream W K) bK := by
    apply wholePlaneVertexι_injective W K
    have hglobal : wholePlaneEdgeWest W (wholePlaneEdgeι W K aK) =
        wholePlaneEdgeEast W (wholePlaneEdgeι W K bK) := by
      rw [haK, hbK]
      exact hsourceEndpoint
    rw [wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι] at hglobal
    exact hglobal
  have hjEq : j = i + 1 := by
    apply boundaryVertex_injective (shiftedStream W K) (hhit K)
    calc
      boundaryVertex (shiftedStream W K) (hhit K) j =
          edgeWest (shiftedStream W K) (boundaryOuterEdge (shiftedStream W K) (hhit K) j) :=
        (boundaryOuterEdge_endpoints (shiftedStream W K) (hhit K) j).1.symm
      _ = edgeWest (shiftedStream W K) aK := by rw [hja]
      _ = edgeEast (shiftedStream W K) bK := hlocalEndpoint
      _ = edgeEast (shiftedStream W K)
          (boundaryOuterEdge (shiftedStream W K) (hhit K) i) := by rw [hib]
      _ = boundaryVertex (shiftedStream W K) (hhit K) (i + 1) :=
        (boundaryOuterEdge_endpoints (shiftedStream W K) (hhit K) i).2.1
  have hmissLabel : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W K (boundaryOuterEdge (shiftedStream W K) (hhit K) j)) := by
    rw [← hja, haK]
    exact hmissing k
  have hstep := wholePlane_missing_boundary_faceSucc W H K (hhit K) j hj hmissLabel
  have hstart : wholePlaneDartι W K
      (futureMapBoundaryDart (shiftedStream W K) (hhit K) j) = (e k, true) := by
    change (wholePlaneEdgeι W K (boundaryOuterEdge (shiftedStream W K) (hhit K) j), true) = _
    rw [← hja, haK]
  have hend : wholePlaneDartι W K
      (futureMapBoundaryDart (shiftedStream W K) (hhit K) (j - 1)) =
        (e (k - 1), true) := by
    have hij : j - 1 = i := by omega
    change (wholePlaneEdgeι W K (boundaryOuterEdge (shiftedStream W K) (hhit K) (j - 1)), true) = _
    rw [hij, ← hib, hbK]
  rw [hstart, hend] at hstep
  exact hstep.2



private theorem sameCycle_preserves_of_invariant {α : Type*}
    (f : Equiv.Perm α) (P : α → Prop) (x y : α) (hx : P x)
    (hforward : ∀ d, P d → P (f d))
    (hbackward : ∀ d, P d → P (f.symm d))
    (hxy : f.SameCycle x y) : P y := by
  obtain ⟨z, hz⟩ := hxy
  have hpow : ∀ z : ℤ, P ((f ^ z) x) := by
    intro z
    induction z using Int.induction_on with
    | zero => simpa using hx
    | succ z ih =>
      rw [add_comm (z : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply]
      exact hforward _ ih
    | pred z ih =>
      rw [show -(z : ℤ) - 1 = -1 + -(z : ℤ) by omega,
        zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      exact hbackward _ ih
  rw [← hz]
  exact hpow z



theorem uibhbotCodeLawRel_ae_sourceChainEastDarts_outerOrbit_iff :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N),
      ∃ e : ℤ → WholePlaneEdge W,
        (∀ k : ℤ,
          wholePlaneEdgeWest W (e k) = (uibhbotBusemannSource k W).id ∧
          wholePlaneEdgeEast W (e k) =
            (uibhbotBusemannSource (k + 1) W).id ∧
          ¬ wholePlaneEdgePresent W (e k) ∧
          ∃ N n : ℕ, 0 < n ∧
            (n : ℤ) - N = uibhbotBoundaryHitTime k W ∧
            e k = wholePlaneEdgeι W N
              (kmswLLCreatedEdge (shiftedStream W N) n)) ∧
        Function.Injective e ∧ e 0 = uibhbotRootEdge W ∧
        (∀ k : ℤ,
          Equiv.Perm.SameCycle
            ((wholePlaneRotation W H).symm * wholePlaneDartFlip W)
            (uibhbotWholePlaneOuterDart W) (e k, true)) ∧
        ∀ d : WholePlaneDart W,
          Equiv.Perm.SameCycle
            ((wholePlaneRotation W H).symm * wholePlaneDartFlip W)
            (uibhbotWholePlaneOuterDart W) d →
          ∃ k : ℤ, d = (e k, true) := by
  filter_upwards [uibhbotCodeLawRel_ae_sourceChainEastDarts_outerOrbit] with W hsource
  obtain ⟨H, hhit, e, hedge, hinj, hroot, heOrbit⟩ := hsource
  refine ⟨H, hhit, e, hedge, hinj, hroot, heOrbit, ?_⟩
  intro d hd
  let f := wholePlaneFaceSucc W H
  let P : WholePlaneDart W → Prop := fun q => ∃ k : ℤ, q = (e k, true)
  have houter : uibhbotWholePlaneOuterDart W = (e 0, true) := by
    change wholePlaneDartFlip W (uibhbotRootEdge W, false) = (e 0, true)
    rw [← hroot]
    rfl
  have hP : P (uibhbotWholePlaneOuterDart W) := ⟨0, houter⟩
  have hforward : ∀ q, P q → P (f q) := by
    rintro q ⟨k, rfl⟩
    exact ⟨k - 1, uibhbotSourceChainEastDart_faceSucc W H hhit e
      (fun j => (hedge j).1) (fun j => (hedge j).2.1)
      (fun j => (hedge j).2.2.1) k⟩
  have hbackward : ∀ q, P q → P (f.symm q) := by
    rintro q ⟨k, rfl⟩
    have hstep := uibhbotSourceChainEastDart_faceSucc W H hhit e
      (fun j => (hedge j).1) (fun j => (hedge j).2.1)
      (fun j => (hedge j).2.2.1) (k + 1)
    have hstep' : f (e (k + 1), true) = (e k, true) := by
      simpa only [f, show (k + 1) - 1 = k by omega] using hstep
    have hinv : f.symm (e k, true) = (e (k + 1), true) := by
      exact (congrArg f.symm hstep'.symm).trans (f.symm_apply_apply _)
    exact ⟨k + 1, hinv⟩
  have hP' := sameCycle_preserves_of_invariant f P _ d hP
    hforward hbackward hd
  exact hP'



theorem uibhbotSourceChainEastDarts_gluedOuterFace
    (W : ℤ → Fin 3)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (H : WholePlaneRotationHypothesis W)
    (e : ℤ → WholePlaneEdge W)
    (hOrbit : ∀ d : WholePlaneDart W,
      Equiv.Perm.SameCycle
        ((wholePlaneRotation W H).symm * wholePlaneDartFlip W)
        (uibhbotWholePlaneOuterDart W) d ↔
      ∃ k : ℤ, d = (e k, true))
    (d : WholePlaneDart W) :
    (WholePlanePastGlueDrawing.glueDrawing W h0 hp H).dartBorders d
      (WholePlaneGlueFaceCorrespondenceFull.faceOrbitEquiv W h0 hp H
        (Quotient.mk _ (uibhbotWholePlaneOuterDart W))) ↔
      ∃ k : ℤ, d = (e k, true) := by
  rw [WholePlaneGlueFaceCorrespondenceFull.dartBorders_faceOrbitEquiv_iff]
  let S := Equiv.Perm.SameCycle.setoid (wholePlaneFaceSucc W H)
  have hquot : Quotient.mk S d = Quotient.mk S (uibhbotWholePlaneOuterDart W) ↔
      Equiv.Perm.SameCycle
        ((wholePlaneRotation W H).symm * wholePlaneDartFlip W)
        (uibhbotWholePlaneOuterDart W) d := by
    constructor
    · intro h
      exact (Quotient.exact h).symm
    · intro h
      exact Quotient.sound h.symm
  rw [hquot]
  exact hOrbit d

end DirectedDistances.PaperProofs.Section5
