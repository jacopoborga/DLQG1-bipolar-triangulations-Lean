/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization2

/-! # Geometric edge identities toward Proposition 3.9 -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5

/-- Helper toward Proposition 3.9: quotienting the two darts of an edge
retains exactly its edge identity, including parallel edges. -/
@[expose] def uibotDrawingEdgeEquiv {E V : Type*}
    {rot : Equiv.Perm (E × Bool)} {vert : E × Bool → V}
    (P : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot vert) :
    P.GeometricEdge ≃ E where
  toFun e := e.out.1
  invFun e := Quotient.mk P.edgeSetoid (e, false)
  left_inv e := by
    calc
      Quotient.mk P.edgeSetoid (e.out.1, false) = Quotient.mk P.edgeSetoid e.out := by
        apply Quotient.sound
        rcases e.out with ⟨a, b⟩
        cases b
        · exact Or.inl rfl
        · exact Or.inr rfl
      _ = e := Quotient.out_eq e
  right_inv e := by
    rcases P.geometricEdge_out_mk (e, false) with h | h
    · exact congrArg Prod.fst h
    · exact congrArg Prod.fst h

/-- Helper toward Proposition 3.9: the edge identity of any dart class is
the original edge, independently of the chosen quotient representative. -/
theorem uibotDrawingEdgeEquiv_mk {E V : Type*}
    {rot : Equiv.Perm (E × Bool)} {vert : E × Bool → V}
    (P : PLDrawing (E × Bool) V (fun d => (d.1, !d.2)) rot vert)
    (e : E) (b : Bool) :
    uibotDrawingEdgeEquiv P (Quotient.mk P.edgeSetoid (e, b)) = e := by
  rcases P.geometricEdge_out_mk (e, b) with h | h
  · exact congrArg Prod.fst h
  · exact congrArg Prod.fst h

/-- Helper toward Proposition 3.9: the finite geometric induced-edge
predicate is exactly the stage endpoint predicate on its individual edge ID. -/
theorem uibotFiniteGeometricBallEdge_iff {w : ℕ → Fin 3} {n : ℕ}
    (P : StageDrawing w n) (Q : StageGeom w n P)
    (k : ℕ) (hk : k ≤ n) (r : ℕ) (e : P.GeometricEdge) :
    e ∈ d39GeomBallEdges (kmswStageDrawingDirectedPlaneMap P Q)
      (uibotFiniteStageGeometricRoot P k hk) r ↔
    (kmswStage w n).west e.out.1.val ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r (activeInitial w k) ∧
    (kmswStage w n).east e.out.1.val ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r (activeInitial w k) := by
  change (stageVertex w n e.out ∈ _ ∧ stageVertex w n (edgeFlip _ e.out) ∈ _) ↔ _
  rw [uibotFiniteStageGeometricBallVertices_iff, uibotFiniteStageGeometricBallVertices_iff]
  rcases e.out with ⟨a, b⟩
  cases b
  · rfl
  · exact and_comm

/-- Helper toward Proposition 3.9: the whole-plane geometric induced-edge
predicate is exactly the colimit endpoint predicate on its individual edge ID. -/
theorem uibotWholePlaneGeometricBallEdge_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (r : ℕ) (e : G.GeometricEdge) :
    e ∈ d39GeomBallEdges (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r ↔
    wholePlaneEdgeWest W e.out.1 ∈
      wholePlaneBallVertices W r (wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0)) ∧
    wholePlaneEdgeEast W e.out.1 ∈
      wholePlaneBallVertices W r (wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0)) := by
  change (wholePlaneDartVertex W e.out ∈ _ ∧
    wholePlaneDartVertex W (wholePlaneDartFlip W e.out) ∈ _) ↔ _
  rw [uibotWholePlaneGeometricBallVertices_eq_colimit]
  rcases e.out with ⟨a, b⟩
  cases b
  · rfl
  · exact and_comm

/-- Helper toward Proposition 3.9: the finite geometric ball-edge carrier
is equivalent to the allocated stage IDs with both endpoints in the ball. -/
@[expose] def uibotFiniteGeometricBallEdgeEquiv {w : ℕ → Fin 3} {n : ℕ}
    (P : StageDrawing w n) (Q : StageGeom w n P)
    (k : ℕ) (hk : k ≤ n) (r : ℕ) :
    {e // e ∈ d39GeomBallEdges (kmswStageDrawingDirectedPlaneMap P Q)
      (uibotFiniteStageGeometricRoot P k hk) r} ≃
    {e : Fin (kmswStage w n).nextEdge //
      (kmswStage w n).west e.val ∈
        kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r (activeInitial w k) ∧
      (kmswStage w n).east e.val ∈
        kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r (activeInitial w k)} :=
  (uibotDrawingEdgeEquiv P).subtypeEquiv
    (uibotFiniteGeometricBallEdge_iff P Q k hk r)

/-- Helper toward Proposition 3.9: the whole-plane geometric ball-edge
carrier is equivalent to the colimit IDs with both endpoints in the ball. -/
@[expose] def uibotWholePlaneGeometricBallEdgeEquiv (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) (r : ℕ) :
    {e // e ∈ d39GeomBallEdges (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r} ≃
    {e : WholePlaneEdge W //
      wholePlaneEdgeWest W e ∈
        wholePlaneBallVertices W r (wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0)) ∧
      wholePlaneEdgeEast W e ∈
        wholePlaneBallVertices W r (wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0))} :=
  (uibotDrawingEdgeEquiv G).subtypeEquiv
    (uibotWholePlaneGeometricBallEdge_iff W H G hp r)

/-- Helper toward Proposition 3.9: agreeing captured windows identify the
actual geometric edge quotients. The action uses the infinite window map,
which fixes edge identities independently of endpoint storage. -/
theorem uibotFiniteRootWindow_geometricEdgeEquiv {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (Q : StageGeom (finiteCodeExtend w) (n - 1) P)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    ∃ E : {e // e ∈ d39GeomBallEdges (kmswStageDrawingDirectedPlaneMap P Q)
        (uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega)) r} ≃
      {e // e ∈ d39GeomBallEdges (uibotWholePlaneGeometricMap W H G hp)
        (uibotWholePlaneGeometricRoot W H G) r},
      ∀ e a, e.val.out.1.val = kmswWindowEdgeMapInf (finiteCodeExtend w)
        (j.val - N) a → (E e).val.out.1 = wholePlaneEdgeι W N a := by
  classical
  let u := shiftedStream W N
  let s := j.val - N
  let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r
    (activeInitial u N)
  obtain ⟨_, hcode⟩ := uibotFiniteRootWindow_codeAgreement w j u hwindow
  have hs : kmswStage (fun i => finiteCodeExtend w (s + i)) (2 * N) =
      kmswStage u (2 * N) := kmswStage_congr hcode
  have hf := uibotFiniteRootWindow_rootBallEdges_bijOn w j u hwindow hcap
  dsimp only at hf
  let A := uibotFiniteGeometricBallEdgeEquiv P Q j.val
    (by have := j.isLt; omega) r
  let B := uibotWholePlaneGeometricBallEdgeEquiv W H G hp r
  let C : {e : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge //
      (kmswStage (finiteCodeExtend w) (n - 1)).west e.val ∈
        kmswStageBallVertices (fun _ _ => True)
          (kmswStage (finiteCodeExtend w) (n - 1)) r (activeInitial (finiteCodeExtend w) j.val) ∧
      (kmswStage (finiteCodeExtend w) (n - 1)).east e.val ∈
        kmswStageBallVertices (fun _ _ => True)
          (kmswStage (finiteCodeExtend w) (n - 1)) r (activeInitial (finiteCodeExtend w) j.val)} ≃
      {e : ℕ // e < (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge ∧
      (kmswStage (finiteCodeExtend w) (n - 1)).west e ∈
        kmswStageBallVertices (fun _ _ => True)
          (kmswStage (finiteCodeExtend w) (n - 1)) r (activeInitial (finiteCodeExtend w) j.val) ∧
      (kmswStage (finiteCodeExtend w) (n - 1)).east e ∈
        kmswStageBallVertices (fun _ _ => True)
          (kmswStage (finiteCodeExtend w) (n - 1)) r (activeInitial (finiteCodeExtend w) j.val)} := {
    toFun e := ⟨e.val.val, e.val.isLt, e.property⟩
    invFun e := ⟨⟨e.val, e.property.1⟩, e.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hg : Set.BijOn
      (fun e : Fin (kmswStage (fun i => finiteCodeExtend w (s + i)) (2 * N)).nextEdge =>
        wholePlaneEdgeι W N e.val)
      (kmswWindowFreshSetSourceEdges (finiteCodeExtend w) s (2 * N) S)
      {e | wholePlaneEdgeWest W e ∈
          wholePlaneBallVertices W r (wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0)) ∧
        wholePlaneEdgeEast W e ∈
          wholePlaneBallVertices W r (wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0))} := by
    unfold kmswWindowFreshSetSourceEdges
    rw [hs]
    exact uibotWholePlane_rootBallEdges_bijOn W N r hcap
  let F := hf.equiv _
  let J := hg.equiv _
  let E := (A.trans C).trans (F.symm.trans (J.trans B.symm))
  refine ⟨E, ?_⟩
  intro e a he
  let x := F.symm ((A.trans C) e)
  have hx : (kmswWindowFreshSetEdgeMap (finiteCodeExtend w) s (2 * N) x.val).val =
      e.val.out.1.val := congrArg Subtype.val (F.apply_symm_apply ((A.trans C) e))
  have hxa : x.val.val = a := by
    apply kmswWindowEdgeMapInf_injective (finiteCodeExtend w) s
    rw [kmswWindowEdgeMapInf_eq_stage _ _ (2 * N) _ x.val.isLt]
    exact hx.trans he
  have hout : (E e).val.out.1 = wholePlaneEdgeι W N x.val.val :=
    congrArg Subtype.val (B.apply_symm_apply (J x))
  exact hout.trans (congrArg (wholePlaneEdgeι W N) hxa)

private theorem uibotStageLL_mono (w : ℕ → Fin 3) {n m e : ℕ}
    (hnm : n ≤ m) (he : e ∈ (kmswStage w n).LL) :
    e ∈ (kmswStage w m).LL := by
  induction m, hnm using Nat.le_induction with
  | base => exact he
  | succ m hm ih =>
    change e ∈ (kmswStep (kmswStage w m) (w m)).LL
    unfold kmswStep
    cases hc : kmswCodeStep (w m) with
    | down =>
      cases hs : (kmswStage w m).UR <;>
        simpa [kmswStepOfStep, hs, State.addEdge] using ih
    | up => simpa only [kmswStepOfStep, State.addEdge] using ih
    | left =>
      cases hs : (kmswStage w m).UL.dropLast.reverse with
      | cons a as => simpa only [kmswStepOfStep, hs, State.addEdge] using ih
      | nil =>
        simpa only [kmswStepOfStep, hs, State.addEdge, List.mem_cons] using (Or.inr ih)

/-- Helper toward Proposition 3.9: an edge incident to a captured window
vertex is already present at the window end when all colimit edges are present. -/
theorem uibotCapturedWindowEdge_present (W : ℤ → Fin 3) (N r : ℕ)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (e : Fin (kmswStage (shiftedStream W N) (2 * N)).nextEdge)
    (he : (kmswStage (shiftedStream W N) (2 * N)).west e.val ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) (2 * N)) r
        (activeInitial (shiftedStream W N) N)) :
    (kmswStage (shiftedStream W N) (2 * N)).present e.val = true := by
  let u := shiftedStream W N
  let v := (kmswStage u (2 * N)).west e.val
  have hv : v < (kmswStage u (2 * N)).nextVertex :=
    (kmswStage_endpoints_lt_nextVertex u (2 * N) e.val e.isLt).1
  have hnon := hcap.1.2.1 v he
  have hf : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM (edgeWest u e.val) := by
    intro M hNM
    have hc : ∀ i < 2 * N, shiftedStream W M (M - N + i) = u i := by
      intro i _
      exact congrFun (shiftedStream_shift W N M hNM) i
    have hv' : v < (kmswStage (fun i => shiftedStream W M (M - N + i)) (2 * N)).nextVertex := by
      rw [kmswStage_congr hc]
      exact hv
    change (kmswStage (shiftedStream W M) (M - N)).nextVertex ≤
      kmswWindowVertexMapInf (shiftedStream W M) (M - N) (edgeWest u e.val)
    rw [← (edge_endpoints_eq u e.isLt).1,
      kmswWindowVertexMapInf_eq_stage _ _ (2 * N) _ hv']
    exact kmswWindowPatchVertexMap_fresh_for_every_prefix u (2 * N) v hv
      hnon.1 hnon.2 (shiftedStream W M) (M - N) hc
  have hpRun : EdgePresent u e.val :=
    (wholePlaneEdgePresent_ι_of_fresh W N e.val false hf).mp (hp _)
  by_contra hnot
  change ¬ (kmswStage u (2 * N)).present e.val = true at hnot
  have hfalse : (kmswStage u (2 * N)).present e.val = false := by
    cases hh : (kmswStage u (2 * N)).present e.val
    · rfl
    · exact (hnot hh).elim
  rcases ((kmswStage_status u (2 * N)).1 e.val e.isLt).mp hfalse with hUR | hLL
  · exact hcap.2 v he (Or.inl ⟨e.val, List.mem_append_right _ hUR, Or.inl rfl⟩)
  · obtain ⟨m, hm⟩ := hpRun.eventually_present
    have ht := hm (max m (2 * N)) (Nat.le_max_left _ _)
    have hLL' := uibotStageLL_mono u (Nat.le_max_right m (2 * N)) hLL
    have hfalse' := ((kmswStage_status u (max m (2 * N))).1 e.val ht.1).mpr (Or.inr hLL')
    rw [ht.2] at hfalse'
    contradiction

/-- Helper toward Proposition 3.9: every geometric edge in the captured
finite ball is present; missing boundary edges outside the ball are untouched. -/
theorem uibotFiniteRootWindow_geometricBall_noMissing {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (W : ℤ → Fin 3)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (Q : StageGeom (finiteCodeExtend w) (n - 1) P)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (e : {e // e ∈ d39GeomBallEdges (kmswStageDrawingDirectedPlaneMap P Q)
      (uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega)) r}) :
    ¬ (kmswStageDrawingDirectedPlaneMap P Q).missing e.val := by
  classical
  let u := shiftedStream W N
  let s := j.val - N
  let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r (activeInitial u N)
  obtain ⟨hvalid, hcode⟩ := uibotFiniteRootWindow_codeAgreement w j u hwindow
  have hs : kmswStage (fun i => finiteCodeExtend w (s + i)) (2 * N) =
      kmswStage u (2 * N) := kmswStage_congr hcode
  have hn : s + 2 * N ≤ n - 1 := by
    have := hvalid.1
    have := hvalid.2
    dsimp [s]
    omega
  have hmem := (uibotFiniteGeometricBallEdge_iff P Q j.val
    (by have := j.isLt; omega) r e.val).mp e.property
  obtain ⟨a, ha, hae⟩ := (uibotFiniteRootWindow_rootBallEdges_bijOn
    w j u hwindow hcap).2.2 ⟨e.val.out.1.isLt, hmem⟩
  have ha' : (kmswStage u (2 * N)).west a.val ∈ S ∧
      (kmswStage u (2 * N)).east a.val ∈ S := by
    change (kmswStage (fun i => finiteCodeExtend w (s + i)) (2 * N)).west a.val ∈ S ∧
      (kmswStage (fun i => finiteCodeExtend w (s + i)) (2 * N)).east a.val ∈ S at ha
    rwa [congrArg State.west hs, congrArg State.east hs] at ha
  have hab : a.val < (kmswStage u (2 * N)).nextEdge := by
    rw [← congrArg State.nextEdge hs]
    exact a.isLt
  have hpSource := uibotCapturedWindowEdge_present W N r hp hcap ⟨a.val, hab⟩ ha'.1
  have hfresh : ∀ v ∈ S,
      v < (kmswStage (fun i => finiteCodeExtend w (s + i)) (2 * N)).nextVertex ∧
        (kmswStage (finiteCodeExtend w) s).nextVertex ≤
          kmswWindowPatchVertexMap (finiteCodeExtend w) s (2 * N) v := by
    intro v hv
    have hb := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
    refine ⟨by rw [hs]; exact hb, ?_⟩
    exact kmswWindowPatchVertexMap_fresh_for_every_prefix u (2 * N) v hb
      (hcap.1.2.1 v hv).1 (hcap.1.2.1 v hv).2 (finiteCodeExtend w) s hcode
  have hpres := kmswWindowFreshSetEdgeMap_present (finiteCodeExtend w) s (2 * N) S
    hfresh ⟨a, ha⟩
  rw [congrArg State.present hs] at hpres
  have hpEnd : (kmswStage (finiteCodeExtend w) (s + 2 * N)).present
      (kmswWindowFreshSetEdgeMap (finiteCodeExtend w) s (2 * N) a).val = true :=
    hpres.symm.trans hpSource
  have hpFinal := (present_mono (finiteCodeExtend w)
    (kmswWindowFreshSetEdgeMap (finiteCodeExtend w) s (2 * N) a).isLt hpEnd (n - 1) hn).2
  change (kmswWindowFreshSetEdgeMap (finiteCodeExtend w) s (2 * N) a).val =
    e.val.out.1.val at hae
  rw [hae] at hpFinal
  change ¬ (kmswStage (finiteCodeExtend w) (n - 1)).present e.val.out.1.val = false
  rw [hpFinal]
  decide

/-- Helper toward Proposition 3.9: the geometric edge equivalence preserves
missing tags, directed orientation and the ordered chronological root. The
Boolean flip compensates exactly for the two quotient endpoint choices. -/
theorem uibotFiniteRootWindow_geometricEdgeData {n N r : ℕ} (hr : 0 < r)
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (Q : StageGeom (finiteCodeExtend w) (n - 1) P)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    let M := kmswStageDrawingDirectedPlaneMap P Q
    let rho := uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega)
    let M' := uibotWholePlaneGeometricMap W H G hp
    let rho' := uibotWholePlaneGeometricRoot W H G
    ∃ E : {e // e ∈ d39GeomBallEdges M rho r} ≃
      {e // e ∈ d39GeomBallEdges M' rho' r},
      (∀ e a, e.val.out.1.val = kmswWindowEdgeMapInf (finiteCodeExtend w)
        (j.val - N) a → (E e).val.out.1 = wholePlaneEdgeι W N a) ∧
      (∀ e, M'.missing (E e).val ↔ M.missing e.val) ∧
      (∀ e (he : ¬ M.missing e.val),
        M'.forward ⟨(E e).val, uibotWholePlaneGeometricMap_noMissing W H G hp _⟩ =
          Bool.xor (M.forward ⟨e.val, he⟩) (Bool.xor e.val.out.2 (E e).val.out.2)) ∧
      (E ⟨rho.1, d39GeomRootEdge_mem M rho hr⟩).val = rho'.1 ∧
      rho'.2 = Bool.xor rho.2
        (Bool.xor rho.1.out.2 (E ⟨rho.1, d39GeomRootEdge_mem M rho hr⟩).val.out.2) := by
  classical
  dsimp only
  obtain ⟨E, hE⟩ := uibotFiniteRootWindow_geometricEdgeEquiv w j W H G hp P Q hwindow hcap
  let M := kmswStageDrawingDirectedPlaneMap P Q
  let rho := uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega)
  let M' := uibotWholePlaneGeometricMap W H G hp
  let rho' := uibotWholePlaneGeometricRoot W H G
  let e : {e // e ∈ d39GeomBallEdges M rho r} := ⟨rho.1, d39GeomRootEdge_mem M rho hr⟩
  have hroot : (E e).val = rho'.1 := by
    obtain ⟨hv, hc⟩ := uibotFiniteRootWindow_codeAgreement w j (shiftedStream W N) hwindow
    have hs : j.val - N + N = j.val := by have := hv.1; omega
    have ha : act (fun i => finiteCodeExtend w (j.val - N + i)) N =
        act (shiftedStream W N) N :=
      congrArg State.active (kmswStage_congr (fun i hi => hc i (by omega)))
    have hmap := uibotWindowEdgeMapInf_act (finiteCodeExtend w) (j.val - N) N
    rw [ha, hs] at hmap
    have hid : e.val.out.1.val = act (finiteCodeExtend w) j.val :=
      congrArg Fin.val (uibotDrawingEdgeEquiv_mk P
        ⟨act (finiteCodeExtend w) j.val, act_lt_nextEdge _ (by have := j.isLt; omega)⟩ false)
    have hout := hE e (act (shiftedStream W N) N) (hid.trans hmap.symm)
    apply (uibotDrawingEdgeEquiv G).injective
    change (E e).val.out.1 = rho'.1.out.1
    rw [hout, uibotWholePlane_centerRootEdge]
    exact (uibotDrawingEdgeEquiv_mk G (wholePlaneEdgeι W 0 0) false).symm
  refine ⟨E, hE, ?_, ?_, hroot, ?_⟩
  · intro a
    exact iff_of_false (uibotWholePlaneGeometricMap_noMissing W H G hp _)
      (uibotFiniteRootWindow_geometricBall_noMissing w j W hp P Q hwindow hcap a)
  · intro a ha
    change (!((E a).val.out.2)) = Bool.xor (!a.val.out.2)
      (Bool.xor a.val.out.2 (E a).val.out.2)
    cases a.val.out.2 <;> cases (E a).val.out.2 <;> rfl
  · change rho'.2 = Bool.xor rho.2 (Bool.xor rho.1.out.2 (E e).val.out.2)
    rw [hroot]
    change (!rho'.1.out.2) = Bool.xor (!rho.1.out.2) (Bool.xor rho.1.out.2 rho'.1.out.2)
    cases rho.1.out.2 <;> cases rho'.1.out.2 <;> rfl

private theorem uibotFiniteRootWindow_edge_witness {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r)
    (e : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge)
    (he : (kmswStage (finiteCodeExtend w) (n - 1)).west e.val ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage (finiteCodeExtend w) (n - 1)) r
        (activeInitial (finiteCodeExtend w) j.val) ∧
      (kmswStage (finiteCodeExtend w) (n - 1)).east e.val ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage (finiteCodeExtend w) (n - 1)) r
        (activeInitial (finiteCodeExtend w) j.val)) :
    ∃ a : Fin (kmswStage u (2 * N)).nextEdge,
      (kmswStage u (2 * N)).west a.val ∈
        kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r (activeInitial u N) ∧
      (kmswStage u (2 * N)).east a.val ∈
        kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r (activeInitial u N) ∧
      e.val = kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.val ∧
      (kmswStage (finiteCodeExtend w) (n - 1)).west e.val =
        kmswWindowPatchVertexMap (finiteCodeExtend w) (j.val - N) (2 * N)
          ((kmswStage u (2 * N)).west a.val) ∧
      (kmswStage (finiteCodeExtend w) (n - 1)).east e.val =
        kmswWindowPatchVertexMap (finiteCodeExtend w) (j.val - N) (2 * N)
          ((kmswStage u (2 * N)).east a.val) := by
  obtain ⟨hv, hc⟩ := uibotFiniteRootWindow_codeAgreement w j u hwindow
  have hs := kmswStage_congr hc
  have hn : j.val - N + 2 * N ≤ n - 1 := by
    have := hv.1
    have := hv.2
    omega
  obtain ⟨a, ha, hae⟩ := (uibotFiniteRootWindow_rootBallEdges_bijOn w j u hwindow hcap).2.2
    ⟨e.isLt, he⟩
  have ha' := ha
  change (kmswStage (fun i => finiteCodeExtend w (j.val - N + i)) (2 * N)).west a.val ∈ _ ∧
    (kmswStage (fun i => finiteCodeExtend w (j.val - N + i)) (2 * N)).east a.val ∈ _ at ha'
  rw [congrArg State.west hs, congrArg State.east hs] at ha'
  have hab : a.val < (kmswStage u (2 * N)).nextEdge := by
    rw [← congrArg State.nextEdge hs]
    exact a.isLt
  refine ⟨⟨a.val, hab⟩, ha'.1, ha'.2, ?_, ?_, ?_⟩
  · rw [kmswWindowEdgeMapInf_eq_stage _ _ (2 * N) _ a.isLt]
    exact hae.symm
  · have hst := (kmswStage_endpoints_stable (finiteCodeExtend w) hn
        (kmswWindowFreshSetEdgeMap (finiteCodeExtend w) (j.val - N) (2 * N) a).isLt).1
    have hw := kmswWindowFreshSetEdgeMap_west (finiteCodeExtend w) (j.val - N) (2 * N) a
    rw [congrArg State.west hs] at hw
    exact (congrArg (kmswStage (finiteCodeExtend w) (n - 1)).west hae).symm.trans (hst.trans hw)
  · have hst := (kmswStage_endpoints_stable (finiteCodeExtend w) hn
        (kmswWindowFreshSetEdgeMap (finiteCodeExtend w) (j.val - N) (2 * N) a).isLt).2
    have hw := kmswWindowFreshSetEdgeMap_east (finiteCodeExtend w) (j.val - N) (2 * N) a
    rw [congrArg State.east hs] at hw
    exact (congrArg (kmswStage (finiteCodeExtend w) (n - 1)).east hae).symm.trans (hst.trans hw)

/-- Helper toward Proposition 3.9: the same captured-window vertex and
edge equivalences preserve both ordered endpoints, all missing tags, directed
orientations, and the ordered chronological root. No geometric extension or
retained-face correspondence is inferred from these incidence fields. -/
theorem uibotFiniteRootWindow_geometricIncidenceData {n N r : ℕ} (hr : 0 < r)
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (Q : StageGeom (finiteCodeExtend w) (n - 1) P)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    let M := kmswStageDrawingDirectedPlaneMap P Q
    let rho := uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega)
    let M' := uibotWholePlaneGeometricMap W H G hp
    let rho' := uibotWholePlaneGeometricRoot W H G
    ∃ (V : {v // v ∈ d39GeomBallVertices M rho r} ≃
        {v // v ∈ d39GeomBallVertices M' rho' r})
      (E : {e // e ∈ d39GeomBallEdges M rho r} ≃
        {e // e ∈ d39GeomBallEdges M' rho' r}),
      (∀ e, (V ⟨M.src e.val, e.property.1⟩).val =
        if Bool.xor e.val.out.2 (E e).val.out.2 then M'.tgt (E e).val
        else M'.src (E e).val) ∧
      (∀ e, (V ⟨M.tgt e.val, e.property.2⟩).val =
        if Bool.xor e.val.out.2 (E e).val.out.2 then M'.src (E e).val
        else M'.tgt (E e).val) ∧
      (∀ e, M'.missing (E e).val ↔ M.missing e.val) ∧
      (∀ e (he : ¬ M.missing e.val),
        M'.forward ⟨(E e).val, uibotWholePlaneGeometricMap_noMissing W H G hp _⟩ =
          Bool.xor (M.forward ⟨e.val, he⟩) (Bool.xor e.val.out.2 (E e).val.out.2)) ∧
      (E ⟨rho.1, d39GeomRootEdge_mem M rho hr⟩).val = rho'.1 ∧
      rho'.2 = Bool.xor rho.2
        (Bool.xor rho.1.out.2 (E ⟨rho.1, d39GeomRootEdge_mem M rho hr⟩).val.out.2) := by
  classical
  dsimp only
  obtain ⟨V, hV⟩ := uibotFiniteRootWindow_geometricVertexEquiv w j W H G hp P Q hwindow hcap
  obtain ⟨E, hE, hmissing, horient, hroot, hbool⟩ :=
    uibotFiniteRootWindow_geometricEdgeData hr w j W H G hp P Q hwindow hcap
  let M := kmswStageDrawingDirectedPlaneMap P Q
  let rho := uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega)
  let M' := uibotWholePlaneGeometricMap W H G hp
  have hends (e : {e // e ∈ d39GeomBallEdges M rho r}) :
      ∃ (vwest veast : {v // v ∈ d39GeomBallVertices M rho r}),
        vwest.val.val = (kmswStage (finiteCodeExtend w) (n - 1)).west e.val.out.1.val ∧
        veast.val.val = (kmswStage (finiteCodeExtend w) (n - 1)).east e.val.out.1.val ∧
        (V vwest).val = wholePlaneEdgeWest W (E e).val.out.1 ∧
        (V veast).val = wholePlaneEdgeEast W (E e).val.out.1 := by
    have he := (uibotFiniteGeometricBallEdge_iff P Q j.val
      (by have := j.isLt; omega) r e.val).mp e.property
    obtain ⟨a, haw, hae, hid, hw, ht⟩ :=
      uibotFiniteRootWindow_edge_witness w j (shiftedStream W N) hwindow hcap e.val.out.1 he
    have hb := kmswStage_endpoints_lt_nextVertex (finiteCodeExtend w) (n - 1)
      e.val.out.1.val e.val.out.1.isLt
    let vw : {v // v ∈ d39GeomBallVertices M rho r} := ⟨⟨_, hb.1⟩,
      (uibotFiniteStageGeometricBallVertices_iff P Q j.val
        (by have := j.isLt; omega) r _).mpr he.1⟩
    let vt : {v // v ∈ d39GeomBallVertices M rho r} := ⟨⟨_, hb.2⟩,
      (uibotFiniteStageGeometricBallVertices_iff P Q j.val
        (by have := j.isLt; omega) r _).mpr he.2⟩
    refine ⟨vw, vt, rfl, rfl, ?_, ?_⟩
    · rw [hE e a.val hid, wholePlaneEdgeWest_ι, ← (edge_endpoints_eq _ a.isLt).1]
      exact hV _ haw vw hw
    · rw [hE e a.val hid, wholePlaneEdgeEast_ι, ← (edge_endpoints_eq _ a.isLt).2]
      exact hV _ hae vt ht
  refine ⟨V, E, ?_, ?_, hmissing, horient, hroot, hbool⟩
  · intro e
    obtain ⟨vw, vt, hw, ht, hVw, hVt⟩ := hends e
    have hs : M.src e.val = if e.val.out.2 then vt.val else vw.val := by
      apply Fin.ext
      change stageEndpoint _ e.val.out = _
      cases hb : e.val.out.2 <;> simp [stageEndpoint, hb, hw, ht]
    have hvs : (⟨M.src e.val, e.property.1⟩ : {v // v ∈ d39GeomBallVertices M rho r}) =
        if e.val.out.2 then vt else vw := by
      cases hb : e.val.out.2 <;> apply Subtype.ext <;> simpa [hb] using hs
    change (V ⟨M.src e.val, e.property.1⟩).val = _
    rw [hvs]
    change (V (if e.val.out.2 then vt else vw)).val =
      if Bool.xor e.val.out.2 (E e).val.out.2 then
        wholePlaneDartVertex W (wholePlaneDartFlip W (E e).val.out)
      else wholePlaneDartVertex W (E e).val.out
    rcases hc : (E e).val.out with ⟨a, b⟩
    have hVw' : (V vw).val = wholePlaneEdgeWest W a :=
      hVw.trans (congrArg (wholePlaneEdgeWest W) (congrArg Prod.fst hc))
    have hVt' : (V vt).val = wholePlaneEdgeEast W a :=
      hVt.trans (congrArg (wholePlaneEdgeEast W) (congrArg Prod.fst hc))
    cases hb : e.val.out.2 <;> cases b
    · exact hVw'
    · exact hVw'
    · exact hVt'
    · exact hVt'
  · intro e
    obtain ⟨vw, vt, hw, ht, hVw, hVt⟩ := hends e
    have hs : M.tgt e.val = if e.val.out.2 then vw.val else vt.val := by
      apply Fin.ext
      change stageEndpoint _ (edgeFlip _ e.val.out) = _
      cases hb : e.val.out.2 <;> simp [stageEndpoint, edgeFlip, hb, hw, ht]
    have hvs : (⟨M.tgt e.val, e.property.2⟩ : {v // v ∈ d39GeomBallVertices M rho r}) =
        if e.val.out.2 then vw else vt := by
      cases hb : e.val.out.2 <;> apply Subtype.ext <;> simpa [hb] using hs
    change (V ⟨M.tgt e.val, e.property.2⟩).val = _
    rw [hvs]
    change (V (if e.val.out.2 then vw else vt)).val =
      if Bool.xor e.val.out.2 (E e).val.out.2 then
        wholePlaneDartVertex W (E e).val.out
      else wholePlaneDartVertex W (wholePlaneDartFlip W (E e).val.out)
    rcases hc : (E e).val.out with ⟨a, b⟩
    have hVw' : (V vw).val = wholePlaneEdgeWest W a :=
      hVw.trans (congrArg (wholePlaneEdgeWest W) (congrArg Prod.fst hc))
    have hVt' : (V vt).val = wholePlaneEdgeEast W a :=
      hVt.trans (congrArg (wholePlaneEdgeEast W) (congrArg Prod.fst hc))
    cases hb : e.val.out.2 <;> cases b
    · exact hVt'
    · exact hVt'
    · exact hVw'
    · exact hVw'















































end DirectedDistances.PaperProofs.Section3
end
