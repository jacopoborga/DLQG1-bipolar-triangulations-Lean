module

public import DirectedDistances.PlanarMap.FacedFramedBall
public import DirectedDistances.PaperProofs.Section5.UIBHBOTBallLawRel
import all DirectedDistances.PaperProofs.Section5.UIBHBOTBallLawRel
public import DirectedDistances.KMSW.KMSWWholePlaneFaces

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory

private def retainedOrbit {A : Type*} (p : Equiv.Perm A) (S : Set A) (x : A) : Prop :=
  ∀ y, p.SameCycle x y → y ∈ S

private theorem retainedOrbit_step {A : Type*} (p : Equiv.Perm A) (S : Set A) (x : A) :
    retainedOrbit p S (p x) ↔ retainedOrbit p S x := by
  exact forall_congr' fun y => imp_congr (Equiv.Perm.sameCycle_apply_left) Iff.rfl

private theorem commute_zpow {A B : Type*} (f : A → B)
    (p : Equiv.Perm A) (q : Equiv.Perm B)
    (h : ∀ x, f (p x) = q (f x)) (i : ℤ) (x : A) :
    f ((p ^ i) x) = (q ^ i) (f x) := by
  have hn (n : ℕ) : ∀ x, f ((p ^ n) x) = (q ^ n) (f x) := by
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, h, ih]
  have hi (x : A) : f (p.symm x) = q.symm (f x) := by
    apply q.injective
    rw [← h, p.apply_symm_apply, q.apply_symm_apply]
  have hneg (n : ℕ) : ∀ x, f ((p.symm ^ n) x) = (q.symm ^ n) (f x) := by
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, hi, ih]
  cases i with
  | ofNat n => exact hn n x
  | negSucc n =>
    simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.inv_def] using hneg (n + 1) x

private theorem retainedOrbit_transport {A B : Type*} [Finite A]
    (p : Equiv.Perm A) (q : Equiv.Perm B) (S : Set A) (T : Set B)
    (f : A → B) (hf : Function.Injective f) (hb : Set.BijOn f S T)
    (hs : ∀ x, x ∈ S → f (p x) = q (f x)) (x : A) :
    retainedOrbit p S x ↔ retainedOrbit q T (f x) := by
  classical
  have hm (a : A) : f a ∈ T ↔ a ∈ S := by
    constructor
    · intro ha
      obtain ⟨b, hb, he⟩ := hb.2.2 ha
      exact hf he ▸ hb
    · exact fun ha => hb.1 ha
  constructor
  · intro hx y hy
    let U := {a | retainedOrbit p S a}
    let P := p.subtypePerm (retainedOrbit_step p S)
    let z : U := ⟨x, hx⟩
    let F : U → B := fun a => f a.1
    have hc (a : U) : F (P a) = q (F a) :=
      hs a.1 (a.2 a.1 (Equiv.Perm.SameCycle.refl _ _))
    obtain ⟨i, hi⟩ := hy
    have he := commute_zpow F P q hc i z
    have ht : F ((P ^ i) z) ∈ T :=
      hb.1 (((P ^ i) z).2 _ (Equiv.Perm.SameCycle.refl _ _))
    rw [he, hi] at ht
    exact ht
  · intro hx y hy
    obtain ⟨n, rfl⟩ := hy.exists_nat_pow_eq
    have hn (n : ℕ) : (p ^ n) x ∈ S ∧ f ((p ^ n) x) = (q ^ n) (f x) := by
      induction n with
      | zero => exact ⟨(hm x).1 (hx _ (Equiv.Perm.SameCycle.refl _ _)), rfl⟩
      | succ n ih =>
        have he : f ((p ^ (n + 1)) x) = (q ^ (n + 1)) (f x) := by
          rw [pow_succ', Equiv.Perm.mul_apply, hs _ ih.1, ih.2,
            pow_succ', Equiv.Perm.mul_apply]
        refine ⟨(hm _).1 ?_, he⟩
        rw [he]
        exact hx _ ⟨(n + 1 : ℕ), by simp only [zpow_natCast]⟩
    exact (hn n).1

private theorem rel_face_step (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (r N m c : ℕ)
    (hev : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hg : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k))
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hd : d ∈ kmswStageBallDarts (fun _ _ => True)
      (kmswStage (shiftedStream W N) m) r c) :
    wholePlaneDartι W N (((kmswMap (shiftedStream W N) m).faceSucc d).1.val,
      ((kmswMap (shiftedStream W N) m).faceSucc d).2) =
      wholePlaneFaceSucc W H (wholePlaneDartι W N (d.1.val, d.2)) := by
  have hv := ((kmswStageBallDarts_mem_iff _ _ _ _ _).mp hd).2
  have hf := fun M hNM => relVertex_fresh W r N m c M _ hev hg hv hNM
  rw [wholePlaneFaceSucc_ι_of_fresh W H N (d.1.val, d.2) (by
    intro M hNM
    simpa only [stageEndpoint, edgeFlip, Equiv.coe_fn_mk, (edge_endpoints_eq _ d.1.isLt).1,
      (edge_endpoints_eq _ d.1.isLt).2] using hf M hNM),
    kmswInfFaceSucc_eq_stage (shiftedStream W N) (H.1 N) m d
      (capturedVertex_complete _ _ _ ((relSucc _ _ _ _ hev).2 _ hv))]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The captured original stage faces are exactly the whole-plane original faces retained in -/
theorem UIBHBOTCertifiedRootCapture.originalFace_iff
    {W : ℤ → Fin 3} {r : ℕ} (C : UIBHBOTCertifiedRootCapture W r)
    (H : WholePlaneRotationHypothesis W)
    (d : StageDart (kmswStage (shiftedStream W C.N) C.m).nextEdge) :
    (∀ e, (kmswMap (shiftedStream W C.N) C.m).faceSucc.SameCycle d e →
      e ∈ kmswStageBallDarts (fun _ _ => True)
        (kmswStage (shiftedStream W C.N) C.m) r C.c) ↔
    (∀ e, (wholePlaneFaceSucc W H).SameCycle
      (wholePlaneDartι W C.N (d.1.val, d.2)) e →
      wholePlaneEdgeWest W e.1 ∈ uibhbotRootBallVertices W r ∧
      wholePlaneEdgeEast W e.1 ∈ uibhbotRootBallVertices W r) := by
  refine retainedOrbit_transport
    (kmswMap (shiftedStream W C.N) C.m).faceSucc (wholePlaneFaceSucc W H)
    (↑(kmswStageBallDarts (fun _ _ => True)
      (kmswStage (shiftedStream W C.N) C.m) r C.c))
    {e | wholePlaneEdgeWest W e.1 ∈ uibhbotRootBallVertices W r ∧
      wholePlaneEdgeEast W e.1 ∈ uibhbotRootBallVertices W r}
    (fun d => wholePlaneDartι W C.N (d.1.val, d.2)) ?_ ?_ ?_ d
  · intro a b hab
    apply Prod.ext
    · exact Fin.ext (wholePlaneEdgeι_injective W C.N (congrArg Prod.fst hab))
    · exact congrArg (fun d : WholePlaneDart W => d.2) hab
  · exact uibhbotRelaxedCapturedStageBallDarts_bijOn W r C.N C.m C.c C.event
      (fun M h k hk => (C.seams M h k hk).1) C.center
  · exact rel_face_step W H r C.N C.m C.c C.event
      (fun M h k hk => (C.seams M h k hk).1)

private theorem induced_original_closed {A : Type} [Fintype A] [DecidableEq A]
    (M : CombinatorialMap A) (S : Finset A)
    (hf : ∀ d, d ∈ S → M.edgeInv d ∈ S) (d : S) :
    retainedOrbit M.faceSucc (↑S)
      ((inducedCombinatorialMap M S hf).faceSucc d).1 ↔
      retainedOrbit M.faceSucc (↑S) d.1 := by
  let p := (inducedCombinatorialMap M S hf).faceSucc
  have hs (x : S) (hx : retainedOrbit M.faceSucc (↑S) x.1) :
      retainedOrbit M.faceSucc (↑S) (p x).1 := by
    have hn : M.faceSucc x.1 ∈ S := hx _ ⟨1, by simp only [zpow_one]⟩
    rw [inducedCombinatorialMap_faceSucc_of_mem M S hf x hn]
    exact (retainedOrbit_step M.faceSucc (↑S) x.1).2 hx
  constructor
  · intro h
    have hn (n : ℕ) : retainedOrbit M.faceSucc (↑S) ((p ^ (n + 1)) d).1 := by
      induction n with
      | zero => exact h
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact hs _ ih
    obtain ⟨n, hpos, _, he⟩ :=
      (Equiv.Perm.SameCycle.refl p d).exists_pow_eq''
    cases n with
    | zero => omega
    | succ n =>
      have ht := hn n
      rw [he] at ht
      exact ht
  · exact hs d

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The finite induced framed ball retains exactly the original ambient face cycles. -/
@[expose] noncomputable def uibhbotInducedLocalFacedBallRel
    {A : Type} [Fintype A] [DecidableEq A]
    (M : DirectedMapWithMissing A) (S : Finset A)
    (hf : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hp : M.toCombinatorialMap.IsPlanar)
    (hc : (inducedCombinatorialMap M.toCombinatorialMap S hf).IsConnected)
    (root : S) (hm : M.missing root.1) : FacedFramedBall where
  toFramedBall := uibhbotInducedLocalFramedBallRel M S hf hp hc root hm
  original := {d | ∀ e, M.faceSucc.SameCycle d.1 e → e ∈ S}
  original_closed := by exact induced_original_closed M.toCombinatorialMap S hf

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A certified capture with the local topology selection of original stage faces. -/
@[expose] noncomputable def UIBHBOTCertifiedRootCapture.facedBall
    {W : ℤ → Fin 3} {r : ℕ} (C : UIBHBOTCertifiedRootCapture W r) (hr : 0 < r) :
    FacedFramedBall := by
  classical
  let u := shiftedStream W C.N
  let s := kmswStage u C.m
  let M := kmswStageDirectedMap u C.m
  let S := kmswStageBallDarts (fun _ _ => True) s r
    (stageEndpoint s (edgeFlip _ C.dart))
  have hf : ∀ x, x ∈ S → M.edgeInv x ∈ S := by
    intro x hx
    exact (kmswStageBallDarts_edgeFlip (fun _ _ => True) s r
      (stageEndpoint s (edgeFlip _ C.dart)) x).mp hx
  exact uibhbotInducedLocalFacedBallRel M S hf (kmswMap_isPlanar u C.m)
    (kmswStageBallCombinatorialMap_rooted_isConnected u C.m r C.dart hr)
    ⟨C.dart, (kmswStageBallRootEdge_mem u C.m r C.dart hr).1⟩ C.missing

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Forgetting original faces recovers the existing captured framed ball exactly. -/
theorem UIBHBOTCertifiedRootCapture.facedBall_forget
    {W : ℤ → Fin 3} {r : ℕ} (C : UIBHBOTCertifiedRootCapture W r) (hr : 0 < r) :
    (C.facedBall hr).toFramedBall = C.framedBall hr := rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The selected faces are exactly the whole-plane face orbits contained in the root ball. -/
theorem UIBHBOTCertifiedRootCapture.facedBall_original_iff
    {W : ℤ → Fin 3} {r : ℕ} (C : UIBHBOTCertifiedRootCapture W r)
    (H : WholePlaneRotationHypothesis W) (hr : 0 < r) (d : (C.facedBall hr).toFramedBall.D) :
    d ∈ (C.facedBall hr).original ↔
      ∀ e, (wholePlaneFaceSucc W H).SameCycle
        (wholePlaneDartι W C.N (d.1.1.val, d.1.2)) e →
        wholePlaneEdgeWest W e.1 ∈ uibhbotRootBallVertices W r ∧
        wholePlaneEdgeEast W e.1 ∈ uibhbotRootBallVertices W r := by
  change retainedOrbit (kmswMap (shiftedStream W C.N) C.m).faceSucc
    (↑(kmswStageBallDarts (fun _ _ => True)
      (kmswStage (shiftedStream W C.N) C.m) r
      (stageEndpoint _ (edgeFlip _ C.dart)))) d.1 ↔ _
  simpa only [retainedOrbit, C.dart_center, Finset.mem_coe] using (C.originalFace_iff H d.1)

private theorem capture_embedding_iso
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (r : ℕ) (hr : 0 < r)
    (N m c N' m' c' : ℕ)
    (hevent : kmswWindowCaptureEventStrongRel (shiftedStream W N) m (r + 1) c)
    (hglob : ∀ M, N ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N) m (r + 1) c,
        minL (shiftedStream W M) (M - N + k) =
          L (shiftedStream W M) (M - N + k))
    (hcenter : wholePlaneVertexι W N c = uibhbotRootFirstVertex W)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge)
    (hdcenter : stageEndpoint (kmswStage (shiftedStream W N) m)
      (edgeFlip _ d) = c)
    (hdroot : wholePlaneEdgeι W N d.1.val = uibhbotRootEdge W)
    (hdmissing : (kmswStageDirectedMap (shiftedStream W N) m).missing d)
    (hevent' : kmswWindowCaptureEventStrongRel (shiftedStream W N') m' (r + 1) c')
    (hglob' : ∀ M, N' ≤ M →
      ∀ k ∈ kmswBallLeftSeamSet (shiftedStream W N') m' (r + 1) c',
        minL (shiftedStream W M) (M - N' + k) =
          L (shiftedStream W M) (M - N' + k))
    (hcenter' : wholePlaneVertexι W N' c' = uibhbotRootFirstVertex W)
    (d' : StageDart (kmswStage (shiftedStream W N') m').nextEdge)
    (hdcenter' : stageEndpoint (kmswStage (shiftedStream W N') m')
      (edgeFlip _ d') = c')
    (hdroot' : wholePlaneEdgeι W N' d'.1.val = uibhbotRootEdge W)
    (hdmissing' : (kmswStageDirectedMap (shiftedStream W N') m').missing d') :
    ∃ I : FramedBallIso
      (uibhbotRelaxedCapturedStageFramedBall W r hr N m c hevent hcenter d
        hdcenter hdroot hdmissing)
      (uibhbotRelaxedCapturedStageFramedBall W r hr N' m' c' hevent' hcenter' d'
        hdcenter' hdroot' hdmissing'),
      ∀ x, wholePlaneDartι W N (x.1.1.val, x.1.2) =
        wholePlaneDartι W N' ((I.mapIso.toEquiv x).1.1.val,
          (I.mapIso.toEquiv x).1.2) := by
  classical
  subst c
  subst c'
  let A := uibhbotRelaxedCapturedStageFramedBall W r hr N m _ hevent hcenter d
    rfl hdroot hdmissing
  let B := uibhbotRelaxedCapturedStageFramedBall W r hr N' m' _ hevent' hcenter' d'
    rfl hdroot' hdmissing'
  obtain ⟨e, he⟩ := uibhbotRelaxedCapturedStageBallDarts_equiv W r N m _ N' m' _
    hevent hglob hcenter hevent' hglob' hcenter'
  let E : A.D ≃ B.D := e
  let a0 : A.D := ⟨d, (kmswStageBallRootEdge_mem _ m r d hr).1⟩
  let b0 : B.D := ⟨d', (kmswStageBallRootEdge_mem _ m' r d' hr).1⟩
  have hrot : ∀ x, E (A.map.rot x) = B.map.rot (E x) :=
    uibhbotRelaxedCapturedStageBallDarts_equiv_rot W H r N m _ N' m' _
      hevent hglob hcenter hevent' hglob' hcenter' e he
  have hflip : ∀ x, E (A.map.edgeInv x) = B.map.edgeInv (E x) :=
    uibhbotCapturedStageBallDarts_equiv_edgeFlip W r N m _ N' m' _ e he
  have htags := uibhbotRelaxedCapturedStageBallDarts_equiv_tags W r N m _ N' m' _
    hevent hglob hevent' hglob' e he
  have hs := uibhbotRelaxedCapture_rootDart_side W N m _ hcenter d rfl hdroot
  have hs' := uibhbotRelaxedCapture_rootDart_side W N' m' _ hcenter' d' rfl hdroot'
  have hbase : E a0 = b0 := by
    have h := he a0
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      apply wholePlaneEdgeι_injective W N'
      calc
        wholePlaneEdgeι W N' (E a0).1.1.val =
            wholePlaneEdgeι W N d.1.val := (congrArg Prod.fst h).symm
        _ = uibhbotRootEdge W := hdroot
        _ = wholePlaneEdgeι W N' d'.1.val := hdroot'.symm
    · change (E a0).1.2 = d'.2
      have hb : d.2 = (E a0).1.2 :=
        congrArg (fun q : WholePlaneDart W => q.2) h
      exact hb.symm.trans (hs.trans hs'.symm)
  have hroot : E A.rootDart = B.rootDart := by
    exact (hflip a0).trans (congrArg B.map.edgeInv hbase)
  have hsym (x : A.D) : E (A.map.rot.symm x) = B.map.rot.symm (E x) := by
    apply B.map.rot.injective
    rw [← hrot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hface (x : A.D) : E (A.map.faceSucc x) = B.map.faceSucc (E x) := by
    change E (A.map.rot.symm (A.map.edgeInv x)) =
      B.map.rot.symm (B.map.edgeInv (E x))
    rw [hsym, hflip]
  have hoA := uibhbotRelaxedCapturedStageFramedBall_outer_root W r hr N m _ hevent hcenter d
    rfl hdroot hdmissing
  have hoB := uibhbotRelaxedCapturedStageFramedBall_outer_root W r hr N' m' _ hevent' hcenter' d'
    rfl hdroot' hdmissing'
  change A.map.IsOuter (A.map.edgeInv (A.map.edgeInv a0)) at hoA
  rw [A.map.edgeInv_invol] at hoA
  change B.map.IsOuter (B.map.edgeInv (B.map.edgeInv b0)) at hoB
  rw [B.map.edgeInv_invol] at hoB
  have houter (x : A.D) : B.map.IsOuter (E x) ↔ A.map.IsOuter x := by
    have hcycle := sameCycle_equiv_iff E A.map.faceSucc B.map.faceSucc hface
      a0 x
    rw [hbase] at hcycle
    constructor
    · intro hx
      exact hoA.trans (hcycle.mpr (hoB.symm.trans hx))
    · intro hx
      exact hoB.trans (hcycle.mp (hoA.symm.trans hx))
  let I : DirectedMapWithMissingIso A.map B.map :=
    { toEquiv := E
      rot_comm := hrot
      edgeInv_comm := hflip
      missing_iff := fun x => (htags x).2.1
      tail_iff := fun x => (htags x).2.2
      outer_iff := houter }
  refine ⟨{ mapIso := I
            root_vertex := ?_
            frameEdge_comm := hroot
            frameOther_comm := ?_ }, ?_⟩
  · exact hroot.sameCycle B.map.rot
  · right
    refine ⟨E a0, b0, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · exact hbase.sameCycle B.map.rot

  · exact he

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Certified captures give isomorphic faced balls, preserving all original-face incidences. -/
noncomputable def UIBHBOTCertifiedRootCapture.facedIso
    {W : ℤ → Fin 3} {r : ℕ} (C D : UIBHBOTCertifiedRootCapture W r)
    (H : WholePlaneRotationHypothesis W) (hr : 0 < r) :
    FacedFramedBallIso (C.facedBall hr) (D.facedBall hr) := by
  classical
  let hex := capture_embedding_iso W H r hr
    C.N C.m C.c D.N D.m D.c C.event (fun M h k hk => (C.seams M h k hk).1)
    C.center C.dart C.dart_center C.root C.missing
    D.event (fun M h k hk => (D.seams M h k hk).1)
    D.center D.dart D.dart_center D.root D.missing
  let I := Classical.choose hex
  have hi := Classical.choose_spec hex
  refine ⟨I, ?_⟩
  intro d
  rw [D.facedBall_original_iff H hr, C.facedBall_original_iff H hr, hi d]
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The faced class does not depend on the certified capture. -/
theorem UIBHBOTCertifiedRootCapture.facedClass_eq
    {W : ℤ → Fin 3} {r : ℕ} (C D : UIBHBOTCertifiedRootCapture W r)
    (H : WholePlaneRotationHypothesis W) (hr : 0 < r) :
    Quotient.mk FacedFramedBall.setoid (C.facedBall hr) =
      Quotient.mk FacedFramedBall.setoid (D.facedBall hr) :=
  Quotient.sound ⟨C.facedIso D H hr⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The measurable structure on the countable faced class space. -/
instance instMeasurableSpaceFacedFramedBallClass : MeasurableSpace FacedFramedBallClass :=
  ⊤

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Form the isomorphism class of a faced captured ball. -/
@[expose] def facedCapturedStageBallClass (B : FacedFramedBall) : FacedFramedBallClass :=
  Quotient.mk FacedFramedBall.setoid B

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The default faced class lies above the existing default framed class. -/
@[expose] noncomputable def facedOffCaptureClassRel : FacedFramedBallClass :=
  facedCapturedStageBallClass
    ⟨uibhbotOffCaptureClassRel.out, ∅, fun _ => Iff.rfl⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Forgetting the default face selection recovers the default framed class. -/
theorem facedOffCaptureClassRel_forget :
    facedOffCaptureClassRel.forget = uibhbotOffCaptureClassRel :=
  Quotient.out_eq _

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Select a faced capture on the proved almost-sure event, with a fixed default elsewhere. -/
@[expose] noncomputable def facedUIBHBOTBallClassRel (W : ℤ → Fin 3) (r : ℕ)
    (hr : 0 < r) : FacedFramedBallClass := by
  classical
  exact if h : WholePlaneRotationHypothesis W ∧
      Nonempty (UIBHBOTCertifiedRootCapture W r) then
    facedCapturedStageBallClass ((Classical.choice h.2).facedBall hr)
  else facedOffCaptureClassRel

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
On the rotation event every certified capture gives the selected faced class. -/
theorem facedUIBHBOTBallClassRel_eq_capture (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (r : ℕ) (hr : 0 < r)
    (C : UIBHBOTCertifiedRootCapture W r) :
    facedUIBHBOTBallClassRel W r hr = facedCapturedStageBallClass (C.facedBall hr) := by
  classical
  rw [facedUIBHBOTBallClassRel, dite_eq_left ⟨H, ⟨C⟩⟩]
  exact UIBHBOTCertifiedRootCapture.facedClass_eq _ C H hr

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Forgetting faces agrees pointwise with the existing canonical framed selector. -/
theorem facedUIBHBOTBallClassRel_forget (W : ℤ → Fin 3) (r : ℕ) (hr : 0 < r) :
    (facedUIBHBOTBallClassRel W r hr).forget = uibhbotBallClassRel W r hr := by
  classical
  by_cases h : WholePlaneRotationHypothesis W ∧
      Nonempty (UIBHBOTCertifiedRootCapture W r)
  · rw [facedUIBHBOTBallClassRel, uibhbotBallClassRel, dite_eq_left h, dite_eq_left h]
    rfl
  · rw [facedUIBHBOTBallClassRel, uibhbotBallClassRel, dite_eq_right h, dite_eq_right h]
    exact facedOffCaptureClassRel_forget

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The total finite-stage faced selector, defaulting only for invalid local data. -/
@[expose] noncomputable def facedUIBHBOTStageDataBallClassRel
    (p : Σ s : State, DirectedMapWithMissing (StageDart s.nextEdge))
    (r e : ℕ) (b : Bool) : FacedFramedBallClass := by
  classical
  let s := p.1
  let M := p.2
  exact if he : e < s.nextEdge then
    let d : StageDart s.nextEdge := (⟨e, he⟩, b)
    let S := kmswStageBallDarts (fun _ _ => True) s r (stageEndpoint s (edgeFlip _ d))
    if hf : ∀ x, x ∈ S → M.edgeInv x ∈ S then
      if hv : M.toCombinatorialMap.IsPlanar ∧
          (@CombinatorialMap.IsConnected {x : StageDart s.nextEdge // x ∈ S}
            (Finset.Subtype.fintype S) (fun a b => a.instDecidableEq b)
            (inducedCombinatorialMap M.toCombinatorialMap S hf)) ∧
          d ∈ S ∧ M.missing d then
        facedCapturedStageBallClass
          (uibhbotInducedLocalFacedBallRel M S hf hv.1 hv.2.1 ⟨d, hv.2.2.1⟩ hv.2.2.2)
      else facedOffCaptureClassRel
    else facedOffCaptureClassRel
  else facedOffCaptureClassRel

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A certified capture's class equals the class computed from its finite stage and
the raw index of its root dart. No global rotation hypothesis is needed. -/
theorem UIBHBOTCertifiedRootCapture.facedClass_eq_stageData {W : ℤ → Fin 3} {r : ℕ}
    (C : UIBHBOTCertifiedRootCapture W r) (hr : 0 < r) :
    facedCapturedStageBallClass (C.facedBall hr) =
      facedUIBHBOTStageDataBallClassRel
        ⟨kmswStage (shiftedStream W C.N) C.m,
          kmswStageDirectedMap (shiftedStream W C.N) C.m⟩ r C.dart.1.val C.dart.2 := by
  classical
  let u := shiftedStream W C.N
  let s := kmswStage u C.m
  let M := kmswStageDirectedMap u C.m
  let d := C.dart
  let S := kmswStageBallDarts (fun _ _ => True) s r (stageEndpoint s (edgeFlip _ d))
  have hf : ∀ x, x ∈ S → M.edgeInv x ∈ S := by
    intro x hx
    exact (kmswStageBallDarts_edgeFlip (fun _ _ => True) s r
      (stageEndpoint s (edgeFlip _ d)) x).mp hx
  have hv : M.toCombinatorialMap.IsPlanar ∧
      (@CombinatorialMap.IsConnected {x : StageDart s.nextEdge // x ∈ S}
            (Finset.Subtype.fintype S) (fun a b => a.instDecidableEq b)
            (inducedCombinatorialMap M.toCombinatorialMap S hf)) ∧
      d ∈ S ∧ M.missing d :=
    ⟨kmswMap_isPlanar u C.m,
      kmswStageBallCombinatorialMap_rooted_isConnected u C.m r d hr,
      (kmswStageBallRootEdge_mem u C.m r d hr).1, C.missing⟩
  unfold facedUIBHBOTStageDataBallClassRel
  rw [dite_eq_left C.dart.1.isLt]
  dsimp only
  rw [dite_eq_left hf, dite_eq_left hv]
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Equality on the stage window preserves the finite-stage class, including its
rotation, tags, frame and surviving outer face. -/
theorem facedUIBHBOTStageDataBallClassRel_eq_of_window (W V : ℤ → Fin 3)
    (N m r e : ℕ) (b : Bool)
    (h : ∀ i < m, W ((i : ℤ) - N) = V ((i : ℤ) - N)) :
    facedUIBHBOTStageDataBallClassRel
        ⟨kmswStage (shiftedStream W N) m, kmswStageDirectedMap (shiftedStream W N) m⟩
        r e b =
      facedUIBHBOTStageDataBallClassRel
        ⟨kmswStage (shiftedStream V N) m, kmswStageDirectedMap (shiftedStream V N) m⟩
        r e b := by
  exact congrArg (fun p => facedUIBHBOTStageDataBallClassRel p r e b)
    (relStageMap_data_eq (shiftedStream W N) (shiftedStream V N) m h)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The finite-stage class depends only on the stage window, so it is measurable
for every fixed window and raw dart index, with no rotation hypothesis. -/
theorem measurable_facedUIBHBOTStageDataBallClassRel (N m r e : ℕ) (b : Bool) :
    Measurable (fun W : ℤ → Fin 3 => facedUIBHBOTStageDataBallClassRel
      ⟨kmswStage (shiftedStream W N) m, kmswStageDirectedMap (shiftedStream W N) m⟩
      r e b) := by
  have hm : Measurable (fun u : ℕ → Fin 3 => facedUIBHBOTStageDataBallClassRel
      ⟨kmswStage u m, kmswStageDirectedMap u m⟩ r e b) := by
    apply measurable_of_factors_prefix m
    intro u v h
    exact congrArg (fun p => facedUIBHBOTStageDataBallClassRel p r e b)
      (relStageMap_data_eq u v m h)
  exact hm.comp (measurable_relShift N)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
On the capture event the faced-class fibres are countable unions of window fibres. -/
theorem facedUIBHBOTBallClassRel_event_fibre (r : ℕ) (hr : 0 < r) (B : FacedFramedBallClass) :
    {W : ℤ → Fin 3 | (WholePlaneRotationHypothesis W ∧
        Nonempty (UIBHBOTCertifiedRootCapture W r)) ∧ facedUIBHBOTBallClassRel W r hr = B} =
      ⋃ N : ℕ, ⋃ m : ℕ, ⋃ c : ℕ, ⋃ e : ℕ, ⋃ b : Bool,
        ({W | uibhbotFixedCaptureRel W r N m c e b} ∩
          {W | WholePlaneRotationHypothesis W ∧
            Nonempty (UIBHBOTCertifiedRootCapture W r)}) ∩
          {W | facedUIBHBOTStageDataBallClassRel
            ⟨kmswStage (shiftedStream W N) m,
              kmswStageDirectedMap (shiftedStream W N) m⟩ r e b = B} := by
  ext W
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨H, ⟨C⟩⟩, hB⟩
    refine ⟨C.N, C.m, C.c, C.dart.1.val, C.dart.2, ⟨?_, H, ⟨C⟩⟩, ?_⟩
    · exact (uibhbotFixedCaptureRel_iff W r _ _ _ _ _).mpr
        ⟨C, rfl, rfl, rfl, rfl, rfl⟩
    · exact (C.facedClass_eq_stageData hr).symm.trans
        ((facedUIBHBOTBallClassRel_eq_capture W H r hr C).symm.trans hB)
  · rintro ⟨N, m, c, e, b, ⟨hcap, H, hne⟩, hB⟩
    rcases (uibhbotFixedCaptureRel_iff W r N m c e b).mp hcap with
      ⟨C, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨⟨H, hne⟩, (facedUIBHBOTBallClassRel_eq_capture W H r hr C).trans
      ((C.facedClass_eq_stageData hr).trans hB)⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The total canonical class selector, with its explicit off-event default, is measurable. -/
theorem measurable_facedUIBHBOTBallClassRel (r : ℕ) (hr : 0 < r) :
    Measurable (fun W : ℤ → Fin 3 => facedUIBHBOTBallClassRel W r hr) := by
  apply measurable_to_countable'
  intro B
  have hE := measurableSet_uibhbotBallClassRel_event r
  have hf : MeasurableSet {W : ℤ → Fin 3 | (WholePlaneRotationHypothesis W ∧
      Nonempty (UIBHBOTCertifiedRootCapture W r)) ∧ facedUIBHBOTBallClassRel W r hr = B} := by
    rw [facedUIBHBOTBallClassRel_event_fibre r hr B]
    exact MeasurableSet.iUnion (fun N => MeasurableSet.iUnion (fun m =>
      MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun e =>
        MeasurableSet.iUnion (fun b =>
          ((measurableSet_uibhbotFixedCaptureRel r N m c e b).inter hE).inter
            ((measurable_facedUIBHBOTStageDataBallClassRel N m r e b)
              ((Set.to_countable {B}).measurableSet)))))))
  have hd : MeasurableSet {W : ℤ → Fin 3 | facedOffCaptureClassRel = B} :=
    (measurable_const : Measurable (fun _ : ℤ → Fin 3 =>
      facedOffCaptureClassRel = B)).setOf
  have heq : {W : ℤ → Fin 3 | facedUIBHBOTBallClassRel W r hr = B} =
      {W | (WholePlaneRotationHypothesis W ∧
        Nonempty (UIBHBOTCertifiedRootCapture W r)) ∧ facedUIBHBOTBallClassRel W r hr = B} ∪
      ({W | WholePlaneRotationHypothesis W ∧
        Nonempty (UIBHBOTCertifiedRootCapture W r)}ᶜ ∩
        {W | facedOffCaptureClassRel = B}) := by
    ext W
    classical
    by_cases h : WholePlaneRotationHypothesis W ∧
        Nonempty (UIBHBOTCertifiedRootCapture W r)
    · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, h, true_and, not_true, false_and, or_false]
    · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, h, false_and, not_false_eq_true, true_and, false_or]
      have hoff : facedUIBHBOTBallClassRel W r hr = facedOffCaptureClassRel :=
        dite_eq_right h
      rw [hoff]
  change MeasurableSet {W : ℤ → Fin 3 | facedUIBHBOTBallClassRel W r hr = B}
  rw [heq]
  exact hf.union (hE.compl.inter hd)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The probability law of the canonical faced ball at positive radius. -/
@[expose] noncomputable def facedUIBHBOTBSBallLaw (r : ℕ) (hr : 0 < r) :
    ProbabilityMeasure FacedFramedBallClass :=
  uibhbotCodeLawRel.map (fun W => facedUIBHBOTBallClassRel W r hr)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The forgetful map on faced classes is measurable. -/
theorem measurable_facedFramedBallClass_forget :
    Measurable FacedFramedBallClass.forget := measurable_of_countable _

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Forgetting original-face selection pushes the faced law to the existing framed law. -/
theorem facedUIBHBOTBSBallLaw_forget (r : ℕ) (hr : 0 < r) :
    (facedUIBHBOTBSBallLaw r hr).map FacedFramedBallClass.forget =
      uibhbotBSBallLaw r hr := by
  apply Subtype.ext
  change ((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    (fun W => facedUIBHBOTBallClassRel W r hr)).map FacedFramedBallClass.forget = _
  rw [Measure.map_map measurable_facedFramedBallClass_forget
    (measurable_facedUIBHBOTBallClassRel r hr)]
  congr 1
  funext W
  exact facedUIBHBOTBallClassRel_forget W r hr

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Almost surely every certified capture gives the canonical faced class. -/
theorem uibhbotCodeLawRel_ae_facedBallClassRel (r : ℕ) (hr : 0 < r) :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      Nonempty (UIBHBOTCertifiedRootCapture W r) ∧
        ∀ C : UIBHBOTCertifiedRootCapture W r,
          facedUIBHBOTBallClassRel W r hr = facedCapturedStageBallClass (C.facedBall hr) := by
  filter_upwards [uibhbotCodeLawRel_ae_ballClassRel_event r] with W h
  exact ⟨h.2, fun C => facedUIBHBOTBallClassRel_eq_capture W h.1 r hr C⟩

end DirectedDistances.PaperProofs.Section5
