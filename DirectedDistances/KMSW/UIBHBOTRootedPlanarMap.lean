module

public import DirectedDistances.KMSW.WholePlaneRootedMapFields
public import DirectedDistances.PaperProofs.Section5.UIBHBOTFacedBallLaw
public import DirectedDistances.PaperProofs.Section5.DiskRootedPlanarObject
import all DirectedDistances.PaperProofs.Section5.DiskRootedPlanarObject
import all DirectedDistances.PaperProofs.Section5.UIBHBOTBallLawRel

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section5
open DirectedDistances.RandomWalk MeasureTheory

private noncomputable def orbitVertex (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) :
    RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H) →
      WholePlaneVertex W :=
  Quotient.lift (wholePlaneDartVertex W) (fun d e h =>
    (wholePlaneRotation_sameCycle_dartVertex W H d e h).symm)

private theorem vertexClass_eq_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d e : WholePlaneDart W) :
    rootedLocallyFiniteVertexClass (wholePlaneRotation W H) d =
        rootedLocallyFiniteVertexClass (wholePlaneRotation W H) e ↔
      wholePlaneDartVertex W d = wholePlaneDartVertex W e := by
  constructor
  · exact fun h => congrArg (orbitVertex W H) h
  · exact fun h => Quotient.sound (wholePlaneRotation_sameVertex_sameCycle_proof W H d e h)

private theorem dart_adjacent (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    wholePlaneAdjacent W (wholePlaneDartVertex W d)
      (wholePlaneDartVertex W (wholePlaneDartFlip W d)) := by
  rcases d with ⟨e, b⟩
  cases b
  · exact ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨e, Or.inr ⟨rfl, rfl⟩⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The rotation-quotient radius agrees with the all-geometric colimit radius. -/
theorem uibhbotWholePlane_withinRadius_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0) (r : ℕ) (d : WholePlaneDart W) :
    rootedLocallyFiniteWithinRadius
        (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) r
        (rootedLocallyFiniteVertexClass (wholePlaneRotation W H) d) ↔
      wholePlaneDartVertex W d ∈ uibhbotRootBallVertices W r := by
  let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
  constructor
  · intro hd
    have hforward : ∀ {s v}, rootedLocallyFiniteWithinRadius M s v →
        wholePlaneDistanceLe W s (uibhbotRootFirstVertex W) (orbitVertex W H v) := by
      intro s v hv
      induction hv with
      | root => exact ⟨0, le_rfl, .nil (Set.mem_univ _)⟩
      | stay h ih =>
        obtain ⟨k, hk, hp⟩ := ih
        exact ⟨k, Nat.le_trans hk (Nat.le_succ _), hp⟩
      | edge h hs ih =>
        obtain ⟨x, hx, hy⟩ := hs
        obtain ⟨k, hk, hp⟩ := ih
        refine ⟨k + 1, Nat.succ_le_succ hk,
          .snoc hp (Set.mem_univ _) (Set.mem_univ _) ?_⟩
        rw [← hx, ← hy]
        exact dart_adjacent W x
    exact hforward hd
  · rintro ⟨k, hk, hp⟩
    have hpath : ∀ {k v}, WholePlanePath W Set.univ (uibhbotRootFirstVertex W) k v →
        ∀ e : WholePlaneDart W, wholePlaneDartVertex W e = v →
          rootedLocallyFiniteWithinRadius M k
            (rootedLocallyFiniteVertexClass M.rot e) := by
      intro k v hp
      induction hp with
      | nil hv =>
        intro e he
        have heq := (vertexClass_eq_iff W H e M.rootDart).2 he
        change rootedLocallyFiniteVertexClass M.rot e = _ at heq
        rw [heq]
        exact .root
      | @snoc n y z hp hy hz ha ih =>
        intro e he
        obtain ⟨a, ha | ha⟩ := ha
        · let x : WholePlaneDart W := (a, false)
          have hx : wholePlaneDartVertex W x = y := ha.1
          have hxe : rootedLocallyFiniteVertexClass M.rot (M.edgeInv x) =
              rootedLocallyFiniteVertexClass M.rot e :=
            (vertexClass_eq_iff W H _ e).2 (ha.2.trans he.symm)
          rw [← hxe]
          exact .edge (ih x hx) ⟨x, rfl, rfl⟩
        · let x : WholePlaneDart W := (a, true)
          have hx : wholePlaneDartVertex W x = y := ha.2
          have hxe : rootedLocallyFiniteVertexClass M.rot (M.edgeInv x) =
              rootedLocallyFiniteVertexClass M.rot e :=
            (vertexClass_eq_iff W H _ e).2 (ha.1.trans he.symm)
          rw [← hxe]
          exact .edge (ih x hx) ⟨x, rfl, rfl⟩
    exact (mem_rootedLocallyFiniteRadiusVertices M r _).1
      (rootedLocallyFiniteRadiusVertices_mono M hk
        ((mem_rootedLocallyFiniteRadiusVertices M k _).2 (hpath hp d rfl)))

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The constructed map's induced dart ball is the colimit geometric dart ball. -/
theorem uibhbotWholePlane_ballDarts_iff (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0) (r : ℕ) (d : WholePlaneDart W) :
    d ∈ rootedLocallyFiniteBallDarts
        (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) r ↔
      wholePlaneEdgeWest W d.1 ∈ uibhbotRootBallVertices W r ∧
        wholePlaneEdgeEast W d.1 ∈ uibhbotRootBallVertices W r := by
  erw [mem_rootedLocallyFiniteBallDarts,
    mem_rootedLocallyFiniteRadiusVertices, mem_rootedLocallyFiniteRadiusVertices]
  change (rootedLocallyFiniteWithinRadius
      (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) r
      (rootedLocallyFiniteVertexClass (wholePlaneRotation W H) d) ∧
    rootedLocallyFiniteWithinRadius
      (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) r
      (rootedLocallyFiniteVertexClass (wholePlaneRotation W H) (wholePlaneDartFlip W d))) ↔ _
  rw [uibhbotWholePlane_withinRadius_iff, uibhbotWholePlane_withinRadius_iff]
  rcases d with ⟨e, b⟩
  cases b
  · exact Iff.rfl
  · exact and_comm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The stage inclusion bijects certified ball darts with ambient ball darts. -/
@[expose] noncomputable def uibhbotCapturedBallEquiv (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0) {r : ℕ}
    (C : UIBHBOTCertifiedRootCapture W r) :
    KMSWStageBallDart (fun _ _ => True) (kmswStage (shiftedStream W C.N) C.m) r C.c ≃
      {d : (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).D //
        d ∈ rootedLocallyFiniteBallDarts
          (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀) r} := by
  let hb := uibhbotRelaxedCapturedStageBallDarts_bijOn W r C.N C.m C.c C.event
    (fun M h k hk => (C.seams M h k hk).1) C.center
  let f := fun d : KMSWStageBallDart (fun _ _ => True)
      (kmswStage (shiftedStream W C.N) C.m) r C.c =>
    (⟨wholePlaneDartι W C.N (d.1.1.val, d.1.2),
      (uibhbotWholePlane_ballDarts_iff W H hhit C₀ r _).2 (hb.1 d.2)⟩ :
      {d : (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀).D //
        d ∈ rootedLocallyFiniteBallDarts
          (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀) r})
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    exact hb.2.1 a.2 b.2 (congrArg Subtype.val hab)
  · intro d
    obtain ⟨a, ha, had⟩ := hb.2.2
      ((uibhbotWholePlane_ballDarts_iff W H hhit C₀ r d.1).1 d.2)
    exact ⟨⟨a, ha⟩, Subtype.ext had⟩

private theorem firstReturn_embedding {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : Equiv.Perm A) (g : Equiv.Perm B) (S : Finset A) (T : Finset B)
    (hS : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (f ^ k) x.1 ∈ S)
    (hT : ∀ x : T, ∃ k : ℕ, 0 < k ∧ (g ^ k) x.1 ∈ T)
    (i : A → B) (hi : Function.Injective i) (U : Set A)
    (hU : ∀ x, x ∈ U → f x ∈ U)
    (hrot : ∀ x, x ∈ U → i (f x) = g (i x))
    (E : S ≃ T) (he : ∀ x, (E x).1 = i x.1) (x : S) (hx : x.1 ∈ U) :
    E (cyclicFirstReturn f S hS x) = cyclicFirstReturn g T hT (E x) := by
  have hiter (k : ℕ) : (f ^ k) x.1 ∈ U ∧
      i ((f ^ k) x.1) = (g ^ k) (i x.1) := by
    induction k with
    | zero => exact ⟨hx, rfl⟩
    | succ k ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨hU _ ih.1, (hrot _ ih.1).trans (congrArg g ih.2)⟩
  have hmem (k : ℕ) : (f ^ k) x.1 ∈ S ↔ (g ^ k) (E x).1 ∈ T := by
    rw [he x, ← (hiter k).2]
    constructor
    · intro hk
      rw [← he ⟨_, hk⟩]
      exact (E ⟨_, hk⟩).2
    · intro hk
      let y : T := ⟨_, hk⟩
      have hval : i (E.symm y).1 = i ((f ^ k) x.1) := by
        rw [← he, E.apply_symm_apply]
      exact hi hval ▸ (E.symm y).2
  let k := cyclicFirstReturnTime f S hS x
  let l := cyclicFirstReturnTime g T hT (E x)
  have ht : k = l := by
    apply Nat.le_antisymm
    · exact Nat.find_min' _ ⟨(cyclicFirstReturnTime_spec g T hT (E x)).1,
        (hmem l).2 (cyclicFirstReturnTime_spec g T hT (E x)).2.1⟩
    · exact Nat.find_min' _ ⟨(cyclicFirstReturnTime_spec f S hS x).1,
        (hmem k).1 (cyclicFirstReturnTime_spec f S hS x).2.1⟩
  apply Subtype.ext
  rw [he, (firstReturn_spec f S hS x).1, (hiter k).2,
    (firstReturn_spec g T hT (E x)).1, he x]
  exact congrArg (fun n => (g ^ n) (i x.1)) ht

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The captured dart bijection preserves the first-return vertex rotation. -/
theorem uibhbotCapturedBallEquiv_rot (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0) {r : ℕ}
    (C : UIBHBOTCertifiedRootCapture W r) :
    let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀
    letI : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r} :=
      Classical.decEq _
    let E := uibhbotCapturedBallEquiv W H hhit C₀ C
    ∀ d, E (kmswStageBallRot (fun _ _ => True) (shiftedStream W C.N) C.m r C.c d) =
      (rootedLocallyFiniteBallCombinatorialMap M r).rot (E d) := by
  classical
  intro M E d
  let u := shiftedStream W C.N
  let s := kmswStage u C.m
  let S := kmswStageBallDarts (fun _ _ => True) s r C.c
  let T := rootedLocallyFiniteBallDarts M r
  let i := fun x : StageDart s.nextEdge => wholePlaneDartι W C.N (x.1.val, x.2)
  let U : Set (StageDart s.nextEdge) :=
    {x | stageEndpoint s x ∈ kmswStageBallVertices (fun _ _ => True) s r C.c}
  have hi : Function.Injective i := by
    intro a b hab
    apply Prod.ext
    · exact Fin.ext (wholePlaneEdgeι_injective W C.N (congrArg Prod.fst hab))
    · exact congrArg (fun q : WholePlaneDart W => q.2) hab
  have hU (x : StageDart s.nextEdge) (hx : x ∈ U) : stageRot u C.m x ∈ U := by
    have hep := (stageRot_sameCycle_iff_endpoint_eq u C.m x (stageRot u C.m x)).1
      ⟨1, rfl⟩
    change stageEndpoint s (stageRot u C.m x) ∈
      kmswStageBallVertices (fun _ _ => True) s r C.c
    change stageEndpoint s x ∈ kmswStageBallVertices (fun _ _ => True) s r C.c at hx
    exact hep ▸ hx
  have hrot (x : StageDart s.nextEdge) (hx : x ∈ U) :
      i (stageRot u C.m x) = M.rot (i x) := by
    change wholePlaneDartι W C.N ((stageRot u C.m x).1.val, (stageRot u C.m x).2) =
      wholePlaneRotation W H (wholePlaneDartι W C.N (x.1.val, x.2))
    rw [relDart_rotation_agrees W H r C.N C.m C.c C.event
      (fun Q h k hk => (C.seams Q h k hk).1) x hx,
      kmswInfRot_eq_stage u (H.1 C.N) C.m x
        (capturedVertex_complete u C.m _ ((relSucc u C.m r C.c C.event).2 _ hx))]
  have hreturn : ∀ x : T, ∃ k : ℕ, 0 < k ∧ (M.rot ^ k) x.1 ∈ T := by
    intro x
    obtain ⟨k, hk, he⟩ := rootedLocallyFiniteRotationReturn M x.1
    refine ⟨k, hk, ?_⟩
    rw [he]
    exact x.2
  change E (cyclicFirstReturn (stageRot u C.m) S (finitePermutationReturn _ _) d) =
    cyclicFirstReturn M.rot T hreturn (E d)
  exact firstReturn_embedding (stageRot u C.m) M.rot S T
    (finitePermutationReturn _ _) hreturn i hi U hU hrot E (fun _ => rfl) d
      ((kmswStageBallDarts_mem_iff _ _ _ _ _).1 d.2).1

private theorem eulerChar_equiv {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M : CombinatorialMap A) (N : CombinatorialMap B) (E : A ≃ B)
    (hr : ∀ x, E (M.rot x) = N.rot (E x))
    (he : ∀ x, E (M.edgeInv x) = N.edgeInv (E x)) : M.eulerChar = N.eulerChar := by
  classical
  have hs (x : A) : E (M.rot.symm x) = N.rot.symm (E x) := by
    apply N.rot.injective
    rw [← hr, M.rot.apply_symm_apply, N.rot.apply_symm_apply]
  have hf (x : A) : E (M.faceSucc x) = N.faceSucc (E x) := by
    change E (M.rot.symm (M.edgeInv x)) = N.rot.symm (N.edgeInv (E x))
    rw [hs, he]
  have hc (p : Equiv.Perm A) (q : Equiv.Perm B)
      (h : ∀ x, E (p x) = q (E x)) :
      Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid p)) =
        Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid q)) :=
    Fintype.card_congr (Quotient.congr E (framedBall_sameCycle_iff_of_equiv E p q h))
  unfold CombinatorialMap.eulerChar CombinatorialMap.numVertices
    CombinatorialMap.numEdges CombinatorialMap.numFaces
  rw [hc M.rot N.rot hr, hc M.edgeInv N.edgeInv he, hc M.faceSucc N.faceSucc hf]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Every positive-radius ambient ball is planar, by certified finite-stage capture. -/
theorem uibhbotWholePlane_ball_isPlanar (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0) (r : ℕ) (hr : 0 < r)
    (C : UIBHBOTCertifiedRootCapture W r) :
    let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀
    letI : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r} :=
      Classical.decEq _
    (rootedLocallyFiniteBallCombinatorialMap M r).IsPlanar := by
  classical
  intro M
  let u := shiftedStream W C.N
  let s := kmswStage u C.m
  let S := kmswStageBallDarts (fun _ _ => True) s r C.c
  have hflip : ∀ d, d ∈ S → (kmswMap u C.m).edgeInv d ∈ S := by
    intro d hd
    exact (kmswStageBallDarts_edgeFlip (fun _ _ => True) s r C.c d).1 hd
  let A := inducedCombinatorialMap (kmswMap u C.m) S hflip
  let B := kmswStageBallCombinatorialMap (fun _ _ => True) u C.m r C.c
  have hcongr := map_properties_congr A B rfl rfl
  have hconn : B.IsConnected := by
    change (kmswStageBallCombinatorialMap (fun _ _ => True) u C.m r C.c).IsConnected
    rw [← C.dart_center]
    exact kmswStageBallCombinatorialMap_rooted_isConnected u C.m r C.dart hr
  have hne : S.Nonempty := by
    refine ⟨C.dart, ?_⟩
    change C.dart ∈ kmswStageBallDarts (fun _ _ => True) s r C.c
    rw [← C.dart_center]
    exact (kmswStageBallRootEdge_mem u C.m r C.dart hr).1
  have hplanar : B.IsPlanar := hcongr.2.mp
    (inducedCombinatorialMap_isPlanar_of_planar_connected
      (kmswMap u C.m) (kmswMap_isPlanar u C.m) S hflip (hcongr.1.mpr hconn) hne)
  let N := rootedLocallyFiniteBallCombinatorialMap M r
  let E := uibhbotCapturedBallEquiv W H hhit C₀ C
  have hrot : ∀ x, E (B.rot x) = N.rot (E x) :=
    uibhbotCapturedBallEquiv_rot W H hhit C₀ C
  have hedge : ∀ x, E (B.edgeInv x) = N.edgeInv (E x) := by
    intro x
    apply Subtype.ext
    rfl
  exact ⟨rootedLocallyFiniteBallCombinatorialMap_connected M r hr,
    (eulerChar_equiv B N E hrot hedge).symm.trans hplanar.2⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Package the source UIBHBOT as a rooted locally finite planar map on the capture event. -/
@[expose] noncomputable def uibhbotRootedLocallyFinitePlanarMap (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)) :
    RootedLocallyFinitePlanarMap where
  toRootedLocallyFiniteMap := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀
  ball_isPlanar := fun r hr =>
    uibhbotWholePlane_ball_isPlanar W H hhit C₀ r hr (Classical.choice (hcap r))
  outerFace_captured_in_larger_ball :=
    uibhbotWholePlane_outerFace_captured_in_larger_ball W H hhit C₀

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The code law almost surely supplies the constructed planar carrier and all captures. -/
theorem uibhbotCodeLawRel_ae_rootedLocallyFinitePlanarMap :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C₀ : UIBHBOTCertifiedRootCapture W 0)
        (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)),
        (uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap).toRootedLocallyFiniteMap =
          uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀ := by
  filter_upwards [uibhbotCodeLawRel_ae_rootedLocallyFiniteMap] with W hW
  obtain ⟨H, hhit, C₀, hcap, _⟩ := hW
  exact ⟨H, hhit, C₀, hcap, rfl⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Simultaneously every positive-radius ball is planar almost surely under the code law. -/
theorem uibhbotCodeLawRel_ae_ball_isPlanar :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C₀ : UIBHBOTCertifiedRootCapture W 0),
        ∀ r, 0 < r →
          let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C₀
          letI : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r} :=
            Classical.decEq _
          (rootedLocallyFiniteBallCombinatorialMap M r).IsPlanar := by
  filter_upwards [uibhbotCodeLawRel_ae_rootedLocallyFiniteMap] with W hW
  obtain ⟨H, hhit, C₀, hcap, _⟩ := hW
  exact ⟨H, hhit, C₀, fun r hr =>
    uibhbotWholePlane_ball_isPlanar W H hhit C₀ r hr (Classical.choice (hcap r))⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The certified faced ball and the constructed map's faced ball agree at source radius r. -/
noncomputable def uibhbotRootedLocallyFinitePlanarMap_facedBallIso
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r))
    (r : ℕ) (hr : 0 < r) (C : UIBHBOTCertifiedRootCapture W r) :
    FacedFramedBallIso (C.facedBall hr)
      (rootedLocallyFiniteFacedBall
        (uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap) r hr) := by
  classical
  rcases C with ⟨N, m, c, hev, hseams, hcenter, dart, hdcenter, hroot, hmissing⟩
  subst c
  let C : UIBHBOTCertifiedRootCapture W r :=
    ⟨N, m, _, hev, hseams, hcenter, dart, rfl, hroot, hmissing⟩
  change FacedFramedBallIso (C.facedBall hr) _
  let P := uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap
  let M := P.toRootedLocallyFiniteMap
  let A := (C.facedBall hr).toFramedBall
  let B := rootedLocallyFiniteFramedBall P r hr
  let E : A.D ≃ B.D := uibhbotCapturedBallEquiv W H hhit C₀ C
  have hrot (x : A.D) : E (A.map.rot x) = B.map.rot (E x) :=
    uibhbotCapturedBallEquiv_rot W H hhit C₀ C x
  have hedge (x : A.D) : E (A.map.edgeInv x) = B.map.edgeInv (E x) := by
    apply Subtype.ext
    rfl
  have hsymm (x : A.D) : E (A.map.rot.symm x) = B.map.rot.symm (E x) := by
    apply B.map.rot.injective
    rw [← hrot, A.map.rot.apply_symm_apply, B.map.rot.apply_symm_apply]
  have hface (x : A.D) : E (A.map.faceSucc x) = B.map.faceSucc (E x) := by
    change E (A.map.rot.symm (A.map.edgeInv x)) =
      B.map.rot.symm (B.map.edgeInv (E x))
    rw [hsymm, hedge]
  have hcycles := framedBall_sameCycle_iff_of_equiv E A.map.faceSucc B.map.faceSucc hface
  have hside := uibhbotRelaxedCapture_rootDart_side W N m _ hcenter dart rfl hroot
  have hrootE : E A.rootDart = B.rootDart := by
    apply Subtype.ext
    change (wholePlaneEdgeι W N dart.1.val, !dart.2) = (uibhbotRootEdge W, false)
    exact Prod.ext hroot (by rw [hside]; rfl)
  have hbase : E (A.map.edgeInv A.rootDart) = B.map.edgeInv B.rootDart := by
    rw [hedge, hrootE]
  have hoA : A.map.IsOuter (A.map.edgeInv A.rootDart) :=
    uibhbotRelaxedCapturedStageFramedBall_outer_root W r hr N m _ hev hcenter
      dart rfl hroot hmissing
  have hoB : B.map.IsOuter (B.map.edgeInv B.rootDart) := by
    apply rootedLocallyFiniteBall_outer_survives P r hr
    exact Equiv.Perm.SameCycle.rfl
  have hmissingE (x : A.D) : B.map.missing (E x) ↔ A.map.missing x := by
    have hp := relStage_wholePlane_present W r N m _ hev
      (fun Q h k hk => (hseams Q h k hk).1) x
    change (¬ wholePlaneEdgePresent W (wholePlaneEdgeι W N x.1.1.val)) ↔
      (kmswStage (shiftedStream W N) m).present x.1.1.val = false
    rw [hp]
    cases (kmswStage (shiftedStream W N) m).present x.1.1.val <;> simp
  have htailE (x : A.D) : B.map.tail (E x) ↔ A.map.tail x := by
    have hp := relStage_wholePlane_present W r N m _ hev
      (fun Q h k hk => (hseams Q h k hk).1) x
    change (¬ x.1.2 ∧ wholePlaneEdgePresent W (wholePlaneEdgeι W N x.1.1.val)) ↔
      ((kmswStage (shiftedStream W N) m).present x.1.1.val = true ∧ x.1.2 = false)
    rw [hp]
    cases x.1.2 <;> simp
  refine ⟨{
    mapIso := {
      toEquiv := E
      rot_comm := hrot
      edgeInv_comm := hedge
      missing_iff := hmissingE
      tail_iff := htailE
      outer_iff := ?_ }
    root_vertex := ?_
    frameEdge_comm := hrootE
    frameOther_comm := ?_ }, ?_⟩
  · intro x
    constructor
    · intro hx
      apply hoA.trans
      apply (hcycles _ _).2
      rw [hbase]
      exact hoB.symm.trans hx
    · intro hx
      apply hoB.trans
      rw [← hbase]
      exact (hcycles _ _).1 (hoA.symm.trans hx)
  · rw [hrootE]
  · right
    refine ⟨E (A.map.edgeInv A.rootDart), B.map.edgeInv B.rootDart, ?_, rfl, ?_⟩
    · change some (E ⟨dart, _⟩) = some (E (A.map.edgeInv A.rootDart))
      apply congrArg some
      apply congrArg E
      apply Subtype.ext
      change dart = (dart.1, !(!dart.2))
      exact Prod.ext rfl (Bool.not_not dart.2).symm
    · rw [hbase]
  · intro x
    rw [C.facedBall_original_iff H hr]
    change (∀ e, (wholePlaneFaceSucc W H).SameCycle
        (wholePlaneDartι W N (x.1.1.val, x.1.2)) e →
          e ∈ rootedLocallyFiniteBallDarts M r) ↔ _
    exact forall_congr' fun e => imp_congr Iff.rfl
      (uibhbotWholePlane_ballDarts_iff W H hhit C₀ r e)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The constructed map has the canonical faced UIBHBOT class at every positive source radius. -/
theorem uibhbotRootedLocallyFinitePlanarMap_facedBallClass_eq
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r))
    (r : ℕ) (hr : 0 < r) :
    Quotient.mk FacedFramedBall.setoid
        (rootedLocallyFiniteFacedBall
          (uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap) r hr) =
      facedUIBHBOTBallClassRel W r hr := by
  let C := Classical.choice (hcap r)
  rw [facedUIBHBOTBallClassRel_eq_capture W H r hr C]
  exact Quotient.sound
    ⟨(uibhbotRootedLocallyFinitePlanarMap_facedBallIso W H hhit C₀ hcap r hr C).symm⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The class-system index r denotes source radius r+1 on both sides. -/
theorem uibhbotRootedLocallyFinitePlanarMap_facedBallClass_index_eq
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C₀ : UIBHBOTCertifiedRootCapture W 0)
    (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)) (r : ℕ) :
    rootedLocallyFiniteFacedBallClass r
        (uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap) =
      facedUIBHBOTBallClassRel W (r + 1) (Nat.succ_pos r) :=
  uibhbotRootedLocallyFinitePlanarMap_facedBallClass_eq W H hhit C₀ hcap
    (r + 1) (Nat.succ_pos r)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
All faced-ball classes of the constructed carrier agree simultaneously almost surely. -/
theorem uibhbotCodeLawRel_ae_rootedLocallyFinitePlanarMap_facedBallClass :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C₀ : UIBHBOTCertifiedRootCapture W 0)
        (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)),
        ∀ r (hr : 0 < r),
          Quotient.mk FacedFramedBall.setoid
              (rootedLocallyFiniteFacedBall
                (uibhbotRootedLocallyFinitePlanarMap W H hhit C₀ hcap) r hr) =
            facedUIBHBOTBallClassRel W r hr := by
  filter_upwards [uibhbotCodeLawRel_ae_rootedLocallyFiniteMap] with W hW
  obtain ⟨H, hhit, C₀, hcap, _⟩ := hW
  exact ⟨H, hhit, C₀, hcap,
    uibhbotRootedLocallyFinitePlanarMap_facedBallClass_eq W H hhit C₀ hcap⟩

end DirectedDistances.KMSW
