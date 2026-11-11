module

public import DirectedDistances.PaperProofs.Section5.DiskRootedMapObject
public import DirectedDistances.PlanarMap.FacedFramedBall
public import DirectedDistances.PlanarMap.KMSWStageFacedFramedBall

import DirectedDistances.PaperProofs.Section5.DiskBSBallRestriction

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] def diskRootedMapOfCodeMark_ballPlanarityObligation {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1))
    : Prop :=
  ∀ r, 0 < r →
    let M := diskRootedMapOfCodeMark c k
    letI : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r} :=
      Classical.decEq _
    (rootedLocallyFiniteBallCombinatorialMap M r).IsPlanar

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] def diskRootedMapOfCodeMark_outerFaceCaptureObligation {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) : Prop :=
  let M := diskRootedMapOfCodeMark c k
  ∀ r, 0 < r → ∀ d, d ∈ rootedLocallyFiniteBallDarts M r →
    Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv) M.outer d →
      ∃ R, r ≤ R ∧
        ∃ hdR : d ∈ rootedLocallyFiniteBallDarts M R,
        ∃ hfR : rootedLocallyFiniteOuterFrameDart M ∈
            rootedLocallyFiniteBallDarts M R,
        letI : DecidableEq {e : M.D // e ∈ rootedLocallyFiniteBallDarts M R} :=
          Classical.decEq _
        CombinatorialMap.IsOuter
          (rootedLocallyFiniteBallCombinatorialMap M R)
          ⟨rootedLocallyFiniteOuterFrameDart M, hfR⟩ ⟨d, hdR⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] def diskRootedMapOfCodeMark_facedBallIsoObligation {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1))
    (M : RootedLocallyFinitePlanarMap)
    (_hM : M.toRootedLocallyFiniteMap = diskRootedMapOfCodeMark c k) : Prop :=
  ∀ r (hr : 0 < r),
    Nonempty (FacedFramedBallIso
      (rootedLocallyFiniteFacedBall M r hr)
      (kmswDiskStageFacedFramedBall c k r hr))

private theorem finite_ball_exhaustion (M : RootedLocallyFiniteMap) [Fintype M.D]
    (r : ℕ) : ∃ R, r ≤ R ∧ ∀ d : M.D, d ∈ rootedLocallyFiniteBallDarts M R := by
  classical
  choose radius hradius using rootedLocallyFinite_dart_reachable M
  let R := max r (Finset.univ.sup radius)
  have hvertex (d : M.D) : rootedLocallyFiniteVertexClassOf M d ∈
      rootedLocallyFiniteRadiusVertices M R := by
    apply rootedLocallyFiniteRadiusVertices_mono M
      (le_trans (Finset.le_sup (Finset.mem_univ d)) (le_max_right _ _))
    exact (mem_rootedLocallyFiniteRadiusVertices M _ _).2 (hradius d)
  exact ⟨R, le_max_left _ _, fun d =>
    (mem_rootedLocallyFiniteBallDarts M R d).2 ⟨hvertex d, hvertex (M.edgeInv d)⟩⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
by a sufficiently large all-geometric ball, also beyond any prescribed radius. -/
theorem diskRootedMapOfCodeMark_ball_exhaustion {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) (r : ℕ) :
    ∃ R, r ≤ R ∧ ∀ d : (diskRootedMapOfCodeMark c k).D,
      d ∈ rootedLocallyFiniteBallDarts (diskRootedMapOfCodeMark c k) R := by
  let : Fintype (diskRootedMapOfCodeMark c k).D := inferInstanceAs
    (Fintype (StageDart (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).nextEdge))
  exact finite_ball_exhaustion _ r

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
all ambient face incidences, including the selected outer-facing frame dart. -/
theorem diskRootedMapOfCodeMark_outerFaceCaptureObligation_holds {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) :
    diskRootedMapOfCodeMark_outerFaceCaptureObligation c k := by
  classical
  intro r _ d _ hd
  let M := diskRootedMapOfCodeMark c k
  obtain ⟨R, hrR, hR⟩ := diskRootedMapOfCodeMark_ball_exhaustion c k r
  refine ⟨R, hrR, hR d, hR (rootedLocallyFiniteOuterFrameDart M), ?_⟩
  let N := rootedLocallyFiniteBallCombinatorialMap M R
  let E : {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} ≃ M.D := {
    toFun := Subtype.val
    invFun := fun d => ⟨d, hR d⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let : Finite M.D := by
    change Finite (StageDart (kmswStage
      (finiteCodeExtend (n := n + 1) c.val) n).nextEdge)
    infer_instance
  have hface (x) : E (N.faceSucc x) = (M.rot.symm * M.edgeInv) (E x) :=
    rootedLocallyFiniteBall_faceSucc_of_mem M R x (hR _)
  have hcycle := (rootedLocallyFiniteOuterFrameDart_outer M).symm.trans hd
  exact (sameCycle_iff_of_intertwine N.faceSucc (M.rot.symm * M.edgeInv)
    E hface _ _).2 hcycle

private theorem map_properties_congr {D : Type} {f g : Fintype D}
    {de df : DecidableEq D}
    (A : @CombinatorialMap D f de) (B : @CombinatorialMap D g df)
    (hedge : @CombinatorialMap.edgeInv D f de A =
      @CombinatorialMap.edgeInv D g df B)
    (hrot : @CombinatorialMap.rot D f de A = @CombinatorialMap.rot D g df B) :
    (@CombinatorialMap.IsConnected D f de A ↔
      @CombinatorialMap.IsConnected D g df B) ∧
    (@CombinatorialMap.IsPlanar D f de A ↔
      @CombinatorialMap.IsPlanar D g df B) := by
  have hf : f = g := Subsingleton.elim _ _
  cases hf
  have hd : de = df := Subsingleton.elim _ _
  cases hd
  have hAB : A = B := by
    cases A
    cases B
    cases hedge
    cases hrot
    rfl
  subst B
  exact ⟨Iff.rfl, Iff.rfl⟩

@[reducible] private noncomputable def diskDartFintype {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) :
    Fintype (diskRootedMapOfCodeMark c k).D := inferInstanceAs
  (Fintype (StageDart (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).nextEdge))

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
the planar finite KMSW stage is planar. -/
theorem diskRootedMapOfCodeMark_ballPlanarityObligation_holds {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) :
    diskRootedMapOfCodeMark_ballPlanarityObligation c k := by
  classical
  intro r hr
  let M := diskRootedMapOfCodeMark c k
  let u := finiteCodeExtend (n := n + 1) c.val
  let : Fintype M.D := diskDartFintype c k
  let A : CombinatorialMap M.D := {
    edgeInv := M.edgeInv
    edgeInv_invol := M.edgeInv_invol
    edgeInv_ne := M.edgeInv_ne
    rot := M.rot }
  have hA : A.IsPlanar :=
    (map_properties_congr A (kmswMap u n) rfl rfl).2.mpr (kmswMap_isPlanar u n)
  let S := rootedLocallyFiniteBallDarts M r
  have hflip : ∀ d, d ∈ S → A.edgeInv d ∈ S :=
    rootedLocallyFiniteBallDarts_edgeInv_closed M r
  let N := inducedCombinatorialMap A S hflip
  let B := rootedLocallyFiniteBallCombinatorialMap M r
  have hmaps := map_properties_congr N B rfl rfl
  have hconn := hmaps.1.mpr (rootedLocallyFiniteBallCombinatorialMap_connected M r hr)
  have hplanar := inducedCombinatorialMap_isPlanar_of_planar_connected A
    hA S hflip hconn ⟨M.rootDart, (rootedLocallyFiniteBallDarts_frame_mem M hr).1⟩
  exact hmaps.2.mp hplanar

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
marked missing edge defines a rooted locally finite planar map. -/
@[expose] noncomputable def diskRootedPlanarMapOfCodeMark {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) :
    RootedLocallyFinitePlanarMap where
  toRootedLocallyFiniteMap := diskRootedMapOfCodeMark c k
  ball_isPlanar := diskRootedMapOfCodeMark_ballPlanarityObligation_holds c k
  outerFace_captured_in_larger_ball :=
    diskRootedMapOfCodeMark_outerFaceCaptureObligation_holds c k

private noncomputable def diskVertexId {ell n : ℕ} (c : KMSWLeftWalkClass ell n)
    (k : Fin (ell - 1))
    (v : RootedLocallyFiniteVertex (diskRootedMapOfCodeMark c k).D
      (diskRootedMapOfCodeMark c k).rot) : ℕ :=
  (stageVertexEquiv (finiteCodeExtend (n := n + 1) c.val) n v).val

private theorem disk_vertexClass_eq_iff {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1))
    (d e : (diskRootedMapOfCodeMark c k).D) :
    rootedLocallyFiniteVertexClassOf (diskRootedMapOfCodeMark c k) d =
        rootedLocallyFiniteVertexClassOf (diskRootedMapOfCodeMark c k) e ↔
      stageEndpoint (kmswStage (finiteCodeExtend (n := n + 1) c.val) n) d =
        stageEndpoint (kmswStage (finiteCodeExtend (n := n + 1) c.val) n) e := by
  constructor
  · intro h
    exact congrArg (diskVertexId c k) h
  · intro h
    exact Quotient.sound ((stageRot_sameCycle_iff_endpoint_eq _ _ _ _).2 h)

private theorem disk_withinRadius_iff {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) (r : ℕ)
    (d : (diskRootedMapOfCodeMark c k).D) :
    rootedLocallyFiniteWithinRadius (diskRootedMapOfCodeMark c k) r
        (rootedLocallyFiniteVertexClassOf (diskRootedMapOfCodeMark c k) d) ↔
      kmswStageDistanceLe (fun _ _ => True)
        (kmswStage (finiteCodeExtend (n := n + 1) c.val) n) r
        (stageEndpoint (kmswStage (finiteCodeExtend (n := n + 1) c.val) n)
          (edgeFlip _ (kmswDiskRootDart c k)))
        (stageEndpoint (kmswStage (finiteCodeExtend (n := n + 1) c.val) n) d) := by
  let M := diskRootedMapOfCodeMark c k
  let u := finiteCodeExtend (n := n + 1) c.val
  let s := kmswStage u n
  let center := stageEndpoint s (edgeFlip _ (kmswDiskRootDart c k))
  constructor
  · intro h
    have forward {r v} (h : rootedLocallyFiniteWithinRadius M r v) :
        kmswStageDistanceLe (fun _ _ => True) s r center (diskVertexId c k v) := by
      induction h with
      | root => exact ⟨0, le_rfl, .nil (Set.mem_univ _)⟩
      | stay h ih => exact kmswStageDistanceLe_mono _ _ (Nat.le_succ _) ih
      | @edge r v w h hstep ih =>
        obtain ⟨e, he, hf⟩ := hstep
        obtain ⟨j, hj, hp⟩ := ih
        refine ⟨j + 1, Nat.succ_le_succ hj,
          .snoc hp (Set.mem_univ _) (Set.mem_univ _) ?_⟩
        exact ⟨e, trivial, congrArg (diskVertexId c k) he,
          congrArg (diskVertexId c k) hf⟩
    exact forward h
  · rintro ⟨j, hj, hp⟩
    have backward {j v} (hp : KMSWStagePath (fun _ _ => True) s Set.univ center j v) :
        ∀ e : M.D, stageEndpoint s e = v →
          rootedLocallyFiniteWithinRadius M j (rootedLocallyFiniteVertexClassOf M e) := by
      induction hp with
      | nil _ =>
        intro e he
        have hc : rootedLocallyFiniteVertexClassOf M e =
            rootedLocallyFiniteVertexClassOf M M.rootDart :=
          (disk_vertexClass_eq_iff c k _ _).2 he
        rw [hc]
        exact .root
      | @snoc j y z hp _ _ hadj ih =>
        intro e he
        obtain ⟨a, _, ha, hf⟩ := hadj
        have hpre := ih a ha
        have hn := rootedLocallyFiniteWithinRadius.edge hpre ⟨a, rfl, rfl⟩
        have heq : rootedLocallyFiniteVertexClassOf M (M.edgeInv a) =
            rootedLocallyFiniteVertexClassOf M e :=
          (disk_vertexClass_eq_iff c k _ _).2 (hf.trans he.symm)
        change rootedLocallyFiniteWithinRadius M (j + 1)
          (rootedLocallyFiniteVertexClassOf M (M.edgeInv a)) at hn
        rw [heq] at hn
        exact hn
    have hshort := backward hp d rfl
    exact (mem_rootedLocallyFiniteRadiusVertices M r _).1
      (rootedLocallyFiniteRadiusVertices_mono M hj
        ((mem_rootedLocallyFiniteRadiusVertices M j _).2 hshort))

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
use exactly the same all-geometric radius r, including radius zero. -/
theorem diskRootedMapOfCodeMark_ballDarts_eq {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) (r : ℕ) :
    rootedLocallyFiniteBallDarts (diskRootedMapOfCodeMark c k) r =
      kmswStageBallDarts (fun _ _ => True)
        (kmswStage (finiteCodeExtend (n := n + 1) c.val) n) r
        (stageEndpoint (kmswStage (finiteCodeExtend (n := n + 1) c.val) n)
          (edgeFlip _ (kmswDiskRootDart c k))) := by
  classical
  ext d
  exact (mem_rootedLocallyFiniteBallDarts _ r d).trans
    ((and_congr
      ((mem_rootedLocallyFiniteRadiusVertices _ r _).trans
        (disk_withinRadius_iff c k r d))
      ((mem_rootedLocallyFiniteRadiusVertices _ r _).trans
        (disk_withinRadius_iff c k r _))).trans
      (kmswStageBallDarts_mem_iff_distanceLe (fun _ _ => True)
        (finiteCodeExtend (n := n + 1) c.val) n r _ d).symm)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
independent of the decidable-equality instance and proofs of return. -/
theorem diskFirstReturn_val_congr {D : Type} {de df : DecidableEq D}
    (p q : Equiv.Perm D) (hpq : p = q) (S T : Finset D) (hST : S = T)
    (hS : ∀ x : S, ∃ j : ℕ, 0 < j ∧ (p ^ j) x.1 ∈ S)
    (hT : ∀ x : T, ∃ j : ℕ, 0 < j ∧ (q ^ j) x.1 ∈ T)
    (x : S) (y : T) (hxy : x.1 = y.1) :
    (@cyclicFirstReturn D de p S hS x).1 =
      (@cyclicFirstReturn D df q T hT y).1 := by
  have hd : de = df := Subsingleton.elim _ _
  cases hd
  subst q
  subst T
  have h : x = y := Subtype.ext hxy
  subst y
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
exactly when every vertex on its ambient boundary orbit is retained. -/
theorem diskRootedMapOfCodeMark_original_iff {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) (r : ℕ)
    (d : (diskRootedMapOfCodeMark c k).D) :
    rootedLocallyFiniteBallContainsOriginalFace (diskRootedMapOfCodeMark c k) r d ↔
      ∀ j : ℕ,
        stageEndpoint (kmswStage (finiteCodeExtend (n := n + 1) c.val) n)
          (((kmswMap (finiteCodeExtend (n := n + 1) c.val) n).faceSucc ^ j) d) ∈
        kmswStageBallVertices (fun _ _ => True)
          (kmswStage (finiteCodeExtend (n := n + 1) c.val) n) r
          (stageEndpoint (kmswStage (finiteCodeExtend (n := n + 1) c.val) n)
            (edgeFlip _ (kmswDiskRootDart c k))) := by
  let M := diskRootedMapOfCodeMark c k
  let u := finiteCodeExtend (n := n + 1) c.val
  let s := kmswStage u n
  let p := (kmswMap u n).faceSucc
  have hmem := Finset.ext_iff.mp (diskRootedMapOfCodeMark_ballDarts_eq c k r)
  have hfaceend (e : M.D) : stageEndpoint s (p e) =
      stageEndpoint s (edgeFlip _ e) := by
    apply (stageRot_sameCycle_iff_endpoint_eq u n _ _).1
    change (stageRot u n).SameCycle ((stageRot u n).symm (edgeFlip _ e)) _
    exact ⟨1, by rw [zpow_one, Equiv.apply_symm_apply]⟩
  constructor
  · intro h j
    have hj : (p ^ j) d ∈ rootedLocallyFiniteBallDarts M r :=
      h _ ⟨(j : ℤ), by rw [zpow_natCast]; rfl⟩
    exact ((kmswStageBallDarts_mem_iff _ _ _ _ _).1 ((hmem _).1 hj)).1
  · intro h e he
    let : Finite M.D := by
      change Finite (StageDart (kmswStage u n).nextEdge)
      infer_instance
    obtain ⟨j, hj⟩ := he.exists_nat_pow_eq
    apply (hmem e).2
    apply (kmswStageBallDarts_mem_iff _ _ _ _ e).2
    have hj' : (p ^ j) d = e := hj
    refine ⟨?_, ?_⟩
    · rw [← hj']
      exact h j
    · have hnext := h (j + 1)
      change stageEndpoint s ((p ^ (j + 1)) d) ∈ _ at hnext
      rw [pow_succ'] at hnext
      change stageEndpoint s (p ((p ^ j) d)) ∈ _ at hnext
      have hh : stageEndpoint s (p e) ∈ _ := hj' ▸ hnext
      exact (hfaceend e) ▸ hh

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
source radius r, without an index shift, and retain all original faces. -/
@[expose] noncomputable def diskRootedPlanarMapOfCodeMark_facedBallIso {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) (r : ℕ) (hr : 0 < r) :
    FacedFramedBallIso
      (rootedLocallyFiniteFacedBall (diskRootedPlanarMapOfCodeMark c k) r hr)
      (kmswDiskStageFacedFramedBall c k r hr) := by
  classical
  let M := diskRootedMapOfCodeMark c k
  let P := diskRootedPlanarMapOfCodeMark c k
  let u := finiteCodeExtend (n := n + 1) c.val
  let B := rootedLocallyFiniteFramedBall P r hr
  let C := kmswDiskStageFramedBall c k r hr
  have hmem := Finset.ext_iff.mp (diskRootedMapOfCodeMark_ballDarts_eq c k r)
  let E : B.D ≃ C.D := {
    toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
    invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hrot (x : B.D) : E (B.map.rot x) = C.map.rot (E x) := by
    apply Subtype.ext
    exact diskFirstReturn_val_congr M.rot (stageRot u n) rfl _ _
      (diskRootedMapOfCodeMark_ballDarts_eq c k r) _ _ x (E x) rfl
  have hedge (x : B.D) : E (B.map.edgeInv x) = C.map.edgeInv (E x) := by
    apply Subtype.ext
    rfl
  have hsymm (x : B.D) : E (B.map.rot.symm x) = C.map.rot.symm (E x) := by
    apply C.map.rot.injective
    rw [← hrot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hface (x : B.D) : E (B.map.faceSucc x) = C.map.faceSucc (E x) := by
    change E (B.map.rot.symm (B.map.edgeInv x)) =
      C.map.rot.symm (C.map.edgeInv (E x))
    rw [hsymm, hedge]
  have hcycles := framedBall_sameCycle_iff_of_equiv E B.map.faceSucc C.map.faceSucc hface
  have houter : C.map.faceSucc.SameCycle C.map.outer (E B.map.outer) := by
    apply kmswDiskRootDart_ball_outer_survives c k r hr
    exact rootedLocallyFiniteOuterFrameDart_outer M
  refine ⟨{
    mapIso := {
      toEquiv := E
      rot_comm := hrot
      edgeInv_comm := hedge
      missing_iff := fun _ => Iff.rfl
      tail_iff := fun _ => Iff.rfl
      outer_iff := ?_ }
    root_vertex := ?_
    frameEdge_comm := ?_
    frameOther_comm := ?_ }, ?_⟩
  · intro x
    exact ⟨fun h => (hcycles _ _).2 (houter.symm.trans h),
      fun h => houter.trans ((hcycles _ _).1 h)⟩
  · change C.map.rot.SameCycle (E B.rootDart) C.rootDart
    have heq : E B.rootDart = C.rootDart := Subtype.ext rfl
    rw [heq]
  · exact Subtype.ext rfl
  · right
    refine ⟨E (B.map.edgeInv B.frameEdgeDart), C.map.edgeInv C.frameEdgeDart,
      ?_, ?_, ?_⟩
    · rfl
    · exact (kmswDiskStageFramedBall_root_spec c k r hr).2.2.1
    · have heq : E (B.map.edgeInv B.frameEdgeDart) =
          C.map.edgeInv C.frameEdgeDart := by
        rw [hedge]
        rfl
      rw [heq]
      exact Equiv.Perm.SameCycle.rfl
  · intro x
    exact (diskRootedMapOfCodeMark_original_iff c k r x.1).symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
planar extension of the disk rooted map, at the same positive source radius. -/
theorem diskRootedMapOfCodeMark_facedBallIsoObligation_holds {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1))
    (M : RootedLocallyFinitePlanarMap)
    (hM : M.toRootedLocallyFiniteMap = diskRootedMapOfCodeMark c k) :
    diskRootedMapOfCodeMark_facedBallIsoObligation c k M hM := by
  have heq : M = diskRootedPlanarMapOfCodeMark c k := by
    cases M
    cases hM
    rfl
  subst M
  intro r hr
  exact ⟨diskRootedPlanarMapOfCodeMark_facedBallIso c k r hr⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
exactly the same positive source radius r. -/
theorem diskRootedPlanarMapOfCodeMark_facedBallClass_eq {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) (r : ℕ) (hr : 0 < r) :
    Quotient.mk FacedFramedBall.setoid
        (rootedLocallyFiniteFacedBall (diskRootedPlanarMapOfCodeMark c k) r hr) =
      Quotient.mk FacedFramedBall.setoid (kmswDiskStageFacedFramedBall c k r hr) :=
  Quotient.sound ⟨diskRootedPlanarMapOfCodeMark_facedBallIso c k r hr⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
source radius r+1 on both sides of this equality. -/
theorem diskRootedPlanarMapOfCodeMark_facedBallClass_index_eq {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) (r : ℕ) :
    rootedLocallyFiniteFacedBallClass r (diskRootedPlanarMapOfCodeMark c k) =
      Quotient.mk FacedFramedBall.setoid
        (kmswDiskStageFacedFramedBall c k (r + 1) (Nat.succ_pos r)) :=
  diskRootedPlanarMapOfCodeMark_facedBallClass_eq c k (r + 1) (Nat.succ_pos r)

end DirectedDistances.PaperProofs.Section5
