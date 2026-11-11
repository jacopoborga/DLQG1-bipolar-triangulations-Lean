module

public import DirectedDistances.PaperProofs.Section5.DiskWindowClassField
import DirectedDistances.KMSW.BoundaryVertexVisits

/-! Helpers toward Proposition 5.16 (`prop-disk-bs-conv`), not paper results.
The ordered missing frame determines the outer face once its opposite
incidence is known to belong to that face. Representatives need not agree. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A commuting equivalence preserves face and vertex orbits. -/
theorem framedIso_sameCycle_transport {D E : Type} [Finite D] [Finite E]
    (e : D ≃ E) (σ : Equiv.Perm D) (τ : Equiv.Perm E)
    (hcomm : ∀ d, e (σ d) = τ (e d)) (a b : D) :
    τ.SameCycle (e a) (e b) ↔ σ.SameCycle a b := by
  have hp (j : ℕ) (d : D) : e ((σ ^ j) d) = (τ ^ j) (e d) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, hcomm, ih,
        pow_succ', Equiv.Perm.mul_apply]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := h.exists_nat_pow_eq
    refine ⟨(j : ℤ), ?_⟩
    rw [zpow_natCast]
    exact e.injective ((hp j a).trans hj)
  · intro h
    obtain ⟨j, hj⟩ := h.exists_nat_pow_eq
    refine ⟨(j : ℤ), ?_⟩
    rw [zpow_natCast, ← hp, hj]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A rotation and edge compatible equivalence preserving the ordered frame and
its tags preserves the outer face automatically when the opposite frame -/
@[expose] def framedBallIso_of_orderedFrame
    (M N : FramedBall) (e : M.D ≃ N.D)
    (hrot : ∀ d, e (M.map.rot d) = N.map.rot (e d))
    (hflip : ∀ d, e (M.map.edgeInv d) = N.map.edgeInv (e d))
    (hmissing : ∀ d, N.map.missing (e d) ↔ M.map.missing d)
    (htail : ∀ d, N.map.tail (e d) ↔ M.map.tail d)
    (hframe : e M.frameEdgeDart = N.frameEdgeDart)
    (hmroot : M.rootDart = M.frameEdgeDart)
    (hnroot : N.rootDart = N.frameEdgeDart)
    (hmother : M.frameOtherDart = some (M.map.edgeInv M.frameEdgeDart))
    (hnother : N.frameOtherDart = some (N.map.edgeInv N.frameEdgeDart))
    (hmouter : M.map.IsOuter (M.map.edgeInv M.frameEdgeDart))
    (hnouter : N.map.IsOuter (N.map.edgeInv N.frameEdgeDart)) :
    FramedBallIso M N := by
  have hinv (d : M.D) : e (M.map.rot.symm d) = N.map.rot.symm (e d) := by
    apply N.map.rot.injective
    rw [← hrot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hface (d : M.D) : e (M.map.faceSucc d) = N.map.faceSucc (e d) := by
    change e (M.map.rot.symm (M.map.edgeInv d)) =
      N.map.rot.symm (N.map.edgeInv (e d))
    rw [hinv, hflip]
  have hf : e (M.map.edgeInv M.frameEdgeDart) =
      N.map.edgeInv N.frameEdgeDart := by rw [hflip, hframe]
  have ho : N.map.faceSucc.SameCycle (e M.map.outer) N.map.outer := by
    have h := (framedIso_sameCycle_transport e M.map.faceSucc N.map.faceSucc hface
      M.map.outer (M.map.edgeInv M.frameEdgeDart)).mpr hmouter
    rw [hf] at h
    exact h.trans hnouter.symm
  refine
    { mapIso :=
        { toEquiv := e
          rot_comm := hrot
          edgeInv_comm := hflip
          missing_iff := hmissing
          tail_iff := htail
          outer_iff := ?_ }
      root_vertex := ?_
      frameEdge_comm := hframe
      frameOther_comm := ?_ }
  · intro d
    constructor
    · intro hd
      exact (framedIso_sameCycle_transport e M.map.faceSucc N.map.faceSucc hface
        M.map.outer d).mp (ho.trans hd)
    · intro hd
      exact ho.symm.trans ((framedIso_sameCycle_transport e M.map.faceSucc N.map.faceSucc hface
        M.map.outer d).mpr hd)
  · rw [hmroot, hframe, hnroot]
  · right
    refine ⟨N.map.edgeInv N.frameEdgeDart, N.map.edgeInv N.frameEdgeDart,
      ?_, hnother, Equiv.Perm.SameCycle.rfl⟩
    rw [hmother, Option.map_some, hf]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The disk's outer representative is exactly its other frame incidence. -/
theorem diskStageFramedBall_outer_frame {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) (r : ℕ) (hr : 0 < r) :
    let B := kmswDiskStageFramedBall c k r hr
    B.map.outer = B.map.edgeInv B.frameEdgeDart := by
  dsimp only
  apply Subtype.ext
  exact ((kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n).edgeInv_invol
    (kmswDiskRootDart c k)).symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The local constructor has the canonical ordered frame, and an ambient outer
root remains on its chosen outer face. -/
theorem inducedLocalFramedBall_orderedFrame
    {D : Type} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (S : Finset D)
    (hf : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hp : M.toCombinatorialMap.IsPlanar)
    (hc : (inducedCombinatorialMap M.toCombinatorialMap S hf).IsConnected)
    (root : S) (hm : M.missing root.1) (ho : M.IsOuter root.1) :
    let B := uibhbotInducedLocalFramedBallRel M S hf hp hc root hm
    B.rootDart = B.frameEdgeDart ∧
      B.frameOtherDart = some (B.map.edgeInv B.frameEdgeDart) ∧
      B.map.IsOuter (B.map.edgeInv B.frameEdgeDart) := by
  classical
  dsimp only
  let B := uibhbotInducedLocalFramedBallRel M S hf hp hc root hm
  have hroot : (B.map.edgeInv B.frameEdgeDart).1 = root.1 :=
    M.edgeInv_invol root.1
  refine ⟨rfl, ?_, ?_⟩
  · apply congrArg some
    apply Subtype.ext
    exact hroot.symm
  · have hex : ∃ o : D, o ∈ S ∧ M.IsOuter o := ⟨root.1, root.2, ho⟩
    dsimp only [B, uibhbotInducedLocalFramedBallRel,
      inducedFramedBallOfMissingRoot, inducedDirectedMapWithMissing,
      DirectedMapWithMissing.IsOuter, CombinatorialMap.IsOuter]
    apply inducedCombinatorialMap_face_sameCycle_of_connected_planar
    · exact hp
    · exact hc
    · exact (Classical.choose_spec hex).2.symm.trans (hroot.symm ▸ ho)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
At an allocated missing dart the stage-data selector takes its valid local -/
theorem stageDataBallClass_eq_localFrame (u : ℕ → Fin 3) (m r : ℕ)
    (hr : 0 < r) (d : StageDart (kmswStage u m).nextEdge)
    (hm : (kmswStageDirectedMap u m).missing d) :
    let M := kmswStageDirectedMap u m
    let S := kmswStageBallDarts (fun _ _ => True) (kmswStage u m) r
      (stageEndpoint (kmswStage u m) (edgeFlip _ d))
    let hf := fun e he => (kmswStageBallDarts_edgeFlip
      (fun _ _ => True) (kmswStage u m) r
      (stageEndpoint (kmswStage u m) (edgeFlip _ d)) e).mp he
    uibhbotStageDataBallClassRel ⟨kmswStage u m, M⟩ r d.1.val d.2 =
      Quotient.mk FramedBall.setoid
        (uibhbotInducedLocalFramedBallRel M S hf (kmswMap_isPlanar u m)
          (kmswStageBallCombinatorialMap_rooted_isConnected u m r d hr)
          ⟨d, (kmswStageBallRootEdge_mem u m r d hr).1⟩ hm) := by
  classical
  dsimp only
  unfold uibhbotStageDataBallClassRel
  rw [dite_eq_left d.1.isLt]
  dsimp only
  have hd : ((⟨d.1.val, d.1.isLt⟩, d.2) : StageDart _) = d := rfl
  simp only [hd]
  rw [dite_eq_left, dite_eq_left]
  · rfl
  · exact ⟨kmswMap_isPlanar u m,
      kmswStageBallCombinatorialMap_rooted_isConnected u m r d hr,
      (kmswStageBallRootEdge_mem u m r d hr).1, hm⟩
  · intro e he
    exact (kmswStageBallDarts_edgeFlip (fun _ _ => True) (kmswStage u m) r
      (stageEndpoint (kmswStage u m) (edgeFlip _ d)) e).mp he

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The disk framed class is exactly its finite stage-data class, despite the
local selector's potentially different representative of the outer face. -/
theorem diskStageFramedBall_class_eq_stageData {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) (r : ℕ) (hr : 0 < r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    Quotient.mk FramedBall.setoid (kmswDiskStageFramedBall c k r hr) =
      uibhbotStageDataBallClassRel ⟨kmswStage u n, kmswStageDirectedMap u n⟩ r
        (kmswLLCreatedEdge u (kmswDiskFirstHit c k)) true := by
  classical
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let d := kmswDiskRootDart c k
  let M := kmswStageDirectedMap u n
  let S := kmswStageBallDarts (fun _ _ => True) (kmswStage u n) r
    (stageEndpoint (kmswStage u n) (edgeFlip _ d))
  let hf := fun e he => (kmswStageBallDarts_edgeFlip (fun _ _ => True)
    (kmswStage u n) r (stageEndpoint (kmswStage u n) (edgeFlip _ d)) e).mp he
  let root : S := ⟨d, (kmswStageBallRootEdge_mem u n r d hr).1⟩
  let B := kmswDiskStageFramedBall c k r hr
  let C := uibhbotInducedLocalFramedBallRel M S hf (kmswMap_isPlanar u n)
    (kmswStageBallCombinatorialMap_rooted_isConnected u n r d hr)
    root (kmswDiskRootDart_missing c k)
  have hC := inducedLocalFramedBall_orderedFrame M S hf (kmswMap_isPlanar u n)
    (kmswStageBallCombinatorialMap_rooted_isConnected u n r d hr)
    root (kmswDiskRootDart_missing c k) (kmswDiskRootDart_ambient_isOuter c k)
  change Quotient.mk FramedBall.setoid B =
    uibhbotStageDataBallClassRel ⟨kmswStage u n, M⟩ r d.1.val d.2
  rw [stageDataBallClass_eq_localFrame u n r hr d (kmswDiskRootDart_missing c k)]
  apply Quotient.sound
  refine ⟨framedBallIso_of_orderedFrame B C (Equiv.refl _) (fun _ => rfl)
    (fun _ => rfl) (fun _ => Iff.rfl) (fun _ => Iff.rfl) rfl rfl hC.1
    (kmswDiskStageFramedBall_root_spec c k r hr).2.2.1 hC.2.1 ?_ hC.2.2⟩
  rw [← diskStageFramedBall_outer_frame c k r hr]
  exact Equiv.Perm.SameCycle.rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Finite stage-data classes depend only on the stage's consumed letters. -/
theorem framedStageDataClass_eq_prefix (u v : ℕ → Fin 3) (m r e : ℕ)
    (b : Bool) (h : ∀ i < m, u i = v i) :
    uibhbotStageDataBallClassRel ⟨kmswStage u m, kmswStageDirectedMap u m⟩ r e b =
      uibhbotStageDataBallClassRel ⟨kmswStage v m, kmswStageDirectedMap v m⟩ r e b := by
  have hu : shiftedStream (fun t => u t.toNat) 0 = u := by
    funext i
    simp only [shiftedStream, Nat.cast_zero, sub_zero, Int.toNat_natCast]
  have hv : shiftedStream (fun t => v t.toNat) 0 = v := by
    funext i
    simp only [shiftedStream, Nat.cast_zero, sub_zero, Int.toNat_natCast]
  have hc := uibhbotStageDataBallClassRel_eq_of_window (fun t => u t.toNat)
    (fun t => v t.toNat) 0 m r e b (by
      intro i hi
      simpa only [Nat.cast_zero, sub_zero, Int.toNat_natCast] using h i hi)
  rw [hu, hv] at hc
  exact hc

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The actual bridge support identifies its disk class with the bridge stage,
rooted at the record edge created at the sampled level's first hit. -/
theorem diskBSBallClass_decoder_eq_bridgeStageData
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (r : ℕ) (hr : 0 < r) (p : (ℕ → Fin 3) × ℕ)
    (hp : p.1 ∈ coneEvent (ell : ℤ) 0 n)
    (hlo : 1 ≤ p.2) (hhi : p.2 ≤ ell) :
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    diskBSBallClass n ell hell r hr (diskBridgeDecoder ell n hell hle hmod p) =
      uibhbotStageDataBallClassRel ⟨kmswStage w n, kmswStageDirectedMap w n⟩ r
        (kmswLLCreatedEdge w T) true := by
  let c : KMSWLeftWalkClass (ell + 1) n :=
    ⟨diskBridgePrefix n p, diskBridgePrefix_admissible_of_cone ell n p hp⟩
  let k : Fin ell := ⟨p.2 - 1, by omega⟩
  let kc := Fin.cast (by omega : ell = (ell + 1) - 1) k
  let u := finiteCodeExtend (n := n + 1) c.val
  let w := fun i => p.1 (i + 1)
  have hcode : ∀ i < n, u i = w i := by
    intro i hi
    simp only [u, finiteCodeExtend, Nat.add_sub_cancel, dite_eq_left hi]
    exact diskBridgePrefix_apply n p ⟨i, hi⟩
  have hT := kmswDiskFirstHit_eq_codeFstFirstHit_toNat ell n p c
    (fun i => diskBridgePrefix_apply n p i) k (by dsimp [k]; omega)
  have hTn : kmswDiskFirstHit c kc ≤ n := (kmswDiskFirstHit_spec c kc).2.1
  have hedge : kmswLLCreatedEdge u (kmswDiskFirstHit c kc) =
      kmswLLCreatedEdge w (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat := by
    unfold kmswLLCreatedEdge
    rw [kmswStage_congr (fun i hi => hcode i (hi.trans_le hTn))]
    rw [hT]
  rw [diskBSBallClass_decoder_eq_prefix_stage n ell hell hle hmod r hr p hp hlo hhi]
  change Quotient.mk FramedBall.setoid (kmswDiskStageFramedBall c kc r hr) = _
  rw [diskStageFramedBall_class_eq_stageData c kc r hr, hedge]
  exact framedStageDataClass_eq_prefix u w n r _ true hcode

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Positive-radius capture excludes the zero-length window. -/
theorem framedCapture_window_pos {N r K0 : ℕ} {u : ℕ → Fin 3}
    (hev : kmswWindowCaptureEventK N r K0 u) : 0 < N := by
  have hc := kmswStageBallVertices_center (fun _ _ => True)
    (kmswStage u (2 * N)) r (activeInitial u N) hev.1.1.1
  have htwo := (hev.1.1.2.1 _ hc).1
  by_contra hn
  have hzero : N = 0 := by omega
  subst N
  simp [CutConverse.activeInitial_eq, kmswStage, kmswInit] at htwo

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
On actual bridge support the decoded central time is a strict horizontal
record. The cone starts at `ell`, independently of the sampled level `p.2`. -/
theorem decodedWindow_central_record {ell n N : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (hp : p.1 ∈ coneEvent (ell : ℤ) 0 n)
    (hlo : 1 ≤ p.2) (hhi : p.2 ≤ ell)
    (h : bridgeOptionWindow n N p = some x) :
    ∀ j < N, L (windowCodeDecode N x) N < L (windowCodeDecode N x) j := by
  let c : KMSWLeftWalkClass (ell + 1) n :=
    ⟨diskBridgePrefix n p, diskBridgePrefix_admissible_of_cone ell n p hp⟩
  let k : Fin ell := ⟨p.2 - 1, by omega⟩
  let kc := Fin.cast (by omega : ell = (ell + 1) - 1) k
  let v := finiteCodeExtend (n := n + 1) c.val
  let u := windowCodeDecode N x
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  have hT := kmswDiskFirstHit_eq_codeFstFirstHit_toNat ell n p c
    (fun i => diskBridgePrefix_apply n p i) k (by dsimp [k]; omega)
  have hvalid : N ≤ T ∧ T + N ≤ n := by
    unfold bridgeOptionWindow at h
    split at h
    · exact ⟨‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2⟩
    · contradiction
  have hsN : s + N = T := by dsimp [s]; omega
  have hcode (i : ℕ) (hi : i < 2 * N) : v (s + i) = u i := by
    have hin : s + i < n := by dsimp [s]; omega
    change (if ht : s + i < n + 1 - 1 then c.val ⟨s + i, ht⟩ else 0) = _
    rw [dite_eq_left (by omega : s + i < n + 1 - 1)]
    change diskBridgePrefix n p ⟨s + i, hin⟩ = u i
    rw [diskBridgePrefix_apply]
    exact (windowCodeDecode_bridge h i hi).symm
  have hshift (j : ℕ) (hj : j ≤ 2 * N) : L v (s + j) = L v s + L u j := by
    induction j with
    | zero => simp only [L, Finset.range_zero, Finset.sum_empty, add_zero]
    | succ j ih =>
      have hg : L v (s + j + 1) = L v (s + j) +
          (lazyTwoDimensionalStep (v (s + j))).1 := Finset.sum_range_succ _ _
      have hu : L u (j + 1) = L u j +
          (lazyTwoDimensionalStep (u j)).1 := Finset.sum_range_succ _ _
      rw [Nat.add_succ, hg, hu, ih (by omega), hcode j (by omega), add_assoc]
  have hs := kmswDiskFirstHit_spec c kc
  have hrecord : ∀ j < T, L v T < L v j := by
    change kmswDiskFirstHit c kc = T at hT
    rw [← hT]
    intro j hj
    rw [hs.2.2.2.1]
    exact hs.2.2.2.2.1 j hj
  intro j hj
  have hlt := hrecord (s + j) (by omega)
  rw [← hsN, hshift N (by omega), hshift j (by omega)] at hlt
  exact (add_lt_add_iff_left (L v s)).mp hlt

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A strict LL record supplies the allocated missing outer dart, with the -/
theorem framedRootData_of_record (u : ℕ → Fin 3) (N m : ℕ)
    (hN : 0 < N) (hNm : N ≤ m) (hrec : ∀ j < N, L u N < L u j) :
    ∃ d : StageDart (kmswStage u m).nextEdge,
      d.1.val = kmswLLCreatedEdge u N ∧ d.2 = true ∧
      (kmswStageDirectedMap u m).missing d ∧
      (kmswStageDirectedMap u m).IsOuter d ∧
      stageEndpoint (kmswStage u m) (edgeFlip _ d) = activeInitial u N := by
  classical
  have hLL : kmswLLCreatedEdge u N ∈ (kmswStage u m).LL := by
    rw [kmswStage_LL_eq]
    apply List.mem_map.mpr
    refine ⟨N, List.mem_reverse.mpr ?_, rfl⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (by omega), of_decide_eq_true (by simpa using
      (show 0 < N ∧ ∀ j < N, L u N < L u j from ⟨hN, hrec⟩))⟩
  have he : kmswLLCreatedEdge u N < (kmswStage u m).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge u m).2 _ (by
      simp only [List.mem_append]
      exact Or.inl (Or.inr hLL))
  let d : StageDart (kmswStage u m).nextEdge := (⟨kmswLLCreatedEdge u N, he⟩, true)
  have htag := (kmswStageDirectedMap_LL_east u m d.1).mpr hLL
  refine ⟨d, rfl, rfl, htag.1, htag.2, ?_⟩
  have hNbound : kmswLLCreatedEdge u N < (kmswStage u N).nextEdge := by
    have hactive := (kmswStage_boundary_ids_lt_nextEdge u N).1
    unfold kmswLLCreatedEdge
    omega
  have hstable := (kmswStage_endpoints_stable u hNm hNbound).1
  change (kmswStage u m).west (kmswLLCreatedEdge u N) = _
  rw [hstable, kmswLLCreatedEdge_west_eq_act u hN hrec, CutConverse.activeInitial_eq]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The LL-created edge of the shifted window maps to the sampled disk frame edge. -/
theorem diskFrame_createdEdge_window_map {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (s : ℕ)
    (hs : s < kmswDiskFirstHit c k) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let T := kmswDiskFirstHit c k
    let m := n - s
    let v := fun i => u (s + i)
    (kmswWindowPatchData u s m).φ (kmswLLCreatedEdge v (T - s)) =
      kmswLLCreatedEdge u T := by
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let T := kmswDiskFirstHit c k
  let m := n - s
  let v := fun i => u (s + i)
  have hspec := kmswDiskFirstHit_spec c k
  dsimp only [u, T] at hspec
  have hTn : T ≤ n := hspec.2.1
  have hτpos : 0 < T - s := by omega
  have hτle : T - s ≤ m := by omega
  let j := T - s - 1
  have hsj : s + j = T - 1 := by dsimp [j]; omega
  obtain ⟨j₀, hj₀T, _, hj₀code, hj₀drop, hj₀tr, _, _, _⟩ :=
    kmswDiskFirstHit_triangle c k
  have hrootId : kmswLLCreatedEdge u T =
      (kmswStage u (T - 1)).nextEdge + 1 := by
    have hfresh := stageTriangleDartTriple_left_fresh u j₀ hj₀code
      (by rw [hj₀drop]; rfl)
    rw [hfresh] at hj₀tr
    have hthird := congrArg (fun t => t.2.2.1) hj₀tr
    change (kmswStage u j₀.val).nextEdge + 1 = kmswLLCreatedEdge u T at hthird
    have hthird' : (kmswStage u (T - 1)).nextEdge + 1 =
        kmswLLCreatedEdge u T := by
      simpa only [hj₀T] using hthird
    exact hthird'.symm
  have hdropGlobal : (kmswStage u (s + j)).UL.dropLast = [] := by
    rw [hsj]
    simpa [hj₀T] using hj₀drop
  have hcode : v j = 0 := by
    dsimp [v, j]
    rw [hsj]
    simpa [hj₀T] using hj₀code
  let pre := kmswStage v j
  let globalPre := kmswStage u (s + j)
  let data := kmswWindowPatchData u s j
  have hrel := kmswWindowPatchData_rel u s j
  change KMSWWindowPatchRel (kmswStage u s) globalPre pre data.φ
    data.A data.B data.YL data.YR data.XL data.XR at hrel
  have hglobalULne : globalPre.UL ≠ [] := by
    exact (kmswStage_UL_nonempty_active_last u (s + j)).1
  have hpreULne : pre.UL ≠ [] := by
    exact (kmswStage_UL_nonempty_active_last v j).1
  have hglobalULlen : globalPre.UL.length = 1 := by
    have hdropGlobal' : globalPre.UL.dropLast = [] := by
      simpa only [globalPre] using hdropGlobal
    have hlen := congrArg List.length hdropGlobal'
    simp only [List.length_dropLast, List.length_nil] at hlen
    have hpos := List.length_pos_of_ne_nil hglobalULne
    omega
  have hA : data.A = [] := by
    apply List.length_eq_zero_iff.mp
    have hlen := congrArg List.length hrel.ul
    simp only [List.length_append, List.length_map] at hlen
    rw [hglobalULlen] at hlen
    have hprepos := List.length_pos_of_ne_nil hpreULne
    omega
  have hpreULlen : pre.UL.length = 1 := by
    have hlen : globalPre.UL.length = data.A.length + pre.UL.length := by
      simpa only [List.length_append, List.length_map] using
        congrArg List.length hrel.ul
    rw [hglobalULlen, hA] at hlen
    simpa only [List.length_nil, Nat.zero_add] using hlen.symm
  have hdropPre : pre.UL.dropLast = [] := by
    apply List.length_eq_zero_iff.mp
    rw [List.length_dropLast, hpreULlen]
  have hcode' : u (s + j) = 0 := by simpa [v] using hcode
  have hdropRev : pre.UL.dropLast.reverse = [] := by
    rw [hdropPre]
    rfl
  have hrootLocal : kmswLLCreatedEdge v (j + 1) = pre.nextEdge + 1 := by
    have hnext : (kmswStage v (j + 1)).nextEdge = pre.nextEdge + 2 := by
      change (kmswStep (kmswStage v j) (v j)).nextEdge = pre.nextEdge + 2
      rw [hcode]
      simp [kmswStep, kmswStepOfStep, kmswCodeStep, hdropRev,
        State.addEdge, pre]
    change (kmswStage v (j + 1)).nextEdge - 1 = pre.nextEdge + 1
    rw [hnext]
    omega
  have hmapFresh :
      (kmswWindowPatchData u s (j + 1)).φ (pre.nextEdge + 1) =
        globalPre.nextEdge + 1 := by
    have hARev : data.A.reverse = [] := by rw [hA]; rfl
    have hfresh : kmswCodeStep (u (s + j)) = Step.left := by
      simp [kmswCodeStep, hcode']
    change (KMSWWindowPatchData.step globalPre pre
      (kmswCodeStep (u (s + j))) data).φ (pre.nextEdge + 1) =
        globalPre.nextEdge + 1
    rw [hfresh]
    simp [KMSWWindowPatchData.step, hdropRev, hARev]
  have hlocalBound : kmswLLCreatedEdge v (j + 1) <
      (kmswStage v (j + 1)).nextEdge := by
    rw [hrootLocal]
    have hnext : (kmswStage v (j + 1)).nextEdge = pre.nextEdge + 2 := by
      change (kmswStep (kmswStage v j) (v j)).nextEdge = pre.nextEdge + 2
      rw [hcode]
      simp [kmswStep, kmswStepOfStep, kmswCodeStep, hdropRev,
        State.addEdge, pre]
    rw [hnext]
    omega
  have hmapStable := kmswWindowPatchData_extends_le u s (j + 1) m
    (by dsimp [j, m]; omega) (kmswLLCreatedEdge v (j + 1)) hlocalBound
  calc
    (kmswWindowPatchData u s m).φ (kmswLLCreatedEdge v (T - s)) =
        (kmswWindowPatchData u s (j + 1)).φ (kmswLLCreatedEdge v (j + 1)) := by
          have hτ : T - s = j + 1 := by dsimp [j]; omega
          rw [hτ]
          exact hmapStable
    _ = globalPre.nextEdge + 1 := by rw [hrootLocal]; exact hmapFresh
    _ = kmswLLCreatedEdge u T := by
      change (kmswStage u (s + j)).nextEdge + 1 =
        kmswLLCreatedEdge u T
      rw [hsj]
      exact hrootId.symm


/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A positive-radius local framed ball at an allocated missing dart. -/
@[expose] noncomputable def framedStageBallAtMissingDart (u : ℕ → Fin 3) (m r : ℕ)
    (hr : 0 < r) (d : StageDart (kmswStage u m).nextEdge)
    (hm : (kmswStageDirectedMap u m).missing d) : FramedBall :=
  uibhbotInducedLocalFramedBallRel (kmswStageDirectedMap u m)
    (kmswStageBallDarts (fun _ _ => True) (kmswStage u m) r
      (stageEndpoint (kmswStage u m) (edgeFlip _ d)))
    (fun e he => (kmswStageBallDarts_edgeFlip (fun _ _ => True)
      (kmswStage u m) r (stageEndpoint (kmswStage u m) (edgeFlip _ d)) e).mp he)
    (kmswMap_isPlanar u m)
    (kmswStageBallCombinatorialMap_rooted_isConnected u m r d hr)
    ⟨d, (kmswStageBallRootEdge_mem u m r d hr).1⟩ hm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The decoded LL-created edge maps to the sampled disk edge already in the
captured window, rather than only in the full remaining suffix. -/
theorem diskFrame_decoded_createdEdge_map {ell n N r K0 : ℕ}
    (p : (ℕ → Fin 3) × ℕ) (c : KMSWLeftWalkClass (ell + 1) n)
    (hc : ∀ i : Fin n, c.val i = p.1 (i.val + 1))
    (k : Fin ell) (hk : k.val + 1 = p.2)
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x)) :
    let v := finiteCodeExtend (n := n + 1) c.val
    let kc := Fin.cast (by omega : ell = (ell + 1) - 1) k
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    (kmswWindowPatchData v (T - N) (2 * N)).φ
        (kmswLLCreatedEdge (windowCodeDecode N x) N) =
      kmswLLCreatedEdge v (kmswDiskFirstHit c kc) := by
  dsimp only
  let v := finiteCodeExtend (n := n + 1) c.val
  let kc := Fin.cast (by omega : ell = (ell + 1) - 1) k
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  let localCode := fun i => v (s + i)
  have hT := kmswDiskFirstHit_eq_codeFstFirstHit_toNat ell n p c hc k hk
  change kmswDiskFirstHit c kc = T at hT
  have hN := framedCapture_window_pos hev
  have hvalid : N ≤ T ∧ T + N ≤ n := by
    unfold bridgeOptionWindow at h
    split at h
    · exact ⟨‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2⟩
    · contradiction
  have hcode (i : ℕ) (hi : i < 2 * N) : localCode i = windowCodeDecode N x i := by
    have hin : s + i < n := by dsimp [s]; omega
    change (if ht : s + i < n + 1 - 1 then c.val ⟨s + i, ht⟩ else 0) = _
    rw [dite_eq_left (by omega : s + i < n + 1 - 1)]
    rw [hc ⟨s + i, hin⟩]
    exact (windowCodeDecode_bridge h i hi).symm
  have hlocal : kmswLLCreatedEdge localCode N =
      kmswLLCreatedEdge (windowCodeDecode N x) N := by
    unfold kmswLLCreatedEdge
    rw [kmswStage_congr (fun i hi => hcode i (by omega))]
  have hbound : kmswLLCreatedEdge localCode N <
      (kmswStage localCode (2 * N)).nextEdge := by
    have hactive := (kmswStage_boundary_ids_lt_nextEdge localCode N).1
    have hm := kmswStage_nextEdge_mono localCode (show N ≤ 2 * N by omega)
    unfold kmswLLCreatedEdge
    omega
  have hext := kmswWindowPatchData_extends_le v s (2 * N) (n - s)
    (by dsimp [s]; omega) (kmswLLCreatedEdge localCode N) hbound
  have hfull := diskFrame_createdEdge_window_map c kc s (by rw [hT]; dsimp [s]; omega)
  dsimp only at hfull
  have htime : kmswDiskFirstHit c kc - s = N := by rw [hT]; dsimp [s]; omega
  rw [htime] at hfull
  rw [← hlocal]
  exact hext.symm.trans hfull

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
OPEN obligation: compose the captured dart equivalences preserving rotation,
edge reversal and tags, with their known patch edge IDs and ordered sides.
Root and outer-face correspondence are consequences, not fields of this -/
@[expose] def DiskWindowFramedDartTransport : Prop :=
  ∀ (n ell N K0 r : ℕ) (hr : 0 < r) (p : (ℕ → Fin 3) × ℕ)
    (c : KMSWLeftWalkClass (ell + 1) n)
    (hc : ∀ i : Fin n, c.val i = p.1 (i.val + 1))
    (k : Fin ell) (hk : k.val + 1 = p.2)
    (x : Fin (2 * N + 1) → ℤ × ℤ),
    bridgeOptionWindow n N p = some x →
    kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) →
    ¬ DiskDip N K0 p →
    ∀ (d : StageDart (kmswStage (windowCodeDecode N x) (2 * N)).nextEdge),
    d.1.val = kmswLLCreatedEdge (windowCodeDecode N x) N → d.2 = true →
    ∀ (hm : (kmswStageDirectedMap (windowCodeDecode N x) (2 * N)).missing d),
    let B := kmswDiskStageFramedBall c
      (Fin.cast (by omega : ell = (ell + 1) - 1) k) r hr
    let C := framedStageBallAtMissingDart (windowCodeDecode N x) (2 * N) r hr d hm
    let v := finiteCodeExtend (n := n + 1) c.val
    let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
    ∃ e : C.D ≃ B.D,
      (∀ z, (e z).1.1.val = (kmswWindowPatchData v s (2 * N)).φ z.1.1.val) ∧
      (∀ z, (e z).1.2 = z.1.2) ∧
      (∀ z, e (C.map.rot z) = B.map.rot (e z)) ∧
      (∀ z, e (C.map.edgeInv z) = B.map.edgeInv (e z)) ∧
      (∀ z, B.map.missing (e z) ↔ C.map.missing z) ∧
      (∀ z, B.map.tail (e z) ↔ C.map.tail z)

/- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
CONDITIONAL on the single open dart transport obligation. Ordered roots, -/
theorem diskWindowClass_eq_of_framedDartTransport
    (htransport : DiskWindowFramedDartTransport)
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (N K0 r : ℕ) (hr : 0 < r) (p : (ℕ → Fin 3) × ℕ)
    (hp : p.1 ∈ coneEvent (ell : ℤ) 0 n)
    (hlo : 1 ≤ p.2) (hhi : p.2 ≤ ell)
    (x : Fin (2 * N + 1) → ℤ × ℤ)
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    diskBSBallClass n ell hell r hr (diskBridgeDecoder ell n hell hle hmod p) =
      uibhbotDecodedWindowBallClass N r x := by
  let c : KMSWLeftWalkClass (ell + 1) n :=
    ⟨diskBridgePrefix n p, diskBridgePrefix_admissible_of_cone ell n p hp⟩
  let k : Fin ell := ⟨p.2 - 1, by omega⟩
  let kc := Fin.cast (by omega : ell = (ell + 1) - 1) k
  let u := windowCodeDecode N x
  have hc : ∀ i : Fin n, c.val i = p.1 (i.val + 1) := diskBridgePrefix_apply n p
  have hk : k.val + 1 = p.2 := by dsimp [k]; omega
  have hrec := decodedWindow_central_record hp hlo hhi h
  obtain ⟨d, hde, hdb, hdm, hdo, _⟩ := framedRootData_of_record u N (2 * N)
    (framedCapture_window_pos hev) (by omega) hrec
  let B := kmswDiskStageFramedBall c kc r hr
  let C := framedStageBallAtMissingDart u (2 * N) r hr d hdm
  obtain ⟨e, heId, heSide, hrot, hflip, hmissing, htail⟩ :=
    htransport n ell N K0 r hr p c hc k hk x h hev hnd d hde hdb hdm
  have hC : C.rootDart = C.frameEdgeDart ∧
      C.frameOtherDart = some (C.map.edgeInv C.frameEdgeDart) ∧
      C.map.IsOuter (C.map.edgeInv C.frameEdgeDart) := by
    exact inducedLocalFramedBall_orderedFrame _ _ _ _ _ _ hdm hdo
  have hframe : e C.frameEdgeDart = B.frameEdgeDart := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      calc
        (e C.frameEdgeDart).1.1.val =
            (kmswWindowPatchData (finiteCodeExtend (n := n + 1) c.val)
              ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N)).φ
                C.frameEdgeDart.1.1.val := heId _
        _ = kmswLLCreatedEdge (finiteCodeExtend (n := n + 1) c.val)
            (kmswDiskFirstHit c kc) := by
          change (kmswWindowPatchData (finiteCodeExtend (n := n + 1) c.val)
            ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N) (2 * N)).φ d.1.val = _
          rw [hde]
          exact diskFrame_decoded_createdEdge_map p c hc k hk h hev
        _ = B.frameEdgeDart.1.1.val := rfl
    · rw [heSide]
      change Bool.not d.2 = Bool.not true
      exact congrArg Bool.not hdb
  have hBouter : B.map.IsOuter (B.map.edgeInv B.frameEdgeDart) := by
    rw [← diskStageFramedBall_outer_frame c kc r hr]
    exact Equiv.Perm.SameCycle.rfl
  let I := framedBallIso_of_orderedFrame C B e hrot hflip hmissing htail hframe
    hC.1 rfl hC.2.1 (kmswDiskStageFramedBall_root_spec c kc r hr).2.2.1
    hC.2.2 hBouter
  rw [diskBSBallClass_decoder_eq_prefix_stage n ell hell hle hmod r hr p hp hlo hhi]
  change Quotient.mk FramedBall.setoid B =
    uibhbotStageDataBallClassRel
      ⟨kmswStage u (2 * N), kmswStageDirectedMap u (2 * N)⟩ r
      (kmswLLCreatedEdge u N) true
  rw [← hde, ← hdb, stageDataBallClass_eq_localFrame u (2 * N) r hr d hdm]
  exact Quotient.sound ⟨I.symm⟩

private theorem framedBridge_ae_support (ell n : ℕ) :
    ∀ᵐ p ∂bridgeLevelLaw n ell,
      p.1 ∈ coneEvent (ell : ℤ) 0 n ∧ 1 ≤ p.2 ∧ p.2 ≤ ell := by
  have hmeas : MeasurableSet (coneEvent (ell : ℤ) 0 n) := by
    simp only [coneEvent, Set.ofPred_and]
    apply MeasurableSet.inter
    · simp only [Set.ofPred_forall]
      refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
      have hj := (measurable_pi_apply j).comp measurable_codeWalk
      simp only [Set.ofPred_and]
      exact (measurableSet_le measurable_const (measurable_const.add hj.fst)).inter
        (measurableSet_le measurable_const (measurable_const.add hj.snd))
    · exact (measurable_const.add ((measurable_pi_apply n).comp measurable_codeWalk))
        (measurableSet_singleton (0, 0))
  have hc : (cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n))
      (coneEvent (ell : ℤ) 0 n)ᶜ = 0 := by
    rw [ProbabilityTheory.cond_apply hmeas]
    simp
  have hk : Measure.uniformOfFinset (Finset.Icc 1 ell)
      (Finset.Icc 1 ell : Set ℕ)ᶜ = 0 := by
    rw [Measure.uniformOfFinset_apply]
    simp
  have hs := Measure.measure_prod_compl_eq_zero hc hk
  apply (ae_iff.mpr hs).mono
  intro p hp
  have hp' : p ∈ coneEvent (ell : ℤ) 0 n ×ˢ (Finset.Icc 1 ell : Set ℕ) := by
    simpa only [not_not] using hp
  exact ⟨hp'.1, Finset.mem_Icc.mp hp'.2⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
CONDITIONAL reduction of the exact assembly field to the single open dart -/
theorem diskWindowClassComparison_of_framedDartTransport
    (htransport : DiskWindowFramedDartTransport) : DiskWindowClassComparison := by
  apply diskWindowClassComparison_of_class_eq
  intro n ell hell hle hmod N K0 r hr
  filter_upwards [framedBridge_ae_support ell n] with p hp
  intro x h hev hnd
  exact diskWindowClass_eq_of_framedDartTransport htransport n ell hell hle hmod
    N K0 r hr p hp.1 hp.2.1 hp.2.2 x h hev hnd

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
CONDITIONAL exact decoder-stage residual, almost surely under the bridge law.
The only open premise is the dart transport obligation defined above. -/
theorem diskWindowFramedClass_ae_of_framedDartTransport
    (htransport : DiskWindowFramedDartTransport)
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (N K0 r : ℕ) (hr : 0 < r) :
    ∀ᵐ p ∂bridgeLevelLaw n ell, ∀ x,
      bridgeOptionWindow n N p = some x →
      kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) →
      ¬ DiskDip N K0 p →
      Quotient.mk FramedBall.setoid
        (kmswDiskStageFramedBall
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm
            (diskBridgeDecoderCore ell n (by omega) hle hmod
              (diskBridgePrefix n p, p.2)).1)
          (Fin.cast (by omega : ell = (ell + 1) - 1)
            (diskBridgeDecoderCore ell n (by omega) hle hmod
              (diskBridgePrefix n p, p.2)).2) r hr) =
        uibhbotStageDataBallClassRel
          ⟨kmswStage (windowCodeDecode N x) (2 * N),
            kmswStageDirectedMap (windowCodeDecode N x) (2 * N)⟩
          r (kmswLLCreatedEdge (windowCodeDecode N x) N) true := by
  have hclass := DiskWindowClassComparison.class_eq_on_capture
    (diskWindowClassComparison_of_framedDartTransport htransport)
    n ell hell hle hmod N K0 r hr
  filter_upwards [hclass] with p hp
  intro x h hev hnd
  have hpoint := hp x h hev hnd
  rw [diskBSBallClass_decoder_stage_repr, uibhbotDecodedWindowBallClass_stage_repr]
    at hpoint
  change (Quotient.mk FramedBall.setoid _ = _) at hpoint
  rw [diskBridgeDecoder_eq_core] at hpoint
  exact hpoint

end DirectedDistances.PaperProofs.Section5
