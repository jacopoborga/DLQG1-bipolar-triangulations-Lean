module

public import DirectedDistances.KMSW.KMSWStageBallDartsStage
public import DirectedDistances.KMSW.KMSWStageBallMap
public import DirectedDistances.KMSW.KMSWDiskRootFrameWindowOrder
public import DirectedDistances.PlanarMap.CyclicRestriction
public import DirectedDistances.PlanarMap.FramedBallIso
import DirectedDistances.PlanarMap.PlanarFaceCycleSpace

/-! Helpers toward Proposition 5.16 (`prop-disk-bs-conv`,
ball retains its ordered missing root edge at every positive radius. Connected
planar restrictions preserve ambient face incidences, yielding a framed ball
with the carrier, tags, orientations, vertices and original-face specifications -/

public section
namespace DirectedDistances.PlanarMap

open DirectedDistances.KMSW

variable {D : Type} [Fintype D] [DecidableEq D]

/-- Restrict a combinatorial map to an involution-closed finite dart set, using
first return for its rotation.
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] noncomputable def inducedCombinatorialMap
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S) :
    CombinatorialMap {d : D // d ∈ S} := by
  have hclosed : ∀ d, M.edgeInv d ∈ S ↔ d ∈ S := by
    intro d
    constructor
    · intro hd
      have h := hflip (M.edgeInv d) hd
      simpa [M.edgeInv_invol] using h
    · exact hflip d
  exact
    { edgeInv := M.edgeInv.subtypePerm hclosed
      edgeInv_invol := by
        intro d
        apply Subtype.ext
        change M.edgeInv (M.edgeInv d.1) = d.1
        exact M.edgeInv_invol d.1
      edgeInv_ne := by
        intro d hd
        apply M.edgeInv_ne d.1
        exact congrArg Subtype.val hd
      rot := cyclicFirstReturn M.rot S (finitePermutationReturn M.rot S) }

/-- The induced rotation is exactly first return of the ambient rotation.
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem inducedCombinatorialMap_rot
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S) :
    (inducedCombinatorialMap M S hflip).rot =
      cyclicFirstReturn M.rot S (finitePermutationReturn M.rot S) := rfl

private theorem firstReturn_next_of_mem
    (σ : Equiv.Perm D) (S : Finset D) (x : S) (hx : σ x.1 ∈ S) :
    (cyclicFirstReturn σ S (finitePermutationReturn σ S) x).1 = σ x.1 := by
  have ht : cyclicFirstReturnTime σ S (finitePermutationReturn σ S) x = 1 := by
    apply Nat.le_antisymm
    · exact Nat.find_min' (finitePermutationReturn σ S x)
        ⟨Nat.one_pos, by simpa only [pow_one] using hx⟩
    · exact (cyclicFirstReturnTime_spec σ S (finitePermutationReturn σ S) x).1
  rw [(firstReturn_spec σ S (finitePermutationReturn σ S) x).1, ht, pow_one]

/-- An ambient face step survives whenever its successor is retained. This
does not identify the induced face permutation with ambient face first return
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem inducedCombinatorialMap_faceSucc_of_mem
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (d : S) (hface : M.faceSucc d.1 ∈ S) :
    ((inducedCombinatorialMap M S hflip).faceSucc d).1 = M.faceSucc d.1 := by
  let N := inducedCombinatorialMap M S hflip
  let y : S := ⟨M.faceSucc d.1, hface⟩
  have hnext : M.rot y.1 = M.edgeInv d.1 := by
    exact M.rot.apply_symm_apply (M.edgeInv d.1)
  have hy : M.rot y.1 ∈ S := hnext.symm ▸ hflip d.1 d.2
  have hrot : N.rot y = N.edgeInv d := by
    apply Subtype.ext
    exact (firstReturn_next_of_mem M.rot S y hy).trans hnext
  change (N.rot.symm (N.edgeInv d)).1 = M.faceSucc d.1
  rw [← hrot, Equiv.symm_apply_apply]

/-- Every iterate of a completely retained ambient face keeps its incidence
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem inducedCombinatorialMap_face_pow_of_mem
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (d : S) (hface : ∀ j : ℕ, (M.faceSucc ^ j) d.1 ∈ S) (j : ℕ) :
    (((inducedCombinatorialMap M S hflip).faceSucc ^ j) d).1 =
      (M.faceSucc ^ j) d.1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have hmem : M.faceSucc
          (((inducedCombinatorialMap M S hflip).faceSucc ^ j) d).1 ∈ S := by
        rw [ih]
        simpa only [pow_succ', Equiv.Perm.mul_apply] using hface (j + 1)
      rw [inducedCombinatorialMap_faceSucc_of_mem M S hflip _ hmem, ih,
        pow_succ', Equiv.Perm.mul_apply]

/-- A completely retained ambient face is exactly one induced face, with no
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem inducedCombinatorialMap_face_sameCycle_iff
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (d : S) (hface : ∀ j : ℕ, (M.faceSucc ^ j) d.1 ∈ S) (e : S) :
    (inducedCombinatorialMap M S hflip).faceSucc.SameCycle d e ↔
      M.faceSucc.SameCycle d.1 e.1 := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := h.exists_nat_pow_eq
    refine ⟨(j : ℤ), ?_⟩
    simpa only [zpow_natCast] using
      (inducedCombinatorialMap_face_pow_of_mem M S hflip d hface j).symm.trans
        (congrArg Subtype.val hj)
  · intro h
    obtain ⟨j, hj⟩ := h.exists_nat_pow_eq
    refine ⟨(j : ℤ), ?_⟩
    rw [zpow_natCast]
    apply Subtype.ext
    exact (inducedCombinatorialMap_face_pow_of_mem M S hflip d hface j).trans hj

/-- A retained triangle keeps all three ordered face incidences and distinct
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem inducedCombinatorialMap_faceSucc3Cycle
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S) (a b c : S)
    (hcycle : FaceSucc3Cycle M.faceSucc a.1 b.1 c.1) :
    FaceSucc3Cycle (inducedCombinatorialMap M S hflip).faceSucc a b c := by
  rcases hcycle with ⟨hab, hbc, hca, hneab, hnebc, hneca⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    exact (inducedCombinatorialMap_faceSucc_of_mem M S hflip a
      (hab.symm ▸ b.2)).trans hab
  · apply Subtype.ext
    exact (inducedCombinatorialMap_faceSucc_of_mem M S hflip b
      (hbc.symm ▸ c.2)).trans hbc
  · apply Subtype.ext
    exact (inducedCombinatorialMap_faceSucc_of_mem M S hflip c
      (hca.symm ▸ a.2)).trans hca
  · exact fun h => hneab (congrArg Subtype.val h)
  · exact fun h => hnebc (congrArg Subtype.val h)
  · exact fun h => hneca (congrArg Subtype.val h)

/-- Restrict a directed map with missing edges to a finite involution-closed
dart set, assuming ambient outer-face darts retained by the set remain on one
restricted outer face.
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] noncomputable def inducedDirectedMapWithMissing
    (M : DirectedMapWithMissing D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (outer : {d : D // d ∈ S})
    (houter : ∀ d (hd : d ∈ S),
      CombinatorialMap.IsOuter M.toCombinatorialMap M.outer d →
        CombinatorialMap.IsOuter
          (inducedCombinatorialMap M.toCombinatorialMap S hflip)
          outer ⟨d, hd⟩) :
    DirectedMapWithMissing {d : D // d ∈ S} := by
  refine
    { toCombinatorialMap := inducedCombinatorialMap M.toCombinatorialMap S hflip
      missing := fun d => M.missing d.1
      missing_edgeInv := ?_
      tail := fun d => M.tail d.1
      tail_iff := ?_
      tail_missing := ?_
      outer := outer
      missing_outer := ?_ }
  · intro d
    exact M.missing_edgeInv d.1
  · intro d hd
    exact M.tail_iff d.1 hd
  · intro d hd ht
    exact M.tail_missing d.1 hd ht
  · intro d hd
    rcases M.missing_outer d.1 hd with ho | ho
    · exact Or.inl (houter d.1 d.2 ho)
    · exact Or.inr (houter (M.edgeInv d.1) (hflip d.1 d.2) ho)

/-- Make a framed ball carrier from an involution-closed finite dart set and a
retained missing root dart. The root, frame edge, and opposite incidence follow
the ordered endpoints of that dart.
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] noncomputable def inducedFramedBallOfMissingRoot
    (M : DirectedMapWithMissing D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (outer : {d : D // d ∈ S})
    (houter : ∀ d (hd : d ∈ S),
      CombinatorialMap.IsOuter M.toCombinatorialMap M.outer d →
        CombinatorialMap.IsOuter
          (inducedCombinatorialMap M.toCombinatorialMap S hflip)
          outer ⟨d, hd⟩)
    (root : {d : D // d ∈ S}) (hroot : M.missing root.1) : FramedBall := by
  let N := inducedDirectedMapWithMissing M S hflip outer houter
  exact
    { D := {d : D // d ∈ S}
      map := N
      rootDart := N.edgeInv root
      frameEdgeDart := N.edgeInv root
      frameEdge_missing := (N.missing_edgeInv root).mp hroot
      frameEdge_at_root := Equiv.Perm.SameCycle.rfl
      frameOtherDart := some root
      frameOtherDart_valid := by
        intro y hy
        simp only [Option.some.injEq] at hy
        subst y
        rw [N.edgeInv_invol]
        }

/-- The generic missing-root frame uses the root incidence and retains the
opposite dart as its other endpoint mark.
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem inducedFramedBallOfMissingRoot_frame_spec
    (M : DirectedMapWithMissing D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (outer : {d : D // d ∈ S})
    (houter : ∀ d (hd : d ∈ S),
      CombinatorialMap.IsOuter M.toCombinatorialMap M.outer d →
        CombinatorialMap.IsOuter
          (inducedCombinatorialMap M.toCombinatorialMap S hflip)
          outer ⟨d, hd⟩)
    (root : {d : D // d ∈ S}) (hroot : M.missing root.1) :
    let B := inducedFramedBallOfMissingRoot M S hflip outer houter root hroot
    B.rootDart = B.frameEdgeDart ∧ B.frameOtherDart = some root := by
  simp [inducedFramedBallOfMissingRoot]

/-- The generic frame retains its exact dart set, first-return rotation,
tags, orientations, outer mark, and both ordered root incidences
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem inducedFramedBallOfMissingRoot_data_spec
    (M : DirectedMapWithMissing D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (outer : {d : D // d ∈ S})
    (houter : ∀ d (hd : d ∈ S),
      CombinatorialMap.IsOuter M.toCombinatorialMap M.outer d →
        CombinatorialMap.IsOuter
          (inducedCombinatorialMap M.toCombinatorialMap S hflip)
          outer ⟨d, hd⟩)
    (root : {d : D // d ∈ S}) (hroot : M.missing root.1) :
    let B := inducedFramedBallOfMissingRoot M S hflip outer houter root hroot
    B.D = {d : D // d ∈ S} ∧
      B.map.rot = cyclicFirstReturn M.rot S (finitePermutationReturn M.rot S) ∧
      B.map.outer = outer ∧
      B.rootDart = (⟨M.edgeInv root.1, hflip root.1 root.2⟩ : S) ∧
      B.frameEdgeDart = B.rootDart ∧
      B.frameOtherDart = some root ∧
      B.map.edgeInv B.rootDart = root ∧
      (∀ x : S, B.map.missing x ↔ M.missing x.1) ∧
      (∀ x : S, B.map.tail x ↔ M.tail x.1) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · apply Subtype.ext
    exact M.edgeInv_invol root.1
  · exact fun _ => Iff.rfl
  · exact fun _ => Iff.rfl

/-- The opposite endpoint of every retained stage-ball dart is in the ball
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswStageBallDart_flip_endpoint_mem
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ)
    (d : KMSWStageBallDart P (kmswStage w n) r c) :
    stageEndpoint (kmswStage w n) (edgeFlip _ d.1) ∈
      kmswStageBallVertices P (kmswStage w n) r c := by
  exact (kmswStageBallDarts_mem_iff P (kmswStage w n) r c d.1).mp d.2 |>.2

/-- Both ordered incidences of a stage root edge are retained by every
positive-radius all-geometric ball centered at its first endpoint
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswStageBallRootEdge_mem
    (w : ℕ → Fin 3) (n r : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) (hr : 0 < r) :
    d ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage w n) r
        (stageEndpoint (kmswStage w n) (edgeFlip _ d)) ∧
      edgeFlip _ d ∈ kmswStageBallDarts (fun _ _ => True)
        (kmswStage w n) r (stageEndpoint (kmswStage w n) (edgeFlip _ d)) := by
  let s := kmswStage w n
  let c := stageEndpoint s (edgeFlip s.nextEdge d)
  have hzero : kmswStageDistanceLe (fun _ _ => True) s 0 c c :=
    ⟨0, Nat.zero_le _, .nil (Set.mem_univ _)⟩
  have hstep := kmswStageDistanceLe_otherEndpoint_succ
    (fun _ _ => True) w n 0 c d (by trivial)
  have hcenter : kmswStageDistanceLe (fun _ _ => True) s r c
      (stageEndpoint s (edgeFlip s.nextEdge d)) := by
    simpa [c] using kmswStageDistanceLe_mono (fun _ _ => True) s
      (show 0 ≤ r by omega) hzero
  have hother : kmswStageDistanceLe (fun _ _ => True) s r c
      (stageEndpoint s d) :=
    kmswStageDistanceLe_mono (fun _ _ => True) s (show 1 ≤ r by omega)
      (hstep.2 (by simpa [c] using hzero))
  have hd : d ∈ kmswStageBallDarts (fun _ _ => True) s r c :=
    (kmswStageBallDarts_mem_iff_distanceLe (fun _ _ => True) w n r c d).2
      ⟨hother, hcenter⟩
  have hflip : edgeFlip s.nextEdge d ∈ kmswStageBallDarts
      (fun _ _ => True) s r c :=
    (kmswStageBallDarts_edgeFlip (fun _ _ => True) s r c d).mp hd
  exact ⟨hd, hflip⟩

/-- The sampled KMSW disk root dart and its opposite incidence survive in the
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskRootDart_ball_mem {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let S := kmswStage u n
    let d := kmswDiskRootDart c k
    d ∈ kmswStageBallDarts (fun _ _ => True) S r
        (stageEndpoint S (edgeFlip _ d)) ∧
      edgeFlip _ d ∈ kmswStageBallDarts (fun _ _ => True) S r
        (stageEndpoint S (edgeFlip _ d)) := by
  dsimp only
  exact kmswStageBallRootEdge_mem
    (finiteCodeExtend (n := n + 1) c.val) n r (kmswDiskRootDart c k) hr

/-- The sampled disk root edge is missing in its finite KMSW stage
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskRootDart_missing {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n).missing
      (kmswDiskRootDart c k) := by
  let u := finiteCodeExtend (n := n + 1) c.val
  let T := kmswDiskFirstHit c k
  have hspec := kmswDiskFirstHit_spec c k
  dsimp only at hspec
  rcases hspec with ⟨hT, hTn, hL0, hLT, hbefore, hedge⟩
  have hrec : ∀ j < T, L u T < L u j := by
    intro j hj
    rw [hLT]
    exact hbefore j hj
  have hmissing := kmswLLCreatedEdge_missing u hT hrec
  have hbound : kmswLLCreatedEdge u T < (kmswStage u n).nextEdge :=
    stageRun_edge_bound u n _ (Or.inl (Or.inr (List.mem_reverse.mp
      (hedge ▸ List.get_mem _ _))))
  have hLL : kmswLLCreatedEdge u T ∈ (kmswStage u n).LL := by
    rw [← hedge]
    exact List.mem_reverse.mp (List.get_mem _ _)
  have hstatus := (kmswStage_status u n).1 _ hbound
  change (kmswStage u n).present (kmswDiskRootDart c k).1.val = false
  dsimp [kmswDiskRootDart]
  exact hstatus.mpr (Or.inr hLL)

/-- The retained sampled root dart marks the ambient stage outer face without
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskRootDart_ambient_isOuter {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) :
    (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n).IsOuter
      (kmswDiskRootDart c k) := by
  have hk := k.isLt
  exact DirectedDistances.KMSW.kmswDiskRootDart_isOuter (by omega) c k

/-- A retained stage face step keeps its ambient incidence
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswStageBallCombinatorialMap_faceSucc_of_mem
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ)
    (d : KMSWStageBallDart P (kmswStage w n) r c)
    (hface : (kmswMap w n).faceSucc d.1 ∈
      kmswStageBallDarts P (kmswStage w n) r c) :
    ((kmswStageBallCombinatorialMap P w n r c).faceSucc d).1 =
      (kmswMap w n).faceSucc d.1 := by
  let S := kmswStageBallDarts P (kmswStage w n) r c
  let N := kmswStageBallCombinatorialMap P w n r c
  let y : KMSWStageBallDart P (kmswStage w n) r c :=
    ⟨(kmswMap w n).faceSucc d.1, hface⟩
  have hnext : stageRot w n y.1 = edgeFlip _ d.1 := by
    exact (stageRot w n).apply_symm_apply (edgeFlip _ d.1)
  have hy : stageRot w n y.1 ∈ S := by
    rw [hnext]
    exact (kmswStageBallDarts_edgeFlip P (kmswStage w n) r c d.1).mp d.2
  have hrot : N.rot y = N.edgeInv d := by
    apply Subtype.ext
    exact (firstReturn_next_of_mem (stageRot w n) S y hy).trans hnext
  change (N.rot.symm (N.edgeInv d)).1 = (kmswMap w n).faceSucc d.1
  rw [← hrot, Equiv.symm_apply_apply]

private theorem kmswStage_faceSucc_endpoint
    (w : ℕ → Fin 3) (n : ℕ) (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) ((kmswMap w n).faceSucc d) =
      stageEndpoint (kmswStage w n) (edgeFlip _ d) := by
  apply (stageRot_sameCycle_iff_endpoint_eq w n _ _).mp
  refine ⟨1, ?_⟩
  rw [zpow_one]
  change (stageRot w n) ((stageRot w n).symm (edgeFlip _ d)) = edgeFlip _ d
  exact (stageRot w n).apply_symm_apply (edgeFlip _ d)

/-- Every original triangle whose three boundary vertices are retained keeps
its three distinct darts and ordered face incidences
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswStageBallCombinatorialMap_triangle_of_vertices
    (w : ℕ → Fin 3) (n r c : ℕ) (j : TriangleCreationTime w) (hj : j.val < n)
    (hv₁ : stageEndpoint (kmswStage w n) (stageTriangleDart₁ w n j hj) ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r c)
    (hv₂ : stageEndpoint (kmswStage w n) (stageTriangleDart₂ w n j hj) ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r c)
    (hv₃ : stageEndpoint (kmswStage w n) (stageTriangleDart₃ w n j hj) ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r c) :
    let S := kmswStageBallDarts (fun _ _ => True) (kmswStage w n) r c
    ∃ (h₁ : stageTriangleDart₁ w n j hj ∈ S)
      (h₂ : stageTriangleDart₂ w n j hj ∈ S)
      (h₃ : stageTriangleDart₃ w n j hj ∈ S),
      FaceSucc3Cycle
        (kmswStageBallCombinatorialMap (fun _ _ => True) w n r c).faceSucc
        ⟨stageTriangleDart₁ w n j hj, h₁⟩ ⟨stageTriangleDart₂ w n j hj, h₂⟩
        ⟨stageTriangleDart₃ w n j hj, h₃⟩ := by
  dsimp only
  obtain ⟨hab, hbc, hca, hneab, hnebc, hneca⟩ := stageTriangle_isFace w j n hj
  have h₁ : stageTriangleDart₁ w n j hj ∈
      kmswStageBallDarts (fun _ _ => True) (kmswStage w n) r c := by
    apply (kmswStageBallDarts_mem_iff _ _ _ _ _).mpr
    refine ⟨hv₁, ?_⟩
    rw [← kmswStage_faceSucc_endpoint w n, hab]
    exact hv₂
  have h₂ : stageTriangleDart₂ w n j hj ∈
      kmswStageBallDarts (fun _ _ => True) (kmswStage w n) r c := by
    apply (kmswStageBallDarts_mem_iff _ _ _ _ _).mpr
    refine ⟨hv₂, ?_⟩
    rw [← kmswStage_faceSucc_endpoint w n, hbc]
    exact hv₃
  have h₃ : stageTriangleDart₃ w n j hj ∈
      kmswStageBallDarts (fun _ _ => True) (kmswStage w n) r c := by
    apply (kmswStageBallDarts_mem_iff _ _ _ _ _).mpr
    refine ⟨hv₃, ?_⟩
    rw [← kmswStage_faceSucc_endpoint w n, hca]
    exact hv₁
  refine ⟨h₁, h₂, h₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    exact (kmswStageBallCombinatorialMap_faceSucc_of_mem _ w n r c
      ⟨_, h₁⟩ (hab.symm ▸ h₂)).trans hab
  · apply Subtype.ext
    exact (kmswStageBallCombinatorialMap_faceSucc_of_mem _ w n r c
      ⟨_, h₂⟩ (hbc.symm ▸ h₃)).trans hbc
  · apply Subtype.ext
    exact (kmswStageBallCombinatorialMap_faceSucc_of_mem _ w n r c
      ⟨_, h₃⟩ (hca.symm ▸ h₁)).trans hca
  · exact fun h => hneab (congrArg Subtype.val h)
  · exact fun h => hnebc (congrArg Subtype.val h)
  · exact fun h => hneca (congrArg Subtype.val h)

/-- The sampled missing root has both ordered incidences in the positive
vertices, and neither incidence is oriented
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskRootDart_ball_ordered {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let s := kmswStage u n
    let T := kmswDiskFirstHit c k
    let d := kmswDiskRootDart c k
    let B := kmswStageBallCombinatorialMap (fun _ _ => True) u n r
      (stageEndpoint s (edgeFlip _ d))
    ∃ x y : KMSWStageBallDart (fun _ _ => True) s r
        (stageEndpoint s (edgeFlip _ d)),
      B.edgeInv x = y ∧ x.1 = d ∧ y.1 = edgeFlip _ d ∧
      (stageEndpoint s y.1, stageEndpoint s x.1) =
        (activeInitial u T, activeInitial u (T - 1)) ∧
      (kmswStageDirectedMap u n).missing x.1 ∧
      (kmswStageDirectedMap u n).missing y.1 ∧
      ¬ (kmswStageDirectedMap u n).tail x.1 ∧
      ¬ (kmswStageDirectedMap u n).tail y.1 := by
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let d := kmswDiskRootDart c k
  have hm := kmswDiskRootDart_missing c k
  have hf := (kmswDiskRootDart_hit_frame_iff c k d).mpr rfl
  have hm' : (kmswStageDirectedMap u n).missing (edgeFlip _ d) :=
    ((kmswStageDirectedMap u n).missing_edgeInv d).mp hm
  refine ⟨⟨d, (kmswDiskRootDart_ball_mem c k r hr).1⟩,
    ⟨edgeFlip _ d, (kmswDiskRootDart_ball_mem c k r hr).2⟩,
    rfl, rfl, rfl, Prod.ext hf.2.1 hf.2.2, hm, hm', ?_, ?_⟩
  · exact (kmswStageDirectedMap u n).tail_missing d hm
  · exact (kmswStageDirectedMap u n).tail_missing (edgeFlip _ d) hm'

private def framedDartStep (M : CombinatorialMap D) (x y : D) : Prop :=
  y = M.rot x ∨ y = M.rot.symm x ∨
    y = M.edgeInv x ∨ y = M.edgeInv.symm x

private theorem framedDartStep_symm (M : CombinatorialMap D) {x y : D}
    (h : framedDartStep M x y) : framedDartStep M y x := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl (by rw [h, Equiv.symm_apply_apply]))
  · exact Or.inl (by rw [h, Equiv.apply_symm_apply])
  · exact Or.inr (Or.inr (Or.inr (by rw [h, Equiv.symm_apply_apply])))
  · exact Or.inr (Or.inr (Or.inl (by rw [h, Equiv.apply_symm_apply])))

private theorem framedDartPath_symm (M : CombinatorialMap D) {x y : D}
    (h : Relation.ReflTransGen (framedDartStep M) x y) :
    Relation.ReflTransGen (framedDartStep M) y x := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.head (framedDartStep_symm M hs)

private theorem framedRotationPath (M : CombinatorialMap D) {x y : D}
    (h : M.rot.SameCycle x y) :
    Relation.ReflTransGen (framedDartStep M) x y := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction k with
  | zero => exact .refl
  | succ k ih =>
      apply ih.tail
      exact Or.inl (by simp only [pow_succ', Equiv.Perm.mul_apply])

private theorem kmswStageBall_pathReach
    (w : ℕ → Fin 3) (n r c : ℕ)
    (x : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r c)
    (hx : stageEndpoint (kmswStage w n) x.1 = c)
    {k v : ℕ} (hp : KMSWStagePath (fun _ _ => True) (kmswStage w n) Set.univ c k v)
    (hk : k ≤ r)
    (y : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r c)
    (hy : stageEndpoint (kmswStage w n) y.1 = v) :
    Relation.ReflTransGen
      (framedDartStep (kmswStageBallCombinatorialMap (fun _ _ => True) w n r c))
      x y := by
  induction hp generalizing y with
  | nil _ =>
      apply framedRotationPath
      exact (kmswStageBallRot_sameCycle_iff_endpoint_eq _ w n r c x y).mpr
        (hx.trans hy.symm)
  | @snoc k v z hp hv hz hadj ih =>
      obtain ⟨d, hdP, hdv, hdz⟩ := hadj
      have hd : d ∈ kmswStageBallDarts (fun _ _ => True) (kmswStage w n) r c := by
        apply (kmswStageBallDarts_mem_iff_distanceLe _ w n r c d).mpr
        constructor
        · rw [hdv]
          exact ⟨k, by omega, hp⟩
        · rw [hdz]
          exact ⟨k + 1, hk, .snoc hp hv hz ⟨d, hdP, hdv, hdz⟩⟩
      let a : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r c := ⟨d, hd⟩
      let N := kmswStageBallCombinatorialMap (fun _ _ => True) w n r c
      have hxa : Relation.ReflTransGen (framedDartStep N) x a :=
        ih (by omega) a hdv
      have hflip : Relation.ReflTransGen (framedDartStep N) a (N.edgeInv a) :=
        .single (Or.inr (Or.inr (Or.inl rfl)))
      have hlast : Relation.ReflTransGen (framedDartStep N) (N.edgeInv a) y := by
        apply framedRotationPath
        apply (kmswStageBallRot_sameCycle_iff_endpoint_eq _ w n r c _ y).mpr
        exact hdz.trans hy.symm
      exact hxa.trans (hflip.trans hlast)

/-- A positive all-geometric ball centered at the first incidence of a retained
root edge is connected through its rotation and geometric edge involution
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswStageBallCombinatorialMap_rooted_isConnected
    (w : ℕ → Fin 3) (n r : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) (hr : 0 < r) :
    (kmswStageBallCombinatorialMap (fun _ _ => True) w n r
      (stageEndpoint (kmswStage w n) (edgeFlip _ d))).IsConnected := by
  let c := stageEndpoint (kmswStage w n) (edgeFlip _ d)
  let x₀ : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r c :=
    ⟨edgeFlip _ d, (kmswStageBallRootEdge_mem w n r d hr).2⟩
  intro x y
  obtain ⟨kx, hkx, hpx⟩ :=
    ((kmswStageBallDarts_mem_iff_distanceLe _ w n r c x.1).mp x.2).1
  obtain ⟨ky, hky, hpy⟩ :=
    ((kmswStageBallDarts_mem_iff_distanceLe _ w n r c y.1).mp y.2).1
  exact (framedDartPath_symm _
    (kmswStageBall_pathReach w n r c x₀ rfl hpx hkx x rfl)).trans
      (kmswStageBall_pathReach w n r c x₀ rfl hpy hky y rfl)

/-- Inducing a map preserves exactly the retained vertex incidences
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem inducedCombinatorialMap_rot_sameCycle_iff
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S) (x y : S) :
    (inducedCombinatorialMap M S hflip).rot.SameCycle x y ↔
      M.rot.SameCycle x.1 y.1 :=
  firstReturn_sameCycle_iff M.rot S (finitePermutationReturn M.rot S) x y

private noncomputable def inducedEdgeExtension
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (c : EdgeSpace (inducedCombinatorialMap M S hflip)) : EdgeSpace M := by
  classical
  let N := inducedCombinatorialMap M S hflip
  refine fun q => Quotient.lift
    (fun d => if hd : d ∈ S then c (edgeClass N ⟨d, hd⟩) else 0) ?_ q
  intro d e hde
  rcases (CombinatorialMap.edgeInv_sameCycle_iff M d e).mp hde with h | h
  · subst e
    rfl
  · subst e
    by_cases hd : d ∈ S
    · rw [dite_eq_left hd, dite_eq_left (hflip d hd)]
      apply congrArg c
      apply Quotient.sound
      exact (CombinatorialMap.edgeInv_sameCycle_iff N _ _).mpr (Or.inr rfl)
    · have hf : M.edgeInv d ∉ S := by
        intro h
        have hh := hflip (M.edgeInv d) h
        exact hd (by simpa only [M.edgeInv_invol] using hh)
      rw [dite_eq_right hd, dite_eq_right hf]

private theorem inducedEdgeExtension_apply
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (c : EdgeSpace (inducedCombinatorialMap M S hflip)) (d : D) :
    inducedEdgeExtension M S hflip c (edgeClass M d) =
      if hd : d ∈ S then
        c (edgeClass (inducedCombinatorialMap M S hflip) ⟨d, hd⟩) else 0 := by
  classical
  rfl

private theorem inducedEdgeExtension_cycle
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (c : EdgeSpace (inducedCombinatorialMap M S hflip))
    (hc : vertexBoundary (inducedCombinatorialMap M S hflip) c = 0) :
    vertexBoundary M (inducedEdgeExtension M S hflip c) = 0 := by
  classical
  let N := inducedCombinatorialMap M S hflip
  ext v
  change (∑ d : D, if vertexClass M d = v then
    inducedEdgeExtension M S hflip c (edgeClass M d) else 0) = 0
  simp_rw [inducedEdgeExtension_apply]
  have hsum : (∑ d : D, if vertexClass M d = v then
      (if hd : d ∈ S then c (edgeClass N ⟨d, hd⟩) else 0) else 0) =
      ∑ d : S, if vertexClass M d.1 = v then c (edgeClass N d) else 0 := by
    calc
      _ = ∑ d : D, if hd : d ∈ S then
          (if vertexClass M d = v then c (edgeClass N ⟨d, hd⟩) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : d ∈ S <;> by_cases hv : vertexClass M d = v <;> simp [hd, hv]
      _ = _ := by
        simpa only [Finset.univ_eq_attach] using
          (Finset.sum_attach_eq_sum_dite S (fun d : S =>
            if vertexClass M d.1 = v then c (edgeClass N d) else 0)).symm
  rw [hsum]
  by_cases hv : ∃ x : S, vertexClass M x.1 = v
  · obtain ⟨x, hx⟩ := hv
    have heq (d : S) : vertexClass M d.1 = v ↔ vertexClass N d = vertexClass N x := by
      rw [← hx]
      constructor
      · intro h
        apply Quotient.sound
        exact (inducedCombinatorialMap_rot_sameCycle_iff M S hflip d x).mpr
          (Quotient.exact h)
      · intro h
        apply Quotient.sound
        exact (inducedCombinatorialMap_rot_sameCycle_iff M S hflip d x).mp
          (Quotient.exact h)
    simp_rw [heq]
    exact congrFun hc (vertexClass N x)
  · apply Finset.sum_eq_zero
    intro d _
    exact ite_eq_right (fun hd => hv ⟨d, hd⟩)

private theorem faceCoeff_corner (M : CombinatorialMap D) (A : FaceSpace M) (d : D) :
    A (faceClass M (M.edgeInv (M.rot d))) = A (faceClass M d) := by
  apply congrArg A
  apply Quotient.sound
  change M.faceSucc.SameCycle (M.edgeInv (M.rot d)) d
  have h : M.faceSucc.SameCycle (M.edgeInv (M.rot d))
      (M.faceSucc (M.edgeInv (M.rot d))) :=
    Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl
  simpa [CombinatorialMap.faceSucc, M.edgeInv_invol] using h

private theorem faceCoeff_induced_rot
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S) (A : FaceSpace M)
    (hzero : ∀ d, d ∉ S → A (faceClass M d) = A (faceClass M (M.edgeInv d)))
    (z : S) :
    A (faceClass M z.1) =
      A (faceClass M (M.edgeInv ((inducedCombinatorialMap M S hflip).rot z).1)) := by
  let k := cyclicFirstReturnTime M.rot S (finitePermutationReturn M.rot S) z
  have hk := cyclicFirstReturnTime_spec M.rot S (finitePermutationReturn M.rot S) z
  have hskip : ∀ j : ℕ, j < k →
      A (faceClass M ((M.rot ^ j) z.1)) = A (faceClass M z.1) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hdel : (M.rot ^ (j + 1)) z.1 ∉ S := hk.2.2 (j + 1) (by omega) hj
      calc
        _ = A (faceClass M (M.edgeInv ((M.rot ^ (j + 1)) z.1))) := hzero _ hdel
        _ = A (faceClass M ((M.rot ^ j) z.1)) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact faceCoeff_corner M A _
        _ = A (faceClass M z.1) := ih (by omega)
  have hreturn : ((inducedCombinatorialMap M S hflip).rot z).1 =
      (M.rot ^ k) z.1 := (firstReturn_spec M.rot S
        (finitePermutationReturn M.rot S) z).1
  have hlast : k - 1 + 1 = k := by have := hk.1; omega
  calc
    _ = A (faceClass M ((M.rot ^ (k - 1)) z.1)) := (hskip _ (by omega)).symm
    _ = A (faceClass M (M.edgeInv (M.rot ((M.rot ^ (k - 1)) z.1)))) :=
      (faceCoeff_corner M A _).symm
    _ = _ := by
      have hp : M.rot ((M.rot ^ (k - 1)) z.1) = (M.rot ^ k) z.1 := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ', hlast]
      rw [hreturn, hp]

private theorem inducedFaceCoeff_constant
    (M : CombinatorialMap D) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hN : (inducedCombinatorialMap M S hflip).IsConnected)
    (T : FaceSpace (inducedCombinatorialMap M S hflip)) (A : FaceSpace M)
    (hA : faceBoundary M A = inducedEdgeExtension M S hflip
      (faceBoundary (inducedCombinatorialMap M S hflip) T)) (x y : S) :
    A (faceClass M x.1) + T (faceClass (inducedCombinatorialMap M S hflip) x) =
      A (faceClass M y.1) + T (faceClass (inducedCombinatorialMap M S hflip) y) := by
  classical
  let N := inducedCombinatorialMap M S hflip
  let f : S → ZMod 2 := fun d => A (faceClass M d.1) + T (faceClass N d)
  have hzero (d : D) (hd : d ∉ S) :
      A (faceClass M d) = A (faceClass M (M.edgeInv d)) := by
    have hz := congrFun hA (edgeClass M d)
    rw [faceBoundary_apply, inducedEdgeExtension_apply, dite_eq_right hd] at hz
    calc
      _ = A (faceClass M d) +
          (A (faceClass M (M.edgeInv d)) + A (faceClass M (M.edgeInv d))) := by
        rw [CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [← add_assoc, hz, zero_add]
  have hflipf (d : S) : f d = f (N.edgeInv d) := by
    have hz := congrFun hA (edgeClass M d.1)
    rw [faceBoundary_apply, inducedEdgeExtension_apply, dite_eq_left d.2,
      faceBoundary_apply] at hz
    change A (faceClass M d.1) + A (faceClass M (M.edgeInv d.1)) =
      T (faceClass N d) + T (faceClass N (N.edgeInv d)) at hz
    dsimp [f]
    have hz' : A (faceClass M d.1) + T (faceClass N d) +
        (A (faceClass M (M.edgeInv d.1)) + T (faceClass N (N.edgeInv d))) = 0 := by
      calc
        _ = (A (faceClass M d.1) + A (faceClass M (M.edgeInv d.1))) +
            (T (faceClass N d) + T (faceClass N (N.edgeInv d))) := by abel
        _ = _ := by rw [hz, CharTwo.add_self_eq_zero]
    have hcancel := congrArg
      (fun q => q + (A (faceClass M (M.edgeInv d.1)) +
        T (faceClass N (N.edgeInv d)))) hz'
    change A (faceClass M d.1) + T (faceClass N d) =
      A (faceClass M (M.edgeInv d.1)) + T (faceClass N (N.edgeInv d))
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using hcancel
  have hrotf (d : S) : f d = f (N.rot d) := by
    have hcornerN : T (faceClass N d) = T (faceClass N (N.edgeInv (N.rot d))) :=
      (faceCoeff_corner N T d).symm
    calc
      f d = f (N.edgeInv (N.rot d)) := by
        exact congrArg₂ (· + ·) (faceCoeff_induced_rot M S hflip A hzero d) hcornerN
      _ = f (N.rot d) := by
        simpa only [N.edgeInv_invol] using (hflipf (N.edgeInv (N.rot d)))
  have hinv (d : S) : N.edgeInv.symm d = N.edgeInv d := by
    apply N.edgeInv.injective
    rw [Equiv.apply_symm_apply, N.edgeInv_invol]
  have hstep (a b : S) (hs : b = N.rot a ∨ b = N.rot.symm a ∨
      b = N.edgeInv a ∨ b = N.edgeInv.symm a) : f a = f b := by
    rcases hs with hs | hs | hs | hs
    · rw [hs]; exact hrotf _
    · rw [hs]
      simpa only [Equiv.apply_symm_apply] using (hrotf (N.rot.symm a)).symm
    · rw [hs]; exact hflipf _
    · rw [hs, hinv]; exact hflipf _
  have hpath := hN x y
  change f x = f y
  induction hpath with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (hstep _ _ hs)

/-- In a connected restriction of a planar map, retained darts on any one
ambient face stay on a single induced face, even if that face leaves the
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem inducedCombinatorialMap_face_sameCycle_of_connected_planar
    (M : CombinatorialMap D) (hM : M.IsPlanar) (S : Finset D)
    (hflip : ∀ d, d ∈ S → M.edgeInv d ∈ S)
    (hN : (inducedCombinatorialMap M S hflip).IsConnected) (x y : S)
    (hxy : M.faceSucc.SameCycle x.1 y.1) :
    (inducedCombinatorialMap M S hflip).faceSucc.SameCycle x y := by
  classical
  let N := inducedCombinatorialMap M S hflip
  by_contra hne
  let T : FaceSpace N := fun q => if q = faceClass N x then 1 else 0
  obtain ⟨A, hA⟩ := planar_cycle_eq_faceBoundary M hM
    (inducedEdgeExtension M S hflip (faceBoundary N T))
    (inducedEdgeExtension_cycle M S hflip _ (vertexBoundary_faceBoundary N T))
  have hconst := inducedFaceCoeff_constant M S hflip hN T A hA x y
  have hambient : faceClass M x.1 = faceClass M y.1 := Quotient.sound hxy
  have hy : faceClass N y ≠ faceClass N x := by
    intro h
    exact hne (Quotient.exact h.symm)
  change A (faceClass M x.1) + T (faceClass N x) =
    A (faceClass M y.1) + T (faceClass N y) at hconst
  simp only [T, ite_eq_left rfl, ite_eq_right hy, hambient, add_zero] at hconst
  have hbad : (1 : ZMod 2) = 0 := add_left_cancel (hconst.trans (add_zero _).symm)
  exact one_ne_zero hbad

/-- Every retained ambient outer-face dart remains on the root-marked outer
face of the induced positive-radius disk ball
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskRootDart_ball_outer_survives {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let d := kmswDiskRootDart c k
    let S := kmswStageBallDarts (fun _ _ => True) (kmswStage u n) r
      (stageEndpoint (kmswStage u n) (edgeFlip _ d))
    ∀ e (he : e ∈ S), (kmswStageDirectedMap u n).IsOuter e →
      @CombinatorialMap.IsOuter _ _ Subtype.instDecidableEq
        (inducedCombinatorialMap (kmswStageDirectedMap u n).toCombinatorialMap S
        (fun e he => (kmswStageBallDarts_edgeFlip
          (fun _ _ => True) (kmswStage u n) r
          (stageEndpoint (kmswStage u n) (edgeFlip _ d)) e).mp he))
        ⟨d, (kmswDiskRootDart_ball_mem c k r hr).1⟩ ⟨e, he⟩ := by
  dsimp only
  intro e he ho
  apply inducedCombinatorialMap_face_sameCycle_of_connected_planar
  · exact kmswMap_isPlanar _ _
  · exact kmswStageBallCombinatorialMap_rooted_isConnected _ n r _ hr
  · exact (kmswDiskRootDart_ambient_isOuter c k).symm.trans ho

/-- The positive all-geometric ball at the ordered sampled missing root,
with inherited tags, orientation, rotation and the root-marked outer face
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[expose] noncomputable def kmswDiskStageFramedBall {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r) :
    FramedBall := by
  let u := finiteCodeExtend (n := n + 1) c.val
  let d := kmswDiskRootDart c k
  let S := kmswStageBallDarts (fun _ _ => True) (kmswStage u n) r
    (stageEndpoint (kmswStage u n) (edgeFlip _ d))
  let hf := fun e he => (kmswStageBallDarts_edgeFlip
    (fun _ _ => True) (kmswStage u n) r
    (stageEndpoint (kmswStage u n) (edgeFlip _ d)) e).mp he
  let root : S := ⟨d, (kmswDiskRootDart_ball_mem c k r hr).1⟩
  exact inducedFramedBallOfMissingRoot (kmswStageDirectedMap u n) S hf root
    (kmswDiskRootDart_ball_outer_survives c k r hr) root (kmswDiskRootDart_missing c k)

/-- The constructed ball has exactly the induced dart carrier, first-return
rotation, geometric edge involution, inherited tags and orientations, and
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskStageFramedBall_data_spec {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let s := kmswStage u n
    let d := kmswDiskRootDart c k
    let v := stageEndpoint s (edgeFlip _ d)
    let B := kmswDiskStageFramedBall c k r hr
    B.D = KMSWStageBallDart (fun _ _ => True) s r v ∧
      B.map.rot = kmswStageBallRot (fun _ _ => True) u n r v ∧
      B.map.edgeInv = kmswStageBallDartFlip (fun _ _ => True) s r v ∧
      B.map.outer.1 = d ∧
      B.rootDart.1 = edgeFlip _ d ∧ B.frameEdgeDart = B.rootDart ∧
      B.frameOtherDart = some ⟨d, (kmswDiskRootDart_ball_mem c k r hr).1⟩ ∧
      (∀ x : B.D, B.map.missing x ↔ (kmswStageDirectedMap u n).missing x.1) ∧
      (∀ x : B.D, B.map.tail x ↔ (kmswStageDirectedMap u n).tail x.1) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

/-- endpoint, with the missing edge unoriented on both incidences
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskStageFramedBall_root_spec {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let s := kmswStage u n
    let T := kmswDiskFirstHit c k
    let B := kmswDiskStageFramedBall c k r hr
    stageEndpoint s B.rootDart.1 = activeInitial u T ∧
      stageEndpoint s (B.map.edgeInv B.frameEdgeDart).1 = activeInitial u (T - 1) ∧
      B.frameOtherDart = some (B.map.edgeInv B.frameEdgeDart) ∧
      B.map.missing B.rootDart ∧ B.map.missing (B.map.edgeInv B.rootDart) ∧
      ¬ B.map.tail B.rootDart ∧ ¬ B.map.tail (B.map.edgeInv B.rootDart) := by
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let d := kmswDiskRootDart c k
  let B := kmswDiskStageFramedBall c k r hr
  have hf := (kmswDiskRootDart_hit_frame_iff c k d).mpr rfl
  have hflip : (B.map.edgeInv B.frameEdgeDart).1 = d := by
    exact (kmswStageDirectedMap u n).edgeInv_invol d
  have hmroot : B.map.missing B.rootDart :=
    ((kmswStageDirectedMap u n).missing_edgeInv d).mp (kmswDiskRootDart_missing c k)
  have hm : B.map.missing (B.map.edgeInv B.rootDart) :=
    (B.map.missing_edgeInv B.rootDart).mp hmroot
  refine ⟨hf.2.1, ?_, ?_, hmroot, hm, B.map.tail_missing _ hmroot,
    B.map.tail_missing _ hm⟩
  · rw [hflip]
    exact hf.2.2
  · apply congrArg some
    apply Subtype.ext
    exact hflip.symm

/-- The constructed framed ball is connected through its retained plane
rotation and geometric edge involution
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskStageFramedBall_isConnected {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r) :
    (kmswDiskStageFramedBall c k r hr).map.toCombinatorialMap.IsConnected := by
  exact kmswStageBallCombinatorialMap_rooted_isConnected
    (finiteCodeExtend (n := n + 1) c.val) n r (kmswDiskRootDart c k) hr

/-- All retained ambient outer-face incidences lie on the constructed ball's
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskStageFramedBall_outer_spec {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let B := kmswDiskStageFramedBall c k r hr
    ∀ x : B.D, (kmswStageDirectedMap u n).IsOuter x.1 → B.map.IsOuter x := by
  dsimp only
  intro x hx
  exact kmswDiskRootDart_ball_outer_survives c k r hr x.1 x.2 hx

/-- Ball vertices are precisely the retained rotation orbits: every ball
vertex has a retained dart and two darts represent the same vertex exactly
when their geometric endpoints agree
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskStageFramedBall_vertices_spec {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let s := kmswStage u n
    let d := kmswDiskRootDart c k
    let v := stageEndpoint s (edgeFlip _ d)
    let B := kmswDiskStageFramedBall c k r hr
    (∀ x y : B.D, B.map.rot.SameCycle x y ↔
      stageEndpoint s x.1 = stageEndpoint s y.1) ∧
      ∀ z : ℕ, z ∈ kmswStageBallVertices (fun _ _ => True) s r v ↔
        ∃ x : B.D, stageEndpoint s x.1 = z := by
  classical
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let s := kmswStage u n
  let d := kmswDiskRootDart c k
  let v := stageEndpoint s (edgeFlip _ d)
  constructor
  · exact kmswStageBallRot_sameCycle_iff_endpoint_eq (fun _ _ => True) u n r v
  · intro z
    constructor
    · intro hz
      obtain ⟨j, hj, hp⟩ := (Finset.mem_filter.mp hz).2
      cases hp with
      | nil _ => exact ⟨⟨edgeFlip _ d, (kmswDiskRootDart_ball_mem c k r hr).2⟩, rfl⟩
      | @snoc j a b hp ha hb hadj =>
        obtain ⟨e, heP, hea, heb⟩ := hadj
        have he : e ∈ kmswStageBallDarts (fun _ _ => True) s r v := by
          apply (kmswStageBallDarts_mem_iff_distanceLe _ u n r v e).mpr
          constructor
          · rw [hea]
            exact ⟨j, by omega, hp⟩
          · rw [heb]
            exact ⟨j + 1, hj, .snoc hp ha hb ⟨e, heP, hea, heb⟩⟩
        exact ⟨⟨edgeFlip _ e, (kmswStageBallDarts_edgeFlip _ s r v e).mp he⟩, heb⟩
    · rintro ⟨x, rfl⟩
      exact ((kmswStageBallDarts_mem_iff _ s r v x.1).mp x.2).1

/-- An original face whose boundary vertices lie in the ball retains exactly
its ambient face orbit, with no added incidences
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskStageFramedBall_face_spec {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let s := kmswStage u n
    let d := kmswDiskRootDart c k
    let v := stageEndpoint s (edgeFlip _ d)
    let B := kmswDiskStageFramedBall c k r hr
    ∀ x : B.D,
      (∀ j : ℕ, stageEndpoint s (((kmswMap u n).faceSucc ^ j) x.1) ∈
        kmswStageBallVertices (fun _ _ => True) s r v) →
      ∀ y : B.D, B.map.faceSucc.SameCycle x y ↔
        (kmswMap u n).faceSucc.SameCycle x.1 y.1 := by
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let s := kmswStage u n
  let d := kmswDiskRootDart c k
  let v := stageEndpoint s (edgeFlip _ d)
  intro x hx y
  refine inducedCombinatorialMap_face_sameCycle_iff (kmswMap u n)
    (kmswStageBallDarts (fun _ _ => True) s r v)
    (fun e he => (kmswStageBallDarts_edgeFlip (fun _ _ => True) s r v e).mp he)
    x ?_ y
  intro j
  apply (kmswStageBallDarts_mem_iff _ s r v _).mpr
  refine ⟨hx j, ?_⟩
  rw [← kmswStage_faceSucc_endpoint u n]
  simpa only [pow_succ', Equiv.Perm.mul_apply] using hx (j + 1)

/-- Every original triangular face with all three boundary vertices retained
keeps its three ordered, distinct incidences in the constructed framed ball
Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskStageFramedBall_triangle_spec {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (r : ℕ) (hr : 0 < r) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let s := kmswStage u n
    let d := kmswDiskRootDart c k
    let v := stageEndpoint s (edgeFlip _ d)
    let B := kmswDiskStageFramedBall c k r hr
    ∀ (j : TriangleCreationTime u) (hj : j.val < n),
      stageEndpoint s (stageTriangleDart₁ u n j hj) ∈
        kmswStageBallVertices (fun _ _ => True) s r v →
      stageEndpoint s (stageTriangleDart₂ u n j hj) ∈
        kmswStageBallVertices (fun _ _ => True) s r v →
      stageEndpoint s (stageTriangleDart₃ u n j hj) ∈
        kmswStageBallVertices (fun _ _ => True) s r v →
      ∃ a b e : B.D, a.1 = stageTriangleDart₁ u n j hj ∧
        b.1 = stageTriangleDart₂ u n j hj ∧ e.1 = stageTriangleDart₃ u n j hj ∧
        FaceSucc3Cycle B.map.faceSucc a b e := by
  dsimp only
  intro j hj hv₁ hv₂ hv₃
  obtain ⟨h₁, h₂, h₃, hcycle⟩ := kmswStageBallCombinatorialMap_triangle_of_vertices
    (finiteCodeExtend (n := n + 1) c.val) n r _ j hj hv₁ hv₂ hv₃
  exact ⟨⟨_, h₁⟩, ⟨_, h₂⟩, ⟨_, h₃⟩, rfl, rfl, rfl, hcycle⟩

end DirectedDistances.PlanarMap
