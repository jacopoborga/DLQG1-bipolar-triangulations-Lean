module

public import DirectedDistances.PlanarMap.FacedFramedBall
public import DirectedDistances.PlanarMap.KMSWStageFramedBall

public section
namespace DirectedDistances.PlanarMap

open DirectedDistances.KMSW
open CombinatorialMap

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
whose entire boundary lies in the all-geometric ball. -/
@[expose] noncomputable def kmswDiskStageFacedFramedBall {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1))
    (r : ℕ) (hr : 0 < r) : FacedFramedBall := by
  classical
  let u := finiteCodeExtend (n := n + 1) c.val
  let s := kmswStage u n
  let d := kmswDiskRootDart c k
  let v := stageEndpoint s (edgeFlip _ d)
  let V := kmswStageBallVertices (fun _ _ => True) s r v
  let B := kmswDiskStageFramedBall c k r hr
  refine ⟨B, {x | ∀ j : ℕ,
    stageEndpoint s (((kmswMap u n).faceSucc ^ j) x.1) ∈ V}, ?_⟩
  intro x
  let q := B.map.faceSucc x
  simp only [Set.mem_ofPred_eq]
  change (∀ j : ℕ,
      stageEndpoint s (((kmswMap u n).faceSucc ^ j) q.1) ∈ V) ↔
    ∀ j : ℕ,
      stageEndpoint s (((kmswMap u n).faceSucc ^ j) x.1) ∈ V
  constructor
  · intro hq
    have hcycle : B.map.faceSucc.SameCycle q x := by
      refine ⟨-1, ?_⟩
      simp [q]
    have hspec := kmswDiskStageFramedBall_face_spec c k r hr q hq
    have hamb := (hspec x).mp hcycle
    obtain ⟨m, hm⟩ := hamb.exists_nat_pow_eq
    intro j
    have heq : ((kmswMap u n).faceSucc ^ (j + m)) q.1 =
        ((kmswMap u n).faceSucc ^ j) x.1 := by
      rw [pow_add, Equiv.Perm.mul_apply, hm]
    rw [← heq]
    exact hq (j + m)
  · intro hx
    have hcycle : B.map.faceSucc.SameCycle x q := by
      refine ⟨1, ?_⟩
      simp [q]
    have hspec := kmswDiskStageFramedBall_face_spec c k r hr x hx
    have hamb := (hspec q).mp hcycle
    obtain ⟨m, hm⟩ := hamb.exists_nat_pow_eq
    intro j
    have heq : ((kmswMap u n).faceSucc ^ (j + m)) x.1 =
        ((kmswMap u n).faceSucc ^ j) q.1 := by
      rw [pow_add, Equiv.Perm.mul_apply, hm]
    rw [← heq]
    exact hx (j + m)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
ambient original face orbit has both endpoints in the retained vertex set. -/
theorem kmswDiskStageFacedFramedBall_original_iff {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1))
    (r : ℕ) (hr : 0 < r)
    (x : ((kmswDiskStageFacedFramedBall c k r hr).toFramedBall).D) :
    x ∈ (kmswDiskStageFacedFramedBall c k r hr).original ↔
      ∀ j : ℕ,
        stageEndpoint (kmswStage (finiteCodeExtend (n := n + 1) c.val) n)
          (((kmswMap (finiteCodeExtend (n := n + 1) c.val) n).faceSucc ^ j)
            x.1) ∈
          kmswStageBallVertices (fun _ _ => True)
            (kmswStage (finiteCodeExtend (n := n + 1) c.val) n) r
            (stageEndpoint (kmswStage (finiteCodeExtend (n := n + 1) c.val) n)
              (edgeFlip _ (kmswDiskRootDart c k))) := by
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
@[reducible] def forgetFacedFramedBall (B : FacedFramedBall) : FramedBall :=
  B.toFramedBall

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem forget_kmswDiskStageFacedFramedBall {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1))
    (r : ℕ) (hr : 0 < r) :
    forgetFacedFramedBall (kmswDiskStageFacedFramedBall c k r hr) =
      kmswDiskStageFramedBall c k r hr := by
  simp [forgetFacedFramedBall, kmswDiskStageFacedFramedBall]

end DirectedDistances.PlanarMap
