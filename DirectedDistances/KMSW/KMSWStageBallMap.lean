module

public import DirectedDistances.PlanarMap.CyclicRestriction
public import DirectedDistances.KMSW.KMSWStageBallDarts
public import DirectedDistances.KMSW.KMSWStageBallDartsStage
public import DirectedDistances.KMSW.StageRotation
public import DirectedDistances.PlanarMap.CombinatorialMap
public import DirectedDistances.KMSW.StageOuterCycle
import DirectedDistances.KMSW.StageVertices

/-! Helper toward `prop-disk-bs-conv` (Proposition 5.16, -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- The cyclic order on retained darts, obtained by first return of the stage -/
@[expose] noncomputable def kmswStageBallRot
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ) :
    Equiv.Perm (KMSWStageBallDart P (kmswStage w n) r c) :=
  cyclicFirstReturn (stageRot w n)
    (kmswStageBallDarts P (kmswStage w n) r c)
    (finitePermutationReturn (stageRot w n)
      (kmswStageBallDarts P (kmswStage w n) r c))

/-- The finite combinatorial map on ball darts, with the restricted edge -/
@[expose] noncomputable def kmswStageBallCombinatorialMap
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ) :
    CombinatorialMap (KMSWStageBallDart P (kmswStage w n) r c) where
  edgeInv := kmswStageBallDartFlip P (kmswStage w n) r c
  edgeInv_invol := by
    intro d
    apply Subtype.ext
    simp [kmswStageBallDartFlip, edgeFlip]
  edgeInv_ne := by
    intro d h
    have hb := congrArg (fun x : KMSWStageBallDart P (kmswStage w n) r c => x.1.2) h
    simp [kmswStageBallDartFlip, edgeFlip] at hb
  rot := kmswStageBallRot P w n r c

/-- Rotation-cycle equivalence on the ball agrees with ambient stage rotation -/
theorem kmswStageBallRot_sameCycle_iff
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ)
    (x y : KMSWStageBallDart P (kmswStage w n) r c) :
    (kmswStageBallRot P w n r c).SameCycle x y ↔
      (stageRot w n).SameCycle x.1 y.1 := by
  exact firstReturn_sameCycle_iff (stageRot w n)
    (kmswStageBallDarts P (kmswStage w n) r c)
    (finitePermutationReturn (stageRot w n)
      (kmswStageBallDarts P (kmswStage w n) r c)) x y

/-- Ball-rotation classes are exactly stage vertices, represented by equal -/
theorem kmswStageBallRot_sameCycle_iff_endpoint_eq
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ)
    (x y : KMSWStageBallDart P (kmswStage w n) r c) :
    (kmswStageBallRot P w n r c).SameCycle x y ↔
      stageEndpoint (kmswStage w n) x.1 =
        stageEndpoint (kmswStage w n) y.1 := by
  rw [kmswStageBallRot_sameCycle_iff]
  exact stageRot_sameCycle_iff_endpoint_eq w n x.1 y.1

/-- Restricting a larger-radius ball rotation to a smaller-radius dart set -/
theorem kmswStageBallRot_nested
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r r' c : ℕ)
    (hrr : r ≤ r') (x : KMSWStageBallDart P (kmswStage w n) r c) :
    let S := kmswStageBallDarts P (kmswStage w n) r' c
    let T := kmswStageBallDarts P (kmswStage w n) r c
    let U := firstReturnSubset S T
    ((@cyclicFirstReturn (KMSWStageBallDart P (kmswStage w n) r' c)
      Subtype.instDecidableEq (kmswStageBallRot P w n r' c) U
      (finitePermutationReturn (kmswStageBallRot P w n r' c) U)
      ⟨⟨x.1, kmswStageBallDarts_mono P (kmswStage w n) hrr x.2⟩,
        by simp [U, firstReturnSubset]⟩).1).1 =
      (kmswStageBallRot P w n r c x).1 := by
  let S := kmswStageBallDarts P (kmswStage w n) r' c
  let T := kmswStageBallDarts P (kmswStage w n) r c
  let U := firstReturnSubset S T
  have hTS : ∀ d, d ∈ T → d ∈ S :=
    fun d hd => kmswStageBallDarts_mono P (kmswStage w n) hrr hd
  simpa [S, T, U, kmswStageBallRot, firstReturnSubset] using
    firstReturn_nested (stageRot w n) S T
      (finitePermutationReturn (stageRot w n) S) hTS x

/-- Missing-edge status inherited by each retained ball dart. The predicate
is provided without choosing an outer face for the ball. -/
@[expose] def kmswStageBallMapMissing
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ)
    (d : KMSWStageBallDart P (kmswStage w n) r c) : Prop :=
  (kmswStageDirectedMap w n).missing d.1

/-- Tail status inherited by each retained ball dart. The predicate is
provided without choosing an outer face for the ball. -/
@[expose] def kmswStageBallMapTail
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ)
    (d : KMSWStageBallDart P (kmswStage w n) r c) : Prop :=
  (kmswStageDirectedMap w n).tail d.1

/-- Missing status is invariant under the restricted edge involution -/
theorem kmswStageBallMapMissing_edgeInv
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ)
    (d : KMSWStageBallDart P (kmswStage w n) r c) :
    kmswStageBallMapMissing P w n r c d ↔
      kmswStageBallMapMissing P w n r c
        (kmswStageBallDartFlip P (kmswStage w n) r c d) := by
  exact (kmswStageDirectedMap w n).missing_edgeInv d.1

/-- On present ball darts, exactly one of the two opposite darts is a tail -/
theorem kmswStageBallMapTail_iff
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ)
    (d : KMSWStageBallDart P (kmswStage w n) r c)
    (hd : ¬ kmswStageBallMapMissing P w n r c d) :
    kmswStageBallMapTail P w n r c d ↔
      ¬ kmswStageBallMapTail P w n r c
        (kmswStageBallDartFlip P (kmswStage w n) r c d) := by
  exact (kmswStageDirectedMap w n).tail_iff d.1 hd

/-- A missing ball dart is not a tail -/
theorem kmswStageBallMapTail_missing
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (n r c : ℕ)
    (d : KMSWStageBallDart P (kmswStage w n) r c)
    (hd : kmswStageBallMapMissing P w n r c d) :
    ¬ kmswStageBallMapTail P w n r c d := by
  exact (kmswStageDirectedMap w n).tail_missing d.1 hd

end DirectedDistances.KMSW
