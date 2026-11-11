module

public import DirectedDistances.PaperProofs.Section5.DiskBSBallLaw
public import DirectedDistances.PlanarMap.RootedLocallyFiniteBallFramed

import DirectedDistances.PaperProofs.Section5.DiskBSBallRestriction
import DirectedDistances.KMSW.StageEdgesConnected

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap

private theorem rootedVertexClass_rot (M : RootedLocallyFiniteMap) (d : M.D) :
    rootedLocallyFiniteVertexClassOf M (M.rot d) =
      rootedLocallyFiniteVertexClassOf M d := by
  exact Quotient.sound Equiv.Perm.SameCycle.rfl.apply_left

private theorem rootedVertexClass_rot_symm (M : RootedLocallyFiniteMap)
    (d : M.D) :
    rootedLocallyFiniteVertexClassOf M (M.rot.symm d) =
      rootedLocallyFiniteVertexClassOf M d := by
  have hcycle : M.rot.SameCycle (M.rot (M.rot.symm d)) (M.rot.symm d) :=
    Equiv.Perm.SameCycle.rfl.apply_left
  have hcycle' : M.rot.SameCycle d (M.rot.symm d) := by
    simpa using hcycle
  exact Quotient.sound hcycle'.symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Every dart of a connected rooted map lies in some finite all-geometric ball -/
theorem rootedLocallyFinite_dart_reachable (M : RootedLocallyFiniteMap)
    (d : M.D) :
    ∃ r, rootedLocallyFiniteWithinRadius M r (rootedLocallyFiniteVertexClassOf M d) := by
  have hconn := M.connected M.rootDart d
  induction hconn with
  | refl => exact ⟨0, by simpa using rootedLocallyFiniteWithinRadius.root (M := M)⟩
  | tail hpath hstep ih =>
      obtain ⟨r, hr⟩ := ih
      rcases hstep with hrot | hrot | hedge | hedge
      · rw [hrot]
        refine ⟨r, ?_⟩
        simpa [rootedVertexClass_rot] using hr
      · rw [hrot]
        refine ⟨r, ?_⟩
        simpa [rootedVertexClass_rot_symm] using hr
      · rw [hedge]
        refine ⟨r + 1, ?_⟩
        apply rootedLocallyFiniteWithinRadius.edge hr
        exact ⟨_, rfl, rfl⟩
      · have hinv (x : M.D) : M.edgeInv.symm x = M.edgeInv x := by
          apply M.edgeInv.injective
          simp [M.edgeInv_invol]
        rw [hinv] at hedge
        rw [hedge]
        refine ⟨r + 1, ?_⟩
        apply rootedLocallyFiniteWithinRadius.edge hr
        exact ⟨_, rfl, rfl⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The rooted finite KMSW stage, marked at the selected missing boundary edge -/
@[expose] noncomputable def diskRootedMapOfCodeMark {ell n : ℕ}
    (c : KMSWLeftWalkClass ell n) (k : Fin (ell - 1)) :
    RootedLocallyFiniteMap := by
  let u := finiteCodeExtend (n := n + 1) c.val
  let s := kmswStage u n
  let d := kmswDiskRootDart c k
  let A : RootedLocallyFiniteMap := {
    D := StageDart s.nextEdge
    countableD := inferInstance
    rot := (kmswStageDirectedMap u n).rot
    edgeInv := (kmswStageDirectedMap u n).edgeInv
    edgeInv_invol := (kmswStageDirectedMap u n).edgeInv_invol
    edgeInv_ne := (kmswStageDirectedMap u n).edgeInv_ne
    missing := (kmswStageDirectedMap u n).missing
    missing_edgeInv := (kmswStageDirectedMap u n).missing_edgeInv
    tail := (kmswStageDirectedMap u n).tail
    tail_iff := (kmswStageDirectedMap u n).tail_iff
    tail_missing := (kmswStageDirectedMap u n).tail_missing
    outer := (kmswStageDirectedMap u n).outer
    missing_outer := (kmswStageDirectedMap u n).missing_outer
    rootDart := edgeFlip _ d
    frameEdgeDart := edgeFlip _ d
    frameEdge_missing := by
      exact ((kmswStageDirectedMap u n).missing_edgeInv d).mp
        (kmswDiskRootDart_missing c k)
    frameEdge_at_root := Equiv.Perm.SameCycle.rfl
    frameOtherDart := some d
    frameOtherDart_valid := by
      intro y hy
      have hy' : d = y := Option.some.inj hy
      rw [← hy']
      change (kmswStageDirectedMap u n).rot.SameCycle
        ((kmswStageDirectedMap u n).edgeInv
          ((kmswStageDirectedMap u n).edgeInv d)) d
      rw [(kmswStageDirectedMap u n).edgeInv_invol]
    locallyFinite := by
      intro x
      exact Set.toFinite _
    connected := by
      exact kmswMap_isConnected u n
    acyclic := by
      exact kmswStageDirectedMap_isAcyclic u n
  }
  exact A

end DirectedDistances.PaperProofs.Section5
