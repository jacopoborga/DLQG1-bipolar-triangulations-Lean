/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingRepresentation4
public import DirectedDistances.PaperProofs.Section5.D39DiskSampleMeasurability
public import DirectedDistances.PaperProofs.Section5.DiskRootedMapObject

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16. The finite sample's rooted stage map is
the KMSW stage directed map on the canonical walk, with the selected missing
dart flipped to the ordered root. All geometric edges, including missing
boundary edges, retain their individual dart identities. -/
@[expose] noncomputable def diskSampleRootedStageMap (ell n : ℕ)
    (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) : RootedLocallyFiniteMap := by
  let c : KMSWLeftWalkClass (ell + 1) n :=
    (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1
  let k : Fin ((ell + 1) - 1) :=
    Fin.cast (by omega : ell = (ell + 1) - 1) p.2
  let u := finiteCodeExtend (n := n + 1) c.val
  let d := kmswDiskRootDart c k
  let s := kmswStage u n
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
    connected := kmswMap_isConnected u n
    acyclic := kmswStageDirectedMap_isAcyclic u n
  }
  exact A

/-- Helper toward Proposition 5.16. The sample-rooted stage map is exactly
`diskRootedMapOfCodeMark` for the canonical walk and cast sample index. -/
theorem diskSampleRootedStageMap_eq_diskRootedMapOfCodeMark (ell n : ℕ)
    (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) :
    diskSampleRootedStageMap ell n hell p =
      diskRootedMapOfCodeMark
        ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1)
        (Fin.cast (by omega : ell = (ell + 1) - 1) p.2) := rfl

/-- Helper toward Proposition 5.16. The rooted stage map has exactly the
dart reversal and vertex rotation used by `StageDrawing w n`, so the drawing
parameter `P : StageDrawing w n` represents this same unrooted stage map. -/
theorem diskSampleRootedStageMap_drawingStructure_eq
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) :
    let w := finiteCodeExtend (n := n + 1)
      ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1).val
    (diskSampleRootedStageMap ell n hell p).rot = stageRot w n ∧
      (diskSampleRootedStageMap ell n hell p).edgeInv =
        edgeFlip (kmswStage w n).nextEdge := by
  exact ⟨rfl, rfl⟩

/-- Helper toward Proposition 5.16. The ordered sample mark roots the stage at
the flipped dart, as required by the paper's ordered missing root convention. -/
theorem diskSampleRootedStageMap_rootDart_eq
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) :
    let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1
    let k : Fin ((ell + 1) - 1) :=
      Fin.cast (by omega : ell = (ell + 1) - 1) p.2
    (diskSampleRootedStageMap ell n hell p).rootDart =
      edgeFlip _ (kmswDiskRootDart c k) := rfl

/-- Helper toward Proposition 5.16. The sample-rooted stage map's rotation
classes are identified with the stage's allocated vertex IDs by the KMSW
endpoint labeling. This is the vertex set used by `StageDrawing`. -/
@[expose] noncomputable def diskSampleRootedStageMap_vertexEquiv
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) :
    RootedLocallyFiniteVertex
      (diskSampleRootedStageMap ell n hell p).D
      (diskSampleRootedStageMap ell n hell p).rot ≃
      Fin (kmswStage
        (finiteCodeExtend (n := n + 1)
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1).val)
        n).nextVertex := by
  let c : KMSWLeftWalkClass (ell + 1) n :=
    (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1
  let u := finiteCodeExtend (n := n + 1) c.val
  change (kmswMap u n).VertexQuotient ≃ _
  exact stageVertexEquiv u n

/-- Helper toward Proposition 5.16. On each dart, the vertex equivalence
above returns the endpoint label used by the stage drawing. -/
theorem diskSampleRootedStageMap_vertexEquiv_dart
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell)
    (d : (diskSampleRootedStageMap ell n hell p).D) :
    diskSampleRootedStageMap_vertexEquiv ell n hell p
        (rootedLocallyFiniteVertexClassOf
          (diskSampleRootedStageMap ell n hell p) d) =
      stageVertex
        (finiteCodeExtend (n := n + 1)
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1).val)
        n d := by
  let c : KMSWLeftWalkClass (ell + 1) n :=
    (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm p.1
  let u := finiteCodeExtend (n := n + 1) c.val
  change stageVertexEquiv u n (Quotient.mk _ d) = _
  rfl

/-- Helper toward Proposition 5.16. The stage-rooted local topology map and the local topology map
of the finite sample have the same core and ordered missing root dart. -/
theorem diskSampleRootedStageD39Map_eq_diskRootedD39MapOfSample
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) :
    (diskSampleRootedStageMap ell n hell p).toD39RootedMap =
      diskRootedD39MapOfSample n ell hell p := by
  rfl

/-- Helper toward Proposition 5.16. The identity dart equivalence gives a
whole rooted-map isomorphism from the sample-rooted stage map to the local topology map
used by the finite sample. Its fields retain rotation, reversal, missing tags,
orientation on present darts, and the ordered root dart. -/
@[expose] noncomputable def diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) :
    D39RootedMapIso
      (diskSampleRootedStageMap ell n hell p).toD39RootedMap
      (diskRootedD39MapOfSample n ell hell p) := by
  rw [diskSampleRootedStageD39Map_eq_diskRootedD39MapOfSample]
  exact D39RootedMapIso.refl _

/-- Helper toward Proposition 5.16. The sample isomorphism acts identically
on each individual geometric dart, retaining parallel-edge identity. -/
theorem diskSampleRootedStageD39Map_dartEquiv_apply
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell)
    (d : ((diskSampleRootedStageMap ell n hell p).toD39RootedMap).core.D) :
    (diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
      ell n hell p).toEquiv d = d := by
  cases diskSampleRootedStageD39Map_eq_diskRootedD39MapOfSample
    ell n hell p
  rfl

/-- Helper toward Proposition 5.16. The stage-to-sample isomorphism retains
the rotation, edge reversal, missing tag, present-edge orientation, and
ordered root dart required by a rooted-map isomorphism. -/
theorem diskSampleRootedStageD39Map_preserves_rootedMapData
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell)
    (d : ((diskSampleRootedStageMap ell n hell p).toD39RootedMap).core.D) :
    (diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
      ell n hell p).toEquiv
        (((diskSampleRootedStageMap ell n hell p).toD39RootedMap).core.rot d) =
      (diskRootedD39MapOfSample n ell hell p).core.rot
        ((diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
          ell n hell p).toEquiv d) ∧
    (diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
      ell n hell p).toEquiv
        (((diskSampleRootedStageMap ell n hell p).toD39RootedMap).core.edgeInv d) =
      (diskRootedD39MapOfSample n ell hell p).core.edgeInv
        ((diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
          ell n hell p).toEquiv d) ∧
    ((diskRootedD39MapOfSample n ell hell p).core.missing
        ((diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
          ell n hell p).toEquiv d) ↔
      ((diskSampleRootedStageMap ell n hell p).toD39RootedMap).core.missing d) ∧
    (¬ ((diskSampleRootedStageMap ell n hell p).toD39RootedMap).core.missing d →
      ((diskRootedD39MapOfSample n ell hell p).core.tail
          ((diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
            ell n hell p).toEquiv d) ↔
        ((diskSampleRootedStageMap ell n hell p).toD39RootedMap).core.tail d)) ∧
    (diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
      ell n hell p).toEquiv
        (((diskSampleRootedStageMap ell n hell p).toD39RootedMap).rootMark.dart) =
      (diskRootedD39MapOfSample n ell hell p).rootMark.dart := by
  exact ⟨(diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
      ell n hell p).rot_comm d,
    (diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
      ell n hell p).edgeInv_comm d,
    (diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
      ell n hell p).missing_iff d,
    (diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
      ell n hell p).tail_iff d,
    (diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
      ell n hell p).root_dart_comm⟩

/-- Helper toward Proposition 5.16. The sample isomorphism's induced vertex
equivalence is the identity on the shared rotation-cycle classes. -/
theorem diskSampleRootedStageD39Map_vertexEquiv_apply
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell)
    (v : RootedLocallyFiniteVertex
      ((diskSampleRootedStageMap ell n hell p).toD39RootedMap).core.D
      ((diskSampleRootedStageMap ell n hell p).toD39RootedMap).core.rot) :
    (diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
      ell n hell p).vertexEquiv v = v := by
  refine Quotient.inductionOn v ?_
  intro d
  rfl

/-- Helper toward Proposition 5.16. The sample isomorphism induces a
bijection between face classes, represented by cycles of `rot.symm * edgeInv`.
This retains the face of each individual dart. -/
@[expose] noncomputable def diskSampleRootedStageD39Map_faceEquiv
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell) :
    Quotient (Equiv.Perm.SameCycle.setoid
      (((diskSampleRootedStageMap ell n hell p).toD39RootedMap).core.rot.symm *
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.edgeInv)) ≃
    Quotient (Equiv.Perm.SameCycle.setoid
      ((diskRootedD39MapOfSample n ell hell p).core.rot.symm *
        (diskRootedD39MapOfSample n ell hell p).core.edgeInv)) := by
  let I := diskSampleRootedStageD39Map_iso_diskRootedD39MapOfSample
    ell n hell p
  exact {
    toFun := Quotient.map I.toEquiv
      (fun _ _ h => (I.faceSameCycle_iff _ _).mp h)
    invFun := Quotient.map I.toEquiv.symm
      (fun _ _ h => (I.symm.faceSameCycle_iff _ _).mp h)
    left_inv := by
      intro q
      refine Quotient.inductionOn q ?_
      intro d
      change Quotient.mk _ (I.toEquiv.symm (I.toEquiv d)) = Quotient.mk _ d
      rw [Equiv.symm_apply_apply]
    right_inv := by
      intro q
      refine Quotient.inductionOn q ?_
      intro d
      change Quotient.mk _ (I.toEquiv (I.toEquiv.symm d)) = Quotient.mk _ d
      rw [Equiv.apply_symm_apply] }

/-- Helper toward Proposition 5.16. The sample isomorphism's induced face
equivalence is the identity on the shared cycles of `rot.symm * edgeInv`. -/
theorem diskSampleRootedStageD39Map_faceEquiv_apply
    (ell n : ℕ) (hell : 0 < ell)
    (p : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} ×
      Fin ell)
    (f : Quotient (Equiv.Perm.SameCycle.setoid
      (((diskSampleRootedStageMap ell n hell p).toD39RootedMap).core.rot.symm *
        (diskSampleRootedStageMap ell n hell p).toD39RootedMap.core.edgeInv))) :
    diskSampleRootedStageD39Map_faceEquiv ell n hell p f = f := by
  refine Quotient.inductionOn f ?_
  intro d
  rfl

end DirectedDistances.PaperProofs.Section5

end
