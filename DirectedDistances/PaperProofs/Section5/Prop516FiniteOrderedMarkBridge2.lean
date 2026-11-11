/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516SourceStatement
public import DirectedDistances.PaperProofs.Section5.Prop516RootAlignment
public import DirectedDistances.PaperProofs.Section5.Prop516RootAlignment2
public import DirectedDistances.PaperProofs.Section5.Prop516RootAlignment3
public import DirectedDistances.KMSW.KMSWDiskFiniteSample
public import DirectedDistances.PaperProofs.Section5.DiskRootedPlanarLaw
public import DirectedDistances.KMSW.KMSWDiskRootOrderedFrame

/-! # Finite ordered missing-edge mark for Proposition 5.16

The finite source list is the KMSW stage `LL` list itself, which is already
west-to-east. Its entries are distinct missing geometric edges. The sample
mark with index `k` selects entry `LL.length - 1 - k`, as recorded by the
ordered-frame result. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory

/-- Helper toward Proposition 5.16. The source lower-left missing-edge list
for a finite channeled sample, in west-to-east order. The sample is represented
by its canonical finite KMSW walk, and the list records geometric edge IDs. -/
@[expose] noncomputable def diskRootedSampleLowerLeftMissingEdgeList
    (n ell : ℕ) (hell : 0 < ell)
    (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}) :
    List ℕ :=
  let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q
  (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).LL

/-- Helper toward Proposition 5.16. The finite source lower-left list has one
entry for each of the `ell` missing boundary edges. -/
theorem diskRootedSampleLowerLeftMissingEdgeList_length
    (n ell : ℕ) (hell : 0 < ell)
    (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}) :
    (diskRootedSampleLowerLeftMissingEdgeList n ell hell q).length = ell := by
  let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q
  have hk : Fin ((ell + 1) - 1) :=
    Fin.cast (by omega : ell = (ell + 1) - 1) ⟨0, hell⟩
  have hlen := (kmswDiskFiniteSample_index_bound c hk).1
  change (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).LL.length = ell
  rw [hlen]
  omega

/-- Helper toward Proposition 5.16. The west-to-east list has exactly the
edge IDs in the finite KMSW lower-left chain. -/
theorem diskRootedSampleLowerLeftMissingEdgeList_mem_iff
    (n ell : ℕ) (hell : 0 < ell)
    (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled})
    (e : ℕ) :
    e ∈ diskRootedSampleLowerLeftMissingEdgeList n ell hell q ↔
      e ∈ (kmswStage
        (finiteCodeExtend (n := n + 1)
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q).val) n).LL := by
  simp [diskRootedSampleLowerLeftMissingEdgeList]

/-- Helper toward Proposition 5.16. The source lower-left missing-edge list
has no repeated geometric edge IDs. -/
theorem diskRootedSampleLowerLeftMissingEdgeList_nodup
    (n ell : ℕ) (hell : 0 < ell)
    (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}) :
    (diskRootedSampleLowerLeftMissingEdgeList n ell hell q).Nodup := by
  let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q
  let u := finiteCodeExtend (n := n + 1) c.val
  simpa [diskRootedSampleLowerLeftMissingEdgeList, c, u] using
    (kmswStageFrontierChain_all u n).LL_nodup

/-- Helper toward Proposition 5.16. Every entry of the source lower-left list
is missing in the finite sampled planar map. -/
theorem diskRootedSampleLowerLeftMissingEdgeList_entries_missing
    (n ell : ℕ) (hell : 0 < ell)
    (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}) :
    ∀ e ∈ diskRootedSampleLowerLeftMissingEdgeList n ell hell q,
      (kmswStage
        (finiteCodeExtend (n := n + 1)
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q).val) n).present e =
        false := by
  let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q
  let u := finiteCodeExtend (n := n + 1) c.val
  intro e he
  have heLL : e ∈ (kmswStage u n).LL := by
    simpa [diskRootedSampleLowerLeftMissingEdgeList, c, u] using he
  exact (kmswStageFrontierChain_all u n).LL_missing_bounded e heLL |>.1

/-- Helper toward Proposition 5.16. The west-to-east lower-left list positions
are explicitly equivalent to `Fin ell`; the equivalence reverses indices,
matching the KMSW exploration order. -/
private def diskRootedFinReverseEquiv (m : ℕ) : Fin m ≃ Fin m where
  toFun i := ⟨m - 1 - i.val, by omega⟩
  invFun i := ⟨m - 1 - i.val, by omega⟩
  left_inv i := by
    apply Fin.ext
    simp
    omega
  right_inv i := by
    apply Fin.ext
    simp
    omega

private def diskRootedFinCastEquiv {m n : ℕ} (h : m = n) : Fin m ≃ Fin n where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv i := by
    apply Fin.ext
    rfl
  right_inv i := by
    apply Fin.ext
    rfl

noncomputable def diskRootedSampleLowerLeftPositionEquiv
    (n ell : ℕ) (hell : 0 < ell)
    (c : KMSWLeftWalkClass (ell + 1) n) :
    Fin ell ≃ Fin (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).LL.length := by
  let S := kmswStage (finiteCodeExtend (n := n + 1) c.val) n
  let k₀ : Fin ((ell + 1) - 1) :=
    Fin.cast (by omega : ell = (ell + 1) - 1) ⟨0, hell⟩
  have hlen : ell = S.LL.length := by
    simpa only [Nat.add_sub_cancel] using
      (kmswDiskFiniteSample_index_bound c k₀).1.symm
  exact (diskRootedFinCastEquiv hlen).trans (diskRootedFinReverseEquiv S.LL.length)

/-- Helper toward Proposition 5.16. The sample mark with index `k` selects
the lower-left entry at west-to-east position `LL.length - 1 - k`. -/
theorem diskRootedSample_mark_eq_orderedMissingEdge
    (n ell : ℕ) (hell : 0 < ell)
    (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled})
      (k : Fin ell) :
    (diskSampleLowerLeftEdgeId
      ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q) k).val =
    (diskRootedSampleLowerLeftMissingEdgeList n ell hell q).get
        (diskRootedSampleLowerLeftPositionEquiv n ell hell
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q) k) := by
  let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q
  let k' : Fin ((ell + 1) - 1) := Fin.cast (by omega : ell = (ell + 1) - 1) k
  have hposition := kmswDiskRootEdge_ll_position c k'
  dsimp only at hposition
  have hmark : (diskSampleLowerLeftEdgeId c k).val =
      kmswLLCreatedEdge (finiteCodeExtend (n := n + 1) c.val)
        (kmswDiskFirstHit c k') := rfl
  rw [hmark]
  have hget := hposition.2.2.2
  have hidx :
      (⟨(kmswStage (finiteCodeExtend (n := n + 1) c.val) n).LL.length - 1 - k'.val,
        by
          have hlen := (kmswDiskFiniteSample_index_bound c k').1
          rw [hlen]
          have hk := k'.isLt
          omega⟩ : Fin (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).LL.length) =
        diskRootedSampleLowerLeftPositionEquiv n ell hell c k := by
    apply Fin.ext
    simp [diskRootedSampleLowerLeftPositionEquiv, diskRootedFinCastEquiv,
      diskRootedFinReverseEquiv, k']
  have hget' :
      (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).LL.get
        (diskRootedSampleLowerLeftPositionEquiv n ell hell c k) =
      kmswLLCreatedEdge (finiteCodeExtend (n := n + 1) c.val)
        (kmswDiskFirstHit c k') := by
    rw [← hidx]
    simpa only [Nat.add_sub_cancel] using hget
  simpa only [diskRootedSampleLowerLeftMissingEdgeList, c] using hget'.symm

/-- Helper toward Proposition 5.16. Conditional on the finite channeled map,
the uniform `Fin ell` mark pushes forward to the uniform counting law on its
source lower-left missing-edge list. -/
theorem diskRootedSample_mark_conditional_uniform
    (n ell : ℕ) (hell : 0 < ell)
    (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}) :
    let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q
    letI : Fintype {e : ℕ // e ∈ (kmswStage
      (finiteCodeExtend (n := n + 1)
        ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q).val) n).LL} :=
      List.Subtype.fintype _
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace
      {e : ℕ // e ∈ (kmswStage
        (finiteCodeExtend (n := n + 1)
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q).val) n).LL} := ⊤
    Measure.map
        (fun k : Fin ell => diskSampleLowerLeftEdgeId c k)
        (uniformCountingMeasure (Fin ell)) =
      uniformCountingMeasure
        {e : ℕ // e ∈ (kmswStage
          (finiteCodeExtend (n := n + 1)
            ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q).val) n).LL} := by
  let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q
  letI : Fintype {e : ℕ // e ∈ (kmswStage
      (finiteCodeExtend (n := n + 1) c.val) n).LL} := List.Subtype.fintype _
  letI : MeasurableSpace (Fin ell) := ⊤
  letI : MeasurableSpace
      {e : ℕ // e ∈ (kmswStage
        (finiteCodeExtend (n := n + 1) c.val) n).LL} := ⊤
  change Measure.map (diskSampleLowerLeftEdgeId c) (uniformCountingMeasure (Fin ell)) =
    uniformCountingMeasure
      {e : ℕ // e ∈ (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).LL}
  exact diskSampleLowerLeftEdgeId_uniform hell c

/-- Helper toward Proposition 5.16. Transporting the source representative's
west-to-east left-boundary dart at index `k` to the canonical finite map gives
the marked geometric edge. -/
theorem diskRootedSample_sourceBoundaryDart_eq_mark
    (n ell : ℕ) (hell : 0 < ell)
    (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled})
    (I : DirectedMapWithMissingIso q.val.out.partialMap
      (kmswStageDirectedMap
        (finiteCodeExtend (n := n + 1)
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q).val) n))
    (k : Fin ell) :
    I.toEquiv (q.val.out.B.leftPath.darts.get
      ⟨k.val, by rw [q.val.out.B.leftPath.darts_length]; omega⟩) =
      kmswDiskRootDart
        ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q)
        (Fin.cast (by omega : ell = (ell + 1) - 1) k) := by
  exact iso_leftPathDart_eq_rootDart (by omega)
    ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q) q I
    (Fin.cast (by omega : ell = (ell + 1) - 1) k)

/-- Helper toward Proposition 5.16. The sampled rooted planar-map edge ID
equals the `k`th entry of the west-to-east source lower-left list. -/
theorem diskRootedSample_rootEdge_eq_orderedMissingEdge
    (n ell : ℕ) (hell : 0 < ell)
    (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled})
    (k : Fin ell) :
    ((diskRootedPlanarMapOfSample n ell hell (q, k)).toRootedLocallyFiniteMap.rootDart).1.val =
    (diskRootedSampleLowerLeftMissingEdgeList n ell hell q).get
        (diskRootedSampleLowerLeftPositionEquiv n ell hell
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q) k) := by
  let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q
  let k' : Fin ((ell + 1) - 1) := Fin.cast (by omega : ell = (ell + 1) - 1) k
  have hroot := diskRootedMapOfCodeMark_rootEdge_eq_sample c k'
  have hmark := diskRootedSample_mark_eq_orderedMissingEdge n ell hell q k
  change ((diskRootedMapOfCodeMark c k').rootDart).1.val = _
  rw [congrArg Fin.val hroot]
  exact hmark

/-- Helper toward Proposition 5.16. The root of every admitted finite sample
is the west endpoint of its marked missing geometric edge. -/
theorem diskRootedSample_root_endpoint_eq_west
    (n ell : ℕ) (hell : 0 < ell)
    (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled})
      (k : Fin ell) :
    stageEndpoint
        (kmswStage
          (finiteCodeExtend (n := n + 1)
            ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q).val) n)
        ((diskRootedPlanarMapOfSample n ell hell (q, k)).toRootedLocallyFiniteMap.rootDart) =
      (kmswStage
        (finiteCodeExtend (n := n + 1)
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q).val) n).west
        (kmswDiskRootDart
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q)
          (Fin.cast (by omega : ell = (ell + 1) - 1) k)).1.val := by
  exact diskRootedPlanarMapOfSample_rootEndpoint_eq_west n ell hell (q, k)

/-- Helper toward Proposition 5.16. The root endpoint is the west endpoint
of the marked edge at its reversed west-to-east `LL` position. -/
theorem diskRootedSample_root_endpoint_eq_westEntry
    (n ell : ℕ) (hell : 0 < ell)
    (q : {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled})
    (k : Fin ell) :
    stageEndpoint
        (kmswStage (finiteCodeExtend (n := n + 1)
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q).val) n)
        ((diskRootedPlanarMapOfSample n ell hell (q, k)).toRootedLocallyFiniteMap.rootDart) =
      (kmswStage (finiteCodeExtend (n := n + 1)
        ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q).val) n).west
        ((diskRootedSampleLowerLeftMissingEdgeList n ell hell q).get
          (diskRootedSampleLowerLeftPositionEquiv n ell hell
            ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q) k)) := by
  let c := (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm q
  let k' : Fin ((ell + 1) - 1) := Fin.cast (by omega : ell = (ell + 1) - 1) k
  have hroot := diskRootedPlanarMapOfSample_rootEndpoint_eq_west n ell hell (q, k)
  have hmark := diskRootedSample_mark_eq_orderedMissingEdge n ell hell q k
  have hmark' : (kmswDiskRootDart c k').1.val =
      (diskRootedSampleLowerLeftMissingEdgeList n ell hell q).get
        (diskRootedSampleLowerLeftPositionEquiv n ell hell c k) := by
    change (diskSampleLowerLeftEdgeId c k).val = _
    exact hmark
  rw [hmark'] at hroot
  exact hroot

end DirectedDistances.PaperProofs.Section5
