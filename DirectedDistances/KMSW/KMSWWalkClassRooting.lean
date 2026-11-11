/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FiniteWalkClass
public import DirectedDistances.KMSW.StageBoundaryMap
public import DirectedDistances.KMSW.KMSWInverse
public import DirectedDistances.PlanarMap.BipolarBoundaryBaseIso

/-! # Boundary identification of the finite-walk stage root

Helpers toward injectivity on unrooted classes for `thm-kmsw`
last dart of the ordered upper-left boundary run, including the one-edge
stage at time zero. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- The active root dart is the last dart of the ordered upper-left boundary
run, for every finite stage, including stage zero (`def-kmsw`,
result. -/
theorem kmswRootedStage_root_getLast_ULDartRun (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageULDartRun w n).getLast? = some (kmswRootedStage w n).root := by
  have hUL := (kmswStage_UL_nonempty_active_last w n).1
  have hULlast := (kmswStage_UL_nonempty_active_last w n).2
  have hrun : kmswStageULDartRun w n ≠ [] := by
    intro h
    have hlen : (kmswStageULDartRun w n).length = (kmswStage w n).UL.length := by
      simp [kmswStageULDartRun, stageDarts]
    rw [h] at hlen
    exact hUL (List.length_eq_zero_iff.mp hlen.symm)
  have hget : (kmswStage w n).UL.getLast? = some (kmswStage w n).active := hULlast
  simp only [kmswStageULDartRun, stageDarts, List.getLast?_map,
    List.getLast?_attach] at hrun ⊢
  simp only [hget] at hrun ⊢
  rfl


/-- The finite walk stage root is the final dart of its ordered UL boundary
run for every `c : KMSWWalkClass ℓ r n`, including `n = 1` (stage zero),
on unrooted classes; not the paper result. -/
theorem kmswWalkClassMap_root_getLast_ULDartRun {ℓ r n : ℕ}
    (c : KMSWWalkClass ℓ r n) :
    (kmswStageULDartRun (codeExtend c) (n - 1)).getLast? =
      some (kmswWalkClassMap c).root := by
  exact kmswRootedStage_root_getLast_ULDartRun (codeExtend c) (n - 1)

private theorem simplePath_getLast_eq_of_chain_mem
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) (L : List D)
    (hne : L ≠ [])
    (hchain : L.IsChain (fun d e => dartHeadVertex M d = dartTailVertex M e))
    (hmem : ∀ d, d ∈ P.darts ↔ d ∈ L) :
    P.darts.getLast? = L.getLast? := by
  have hlastL_mem : L.getLast hne ∈ L := List.getLast_mem hne
  have hlastP_mem : L.getLast hne ∈ P.darts := (hmem _).2 hlastL_mem
  have hpne : P.darts ≠ [] := List.ne_nil_of_mem hlastP_mem
  have hkpos : 0 < k := by
    have hpos : 0 < P.darts.length := List.length_pos_of_mem hlastP_mem
    rw [P.darts_length] at hpos
    exact hpos
  have hlastP_head :
      dartHeadVertex M (P.darts.getLast hpne) = t := by
    let i : Fin P.darts.length := ⟨k - 1, by rw [P.darts_length]; omega⟩
    have hlast_get : P.darts.getLast hpne = P.darts.get i := by
      simp [i, List.getLast_eq_getElem, P.darts_length]
    rw [hlast_get]
    have hstep := P.edge_step i
    have hiend : i.val + 1 = k := by
      simp [i]
      omega
    have hhead :
        dartHeadVertex M (P.darts.get i) =
          P.vertices.get ⟨k, by rw [P.vertices_length]; omega⟩ := by
      simpa only [hiend] using hstep.2.2.2.symm
    exact hhead.trans P.end_vertex
  have hlast_eq : P.darts.getLast hpne = L.getLast hne := by
    by_contra hneLast
    have hlastP_in_L : P.darts.getLast hpne ∈ L := (hmem _).1 (List.getLast_mem hpne)
    obtain ⟨i, hi, hlastEq⟩ := List.getElem_of_mem hlastP_in_L
    have hneIndex : L[i] ≠ L.getLast hne := by
      intro heq
      exact hneLast (hlastEq.symm.trans heq)
    have hsucc : i + 1 < L.length := by
      by_contra hnot
      have hiend : i + 1 = L.length := by omega
      have hlastIndex : L.getLast hne = L[i] := by
        rw [List.getLast_eq_getElem]
        congr 1
        omega
      exact hneIndex hlastIndex.symm
    have hnext_mem : L[i + 1] ∈ L := List.getElem_mem hsucc
    have hnextP_mem : L[i + 1] ∈ P.darts := (hmem _).2 hnext_mem
    obtain ⟨j, hj, hnextEq⟩ := List.getElem_of_mem hnextP_mem
    have hj' : j < k := by simpa only [P.darts_length] using hj
    have hnextTail : dartTailVertex M (P.darts.get ⟨j, by
        exact hj⟩) = t := by
      calc
        _ = dartTailVertex M L[i + 1] := by
          change dartTailVertex M P.darts[j] = dartTailVertex M L[i + 1]
          rw [hnextEq]
        _ = dartHeadVertex M (P.darts.getLast hpne) :=
          (hchain.getElem i hsucc).symm.trans (congrArg (dartHeadVertex M) hlastEq)
        _ = t := hlastP_head
    have hstep := P.edge_step ⟨j, hj⟩
    have hvertex : P.vertices.get ⟨j, by rw [P.vertices_length]; omega⟩ = t :=
      hstep.2.2.1.trans hnextTail
    have hindex :
        (⟨j, by rw [P.vertices_length]; omega⟩ : Fin P.vertices.length) =
          ⟨k, by rw [P.vertices_length]; omega⟩ :=
      (List.nodup_iff_injective_get.mp P.vertices_nodup) (hvertex.trans P.end_vertex.symm)
    have hindex_val := congrArg Fin.val hindex
    have hEqjk : j = k := by simpa using hindex_val
    omega
  rw [List.getLast?_eq_getLast_of_ne_nil hpne,
    List.getLast?_eq_getLast_of_ne_nil hne, hlast_eq]

private theorem kmswStageULDartRun_chain (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStageULDartRun w n).IsChain
      (fun d e => dartHeadVertex (kmswStageDirectedMap w n) d =
        dartTailVertex (kmswStageDirectedMap w n) e) := by
  have hids : List.IsChain (fun e f =>
      (kmswStage w n).east e = (kmswStage w n).west f)
      (kmswStage w n).UL := by
    have h := (kmswStage_boundary_chain_invariant w n).1
    change List.IsChain (fun e f =>
      (kmswStage w n).east e = (kmswStage w n).west f)
      ((kmswStage w n).UL ++ (kmswStage w n).UR) at h
    exact h.left_of_append
  rw [List.isChain_iff_getElem]
  intro i hi
  have hiUL : i + 1 < (kmswStage w n).UL.length := by
    have hlen : (kmswStageULDartRun w n).length = (kmswStage w n).UL.length := by
      simp [kmswStageULDartRun, stageDarts]
    rw [hlen] at hi
    exact hi
  have hstep := hids.getElem i hiUL
  apply Quotient.sound
  apply (stageRot_sameCycle_iff_endpoint_eq w n _ _).2
  simpa [kmswStageULDartRun, stageDarts, kmswStageDirectedMap,
    kmswDirectedMap, dartHeadVertex, dartTailVertex, kmswMap_edgeInv,
    stageEndpoint, edgeFlip_apply] using hstep

private theorem kmswStageULDartRun_mem_map (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    d ∈ kmswStageULDartRun w n ↔ d ∈ (kmswStageDirectedMap w n).ulDarts := by
  have h := kmswStageULDartsFinset_map_mem w n d
  simpa only [kmswStageULDartsFinset, List.mem_toFinset] using h

private theorem kmswWalkClassPath_getLast_ULDartRun {ℓ r n : ℕ}
    (c : KMSWWalkClass ℓ r n) {s t : MapVertex (kmswWalkClassMap c).map}
    {k : ℕ} (P : SimpleDirectedDartPath (kmswWalkClassMap c).map s t k)
    (hboundary : ∀ d, d ∈ P.darts ↔
      d ∈ (kmswWalkClassMap c).map.ulDarts) :
    P.darts.getLast? = some (kmswWalkClassMap c).root := by
  let w := codeExtend c
  let m := n - 1
  have hmem : ∀ d, d ∈ P.darts ↔ d ∈ kmswStageULDartRun w m := by
    intro d
    rw [hboundary d]
    exact (kmswStageULDartRun_mem_map w m d).symm
  have hrunne : kmswStageULDartRun w m ≠ [] := by
    intro hnil
    have hroot := kmswWalkClassMap_root_getLast_ULDartRun c
    change (kmswStageULDartRun w m).getLast? = some _ at hroot
    rw [hnil] at hroot
    simp at hroot
  have hlast := simplePath_getLast_eq_of_chain_mem P
    (kmswStageULDartRun w m) hrunne (kmswStageULDartRun_chain w m) hmem
  rw [hlast]
  exact kmswWalkClassMap_root_getLast_ULDartRun c


/-- A boundary-preserving isomorphism of rooted finite-stage maps, forgetting
only the root-commutation condition. Its ordered left and right boundary paths,
source and sink are included explicitly; this is the data carried by the
corresponding `BipolarBoundaryBaseIso`. Helper toward
not the paper result. -/
structure UnrootedStageIso {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E]
    (M : RootedDirectedMapWithMissing D) (N : RootedDirectedMapWithMissing E) where
  /-- The bijection of darts. -/
  dartEquiv : D ≃ E
  /-- Preserve cyclic order around vertices. -/
  rot_comm : ∀ d, dartEquiv (M.map.rot d) = N.map.rot (dartEquiv d)
  /-- Preserve the opposite dart of each edge. -/
  edgeFlip_comm : ∀ d,
    dartEquiv (M.map.toCombinatorialMap.edgeInv d) =
      N.map.toCombinatorialMap.edgeInv (dartEquiv d)
  /-- Preserve missing-edge status. -/
  missing_iff : ∀ d, M.map.missing d ↔ N.map.missing (dartEquiv d)
  /-- Preserve orientation. -/
  present_iff : ∀ d, ¬ M.map.missing d ↔ ¬ N.map.missing (dartEquiv d)
  /-- Preserve which dart is a tail. -/
  tail_iff : ∀ d, M.map.tail d ↔ N.map.tail (dartEquiv d)
  /-- Preserve the exterior face orbit. -/
  outer_iff : ∀ d, M.map.IsOuter d ↔ N.map.IsOuter (dartEquiv d)
  /-- The source and sink vertices on the first map. -/
  source : MapVertex M.map
  sink : MapVertex M.map
  /-- The source and sink vertices on the second map. -/
  targetSource : MapVertex N.map
  targetSink : MapVertex N.map
  /-- Preserve the source vertex. -/
  source_map : ∀ d, (dartTailVertex M.map d = source) ↔
    (dartTailVertex N.map (dartEquiv d) = targetSource)
  /-- Preserve the sink vertex. -/
  sink_map : ∀ d, (dartTailVertex M.map d = sink) ↔
    (dartTailVertex N.map (dartEquiv d) = targetSink)
  /-- The ordered left boundary path on the first map. -/
  leftLength : ℕ
  leftPath : SimpleDirectedDartPath M.map source sink leftLength
  /-- The ordered right boundary path on the first map. -/
  rightLength : ℕ
  rightPath : SimpleDirectedDartPath M.map source sink rightLength
  /-- The corresponding ordered boundary paths on the second map. -/
  leftPathTarget : SimpleDirectedDartPath N.map targetSource targetSink leftLength
  rightPathTarget : SimpleDirectedDartPath N.map targetSource targetSink rightLength
  /-- The left boundary path enumerates exactly the upper-left boundary darts. -/
  leftPath_boundary : ∀ d, d ∈ leftPath.darts ↔ d ∈ M.map.ulDarts
  /-- The right boundary path, with opposite darts in reverse order, enumerates
  exactly the lower-right boundary darts. -/
  rightPath_boundary : ∀ d,
    d ∈ rightPath.darts.reverse.map M.map.toCombinatorialMap.edgeInv ↔
      d ∈ M.map.lrDarts
  /-- The target paths enumerate the corresponding boundary dart sets. -/
  leftPathTarget_boundary : ∀ d,
    d ∈ leftPathTarget.darts ↔ d ∈ N.map.ulDarts
  rightPathTarget_boundary : ∀ d,
    d ∈ rightPathTarget.darts.reverse.map N.map.toCombinatorialMap.edgeInv ↔
      d ∈ N.map.lrDarts
  /-- The dart equivalence preserves the order of the left boundary path. -/
  leftPath_map : leftPath.darts.map dartEquiv = leftPathTarget.darts
  /-- The dart equivalence preserves the order of the right boundary path. -/
  rightPath_map : rightPath.darts.map dartEquiv = rightPathTarget.darts

namespace UnrootedStageIso

/-- Recover a rooted isomorphism from a boundary-preserving isomorphism when
root commutation has been proved separately. Helper toward injectivity on
the paper result. -/
def toRooted {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E]
    {M : RootedDirectedMapWithMissing D} {N : RootedDirectedMapWithMissing E}
    (I : UnrootedStageIso M N)
    (hroot : I.dartEquiv M.root = N.root) : RootedDirectedMapIso M N where
  dartEquiv := I.dartEquiv
  rot_comm := I.rot_comm
  edgeFlip_comm := I.edgeFlip_comm
  missing_iff := I.missing_iff
  present_iff := I.present_iff
  tail_iff := I.tail_iff
  outer_iff := I.outer_iff
  root_comm := hroot

/-- The boundary path data recovers the active roots of two finite walk
stages from their ordered UL runs. Helper toward injectivity on unrooted
result. -/
theorem root_comm_of_walkClass {ℓ r n : ℕ}
    {c c' : KMSWWalkClass ℓ r n}
    (I : UnrootedStageIso (kmswWalkClassMap c) (kmswWalkClassMap c')) :
    I.dartEquiv (kmswWalkClassMap c).root = (kmswWalkClassMap c').root := by
  have hsource := kmswWalkClassPath_getLast_ULDartRun c I.leftPath
    I.leftPath_boundary
  have htarget := kmswWalkClassPath_getLast_ULDartRun c' I.leftPathTarget
    I.leftPathTarget_boundary
  have hmap := congrArg (Option.map I.dartEquiv) hsource
  rw [← List.getLast?_map, Option.map_some, I.leftPath_map] at hmap
  rw [htarget] at hmap
  exact Option.some.inj hmap.symm

end UnrootedStageIso

/-- The finite walk-class stage map is injective up to unrooted boundary
isomorphism, using the recovered active root and the rooted injectivity helper.
Helper toward injectivity on unrooted classes for `thm-kmsw` -/
theorem kmswWalkClassMap_injective_unrooted {ℓ r n : ℕ}
    (c c' : KMSWWalkClass ℓ r n)
    (I : UnrootedStageIso (kmswWalkClassMap c) (kmswWalkClassMap c')) :
    c = c' := by
  apply kmswWalkClassMap_injective c c'
  exact I.toRooted I.root_comm_of_walkClass

end DirectedDistances.KMSW
