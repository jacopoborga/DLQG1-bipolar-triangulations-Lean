/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.FiniteWalkClassCarrier
public import DirectedDistances.KMSW.KMSWWalkClassRooting
public import DirectedDistances.PlanarMap.KMSWMapIsoClass
import DirectedDistances.PaperProofs.Section3.KMSWBdyOuterFace

/-! # Finite walk classes map to unrooted map classes

injectivity on unrooted classes; not the paper result -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3

 
theorem kmswWalkClassBase_numEdges {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    (kmswWalkClassBase hn c).map.toCombinatorialMap.numEdges = n := by
  have h := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hEdges, _⟩
  rw [kmswWalkClassBase_map]
  change (kmswStageDirectedMap (codeExtend c) (n - 1)).toCombinatorialMap.numEdges = n
  rw [kmswStageDirectedMap_toCombinatorialMap]
  exact hEdges

 
@[expose] noncomputable def kmswWalkClassRep {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) : KMSWMapRep ℓ r n :=
  KMSWMapRep.ofBase (kmswWalkClassBase hn c) (kmswWalkClassBase_numEdges hn c)

 
noncomputable def kmswWalkClassBaseIso_toUnrootedStageIso {ℓ r n : ℕ}
    (hn : 1 ≤ n) (c c' : KMSWWalkClass ℓ r n)
    (I : BipolarBoundaryBaseIso (kmswWalkClassBase hn c)
      (kmswWalkClassBase hn c')) :
    UnrootedStageIso (kmswWalkClassMap c) (kmswWalkClassMap c') := by
  let B := kmswWalkClassBase hn c
  let B' := kmswWalkClassBase hn c'
  rcases B.outerSplit with ⟨_, _, hleft, hright, _, _⟩
  rcases B'.outerSplit with ⟨_, _, hleft', hright', _, _⟩
  refine {
    dartEquiv := I.toEquiv
    rot_comm := I.rot_comm
    edgeFlip_comm := I.edgeInv_comm
    missing_iff := fun d => (I.missing_iff d).symm
    present_iff := ?_
    tail_iff := fun d => (I.tail_iff d).symm
    outer_iff := fun d => (I.outer_iff d).symm
    source := B.source
    sink := B.sink
    targetSource := B'.source
    targetSink := B'.sink
    source_map := I.source_map
    sink_map := I.sink_map
    leftLength := ℓ
    leftPath := B.leftPath
    rightLength := r
    rightPath := B.rightPath
    leftPathTarget := B'.leftPath
    rightPathTarget := B'.rightPath
    leftPath_boundary := hleft
    rightPath_boundary := hright
    leftPathTarget_boundary := hleft'
    rightPathTarget_boundary := hright'
    leftPath_map := I.leftDarts
    rightPath_map := I.rightDarts }
  · intro d
    exact not_congr (I.missing_iff d).symm

 
theorem kmswWalkClassBase_iso_injective {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c c' : KMSWWalkClass ℓ r n)
    (h : Nonempty (BipolarBoundaryBaseIso (kmswWalkClassBase hn c)
      (kmswWalkClassBase hn c'))) : c = c' := by
  rcases h with ⟨I⟩
  exact kmswWalkClassMap_injective_unrooted c c'
    (kmswWalkClassBaseIso_toUnrootedStageIso hn c c' I)

 
theorem kmswWalkClassRep_iso_injective {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c c' : KMSWWalkClass ℓ r n)
    (h : Nonempty (BipolarBoundaryBaseIso (kmswWalkClassRep hn c).B
      (kmswWalkClassRep hn c').B)) : c = c' := by
  apply kmswWalkClassBase_iso_injective hn c c'
  rcases h with ⟨I⟩
  let B := kmswWalkClassBase hn c
  let B' := kmswWalkClassBase hn c'
  let D := StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge
  let D' := StageDart (kmswStage (codeExtend c') (n - 1)).nextEdge
  let e := Fintype.equivFin D
  let e' := Fintype.equivFin D'
  change BipolarBoundaryBaseIso (B.transport e) (B'.transport e') at I
  let J := (B.transportIso e).trans I
  exact ⟨J.trans (B'.transportIso e').symm⟩

 
@[expose] noncomputable def kmswToMapIsoClass {ℓ r n : ℕ} (hn : 1 ≤ n) :
    KMSWWalkClass ℓ r n → KMSWMapIsoClass ℓ r n :=
  fun c => KMSWMapIsoClass.mk (kmswWalkClassRep hn c)

 
theorem kmswToMapIsoClass_injective {ℓ r n : ℕ} (hn : 1 ≤ n) :
    Function.Injective (@kmswToMapIsoClass ℓ r n hn) := by
  intro c c' h
  change KMSWMapIsoClass.mk (kmswWalkClassRep hn c) =
    KMSWMapIsoClass.mk (kmswWalkClassRep hn c') at h
  exact kmswWalkClassRep_iso_injective hn c c'
    ((KMSWMapIsoClass.mk_eq_mk_iff (kmswWalkClassRep hn c)
      (kmswWalkClassRep hn c')).mp h)

end DirectedDistances.KMSW
