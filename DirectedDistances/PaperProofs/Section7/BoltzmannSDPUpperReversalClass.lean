/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperProps2
public import DirectedDistances.PlanarMap.MirrorMap
public import DirectedDistances.PlanarMap.LexLeftmostBaseIso

/-! Supporting lemmas for paper labels `lem-boltzmann-sdp-upper` (see CORRESPONDENCE.md). -/

/-! Reverse all arrows and reflect the plane, on the unrestricted finite base carrier.
No boundary channeling or mutual boundary disjointness is used. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.PlanarMap
open DirectedDistances.KMSW
open Quiver

attribute [local instance 1100] presentDartQuiver

variable {D : Type*} [Fintype D] [DecidableEq D]



@[expose] noncomputable def boltzmannSdpUpper_reverseMap (M : DirectedMapWithMissing D)
    (h : ∀ d, ¬ M.missing d) : DirectedMapWithMissing D :=
  flipOrientation M Set.univ ⟨fun _ _ => Set.mem_univ _, fun d _ => h d⟩



@[expose] noncomputable def boltzmannSdpUpper_reverseMirrorMap
    (M : DirectedMapWithMissing D) (h : ∀ d, ¬ M.missing d) :
    DirectedMapWithMissing D := (boltzmannSdpUpper_reverseMap M h).mirror



@[expose] noncomputable def boltzmannSdpUpper_reverseMirrorVertex
    (M : DirectedMapWithMissing D) (h : ∀ d, ¬ M.missing d) :
    MapVertex M ≃ MapVertex (boltzmannSdpUpper_reverseMirrorMap M h) :=
  CombinatorialMap.vertexQuotientEquiv M.toCombinatorialMap



theorem boltzmannSdpUpper_reverseMap_tail (M : DirectedMapWithMissing D)
    (h : ∀ d, ¬ M.missing d) (d : D) :
    (boltzmannSdpUpper_reverseMap M h).tail d ↔ M.tail (M.edgeInv d) :=
  flipOrientation_tail_of_mem M Set.univ _ d (Set.mem_univ d)



theorem boltzmannSdpUpper_reverseMirrorVertex_tail (M : DirectedMapWithMissing D)
    (h : ∀ d, ¬ M.missing d) (d : D) :
    boltzmannSdpUpper_reverseMirrorVertex M h (dartTailVertex M d) =
      dartTailVertex (boltzmannSdpUpper_reverseMirrorMap M h) d :=
  DirectedMapWithMissing.mirror_dartTailVertex (boltzmannSdpUpper_reverseMap M h) d



theorem boltzmannSdpUpper_reverseMirrorVertex_head (M : DirectedMapWithMissing D)
    (h : ∀ d, ¬ M.missing d) (d : D) :
    boltzmannSdpUpper_reverseMirrorVertex M h (dartHeadVertex M d) =
      dartHeadVertex (boltzmannSdpUpper_reverseMirrorMap M h) d :=
  DirectedMapWithMissing.mirror_dartHeadVertex (boltzmannSdpUpper_reverseMap M h) d



theorem boltzmannSdpUpper_reverseMap_step (M : DirectedMapWithMissing D)
    (h : ∀ d, ¬ M.missing d) (a b : MapVertex M) :
    (boltzmannSdpUpper_reverseMap M h).directedStep a b ↔ M.directedStep b a := by
  constructor
  · rintro ⟨d, hm, ht, ha, hb⟩
    have ht' : M.tail (M.edgeInv d) :=
      (flipOrientation_tail_of_mem M Set.univ _ d (Set.mem_univ d)).mp ht
    refine ⟨M.edgeInv d, h _, ht', hb, ?_⟩
    simpa only [boltzmannSdpUpper_reverseMap, flipOrientation,
      M.toCombinatorialMap.edgeInv_invol] using ha
  · rintro ⟨d, hm, ht, hb, ha⟩
    refine ⟨M.edgeInv d, h _, ?_, ha, ?_⟩
    · apply (flipOrientation_tail_of_mem M Set.univ _ _ (Set.mem_univ _)).mpr
      simpa only [M.toCombinatorialMap.edgeInv_invol] using ht
    · simpa only [boltzmannSdpUpper_reverseMap, flipOrientation,
        M.toCombinatorialMap.edgeInv_invol] using hb



theorem boltzmannSdpUpper_reverseMirror_step (M : DirectedMapWithMissing D)
    (h : ∀ d, ¬ M.missing d) (a b : MapVertex M) :
    (boltzmannSdpUpper_reverseMirrorMap M h).directedStep
      (boltzmannSdpUpper_reverseMirrorVertex M h a)
      (boltzmannSdpUpper_reverseMirrorVertex M h b) ↔ M.directedStep b a := by
  exact (DirectedMapWithMissing.mirror_directedStep_iff
    (boltzmannSdpUpper_reverseMap M h) a b).trans
      (boltzmannSdpUpper_reverseMap_step M h a b)



theorem boltzmannSdpUpper_reverseMirror_acyclic (M : DirectedMapWithMissing D)
    (h : ∀ d, ¬ M.missing d) (ha : M.IsAcyclic) :
    (boltzmannSdpUpper_reverseMirrorMap M h).IsAcyclic := by
  apply (DirectedMapWithMissing.mirror_isAcyclic_iff _).mpr
  intro v hc
  apply ha v
  apply Relation.transGen_swap.mp
  exact Relation.TransGen.lift id
    (fun a b hab => (boltzmannSdpUpper_reverseMap_step M h a b).mp hab) v v hc



@[expose] noncomputable def boltzmannSdpUpper_reverseMirrorPath
    (M : DirectedMapWithMissing D) (h : ∀ d, ¬ M.missing d)
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    SimpleDirectedDartPath (boltzmannSdpUpper_reverseMirrorMap M h)
      (boltzmannSdpUpper_reverseMirrorVertex M h t)
      (boltzmannSdpUpper_reverseMirrorVertex M h s) n where
  darts := P.darts.reverse.map M.edgeInv
  vertices := P.vertices.reverse.map (boltzmannSdpUpper_reverseMirrorVertex M h)
  darts_length := by simp only [List.length_map, List.length_reverse, P.darts_length]
  vertices_length := by
    simp only [List.length_map, List.length_reverse, P.vertices_length]
  vertices_nodup := List.Nodup.map (boltzmannSdpUpper_reverseMirrorVertex M h).injective
    (List.nodup_reverse.mpr P.vertices_nodup)
  start_vertex := by
    simpa only [List.get_eq_getElem, List.getElem_map, List.getElem_reverse,
      P.vertices_length, Nat.add_sub_cancel, Nat.sub_zero] using
      congrArg (boltzmannSdpUpper_reverseMirrorVertex M h) P.end_vertex
  end_vertex := by
    simpa only [List.get_eq_getElem, List.getElem_map, List.getElem_reverse,
      P.vertices_length, Nat.add_sub_cancel, Nat.sub_self] using
      congrArg (boltzmannSdpUpper_reverseMirrorVertex M h) P.start_vertex
  edge_step := by
    intro i
    have hi : i.val < n := by
      simpa only [List.length_map, List.length_reverse, P.darts_length] using i.isLt
    let k : Fin P.darts.length := ⟨n - 1 - i.val, by rw [P.darts_length]; omega⟩
    obtain ⟨hm, ht, ha, hb⟩ := P.edge_step k
    have hget : (P.darts.reverse.map M.edgeInv).get i = M.edgeInv (P.darts.get k) := by
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_reverse,
        P.darts_length, k]
    refine ⟨h _, ?_, ?_, ?_⟩
    · change (boltzmannSdpUpper_reverseMap M h).tail _
      rw [hget]
      apply (flipOrientation_tail_of_mem M Set.univ _ _ (Set.mem_univ _)).mpr
      simpa only [M.toCombinatorialMap.edgeInv_invol] using ht
    · rw [hget]
      rw [← boltzmannSdpUpper_reverseMirrorVertex_tail]
      change _ = boltzmannSdpUpper_reverseMirrorVertex M h
        (dartHeadVertex M (P.darts.get k))
      rw [← hb]
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_reverse]
      congr 2
      simp only [P.vertices_length, k]
      omega
    · rw [hget]
      rw [← boltzmannSdpUpper_reverseMirrorVertex_head]
      change _ = boltzmannSdpUpper_reverseMirrorVertex M h
        (dartTailVertex M (M.edgeInv (M.edgeInv (P.darts.get k))))
      rw [M.toCombinatorialMap.edgeInv_invol, ← ha]
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_reverse]
      congr 2
      simp only [P.vertices_length, k]
      omega



theorem boltzmannSdpUpper_reverseMirrorPath_vertex
    (M : DirectedMapWithMissing D) (h : ∀ d, ¬ M.missing d)
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n)
    (j : Fin (n + 1)) :
    (boltzmannSdpUpper_reverseMirrorPath M h P).vertices.get
      ⟨j.val, by rw [SimpleDirectedDartPath.vertices_length]; exact j.isLt⟩ =
      boltzmannSdpUpper_reverseMirrorVertex M h
        (P.vertices.get ⟨j.rev.val, by rw [P.vertices_length]; exact j.rev.isLt⟩) := by
  have hidx : P.vertices.length - 1 - j.val = j.rev.val := by
    rw [P.vertices_length, Fin.val_rev]
    omega
  change (P.vertices.reverse.map (boltzmannSdpUpper_reverseMirrorVertex M h))[j.val]'(by
    simpa only [List.length_map, List.length_reverse, P.vertices_length] using j.isLt) =
    boltzmannSdpUpper_reverseMirrorVertex M h (P.vertices[j.rev.val]'(by
      rw [P.vertices_length]
      exact j.rev.isLt))
  simp only [List.getElem_map, List.getElem_reverse, hidx]



theorem boltzmannSdpUpper_reverseMap_outerSplit (M : DirectedMapWithMissing D)
    (h : ∀ d, ¬ M.missing d) (W : NonemptyWord D) (L R : List D)
    (hs : FourArcsWitness M W L [] (R.reverse.map M.edgeInv) []) :
    FourArcsWitness (boltzmannSdpUpper_reverseMap M h) W
      (R.reverse.map M.edgeInv) [] L [] := by
  obtain ⟨hc, hr, hul, hlr, _, _⟩ := hs
  refine ⟨hc, ?_, ?_, ?_, ?_, ?_⟩
  · have hr' : W.letters ~r L ++ (R.reverse.map M.edgeInv) := by
      simpa only [List.append_nil] using hr
    simpa only [List.append_nil] using hr'.trans
      (List.isRotated_append (l := L) (l' := R.reverse.map M.edgeInv))
  · intro d
    rw [hlr d]
    change (¬ M.missing d ∧ ¬ M.tail d ∧ M.IsOuter d) ↔
      (¬ M.missing d ∧ (boltzmannSdpUpper_reverseMap M h).tail d ∧ M.IsOuter d)
    rw [boltzmannSdpUpper_reverseMap_tail]
    have ht := M.tail_iff (M.edgeInv d) (h _)
    simpa only [M.toCombinatorialMap.edgeInv_invol] using
      and_congr_right (fun _ => and_congr_left (fun _ => ht.symm))
  · intro d
    rw [hul d]
    change (¬ M.missing d ∧ M.tail d ∧ M.IsOuter d) ↔
      (¬ M.missing d ∧ ¬ (boltzmannSdpUpper_reverseMap M h).tail d ∧ M.IsOuter d)
    rw [boltzmannSdpUpper_reverseMap_tail]
    exact and_congr_right (fun _ => and_congr_left (fun _ => M.tail_iff d (h d)))
  · intro d hd
    cases hd
  · intro d hd
    cases hd



theorem boltzmannSdpUpper_reverseMirror_noMissing (M : DirectedMapWithMissing D)
    (h : ∀ d, ¬ M.missing d) :
    ∀ d, ¬ (boltzmannSdpUpper_reverseMirrorMap M h).missing d := h



@[expose] noncomputable def boltzmannSdpUpper_reverseMirrorBase {L r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D L r) :
    BipolarTriangulationWithBoundaryBase D L r where
  map := boltzmannSdpUpper_reverseMirrorMap B.map B.noMissingDarts
  noMissingDarts := boltzmannSdpUpper_reverseMirror_noMissing B.map B.noMissingDarts
  planar := (CombinatorialMap.isPlanar_mirror_iff _).mpr B.planar
  innerFacesDegreeThree := DirectedMapWithMissing.mirror_innerFacesDegreeThree
    (boltzmannSdpUpper_reverseMap B.map B.noMissingDarts) B.innerFacesDegreeThree
  acyclic := boltzmannSdpUpper_reverseMirror_acyclic B.map B.noMissingDarts B.acyclic
  source := boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts B.sink
  sink := boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts B.source
  isSource := by
    rintro ⟨u, hu⟩
    obtain ⟨v, rfl⟩ :=
      (boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts).surjective u
    exact B.isSink ⟨v, (boltzmannSdpUpper_reverseMirror_step _ _ _ _).mp hu⟩
  source_unique := by
    intro u hu
    obtain ⟨v, rfl⟩ :=
      (boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts).surjective u
    apply congrArg (boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts)
    apply B.sink_unique v
    rintro ⟨w, hw⟩
    exact hu ⟨boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts w,
      (boltzmannSdpUpper_reverseMirror_step _ _ _ _).mpr hw⟩
  isSink := by
    rintro ⟨u, hu⟩
    obtain ⟨v, rfl⟩ :=
      (boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts).surjective u
    exact B.isSource ⟨v, (boltzmannSdpUpper_reverseMirror_step _ _ _ _).mp hu⟩
  sink_unique := by
    intro u hu
    obtain ⟨v, rfl⟩ :=
      (boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts).surjective u
    apply congrArg (boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts)
    apply B.source_unique v
    rintro ⟨w, hw⟩
    exact hu ⟨boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts w,
      (boltzmannSdpUpper_reverseMirror_step _ _ _ _).mpr hw⟩
  left_length_pos := B.left_length_pos
  right_length_pos := B.right_length_pos
  outerWord := DirectedMapWithMissing.mirrorOuterWord
    (boltzmannSdpUpper_reverseMap B.map B.noMissingDarts) B.outerWord
  leftPath := boltzmannSdpUpper_reverseMirrorPath B.map B.noMissingDarts B.leftPath
  rightPath := boltzmannSdpUpper_reverseMirrorPath B.map B.noMissingDarts B.rightPath
  outerSplit := by
    have hs := boltzmannSdpUpper_reverseMap_outerSplit B.map B.noMissingDarts
      B.outerWord B.leftPath.darts B.rightPath.darts B.outerSplit
    have hm := DirectedMapWithMissing.mirror_fourArcsWitness
      (boltzmannSdpUpper_reverseMap B.map B.noMissingDarts) B.outerWord
      (B.rightPath.darts.reverse.map B.map.edgeInv)
      (B.leftPath.darts.reverse.map B.map.edgeInv) (by
        simpa only [boltzmannSdpUpper_reverseMap, flipOrientation, List.map_reverse,
          List.reverse_reverse, List.map_map,
          Function.comp_def, B.map.toCombinatorialMap.edgeInv_invol,
          List.map_id'] using hs)
    simpa only [boltzmannSdpUpper_reverseMirrorMap, boltzmannSdpUpper_reverseMirrorPath,
      boltzmannSdpUpper_reverseMap, flipOrientation, DirectedMapWithMissing.mirror,
      CombinatorialMap.mirror] using hm



theorem boltzmannSdpUpper_reverseMirrorVertex_eq_iff
    (M : DirectedMapWithMissing D) (h : ∀ d, ¬ M.missing d)
    (d : D) (v : MapVertex M) :
    dartTailVertex (boltzmannSdpUpper_reverseMirrorMap M h) d =
      boltzmannSdpUpper_reverseMirrorVertex M h v ↔ dartTailVertex M d = v := by
  rw [← boltzmannSdpUpper_reverseMirrorVertex_tail]
  exact (boltzmannSdpUpper_reverseMirrorVertex M h).injective.eq_iff



@[expose] noncomputable def boltzmannSdpUpper_reverseMirrorBaseIso
    {D' : Type*} [Fintype D'] [DecidableEq D'] {L r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D L r}
    {B' : BipolarTriangulationWithBoundaryBase D' L r}
    (I : BipolarBoundaryBaseIso B B') :
    BipolarBoundaryBaseIso (boltzmannSdpUpper_reverseMirrorBase B)
      (boltzmannSdpUpper_reverseMirrorBase B') where
  toEquiv := I.toEquiv
  rot_comm := by
    intro d
    change I.toEquiv (B.map.rot.symm d) = B'.map.rot.symm (I.toEquiv d)
    apply B'.map.rot.injective
    rw [← I.rot_comm]
    simp only [Equiv.apply_symm_apply]
  edgeInv_comm := I.edgeInv_comm
  missing_iff := I.missing_iff
  tail_iff := by
    intro d
    change (boltzmannSdpUpper_reverseMap B'.map B'.noMissingDarts).tail _ ↔
      (boltzmannSdpUpper_reverseMap B.map B.noMissingDarts).tail _
    rw [boltzmannSdpUpper_reverseMap_tail, boltzmannSdpUpper_reverseMap_tail,
      ← I.edgeInv_comm]
    exact I.tail_iff _
  outer_iff := by
    intro d
    change (boltzmannSdpUpper_reverseMap B'.map B'.noMissingDarts).mirror.IsOuter _ ↔
      (boltzmannSdpUpper_reverseMap B.map B.noMissingDarts).mirror.IsOuter _
    rw [DirectedMapWithMissing.mirror_isOuter_iff,
      DirectedMapWithMissing.mirror_isOuter_iff]
    change B'.map.IsOuter (B'.map.edgeInv (I.toEquiv d)) ↔
      B.map.IsOuter (B.map.edgeInv d)
    rw [← I.edgeInv_comm]
    exact I.outer_iff _
  source_map := by
    intro d
    change dartTailVertex (boltzmannSdpUpper_reverseMirrorMap B.map B.noMissingDarts) d =
      boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts B.sink ↔
      dartTailVertex (boltzmannSdpUpper_reverseMirrorMap B'.map B'.noMissingDarts)
        (I.toEquiv d) =
      boltzmannSdpUpper_reverseMirrorVertex B'.map B'.noMissingDarts B'.sink
    rw [boltzmannSdpUpper_reverseMirrorVertex_eq_iff,
      boltzmannSdpUpper_reverseMirrorVertex_eq_iff]
    exact I.sink_map d
  sink_map := by
    intro d
    change dartTailVertex (boltzmannSdpUpper_reverseMirrorMap B.map B.noMissingDarts) d =
      boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts B.source ↔
      dartTailVertex (boltzmannSdpUpper_reverseMirrorMap B'.map B'.noMissingDarts)
        (I.toEquiv d) =
      boltzmannSdpUpper_reverseMirrorVertex B'.map B'.noMissingDarts B'.source
    rw [boltzmannSdpUpper_reverseMirrorVertex_eq_iff,
      boltzmannSdpUpper_reverseMirrorVertex_eq_iff]
    exact I.source_map d
  leftDarts := by
    change (B.leftPath.darts.reverse.map B.map.edgeInv).map I.toEquiv =
      B'.leftPath.darts.reverse.map B'.map.edgeInv
    rw [← I.leftDarts]
    simp only [List.map_reverse, List.map_map, Function.comp_def, I.edgeInv_comm]
  rightDarts := by
    change (B.rightPath.darts.reverse.map B.map.edgeInv).map I.toEquiv =
      B'.rightPath.darts.reverse.map B'.map.edgeInv
    rw [← I.rightDarts]
    simp only [List.map_reverse, List.map_map, Function.comp_def, I.edgeInv_comm]



@[expose] noncomputable def boltzmannSdpUpper_reverseMirrorBaseTwiceIso {L r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D L r) :
    BipolarBoundaryBaseIso
      (boltzmannSdpUpper_reverseMirrorBase (boltzmannSdpUpper_reverseMirrorBase B)) B where
  toEquiv := Equiv.refl D
  rot_comm := by intro d; rfl
  edgeInv_comm := by intro d; rfl
  missing_iff := by intro d; rfl
  tail_iff := by
    intro d
    change B.map.tail d ↔
      (boltzmannSdpUpper_reverseMap
        (boltzmannSdpUpper_reverseMirrorMap B.map B.noMissingDarts)
        (boltzmannSdpUpper_reverseMirror_noMissing B.map B.noMissingDarts)).tail d
    rw [boltzmannSdpUpper_reverseMap_tail]
    change B.map.tail d ↔
      (boltzmannSdpUpper_reverseMap B.map B.noMissingDarts).tail (B.map.edgeInv d)
    rw [boltzmannSdpUpper_reverseMap_tail, B.map.toCombinatorialMap.edgeInv_invol]
  outer_iff := by
    intro d
    change B.map.IsOuter d ↔
      (boltzmannSdpUpper_reverseMap
        (boltzmannSdpUpper_reverseMirrorMap B.map B.noMissingDarts)
        B.noMissingDarts).mirror.IsOuter d
    rw [DirectedMapWithMissing.mirror_isOuter_iff]
    change B.map.IsOuter d ↔
      (boltzmannSdpUpper_reverseMap B.map B.noMissingDarts).mirror.IsOuter
        (B.map.edgeInv d)
    rw [DirectedMapWithMissing.mirror_isOuter_iff]
    change B.map.IsOuter d ↔ B.map.IsOuter (B.map.edgeInv (B.map.edgeInv d))
    rw [B.map.toCombinatorialMap.edgeInv_invol]
  source_map := by
    intro d
    exact (boltzmannSdpUpper_reverseMirrorVertex_eq_iff
      (boltzmannSdpUpper_reverseMirrorMap B.map B.noMissingDarts)
      (boltzmannSdpUpper_reverseMirror_noMissing B.map B.noMissingDarts) d
      (boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts B.source)).trans
        (boltzmannSdpUpper_reverseMirrorVertex_eq_iff B.map B.noMissingDarts d B.source)
  sink_map := by
    intro d
    exact (boltzmannSdpUpper_reverseMirrorVertex_eq_iff
      (boltzmannSdpUpper_reverseMirrorMap B.map B.noMissingDarts)
      (boltzmannSdpUpper_reverseMirror_noMissing B.map B.noMissingDarts) d
      (boltzmannSdpUpper_reverseMirrorVertex B.map B.noMissingDarts B.sink)).trans
        (boltzmannSdpUpper_reverseMirrorVertex_eq_iff B.map B.noMissingDarts d B.sink)
  leftDarts := by
    change ((B.leftPath.darts.reverse.map B.map.edgeInv).reverse.map B.map.edgeInv).map
      (Equiv.refl D) = B.leftPath.darts
    simp only [List.map_reverse, List.reverse_reverse, List.map_map, Function.comp_def,
      B.map.toCombinatorialMap.edgeInv_invol, List.map_id']
    change List.map id _ = _
    exact List.map_id _
  rightDarts := by
    change ((B.rightPath.darts.reverse.map B.map.edgeInv).reverse.map B.map.edgeInv).map
      (Equiv.refl D) = B.rightPath.darts
    simp only [List.map_reverse, List.reverse_reverse, List.map_map, Function.comp_def,
      B.map.toCombinatorialMap.edgeInv_invol, List.map_id']
    change List.map id _ = _
    exact List.map_id _



@[expose] noncomputable def boltzmannSdpUpper_reverseMirrorRep {L r N : ℕ}
    (R : KMSWMapRep L r N) : KMSWMapRep L r N where
  dartCount := R.dartCount
  B := boltzmannSdpUpper_reverseMirrorBase R.B
  edges := (CombinatorialMap.numEdges_mirror _).trans R.edges



@[expose] noncomputable def boltzmannSdpUpper_reverseMirrorClass {L r N : ℕ}
    (c : KMSWMapIsoClass L r N) : KMSWMapIsoClass L r N :=
  Quotient.map boltzmannSdpUpper_reverseMirrorRep (by
    intro R S h
    obtain ⟨I⟩ := h
    exact ⟨boltzmannSdpUpper_reverseMirrorBaseIso I⟩) c



theorem boltzmannSdpUpper_reverseMirrorClass_involutive {L r N : ℕ} :
    Function.Involutive (boltzmannSdpUpper_reverseMirrorClass (L := L) (r := r) (N := N)) := by
  intro c
  induction c using Quotient.inductionOn with
  | h R =>
    exact Quotient.sound ⟨boltzmannSdpUpper_reverseMirrorBaseTwiceIso R.B⟩



@[expose] noncomputable def boltzmannSdpUpper_reverseMirrorClassEquiv (L r N : ℕ) :
    KMSWMapIsoClass L r N ≃ KMSWMapIsoClass L r N where
  toFun := boltzmannSdpUpper_reverseMirrorClass
  invFun := boltzmannSdpUpper_reverseMirrorClass
  left_inv := boltzmannSdpUpper_reverseMirrorClass_involutive
  right_inv := boltzmannSdpUpper_reverseMirrorClass_involutive



theorem boltzmannSdpUpper_iso_step
    {D' : Type*} [Fintype D'] [DecidableEq D'] {L r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D L r}
    {B' : BipolarTriangulationWithBoundaryBase D' L r}
    (I : BipolarBoundaryBaseIso B B') {a b : MapVertex B.map}
    (hab : B.map.directedStep a b) :
    B'.map.directedStep (I.vertexEquiv a) (I.vertexEquiv b) := by
  obtain ⟨d, hm, ht, ha, hb⟩ := hab
  refine ⟨I.toEquiv d, ?_, (I.tail_iff d).mpr ht, ?_, ?_⟩
  · exact fun h => hm ((I.missing_iff d).mp h)
  · exact (I.vertexEquiv_dartTailVertex d).symm.trans (congrArg I.vertexEquiv ha)
  · exact (I.vertexEquiv_dartHeadVertex d).symm.trans (congrArg I.vertexEquiv hb)



theorem boltzmannSdpUpper_iso_leftVertex
    {D' : Type*} [Fintype D'] [DecidableEq D'] {L r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D L r}
    {B' : BipolarTriangulationWithBoundaryBase D' L r}
    (I : BipolarBoundaryBaseIso B B') (j : Fin (L + 1)) :
    I.vertexEquiv (B.leftPath.vertices.get ⟨j.val, by
      rw [B.leftPath.vertices_length]
      exact j.isLt⟩) =
    B'.leftPath.vertices.get ⟨j.val, by
      rw [B'.leftPath.vertices_length]
      exact j.isLt⟩ := by
  have hp : I.mapPath B.leftPath = B'.leftPath :=
    SimpleDirectedDartPath.eq_of_darts_eq I.leftDarts
  have hv : B.leftPath.vertices.map I.vertexEquiv = B'.leftPath.vertices :=
    congrArg SimpleDirectedDartPath.vertices hp
  have hget {xs ys : List (MapVertex B'.map)} (hxy : xs = ys) (k : ℕ)
      (hx : k < xs.length) (hy : k < ys.length) :
      xs.get ⟨k, hx⟩ = ys.get ⟨k, hy⟩ := by cases hxy; rfl
  exact (by
    simpa only [List.get_eq_getElem, List.getElem_map] using
      hget hv j.val (by
        simpa only [List.length_map, B.leftPath.vertices_length] using j.isLt)
        (by rw [B'.leftPath.vertices_length]; exact j.isLt))



theorem boltzmannSdpUpper_reverseMirrorClass_out {L r N : ℕ}
    (c : KMSWMapIsoClass L r N) :
    boltzmannSdpUpper_reverseMirrorClass c =
      KMSWMapIsoClass.mk (boltzmannSdpUpper_reverseMirrorRep c.out) := by
  calc
    _ = boltzmannSdpUpper_reverseMirrorClass (KMSWMapIsoClass.mk c.out) :=
      congrArg boltzmannSdpUpper_reverseMirrorClass (Quotient.out_eq c).symm
    _ = _ := rfl



@[expose] noncomputable def boltzmannSdpUpper_reverseMirrorOutIso {L r N : ℕ}
    (c : KMSWMapIsoClass L r N) :
    BipolarBoundaryBaseIso (boltzmannSdpUpper_reverseMirrorClass c).out.B
      (boltzmannSdpUpper_reverseMirrorRep c.out).B :=
  Classical.choice ((KMSWMapIsoClass.mk_eq_mk_iff _ _).mp
    ((Quotient.out_eq _).trans (boltzmannSdpUpper_reverseMirrorClass_out c)))



theorem boltzmannSdpUpper_reverseMirrorClass_geometry {L r N : ℕ}
    (c : KMSWMapIsoClass L r N) :
    ∃ f : MapVertex (boltzmannSdpUpper_reverseMirrorClass c).out.B.map →
      MapVertex c.out.B.map,
      (∀ a b, (a ⟶ b) → Nonempty (f b ⟶ f a)) ∧
      f (boltzmannSdpUpper_reverseMirrorClass c).out.B.source = c.out.B.sink ∧
      ∀ j : Fin (L + 1),
        f ((boltzmannSdpUpper_reverseMirrorClass c).out.B.leftPath.vertices.get
          ⟨j.val, by rw [SimpleDirectedDartPath.vertices_length]; exact j.isLt⟩) =
        c.out.B.leftPath.vertices.get
          ⟨j.rev.val, by rw [SimpleDirectedDartPath.vertices_length]; exact j.rev.isLt⟩ := by
  let R : KMSWMapRep L r N := c.out
  let S : KMSWMapRep L r N := (boltzmannSdpUpper_reverseMirrorClass c).out
  let I : BipolarBoundaryBaseIso S.B (boltzmannSdpUpper_reverseMirrorRep R).B :=
    boltzmannSdpUpper_reverseMirrorOutIso c
  let e : MapVertex R.B.map ≃ MapVertex (boltzmannSdpUpper_reverseMirrorRep R).B.map :=
    boltzmannSdpUpper_reverseMirrorVertex R.B.map R.B.noMissingDarts
  refine ⟨fun v => e.symm (I.vertexEquiv v), ?_, ?_, ?_⟩
  · intro a b edge
    have hs := boltzmannSdpUpper_iso_step I
      (show (boltzmannSdpUpper_reverseMirrorClass c).out.B.map.directedStep a b from
        ⟨edge.val, edge.property⟩)
    have hs' : (boltzmannSdpUpper_reverseMirrorRep R).B.map.directedStep
        (e (e.symm (I.vertexEquiv a))) (e (e.symm (I.vertexEquiv b))) := by
      erw [e.apply_symm_apply, e.apply_symm_apply]
      exact hs
    have hr := (boltzmannSdpUpper_reverseMirror_step R.B.map R.B.noMissingDarts
      (e.symm (I.vertexEquiv a)) (e.symm (I.vertexEquiv b))).mp hs'
    obtain ⟨d, hd⟩ := hr
    exact ⟨⟨d, hd⟩⟩
  · change e.symm (I.vertexEquiv _) = _
    rw [I.vertexEquiv_source]
    exact e.symm_apply_apply _
  · intro j
    have hI := boltzmannSdpUpper_iso_leftVertex I j
    have hP := boltzmannSdpUpper_reverseMirrorPath_vertex
      R.B.map R.B.noMissingDarts R.B.leftPath j
    exact (congrArg e.symm (hI.trans hP)).trans (e.symm_apply_apply _)



@[expose] noncomputable def boltzmannSdpUpper_reverseMirrorMarked (r : ℕ) :
    RightVertexMarkedBoltzmannSpace r ≃ RightVertexMarkedBoltzmannSpace r where
  toFun q := ⟨⟨q.1.1, q.1.2.1, boltzmannSdpUpper_reverseMirrorClass q.1.2.2⟩, q.2.rev⟩
  invFun q := ⟨⟨q.1.1, q.1.2.1, boltzmannSdpUpper_reverseMirrorClass q.1.2.2⟩, q.2.rev⟩
  left_inv q := by
    rcases q with ⟨⟨L, N, c⟩, m⟩
    change (⟨⟨L, N, boltzmannSdpUpper_reverseMirrorClass
      (boltzmannSdpUpper_reverseMirrorClass c)⟩, m.rev.rev⟩ :
      RightVertexMarkedBoltzmannSpace r) = _
    rw [boltzmannSdpUpper_reverseMirrorClass_involutive c, Fin.rev_rev]
  right_inv q := by
    rcases q with ⟨⟨L, N, c⟩, m⟩
    change (⟨⟨L, N, boltzmannSdpUpper_reverseMirrorClass
      (boltzmannSdpUpper_reverseMirrorClass c)⟩, m.rev.rev⟩ :
      RightVertexMarkedBoltzmannSpace r) = _
    rw [boltzmannSdpUpper_reverseMirrorClass_involutive c, Fin.rev_rev]



theorem boltzmannSdpUpper_reversalClassGeometry_holds :
    boltzmannSdpUpper_reversalClassGeometry := by
  intro r _hr
  refine ⟨boltzmannSdpUpper_reverseMirrorMarked r, fun _ => rfl, ?_⟩
  rintro ⟨⟨L, N, c⟩, m⟩
  obtain ⟨f, hedge, hsource, hleft⟩ := boltzmannSdpUpper_reverseMirrorClass_geometry c
  refine ⟨f, hedge, hsource, ?_⟩
  intro j hj
  refine ⟨j.rev, ?_, hleft j⟩
  change m.rev ≤ j at hj
  change j.rev ≤ m
  have hm := Fin.rev_le_rev.mpr hj
  rw [Fin.rev_rev] at hm
  exact hm

end DirectedDistances.PaperProofs.Section7
