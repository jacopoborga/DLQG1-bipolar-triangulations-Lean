/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarIncomingInterval
public import DirectedDistances.PlanarMap.FiniteBipolarSwitchCount

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

private def outerBoundaryDarts (B : BipolarTriangulationWithBoundaryBase D ℓ r) : List D :=
  B.leftPath.darts ++ B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv

private theorem outerBoundaryDarts_nodup
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (outerBoundaryDarts B).Nodup := by
  simpa [outerBoundaryDarts] using
    B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup

private theorem outerBoundaryDarts_length
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (outerBoundaryDarts B).length = ℓ + r := by
  simp [outerBoundaryDarts, B.leftPath.darts_length,
    B.rightPath.darts_length]

private theorem outerBoundaryDarts_mem_isOuter
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : d ∈ outerBoundaryDarts B) : B.map.IsOuter d := by
  have hword : d ∈ B.outerWord.letters :=
    (B.outerSplit.2.1.perm.mem_iff).mpr (by simpa [outerBoundaryDarts] using hd)
  exact (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mp hword

private theorem faceSucc_eq_outerBoundaryDarts_formPerm
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : B.map.IsOuter d) :
    B.map.toCombinatorialMap.faceSucc d = (outerBoundaryDarts B).formPerm d := by
  have hword : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr hd
  calc
    B.map.toCombinatorialMap.faceSucc d = B.outerWord.letters.formPerm d :=
      B.outerSplit.1.2.2 d hword
    _ = (outerBoundaryDarts B).formPerm d := by
      simpa [outerBoundaryDarts] using
        congrArg (fun p : Equiv.Perm D => p d)
          (List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1)

private theorem outerBoundaryDarts_tail_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ)
    (hi : i < (outerBoundaryDarts B).length) :
    B.map.tail ((outerBoundaryDarts B)[i]'hi) ↔ i < ℓ := by
  have hi' : i <
      (B.leftPath.darts ++
        B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).length := by
    simpa [outerBoundaryDarts] using hi
  change B.map.tail
      ((B.leftPath.darts ++
        B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[i]'hi') ↔ i < ℓ
  by_cases hleft : i < ℓ
  · have hleft' : i < B.leftPath.darts.length := by
      simpa [B.leftPath.darts_length] using hleft
    rw [List.getElem_append_left hleft']
    have hUL : (B.leftPath.darts[i]) ∈ B.map.ulDarts :=
      (B.outerSplit.2.2.1 _).mp (List.getElem_mem (show i < B.leftPath.darts.length by
        simpa [B.leftPath.darts_length] using hleft))
    constructor
    · intro _
      exact hleft
    · intro _
      exact hUL.2.1
  · have hir : ℓ ≤ i := Nat.le_of_not_gt hleft
    have hRlen :
        (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).length = r := by
      simp [B.rightPath.darts_length]
    have hi'' : i < ℓ + r := by
      rw [← outerBoundaryDarts_length B]
      exact hi
    have hir' : i - ℓ <
        (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).length := by
      rw [hRlen]
      omega
    have hLR :
        (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[i - ℓ]
            ∈ B.map.lrDarts :=
      (B.outerSplit.2.2.2.1 _).mp (List.getElem_mem hir')
    have hnot : ¬ B.map.tail
        (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[i - ℓ] := by
      simpa [DirectedMapWithMissing.lrDarts] using hLR.2.1
    have hnot' : ¬ B.map.tail
        ((B.leftPath.darts ++
          B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[i]'hi') := by
      rw [List.getElem_append_right (as := B.leftPath.darts)
        (bs := B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)
        (by simpa [B.leftPath.darts_length] using hir)]
      simpa [B.leftPath.darts_length] using hnot
    constructor
    · intro htail
      exact (hnot' htail).elim
    · intro hlt
      exact (hleft hlt).elim

private theorem outerBoundaryDarts_faceSwitch_iff_index
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ)
    (hi : i < (outerBoundaryDarts B).length) :
    faceSwitchCorner B ((outerBoundaryDarts B)[i]'hi) ↔
      i + 1 = ℓ ∨ i + 1 = ℓ + r := by
  have hlen := outerBoundaryDarts_length B
  have hℓpos : 0 < ℓ := B.left_length_pos
  have hrpos : 0 < r := B.right_length_pos
  have hNpos : 0 < ℓ + r := by omega
  have hmod : (i + 1) % (ℓ + r) < (outerBoundaryDarts B).length := by
    rw [hlen]
    exact Nat.mod_lt _ hNpos
  have hdOuter : B.map.IsOuter ((outerBoundaryDarts B)[i]'hi) :=
    outerBoundaryDarts_mem_isOuter B (List.getElem_mem hi)
  have hsucc : B.map.toCombinatorialMap.faceSucc ((outerBoundaryDarts B)[i]'hi) =
      (outerBoundaryDarts B)[(i + 1) % (ℓ + r)]'hmod := by
    rw [faceSucc_eq_outerBoundaryDarts_formPerm B hdOuter]
    simpa only [hlen] using List.formPerm_apply_getElem (outerBoundaryDarts B)
      (outerBoundaryDarts_nodup B) i hi
  have hcurrent := outerBoundaryDarts_tail_iff B i hi
  have hnext : B.map.tail (B.map.toCombinatorialMap.faceSucc
      ((outerBoundaryDarts B)[i]'hi)) ↔ (i + 1) % (ℓ + r) < ℓ := by
    rw [hsucc]
    exact outerBoundaryDarts_tail_iff B ((i + 1) % (ℓ + r))
      hmod
  unfold faceSwitchCorner
  rw [hcurrent, hnext]
  by_cases hwrap : i + 1 = ℓ + r
  · rw [hwrap, Nat.mod_self]
    omega
  · have hnextlt : i + 1 < ℓ + r := by omega
    rw [Nat.mod_eq_of_lt hnextlt]
    omega

/-- The outer-face corners that change face-side orientation are exactly the
source and sink junctions of the two boundary arcs. Helper toward
343–369`). -/
theorem outerFaceSwitch_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Nat.card {d : D // B.map.IsOuter d ∧ faceSwitchCorner B d} = 2 := by
  classical
  have hlen := outerBoundaryDarts_length B
  have hℓpos : 0 < ℓ := B.left_length_pos
  have hrpos : 0 < r := B.right_length_pos
  let a : D := (outerBoundaryDarts B)[ℓ - 1]'(by rw [hlen]; omega)
  let b : D := (outerBoundaryDarts B)[ℓ + r - 1]'(by rw [hlen]; omega)
  have haIdx : ℓ - 1 < (outerBoundaryDarts B).length := by
    rw [hlen]
    omega
  have hbIdx : ℓ + r - 1 < (outerBoundaryDarts B).length := by
    rw [hlen]
    omega
  have haOuter : B.map.IsOuter a := by
    dsimp [a]
    exact outerBoundaryDarts_mem_isOuter B (List.getElem_mem haIdx)
  have hbOuter : B.map.IsOuter b := by
    dsimp [b]
    exact outerBoundaryDarts_mem_isOuter B (List.getElem_mem hbIdx)
  have haSwitch : faceSwitchCorner B a := by
    dsimp [a]
    apply (outerBoundaryDarts_faceSwitch_iff_index B (ℓ - 1) haIdx).2
    left
    omega
  have hbSwitch : faceSwitchCorner B b := by
    dsimp [b]
    apply (outerBoundaryDarts_faceSwitch_iff_index B (ℓ + r - 1) hbIdx).2
    right
    omega
  have haTail : B.map.tail a := by
    dsimp [a]
    exact (outerBoundaryDarts_tail_iff B (ℓ - 1) haIdx).2 (by omega)
  have hbNotTail : ¬ B.map.tail b := by
    dsimp [b]
    intro htail
    have hidx := (outerBoundaryDarts_tail_iff B (ℓ + r - 1) hbIdx).1 htail
    omega
  have hab : a ≠ b := by
    intro h
    apply hbNotTail
    rw [← h]
    exact haTail
  have hfilter :
      Finset.univ.filter (fun d : D => B.map.IsOuter d ∧ faceSwitchCorner B d) =
        {a, b} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hdOuter, hdSwitch⟩
      have hdWord : d ∈ outerBoundaryDarts B := by
        have houterWord := (mem_iff_isOuter B.map B.outerWord
          B.outerSplit.1 d).mpr hdOuter
        simpa [outerBoundaryDarts] using B.outerSplit.2.1.perm.mem_iff.mp houterWord
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hdWord
      rcases (outerBoundaryDarts_faceSwitch_iff_index B i hi).1 hdSwitch with
        hleft | hright
      · left
        change (outerBoundaryDarts B)[i] = (outerBoundaryDarts B)[ℓ - 1]
        exact (outerBoundaryDarts_nodup B).getElem_inj_iff.mpr (by omega)
      · right
        change (outerBoundaryDarts B)[i] = (outerBoundaryDarts B)[ℓ + r - 1]
        exact (outerBoundaryDarts_nodup B).getElem_inj_iff.mpr (by omega)
    · intro hd
      rcases hd with rfl | rfl
      · exact ⟨haOuter, haSwitch⟩
      · exact ⟨hbOuter, hbSwitch⟩
  have hcard : Nat.card {d : D // B.map.IsOuter d ∧ faceSwitchCorner B d} =
      (Finset.univ.filter
        (fun d : D => B.map.IsOuter d ∧ faceSwitchCorner B d)).card :=
    Nat.subtype_card _ (by intro d; simp)
  rw [hcard, hfilter]
  simp [hab]

/-- The number of vertex-switch corners on the external face is its `ℓ + r`
boundary darts minus the two pole junctions. Helper toward `lem-lr-ind`; not -/
theorem outerVertexSwitch_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Nat.card {d : D // B.map.IsOuter d ∧ vertexSwitchCorner B d} = ℓ + r - 2 := by
  classical
  let outerDarts : Finset D := Finset.univ.filter fun d => B.map.IsOuter d
  let vertexDarts : Finset D := outerDarts.filter fun d => vertexSwitchCorner B d
  let faceDarts : Finset D := outerDarts.filter fun d => faceSwitchCorner B d
  have houterCard : Nat.card {d : D // B.map.IsOuter d} = outerDarts.card := by
    exact Nat.subtype_card _ (by intro d; simp [outerDarts])
  have hvertexCard :
      Nat.card {d : D // B.map.IsOuter d ∧ vertexSwitchCorner B d} =
        vertexDarts.card := by
    calc
      Nat.card {d : D // B.map.IsOuter d ∧ vertexSwitchCorner B d} =
          (Finset.univ.filter
            (fun d : D => B.map.IsOuter d ∧ vertexSwitchCorner B d)).card :=
        Nat.subtype_card _ (by intro d; simp)
      _ = vertexDarts.card := by
        simp only [vertexDarts, outerDarts, Finset.filter_filter]
  have hfaceCard :
      Nat.card {d : D // B.map.IsOuter d ∧ faceSwitchCorner B d} = faceDarts.card := by
    calc
      Nat.card {d : D // B.map.IsOuter d ∧ faceSwitchCorner B d} =
          (Finset.univ.filter
            (fun d : D => B.map.IsOuter d ∧ faceSwitchCorner B d)).card :=
        Nat.subtype_card _ (by intro d; simp)
      _ = faceDarts.card := by
        simp only [faceDarts, outerDarts, Finset.filter_filter]
  have hfaceComplement :
      outerDarts.filter (fun d => ¬ vertexSwitchCorner B d) = faceDarts := by
    change outerDarts.filter (fun d => ¬ vertexSwitchCorner B d) =
      outerDarts.filter (fun d => faceSwitchCorner B d)
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ho, hnot⟩
      exact ⟨ho, (corner_switch_partition B d).2 hnot⟩
    · rintro ⟨ho, hface⟩
      exact ⟨ho, (corner_switch_partition B d).1 hface⟩
  have hpartition : vertexDarts.card + faceDarts.card = outerDarts.card := by
    change (outerDarts.filter (fun d => vertexSwitchCorner B d)).card +
      faceDarts.card = outerDarts.card
    rw [← hfaceComplement]
    exact Finset.card_filter_add_card_filter_not
      (s := outerDarts) (p := fun d => vertexSwitchCorner B d)
  have houterTotal : outerDarts.card = ℓ + r := by
    rw [← houterCard, outerFace_dartCount_eq_boundaryLengths]
  have hfaceTotal : faceDarts.card = 2 := by
    rw [← hfaceCard, outerFaceSwitch_card]
  rw [hvertexCard]
  omega

end DirectedDistances.PlanarMap
