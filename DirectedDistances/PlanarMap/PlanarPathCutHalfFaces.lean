/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfMap
import DirectedDistances.PlanarMap.FiniteBipolarIncomingInterval

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

/-! # Face structure of a planar path-cut half

paper result. This file studies the face permutation induced by first-return
rotations on the closed half-dart carrier. -/

public section
namespace DirectedDistances.PlanarMap

open Equiv

/-- The proposed outer-boundary darts of the left half: original outer-face
darts retained by the half, together with the reversed darts of the cut path.
paper result. -/
@[expose] def pathCutLeftHalfBoundaryDarts {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Set D :=
  {d | (d ∈ pathCutLeftHalfDarts B P ∧ B.map.IsOuter d) ∨
    ∃ p ∈ P.darts, d = B.map.toCombinatorialMap.edgeInv p}

/-- Every proposed left-half boundary dart lies in the closed left half.
paper result. -/
theorem pathCutLeftHalfBoundaryDarts_subset
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    pathCutLeftHalfBoundaryDarts B P ⊆ pathCutLeftHalfDarts B P := by
  intro d hd
  rcases hd with ⟨hd, _⟩ | ⟨p, hp, rfl⟩
  · exact hd
  · change B.map.toCombinatorialMap.edgeInv p ∈
      pathCutLeftDarts B P ∪ pathCutSeamDarts B P
    right
    change B.map.toCombinatorialMap.edgeInv p ∈ P.darts ∨
      B.map.toCombinatorialMap.edgeInv
        (B.map.toCombinatorialMap.edgeInv p) ∈ P.darts
    rw [B.map.toCombinatorialMap.edgeInv_invol]
    exact Or.inr hp

/-- The left-half face successor is inverse-rotation first return after
reversing the edge dart. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalf_faceSucc_eq_firstReturn {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    ((pathCutLeftHalfMap B P).faceSucc d).1 =
      (firstReturn B.map.toCombinatorialMap.rot.symm
        (pathCutLeftHalfDarts B P)
        ⟨B.map.toCombinatorialMap.edgeInv d.1,
          pathCutLeftHalf_edgeInv_mem B P d.2⟩ : D) := by
  classical
  let S := pathCutLeftHalfDarts B P
  have h := firstReturnPerm_symm B.map.toCombinatorialMap.rot S
  change ((firstReturnPerm B.map.toCombinatorialMap.rot S).symm
      (restrictedPerm B.map.toCombinatorialMap.edgeInv S
        (fun x hx => pathCutLeftHalf_edgeInv_mem B P hx) d)).1 = _
  rw [restrictedPerm_apply, h]
  rfl

/-- If the original face successor lies in the left half, it is the
left-half face successor. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalf_faceSucc_eq_base_of_mem {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {d : D} (hd : d ∈ pathCutLeftHalfDarts B P)
    (hface : B.map.toCombinatorialMap.faceSucc d ∈ pathCutLeftHalfDarts B P) :
    ((pathCutLeftHalfMap B P).faceSucc ⟨d, hd⟩).1 =
      B.map.toCombinatorialMap.faceSucc d := by
  exact congrArg Subtype.val (pathCutLeftHalf_faceSucc_eq B P hd hface)

/-- At a nonouter dart away from the seam, the left-half face successor is
the original face successor. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalf_faceSucc_eq_base_of_inner_offSeam
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {d : D} (hd : d ∈ pathCutLeftHalfDarts B P)
    (hinner : ¬ B.map.IsOuter d)
    (hoffSeam : d ∉ pathCutSeamDarts B P) :
    ((pathCutLeftHalfMap B P).faceSucc ⟨d, hd⟩).1 =
      B.map.toCombinatorialMap.faceSucc d := by
  apply pathCutLeftHalf_faceSucc_eq_base_of_mem B P hd
  change d ∈ pathCutLeftDarts B P ∪ pathCutSeamDarts B P at hd
  have hleft : d ∈ pathCutLeftDarts B P := by
    rcases hd with hleft | hseam
    · exact hleft
    · exact (hoffSeam hseam).elim
  exact Or.inl (pathCutLeft_faceSucc_mem_of_inner B P hleft hinner)

/-- Along the retained left outer arc, any base face-successor that stays on
that arc is also the left-half face-successor. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalf_faceSucc_eq_base_of_leftOuterArc
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {d : D} (hd : d ∈ pathCutLeftOuterArc B)
    (hnext : B.map.toCombinatorialMap.faceSucc d ∈ pathCutLeftOuterArc B) :
    ((pathCutLeftHalfMap B P).faceSucc
      ⟨d, Or.inl ⟨d, Or.inl hd, Relation.ReflTransGen.refl⟩⟩).1 =
      B.map.toCombinatorialMap.faceSucc d := by
  have hnextLeft : B.map.toCombinatorialMap.faceSucc d ∈ pathCutLeftDarts B P :=
    pathCutLeft_faceSucc_mem_of_outerArc B P hd hnext
  exact pathCutLeftHalf_faceSucc_eq_base_of_mem B P
    (Or.inl ⟨d, Or.inl hd, Relation.ReflTransGen.refl⟩)
    (Or.inl hnextLeft)

private theorem leftDarts_rightDarts_disjoint {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    Disjoint (pathCutLeftDarts B P) (pathCutRightDarts B P) := by
  obtain ⟨side, hl, hr, hf, he⟩ := pathCut_exists_side_coloring B P
  have hleft (d : D) (hd : d ∈ pathCutLeftDarts B P) : side d = true := by
    obtain ⟨a, ha, hreach⟩ := hd
    induction hreach with
    | refl => exact hl a ha
    | @tail b c _ hstep ih =>
        rcases hstep with ⟨rfl, hinner | ⟨_, hnext⟩⟩ | ⟨rfl, hseam⟩
        · exact (hf b hinner).trans ih
        · exact hl _ (.inl hnext)
        · exact (he b hseam).trans ih
  have hright (d : D) (hd : d ∈ pathCutRightDarts B P) : side d = false := by
    obtain ⟨a, ha, hreach⟩ := hd
    induction hreach with
    | refl => exact hr a ha
    | @tail b c _ hstep ih =>
        rcases hstep with ⟨rfl, hinner | ⟨_, hnext⟩⟩ | ⟨rfl, hseam⟩
        · exact (hf b hinner).trans ih
        · exact hr _ (.inl hnext)
        · exact (he b hseam).trans ih
  apply Set.disjoint_left.mpr
  intro d hd hd'
  have h := (hleft d hd).symm.trans (hright d hd')
  cases h

private theorem inner_left_not_boundary {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutLeftDarts B P) (hi : ¬ B.map.IsOuter d) :
    d ∉ pathCutLeftHalfBoundaryDarts B P := by
  rintro (⟨_, ho⟩ | ⟨p, hp, rfl⟩)
  · exact hi ho
  · exact Set.disjoint_left.mp (leftDarts_rightDarts_disjoint B P) hd
      (pathCut_pathDart_flip_mem_right B P hp)

private theorem not_boundary_inner_left {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutLeftHalfDarts B P)
    (hb : d ∉ pathCutLeftHalfBoundaryDarts B P) :
    d ∈ pathCutLeftDarts B P ∧ ¬ B.map.IsOuter d := by
  refine ⟨?_, fun ho => hb (.inl ⟨hd, ho⟩)⟩
  rcases hd with hl | (hp | hp)
  · exact hl
  · exact pathCut_pathDart_mem_left B P hp
  · exact (hb (.inr ⟨B.map.toCombinatorialMap.edgeInv d, hp,
      (B.map.toCombinatorialMap.edgeInv_invol d).symm⟩)).elim

private theorem inner_face_whole_left {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutLeftDarts B P) (hi : ¬ B.map.IsOuter d)
    {e : D} (he : B.map.toCombinatorialMap.faceSucc.SameCycle d e) :
    e ∈ pathCutLeftDarts B P ∧ ¬ B.map.IsOuter e := by
  obtain ⟨k, _, hk⟩ := he.exists_pow_eq'
  have hiter (j : ℕ) :
      (B.map.toCombinatorialMap.faceSucc ^ j) d ∈ pathCutLeftDarts B P ∧
        ¬ B.map.IsOuter ((B.map.toCombinatorialMap.faceSucc ^ j) d) := by
    induction j with
    | zero => simpa only [pow_zero, Perm.one_apply] using And.intro hd hi
    | succ j ih =>
        rw [pow_succ', Perm.mul_apply]
        refine ⟨pathCutLeft_faceSucc_mem_of_inner B P ih.1 ih.2, ?_⟩
        intro ho
        exact ih.2 (Perm.sameCycle_apply_right.mp ho)
  exact hk ▸ hiter k




theorem pathCutLeftHalf_inner_face_contained {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutLeftHalfDarts B P)
    (hb : d ∉ pathCutLeftHalfBoundaryDarts B P) :
    ¬ B.map.IsOuter d ∧
      ∀ e : D, B.map.toCombinatorialMap.faceSucc.SameCycle d e →
        e ∈ pathCutLeftHalfDarts B P ∧
          e ∉ pathCutLeftHalfBoundaryDarts B P := by
  obtain ⟨hl, hi⟩ := not_boundary_inner_left B P hd hb
  refine ⟨hi, ?_⟩
  intro e he
  obtain ⟨hel, hei⟩ := inner_face_whole_left B P hl hi he
  exact ⟨Or.inl hel, inner_left_not_boundary B P hel hei⟩




theorem pathCutLeftHalf_inner_faceOrbit_iff {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P})
    (hb : d.1 ∉ pathCutLeftHalfBoundaryDarts B P)
    (e : {e : D // e ∈ pathCutLeftHalfDarts B P}) :
    (pathCutLeftHalfMap B P).faceSucc.SameCycle d e ↔
      B.map.toCombinatorialMap.faceSucc.SameCycle d.1 e.1 := by
  exact pathCutLeftHalf_faceOrbit_iff B P d
    (fun e he => ((pathCutLeftHalf_inner_face_contained B P d.2 hb).2 e he).1) e



theorem pathCutLeftHalf_innerFacesDegreeThree {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P})
    (hb : d.1 ∉ pathCutLeftHalfBoundaryDarts B P) :
    (pathCutLeftHalfMap B P).faceSucc
        ((pathCutLeftHalfMap B P).faceSucc ((pathCutLeftHalfMap B P).faceSucc d)) = d ∧
      (pathCutLeftHalfMap B P).faceSucc d ≠ d ∧
      (pathCutLeftHalfMap B P).faceSucc ((pathCutLeftHalfMap B P).faceSucc d) ≠ d := by
  let f := (pathCutLeftHalfMap B P).faceSucc
  let g := B.map.toCombinatorialMap.faceSucc
  have hc := pathCutLeftHalf_inner_face_contained B P d.2 hb
  have hwhole : ∀ e, g.SameCycle d.1 e → e ∈ pathCutLeftHalfDarts B P :=
    fun e he => (hc.2 e he).1
  have h₁ : (f d).1 = g d.1 :=
    pathCutLeftHalf_faceSucc_eq_base_of_mem B P d.2
      (hwhole _ (Perm.SameCycle.refl g d.1).apply_right)
  have h₂ : (f (f d)).1 = g (g d.1) := by
    rw [pathCutLeftHalf_faceSucc_eq_base_of_mem B P (f d).2]
    · rw [h₁]
    · rw [h₁]
      exact hwhole _ (Perm.SameCycle.refl g d.1).apply_right.apply_right
  have h₃ : (f (f (f d))).1 = g (g (g d.1)) := by
    rw [pathCutLeftHalf_faceSucc_eq_base_of_mem B P (f (f d)).2]
    · rw [h₂]
    · rw [h₂]
      exact hwhole _ (Perm.SameCycle.refl g d.1).apply_right.apply_right.apply_right
  obtain ⟨ht, hn₁, hn₂⟩ := B.innerFacesDegreeThree d.1 hc.1
  exact ⟨Subtype.ext (h₃.trans ht),
    fun h => hn₁ (h₁.symm.trans (congrArg Subtype.val h)),
    fun h => hn₂ (h₂.symm.trans (congrArg Subtype.val h))⟩

private theorem boundary_iff_left_or_reverse {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D) :
    d ∈ pathCutLeftHalfBoundaryDarts B P ↔
      d ∈ B.leftPath.darts ∨ ∃ p ∈ P.darts, d = B.map.toCombinatorialMap.edgeInv p := by
  constructor
  · rintro (⟨hd, ho⟩ | hr)
    · rcases (isOuter_iff_mem_outerArcs B d).mp ho with hl | hr
      · exact Or.inl ((mem_pathCutLeftOuterArc_iff B d).mp hl)
      · have hdr : d ∈ pathCutRightDarts B P :=
          ⟨d, Or.inl hr, Relation.ReflTransGen.refl⟩
        rcases hd with hd | (hp | hp)
        · exact (Set.disjoint_left.mp (leftDarts_rightDarts_disjoint B P) hd hdr).elim
        · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
          exact (hr.2.1 (P.edge_step i).2.1).elim
        · exact Or.inr ⟨B.map.toCombinatorialMap.edgeInv d, hp,
            (B.map.toCombinatorialMap.edgeInv_invol d).symm⟩
    · exact Or.inr hr
  · rintro (hl | hr)
    · have ha := (mem_pathCutLeftOuterArc_iff B d).mpr hl
      exact Or.inl ⟨Or.inl ⟨d, Or.inl ha, Relation.ReflTransGen.refl⟩, ha.2.2⟩
    · exact Or.inr hr

private theorem half_boundary_orbit_closed {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {d e : {d : D // d ∈ pathCutLeftHalfDarts B P}}
    (hd : d.1 ∈ pathCutLeftHalfBoundaryDarts B P)
    (he : (pathCutLeftHalfMap B P).faceSucc.SameCycle d e) :
    e.1 ∈ pathCutLeftHalfBoundaryDarts B P := by
  by_contra hn
  have hbase := (pathCutLeftHalf_inner_faceOrbit_iff B P e hn d).mp he.symm
  exact ((pathCutLeftHalf_inner_face_contained B P e.2 hn).2 d.1 hbase).2 hd

private theorem half_faceSucc_vertex {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    dartTailVertex B.map ((pathCutLeftHalfMap B P).faceSucc d).1 =
      dartHeadVertex B.map d.1 := by
  rw [pathCutLeftHalf_faceSucc_eq_firstReturn]
  apply Quotient.sound
  change B.map.rot.SameCycle
    ((B.map.rot.symm : D → D)^[firstReturnTime B.map.rot.symm
      (pathCutLeftHalfDarts B P)
      ⟨B.map.edgeInv d.1, pathCutLeftHalf_edgeInv_mem B P d.2⟩] (B.map.edgeInv d.1))
    (B.map.edgeInv d.1)
  rw [perm_iterate_eq_pow]
  exact (Perm.SameCycle.pow_left (Perm.SameCycle.refl B.map.rot.symm
    (B.map.edgeInv d.1))).of_inv

private theorem left_boundary_faceSucc_get {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (i : ℕ) (hi : i + 1 < ℓ) :
    B.map.toCombinatorialMap.faceSucc
        (B.leftPath.darts.get ⟨i, by rw [B.leftPath.darts_length]; omega⟩) =
      B.leftPath.darts.get ⟨i + 1, by rw [B.leftPath.darts_length]; omega⟩ := by
  let xs := B.leftPath.darts ++
    B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv
  have hnodup : xs.Nodup := by
    simpa [xs] using B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup
  have hlen : xs.length = ℓ + r := by
    simp [xs, B.leftPath.darts_length, B.rightPath.darts_length]
  let d := B.leftPath.darts.get ⟨i, by rw [B.leftPath.darts_length]; omega⟩
  have hdOuter : B.map.IsOuter d :=
    ((B.outerSplit.2.2.1 d).mp (List.get_mem _ _)).2.2
  have hdWord : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr hdOuter
  have hface : B.map.toCombinatorialMap.faceSucc d = xs.formPerm d := by
    rw [B.outerSplit.1.2.2 d hdWord]
    simpa [xs] using congrArg (fun p : Perm D => p d)
      (List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1)
  have hidx : d = xs[i]'(by rw [hlen]; omega) := by
    dsimp [d, xs]
    rw [List.getElem_append_left (by rw [B.leftPath.darts_length]; omega)]
  have hform := List.formPerm_apply_getElem xs hnodup i (by rw [hlen]; omega)
  have hmod : (i + 1) % xs.length = i + 1 := Nat.mod_eq_of_lt (by rw [hlen]; omega)
  change B.map.toCombinatorialMap.faceSucc d = _
  rw [hface, hidx, hform]
  simp only [hmod]
  dsimp [xs]
  rw [List.getElem_append_left (by rw [B.leftPath.darts_length]; exact hi)]

private theorem left_half_faceSucc_get {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (i : ℕ) (hi : i + 1 < ℓ)
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P})
    (hd : d.1 = B.leftPath.darts.get ⟨i, by rw [B.leftPath.darts_length]; omega⟩) :
    ((pathCutLeftHalfMap B P).faceSucc d).1 =
      B.leftPath.darts.get ⟨i + 1, by rw [B.leftPath.darts_length]; omega⟩ := by
  have hbase := left_boundary_faceSucc_get B i hi
  have hnext : B.map.toCombinatorialMap.faceSucc d.1 ∈ pathCutLeftHalfDarts B P := by
    rw [hd, hbase]
    exact Or.inl ⟨_, Or.inl ((mem_pathCutLeftOuterArc_iff B _).mpr
      (List.get_mem _ _)), Relation.ReflTransGen.refl⟩
  rw [pathCutLeftHalf_faceSucc_eq_base_of_mem B P d.2 hnext, hd, hbase]




theorem pathCutLeftHalf_boundary_single_orbit {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    ∃ d₀ : {d : D // d ∈ pathCutLeftHalfDarts B P},
      d₀.1 ∈ pathCutLeftHalfBoundaryDarts B P ∧
      ∀ e : {d : D // d ∈ pathCutLeftHalfDarts B P},
        (pathCutLeftHalfMap B P).faceSucc.SameCycle d₀ e ↔
          e.1 ∈ pathCutLeftHalfBoundaryDarts B P := by
  let H := {d : D // d ∈ pathCutLeftHalfDarts B P}
  let f := (pathCutLeftHalfMap B P).faceSucc
  let L (i : Fin ℓ) : H :=
    ⟨B.leftPath.darts.get ⟨i.val, by rw [B.leftPath.darts_length]; exact i.isLt⟩,
      Or.inl ⟨_, Or.inl ((mem_pathCutLeftOuterArc_iff B _).mpr
        (List.get_mem _ _)), Relation.ReflTransGen.refl⟩⟩
  let R (i : Fin n) : H :=
    ⟨B.map.edgeInv (P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩),
      pathCutLeftHalfBoundaryDarts_subset B P (.inr ⟨_, List.get_mem _ _, rfl⟩)⟩
  let z : H := L ⟨0, B.left_length_pos⟩
  have hz : z.1 ∈ pathCutLeftHalfBoundaryDarts B P :=
    (boundary_iff_left_or_reverse B P z.1).mpr (.inl (List.get_mem _ _))
  have hL : ∀ (i : ℕ) (hi : i < ℓ), f.SameCycle z (L ⟨i, hi⟩) := by
    intro i
    induction i with
    | zero => intro hi; exact Perm.SameCycle.rfl
    | succ i ih =>
        intro hi
        have hs : f (L ⟨i, by omega⟩) = L ⟨i + 1, hi⟩ :=
          Subtype.ext (left_half_faceSucc_get B P i hi _ rfl)
        exact hs ▸ (ih (by omega)).apply_right
  have hR : ∀ (i : ℕ) (hi : i < n), f.SameCycle z (R ⟨i, hi⟩) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
        intro hi
        let a : Fin P.darts.length := ⟨i, by rw [P.darts_length]; exact hi⟩
        let d : H := R ⟨i, hi⟩
        let e : H := f d
        have hdB : d.1 ∈ pathCutLeftHalfBoundaryDarts B P :=
          Or.inr ⟨_, List.get_mem _ a, rfl⟩
        have heB : e.1 ∈ pathCutLeftHalfBoundaryDarts B P :=
          half_boundary_orbit_closed B P hdB Perm.SameCycle.rfl.apply_right
        have hv : dartTailVertex B.map e.1 = dartTailVertex B.map (P.darts.get a) := by
          calc
            dartTailVertex B.map e.1 = dartHeadVertex B.map d.1 :=
              half_faceSucc_vertex B P d
            _ = dartTailVertex B.map (P.darts.get a) := by
              change dartTailVertex B.map (B.map.edgeInv (B.map.edgeInv
                (P.darts.get a))) = _
              rw [B.map.edgeInv_invol]
        have hecycle : f.SameCycle z e := by
          rcases (boundary_iff_left_or_reverse B P e.1).mp heB with heL | ⟨p, hp, hep⟩
          · obtain ⟨j, hj⟩ := List.mem_iff_get.mp heL
            have hjlt : j.val < ℓ := by simpa only [B.leftPath.darts_length] using j.isLt
            by_cases hj0 : j.val = 0
            · have hez : e = z := by
                apply Subtype.ext
                exact hj.symm.trans (congrArg B.leftPath.darts.get (Fin.ext hj0))
              exact hez ▸ Perm.SameCycle.rfl
            · let k : Fin ℓ := ⟨j.val - 1, by omega⟩
              have hpred : f (L k) = e := by
                apply Subtype.ext
                have hs := left_half_faceSucc_get B P (j.val - 1) (by omega) (L k) rfl
                exact hs.trans ((congrArg B.leftPath.darts.get
                  (Fin.ext (by dsimp; omega))).trans hj)
              have hde : L k = d := f.injective hpred
              have htail : B.map.tail (L k).1 :=
                (B.leftPath.edge_step ⟨k.val, by rw [B.leftPath.darts_length]; exact k.isLt⟩).2.1
              have hn : ¬ B.map.tail d.1 :=
                (B.map.tail_iff _ (B.noMissingDarts _)).mp (P.edge_step a).2.1
              exact (hn (hde ▸ htail)).elim
          · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
            have hjlt : j.val < n := by simpa only [P.darts_length] using j.isLt
            have hhead : dartHeadVertex B.map (P.darts.get j) =
                dartTailVertex B.map (P.darts.get a) := by
              rw [← hj] at hep
              exact (congrArg (dartTailVertex B.map) hep).symm.trans hv
            have hverts := (P.edge_step j).2.2.2.trans
              (hhead.trans (P.edge_step a).2.2.1.symm)
            have hidx := congrArg Fin.val (P.vertices_nodup.get_inj_iff.mp hverts)
            have hji : j.val < i := by dsimp [a] at hidx; omega
            have heR : e = R ⟨j.val, hjlt⟩ := by
              apply Subtype.ext
              exact hep.trans (congrArg B.map.edgeInv hj.symm)
            exact heR ▸ ih j.val hji hjlt
        exact Perm.sameCycle_apply_right.mp hecycle
  refine ⟨z, hz, ?_⟩
  intro e
  constructor
  · exact half_boundary_orbit_closed B P hz
  · intro he
    rcases (boundary_iff_left_or_reverse B P e.1).mp he with heL | ⟨p, hp, hep⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp heL
      have hilt : i.val < ℓ := by simpa only [B.leftPath.darts_length] using i.isLt
      have heq : L ⟨i.val, hilt⟩ = e := Subtype.ext hi
      exact heq ▸ hL i.val hilt
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
      have hilt : i.val < n := by simpa only [P.darts_length] using i.isLt
      have heq : R ⟨i.val, hilt⟩ = e :=
        Subtype.ext ((congrArg B.map.edgeInv hi).trans hep.symm)
      exact heq ▸ hR i.val hilt

private theorem contained_inner_not_boundary {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hi : ¬ B.map.IsOuter d)
    (hwhole : ∀ e : D, B.map.toCombinatorialMap.faceSucc.SameCycle d e →
      e ∈ pathCutLeftHalfDarts B P) :
    d ∉ pathCutLeftHalfBoundaryDarts B P := by
  let f := B.map.toCombinatorialMap.faceSucc
  have hex : ∃ e : D, f.SameCycle d e ∧ B.map.tail e := by
    rcases (innerFace_has_both_boundary_orientations B d hi).1 with ht | ht | ht
    · exact ⟨d, Perm.SameCycle.rfl, ht⟩
    · exact ⟨f d, Perm.SameCycle.rfl.apply_right, ht⟩
    · exact ⟨f (f d), Perm.SameCycle.rfl.apply_right.apply_right, ht⟩
  obtain ⟨e, he, ht⟩ := hex
  have hei : ¬ B.map.IsOuter e := fun ho => hi (ho.trans he.symm)
  have heb : e ∉ pathCutLeftHalfBoundaryDarts B P := by
    rintro (⟨_, ho⟩ | ⟨p, hp, hep⟩)
    · exact hei ho
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
      exact ((B.map.tail_iff _ (B.noMissingDarts _)).mp (P.edge_step i).2.1)
        (hep ▸ ht)
  have hel := (not_boundary_inner_left B P (hwhole e he) heb).1
  have hdl := (inner_face_whole_left B P hel hei he.symm).1
  exact inner_left_not_boundary B P hdl hi




theorem pathCutLeftHalf_numFaces {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    (pathCutLeftHalfMap B P).numFaces =
      Nat.card {q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap //
        q ≠ faceClass B.map.toCombinatorialMap B.map.outer ∧
          ∀ d : D, faceClass B.map.toCombinatorialMap d = q →
            d ∈ pathCutLeftHalfDarts B P} + 1 := by
  classical
  let M := B.map.toCombinatorialMap
  let A := pathCutLeftHalfMap B P
  let H := {d : D // d ∈ pathCutLeftHalfDarts B P}
  obtain ⟨z, hz, hzc⟩ := pathCutLeftHalf_boundary_single_orbit B P
  let I := {q : CombinatorialMap.FaceQuotient A // q ≠ faceClass A z}
  let J := {q : CombinatorialMap.FaceQuotient M //
    q ≠ faceClass M B.map.outer ∧
      ∀ d : D, faceClass M d = q → d ∈ pathCutLeftHalfDarts B P}
  have hrep (q : I) : q.1.out.1 ∉ pathCutLeftHalfBoundaryDarts B P := by
    intro hb
    apply q.2
    calc
      q.1 = faceClass A q.1.out := (Quotient.out_eq q.1).symm
      _ = faceClass A z := Quotient.sound ((hzc q.1.out).mpr hb).symm
  have hclass (q : I) :
      faceClass M q.1.out.1 ≠ faceClass M B.map.outer ∧
        ∀ d : D, faceClass M d = faceClass M q.1.out.1 →
          d ∈ pathCutLeftHalfDarts B P := by
    have hc := pathCutLeftHalf_inner_face_contained B P q.1.out.2 (hrep q)
    refine ⟨fun h => hc.1 (Quotient.exact h).symm, ?_⟩
    intro d hd
    exact (hc.2 d (Quotient.exact hd.symm)).1
  let F : I → J := fun q => ⟨faceClass M q.1.out.1, hclass q⟩
  have hinj : Function.Injective F := by
    intro q q' hq
    have hbase : M.faceSucc.SameCycle q.1.out.1 q'.1.out.1 :=
      Quotient.exact (congrArg Subtype.val hq)
    have hhalf : A.faceSucc.SameCycle q.1.out q'.1.out :=
      (pathCutLeftHalf_inner_faceOrbit_iff B P q.1.out (hrep q) q'.1.out).mpr hbase
    apply Subtype.ext
    calc
      q.1 = faceClass A q.1.out := (Quotient.out_eq q.1).symm
      _ = faceClass A q'.1.out := Quotient.sound hhalf
      _ = q'.1 := Quotient.out_eq q'.1
  have hsurj : Function.Surjective F := by
    intro q
    let d : D := q.1.out
    have hdq : faceClass M d = q.1 := Quotient.out_eq q.1
    have hd : d ∈ pathCutLeftHalfDarts B P := q.2.2 d hdq
    have hi : ¬ B.map.IsOuter d := by
      intro ho
      exact q.2.1 (hdq.symm.trans (Quotient.sound ho.symm))
    have hwhole : ∀ e : D, M.faceSucc.SameCycle d e →
        e ∈ pathCutLeftHalfDarts B P := by
      intro e he
      exact q.2.2 e ((Quotient.sound he.symm).trans hdq)
    have hb := contained_inner_not_boundary B P hi hwhole
    let dh : H := ⟨d, hd⟩
    have hne : faceClass A dh ≠ faceClass A z := by
      intro h
      exact hb ((hzc dh).mp (Quotient.exact h).symm)
    let qh : I := ⟨faceClass A dh, hne⟩
    refine ⟨qh, ?_⟩
    apply Subtype.ext
    have hh : A.faceSucc.SameCycle qh.1.out dh := Quotient.exact (Quotient.out_eq qh.1)
    have hm : M.faceSucc.SameCycle qh.1.out.1 d :=
      (pathCutLeftHalf_inner_faceOrbit_iff B P qh.1.out (hrep qh) dh).mp hh
    exact (Quotient.sound hm).trans hdq
  have hcard : Fintype.card I = Fintype.card J :=
    Fintype.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)
  have hI : Fintype.card I = A.numFaces - 1 := by
    dsimp [I]
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    rfl
  have hpos : 0 < A.numFaces :=
    Fintype.card_pos_iff.mpr ⟨faceClass A z⟩
  change A.numFaces = Nat.card J + 1
  rw [Nat.card_eq_fintype_card]
  omega

end DirectedDistances.PlanarMap
