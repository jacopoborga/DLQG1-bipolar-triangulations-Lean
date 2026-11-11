/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralBipolarBoundary

/-! # Dart-side reachability for a path cut

This is a helper toward `lem-lr-ind`; it is not the paper result
left of a dart. In the outer-face order, the left path is the left arc and
the reversed opposite darts of the right path form the right arc; these arcs
are disjoint and their union is exactly the set of outer darts. A forward
dart of the cut path is seeded on the left and its opposite dart on the
right, including when a path edge coincides with a boundary edge. Flipping a
two sides. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

private theorem outerSplit_leftPath_darts_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    d ∈ B.leftPath.darts ↔ d ∈ B.map.ulDarts := by
  rcases B.outerSplit with ⟨_, _, hleft, _, _, _⟩
  exact hleft d

private theorem outerSplit_rightPath_reverse_edgeInv_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    d ∈ B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv ↔
      d ∈ B.map.lrDarts := by
  rcases B.outerSplit with ⟨_, _, _, hright, _, _⟩
  exact hright d

private theorem outerSplit_isOuterCycle
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    IsOuterCycle B.map B.outerWord := by
  rcases B.outerSplit with ⟨hcycle, _, _, _, _, _⟩
  exact hcycle

private theorem outerSplit_outerWord_perm
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.outerWord.letters ~r
      (B.leftPath.darts ++ [] ++
        (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv) ++ []) := by
  rcases B.outerSplit with ⟨_, hperm, _, _, _, _⟩
  exact hperm

/-- The darts of the path together with their opposite darts. Flipping one
of these darts is forbidden because it crosses the path (`lem-lr-ind`,
paper result. -/
@[expose] def pathCutSeamDarts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Set D :=
  {d | d ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv d ∈ P.darts}

/-- The left outer-face arc is the upper-left dart set singled out by
helper toward `lem-lr-ind`, not the paper result. -/
@[expose] def pathCutLeftOuterArc
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : Set D :=
  B.map.ulDarts

/-- The right outer-face arc is the lower-right dart set singled out by
helper toward `lem-lr-ind`, not the paper result. -/
@[expose] def pathCutRightOuterArc
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : Set D :=
  B.map.lrDarts

/-- Darts anchoring the left side: the left outer-face arc and the directed
toward `lem-lr-ind`, not the paper result. -/
@[expose] def pathCutLeftSeeds
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Set D :=
  {d | d ∈ pathCutLeftOuterArc B ∨ d ∈ P.darts}

/-- Darts anchoring the right side: the right outer-face arc and the reversed
toward `lem-lr-ind`, not the paper result. -/
@[expose] def pathCutRightSeeds
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Set D :=
  {d | d ∈ pathCutRightOuterArc B ∨
    ∃ p ∈ P.darts, d = B.map.toCombinatorialMap.edgeInv p}

/-- A left-side step follows a face successor, except that the exterior face
can be followed only within its left outer arc, or flips a non-seam edge
`lem-lr-ind`, not the paper result. -/
@[expose] def pathCutLeftStep
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d e : D) : Prop :=
  (e = B.map.toCombinatorialMap.faceSucc d ∧
    (¬ B.map.IsOuter d ∨
      (d ∈ pathCutLeftOuterArc B ∧ e ∈ pathCutLeftOuterArc B))) ∨
  (e = B.map.toCombinatorialMap.edgeInv d ∧ d ∉ pathCutSeamDarts B P)

/-- A right-side step follows a face successor, except that the exterior face
can be followed only within its right outer arc, or flips a non-seam edge
`lem-lr-ind`, not the paper result. -/
@[expose] def pathCutRightStep
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d e : D) : Prop :=
  (e = B.map.toCombinatorialMap.faceSucc d ∧
    (¬ B.map.IsOuter d ∨
      (d ∈ pathCutRightOuterArc B ∧ e ∈ pathCutRightOuterArc B))) ∨
  (e = B.map.toCombinatorialMap.edgeInv d ∧ d ∉ pathCutSeamDarts B P)

/-- The left dart set is the reflexive-transitive closure of the left outer
arc and the path under left-side steps (`lem-lr-ind`,
paper result. -/
@[expose] def pathCutLeftDarts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Set D :=
  {d | ∃ a ∈ pathCutLeftSeeds B P,
    Relation.ReflTransGen (pathCutLeftStep B P) a d}

/-- The right dart set is the reflexive-transitive closure of the right outer
arc and the reversed path under right-side steps (`lem-lr-ind`,
paper result. -/
@[expose] def pathCutRightDarts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Set D :=
  {d | ∃ a ∈ pathCutRightSeeds B P,
    Relation.ReflTransGen (pathCutRightStep B P) a d}

/-- The outerSplit left arc is exactly the left boundary dart list
`lem-lr-ind`, not the paper result. -/
theorem mem_pathCutLeftOuterArc_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    d ∈ pathCutLeftOuterArc B ↔ d ∈ B.leftPath.darts := by
  exact (outerSplit_leftPath_darts_iff B d).symm

/-- The outerSplit right arc is exactly the reverse opposite-dart list of the
toward `lem-lr-ind`, not the paper result. -/
theorem mem_pathCutRightOuterArc_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    d ∈ pathCutRightOuterArc B ↔
      d ∈ B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv := by
  exact (outerSplit_rightPath_reverse_edgeInv_iff B d).symm

/-- The left and right outer-face arcs are disjoint by nodup of the outer
`lem-lr-ind`, not the paper result. -/
theorem pathCut_outerArcs_disjoint
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Disjoint (pathCutLeftOuterArc B) (pathCutRightOuterArc B) := by
  have hnodup :
      (B.leftPath.darts ++
        (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)).Nodup := by
    have h := (outerSplit_outerWord_perm B).perm.nodup_iff.mp B.outerWord.nodup
    simpa only [List.nil_append, List.append_nil, List.append_assoc] using h
  have hdisj := List.disjoint_of_nodup_append hnodup
  refine Set.disjoint_left.mpr ?_
  intro d hleft hright
  apply hdisj
  · exact (outerSplit_leftPath_darts_iff B d).mpr hleft
  · exact (outerSplit_rightPath_reverse_edgeInv_iff B d).mpr hright

/-- The outer darts are exactly those in one of the two path arcs, by the
helper toward `lem-lr-ind`, not the paper result. -/
theorem isOuter_iff_mem_outerArcs
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    B.map.IsOuter d ↔
      d ∈ pathCutLeftOuterArc B ∨ d ∈ pathCutRightOuterArc B := by
  rw [← mem_iff_isOuter B.map B.outerWord (outerSplit_isOuterCycle B)]
  rw [(outerSplit_outerWord_perm B).mem_iff]
  simp only [List.append_nil, List.mem_append, mem_pathCutLeftOuterArc_iff,
    mem_pathCutRightOuterArc_iff]

/-- A face successor of an interior dart stays in the left dart set by one
toward `lem-lr-ind`, not the paper result. -/
theorem pathCutLeft_faceSucc_mem_of_inner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutLeftDarts B P) (hinner : ¬ B.map.IsOuter d) :
    B.map.toCombinatorialMap.faceSucc d ∈ pathCutLeftDarts B P := by
  rcases hd with ⟨a, ha, hreach⟩
  have hstep : pathCutLeftStep B P d (B.map.toCombinatorialMap.faceSucc d) :=
    Or.inl ⟨rfl, Or.inl hinner⟩
  exact ⟨a, ha, Relation.ReflTransGen.tail hreach hstep⟩

/-- A face successor that remains in the left outer arc is a left seed
`lem-lr-ind`, not the paper result. -/
theorem pathCutLeft_faceSucc_mem_of_outerArc
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (_hd : d ∈ pathCutLeftOuterArc B)
    (hnext : B.map.toCombinatorialMap.faceSucc d ∈ pathCutLeftOuterArc B) :
    B.map.toCombinatorialMap.faceSucc d ∈ pathCutLeftDarts B P := by
  exact ⟨B.map.toCombinatorialMap.faceSucc d, Or.inl hnext,
    Relation.ReflTransGen.refl⟩

/-- A face successor of an interior dart stays in the right dart set by one
toward `lem-lr-ind`, not the paper result. -/
theorem pathCutRight_faceSucc_mem_of_inner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutRightDarts B P) (hinner : ¬ B.map.IsOuter d) :
    B.map.toCombinatorialMap.faceSucc d ∈ pathCutRightDarts B P := by
  rcases hd with ⟨a, ha, hreach⟩
  have hstep : pathCutRightStep B P d (B.map.toCombinatorialMap.faceSucc d) :=
    Or.inl ⟨rfl, Or.inl hinner⟩
  exact ⟨a, ha, Relation.ReflTransGen.tail hreach hstep⟩

/-- A face successor that remains in the right outer arc is a right seed
`lem-lr-ind`, not the paper result. -/
theorem pathCutRight_faceSucc_mem_of_outerArc
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (_hd : d ∈ pathCutRightOuterArc B)
    (hnext : B.map.toCombinatorialMap.faceSucc d ∈ pathCutRightOuterArc B) :
    B.map.toCombinatorialMap.faceSucc d ∈ pathCutRightDarts B P := by
  exact ⟨B.map.toCombinatorialMap.faceSucc d, Or.inl hnext,
    Relation.ReflTransGen.refl⟩

/-- Every dart of the cut path belongs to the left dart set by its seed
`lem-lr-ind`, not the paper result. -/
theorem pathCut_pathDart_mem_left
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ P.darts) : d ∈ pathCutLeftDarts B P := by
  exact ⟨d, Or.inr hd, Relation.ReflTransGen.refl⟩

/-- The opposite of every path dart belongs to the right dart set by its seed
`lem-lr-ind`, not the paper result. -/
theorem pathCut_pathDart_flip_mem_right
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ P.darts) :
    B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightDarts B P := by
  exact ⟨B.map.toCombinatorialMap.edgeInv d,
    Or.inr ⟨d, hd, rfl⟩, Relation.ReflTransGen.refl⟩

/-- The seam-dart predicate is invariant under edge reversal
`lem-lr-ind`, not the paper result. -/
theorem pathCutSeamDarts_edgeInv_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D) :
    B.map.toCombinatorialMap.edgeInv d ∈ pathCutSeamDarts B P ↔
      d ∈ pathCutSeamDarts B P := by
  change (B.map.toCombinatorialMap.edgeInv d ∈ P.darts ∨
      B.map.toCombinatorialMap.edgeInv
        (B.map.toCombinatorialMap.edgeInv d) ∈ P.darts) ↔
    (d ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv d ∈ P.darts)
  rw [B.map.toCombinatorialMap.edgeInv_invol]
  exact or_comm

/-- Flipping a non-seam dart preserves membership in the left dart set by
helper toward `lem-lr-ind`, not the paper result. -/
theorem pathCutLeft_edgeInv_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutLeftDarts B P)
    (hseam : d ∉ pathCutSeamDarts B P) :
    B.map.toCombinatorialMap.edgeInv d ∈ pathCutLeftDarts B P := by
  rcases hd with ⟨a, ha, hreach⟩
  have hstep : pathCutLeftStep B P d (B.map.toCombinatorialMap.edgeInv d) := by
    exact Or.inr ⟨rfl, hseam⟩
  exact ⟨a, ha, Relation.ReflTransGen.tail hreach hstep⟩

/-- Flipping a non-seam dart preserves membership in the right dart set by
helper toward `lem-lr-ind`, not the paper result. -/
theorem pathCutRight_edgeInv_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutRightDarts B P)
    (hseam : d ∉ pathCutSeamDarts B P) :
    B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightDarts B P := by
  rcases hd with ⟨a, ha, hreach⟩
  have hstep : pathCutRightStep B P d (B.map.toCombinatorialMap.edgeInv d) := by
    exact Or.inr ⟨rfl, hseam⟩
  exact ⟨a, ha, Relation.ReflTransGen.tail hreach hstep⟩

/-- Every dart in a non-seam edge orbit with a left-side representative is
helper toward `lem-lr-ind`, not the paper result. -/
theorem pathCutLeft_edgeOrbit_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d e : D} (hd : d ∈ pathCutLeftDarts B P)
    (hseam : d ∉ pathCutSeamDarts B P)
    (horbit : Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv d e) :
    e ∈ pathCutLeftDarts B P := by
  rcases (CombinatorialMap.edgeInv_sameCycle_iff B.map.toCombinatorialMap d e).mp
      horbit with hde | hde
  · simpa [hde] using hd
  · rw [hde]
    exact pathCutLeft_edgeInv_mem B P hd hseam

/-- Every dart in a non-seam edge orbit with a right-side representative is
helper toward `lem-lr-ind`, not the paper result. -/
theorem pathCutRight_edgeOrbit_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d e : D} (hd : d ∈ pathCutRightDarts B P)
    (hseam : d ∉ pathCutSeamDarts B P)
    (horbit : Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv d e) :
    e ∈ pathCutRightDarts B P := by
  rcases (CombinatorialMap.edgeInv_sameCycle_iff B.map.toCombinatorialMap d e).mp
      horbit with hde | hde
  · simpa [hde] using hd
  · rw [hde]
    exact pathCutRight_edgeInv_mem B P hd hseam

/-- Every dart is reached from one of the two path-cut seed sets using
face-successor and edge-involution steps, by connectedness of the map
`lem-lr-ind`, not the paper result. -/
theorem pathCut_darts_cover
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D) :
    d ∈ pathCutLeftDarts B P ∨ d ∈ pathCutRightDarts B P := by
  classical
  let U : Set D := pathCutLeftDarts B P ∪ pathCutRightDarts B P
  let f := B.map.toCombinatorialMap.faceSucc
  let e := B.map.toCombinatorialMap.edgeInv
  have hface (x : D) (hx : x ∈ U) : f x ∈ U := by
    change x ∈ pathCutLeftDarts B P ∨ x ∈ pathCutRightDarts B P at hx
    rcases hx with hleft | hright
    · by_cases houter : B.map.IsOuter x
      · have hnextOuter : B.map.IsOuter (f x) := by
          change f.SameCycle B.map.outer (f x)
          change f.SameCycle B.map.outer x at houter
          exact Equiv.Perm.sameCycle_apply_right.mpr houter
        rcases (isOuter_iff_mem_outerArcs B (f x)).mp hnextOuter with harc | harc
        · change f x ∈ pathCutLeftDarts B P ∨ f x ∈ pathCutRightDarts B P
          exact Or.inl ⟨f x, Or.inl harc, Relation.ReflTransGen.refl⟩
        · change f x ∈ pathCutLeftDarts B P ∨ f x ∈ pathCutRightDarts B P
          exact Or.inr ⟨f x, Or.inl harc, Relation.ReflTransGen.refl⟩
      · change f x ∈ pathCutLeftDarts B P ∨ f x ∈ pathCutRightDarts B P
        exact Or.inl (pathCutLeft_faceSucc_mem_of_inner B P hleft houter)
    · by_cases houter : B.map.IsOuter x
      · have hnextOuter : B.map.IsOuter (f x) := by
          change f.SameCycle B.map.outer (f x)
          change f.SameCycle B.map.outer x at houter
          exact Equiv.Perm.sameCycle_apply_right.mpr houter
        rcases (isOuter_iff_mem_outerArcs B (f x)).mp hnextOuter with harc | harc
        · change f x ∈ pathCutLeftDarts B P ∨ f x ∈ pathCutRightDarts B P
          exact Or.inl ⟨f x, Or.inl harc, Relation.ReflTransGen.refl⟩
        · change f x ∈ pathCutLeftDarts B P ∨ f x ∈ pathCutRightDarts B P
          exact Or.inr ⟨f x, Or.inl harc, Relation.ReflTransGen.refl⟩
      · change f x ∈ pathCutLeftDarts B P ∨ f x ∈ pathCutRightDarts B P
        exact Or.inr (pathCutRight_faceSucc_mem_of_inner B P hright houter)
  have hedge (x : D) (hx : x ∈ U) : e x ∈ U := by
    change x ∈ pathCutLeftDarts B P ∨ x ∈ pathCutRightDarts B P at hx
    by_cases hseam : x ∈ pathCutSeamDarts B P
    · change x ∈ P.darts ∨ e x ∈ P.darts at hseam
      rcases hseam with hp | hp
      · change e x ∈ pathCutLeftDarts B P ∨ e x ∈ pathCutRightDarts B P
        exact Or.inr (pathCut_pathDart_flip_mem_right B P hp)
      · change e x ∈ pathCutLeftDarts B P ∨ e x ∈ pathCutRightDarts B P
        exact Or.inl (pathCut_pathDart_mem_left B P hp)
    · rcases hx with hleft | hright
      · change e x ∈ pathCutLeftDarts B P ∨ e x ∈ pathCutRightDarts B P
        exact Or.inl (pathCutLeft_edgeInv_mem B P hleft hseam)
      · change e x ∈ pathCutLeftDarts B P ∨ e x ∈ pathCutRightDarts B P
        exact Or.inr (pathCutRight_edgeInv_mem B P hright hseam)
  have hfaceInv (x : D) (hx : x ∈ U) : f.symm x ∈ U := by
    have hpowmem : ∀ k : ℕ, (f ^ k) x ∈ U := by
      intro k
      induction k with
      | zero => simpa using hx
      | succ k ih =>
          rw [pow_succ']
          exact hface _ ih
    have horderpos : 0 < orderOf f := orderOf_pos f
    have hk : orderOf f - 1 + 1 = orderOf f := by omega
    have horder : f ^ orderOf f = 1 := pow_orderOf_eq_one f
    have hprev : f ^ (orderOf f - 1) * f = 1 := by
      rw [← hk, pow_succ] at horder
      exact horder
    have hmul : f * f.symm = 1 := by
      ext y
      simp
    have hpow : f ^ (orderOf f - 1) = f.symm := by
      calc
        f ^ (orderOf f - 1) = f ^ (orderOf f - 1) * 1 := by simp
        _ = f ^ (orderOf f - 1) * (f * f.symm) := by rw [hmul]
        _ = (f ^ (orderOf f - 1) * f) * f.symm := by rw [mul_assoc]
        _ = 1 * f.symm := by rw [hprev]
        _ = f.symm := by simp
    rw [← hpow]
    exact hpowmem (orderOf f - 1)
  have hrotSymm (x : D) (hx : x ∈ U) :
      B.map.toCombinatorialMap.rot.symm x ∈ U := by
    have hEq : f (e x) = B.map.toCombinatorialMap.rot.symm x := by
      simp [f, e, CombinatorialMap.faceSucc, Equiv.Perm.mul_apply,
        B.map.toCombinatorialMap.edgeInv_invol]
    rw [← hEq]
    exact hface (e x) (hedge x hx)
  have hrot (x : D) (hx : x ∈ U) :
      B.map.toCombinatorialMap.rot x ∈ U := by
    have hfsymm : f.symm = e.symm * B.map.toCombinatorialMap.rot := by
      change (B.map.toCombinatorialMap.rot.symm * e)⁻¹ =
        e.symm * B.map.toCombinatorialMap.rot
      rw [mul_inv_rev]
      simp only [Equiv.Perm.inv_def, Equiv.symm_symm]
    have hEq : B.map.toCombinatorialMap.rot x = e (f.symm x) := by
      rw [hfsymm, Equiv.Perm.mul_apply]
      exact (e.apply_symm_apply (B.map.toCombinatorialMap.rot x)).symm
    rw [hEq]
    exact hedge (f.symm x) (hfaceInv x hx)
  have hedgeSymm (x : D) : e.symm x = e x := by
    apply e.injective
    simp [e, B.map.toCombinatorialMap.edgeInv_invol]
  have hstep {x y : D} (hx : x ∈ U)
      (hxy : y = B.map.toCombinatorialMap.rot x ∨
        y = B.map.toCombinatorialMap.rot.symm x ∨
        y = e x ∨ y = e.symm x) : y ∈ U := by
    rcases hxy with hxy | hxy | hxy | hxy
    · rw [hxy]
      exact hrot x hx
    · rw [hxy]
      exact hrotSymm x hx
    · rw [hxy]
      exact hedge x hx
    · rw [hxy, hedgeSymm]
      exact hedge x hx
  cases hpath : B.leftPath.darts with
  | nil =>
      have hlen := B.leftPath.darts_length
      simp [hpath] at hlen
      have hpos := B.left_length_pos
      omega
  | cons a rest =>
      have hseed : a ∈ U := by
        change a ∈ pathCutLeftDarts B P ∨ a ∈ pathCutRightDarts B P
        exact Or.inl ⟨a, Or.inl ((mem_pathCutLeftOuterArc_iff B a).2
          (by simp [hpath])), Relation.ReflTransGen.refl⟩
      have hconn := B.planar.1 a d
      have hd : d ∈ U := by
        induction hconn with
        | refl => exact hseed
        | tail hconn hxy ih => exact hstep ih hxy
      change d ∈ pathCutLeftDarts B P ∨ d ∈ pathCutRightDarts B P at hd
      exact hd

end DirectedDistances.PlanarMap
