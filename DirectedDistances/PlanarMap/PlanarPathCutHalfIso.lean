/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfPathProject
public import DirectedDistances.PlanarMap.KMSWMapIsoClass

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

/-! # Transport of the halves of a planar path cut

paper result. The cut dart sets and their induced half maps are transported by
boundary isomorphisms. -/

public section
namespace DirectedDistances.PlanarMap

variable {D D' : Type*} [Fintype D] [DecidableEq D]
  [Fintype D'] [DecidableEq D']
variable {ℓ r n : ℕ}

private theorem pathCut_pathDarts_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d : D) :
    d ∈ P.darts ↔ I.toEquiv d ∈ P'.darts := by
  rw [hP']
  constructor
  · intro hd
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  · intro hd
    rcases List.mem_map.mp hd with ⟨e, he, hde⟩
    apply I.toEquiv.injective at hde
    simpa [hde] using he

private theorem pathCut_leftOuterArc_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (d : D) :
    d ∈ pathCutLeftOuterArc B ↔ I.toEquiv d ∈ pathCutLeftOuterArc B' := by
  rw [mem_pathCutLeftOuterArc_iff, mem_pathCutLeftOuterArc_iff]
  constructor
  · intro hd
    rw [← I.leftDarts]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  · intro hd
    change I.toEquiv d ∈ B'.leftPath.darts at hd
    rw [← I.leftDarts] at hd
    rcases List.mem_map.mp hd with ⟨e, he, hde⟩
    exact I.toEquiv.injective hde ▸ he

private theorem pathCut_rightOuterArc_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') (d : D) :
    d ∈ pathCutRightOuterArc B ↔ I.toEquiv d ∈ pathCutRightOuterArc B' := by
  rw [mem_pathCutRightOuterArc_iff, mem_pathCutRightOuterArc_iff]
  have hrev : B'.rightPath.darts.reverse =
      B.rightPath.darts.reverse.map I.toEquiv := by
    have h := congrArg List.reverse I.rightDarts
    simpa only [List.map_reverse] using h.symm
  have hmap : B'.rightPath.darts.reverse.map B'.map.toCombinatorialMap.edgeInv =
      (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).map I.toEquiv := by
    rw [hrev, List.map_map, List.map_map]
    congr 1
    funext p
    exact (I.edgeInv_comm p).symm
  rw [hmap]
  constructor
  · intro hd
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  · intro hd
    rcases List.mem_map.mp hd with ⟨q, hq, hqd⟩
    apply I.toEquiv.injective at hqd
    exact hqd ▸ hq

private theorem pathCut_seam_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d : D) :
    d ∈ pathCutSeamDarts B P ↔ I.toEquiv d ∈ pathCutSeamDarts B' P' := by
  change (d ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv d ∈ P.darts) ↔
    (I.toEquiv d ∈ P'.darts ∨
      B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) ∈ P'.darts)
  constructor
  · rintro (hd | hd)
    · exact Or.inl ((pathCut_pathDarts_mem_iff I P P' hP' d).mp hd)
    · exact Or.inr (by
        rw [← I.edgeInv_comm]
        exact (pathCut_pathDarts_mem_iff I P P' hP' _).mp hd)
  · rintro (hd | hd)
    · exact Or.inl ((pathCut_pathDarts_mem_iff I P P' hP' d).mpr hd)
    · exact Or.inr (by
        apply (pathCut_pathDarts_mem_iff I P P' hP' _).mpr
        rw [I.edgeInv_comm]
        exact hd)

private theorem pathCut_leftSeeds_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d : D) :
    d ∈ pathCutLeftSeeds B P ↔ I.toEquiv d ∈ pathCutLeftSeeds B' P' := by
  change (d ∈ pathCutLeftOuterArc B ∨ d ∈ P.darts) ↔
    (I.toEquiv d ∈ pathCutLeftOuterArc B' ∨ I.toEquiv d ∈ P'.darts)
  rw [pathCut_leftOuterArc_mem_iff I,
    pathCut_pathDarts_mem_iff I P P' hP']

private theorem pathCut_rightSeeds_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d : D) :
    d ∈ pathCutRightSeeds B P ↔ I.toEquiv d ∈ pathCutRightSeeds B' P' := by
  change (d ∈ pathCutRightOuterArc B ∨
      ∃ p ∈ P.darts, d = B.map.toCombinatorialMap.edgeInv p) ↔
    (I.toEquiv d ∈ pathCutRightOuterArc B' ∨
      ∃ q ∈ P'.darts, I.toEquiv d = B'.map.toCombinatorialMap.edgeInv q)
  rw [pathCut_rightOuterArc_mem_iff I]
  constructor
  · rintro (hd | ⟨p, hp, hdp⟩)
    · exact Or.inl hd
    · refine Or.inr ⟨I.toEquiv p,
        (pathCut_pathDarts_mem_iff I P P' hP' p).mp hp, ?_⟩
      calc
        I.toEquiv d = I.toEquiv (B.map.toCombinatorialMap.edgeInv p) := congrArg _ hdp
        _ = B'.map.toCombinatorialMap.edgeInv (I.toEquiv p) := I.edgeInv_comm p
  · rintro (hd | ⟨q, hq, hdq⟩)
    · exact Or.inl hd
    · let p := I.toEquiv.symm q
      refine Or.inr ⟨p,
        (pathCut_pathDarts_mem_iff I P P' hP' p).mpr (by simpa [p] using hq), ?_⟩
      apply I.toEquiv.injective
      calc
        I.toEquiv d = B'.map.toCombinatorialMap.edgeInv q := hdq
        _ = I.toEquiv (B.map.toCombinatorialMap.edgeInv p) := by
          rw [I.edgeInv_comm]
          simp [p]

private theorem pathCut_leftStep_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d e : D) :
    pathCutLeftStep B P d e ↔
      pathCutLeftStep B' P' (I.toEquiv d) (I.toEquiv e) := by
  change ((e = B.map.toCombinatorialMap.faceSucc d ∧
      (¬ B.map.IsOuter d ∨ (d ∈ pathCutLeftOuterArc B ∧
        e ∈ pathCutLeftOuterArc B))) ∨
      (e = B.map.toCombinatorialMap.edgeInv d ∧ d ∉ pathCutSeamDarts B P)) ↔
    ((I.toEquiv e = B'.map.toCombinatorialMap.faceSucc (I.toEquiv d) ∧
      (¬ B'.map.IsOuter (I.toEquiv d) ∨ (I.toEquiv d ∈ pathCutLeftOuterArc B' ∧
        I.toEquiv e ∈ pathCutLeftOuterArc B'))) ∨
      (I.toEquiv e = B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) ∧
        I.toEquiv d ∉ pathCutSeamDarts B' P'))
  constructor
  · rintro (⟨he, ho⟩ | ⟨he, hs⟩)
    · left
      refine ⟨?_, ?_⟩
      · calc
          I.toEquiv e = I.toEquiv (B.map.toCombinatorialMap.faceSucc d) := congrArg _ he
          _ = B'.map.toCombinatorialMap.faceSucc (I.toEquiv d) := I.faceSucc_comm d
      · rcases ho with h | ⟨hd, hn⟩
        · exact Or.inl (fun h' => h ((I.outer_iff d).mp h'))
        · exact Or.inr ⟨(pathCut_leftOuterArc_mem_iff I d).mp hd,
            (pathCut_leftOuterArc_mem_iff I e).mp hn⟩
    · right
      refine ⟨?_, fun h => hs ((pathCut_seam_mem_iff I P P' hP' d).mpr h)⟩
      calc
        I.toEquiv e = I.toEquiv (B.map.toCombinatorialMap.edgeInv d) := congrArg _ he
        _ = B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) := I.edgeInv_comm d
  · rintro (⟨he, ho⟩ | ⟨he, hs⟩)
    · left
      refine ⟨I.toEquiv.injective (he.trans (I.faceSucc_comm d).symm), ?_⟩
      rcases ho with h | ⟨hd, hn⟩
      · exact Or.inl (fun h' => h ((I.outer_iff d).mpr h'))
      · exact Or.inr ⟨(pathCut_leftOuterArc_mem_iff I d).mpr hd,
          (pathCut_leftOuterArc_mem_iff I e).mpr hn⟩
    · right
      refine ⟨I.toEquiv.injective (he.trans (I.edgeInv_comm d).symm), ?_⟩
      exact fun h => hs ((pathCut_seam_mem_iff I P P' hP' d).mp h)

private theorem pathCut_rightStep_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d e : D) :
    pathCutRightStep B P d e ↔
      pathCutRightStep B' P' (I.toEquiv d) (I.toEquiv e) := by
  change ((e = B.map.toCombinatorialMap.faceSucc d ∧
      (¬ B.map.IsOuter d ∨ (d ∈ pathCutRightOuterArc B ∧
        e ∈ pathCutRightOuterArc B))) ∨
      (e = B.map.toCombinatorialMap.edgeInv d ∧ d ∉ pathCutSeamDarts B P)) ↔
    ((I.toEquiv e = B'.map.toCombinatorialMap.faceSucc (I.toEquiv d) ∧
      (¬ B'.map.IsOuter (I.toEquiv d) ∨ (I.toEquiv d ∈ pathCutRightOuterArc B' ∧
        I.toEquiv e ∈ pathCutRightOuterArc B'))) ∨
      (I.toEquiv e = B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) ∧
        I.toEquiv d ∉ pathCutSeamDarts B' P'))
  constructor
  · rintro (⟨he, ho⟩ | ⟨he, hs⟩)
    · left
      refine ⟨?_, ?_⟩
      · calc
          I.toEquiv e = I.toEquiv (B.map.toCombinatorialMap.faceSucc d) := congrArg _ he
          _ = B'.map.toCombinatorialMap.faceSucc (I.toEquiv d) := I.faceSucc_comm d
      · rcases ho with h | ⟨hd, hn⟩
        · exact Or.inl (fun h' => h ((I.outer_iff d).mp h'))
        · exact Or.inr ⟨(pathCut_rightOuterArc_mem_iff I d).mp hd,
            (pathCut_rightOuterArc_mem_iff I e).mp hn⟩
    · right
      refine ⟨?_, fun h => hs ((pathCut_seam_mem_iff I P P' hP' d).mpr h)⟩
      calc
        I.toEquiv e = I.toEquiv (B.map.toCombinatorialMap.edgeInv d) := congrArg _ he
        _ = B'.map.toCombinatorialMap.edgeInv (I.toEquiv d) := I.edgeInv_comm d
  · rintro (⟨he, ho⟩ | ⟨he, hs⟩)
    · left
      refine ⟨I.toEquiv.injective (he.trans (I.faceSucc_comm d).symm), ?_⟩
      rcases ho with h | ⟨hd, hn⟩
      · exact Or.inl (fun h' => h ((I.outer_iff d).mpr h'))
      · exact Or.inr ⟨(pathCut_rightOuterArc_mem_iff I d).mpr hd,
          (pathCut_rightOuterArc_mem_iff I e).mpr hn⟩
    · right
      refine ⟨I.toEquiv.injective (he.trans (I.edgeInv_comm d).symm), ?_⟩
      exact fun h => hs ((pathCut_seam_mem_iff I P P' hP' d).mp h)

private theorem pathCut_reflTransGen_iff
    {α β : Type*} (e : α ≃ β) (R : α → α → Prop) (S : β → β → Prop)
    (hstep : ∀ a b, R a b ↔ S (e a) (e b)) (a b : α) :
    Relation.ReflTransGen R a b ↔ Relation.ReflTransGen S (e a) (e b) := by
  constructor
  · intro h
    exact Relation.ReflTransGen.lift e (by
      intro x y hxy
      exact (hstep x y).mp hxy) a b h
  · intro h
    have hback : Relation.ReflTransGen R (e.symm (e a)) (e.symm (e b)) :=
      Relation.ReflTransGen.lift e.symm (by
      intro x y hxy
      exact (hstep (e.symm x) (e.symm y)).mpr (by simpa using hxy))
      (e a) (e b) h
    simpa only [Equiv.symm_apply_apply] using hback

/-- Membership in the left cut dart set is preserved and reflected by a
boundary isomorphism when the selected paths correspond. Helper toward -/
theorem pathCutLeftDarts_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d : D) :
    d ∈ pathCutLeftDarts B P ↔ I.toEquiv d ∈ pathCutLeftDarts B' P' := by
  simp only [pathCutLeftDarts, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, hreach⟩
    refine ⟨I.toEquiv a, (pathCut_leftSeeds_mem_iff I P P' hP' a).mp ha, ?_⟩
    exact (pathCut_reflTransGen_iff I.toEquiv _ _
      (pathCut_leftStep_iff I P P' hP') a d).mp hreach
  · rintro ⟨a', ha', hreach'⟩
    let a := I.toEquiv.symm a'
    refine ⟨a, ?_, ?_⟩
    · exact (pathCut_leftSeeds_mem_iff I P P' hP' a).mpr (by simpa [a] using ha')
    · have hback := (pathCut_reflTransGen_iff I.toEquiv _ _
        (pathCut_leftStep_iff I P P' hP') a d).mpr ?_
      · exact hback
      · simpa [a] using hreach'

/-- Membership in the right cut dart set is preserved and reflected by a
boundary isomorphism when the selected paths correspond. Helper toward -/
theorem pathCutRightDarts_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d : D) :
    d ∈ pathCutRightDarts B P ↔ I.toEquiv d ∈ pathCutRightDarts B' P' := by
  simp only [pathCutRightDarts, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, hreach⟩
    refine ⟨I.toEquiv a, (pathCut_rightSeeds_mem_iff I P P' hP' a).mp ha, ?_⟩
    exact (pathCut_reflTransGen_iff I.toEquiv _ _
      (pathCut_rightStep_iff I P P' hP') a d).mp hreach
  · rintro ⟨a', ha', hreach'⟩
    let a := I.toEquiv.symm a'
    refine ⟨a, ?_, ?_⟩
    · exact (pathCut_rightSeeds_mem_iff I P P' hP' a).mpr (by simpa [a] using ha')
    · have hback := (pathCut_reflTransGen_iff I.toEquiv _ _
        (pathCut_rightStep_iff I P P' hP') a d).mpr ?_
      · exact hback
      · simpa [a] using hreach'

/-- Membership in the path seam is preserved and reflected by the boundary
isomorphism. Helper toward `lem-lr-ind` -/
theorem pathCutSeamDarts_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d : D) :
    d ∈ pathCutSeamDarts B P ↔ I.toEquiv d ∈ pathCutSeamDarts B' P' :=
  pathCut_seam_mem_iff I P P' hP' d

/-- Membership in the closed left half dart set is preserved and reflected
by the boundary isomorphism. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfDarts_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d : D) :
    d ∈ pathCutLeftHalfDarts B P ↔ I.toEquiv d ∈ pathCutLeftHalfDarts B' P' := by
  simp only [pathCutLeftHalfDarts, Set.mem_union]
  rw [pathCutLeftDarts_mem_iff I P P' hP', pathCutSeamDarts_mem_iff I P P' hP']

/-- Membership in the closed right half dart set is preserved and reflected
by the boundary isomorphism. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalfDarts_mem_iff
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) (d : D) :
    d ∈ pathCutRightHalfDarts B P ↔ I.toEquiv d ∈ pathCutRightHalfDarts B' P' := by
  simp only [pathCutRightHalfDarts, Set.mem_union]
  rw [pathCutRightDarts_mem_iff I P P' hP', pathCutSeamDarts_mem_iff I P P' hP']

private theorem iterate_congr_of_commute {α β : Type*} (e : α ≃ β)
    (f : α → α) (g : β → β) (hcomm : ∀ x, e (f x) = g (e x))
    (k : ℕ) (x : α) : e (f^[k] x) = g^[k] (e x) := by
  revert x
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact (ih (f x)).trans (congrArg (g^[k]) (hcomm x))

private theorem firstReturnTime_congr {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (S : Set α) (T : Set β)
    [DecidablePred (fun x : α => x ∈ S)]
    [DecidablePred (fun y : β => y ∈ T)]
    (hS : ∀ x, x ∈ S ↔ e x ∈ T)
    (f : Equiv.Perm α) (g : Equiv.Perm β)
    (hcomm : ∀ x, e (f x) = g (e x)) (x : S) :
    firstReturnTime f S x =
      firstReturnTime g T ⟨e x.1, (hS x.1).mp x.2⟩ := by
  let x' : T := ⟨e x.1, (hS x.1).mp x.2⟩
  have hchar := (firstReturnTime_eq_iff f S x (firstReturnTime f S x)).mp rfl
  have htime : firstReturnTime g T x' = firstReturnTime f S x := by
    apply (firstReturnTime_eq_iff g T x' (firstReturnTime f S x)).2
    rcases hchar with ⟨hpos, hret, hbefore⟩
    refine ⟨hpos, ?_, ?_⟩
    · have hiter := iterate_congr_of_commute e f g hcomm
        (firstReturnTime f S x) x.1
      rw [← hiter]
      exact (hS _).mp hret
    · intro j hj hjlt hmem
      apply hbefore j hj hjlt
      have hiter := iterate_congr_of_commute e f g hcomm j x.1
      apply (hS _).mpr
      rw [hiter]
      exact hmem
  exact htime.symm

private theorem firstReturn_congr {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (S : Set α) (T : Set β)
    [DecidablePred (fun x : α => x ∈ S)]
    [DecidablePred (fun y : β => y ∈ T)]
    (hS : ∀ x, x ∈ S ↔ e x ∈ T)
    (f : Equiv.Perm α) (g : Equiv.Perm β)
    (hcomm : ∀ x, e (f x) = g (e x)) (x : S) :
    (e.subtypeEquiv hS) (firstReturn f S x) =
      firstReturn g T ((e.subtypeEquiv hS) x) := by
  let eS : S ≃ T := e.subtypeEquiv hS
  have htime := firstReturnTime_congr e S T hS f g hcomm x
  apply Subtype.ext
  change e ((f : α → α)^[firstReturnTime f S x] x.1) =
    (g : β → β)^[firstReturnTime g T (eS x)] (e x.1)
  rw [htime]
  exact iterate_congr_of_commute e f g hcomm _ x.1




@[expose] noncomputable def halfLeftCongr
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) :
    {d : D // d ∈ pathCutLeftHalfDarts B P} ≃
      {d' : D' // d' ∈ pathCutLeftHalfDarts B' P'} :=
  I.toEquiv.subtypeEquiv (fun d => pathCutLeftHalfDarts_mem_iff I P P' hP' d)




@[expose] noncomputable def halfRightCongr
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv) :
    {d : D // d ∈ pathCutRightHalfDarts B P} ≃
      {d' : D' // d' ∈ pathCutRightHalfDarts B' P'} :=
  I.toEquiv.subtypeEquiv (fun d => pathCutRightHalfDarts_mem_iff I P P' hP' d)




theorem halfLeftCongr_rot
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    halfLeftCongr I P P' hP' ((pathCutLeftHalfMap B P).rot d) =
      (pathCutLeftHalfMap B' P').rot (halfLeftCongr I P P' hP' d) := by
  classical
  change (I.toEquiv.subtypeEquiv
      (fun x => pathCutLeftHalfDarts_mem_iff I P P' hP' x))
      (firstReturnPerm B.map.toCombinatorialMap.rot
        (pathCutLeftHalfDarts B P) d) =
    firstReturnPerm B'.map.toCombinatorialMap.rot
      (pathCutLeftHalfDarts B' P')
        ((I.toEquiv.subtypeEquiv
          (fun x => pathCutLeftHalfDarts_mem_iff I P P' hP' x)) d)
  exact firstReturn_congr I.toEquiv (pathCutLeftHalfDarts B P)
    (pathCutLeftHalfDarts B' P')
    (fun x => pathCutLeftHalfDarts_mem_iff I P P' hP' x)
    B.map.toCombinatorialMap.rot B'.map.toCombinatorialMap.rot I.rot_comm d




theorem halfRightCongr_rot
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    halfRightCongr I P P' hP' ((pathCutRightHalfMap B P).rot d) =
      (pathCutRightHalfMap B' P').rot (halfRightCongr I P P' hP' d) := by
  classical
  change (I.toEquiv.subtypeEquiv
      (fun x => pathCutRightHalfDarts_mem_iff I P P' hP' x))
      (firstReturnPerm B.map.toCombinatorialMap.rot
        (pathCutRightHalfDarts B P) d) =
    firstReturnPerm B'.map.toCombinatorialMap.rot
      (pathCutRightHalfDarts B' P')
        ((I.toEquiv.subtypeEquiv
          (fun x => pathCutRightHalfDarts_mem_iff I P P' hP' x)) d)
  exact firstReturn_congr I.toEquiv (pathCutRightHalfDarts B P)
    (pathCutRightHalfDarts B' P')
    (fun x => pathCutRightHalfDarts_mem_iff I P P' hP' x)
    B.map.toCombinatorialMap.rot B'.map.toCombinatorialMap.rot I.rot_comm d



theorem halfLeftCongr_edgeInv
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    halfLeftCongr I P P' hP'
        ((pathCutLeftHalfDirectedMap B P).edgeInv d) =
      (pathCutLeftHalfDirectedMap B' P').edgeInv
        (halfLeftCongr I P P' hP' d) := by
  apply Subtype.ext
  change I.toEquiv ((pathCutLeftHalfDirectedMap B P).edgeInv d).1 =
    ((pathCutLeftHalfDirectedMap B' P').edgeInv (halfLeftCongr I P P' hP' d)).1
  rw [(pathCutLeftHalf_embedding_fields B P).2.1 d,
    (pathCutLeftHalf_embedding_fields B' P').2.1 (halfLeftCongr I P P' hP' d)]
  exact I.edgeInv_comm d.1



theorem halfLeftCongr_tail
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    (pathCutLeftHalfDirectedMap B' P').tail (halfLeftCongr I P P' hP' d) ↔
      (pathCutLeftHalfDirectedMap B P).tail d := by
  change B'.map.tail (I.toEquiv d.1) ↔ B.map.tail d.1
  exact I.tail_iff d.1




theorem halfLeftCongr_missing
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutLeftHalfDarts B' P')]
    (d : {d : D // d ∈ pathCutLeftHalfDarts B P}) :
    (pathCutLeftHalfDirectedMap B' P').missing (halfLeftCongr I P P' hP' d) ↔
      (pathCutLeftHalfDirectedMap B P).missing d := by
  rfl



theorem halfRightCongr_edgeInv
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    halfRightCongr I P P' hP'
        ((pathCutRightHalfDirectedMap B P).edgeInv d) =
      (pathCutRightHalfDirectedMap B' P').edgeInv
        (halfRightCongr I P P' hP' d) := by
  apply Subtype.ext
  change I.toEquiv ((pathCutRightHalfDirectedMap B P).edgeInv d).1 =
    ((pathCutRightHalfDirectedMap B' P').edgeInv (halfRightCongr I P P' hP' d)).1
  rw [(pathCutRightHalf_embedding_fields B P).2.1 d,
    (pathCutRightHalf_embedding_fields B' P').2.1 (halfRightCongr I P P' hP' d)]
  exact I.edgeInv_comm d.1



theorem halfRightCongr_tail
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    (pathCutRightHalfDirectedMap B' P').tail (halfRightCongr I P P' hP' d) ↔
      (pathCutRightHalfDirectedMap B P).tail d := by
  change B'.map.tail (I.toEquiv d.1) ↔ B.map.tail d.1
  exact I.tail_iff d.1




theorem halfRightCongr_missing
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B')
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (P' : SimpleDirectedDartPath B'.map B'.source B'.sink n)
    (hP' : P'.darts = P.darts.map I.toEquiv)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [DecidablePred (fun d : D' => d ∈ pathCutRightHalfDarts B' P')]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    (pathCutRightHalfDirectedMap B' P').missing (halfRightCongr I P P' hP' d) ↔
      (pathCutRightHalfDirectedMap B P).missing d := by
  rfl

end DirectedDistances.PlanarMap
