module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfFaces
public import DirectedDistances.PlanarMap.PlanarPathCutRightBase
import DirectedDistances.PlanarMap.FiniteBipolarIncomingInterval

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PlanarMap
open Equiv



@[expose] def pathCutRightHalfBoundaryDarts {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) : Set D :=
  {d | (d ∈ pathCutRightHalfDarts B P ∧ B.map.IsOuter d) ∨
    d ∈ P.darts}



theorem pathCutRightHalfBoundaryDarts_subset
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    pathCutRightHalfBoundaryDarts B P ⊆ pathCutRightHalfDarts B P := by
  intro d hd
  rcases hd with ⟨hd, _⟩ | hp
  · exact hd
  · exact pathCutRightHalf_path_mem B P hp



theorem pathCutRightHalf_faceSucc_eq_firstReturn {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    ((pathCutRightHalfMap B P).faceSucc d).1 =
      (firstReturn B.map.toCombinatorialMap.rot.symm
        (pathCutRightHalfDarts B P)
        ⟨B.map.toCombinatorialMap.edgeInv d.1,
          pathCutRightHalf_edgeInv_mem B P d.2⟩ : D) := by
  classical
  let S := pathCutRightHalfDarts B P
  have h := firstReturnPerm_symm B.map.toCombinatorialMap.rot S
  change ((firstReturnPerm B.map.toCombinatorialMap.rot S).symm
      (restrictedPerm B.map.toCombinatorialMap.edgeInv S
        (fun x hx => pathCutRightHalf_edgeInv_mem B P hx) d)).1 = _
  rw [restrictedPerm_apply, h]
  rfl



theorem pathCutRightHalf_faceSucc_eq_base_of_mem {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {d : D} (hd : d ∈ pathCutRightHalfDarts B P)
    (hface : B.map.toCombinatorialMap.faceSucc d ∈ pathCutRightHalfDarts B P) :
    ((pathCutRightHalfMap B P).faceSucc ⟨d, hd⟩).1 =
      B.map.toCombinatorialMap.faceSucc d := by
  exact congrArg Subtype.val (pathCutRightHalf_faceSucc_eq B P hd hface)



theorem pathCutRightHalf_faceSucc_eq_base_of_inner_offSeam
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {d : D} (hd : d ∈ pathCutRightHalfDarts B P)
    (hinner : ¬ B.map.IsOuter d)
    (hoffSeam : d ∉ pathCutSeamDarts B P) :
    ((pathCutRightHalfMap B P).faceSucc ⟨d, hd⟩).1 =
      B.map.toCombinatorialMap.faceSucc d := by
  apply pathCutRightHalf_faceSucc_eq_base_of_mem B P hd
  change d ∈ pathCutRightDarts B P ∪ pathCutSeamDarts B P at hd
  have hright : d ∈ pathCutRightDarts B P := by
    rcases hd with hright | hseam
    · exact hright
    · exact (hoffSeam hseam).elim
  exact Or.inl (pathCutRight_faceSucc_mem_of_inner B P hright hinner)



theorem pathCutRightHalf_faceSucc_eq_base_of_rightOuterArc
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {d : D} (hd : d ∈ pathCutRightOuterArc B)
    (hnext : B.map.toCombinatorialMap.faceSucc d ∈ pathCutRightOuterArc B) :
    ((pathCutRightHalfMap B P).faceSucc
      ⟨d, Or.inl ⟨d, Or.inl hd, Relation.ReflTransGen.refl⟩⟩).1 =
      B.map.toCombinatorialMap.faceSucc d := by
  have hnextRight : B.map.toCombinatorialMap.faceSucc d ∈ pathCutRightDarts B P :=
    pathCutRight_faceSucc_mem_of_outerArc B P hd hnext
  exact pathCutRightHalf_faceSucc_eq_base_of_mem B P
    (Or.inl ⟨d, Or.inl hd, Relation.ReflTransGen.refl⟩)
    (Or.inl hnextRight)


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


private theorem inner_right_not_boundary {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutRightDarts B P) (hi : ¬ B.map.IsOuter d) :
    d ∉ pathCutRightHalfBoundaryDarts B P := by
  rintro (⟨_, ho⟩ | hp)
  · exact hi ho
  · exact Set.disjoint_left.mp (leftDarts_rightDarts_disjoint B P)
      (pathCut_pathDart_mem_left B P hp) hd

private theorem not_boundary_inner_right {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutRightHalfDarts B P)
    (hb : d ∉ pathCutRightHalfBoundaryDarts B P) :
    d ∈ pathCutRightDarts B P ∧ ¬ B.map.IsOuter d := by
  refine ⟨?_, fun ho => hb (.inl ⟨hd, ho⟩)⟩
  rcases hd with hr | (hp | hp)
  · exact hr
  · exact (hb (.inr hp)).elim
  · have h := pathCut_pathDart_flip_mem_right B P hp
    simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h



theorem pathCutRightHalf_faceOrbit_iff {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P})
    (hwhole : ∀ e : D,
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc d.1 e →
        e ∈ pathCutRightHalfDarts B P)
    (e : {e : D // e ∈ pathCutRightHalfDarts B P}) :
    Equiv.Perm.SameCycle (pathCutRightHalfMap B P).faceSucc d e ↔
      Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc d.1 e.1 := by
  constructor
  · intro h
    obtain ⟨k, hk, hpow⟩ := h.exists_pow_eq'
    have hiter : ((pathCutRightHalfMap B P).faceSucc : _ → _)^[k] d = e := by
      simpa only [perm_iterate_eq_pow] using hpow
    have hval := congrArg Subtype.val hiter
    change (((closedHalfCombinatorialMap B.map (pathCutRightHalfDarts B P)
      (fun x hx => pathCutRightHalf_edgeInv_mem B P hx)).faceSucc : _ → _)^[k] d).1 =
        e.1 at hval
    rw [closedHalf_faceSucc_iterate_eq B.map (pathCutRightHalfDarts B P)
      (fun x hx => pathCutRightHalf_edgeInv_mem B P hx) d hwhole k] at hval
    have hcycle : Equiv.Perm.SameCycle B.map.toCombinatorialMap.faceSucc d.1
        ((B.map.toCombinatorialMap.faceSucc : D → D)^[k] d.1) := by
      refine ⟨(k : ℤ), ?_⟩
      simp only [zpow_natCast]
      rw [← perm_iterate_eq_pow]
    exact hcycle.trans (hval.sameCycle B.map.toCombinatorialMap.faceSucc)
  · intro h
    obtain ⟨k, hk, hpow⟩ := h.exists_pow_eq'
    have hiter : (B.map.toCombinatorialMap.faceSucc : D → D)^[k] d.1 = e.1 := by
      simpa only [perm_iterate_eq_pow] using hpow
    have hhalfIter := closedHalf_faceSucc_iterate_eq B.map
      (pathCutRightHalfDarts B P)
      (fun x hx => pathCutRightHalf_edgeInv_mem B P hx) d hwhole k
    have hiter' : ((pathCutRightHalfMap B P).faceSucc : _ → _)^[k] d = e := by
      change ((closedHalfCombinatorialMap B.map (pathCutRightHalfDarts B P)
        (fun x hx => pathCutRightHalf_edgeInv_mem B P hx)).faceSucc : _ → _)^[k] d = e
      rw [hhalfIter]
      apply Subtype.ext
      exact hiter
    refine ⟨(k : ℤ), ?_⟩
    simp only [zpow_natCast]
    rw [← perm_iterate_eq_pow]
    exact hiter'


private theorem inner_face_whole_right {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutRightDarts B P) (hi : ¬ B.map.IsOuter d)
    {e : D} (he : B.map.toCombinatorialMap.faceSucc.SameCycle d e) :
    e ∈ pathCutRightDarts B P ∧ ¬ B.map.IsOuter e := by
  obtain ⟨k, _, hk⟩ := he.exists_pow_eq'
  have hiter (j : ℕ) :
      (B.map.toCombinatorialMap.faceSucc ^ j) d ∈ pathCutRightDarts B P ∧
        ¬ B.map.IsOuter ((B.map.toCombinatorialMap.faceSucc ^ j) d) := by
    induction j with
    | zero => simpa only [pow_zero, Perm.one_apply] using And.intro hd hi
    | succ j ih =>
        rw [pow_succ', Perm.mul_apply]
        refine ⟨pathCutRight_faceSucc_mem_of_inner B P ih.1 ih.2, ?_⟩
        intro ho
        exact ih.2 (Perm.sameCycle_apply_right.mp ho)
  exact hk ▸ hiter k




theorem pathCutRightHalf_inner_face_contained {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutRightHalfDarts B P)
    (hb : d ∉ pathCutRightHalfBoundaryDarts B P) :
    ¬ B.map.IsOuter d ∧
      ∀ e : D, B.map.toCombinatorialMap.faceSucc.SameCycle d e →
        e ∈ pathCutRightHalfDarts B P ∧
          e ∉ pathCutRightHalfBoundaryDarts B P := by
  obtain ⟨hl, hi⟩ := not_boundary_inner_right B P hd hb
  refine ⟨hi, ?_⟩
  intro e he
  obtain ⟨hel, hei⟩ := inner_face_whole_right B P hl hi he
  exact ⟨Or.inl hel, inner_right_not_boundary B P hel hei⟩




theorem pathCutRightHalf_inner_faceOrbit_iff {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P})
    (hb : d.1 ∉ pathCutRightHalfBoundaryDarts B P)
    (e : {e : D // e ∈ pathCutRightHalfDarts B P}) :
    (pathCutRightHalfMap B P).faceSucc.SameCycle d e ↔
      B.map.toCombinatorialMap.faceSucc.SameCycle d.1 e.1 := by
  exact pathCutRightHalf_faceOrbit_iff B P d
    (fun e he => ((pathCutRightHalf_inner_face_contained B P d.2 hb).2 e he).1) e



theorem pathCutRightHalf_innerFacesDegreeThree {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P})
    (hb : d.1 ∉ pathCutRightHalfBoundaryDarts B P) :
    (pathCutRightHalfMap B P).faceSucc
        ((pathCutRightHalfMap B P).faceSucc ((pathCutRightHalfMap B P).faceSucc d)) = d ∧
      (pathCutRightHalfMap B P).faceSucc d ≠ d ∧
      (pathCutRightHalfMap B P).faceSucc ((pathCutRightHalfMap B P).faceSucc d) ≠ d := by
  let f := (pathCutRightHalfMap B P).faceSucc
  let g := B.map.toCombinatorialMap.faceSucc
  have hc := pathCutRightHalf_inner_face_contained B P d.2 hb
  have hwhole : ∀ e, g.SameCycle d.1 e → e ∈ pathCutRightHalfDarts B P :=
    fun e he => (hc.2 e he).1
  have h₁ : (f d).1 = g d.1 :=
    pathCutRightHalf_faceSucc_eq_base_of_mem B P d.2
      (hwhole _ (Perm.SameCycle.refl g d.1).apply_right)
  have h₂ : (f (f d)).1 = g (g d.1) := by
    rw [pathCutRightHalf_faceSucc_eq_base_of_mem B P (f d).2]
    · rw [h₁]
    · rw [h₁]
      exact hwhole _ (Perm.SameCycle.refl g d.1).apply_right.apply_right
  have h₃ : (f (f (f d))).1 = g (g (g d.1)) := by
    rw [pathCutRightHalf_faceSucc_eq_base_of_mem B P (f (f d)).2]
    · rw [h₂]
    · rw [h₂]
      exact hwhole _ (Perm.SameCycle.refl g d.1).apply_right.apply_right.apply_right
  obtain ⟨ht, hn₁, hn₂⟩ := B.innerFacesDegreeThree d.1 hc.1
  exact ⟨Subtype.ext (h₃.trans ht),
    fun h => hn₁ (h₁.symm.trans (congrArg Subtype.val h)),
    fun h => hn₂ (h₂.symm.trans (congrArg Subtype.val h))⟩


private theorem right_arc_flip {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {p : D}
    (hp : p ∈ B.rightPath.darts) :
    B.map.edgeInv p ∈ pathCutRightOuterArc B := by
  apply (mem_pathCutRightOuterArc_iff B _).mpr
  exact List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, rfl⟩

private theorem boundary_iff_right_or_path {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) (d : D) :
    d ∈ pathCutRightHalfBoundaryDarts B P ↔
      (∃ p ∈ B.rightPath.darts, d = B.map.edgeInv p) ∨ d ∈ P.darts := by
  constructor
  · rintro (⟨hd, ho⟩ | hp)
    · rcases (isOuter_iff_mem_outerArcs B d).mp ho with hl | hr
      · have hdl : d ∈ pathCutLeftDarts B P :=
          ⟨d, Or.inl hl, Relation.ReflTransGen.refl⟩
        rcases hd with hd | (hp | hp)
        · exact (Set.disjoint_left.mp (leftDarts_rightDarts_disjoint B P) hdl hd).elim
        · exact Or.inr hp
        · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
          have hn := (B.map.tail_iff _ (B.noMissingDarts _)).mp (P.edge_step i).2.1
          rw [hi, B.map.edgeInv_invol] at hn
          exact (hn hl.2.1).elim
      · obtain ⟨p, hp, hpd⟩ := List.mem_map.mp ((mem_pathCutRightOuterArc_iff B d).mp hr)
        exact Or.inl ⟨p, List.mem_reverse.mp hp, hpd.symm⟩
    · exact Or.inr hp
  · rintro (⟨p, hp, rfl⟩ | hp)
    · have ha := right_arc_flip B hp
      exact Or.inl ⟨Or.inl ⟨_, Or.inl ha, Relation.ReflTransGen.refl⟩, ha.2.2⟩
    · exact Or.inr hp

private theorem half_boundary_orbit_closed {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {d e : {d : D // d ∈ pathCutRightHalfDarts B P}}
    (hd : d.1 ∈ pathCutRightHalfBoundaryDarts B P)
    (he : (pathCutRightHalfMap B P).faceSucc.SameCycle d e) :
    e.1 ∈ pathCutRightHalfBoundaryDarts B P := by
  by_contra hn
  have hbase := (pathCutRightHalf_inner_faceOrbit_iff B P e hn d).mp he.symm
  exact ((pathCutRightHalf_inner_face_contained B P e.2 hn).2 d.1 hbase).2 hd

private theorem half_faceSucc_vertex {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    dartTailVertex B.map ((pathCutRightHalfMap B P).faceSucc d).1 =
      dartHeadVertex B.map d.1 := by
  rw [pathCutRightHalf_faceSucc_eq_firstReturn]
  apply Quotient.sound
  change B.map.rot.SameCycle
    ((B.map.rot.symm : D → D)^[firstReturnTime B.map.rot.symm
      (pathCutRightHalfDarts B P)
      ⟨B.map.edgeInv d.1, pathCutRightHalf_edgeInv_mem B P d.2⟩] (B.map.edgeInv d.1))
    (B.map.edgeInv d.1)
  rw [perm_iterate_eq_pow]
  exact (Perm.SameCycle.pow_left (Perm.SameCycle.refl B.map.rot.symm
    (B.map.edgeInv d.1))).of_inv


private theorem right_boundary_faceSucc_get {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (i : ℕ) (hi : i + 1 < r) :
    B.map.toCombinatorialMap.faceSucc
        (B.map.edgeInv (B.rightPath.darts.get ⟨i + 1, by rw [B.rightPath.darts_length]; exact hi⟩)) =
      B.map.edgeInv (B.rightPath.darts.get ⟨i, by rw [B.rightPath.darts_length]; omega⟩) := by
  let xs := B.leftPath.darts ++ B.rightPath.darts.reverse.map B.map.edgeInv
  have hnodup : xs.Nodup := by
    simpa [xs] using B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup
  have hlen : xs.length = ℓ + r := by
    simp [xs, B.leftPath.darts_length, B.rightPath.darts_length]
  have hget (k : ℕ) (hk : k < r) :
      xs[ℓ + (r - 1 - k)]'(by rw [hlen]; omega) =
        B.map.edgeInv (B.rightPath.darts.get ⟨k, by rw [B.rightPath.darts_length]; exact hk⟩) := by
    dsimp [xs]
    rw [List.getElem_append_right (by rw [B.leftPath.darts_length]; omega)]
    simp only [B.leftPath.darts_length, Nat.add_sub_cancel_left, List.getElem_map,
      List.getElem_reverse, B.rightPath.darts_length]
    apply congrArg B.map.edgeInv
    apply congrArg B.rightPath.darts.get
    apply Fin.ext
    change r - 1 - (r - 1 - k) = k
    omega
  let d := B.map.edgeInv (B.rightPath.darts.get
    ⟨i + 1, by rw [B.rightPath.darts_length]; exact hi⟩)
  have hdOuter : B.map.IsOuter d := (right_arc_flip B (List.get_mem _ _)).2.2
  have hdWord : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr hdOuter
  have hface : B.map.toCombinatorialMap.faceSucc d = xs.formPerm d := by
    rw [B.outerSplit.1.2.2 d hdWord]
    simpa [xs] using congrArg (fun p : Perm D => p d)
      (List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1)
  let j := ℓ + (r - 1 - (i + 1))
  have hj : j < xs.length := by rw [hlen]; dsimp [j]; omega
  have hjnext : j + 1 = ℓ + (r - 1 - i) := by dsimp [j]; omega
  have hmod : (j + 1) % xs.length = j + 1 :=
    Nat.mod_eq_of_lt (by rw [hlen]; dsimp [j]; omega)
  change B.map.toCombinatorialMap.faceSucc d = _
  rw [hface]
  dsimp only [d]
  rw [← hget (i + 1) hi]
  change xs.formPerm (xs[j]'hj) = _
  rw [List.formPerm_apply_getElem xs hnodup j hj]
  simp only [hmod]
  simpa only [hjnext] using hget i (by omega)

private theorem right_half_facePred_get {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (i : ℕ) (hi : i + 1 < r)
    (d : {d : D // d ∈ pathCutRightHalfDarts B P})
    (hd : d.1 = B.map.edgeInv (B.rightPath.darts.get
      ⟨i, by rw [B.rightPath.darts_length]; omega⟩)) :
    (((pathCutRightHalfMap B P).faceSucc).symm d).1 =
      B.map.edgeInv (B.rightPath.darts.get
        ⟨i + 1, by rw [B.rightPath.darts_length]; exact hi⟩) := by
  let p := B.rightPath.darts.get ⟨i + 1, by rw [B.rightPath.darts_length]; exact hi⟩
  have hp : B.map.edgeInv p ∈ pathCutRightHalfDarts B P :=
    Or.inl ⟨_, Or.inl (right_arc_flip B (List.get_mem _ _)), Relation.ReflTransGen.refl⟩
  let e : {d : D // d ∈ pathCutRightHalfDarts B P} := ⟨B.map.edgeInv p, hp⟩
  have he : (pathCutRightHalfMap B P).faceSucc e = d := by
    apply Subtype.ext
    have hs : B.map.toCombinatorialMap.faceSucc e.1 = d.1 :=
      (right_boundary_faceSucc_get B i hi).trans hd.symm
    rw [pathCutRightHalf_faceSucc_eq_base_of_mem B P e.2 (hs.symm ▸ d.2), hs]
  have h := congrArg (pathCutRightHalfMap B P).faceSucc.symm he
  rw [Equiv.symm_apply_apply] at h
  exact congrArg Subtype.val h.symm

private theorem half_facePred_vertex {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (d : {d : D // d ∈ pathCutRightHalfDarts B P}) :
    dartHeadVertex B.map (((pathCutRightHalfMap B P).faceSucc).symm d).1 =
      dartTailVertex B.map d.1 := by
  have h := half_faceSucc_vertex B P (((pathCutRightHalfMap B P).faceSucc).symm d)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm



theorem pathCutRightHalf_boundary_single_orbit {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    ∃ d₀ : {d : D // d ∈ pathCutRightHalfDarts B P},
      d₀.1 ∈ pathCutRightHalfBoundaryDarts B P ∧
      ∀ e : {d : D // d ∈ pathCutRightHalfDarts B P},
        (pathCutRightHalfMap B P).faceSucc.SameCycle d₀ e ↔
          e.1 ∈ pathCutRightHalfBoundaryDarts B P := by
  let H := {d : D // d ∈ pathCutRightHalfDarts B P}
  let f : Perm H := (pathCutRightHalfMap B P).faceSucc.symm
  let L (i : Fin r) : H :=
    ⟨B.map.edgeInv (B.rightPath.darts.get
        ⟨i.val, by rw [B.rightPath.darts_length]; exact i.isLt⟩),
      Or.inl ⟨_, Or.inl (right_arc_flip B (List.get_mem _ _)), Relation.ReflTransGen.refl⟩⟩
  let R (i : Fin n) : H :=
    ⟨P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩,
      pathCutRightHalf_path_mem B P (List.get_mem _ _)⟩
  let z : H := L ⟨0, B.right_length_pos⟩
  have hz : z.1 ∈ pathCutRightHalfBoundaryDarts B P :=
    (boundary_iff_right_or_path B P z.1).mpr (.inl ⟨_, List.get_mem _ _, rfl⟩)
  have hL : ∀ (i : ℕ) (hi : i < r), f.SameCycle z (L ⟨i, hi⟩) := by
    intro i
    induction i with
    | zero => intro hi; exact Perm.SameCycle.rfl
    | succ i ih =>
        intro hi
        have hs : f (L ⟨i, by omega⟩) = L ⟨i + 1, hi⟩ :=
          Subtype.ext (right_half_facePred_get B P i hi _ rfl)
        exact hs ▸ (ih (by omega)).apply_right
  have hR : ∀ (i : ℕ) (hi : i < n), f.SameCycle z (R ⟨i, hi⟩) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
        intro hi
        let a : Fin P.darts.length := ⟨i, by rw [P.darts_length]; exact hi⟩
        let d : H := R ⟨i, hi⟩
        let e : H := f d
        have hdB : d.1 ∈ pathCutRightHalfBoundaryDarts B P :=
          Or.inr (List.get_mem _ a)
        have heB : e.1 ∈ pathCutRightHalfBoundaryDarts B P :=
          half_boundary_orbit_closed B P hdB (Perm.SameCycle.rfl.apply_right.of_inv)
        have hv : dartHeadVertex B.map e.1 = dartTailVertex B.map (P.darts.get a) :=
          half_facePred_vertex B P d
        have hecycle : f.SameCycle z e := by
          rcases (boundary_iff_right_or_path B P e.1).mp heB with ⟨p, hp, hep⟩ | heR
          · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
            have hjlt : j.val < r := by simpa only [B.rightPath.darts_length] using j.isLt
            by_cases hj0 : j.val = 0
            · have hez : e = z := by
                apply Subtype.ext
                exact hep.trans (congrArg B.map.edgeInv
                  (hj.symm.trans (congrArg B.rightPath.darts.get (Fin.ext hj0))))
              exact hez ▸ Perm.SameCycle.rfl
            · let k : Fin r := ⟨j.val - 1, by omega⟩
              have hpred : f (L k) = e := by
                apply Subtype.ext
                have hs := right_half_facePred_get B P (j.val - 1) (by omega) (L k) rfl
                exact hs.trans ((congrArg B.map.edgeInv
                  ((congrArg B.rightPath.darts.get (Fin.ext (by dsimp; omega))).trans hj)).trans hep.symm)
              have hde : L k = d := f.injective hpred
              have hn : ¬ B.map.tail (L k).1 :=
                (B.map.tail_iff _ (B.noMissingDarts _)).mp
                  (B.rightPath.edge_step ⟨k.val, by rw [B.rightPath.darts_length]; exact k.isLt⟩).2.1
              have ht : B.map.tail d.1 := (P.edge_step a).2.1
              exact (hn (hde.symm ▸ ht)).elim
          · obtain ⟨j, hj⟩ := List.mem_iff_get.mp heR
            have hjlt : j.val < n := by simpa only [P.darts_length] using j.isLt
            have hhead : dartHeadVertex B.map (P.darts.get j) =
                dartTailVertex B.map (P.darts.get a) := by rw [hj]; exact hv
            have hverts := (P.edge_step j).2.2.2.trans
              (hhead.trans (P.edge_step a).2.2.1.symm)
            have hidx := congrArg Fin.val (P.vertices_nodup.get_inj_iff.mp hverts)
            have hji : j.val < i := by dsimp [a] at hidx; omega
            have heq : e = R ⟨j.val, hjlt⟩ := Subtype.ext hj.symm
            exact heq ▸ ih j.val hji hjlt
        exact Perm.sameCycle_apply_right.mp hecycle
  refine ⟨z, hz, ?_⟩
  intro e
  constructor
  · exact half_boundary_orbit_closed B P hz
  · intro he
    apply Perm.SameCycle.of_inv (f := (pathCutRightHalfMap B P).faceSucc)
    rcases (boundary_iff_right_or_path B P e.1).mp he with ⟨p, hp, hep⟩ | heR
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
      have hilt : i.val < r := by simpa only [B.rightPath.darts_length] using i.isLt
      have heq : L ⟨i.val, hilt⟩ = e :=
        Subtype.ext ((congrArg B.map.edgeInv hi).trans hep.symm)
      exact heq ▸ hL i.val hilt
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp heR
      have hilt : i.val < n := by simpa only [P.darts_length] using i.isLt
      have heq : R ⟨i.val, hilt⟩ = e := Subtype.ext hi
      exact heq ▸ hR i.val hilt

private theorem contained_inner_not_boundary {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hi : ¬ B.map.IsOuter d)
    (hwhole : ∀ e : D, B.map.toCombinatorialMap.faceSucc.SameCycle d e →
      e ∈ pathCutRightHalfDarts B P) :
    d ∉ pathCutRightHalfBoundaryDarts B P := by
  let f := B.map.toCombinatorialMap.faceSucc
  have hex : ∃ e : D, f.SameCycle d e ∧ ¬ B.map.tail e := by
    rcases (innerFace_has_both_boundary_orientations B d hi).2 with ht | ht | ht
    · exact ⟨d, Perm.SameCycle.rfl, ht⟩
    · exact ⟨f d, Perm.SameCycle.rfl.apply_right, ht⟩
    · exact ⟨f (f d), Perm.SameCycle.rfl.apply_right.apply_right, ht⟩
  obtain ⟨e, he, ht⟩ := hex
  have hei : ¬ B.map.IsOuter e := fun ho => hi (ho.trans he.symm)
  have heb : e ∉ pathCutRightHalfBoundaryDarts B P := by
    rintro (⟨_, ho⟩ | hp)
    · exact hei ho
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
      exact ht (P.edge_step i).2.1
  have hel := (not_boundary_inner_right B P (hwhole e he) heb).1
  have hdl := (inner_face_whole_right B P hel hei he.symm).1
  exact inner_right_not_boundary B P hdl hi




theorem pathCutRightHalf_numFaces {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    (pathCutRightHalfMap B P).numFaces =
      Nat.card {q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap //
        q ≠ faceClass B.map.toCombinatorialMap B.map.outer ∧
          ∀ d : D, faceClass B.map.toCombinatorialMap d = q →
            d ∈ pathCutRightHalfDarts B P} + 1 := by
  classical
  let M := B.map.toCombinatorialMap
  let A := pathCutRightHalfMap B P
  let H := {d : D // d ∈ pathCutRightHalfDarts B P}
  obtain ⟨z, hz, hzc⟩ := pathCutRightHalf_boundary_single_orbit B P
  let I := {q : CombinatorialMap.FaceQuotient A // q ≠ faceClass A z}
  let J := {q : CombinatorialMap.FaceQuotient M //
    q ≠ faceClass M B.map.outer ∧
      ∀ d : D, faceClass M d = q → d ∈ pathCutRightHalfDarts B P}
  have hrep (q : I) : q.1.out.1 ∉ pathCutRightHalfBoundaryDarts B P := by
    intro hb
    apply q.2
    calc
      q.1 = faceClass A q.1.out := (Quotient.out_eq q.1).symm
      _ = faceClass A z := Quotient.sound ((hzc q.1.out).mpr hb).symm
  have hclass (q : I) :
      faceClass M q.1.out.1 ≠ faceClass M B.map.outer ∧
        ∀ d : D, faceClass M d = faceClass M q.1.out.1 →
          d ∈ pathCutRightHalfDarts B P := by
    have hc := pathCutRightHalf_inner_face_contained B P q.1.out.2 (hrep q)
    refine ⟨fun h => hc.1 (Quotient.exact h).symm, ?_⟩
    intro d hd
    exact (hc.2 d (Quotient.exact hd.symm)).1
  let F : I → J := fun q => ⟨faceClass M q.1.out.1, hclass q⟩
  have hinj : Function.Injective F := by
    intro q q' hq
    have hbase : M.faceSucc.SameCycle q.1.out.1 q'.1.out.1 :=
      Quotient.exact (congrArg Subtype.val hq)
    have hhalf : A.faceSucc.SameCycle q.1.out q'.1.out :=
      (pathCutRightHalf_inner_faceOrbit_iff B P q.1.out (hrep q) q'.1.out).mpr hbase
    apply Subtype.ext
    calc
      q.1 = faceClass A q.1.out := (Quotient.out_eq q.1).symm
      _ = faceClass A q'.1.out := Quotient.sound hhalf
      _ = q'.1 := Quotient.out_eq q'.1
  have hsurj : Function.Surjective F := by
    intro q
    let d : D := q.1.out
    have hdq : faceClass M d = q.1 := Quotient.out_eq q.1
    have hd : d ∈ pathCutRightHalfDarts B P := q.2.2 d hdq
    have hi : ¬ B.map.IsOuter d := by
      intro ho
      exact q.2.1 (hdq.symm.trans (Quotient.sound ho.symm))
    have hwhole : ∀ e : D, M.faceSucc.SameCycle d e →
        e ∈ pathCutRightHalfDarts B P := by
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
      (pathCutRightHalf_inner_faceOrbit_iff B P qh.1.out (hrep qh) dh).mp hh
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




theorem pathCut_inner_face_partition {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hq : q ≠ faceClass B.map.toCombinatorialMap B.map.outer) :
    ((∀ d : D, faceClass B.map.toCombinatorialMap d = q →
        d ∈ pathCutLeftHalfDarts B P) ∨
      (∀ d : D, faceClass B.map.toCombinatorialMap d = q →
        d ∈ pathCutRightHalfDarts B P)) ∧
    ¬ ((∀ d : D, faceClass B.map.toCombinatorialMap d = q →
        d ∈ pathCutLeftHalfDarts B P) ∧
      (∀ d : D, faceClass B.map.toCombinatorialMap d = q →
        d ∈ pathCutRightHalfDarts B P)) := by
  classical
  let M := B.map.toCombinatorialMap
  let d : D := q.out
  have hdq : faceClass M d = q := Quotient.out_eq q
  have hi : ¬ B.map.IsOuter d := by
    intro ho
    exact hq (hdq.symm.trans (Quotient.sound ho.symm))
  have hcycle {e : D} (he : faceClass M e = q) : M.faceSucc.SameCycle d e :=
    Quotient.exact (hdq.trans he.symm)
  constructor
  · rcases pathCut_darts_cover B P d with hl | hr
    · exact Or.inl (fun e he => Or.inl (inner_face_whole_left B P hl hi (hcycle he)).1)
    · exact Or.inr (fun e he => Or.inl (inner_face_whole_right B P hr hi (hcycle he)).1)
  · rintro ⟨hl, hr⟩
    have hex : ∃ e : D, M.faceSucc.SameCycle d e ∧ B.map.tail e := by
      rcases (innerFace_has_both_boundary_orientations B d hi).1 with ht | ht | ht
      · exact ⟨d, Perm.SameCycle.rfl, ht⟩
      · exact ⟨M.faceSucc d, Perm.SameCycle.rfl.apply_right, ht⟩
      · exact ⟨M.faceSucc (M.faceSucc d), Perm.SameCycle.rfl.apply_right.apply_right, ht⟩
    obtain ⟨e, he, ht⟩ := hex
    have heq : faceClass M e = q := (Quotient.sound he.symm).trans hdq
    have hei : ¬ B.map.IsOuter e := fun ho => hi (ho.trans he.symm)
    have hwhole : ∀ a : D, M.faceSucc.SameCycle e a → a ∈ pathCutRightHalfDarts B P := by
      intro a ha
      exact hr a ((Quotient.sound ha.symm).trans heq)
    have heb := contained_inner_not_boundary B P hei hwhole
    have her := (not_boundary_inner_right B P (hr e heq) heb).1
    have hel : e ∈ pathCutLeftDarts B P := by
      rcases hl e heq with hel | (hp | hp)
      · exact hel
      · exact pathCut_pathDart_mem_left B P hp
      · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
        have htp : B.map.tail (B.map.edgeInv e) := hi ▸ (P.edge_step i).2.1
        exact ((B.map.tail_iff e (B.noMissingDarts e)).mp ht htp).elim
    exact Set.disjoint_left.mp (leftDarts_rightDarts_disjoint B P) hel her




theorem pathCutHalves_inner_face_card_sum {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    Nat.card {q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap //
      q ≠ faceClass B.map.toCombinatorialMap B.map.outer ∧
        ∀ d : D, faceClass B.map.toCombinatorialMap d = q →
          d ∈ pathCutLeftHalfDarts B P} +
    Nat.card {q : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap //
      q ≠ faceClass B.map.toCombinatorialMap B.map.outer ∧
        ∀ d : D, faceClass B.map.toCombinatorialMap d = q →
          d ∈ pathCutRightHalfDarts B P} = B.map.toCombinatorialMap.numFaces - 1 := by
  classical
  let M := B.map.toCombinatorialMap
  let Q := CombinatorialMap.FaceQuotient M
  let L : Finset Q := Finset.univ.filter (fun q =>
    q ≠ faceClass M B.map.outer ∧
      ∀ d : D, faceClass M d = q → d ∈ pathCutLeftHalfDarts B P)
  let R : Finset Q := Finset.univ.filter (fun q =>
    q ≠ faceClass M B.map.outer ∧
      ∀ d : D, faceClass M d = q → d ∈ pathCutRightHalfDarts B P)
  let I : Finset Q := Finset.univ.filter (fun q => q ≠ faceClass M B.map.outer)
  have hUnion : L ∪ R = I := by
    ext q
    simp only [L, R, I, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
    · intro hq
      rcases (pathCut_inner_face_partition B P q hq).1 with hl | hr
      · exact Or.inl ⟨hq, hl⟩
      · exact Or.inr ⟨hq, hr⟩
  have hDisjoint : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro q hl hr
    have hl' := (Finset.mem_filter.mp hl).2
    have hr' := (Finset.mem_filter.mp hr).2
    exact (pathCut_inner_face_partition B P q hl'.1).2 ⟨hl'.2, hr'.2⟩
  have hL : Nat.card {q : Q // q ≠ faceClass M B.map.outer ∧
      ∀ d : D, faceClass M d = q → d ∈ pathCutLeftHalfDarts B P} = L.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hR : Nat.card {q : Q // q ≠ faceClass M B.map.outer ∧
      ∀ d : D, faceClass M d = q → d ∈ pathCutRightHalfDarts B P} = R.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hI : I.card = M.numFaces - 1 := by
    have hsub : Fintype.card {q : Q // q ≠ faceClass M B.map.outer} = I.card := by
      rw [Fintype.card_subtype]
    rw [← hsub, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    rfl
  change Nat.card {q : Q // q ≠ faceClass M B.map.outer ∧
      ∀ d : D, faceClass M d = q → d ∈ pathCutLeftHalfDarts B P} +
    Nat.card {q : Q // q ≠ faceClass M B.map.outer ∧
      ∀ d : D, faceClass M d = q → d ∈ pathCutRightHalfDarts B P} = _
  rw [hL, hR, ← Finset.card_union_of_disjoint hDisjoint, hUnion, hI]



theorem pathCutHalves_numFaces_sum {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)] :
    (pathCutLeftHalfMap B P).numFaces + (pathCutRightHalfMap B P).numFaces =
      B.map.toCombinatorialMap.numFaces + 1 := by
  classical
  have hL := pathCutLeftHalf_numFaces B P
  have hR := pathCutRightHalf_numFaces B P
  have hI := pathCutHalves_inner_face_card_sum B P
  have hp : 0 < B.map.toCombinatorialMap.numFaces :=
    Fintype.card_pos_iff.mpr ⟨faceClass B.map.toCombinatorialMap B.map.outer⟩
  omega

end DirectedDistances.PlanarMap
