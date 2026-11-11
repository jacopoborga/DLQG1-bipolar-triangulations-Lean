/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.MonotoneFamilyCapOrient
public import DirectedDistances.KMSW.RunInfDartPartition
public import DirectedDistances.KMSW.RunBoundaryStackSets

/-! Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of the
two-sided (recurrent iid) KMSW drawing); not a paper result.
Face successor: `kmswInfFaceSucc` in `DirectedDistances/KMSW/InfiniteRotation.lean`.
Five of the six public theorems require `h : BoundaryHitWitnesses w`, consisting only of
`rightHit` and `leftHit`: `R` and `L` each hit every negative integer level.
`cap_border_iff` requires only `hfin`, with no boundary-hit hypothesis.
The `SameCycle` statements alone do not certify face-successor orientation; this rests on
`MonotoneFamilyCapOrient` and the left-wedge definition of `dartBorders`. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the two-sided (recurrent iid) KMSW drawing); not a paper result.
Face successor: `kmswInfFaceSucc` in `DirectedDistances/KMSW/InfiniteRotation.lean`.
Requires only `hfin`, with no `BoundaryHitWitnesses` hypothesis.
The darts bordering a creation cap are exactly its three oriented creation darts. -/
theorem cap_border_iff (j : TriangleCreationTime w) (d : ℕ × Bool) :
    (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d
      (capFace w hfin j) ↔ d ∈ stageTriangleDartList w j :=
  ⟨cap_border_dart_mem w hfin j d, (capFace_spec w hfin j).2 d⟩

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the two-sided (recurrent iid) KMSW drawing); not a paper result.
Face successor: `kmswInfFaceSucc` in `DirectedDistances/KMSW/InfiniteRotation.lean`.
Requires `h : BoundaryHitWitnesses w`: only the coordinate hits `rightHit` and `leftHit`.
These assert that `R` and `L` each hit every negative integer level.
Every dart outside the outer orbit belongs to a creation triangle. -/
private theorem full_triangle_of_not_outer (h : BoundaryHitWitnesses w) (d : ℕ × Bool)
    (hd : ¬ (kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart d) :
    ∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j := by
  classical
  have hL : ∀ a : ℤ, ∃ n, L w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.leftHit (min a (-1)) (min_le_right _ _)
    exact ⟨n, hn.le.trans (min_le_left _ _)⟩
  have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := h.rightHit (max (-a) 1) (le_max_right _ _)
    exact ⟨n, by have hm := le_max_left (-a) 1; omega⟩
  have hne (k : ℤ) : d ≠ futureMapBoundaryDart w h k := by
    intro heq
    apply hd
    rw [heq]
    exact (futureMap_outerOrbit_iff_existsUnique w hfin h _).2
      ⟨k, rfl, fun l hl => futureMapBoundaryDart_injective w h hl.symm⟩
  by_contra ht
  rcases (kmswRunInfDart_boundary_iff_not_triangle w hL hR d).mpr ht with
    ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · have hrange : e ∈ Set.range (fun j : ℕ =>
        kmswLLCreatedEdge w (boundaryHitTime w h (-((j : ℤ) + 1)))) := by
      rw [← kmswRunEventuallyLL_eq_range w h]
      exact he
    obtain ⟨j, hj⟩ := hrange
    dsimp only at hj
    apply hne (-((j : ℤ) + 1))
    rw [futureMapBoundaryDart, boundaryOuterEdge_of_negative w h (by omega), hj]
  · have hrange : e ∈ Set.range (fun j : ℕ => kmswRightBoundaryEdge w j) := by
      rw [← kmswRunEventuallyLR_eq_range w h]
      exact he
    obtain ⟨j, hj⟩ := hrange
    dsimp only at hj
    by_cases hj0 : j = 0
    · subst j
      apply hne 0
      rw [futureMapBoundaryDart_zero, ← hj, kmswRightBoundaryEdge_zero]
      rfl
    · apply hne (j : ℤ)
      rw [futureMapBoundaryDart, boundaryOuterEdge_of_positive w h (by omega),
        Int.toNat_natCast, hj]

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the two-sided (recurrent iid) KMSW drawing); not a paper result.
Face successor: `kmswInfFaceSucc` in `DirectedDistances/KMSW/InfiniteRotation.lean`.
Requires only `hfin`, with no `BoundaryHitWitnesses` hypothesis.
The orbit through the first creation dart contains precisely the creation triple. -/
private theorem full_triangle_orbit_iff (j : TriangleCreationTime w) (d : ℕ × Bool) :
    (kmswInfFaceSucc w hfin).SameCycle (stageTriangleDartTriple w j).1 d ↔
      d ∈ stageTriangleDartList w j := by
  let f := kmswInfFaceSucc w hfin
  let t := stageTriangleDartTriple w j
  obtain ⟨h1, h2, h3, _, _, _⟩ := capFace_triangle_darts_sameCycle w hfin j
  change f.SameCycle t.1 d ↔ d ∈ [t.1, t.2.1, t.2.2]
  have h1' : f t.1 = t.2.1 := h1
  have h2' : f t.2.1 = t.2.2 := h2
  have h3' : f t.2.2 = t.1 := h3
  have hi1 : f.symm t.1 = t.2.2 := f.symm_apply_eq.mpr h3'.symm
  have hi2 : f.symm t.2.1 = t.1 := f.symm_apply_eq.mpr h1'.symm
  have hi3 : f.symm t.2.2 = t.2.1 := f.symm_apply_eq.mpr h2'.symm
  constructor
  · rintro ⟨k, rfl⟩
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [add_comm (k : ℤ) 1, zpow_add, Equiv.Perm.mul_apply, zpow_one]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ih ⊢
      rcases ih with h | h | h
      · exact Or.inr (Or.inl (by rw [h, h1']))
      · exact Or.inr (Or.inr (by rw [h, h2']))
      · exact Or.inl (by rw [h, h3'])
    | pred k ih =>
      rw [sub_eq_add_neg, add_comm (-(k : ℤ)) (-1), zpow_add, Equiv.Perm.mul_apply,
        zpow_neg_one]
      change f.symm ((f ^ (-(k : ℤ))) t.1) ∈ [t.1, t.2.1, t.2.2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ih ⊢
      rcases ih with h | h | h
      · exact Or.inr (Or.inr (by rw [h, hi1]))
      · exact Or.inl (by rw [h, hi2])
      · exact Or.inr (Or.inl (by rw [h, hi3]))
  · intro hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact Equiv.Perm.SameCycle.rfl
    · exact ⟨1, by simpa only [zpow_one] using h1'⟩
    · exact ⟨2, by simpa only [show (2 : ℤ) = 1 + 1 from rfl, zpow_add,
        zpow_one, Equiv.Perm.mul_apply, h1'] using h2'⟩

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the two-sided (recurrent iid) KMSW drawing); not a paper result.
Face successor: `kmswInfFaceSucc` in `DirectedDistances/KMSW/InfiniteRotation.lean`.
Requires `h : BoundaryHitWitnesses w`: only the coordinate hits `rightHit` and `leftHit`.
These assert that `R` and `L` each hit every negative integer level.
Every geometric dart borders a realized face, including every missing boundary edge. -/
theorem dart_borders_exists (h : BoundaryHitWitnesses w) (d : ℕ × Bool) :
    ∃ F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face,
      (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d F := by
  classical
  by_cases hd : (kmswInfFaceSucc w hfin).SameCycle futureMapOuterDart d
  · obtain ⟨F, _, hdF, _⟩ :=
      (faceOrbit_outer_iff_common_unbounded_face w h hfin d d).1 ⟨hd, hd⟩
    exact ⟨F, hdF⟩
  · obtain ⟨j, hj⟩ := full_triangle_of_not_outer w hfin h d hd
    exact ⟨capFace w hfin j, (cap_border_iff w hfin j d).2 hj⟩

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the two-sided (recurrent iid) KMSW drawing); not a paper result.
Face successor: `kmswInfFaceSucc` in `DirectedDistances/KMSW/InfiniteRotation.lean`.
Requires `h : BoundaryHitWitnesses w`: only the coordinate hits `rightHit` and `leftHit`.
These assert that `R` and `L` each hit every negative integer level.
Every geometric dart borders exactly one realized face. -/
theorem dart_borders_unique (h : BoundaryHitWitnesses w) (d : ℕ × Bool) :
    ∃! F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face,
      (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d F := by
  obtain ⟨F, hF⟩ := dart_borders_exists w hfin h d
  exact ⟨F, hF, fun G hG => dart_border_face_unique w hfin d G F hG hF⟩

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the two-sided (recurrent iid) KMSW drawing); not a paper result.
Face successor: `kmswInfFaceSucc` in `DirectedDistances/KMSW/InfiniteRotation.lean`.
Requires `h : BoundaryHitWitnesses w`: only the coordinate hits `rightHit` and `leftHit`.
These assert that `R` and `L` each hit every negative integer level.
Two darts share a face-successor orbit exactly when they border a common realized face. -/
theorem faceOrbit_iff_common_face (h : BoundaryHitWitnesses w) (d e : ℕ × Bool) :
    (kmswInfFaceSucc w hfin).SameCycle d e ↔
      ∃ F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face,
        (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d F ∧
        (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders e F := by
  classical
  let f := kmswInfFaceSucc w hfin
  constructor
  · intro hde
    by_cases hd : f.SameCycle futureMapOuterDart d
    · obtain ⟨F, _, hF⟩ :=
        (faceOrbit_outer_iff_common_unbounded_face w h hfin d e).1
          ⟨hd, hd.trans hde⟩
      exact ⟨F, hF⟩
    · obtain ⟨j, hj⟩ := full_triangle_of_not_outer w hfin h d hd
      have hjd := (full_triangle_orbit_iff w hfin j d).2 hj
      have hje := (full_triangle_orbit_iff w hfin j e).1 (hjd.trans hde)
      exact ⟨capFace w hfin j, (cap_border_iff w hfin j d).2 hj,
        (cap_border_iff w hfin j e).2 hje⟩
  · rintro ⟨F, hdF, heF⟩
    by_cases hd : f.SameCycle futureMapOuterDart d
    · obtain ⟨U, hU, hdU, _⟩ :=
        (faceOrbit_outer_iff_common_unbounded_face w h hfin d d).1 ⟨hd, hd⟩
      have hFU := dart_border_face_unique w hfin d F U hdF hdU
      subst F
      have he := (faceOrbit_outer_iff_common_unbounded_face w h hfin d e).2
        ⟨U, hU, hdU, heF⟩
      exact he.1.symm.trans he.2
    · obtain ⟨j, hj⟩ := full_triangle_of_not_outer w hfin h d hd
      have hdc := (cap_border_iff w hfin j d).2 hj
      have hFc := dart_border_face_unique w hfin d F (capFace w hfin j) hdF hdc
      rw [hFc] at heF
      have hje := (cap_border_iff w hfin j e).1 heF
      exact ((full_triangle_orbit_iff w hfin j d).2 hj).symm.trans
        ((full_triangle_orbit_iff w hfin j e).2 hje)

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the two-sided (recurrent iid) KMSW drawing); not a paper result.
Face successor: `kmswInfFaceSucc` in `DirectedDistances/KMSW/InfiniteRotation.lean`.
Requires `h : BoundaryHitWitnesses w`: only the coordinate hits `rightHit` and `leftHit`.
These assert that `R` and `L` each hit every negative integer level.
Each bounded realized face is a creation cap face. -/
private theorem full_boundedFace_eq_capFace (h : BoundaryHitWitnesses w)
    (F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face)
    (hF : ¬ (monotoneFamilyDrawing w hfin (monotone_family_all w)).IsUnbounded F) :
    ∃ j : TriangleCreationTime w, F = capFace w hfin j := by
  let G := familyG w (monotone_family_all w)
  let Q := familyQ w (monotone_family_all w)
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  obtain ⟨n, i, hFi⟩ := limitDrawing_boundedFace_eq_capRegion_twoSided w hfin h F hF
  have hmem : (kmswStage w n).triangles.get i ∈
      (stageTriangleTimes w n).map (stageTriangleRecord w) := by
    rw [stageTriangleTimes_records]
    exact List.get_mem _ i
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hmem
  let k := (stageTriangleRecord_fin_index w j).choose
  have hk : (kmswStage w (j.val + 1)).triangles.get k = stageTriangleRecord w j :=
    (stageTriangleRecord_fin_index w j).choose_spec
  have htri : (kmswStage w n).triangles.get i =
      (kmswStage w (j.val + 1)).triangles.get k := hj.symm.trans hk.symm
  have hregion : ((G n).cap i).region = ((G (j.val + 1)).cap k).region := by
    apply monotone_cap_region_eq w (G n) (G (j.val + 1)) i k htri
    intro e he
    have hb := triBound_stage w n ((kmswStage w n).triangles.get i)
      (List.get_mem _ i)
    have hb' := triBound_stage w (j.val + 1)
      ((kmswStage w (j.val + 1)).triangles.get k) (List.get_mem _ k)
    rw [← htri] at hb'
    have heN : e < (kmswStage w n).nextEdge := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hb.1
      · exact hb.2.1
      · exact hb.2.2
    have heJ : e < (kmswStage w (j.val + 1)).nextEdge := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hb'.1
      · exact hb'.2.1
      · exact hb'.2.2
    have haN : P.arc (e, false) = (Q n).arc (⟨⟨e, heN⟩, false⟩) :=
      familyDrawing_arc w hfin (monotone_family_all w) n (⟨⟨e, heN⟩, false⟩)
    have haJ : P.arc (e, false) = (Q (j.val + 1)).arc (⟨⟨e, heJ⟩, false⟩) :=
      familyDrawing_arc w hfin (monotone_family_all w) (j.val + 1)
        (⟨⟨e, heJ⟩, false⟩)
    simp only [stageEdgeTrace, dite_eq_left heN, dite_eq_left heJ]
    exact congrArg Polyline.image (haN.symm.trans haJ)
  refine ⟨j, Subtype.ext ?_⟩
  exact hFi.trans (hregion.trans (capFace_spec w hfin j).1.symm)

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the two-sided (recurrent iid) KMSW drawing); not a paper result.
Face successor: `kmswInfFaceSucc` in `DirectedDistances/KMSW/InfiniteRotation.lean`.
Requires `h : BoundaryHitWitnesses w`: only the coordinate hits `rightHit` and `leftHit`.
These assert that `R` and `L` each hit every negative integer level.
Every realized face has a bordering geometric dart. -/
theorem face_bordered (h : BoundaryHitWitnesses w)
    (F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face) :
    ∃ d : ℕ × Bool,
      (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d F := by
  classical
  by_cases hF : (monotoneFamilyDrawing w hfin (monotone_family_all w)).IsUnbounded F
  · obtain ⟨U, hU, hdU, _⟩ :=
      (faceOrbit_outer_iff_common_unbounded_face w h hfin
        futureMapOuterDart futureMapOuterDart).1
          ⟨Equiv.Perm.SameCycle.rfl, Equiv.Perm.SameCycle.rfl⟩
    obtain ⟨V, _, huniq, _⟩ := monotoneFamilyDrawing_faceClassification_twoSided w hfin h
    have hFU : F = U := (huniq F hF).trans (huniq U hU).symm
    exact ⟨futureMapOuterDart, hFU.symm ▸ hdU⟩
  · obtain ⟨j, rfl⟩ := full_boundedFace_eq_capFace w hfin h F hF
    exact ⟨(stageTriangleDartTriple w j).1,
      (capFace_triangle_darts_border w hfin j).1⟩

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
the two-sided (recurrent iid) KMSW drawing); not a paper result.
Face successor: `kmswInfFaceSucc` in `DirectedDistances/KMSW/InfiniteRotation.lean`.
Requires `h : BoundaryHitWitnesses w`: only the coordinate hits `rightHit` and `leftHit`.
These assert that `R` and `L` each hit every negative integer level.
A bounded face has exactly the darts of one creation triangle, which form one
three-element face-successor orbit. -/
theorem boundedFace_orbit_is_triangle (h : BoundaryHitWitnesses w)
    (F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face)
    (hF : ¬ (monotoneFamilyDrawing w hfin (monotone_family_all w)).IsUnbounded F) :
    ∃ j : TriangleCreationTime w,
      {d | (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d F} =
        {d | d ∈ stageTriangleDartList w j} ∧
      {d | (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d F} =
        {d | (kmswInfFaceSucc w hfin).SameCycle (stageTriangleDartTriple w j).1 d} ∧
      FaceSucc3Cycle (kmswInfFaceSucc w hfin) (stageTriangleDartTriple w j).1
        (stageTriangleDartTriple w j).2.1 (stageTriangleDartTriple w j).2.2 ∧
      (stageTriangleDartList w j).toFinset.card = 3 := by
  obtain ⟨j, rfl⟩ := full_boundedFace_eq_capFace w hfin h F hF
  refine ⟨j, ?_, ?_, capFace_triangle_darts_sameCycle w hfin j, ?_⟩
  · exact Set.ext (fun d => cap_border_iff w hfin j d)
  · exact Set.ext (fun d => (cap_border_iff w hfin j d).trans
      (full_triangle_orbit_iff w hfin j d).symm)
  · rw [List.toFinset_card_of_nodup (stageTriangleDartList_nodup w j)]
    rfl

end DirectedDistances.KMSW
