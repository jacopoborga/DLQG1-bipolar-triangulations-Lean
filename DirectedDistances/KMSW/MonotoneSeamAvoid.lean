module

public import DirectedDistances.KMSW.MonotoneSeamRegions

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

variable (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)




theorem monotoneFamilyDrawing_nonseam_interior_avoid_seam
    (d : ℕ × Bool)
    (hns : ∀ k : ℤ, d.1 ≠ boundaryOuterEdge w h k) :
    ∀ z ∈ ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc d).interior,
      z.im ≠ seamFun w h hfin z.re := by
  intro z hzInterior
  by_contra hAvoid
  have hzEq : z.im = seamFun w h hfin z.re := hAvoid
  have hzGraph : z ∈ {q : ℂ | q.im = seamFun w h hfin q.re} := hzEq
  rw [seamFun_graph w h hfin] at hzGraph
  obtain ⟨k, hzSeam⟩ := Set.mem_iUnion.mp hzGraph
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let e := boundaryOuterEdge w h k
  let s : ℕ × Bool := (e, true)
  have hzSeamImage : z ∈ (P.arc s).image := by
    change z ∈ (P.arc (boundaryOuterEdge w h k, true)).image
    exact hzSeam
  have hsd : s ≠ d := by
    intro heq
    apply hns k
    simpa only [s, e] using (congrArg Prod.fst heq).symm
  have hsf : s ≠ (d.1, !d.2) := by
    intro heq
    apply hns k
    simpa only [s, e] using (congrArg Prod.fst heq).symm
  have hzSeamInterior : z ∈ (P.arc s).interior := by
    by_cases hzNot : z ∈ (P.arc s).interior
    · exact hzNot
    · have hEnds : z = (P.arc s).start ∨ z = (P.arc s).finish := by
        by_contra hEnds
        apply hzNot
        simp only [Polyline.interior, Set.mem_sdiff, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        exact ⟨hzSeamImage, fun hp => hEnds (by simpa using hp)⟩
      rcases hEnds with hzStart | hzFinish
      · have hzPos : z = P.pos (kmswLimitDartVertex w s) :=
          hzStart.trans (P.arc_start s)
        exact False.elim (P.interior_avoids_vertices d (kmswLimitDartVertex w s)
          (hzPos ▸ hzInterior))
      · have hzPos : z = P.pos (kmswLimitDartVertex w (e, false)) :=
          hzFinish.trans (P.arc_finish s)
        exact False.elim (P.interior_avoids_vertices d
          (kmswLimitDartVertex w (e, false)) (hzPos ▸ hzInterior))
  have hdisj := P.interior_disjoint d s hsd hsf
  exact (Set.disjoint_left.mp hdisj) hzInterior hzSeamInterior




theorem monotoneFamilyDrawing_nonseam_interior_above_seam
    (d : ℕ × Bool)
    (hns : ∀ k : ℤ, d.1 ≠ boundaryOuterEdge w h k)
    (z : ℂ)
    (hz : z ∈ ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc d).interior) :
    seamFun w h hfin z.re < z.im := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  have hzImage : z ∈ P.image := by
    change z ∈ Set.range P.pos ∪ {q | ∃ e, q ∈ (P.arc e).image}
    exact Or.inr ⟨d, hz.1⟩
  have hAbove := monotoneFamilyDrawing_above_seam w h hfin hzImage
  exact lt_of_le_of_ne hAbove
    (Ne.symm (monotoneFamilyDrawing_nonseam_interior_avoid_seam
      w h hfin d hns z hz))

end DirectedDistances.KMSW
