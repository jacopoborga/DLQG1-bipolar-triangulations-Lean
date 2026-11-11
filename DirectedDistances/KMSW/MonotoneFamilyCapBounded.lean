/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.MonotoneFamilyFaceOrbitsCap

/-! Helper toward the plane-face correspondence for the one-sided KMSW drawing; not a -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

/-- Helper toward the plane-face correspondence for the one-sided KMSW drawing;
A bounded face set cannot satisfy the definition's quantified unboundedness. -/
private theorem bounded_not_unbounded {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (F : P.Face) (hF : Bornology.IsBounded F.val) : ¬ P.IsUnbounded F := by
  obtain ⟨R, hR⟩ := hF.subset_closedBall (0 : ℂ)
  intro h
  obtain ⟨z, hz, hnorm⟩ := h R
  have hzR : ‖z‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hz
  exact (not_lt_of_ge hzR) hnorm

/-- Helper toward the plane-face correspondence for the one-sided KMSW drawing;
The selected creation cap is bounded by the graph-region bound; endpoint joins
extend the strict interior separation to the closed horizontal interval. -/
theorem capFace_bounded (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) :
    Bornology.IsBounded (capFace w hfin j).val := by
  let i := (stageTriangleRecord_fin_index w j).choose
  let C := (familyG w (monotone_family_all w) (j.val + 1)).cap i
  have hlowhigh : ∀ x ∈ Icc C.a C.b, C.low x ≤ C.high x := by
    intro x hx
    rcases hx with ⟨hax, hxb⟩
    by_cases hxa : x = C.a
    · rw [hxa, C.left_join]
    by_cases hxeqB : x = C.b
    · rw [hxeqB, C.right_join]
    have hleft : C.a < x := lt_of_le_of_ne hax (Ne.symm hxa)
    have hright : x < C.b := lt_of_le_of_ne hxb hxeqB
    exact (C.separated x ⟨hleft, hright⟩).le
  have hregion : Bornology.IsBounded C.region := by
    change Bornology.IsBounded (graphRegion C.a C.b C.low C.high)
    exact isBounded_graphRegion C.low_continuous C.high_continuous hlowhigh
  have hcap : (capFace w hfin j).val = C.region := by
    simpa [C, i] using (capFace_spec w hfin j).1
  rw [hcap]
  exact hregion

/-- Helper toward the plane-face correspondence for the one-sided KMSW drawing;
The selected creation cap does not satisfy quantified unboundedness. -/
theorem capFace_not_unbounded (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    ¬ P.IsUnbounded (capFace w hfin j) := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  exact bounded_not_unbounded P (capFace w hfin j) (capFace_bounded w hfin j)

end DirectedDistances.KMSW
