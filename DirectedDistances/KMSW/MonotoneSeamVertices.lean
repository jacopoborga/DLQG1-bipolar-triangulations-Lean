module

public import DirectedDistances.KMSW.MonotoneSeamAvoid

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set

variable (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)




theorem boundaryVertex_pos_eq (k : ℤ) :
    (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
        (boundaryVertex w h k) =
      ⟨seamX w h hfin k, seamFun w h hfin (seamX w h hfin k)⟩ := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let d := futureMapBoundaryDart w h k
  have hfinish : (P.arc d).finish = P.pos (boundaryVertex w h k) := by
    calc
      (P.arc d).finish = P.pos (kmswLimitDartVertex w (futureMapEdgeInv d)) := by
        simpa [d, futureMapBoundaryDart, futureMapEdgeInv] using P.arc_finish d
      _ = P.pos (boundaryVertex w h k) :=
        congrArg P.pos (futureMapBoundaryDart_endpoints w h k).2
  have hlen := P.arc_length d
  have himage : (P.arc d).finish ∈ (P.arc d).image := by
    refine Or.inr ⟨(P.arc d).points.length - 2, by omega, ?_⟩
    unfold Polyline.segmentAt
    have hi : (P.arc d).points.length - 2 + 1 =
        (P.arc d).points.length - 1 := by omega
    rw [hi, Polyline.point_last_eq_finish]
    exact right_mem_segment ℝ _ _
  have hgraph : (P.arc d).finish ∈
      {z : ℂ | z.im = seamFun w h hfin z.re} := by
    rw [seamFun_graph w h hfin]
    exact Set.mem_iUnion.mpr ⟨k, himage⟩
  rw [hfinish] at hgraph
  apply Complex.ext
  · rfl
  · exact hgraph




theorem pos_mem_seam_iff (v : ℕ) :
    ((monotoneFamilyDrawing w hfin (monotone_family_all w)).pos v).im =
      seamFun w h hfin
        ((monotoneFamilyDrawing w hfin (monotone_family_all w)).pos v).re ↔
      ∃ k : ℤ, v = boundaryVertex w h k := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  constructor
  · intro hv
    have hgraph : P.pos v ∈ {z : ℂ | z.im = seamFun w h hfin z.re} := hv
    rw [seamFun_graph w h hfin] at hgraph
    obtain ⟨k, himage⟩ := Set.mem_iUnion.mp hgraph
    let d := futureMapBoundaryDart w h k
    have hstart : (P.arc d).start = P.pos (boundaryVertex w h (k + 1)) := by
      calc
        (P.arc d).start = P.pos (kmswLimitDartVertex w d) := P.arc_start d
        _ = P.pos (boundaryVertex w h (k + 1)) :=
          congrArg P.pos (futureMapBoundaryDart_endpoints w h k).1
    have hfinish : (P.arc d).finish = P.pos (boundaryVertex w h k) := by
      calc
        (P.arc d).finish = P.pos
            (kmswLimitDartVertex w (futureMapEdgeInv d)) := by
          simpa [d, futureMapBoundaryDart, futureMapEdgeInv] using P.arc_finish d
        _ = P.pos (boundaryVertex w h k) :=
          congrArg P.pos (futureMapBoundaryDart_endpoints w h k).2
    have hends : P.pos v = (P.arc d).start ∨ P.pos v = (P.arc d).finish := by
      by_contra hends
      apply P.interior_avoids_vertices d v
      simp only [Polyline.interior, Set.mem_sdiff, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact ⟨himage, fun he => hends (by simpa using he)⟩
    rcases hends with hs | ht
    · exact ⟨k + 1, P.pos_injective (hs.trans hstart)⟩
    · exact ⟨k, P.pos_injective (ht.trans hfinish)⟩
  · rintro ⟨k, rfl⟩
    have heq := boundaryVertex_pos_eq w h hfin k
    rw [heq]




theorem vertex_strictly_above_seam (v : ℕ)
    (hv : ∀ k : ℤ, v ≠ boundaryVertex w h k) :
    seamFun w h hfin
        ((monotoneFamilyDrawing w hfin (monotone_family_all w)).pos v).re <
      ((monotoneFamilyDrawing w hfin (monotone_family_all w)).pos v).im := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  have hImage : P.pos v ∈ P.image := by
    change P.pos v ∈ Set.range P.pos ∪ {z | ∃ d, z ∈ (P.arc d).image}
    exact Or.inl ⟨v, rfl⟩
  have hAbove := monotoneFamilyDrawing_above_seam w h hfin hImage
  have hNe : (P.pos v).im ≠ seamFun w h hfin (P.pos v).re := by
    intro heq
    obtain ⟨k, hk⟩ := (pos_mem_seam_iff w h hfin v).1 heq
    exact hv k hk
  exact lt_of_le_of_ne hAbove (Ne.symm hNe)

end DirectedDistances.KMSW
