module

public import DirectedDistances.PlanarMap.PlaneRealization
import DirectedDistances.KMSW.LeftmostGeodesicUIQBOT

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private theorem kmswLimitDartVertex_eq_stageEndpoint (w : ℕ → Fin 3) (n : ℕ)
    (x : StageDart (kmswStage w n).nextEdge) :
    kmswLimitDartVertex w (x.1.val, x.2) = stageEndpoint (kmswStage w n) x := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w x.1.isLt
  cases hb : x.2 <;>
    simp [kmswLimitDartVertex, stageEndpoint, hb, hw, he]

/-- Helper toward the plane-realization obligation of adjudication n308:
combinatorial precondition for a PLDrawing of the KMSW union; not a paper result -/
theorem kmswLimitDartVertex_rot (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : ℕ × Bool) :
    kmswLimitDartVertex w (kmswInfRot w hfin d) = kmswLimitDartVertex w d := by
  obtain ⟨N, hN⟩ := kmswInfRot_eventually_eq_stage w hfin d
  obtain ⟨hd, hrot⟩ := hN N le_rfl
  let x : StageDart (kmswStage w N).nextEdge := (⟨d.1, hd⟩, d.2)
  let y := stageRot w N x
  have hxy : stageEndpoint (kmswStage w N) y = stageEndpoint (kmswStage w N) x :=
    ((stageRot_sameCycle_iff_endpoint_eq w N x y).1 ⟨1, rfl⟩).symm
  calc
    kmswLimitDartVertex w (kmswInfRot w hfin d) =
        kmswLimitDartVertex w (y.1.val, y.2) := by rw [hrot]
    _ = stageEndpoint (kmswStage w N) y := kmswLimitDartVertex_eq_stageEndpoint w N y
    _ = stageEndpoint (kmswStage w N) x := hxy
    _ = kmswLimitDartVertex w d := by
      rw [kmswLimitDartVertex_eq_stageEndpoint w N x]

private theorem edgeWest_ne_edgeEast (w : ℕ → Fin 3) (e : ℕ) :
    edgeWest w e ≠ edgeEast w e := by
  have hr := kmswStageRank_strict w e e (kmsw_edge_allocated_by_self w e)
  have he := edge_endpoints_eq w (kmsw_edge_allocated_by_self w e)
  rw [he.1, he.2] at hr
  intro h
  rw [h] at hr
  exact (lt_irrefl _ hr)

/-- Helper toward the plane-realization obligation of adjudication n308:
combinatorial precondition for a PLDrawing of the KMSW union; not a paper result -/
theorem kmswLimitDartVertex_flip_ne (w : ℕ → Fin 3) (d : ℕ × Bool) :
    kmswLimitDartVertex w (d.1, !d.2) ≠ kmswLimitDartVertex w d := by
  cases hb : d.2
  · simpa [kmswLimitDartVertex, hb] using (edgeWest_ne_edgeEast w d.1).symm
  · simpa [kmswLimitDartVertex, hb] using edgeWest_ne_edgeEast w d.1

/-- Helper toward the plane-realization obligation of adjudication n308:
combinatorial precondition for a PLDrawing of the KMSW union; not a paper result -/
theorem kmswLimitDart_star_finite (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (v : ℕ) :
    {d : ℕ × Bool | kmswLimitDartVertex w d = v}.Finite := by
  let E : Set ℕ := {e | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}
  have hE : E.Finite := hfin v
  have hprod : (E ×ˢ (Set.univ : Set Bool)).Finite :=
    hE.prod (Set.finite_univ (α := Bool))
  apply hprod.subset
  intro d hd
  change d.1 ∈ E ∧ d.2 ∈ Set.univ
  refine ⟨?_, Set.mem_univ _⟩
  have ha := kmsw_edge_allocated_by_self w d.1
  obtain ⟨hw, he⟩ := edge_endpoints_eq w ha
  refine ⟨d.1, ha, ?_⟩
  change (if d.2 then edgeEast w d.1 else edgeWest w d.1) = v at hd
  cases hb : d.2
  · exact Or.inl (hw.trans (by simpa [hb] using hd))
  · exact Or.inr (he.trans (by simpa [hb] using hd))

/-- Helper toward the plane-realization obligation of adjudication n308:
combinatorial precondition for a PLDrawing of the KMSW union; not a paper result -/
theorem kmswLimitDart_same_vertex_sameCycle (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d e : ℕ × Bool) (hv : kmswLimitDartVertex w d = kmswLimitDartVertex w e) :
    (kmswInfRot w hfin).SameCycle d e := by
  have hv' : (if d.2 then edgeEast w d.1 else edgeWest w d.1) =
      (if e.2 then edgeEast w e.1 else edgeWest w e.1) := by
    simpa [kmswLimitDartVertex] using hv
  obtain ⟨k, hk⟩ := (kmswInfRot_exists_pow_iff_endpoint w hfin d e).2 hv'
  exact ⟨(k : ℤ), by simpa only [zpow_natCast] using hk⟩

end DirectedDistances.KMSW
