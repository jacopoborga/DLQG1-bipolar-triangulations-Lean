module

public import DirectedDistances.KMSW.CutVertexDisconnects
public import DirectedDistances.KMSW.LocalFinitenessUpperChain
import DirectedDistances.KMSW.InfiniteRotation
import DirectedDistances.KMSW.StageIncidence

/-! # Every vertex ID is allocated under finite incidence

The UIQBOT vertex carrier is the set of allocated vertex IDs, i.e. those created at some
every natural number is such an ID: the edge `e` exists by stage `e` and its west endpoint is
allocated by then, so if `v` were never allocated, every edge would be incident to one of the
finitely many vertices below `v`, each of which has only finitely many incident edges.

As a consequence, the disconnection witnesses of `mapCutVertex_removed_disconnected` -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory
open DirectedDistances.RandomWalk

/-- Under finite incidence, every natural vertex ID is allocated at some finite stage. -/
theorem kmsw_vertex_allocated_of_finite_incidence (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) (v : ℕ) :
    ∃ n, v < (kmswStage w n).nextVertex := by
  by_contra hno
  simp only [not_exists, not_lt] at hno
  have hcover : (Set.univ : Set ℕ) ⊆ ⋃ u ∈ Set.Iio v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)} := by
    intro e _
    have he := kmsw_edge_allocated_by_self w e
    have hlt := (kmswStage_endpoints_lt_nextVertex w e e he).1
    have hu : (kmswStage w e).west e < v := lt_of_lt_of_le hlt (hno e)
    simp only [Set.mem_iUnion]
    exact ⟨(kmswStage w e).west e, hu, e, he, Or.inl rfl⟩
  have hfinU : (⋃ u ∈ Set.Iio v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}).Finite :=
    (Set.finite_Iio v).biUnion (fun u _ => hfin u)
  exact Set.infinite_univ (hfinU.subset hcover)

/-- Almost surely, every vertex ID of the UIQBOT carrier is allocated. -/
theorem pitmanCodes_ae_vertex_allocated :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ v : ℕ,
      ∃ n, v < (kmswStage (pitmanCode (fun i => ω (i + 1))) n).nextVertex := by
  filter_upwards [pitmanCodes_ae_finite_incident_edges] with ω hω v
  exact kmsw_vertex_allocated_of_finite_incidence _ hω v

/-- `mapCutVertex_removed_disconnected` with allocated witnesses: removing a map-level cut
vertex `v ≠ 0` separates two allocated vertices of the map (`def-cut-vertex`, -/
theorem mapCutVertex_removed_disconnected_allocated (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) {v : ℕ}
    (hcut : mapCutVertex w hfin v) (hv0 : v ≠ 0) :
    ∃ x y, (∃ n, x < (kmswStage w n).nextVertex) ∧
      (∃ n, y < (kmswStage w n).nextVertex) ∧ x ≠ v ∧ y ≠ v ∧
      ∀ p : FiniteUndirectedEdgePath w x y, v ∈ p.vertices := by
  obtain ⟨x, y, hx, hy, hp⟩ :=
    mapCutVertex_removed_disconnected w hfin htrans hR hL0 hcut hv0
  exact ⟨x, y, kmsw_vertex_allocated_of_finite_incidence w hfin x,
    kmsw_vertex_allocated_of_finite_incidence w hfin y, hx, hy, hp⟩

/-- Almost surely, removing any map-level cut vertex other than the source separates two -/
theorem pitmanCodes_ae_mapCutVertex_removed_disconnected_allocated :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∀ v, mapCutVertex w hfin v → v ≠ 0 →
          ∃ x y, (∃ n, x < (kmswStage w n).nextVertex) ∧
            (∃ n, y < (kmswStage w n).nextVertex) ∧ x ≠ v ∧ y ≠ v ∧
            ∀ p : FiniteUndirectedEdgePath w x y, v ∈ p.vertices := by
  filter_upwards [pitmanCodes_ae_infinite_mapCutVertices] with ω hω
  obtain ⟨hfin, htrans, hR, hL0, -⟩ := hω
  exact ⟨hfin, fun v hcut hv0 =>
    mapCutVertex_removed_disconnected_allocated _ hfin htrans hR hL0 hcut hv0⟩

end DirectedDistances.KMSW
