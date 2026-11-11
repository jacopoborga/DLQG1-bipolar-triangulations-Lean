module

public import DirectedDistances.PlanarMap.PolylineStripMap

/-! # Polyline transfer using finitely many local cuts

Generic helpers for compact arcs. The affine strip hypothesis is restricted to the
endpoint range of the polyline and does not require a global sequence of breakpoints. -/

public section

namespace DirectedDistances.PlanarMap
namespace Polyline

noncomputable section

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision
with locally finite cuts); not a paper result. -/
private theorem local_point_re_bounds (p : Polyline) (hp : p.XMonotone) {i : ℕ}
    (hi : i < p.points.length) :
    p.start.re ≤ (p.point i).re ∧ (p.point i).re ≤ p.finish.re := by
  constructor
  · rw [← p.point_zero_eq_start]
    exact point_re_le_of_le hp (Nat.zero_le i) hi
  · rw [← p.point_last_eq_finish]
    exact point_re_le_of_le hp (by omega) (by omega)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision
with locally finite cuts); not a paper result. Every refined vertex stays in the endpoint strip. -/
theorem point_re_bounds_subdivideAt (p : Polyline) (xs : Finset ℝ)
    (hp : p.XMonotone) {i : ℕ} (hi : i < (subdivideAt p xs).points.length) :
    p.start.re ≤ ((subdivideAt p xs).point i).re ∧
      ((subdivideAt p xs).point i).re ≤ p.finish.re := by
  simpa only [start_subdivideAt, finish_subdivideAt] using
    local_point_re_bounds (subdivideAt p xs) (xMonotone_subdivideAt p xs hp) hi

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision
with locally finite cuts); not a paper result. No global breakpoint sequence is required. -/
theorem affineOnSegments_subdivideAt_local (F : ℂ → ℂ) (p : Polyline) (xs : Finset ℝ)
    (hp : p.XMonotone)
    (haff : ∀ s t : ℝ, p.start.re ≤ s → s < t → t ≤ p.finish.re →
      (∀ c ∈ xs, c ∉ Set.Ioo s t) →
      ∃ A : ℂ →ᵃ[ℝ] ℂ, Set.EqOn F A {z | s ≤ z.re ∧ z.re ≤ t}) :
    AffineOnSegments F (subdivideAt p xs) := by
  intro i hi
  have hmono := xMonotone_subdivideAt p xs hp
  have hlt := point_re_lt hmono (Nat.lt_succ_self i) hi
  have hlo := (point_re_bounds_subdivideAt p xs hp (by omega :
    i < (subdivideAt p xs).points.length)).1
  have hhi := (point_re_bounds_subdivideAt p xs hp hi).2
  obtain ⟨A, hA⟩ := haff _ _ hlo hlt hhi (by
    intro c hc hbetween
    rcases doesNotCross_subdivideAt p xs hi hc with hleft | hright
    · exact (not_lt_of_ge hleft.2) hbetween.2
    · exact (not_lt_of_ge hright.1) hbetween.1)
  refine ⟨A, ?_⟩
  intro z hz
  exact hA (segmentAt_re_bounds hmono hi hz)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision
with locally finite cuts); not a paper result. Subdivision preserves the exact interior set. -/
theorem interior_subdivideAt (p : Polyline) (xs : Finset ℝ) :
    (subdivideAt p xs).interior = p.interior := by
  simp only [interior, image_subdivideAt, start_subdivideAt, finish_subdivideAt]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision
with locally finite cuts); not a paper result. The image formula needs no injectivity. -/
theorem image_mapPoints_subdivideAt_local (F : ℂ → ℂ) (p : Polyline) (xs : Finset ℝ)
    (hp : p.XMonotone)
    (haff : ∀ s t : ℝ, p.start.re ≤ s → s < t → t ≤ p.finish.re →
      (∀ c ∈ xs, c ∉ Set.Ioo s t) →
      ∃ A : ℂ →ᵃ[ℝ] ℂ, Set.EqOn F A {z | s ≤ z.re ∧ z.re ≤ t}) :
    (mapPoints F (subdivideAt p xs)).image = F '' p.image := by
  rw [image_mapPoints F _ (affineOnSegments_subdivideAt_local F p xs hp haff),
    image_subdivideAt]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision
with locally finite cuts); not a paper result. -/
theorem interior_mapPoints_subdivideAt_local (F : ℂ → ℂ) (p : Polyline)
    (xs : Finset ℝ) (hp : p.XMonotone)
    (haff : ∀ s t : ℝ, p.start.re ≤ s → s < t → t ≤ p.finish.re →
      (∀ c ∈ xs, c ∉ Set.Ioo s t) →
      ∃ A : ℂ →ᵃ[ℝ] ℂ, Set.EqOn F A {z | s ≤ z.re ∧ z.re ≤ t})
    (hinj : Set.InjOn F p.image) :
    (mapPoints F (subdivideAt p xs)).interior = F '' p.interior := by
  have hinj' : Set.InjOn F (subdivideAt p xs).image := by
    rwa [image_subdivideAt]
  rw [interior_mapPoints F _ (affineOnSegments_subdivideAt_local F p xs hp haff)
    hinj', interior_subdivideAt]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision
with locally finite cuts); not a paper result. Includes the permitted singleton case. -/
private theorem local_isSimple_of_xMonotone (p : Polyline) (hp : p.XMonotone) :
    p.IsSimple := by
  by_cases hlen : 2 ≤ p.points.length
  · exact isSimple_of_XMonotone hp hlen
  · refine ⟨?_, ?_, ?_⟩
    · intro i hi
      omega
    · intro i hi
      omega
    · intro i j hi
      omega

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision
with locally finite cuts); not a paper result. Strict monotonicity supplies simplicity. -/
theorem isSimple_mapPoints_subdivideAt_local (F : ℂ → ℂ) (p : Polyline)
    (xs : Finset ℝ) (hp : p.XMonotone)
    (haff : ∀ s t : ℝ, p.start.re ≤ s → s < t → t ≤ p.finish.re →
      (∀ c ∈ xs, c ∉ Set.Ioo s t) →
      ∃ A : ℂ →ᵃ[ℝ] ℂ, Set.EqOn F A {z | s ≤ z.re ∧ z.re ≤ t})
    (hinj : Set.InjOn F p.image) : (mapPoints F (subdivideAt p xs)).IsSimple := by
  have hinj' : Set.InjOn F (subdivideAt p xs).image := by
    rwa [image_subdivideAt]
  exact isSimple_mapPoints F _ (affineOnSegments_subdivideAt_local F p xs hp haff)
    hinj' (local_isSimple_of_xMonotone _ (xMonotone_subdivideAt p xs hp))

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision
with locally finite cuts); not a paper result. Each arc may have its own finite cut set. -/
theorem interior_disjoint_mapPoints_subdivideAt_local (F : ℂ → ℂ) (p q : Polyline)
    (xs ys : Finset ℝ) (hp : p.XMonotone) (hq : q.XMonotone)
    (haffp : ∀ s t : ℝ, p.start.re ≤ s → s < t → t ≤ p.finish.re →
      (∀ c ∈ xs, c ∉ Set.Ioo s t) →
      ∃ A : ℂ →ᵃ[ℝ] ℂ, Set.EqOn F A {z | s ≤ z.re ∧ z.re ≤ t})
    (haffq : ∀ s t : ℝ, q.start.re ≤ s → s < t → t ≤ q.finish.re →
      (∀ c ∈ ys, c ∉ Set.Ioo s t) →
      ∃ A : ℂ →ᵃ[ℝ] ℂ, Set.EqOn F A {z | s ≤ z.re ∧ z.re ≤ t})
    (hinj : Set.InjOn F (p.image ∪ q.image))
    (h : Disjoint p.interior q.interior) :
    Disjoint (mapPoints F (subdivideAt p xs)).interior
      (mapPoints F (subdivideAt q ys)).interior := by
  apply interior_disjoint_mapPoints F _ _
    (affineOnSegments_subdivideAt_local F p xs hp haffp)
    (affineOnSegments_subdivideAt_local F q ys hq haffq)
  · simpa only [image_subdivideAt] using hinj
  · simpa only [interior_subdivideAt] using h

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision
with locally finite cuts); not a paper result. Reverses a decreasing arc before subdivision. -/
theorem affineOnSegments_subdivideAt_reverse_local (F : ℂ → ℂ) (q : Polyline)
    (xs : Finset ℝ) (hq : q.reverse.XMonotone)
    (haff : ∀ s t : ℝ, q.finish.re ≤ s → s < t → t ≤ q.start.re →
      (∀ c ∈ xs, c ∉ Set.Ioo s t) →
      ∃ A : ℂ →ᵃ[ℝ] ℂ, Set.EqOn F A {z | s ≤ z.re ∧ z.re ≤ t}) :
    AffineOnSegments F (subdivideAt q.reverse xs) := by
  apply affineOnSegments_subdivideAt_local F q.reverse xs hq
  simpa only [start_reverse, finish_reverse] using haff

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision
with locally finite cuts); not a paper result. Pointwise transfer commutes with reversal. -/
theorem mapPoints_reverse (F : ℂ → ℂ) (p : Polyline) :
    mapPoints F p.reverse = (mapPoints F p).reverse := by
  cases p
  simp only [mapPoints, reverse, List.map_reverse]

end
end Polyline
end DirectedDistances.PlanarMap
