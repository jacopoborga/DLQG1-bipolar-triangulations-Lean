module

public import DirectedDistances.PlanarMap.PlaneRealization
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.IntermediateValue

/-! # The exterior of a finite piecewise linear drawing

Generic helpers for plan n338 leaf 7 and adjudication n308, using the external-face -/

public section
namespace DirectedDistances.PlanarMap

open Set Metric

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 7, generic part); not a paper result. -/
theorem Polyline.isCompact_image (p : Polyline) : IsCompact p.image := by
  have hseg (i : ℕ) : IsCompact (p.segmentAt i) := by
    rw [Polyline.segmentAt, segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have heq : p.image = {p.start} ∪
      ⋃ i : Fin p.points.length, ⋃ (_ : i.val + 1 < p.points.length), p.segmentAt i := by
    ext z
    simp only [Polyline.image, mem_union, mem_singleton_iff, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro (h | ⟨i, hi, hz⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨i, Nat.lt_of_succ_lt hi⟩, hi, hz⟩
    · rintro (h | ⟨i, hi, hz⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i.val, hi, hz⟩
  rw [heq]
  exact isCompact_singleton.union (isCompact_iUnion fun i =>
    isCompact_iUnion fun _ => hseg i.val)

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 7, generic part); not a paper result. -/
theorem isCompact_image [Finite D] [Finite V] (P : PLDrawing D V flip rot vert) :
    IsCompact P.image := by
  have heq : P.image = range P.pos ∪ ⋃ d, (P.arc d).image := by
    ext z
    simp only [image, mem_union, mem_ofPred_eq, mem_iUnion]
  rw [heq]
  exact (finite_range P.pos).isCompact.union (isCompact_iUnion fun d =>
    (P.arc d).isCompact_image)

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 7, generic part); not a paper result. -/
theorem isBounded_image [Finite D] [Finite V] (P : PLDrawing D V flip rot vert) :
    Bornology.IsBounded P.image := P.isCompact_image.isBounded

end PLDrawing

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 7, generic part); not a paper result. -/
theorem isConnected_compl_closedBall_complex (R : ℝ) :
    IsConnected (closedBall (0 : ℂ) R)ᶜ := by
  rcases lt_or_ge R 0 with hR | hR
  · rw [closedBall_eq_empty.mpr hR, compl_empty]
    exact isConnected_univ
  · let f : ℝ × ℝ → ℂ := fun x => (x.1 : ℂ) * Complex.exp (x.2 * Complex.I)
    have hf : Continuous f := by fun_prop
    have heq : f '' (Ioi R ×ˢ (univ : Set ℝ)) = (closedBall (0 : ℂ) R)ᶜ := by
      ext z
      constructor
      · rintro ⟨⟨r, t⟩, ⟨hr, _⟩, rfl⟩
        change R < r at hr
        simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
        simpa only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hR.trans hr.le), Complex.norm_exp_ofReal_mul_I, mul_one] using hr
      · intro hz
        have hzR : R < ‖z‖ := by
          simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hz
        exact ⟨(‖z‖, Complex.arg z), ⟨hzR, mem_univ _⟩,
          Complex.norm_mul_exp_arg_mul_I z⟩
    rw [← heq]
    exact (isConnected_Ioi.prod isConnected_univ).image f hf.continuousOn

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 7, generic part); not a paper result. -/
theorem unbounded_face_contains_compl_ball [Finite D] [Finite V]
    (P : PLDrawing D V flip rot vert) :
    ∃ R : ℝ, P.image ⊆ closedBall 0 R ∧
      ∀ U : P.Face, P.IsUnbounded U → (closedBall (0 : ℂ) R)ᶜ ⊆ U.val := by
  obtain ⟨R, hR⟩ := P.isBounded_image.subset_closedBall 0
  refine ⟨R, hR, ?_⟩
  intro U hU
  obtain ⟨z, hzU, hzR⟩ := hU R
  have hz : z ∈ (closedBall (0 : ℂ) R)ᶜ := by
    simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hzR
  obtain ⟨x, _, hx⟩ := U.property
  rw [hx] at hzU ⊢
  rw [connectedComponentIn_eq hzU]
  exact (isConnected_compl_closedBall_complex R).isPreconnected.subset_connectedComponentIn
    hz (compl_subset_compl.mpr hR)

/-- Helper toward the plane-realization obligation of adjudication n308
(plan n338 leaf 7, generic part); not a paper result. -/
theorem existsUnique_unbounded_face [Finite D] [Finite V]
    (P : PLDrawing D V flip rot vert) : ∃! U : P.Face, P.IsUnbounded U := by
  obtain ⟨R, hR, hall⟩ := P.unbounded_face_contains_compl_ball
  obtain ⟨z, hzR⟩ := NormedField.exists_lt_norm ℂ R
  have hz : z ∈ (closedBall (0 : ℂ) R)ᶜ := by
    simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hzR
  have hcompl : (closedBall (0 : ℂ) R)ᶜ ⊆ P.imageᶜ := compl_subset_compl.mpr hR
  let U : P.Face := ⟨connectedComponentIn P.imageᶜ z, z, hcompl hz, rfl⟩
  have hEU : (closedBall (0 : ℂ) R)ᶜ ⊆ U.val :=
    (isConnected_compl_closedBall_complex R).isPreconnected.subset_connectedComponentIn
      hz hcompl
  have hU : P.IsUnbounded U := by
    intro S
    obtain ⟨w, hw⟩ := NormedField.exists_lt_norm ℂ (max R S)
    have hwR : R < ‖w‖ := lt_of_le_of_lt (le_max_left R S) hw
    have hwS : S < ‖w‖ := lt_of_le_of_lt (le_max_right R S) hw
    refine ⟨w, hEU ?_, hwS⟩
    simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hwR
  refine ⟨U, hU, ?_⟩
  intro F hF
  exact P.faces_eq_of_mem (hall F hF hz) (hEU hz)

end PLDrawing

end DirectedDistances.PlanarMap
