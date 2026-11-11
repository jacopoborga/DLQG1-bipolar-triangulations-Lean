module

public import DirectedDistances.PlanarMap.PlaneRealization
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.DenselyOrdered

/-! # Bounded faces of locally finite piecewise linear drawings

The geometric local finiteness of a drawing forces a bounded face to have only
finitely many bordering darts. Consequently, infinitely many bordering darts
certify an unbounded face. These helpers do not identify the UIBHBOT faces.

A finite simple boundary cycle alone does not imply boundedness: the exterior
face of a finite triangle drawing also has such a cycle. Identifying the bounded
side of a realized created-triangle cycle remains a separate obligation. -/

public section

namespace DirectedDistances.PlanarMap.PLDrawing

open Set

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
variable (P : PLDrawing D V flip rot vert)

/-- If the left wedge of a dart lies in a face, its tail position lies in the closure
of that face. This uses precisely the wedge condition in `dartBorders`. -/
theorem dartBorders_start_mem_closure {d : D} {F : P.Face}
    (h : P.dartBorders d F) : P.pos (vert d) ∈ closure F.val := by
  obtain ⟨δ, hδ, hwedge⟩ := h
  let f : ℝ → ℂ := fun t => (P.arc d).start + (t : ℂ) *
    ((P.arc d).initialDirection + (δ / 2 : ℝ) * Complex.I *
      (P.arc d).initialDirection)
  have hf : Continuous f := by fun_prop
  have hzero : (0 : ℝ) ∈ closure (Ioo 0 δ) := by
    rw [closure_Ioo (ne_of_lt hδ)]
    exact ⟨le_rfl, hδ.le⟩
  have hsubset : f '' Ioo 0 δ ⊆ F.val := by
    rintro z ⟨t, ht, rfl⟩
    exact hwedge t (δ / 2) ht.1 ht.2 (half_pos hδ) (half_lt_self hδ)
  have hstart := closure_mono hsubset (mem_closure_image hf.continuousAt hzero)
  simpa only [f, Complex.ofReal_zero, zero_mul, add_zero, P.arc_start] using hstart

/-- A bounded face of a locally finite drawing has only finitely many bordering
darts, counting dart identities even when edges have the same endpoints. -/
theorem finite_borderDarts_of_bounded (F : P.Face)
    (hF : Bornology.IsBounded F.val) : {d | P.dartBorders d F}.Finite := by
  apply (P.locally_finite (closure F.val) hF.closure).subset
  intro d hd
  refine ⟨P.pos (vert d), P.dartBorders_start_mem_closure hd, ?_⟩
  rw [← P.arc_start d]
  exact Or.inl rfl

/-- Infinitely many distinct darts bordering a face force that face to be unbounded
in the norm sense of `IsUnbounded`. -/
theorem isUnbounded_of_infinite_borderDarts (F : P.Face)
    (hD : {d | P.dartBorders d F}.Infinite) : P.IsUnbounded F := by
  by_contra hF
  change ¬ (∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖) at hF
  push Not at hF
  obtain ⟨R, hR⟩ := hF
  apply hD (P.finite_borderDarts_of_bounded F ?_)
  apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
  refine ⟨R, fun z hz => ?_⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hR z hz

end DirectedDistances.PlanarMap.PLDrawing
