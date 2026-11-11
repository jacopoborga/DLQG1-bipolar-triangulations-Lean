/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMap
import Mathlib.Analysis.SpecialFunctions.Complex.Circle






public section

namespace DirectedDistances.PlanarMap.PlaneGraphDrawing

open Set Metric

variable {V E : Type*} (D : PlaneGraphDrawing V E)

/-- The image of a drawing with finitely many vertices and geometric edges is compact. -/
theorem isCompact_image [Finite V] [Finite E] : IsCompact D.image := by
  classical
  exact (Set.finite_range D.pos).isCompact.union
    (isCompact_iUnion fun e => isCompact_range (D.arc e).continuous)

/-- The exterior of a nonnegative-radius disk in the plane is connected. -/
theorem isConnected_norm_gt (r : ℝ) (hr : 0 ≤ r) :
    IsConnected {z : ℂ | r < ‖z‖} := by
  let f : Circle × ℝ → ℂ := fun p => p.2 • (p.1 : ℂ)
  have hc : IsConnected (f '' ((Set.univ : Set Circle) ×ˢ Set.Ioi r)) :=
    (isConnected_univ.prod isConnected_Ioi).image f
      (by fun_prop)
  have heq : f '' ((Set.univ : Set Circle) ×ˢ Set.Ioi r) = {z : ℂ | r < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨u, t⟩, ⟨_, ht⟩, rfl⟩
      change r < ‖t • (u : ℂ)‖
      rw [norm_smul, Real.norm_of_nonneg (hr.trans ht.le), Circle.norm_coe, mul_one]
      exact ht
    · intro hz
      have hpos : 0 < ‖z‖ := lt_of_le_of_lt hr hz
      let u : Circle := ⟨‖z‖⁻¹ • z, by
        apply mem_sphere_zero_iff_norm.mpr
        rw [norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), inv_mul_cancel₀ hpos.ne']⟩
      refine ⟨(u, ‖z‖), ⟨Set.mem_univ _, hz⟩, ?_⟩
      change ‖z‖ • (‖z‖⁻¹ • z) = z
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rwa [heq] at hc

/-- Every disk exterior in the plane is unbounded. -/
theorem not_isBounded_norm_gt (r : ℝ) :
    ¬ Bornology.IsBounded {z : ℂ | r < ‖z‖} := by
  intro hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  let t := max (max C r) 0 + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htC : C < t := lt_of_le_of_lt (le_max_left C r |>.trans (le_max_left _ 0))
    (lt_add_one _)
  have htr : r < t := lt_of_le_of_lt (le_max_right C r |>.trans (le_max_left _ 0))
    (lt_add_one _)
  have hn : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht]
  have hle := hC (t : ℂ) (show r < ‖(t : ℂ)‖ by rw [hn]; exact htr)
  rw [hn] at hle
  exact (not_lt_of_ge hle) htC




theorem existsUnique_isExternal [Finite V] [Finite E] :
    ∃! F : D.Face, D.IsExternal F := by
  classical
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp D.isCompact_image.isBounded
  let r := max C 0
  have hr : 0 ≤ r := le_max_right _ _
  let U : Set ℂ := {z | r < ‖z‖}
  have hU : IsConnected U := isConnected_norm_gt r hr
  have hUsub : U ⊆ D.imageᶜ := by
    intro z hz hzD
    exact (not_lt_of_ge ((hC z hzD).trans (le_max_left _ _))) hz
  obtain ⟨z, hz⟩ := hU.nonempty
  have hUcomp : U ⊆ connectedComponentIn D.imageᶜ z :=
    hU.isPreconnected.subset_connectedComponentIn hz hUsub
  let F : D.Face := ⟨connectedComponentIn D.imageᶜ z, z, hUsub hz, rfl⟩
  refine ⟨F, ?_, ?_⟩
  · intro hb
    exact not_isBounded_norm_gt r (hb.subset hUcomp)
  · intro G hG
    have hw : ∃ w ∈ G.val, r < ‖w‖ := by
      by_contra h
      apply hG
      exact isBounded_iff_forall_norm_le.mpr ⟨r, fun w hw =>
        le_of_not_gt (fun hlt => h ⟨w, hw, hlt⟩)⟩
    obtain ⟨w, hwG, hwU⟩ := hw
    obtain ⟨a, ha, hGa⟩ := G.property
    apply Subtype.ext
    change G.val = connectedComponentIn D.imageᶜ z
    have haw : connectedComponentIn D.imageᶜ a = connectedComponentIn D.imageᶜ w :=
      connectedComponentIn_eq (hGa ▸ hwG)
    have hUz : z ∈ connectedComponentIn D.imageᶜ w :=
      hU.isPreconnected.subset_connectedComponentIn hwU hUsub hz
    exact hGa.trans (haw.trans (connectedComponentIn_eq hUz))

end DirectedDistances.PlanarMap.PlaneGraphDrawing
