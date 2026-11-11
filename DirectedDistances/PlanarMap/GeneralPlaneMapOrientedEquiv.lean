/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMapSideDegree
public import DirectedDistances.PlanarMap.GeneralPlaneMapInvariance

/-! # Orientation-preserving equivalences of general plane maps

orientation preservation is defined by preservation of winding numbers of
loops about points off the loop. This is the degree-`+1` characterization and
makes winding-side transport a direct consequence of the property field. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Definition 1.1: a homeomorphism preserves the winding
number of every loop about every point outside that loop. This choice of
definition makes orientation-preserving transport of winding-side tests a
direct consequence of the property. -/
@[expose] def OrientationPreserving (f : ℂ ≃ₜ ℂ) : Prop :=
  ∀ {z : ℂ} (L : Path z z) (w : ℂ), w ∉ Set.range L → ∀ n : ℤ,
    HasWinding L w n ↔ HasWinding (L.map f.continuous) (f w) n

/-- Helper toward Definition 1.1: the identity homeomorphism preserves
winding numbers. -/
theorem orientationPreserving_refl :
    OrientationPreserving (Homeomorph.refl ℂ) := by
  intro z L w hw n
  have hmap : (L.map (Homeomorph.refl ℂ).continuous) = L := by
    apply Path.ext
    funext t
    rfl
  rw [hmap]
  rfl

/-- Helper toward Definition 1.1: a composition of winding-preserving
homeomorphisms preserves winding numbers. -/
theorem OrientationPreserving.trans {f g : ℂ ≃ₜ ℂ}
    (hf : OrientationPreserving f) (hg : OrientationPreserving g) :
    OrientationPreserving (f.trans g) := by
  intro z L w hw n
  have hwf : f w ∉ Set.range (L.map f.continuous) := by
    rintro ⟨t, ht⟩
    apply hw
    refine ⟨t, ?_⟩
    apply f.injective
    simpa using ht
  have hpath : (L.map (f.trans g).continuous) =
      (L.map f.continuous).map g.continuous := by
    apply Path.ext
    funext t
    rfl
  rw [hpath]
  exact (hf L w hw n).trans (hg (L.map f.continuous) (f w) hwf n)

/-- Helper toward Definition 1.1: the inverse of a winding-preserving
homeomorphism preserves winding numbers. -/
theorem OrientationPreserving.symm {f : ℂ ≃ₜ ℂ}
    (hf : OrientationPreserving f) : OrientationPreserving f.symm := by
  intro z L w hw n
  have hw' : f.symm w ∉ Set.range (L.map f.symm.continuous) := by
    rintro ⟨t, ht⟩
    apply hw
    refine ⟨t, ?_⟩
    have h := congrArg f ht
    simpa using h
  have hpath : (L.map f.symm.continuous).map f.continuous =
      L.cast (f.apply_symm_apply z) (f.apply_symm_apply z) := by
    apply Path.ext
    funext t
    simp
  have h := hf (L.map f.symm.continuous) (f.symm w) hw' n
  have hcast : HasWinding
      (L.cast (f.apply_symm_apply z) (f.apply_symm_apply z)) w n ↔
      HasWinding L w n := by
    constructor
    · rintro ⟨φ, hφ, hinc⟩
      refine ⟨φ, ?_, hinc⟩
      intro t
      exact hφ t
    · rintro ⟨φ, hφ, hinc⟩
      refine ⟨φ, ?_, hinc⟩
      intro t
      exact hφ t
  have h' : HasWinding (L.map f.symm.continuous) (f.symm w) n ↔
      HasWinding L w n := by
    calc
      _ ↔ HasWinding
          ((L.map f.symm.continuous).map f.continuous)
            (f (f.symm w)) n := h
      _ ↔ HasWinding
          (L.cast (f.apply_symm_apply z) (f.apply_symm_apply z)) w n := by
        rw [hpath]
        rw [f.apply_symm_apply w]
      _ ↔ HasWinding L w n := hcast
  exact h'.symm

/-- Helper toward Definition 1.1: a directed drawing equivalence whose plane
homeomorphism preserves winding numbers. The orientation condition is the only
additional field beyond the existing directed `HomeoEquiv`. -/
structure DirectedPlaneMap.OrientedHomeoEquiv
    {V E V' E' : Type*} (M : DirectedPlaneMap V E)
    (M' : DirectedPlaneMap V' E') where
  /-- Helper toward Definition 1.1: the underlying directed drawing
  equivalence. -/
  toHomeoEquiv : DirectedPlaneMap.HomeoEquiv M M'
  /-- Helper toward Definition 1.1: the plane homeomorphism preserves
  winding numbers. -/
  orientationPreserving :
    OrientationPreserving toHomeoEquiv.drawing.h



















end DirectedDistances.PlanarMap

end
