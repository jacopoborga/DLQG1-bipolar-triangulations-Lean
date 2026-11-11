/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLDiskArcGluing
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Order.IntermediateValue

import Mathlib.Order.CompleteLatticeIntervals

/-! # Proper arcs on the circle

Helpers toward Proposition 5.16. The slit argument gives a real coordinate
for an arc avoiding a chosen point; the identification with a standard path
is recorded separately from the imported standard-path complement formula. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

/-- Helper toward Proposition 5.16: rotate a chosen circle point to `-1`. -/
def rotateCircleAt (c z : Circle) : Circle := -c⁻¹ * z

/-- Helper toward Proposition 5.16: the rotation sends its chosen point to `-1`. -/
theorem rotateCircleAt_self (c : Circle) : rotateCircleAt c c = -1 := by
  simp [rotateCircleAt]

/-- Helper toward Proposition 5.16: rotation is injective. -/
theorem rotateCircleAt_injective (c : Circle) : Function.Injective (rotateCircleAt c) := by
  intro x y h
  dsimp [rotateCircleAt] at h
  exact mul_left_cancel h

/-- Helper toward Proposition 5.16: the slit argument is the real coordinate
of the rotated circle point. -/
def rotatedCircleArg (c z : Circle) : ℝ := Complex.arg ((rotateCircleAt c z : Circle) : ℂ)

/-- Helper toward Proposition 5.16: away from the cut point, the rotated
argument lies strictly between `-π` and `π`. -/
theorem rotatedCircleArg_mem_Ioo (c z : Circle) (hz : z ≠ c) :
    rotatedCircleArg c z ∈ Set.Ioo (-Real.pi) Real.pi := by
  have hrot : rotateCircleAt c z ≠ -1 := by
    intro h
    apply hz
    have h' := congrArg (fun w : Circle => -c * w) h
    simpa [rotateCircleAt] using h'
  have harg : Complex.arg ((rotateCircleAt c z : Circle) : ℂ) ≠ Real.pi := by
    intro h
    apply hrot
    have h1 : ((rotateCircleAt c z : Circle) : ℂ).arg = (((-1 : Circle) : ℂ).arg) := by
      change Complex.arg ((rotateCircleAt c z : Circle) : ℂ) = Complex.arg (-1 : ℂ)
      rw [Complex.arg_neg_one]
      exact h
    exact Circle.injective_arg h1
  constructor
  · exact Complex.neg_pi_lt_arg _
  · exact lt_of_le_of_ne (Complex.arg_le_pi _) harg

/-- Helper toward Proposition 5.16: the rotated argument is continuous on the
circle with the chosen point removed. -/
theorem continuousOn_rotatedCircleArg (c : Circle) :
    ContinuousOn (rotatedCircleArg c) ({z : Circle | z ≠ c}) := by
  have hrot : Continuous fun z : Circle => ((rotateCircleAt c z : Circle) : ℂ) := by
    exact continuous_subtype_val.comp (continuous_const.mul continuous_id)
  have hmaps : Set.MapsTo (fun z : Circle => ((rotateCircleAt c z : Circle) : ℂ))
      {z : Circle | z ≠ c} Complex.slitPlane := by
    intro z hz
    rw [Complex.mem_slitPlane_iff_arg]
    constructor
    · exact (rotatedCircleArg_mem_Ioo c z hz).2.ne
    · apply norm_ne_zero_iff.mp
      simpa only [Circle.norm_coe] using (one_ne_zero : (1 : ℝ) ≠ 0)
  change ContinuousOn (fun z : Circle => Complex.arg ((rotateCircleAt c z : Circle) : ℂ)) _
  exact Complex.continuousOn_arg.comp hrot.continuousOn hmaps

/-- Helper toward Proposition 5.16: the slit argument is injective on the
circle with the chosen point removed. -/
theorem injectiveOn_rotatedCircleArg (c : Circle) :
    Set.InjOn (rotatedCircleArg c) {z : Circle | z ≠ c} := by
  intro x hx y hy hxy
  apply rotateCircleAt_injective c
  exact Circle.injective_arg (by simpa [rotatedCircleArg] using hxy)

/-- Helper toward Proposition 5.16: a continuous injective real-valued map
on the closed interval has as range the closed interval between its endpoint
values. -/
theorem continuousInjective_Icc_range {f : Set.Icc (-1 : ℝ) 1 → ℝ}
    (hf : Continuous f) (hi : Function.Injective f) :
    (StrictMono f ∨ StrictAnti f) ∧
      Set.range f = Set.Icc
        (min (f ⟨-1, by norm_num⟩) (f ⟨1, by norm_num⟩))
        (max (f ⟨-1, by norm_num⟩) (f ⟨1, by norm_num⟩)) := by
  let g : ℝ → ℝ := fun x => if hx : x ∈ Set.Icc (-1 : ℝ) 1 then f ⟨x, hx⟩ else 0
  have hg_mem (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : g x = f ⟨x, hx⟩ := by
    change (if hx' : x ∈ Set.Icc (-1 : ℝ) 1 then f ⟨x, hx'⟩ else 0) = _
    rw [dite_eq_left hx]
  have hg : ContinuousOn g (Set.Icc (-1 : ℝ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hfun : (fun x : Set.Icc (-1 : ℝ) 1 => g x) = f := by
      funext x
      exact hg_mem x x.property
    change Continuous (fun x : Set.Icc (-1 : ℝ) 1 => g x)
    rw [hfun]
    exact hf
  have hgi : Set.InjOn g (Set.Icc (-1 : ℝ) 1) := by
    intro x hx y hy hxy
    have hsub : f ⟨x, hx⟩ = f ⟨y, hy⟩ := by
      rw [← hg_mem x hx, ← hg_mem y hy]
      exact hxy
    exact congrArg Subtype.val (hi hsub)
  have hmono := hg.strictMonoOn_of_injOn_Icc' (by norm_num) hgi
  have hImage : Set.range f = g '' Set.Icc (-1 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, by rw [hg_mem x x.property]⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hx⟩, by rw [← hg_mem x hx]; exact hxy⟩
  rcases hmono with hm | ha
  · have hfm : StrictMono f := by
      intro x y hxy
      rw [← hg_mem x x.property, ← hg_mem y y.property]
      exact hm x.property y.property hxy
    have hrange : Set.range f = Set.Icc (g (-1)) (g 1) := by
      rw [hImage]
      exact hg.image_Icc_of_monotoneOn (by norm_num) hm.monotoneOn
    have h01 : g (-1) ≤ g 1 := (hm (by norm_num) (by norm_num) (by norm_num)).le
    have h01f : f ⟨-1, by norm_num⟩ ≤ f ⟨1, by norm_num⟩ := by
      rw [← hg_mem (-1) (by norm_num), ← hg_mem 1 (by norm_num)]
      exact h01
    have hleft : g (-1) = f ⟨-1, by norm_num⟩ := hg_mem _ (by norm_num)
    have hright : g 1 = f ⟨1, by norm_num⟩ := hg_mem _ (by norm_num)
    refine ⟨Or.inl hfm, ?_⟩
    rw [hleft, hright] at hrange
    simpa [min_eq_left h01f, max_eq_right h01f] using hrange
  · have hfa : StrictAnti f := by
      intro x y hxy
      rw [← hg_mem x x.property, ← hg_mem y y.property]
      exact ha x.property y.property hxy
    have hrange : Set.range f = Set.Icc (g 1) (g (-1)) := by
      rw [hImage]
      exact hg.image_Icc_of_antitoneOn (by norm_num) ha.antitoneOn
    have h10 : g 1 ≤ g (-1) := (ha (by norm_num) (by norm_num) (by norm_num)).le
    have h10f : f ⟨1, by norm_num⟩ ≤ f ⟨-1, by norm_num⟩ := by
      rw [← hg_mem 1 (by norm_num), ← hg_mem (-1) (by norm_num)]
      exact h10
    have hleft : g (-1) = f ⟨-1, by norm_num⟩ := hg_mem _ (by norm_num)
    have hright : g 1 = f ⟨1, by norm_num⟩ := hg_mem _ (by norm_num)
    refine ⟨Or.inr hfa, ?_⟩
    rw [hleft, hright] at hrange
    simpa [min_eq_right h10f, max_eq_left h10f] using hrange

/-- Helper toward Proposition 5.16: cutting the circle at a point missed by
an embedded interval turns its argument into a continuous injective real
function, hence a strictly monotone or antitone function with interval range. -/
theorem rotatedCircleArg_interval_range
    (phi : Set.Icc (-1 : ℝ) 1 → Circle) (hphi : Continuous phi)
    (hinj : Function.Injective phi) (c : Circle) (hc : ∀ t, phi t ≠ c) :
    (StrictMono (fun t => rotatedCircleArg c (phi t)) ∨
      StrictAnti (fun t => rotatedCircleArg c (phi t))) ∧
      Set.range (fun t => rotatedCircleArg c (phi t)) = Set.Icc
        (min (rotatedCircleArg c (phi ⟨-1, by norm_num⟩))
          (rotatedCircleArg c (phi ⟨1, by norm_num⟩)))
        (max (rotatedCircleArg c (phi ⟨-1, by norm_num⟩))
          (rotatedCircleArg c (phi ⟨1, by norm_num⟩))) := by
  let f : Set.Icc (-1 : ℝ) 1 → ℝ := fun t => rotatedCircleArg c (phi t)
  have hf : Continuous f := by
    dsimp [f]
    have hmaps : Set.MapsTo phi Set.univ {z : Circle | z ≠ c} := by
      intro t _
      exact hc t
    exact continuousOn_univ.mp
      ((continuousOn_rotatedCircleArg c).comp hphi.continuousOn hmaps)
  have hfi : Function.Injective f := by
    intro x y hxy
    apply hinj
    exact injectiveOn_rotatedCircleArg c (hc x) (hc y) hxy
  simpa [f] using continuousInjective_Icc_range hf hfi

/-- Helper toward Proposition 5.16: a standard circle path is homeomorphic
to the closed interval, with its two endpoints retained. -/
theorem exists_homeomorph_Icc_circlePath_range {x y : Circle} (hxy : x ≠ y) :
    ∃ e : Set.Icc (-1 : ℝ) 1 ≃ₜ Set.range (Circle.path x y),
      (e ⟨-1, by norm_num⟩ : Set.range (Circle.path x y)) = ⟨x, by
        exact ⟨⟨0, by norm_num⟩, by simp⟩⟩ ∧
      (e ⟨1, by norm_num⟩ : Set.range (Circle.path x y)) = ⟨y, by
        exact ⟨⟨1, by norm_num⟩, by simp⟩⟩ := by
  let q : Set.Icc (-1 : ℝ) 1 → unitInterval := fun t =>
    ⟨((t : ℝ) + 1) / 2, by
      constructor
      · linarith [t.property.1]
      · linarith [t.property.2]⟩
  have hqcont : Continuous q := by
    exact ((continuous_subtype_val.add continuous_const).div_const 2).subtype_mk _
  have hqinj : Function.Injective q := by
    intro a b hab
    apply Subtype.ext
    have hab' := congrArg (fun u : unitInterval => (u : ℝ)) hab
    dsimp [q] at hab'
    linarith
  have hqsurj : Function.Surjective q := by
    intro u
    let t : Set.Icc (-1 : ℝ) 1 := ⟨2 * (u : ℝ) - 1, by
      constructor <;> linarith [u.property.1, u.property.2]⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    dsimp [q, t]
    ring
  have hqleft : q ⟨-1, by norm_num⟩ = 0 := by
    apply Subtype.ext
    simp [q]
  have hqright : q ⟨1, by norm_num⟩ = 1 := by
    apply Subtype.ext
    simp [q]
  let p := Circle.path x y
  let f : Set.Icc (-1 : ℝ) 1 → Set.range p := fun t => ⟨p (q t), ⟨q t, rfl⟩⟩
  have hfi : Function.Injective f := by
    intro a b hab
    have hpab := congrArg Subtype.val hab
    have hqab : q a = q b := (Circle.path_injective_of_ne hxy) hpab
    exact hqinj hqab
  have hfs : Function.Surjective f := by
    intro z
    rcases z.property with ⟨u, hu⟩
    obtain ⟨t, ht⟩ := hqsurj u
    refine ⟨t, ?_⟩
    apply Subtype.ext
    change p (q t) = z.val
    rw [ht]
    exact hu
  have hfc : Continuous f := by
    exact (p.continuous.comp hqcont).subtype_mk _
  let e : Set.Icc (-1 : ℝ) 1 ≃ Set.range p := Equiv.ofBijective f ⟨hfi, hfs⟩
  let H : Set.Icc (-1 : ℝ) 1 ≃ₜ Set.range p :=
    hfc.homeoOfEquivCompactToT2 (f := e)
  refine ⟨H, ?_, ?_⟩
  · apply Subtype.ext
    change p (q ⟨-1, by norm_num⟩) = x
    rw [hqleft]
    simp [p]
  · apply Subtype.ext
    change p (q ⟨1, by norm_num⟩) = y
    rw [hqright]
    simp [p]






































end DirectedDistances.PlanarMap
