/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonWinding5

/-! # Logarithmic lift bridge for polygonal winding

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16: a path has lift increment c about w
when its translate by -w has a continuous logarithmic lift with endpoint
increment c. -/
@[expose] def HasLiftIncrement {a b : ℂ} (g : Path a b) (w c : ℂ) : Prop :=
  ∃ φ : C(unitInterval, ℂ),
    (∀ t, Complex.exp (φ t) = g t - w) ∧ φ 1 - φ 0 = c

/-- Helper toward Proposition 5.16: on a loop, lift increment is exactly the
continuous-logarithm formulation of HasWinding. -/
theorem hasLiftIncrement_iff_hasWinding {z w : ℂ} (L : Path z z) (n : ℤ) :
    HasLiftIncrement L w (2 * Real.pi * Complex.I * n) ↔ HasWinding L w n :=
  Iff.rfl

/-- Helper toward Proposition 5.16: the relative logarithm on a segment gives
a lift whose endpoint increment is the logarithm of the endpoint quotient. -/
theorem hasLiftIncrement_segment {a b w A : ℂ}
    (hA : Complex.exp A = a - w)
    (hquot : (b - w) / (a - w) ∈ Complex.slitPlane) :
    HasLiftIncrement (Path.segment a b) w (Complex.log ((b - w) / (a - w)) : ℂ) := by
  have ha : a - w ≠ 0 := by rw [← hA]; exact Complex.exp_ne_zero _
  let q : ℂ := (b - w) / (a - w)
  have hq : q ∈ Complex.slitPlane := by simpa [q] using hquot
  have hqcases := (Complex.mem_slitPlane_iff).mp hq
  have hratio (t : unitInterval) :
      ((Path.segment a b) t - w) / (a - w) =
        (1 - (t : ℂ)) + (t : ℂ) * q := by
    dsimp [q]
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
      Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    field_simp [ha]
    ring
  have hratio_slit (t : unitInterval) :
      ((Path.segment a b) t - w) / (a - w) ∈ Complex.slitPlane := by
    rw [hratio]
    rw [Complex.mem_slitPlane_iff]
    by_cases ht0 : (t : ℝ) = 0
    · left
      simp [ht0]
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
      have hre : ((1 - (t : ℂ)) + (t : ℂ) * q).re =
          1 - (t : ℝ) + (t : ℝ) * q.re := by simp
      have him : ((1 - (t : ℂ)) + (t : ℂ) * q).im =
          (t : ℝ) * q.im := by simp
      rcases hqcases with hqre | hqim
      · left
        rw [hre]
        nlinarith only [t.2.1, t.2.2, hqre, mul_pos htpos hqre]
      · right
        rw [him]
        exact mul_ne_zero (ne_of_gt htpos) hqim
  let φ : C(unitInterval, ℂ) :=
    ⟨fun t => A + Complex.log (((Path.segment a b) t - w) / (a - w)),
      continuous_const.add
        (((Path.segment a b).continuous.sub continuous_const).div_const (a - w) |>.clog
          hratio_slit)⟩
  refine ⟨φ, ?_, ?_⟩
  · intro t
    change Complex.exp (A + Complex.log (((Path.segment a b) t - w) / (a - w))) = _
    rw [Complex.exp_add, Complex.exp_log
      (Complex.slitPlane_ne_zero (hratio_slit t)), hA]
    dsimp [q] at hratio ⊢
    field_simp [ha]
  · change (A + Complex.log (((Path.segment a b) 1 - w) / (a - w))) -
      (A + Complex.log (((Path.segment a b) 0 - w) / (a - w))) = _
    simp [ha]

/-- Helper toward Proposition 5.16: lift increments add under path
concatenation, after shifting the second lift to agree at the junction. -/
theorem hasLiftIncrement_trans {a b c w c₁ c₂ : ℂ}
    {g₁ : Path a b} {g₂ : Path b c}
    (h₁ : HasLiftIncrement g₁ w c₁) (h₂ : HasLiftIncrement g₂ w c₂) :
    HasLiftIncrement (g₁.trans g₂) w (c₁ + c₂) := by
  obtain ⟨φ₁, hφ₁, hi₁⟩ := h₁
  obtain ⟨φ₂, hφ₂, hi₂⟩ := h₂
  have hj : g₁ 1 = g₂ 0 := by
    calc
      g₁ 1 = b := Path.target g₁
      _ = g₂ 0 := (Path.source g₂).symm
  have heq : Complex.exp (φ₁ 1) = Complex.exp (φ₂ 0) := by
    rw [hφ₁, hφ₂, hj]
  let d : ℂ := φ₁ 1 - φ₂ 0
  have hd : Complex.exp d = 1 := by
    dsimp [d]
    rw [Complex.exp_sub, heq]
    exact div_self (Complex.exp_ne_zero _)
  let φ₂' : C(unitInterval, ℂ) :=
    ⟨fun t => φ₂ t + d, φ₂.continuous.add continuous_const⟩
  have hφ₂' (t : unitInterval) : Complex.exp (φ₂' t) = g₂ t - w := by
    change Complex.exp (φ₂ t + d) = _
    rw [Complex.exp_add, hφ₂ t, hd]
    simp
  have hstart : φ₂' 0 = φ₁ 1 := by
    dsimp [φ₂', d]
    simp
  let α : Path (φ₁ 0) (φ₁ 1) := ⟨φ₁, rfl, rfl⟩
  let β : Path (φ₁ 1) (φ₂ 1 + d) := ⟨φ₂', hstart, rfl⟩
  let Ψ : C(unitInterval, ℂ) := (α.trans β).toContinuousMap
  have hΨ (t : unitInterval) : Complex.exp (Ψ t) = (g₁.trans g₂) t - w := by
    change Complex.exp ((α.trans β) t) = _
    rw [Path.trans_apply α β, Path.trans_apply g₁ g₂]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [dite_eq_left ht]
      exact hφ₁ _
    · simp only [dite_eq_right ht]
      exact hφ₂' _
  have hiΨ : Ψ 1 - Ψ 0 = c₁ + c₂ := by
    change (α.trans β) 1 - (α.trans β) 0 = _
    simp only [Path.target, Path.source]
    change φ₂ 1 + (φ₁ 1 - φ₂ 0) - φ₁ 0 = _
    calc
      (φ₂ 1 + (φ₁ 1 - φ₂ 0)) - φ₁ 0 =
          (φ₁ 1 - φ₁ 0) + (φ₂ 1 - φ₂ 0) := by ring
      _ = c₁ + c₂ := by rw [hi₁, hi₂]
  exact ⟨Ψ, hΨ, hiΨ⟩

/-- Helper toward Proposition 5.16: an edge quotient of a polyline avoiding
the viewpoint belongs to the slit plane of the principal logarithm. -/
theorem edgeRatio_mem_slitPlane (p : Polyline) (z : ℂ) (i : ℕ)
    (hi : i + 1 < p.points.length) (hz : z ∉ p.image) :
    ((p.point (i + 1) - z) / (p.point i - z)) ∈ Complex.slitPlane := by
  have harg := Polyline.edgeAngle_mem_Ioo p z i hi hz
  have harg' : Complex.arg
      ((p.point (i + 1) - z) / (p.point i - z)) < Real.pi := by
    simpa [Polyline.edgeAngle] using harg.2
  have hleft : p.point i ∈ p.image := by
    change p.point i ∈ {p.start} ∪
      {x : ℂ | ∃ j, j + 1 < p.points.length ∧ x ∈ p.segmentAt j}
    exact Or.inr ⟨i, by omega, left_mem_segment ℝ _ _⟩
  have hright : p.point (i + 1) ∈ p.image := by
    change p.point (i + 1) ∈ {p.start} ∪
      {x : ℂ | ∃ j, j + 1 < p.points.length ∧ x ∈ p.segmentAt j}
    exact Or.inr ⟨i, hi, right_mem_segment ℝ _ _⟩
  rw [Complex.mem_slitPlane_iff_arg]
  refine ⟨ne_of_lt harg', div_ne_zero ?_ ?_⟩
  · exact sub_ne_zero.mpr (fun h => hz (h ▸ hright))
  · exact sub_ne_zero.mpr (fun h => hz (h ▸ hleft))

/-- Helper toward Proposition 5.16: the sum of logarithmic segment
increments associated to a list of vertices. -/
def listLogIncrement (w a : ℂ) : List ℂ → ℂ
  | [] => 0
  | [b] => Complex.log ((b - w) / (a - w))
  | b :: c :: l =>
      Complex.log ((b - w) / (a - w)) + listLogIncrement w b (c :: l)

/-- Helper toward Proposition 5.16: the recursive path through a finite
vertex list has a logarithmic lift with the sum of its edge increments. -/
theorem listPath_hasLiftIncrement (z a : ℂ) :
    ∀ l : List ℂ, z ∉ (Polyline.ofHead a l).image →
      HasLiftIncrement (Polyline.listPath a l) z (listLogIncrement z a l) := by
  intro l
  induction l generalizing a with
  | nil =>
      intro hz
      have ha : a ≠ z := by
        intro h
        subst z
        apply hz
        simp [Polyline.image, Polyline.ofHead, Polyline.start]
      let φ : C(unitInterval, ℂ) := ⟨fun _ => Complex.log (a - z), continuous_const⟩
      have hpath (t : unitInterval) : Polyline.listPath a [] t = a := rfl
      refine ⟨φ, ?_, ?_⟩
      · intro t
        rw [hpath]
        exact Complex.exp_log (sub_ne_zero.mpr ha)
      · simp [φ, listLogIncrement]
  | cons b l ih =>
      cases l with
      | nil =>
          intro hz
          let p : Polyline := Polyline.ofHead a [b]
          have hlen : 1 < p.points.length := by simp [p, Polyline.ofHead]
          have hpavoid : z ∉ p.image := by simpa [p] using hz
          have hquot' := edgeRatio_mem_slitPlane p z 0 hlen hpavoid
          have hpa : p.point 0 = a := by
            simpa [p] using Polyline.point_ofHead_zero a [b]
          have hpb : p.point 1 = b := by
            change (Polyline.ofHead a [b]).point 1 = b
            rw [Polyline.point_ofHead_succ a b [] 0 (by simp : 0 < (b :: []).length)]
            exact Polyline.point_ofHead_zero b []
          have hquot : (b - z) / (a - z) ∈ Complex.slitPlane := by
            simpa [hpa, hpb] using hquot'
          have ha : a - z ≠ 0 := by
            apply sub_ne_zero.mpr
            have hmem : a ∈ p.image := by
              change a ∈ {p.start} ∪ _
              exact Or.inl (by simp [p, Polyline.ofHead, Polyline.start])
            intro h
            exact hpavoid (h ▸ hmem)
          simpa [Polyline.listPath, listLogIncrement] using
            hasLiftIncrement_segment (Complex.exp_log ha) hquot
      | cons c l =>
          intro hz
          have hzP : z ∉ (Polyline.ofHead a (b :: c :: l)).image := hz
          have hsplit := Polyline.image_ofHead_cons a b (c :: l)
          rw [hsplit] at hz
          have hzseg : z ∉ segment ℝ a b := fun h => hz (Or.inl h)
          have hztail : z ∉ (Polyline.ofHead b (c :: l)).image :=
            fun h => hz (Or.inr h)
          let p : Polyline := Polyline.ofHead a (b :: c :: l)
          have hlen : 1 < p.points.length := by simp [p, Polyline.ofHead]
          have hquot' := edgeRatio_mem_slitPlane p z 0 hlen (by simpa [p] using hzP)
          have hpa : p.point 0 = a := by
            simpa [p] using Polyline.point_ofHead_zero a (b :: c :: l)
          have hpb : p.point 1 = b := by
            change (Polyline.ofHead a (b :: c :: l)).point 1 = b
            rw [Polyline.point_ofHead_succ a b (c :: l) 0
              (by simp : 0 < (b :: c :: l).length)]
            exact Polyline.point_ofHead_zero b (c :: l)
          have hquot : (b - z) / (a - z) ∈ Complex.slitPlane := by
            simpa [hpa, hpb] using hquot'
          have ha : a - z ≠ 0 := by
            apply sub_ne_zero.mpr
            intro h
            apply hzseg
            simpa [h] using (left_mem_segment ℝ a b)
          have hfirst : HasLiftIncrement (Path.segment a b) z
              (Complex.log ((b - z) / (a - z))) :=
            hasLiftIncrement_segment (Complex.exp_log ha) hquot
          have hrest := ih b hztail
          change HasLiftIncrement
            ((Path.segment a b).trans (Polyline.listPath b (c :: l))) z
            (Complex.log ((b - z) / (a - z)) + listLogIncrement z b (c :: l))
          exact hasLiftIncrement_trans hfirst hrest




















end PlanarMap
end DirectedDistances

end
