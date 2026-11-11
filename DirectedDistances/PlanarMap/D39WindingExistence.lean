module

public import DirectedDistances.PlanarMap.D39CyclicOrderWinding2
public import DirectedDistances.PlanarMap.D39PolygonWinding
public import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-! # Logarithmic winding lifts

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16: every loop has a logarithmic winding
integer about any point outside its image. -/
theorem hasWinding_exists {z : ℂ} (L : Path z z) (w : ℂ)
    (havoid : w ∉ Set.range L) : ∃ n : ℤ, HasWinding L w n := by
  let f : C(unitInterval, ℂ) := ⟨fun t => L t - w, L.continuous.sub continuous_const⟩
  have hzero (t : unitInterval) : f t ≠ 0 := by
    intro ht
    apply havoid
    exact ⟨t, sub_eq_zero.mp (by simpa [f] using ht)⟩
  let γ : Path (⟨f 0, hzero 0⟩ : {x : ℂ // x ≠ 0})
      (⟨f 1, hzero 1⟩ : {x : ℂ // x ≠ 0}) :=
    { toFun := fun t => ⟨f t, hzero t⟩
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
  have hbase : Complex.exp (Complex.log (f 0)) = f 0 :=
    Complex.exp_log (hzero 0)
  let φ := Complex.isCoveringMap_exp.liftPath γ (Complex.log (f 0)) (by
    apply Subtype.ext
    exact hbase.symm)
  have hφ (t : unitInterval) : Complex.exp (φ t) = f t := by
    have ht := congrFun
      (Complex.isCoveringMap_exp.liftPath_lifts γ (Complex.log (f 0)) (by
        apply Subtype.ext
        exact hbase.symm)) t
    exact congrArg Subtype.val ht
  have hloop : Complex.exp (φ 1) = Complex.exp (φ 0) := by
    rw [hφ, hφ]
    simp [f, L.source, L.target]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hloop
  refine ⟨n, φ, ?_, ?_⟩
  · intro t
    simpa [f] using hφ t
  · rw [hn]
    ring

/-- Helper toward Proposition 5.16: winding integers add under concatenation
of loops at a common base point. -/
theorem hasWinding_additive {z w : ℂ} {L₁ L₂ : Path z z} {m n : ℤ}
    (h₁ : HasWinding L₁ w m) (h₂ : HasWinding L₂ w n) :
    HasWinding (L₁.trans L₂) w (m + n) :=
  hasWinding_trans_loop h₁ h₂

/-- Helper toward Proposition 5.16: winding is invariant under a homotopy of
loops that avoids the reference point. -/
theorem hasWinding_homotopy {z w : ℂ} {L₀ L₁ : Path z z} {n : ℤ}
    (H : C(unitInterval × unitInterval, ℂ))
    (hH₀ : ∀ s, H (0, s) = L₀ s) (hH₁ : ∀ s, H (1, s) = L₁ s)
    (hloop : ∀ u, H (u, 1) = H (u, 0))
    (havoid : ∀ u s, H (u, s) ≠ w) (hw : HasWinding L₀ w n) :
    HasWinding L₁ w n := by
  obtain ⟨φ₀, hφ₀, hinc₀⟩ := hw
  have hnonzero (u : unitInterval × unitInterval) : H u - w ≠ 0 := by
    intro h
    exact havoid u.1 u.2 (sub_eq_zero.mp h)
  let G : C(unitInterval × unitInterval, {x : ℂ // x ≠ 0}) :=
    { toFun := fun u => ⟨H u - w, hnonzero u⟩
      continuous_toFun := by fun_prop }
  have hstart : ∀ s, G (0, s) =
      ⟨Complex.exp (φ₀ s), Complex.exp_ne_zero _⟩ := by
    intro s
    apply Subtype.ext
    change H (0, s) - w = Complex.exp (φ₀ s)
    rw [hH₀ s]
    exact (hφ₀ s).symm
  let F := Complex.isCoveringMap_exp.liftHomotopy G φ₀ hstart
  have hFlift : (fun x : ℂ => (⟨Complex.exp x, Complex.exp_ne_zero x⟩ :
      {x : ℂ // x ≠ 0})) ∘ F = G :=
    Complex.isCoveringMap_exp.liftHomotopy_lifts G φ₀ hstart
  have hFexp (u s : unitInterval) : Complex.exp (F (u, s)) = H (u, s) - w := by
    simpa [G, Function.comp_apply] using
      congrArg Subtype.val (congrFun hFlift (u, s))
  have hFzero (s : unitInterval) : F (0, s) = φ₀ s := by
    simpa [F] using Complex.isCoveringMap_exp.liftHomotopy_zero G φ₀ hstart s
  let φ₁ : C(unitInterval, ℂ) := ⟨fun s => F (1, s), by fun_prop⟩
  have hφ₁ (s : unitInterval) : Complex.exp (φ₁ s) = L₁ s - w := by
    simpa [φ₁, hH₁ s] using hFexp 1 s
  let d : unitInterval → ℂ := fun u => F (u, 1) - F (u, 0)
  have hd : Continuous d := by fun_prop
  have hdexp (u : unitInterval) : Complex.exp (d u) = 1 := by
    dsimp [d]
    rw [Complex.exp_sub, hFexp u 1, hFexp u 0, hloop u]
    exact div_self (sub_ne_zero.mpr (havoid u 0))
  let T := AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ)
  letI : DiscreteTopology T := NormedSpace.discreteTopology_zmultiples _
  have hdmem (u : unitInterval) : d u ∈ T := by
    have heq : Complex.exp (d u) = Complex.exp (0 : ℂ) := by simpa using hdexp u
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
    change d u ∈ AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ)
    rw [AddSubgroup.mem_zmultiples_iff]
    exact ⟨k, by simpa [zsmul_eq_mul, mul_comm] using hk.symm⟩
  let dT : unitInterval → T := fun u => ⟨d u, hdmem u⟩
  have hdTc : Continuous dT := Continuous.subtype_mk hd hdmem
  have hd10 : d 1 = d 0 := congrArg Subtype.val
    (PreconnectedSpace.constant inferInstance hdTc)
  have hinc : φ₁ 1 - φ₁ 0 = φ₀ 1 - φ₀ 0 := by
    calc
      φ₁ 1 - φ₁ 0 = d 1 := rfl
      _ = d 0 := hd10
      _ = φ₀ 1 - φ₀ 0 := by
        change F (0, 1) - F (0, 0) = φ₀ 1 - φ₀ 0
        rw [hFzero 1, hFzero 0]
  refine ⟨φ₁, hφ₁, ?_⟩
  calc
    φ₁ 1 - φ₁ 0 = φ₀ 1 - φ₀ 0 := hinc
    _ = 2 * Real.pi * Complex.I * n := hinc₀

/-- Helper toward Proposition 5.16: the winding integer is constant on any
preconnected subset of the complement of a loop image. -/
theorem hasWinding_value_constant_on_preconnected {z : ℂ} (L : Path z z)
    (U : Set ℂ) (hU : U ⊆ (Set.range L)ᶜ) (hconn : IsPreconnected U) :
    ∃ n : ℤ, ∀ w ∈ U, HasWinding L w n := by
  let ω : U → ℤ := fun x => Classical.choose
    (hasWinding_exists L x.1 (fun h => hU x.2 h))
  have hω (x : U) : HasWinding L x.1 (ω x) :=
    Classical.choose_spec (hasWinding_exists L x.1 (fun h => hU x.2 h))
  have hloc : IsLocallyConstant ω := by
    apply ((IsLocallyConstant.tfae ω).out 2 1).mp
    intro x
    have havoid : ∀ t : unitInterval, L t ≠ (x : ℂ) := by
      intro t ht
      exact hU x.2 ⟨t, ht⟩
    obtain ⟨ε, hε, hnear⟩ :=
      hasWinding_value_eq_of_nearby L x.1 (ω x) havoid (hω x)
    filter_upwards [Metric.ball_mem_nhds x hε] with y hy
    have hy' : dist (y : ℂ) (x : ℂ) < ε := by simpa [Subtype.dist_eq] using hy
    exact hnear y hy' (ω y) (hω y)
  by_cases hempty : U.Nonempty
  · obtain ⟨x, hx⟩ := hempty
    letI : PreconnectedSpace U := Subtype.preconnectedSpace hconn
    let x' : U := ⟨x, hx⟩
    refine ⟨ω x', ?_⟩
    intro w hw
    let y : U := ⟨w, hw⟩
    have hxy : ω y = ω x' := hloc.apply_eq_of_preconnectedSpace y x'
    simpa [y, hxy] using hω y
  · exact ⟨0, fun w hw => (hempty ⟨w, hw⟩).elim⟩

/-- Helper toward Proposition 5.16: a loop contained in a disk has winding
zero about points outside that disk. -/
theorem hasWinding_zero_of_norm_bound {z w : ℂ} (L : Path z z) {R : ℝ}
    (hR : 0 ≤ R) (hbound : ∀ t, ‖L t‖ ≤ R) (hfar : R < ‖w‖) :
    HasWinding L w 0 := by
  have hw : w ≠ 0 := by
    intro h
    subst w
    exact (not_lt_of_ge hR) (by simpa using hfar)
  have hden : -w ≠ 0 := neg_ne_zero.mpr hw
  let q : unitInterval → ℂ := fun t => (L t - w) / (-w)
  have hqcont : Continuous q := by
    dsimp [q]
    exact (L.continuous.sub continuous_const).div_const _
  have hquot (t : unitInterval) : q t - 1 = L t / (-w) := by
    dsimp [q]
    field_simp [hden]
    ring
  have hqnorm (t : unitInterval) : ‖q t - 1‖ < 1 := by
    rw [hquot, norm_div]
    apply (div_lt_one (norm_pos_iff.mpr hden)).2
    simpa [norm_neg] using (hbound t).trans_lt hfar
  have hqslit (t : unitInterval) : q t ∈ Complex.slitPlane := by
    apply Complex.ball_one_subset_slitPlane
    change dist (q t) 1 < 1
    rw [dist_eq_norm]
    exact hqnorm t
  have hq01 : q 1 = q 0 := by simp [q, L.source, L.target]
  let φ : C(unitInterval, ℂ) :=
    ⟨fun t => Complex.log (-w) + Complex.log (q t),
      continuous_const.add (hqcont.clog hqslit)⟩
  refine ⟨φ, ?_, ?_⟩
  · intro t
    change Complex.exp (Complex.log (-w) + Complex.log (q t)) = L t - w
    rw [Complex.exp_add, Complex.exp_log hden,
      Complex.exp_log (Complex.slitPlane_ne_zero (hqslit t))]
    dsimp [q]
    field_simp [hden]
  · dsimp [φ]
    rw [hq01]
    simp
































end DirectedDistances.PlanarMap

end
