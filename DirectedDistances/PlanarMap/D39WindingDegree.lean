module

public import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedEquiv
public import DirectedDistances.PlanarMap.D39WindingExistence
import Mathlib.Topology.Homotopy.Lifting

/-! # Free homotopy and winding

Helpers toward Proposition 5.16. No numbered paper result is claimed here. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16: winding is invariant under a free homotopy
through loops avoiding the reference point; endpoint base points may differ. -/
theorem hasWinding_freeHomotopy {z₀ z₁ w : ℂ}
    {L₀ : Path z₀ z₀} {L₁ : Path z₁ z₁} {n : ℤ}
    (H : C(I × I, ℂ))
    (hH₀ : ∀ s, H (0, s) = L₀ s) (hH₁ : ∀ s, H (1, s) = L₁ s)
    (hloop : ∀ u, H (u, 1) = H (u, 0))
    (havoid : ∀ u s, H (u, s) ≠ w) (hw : HasWinding L₀ w n) :
    HasWinding L₁ w n := by
  obtain ⟨φ₀, hφ₀, hinc₀⟩ := hw
  have hnonzero (u : I × I) : H u - w ≠ 0 :=
    sub_ne_zero.mpr (havoid u.1 u.2)
  let G : C(I × I, {x : ℂ // x ≠ 0}) :=
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
  have hFexp (u s : I) : Complex.exp (F (u, s)) = H (u, s) - w := by
    simpa [G, Function.comp_apply] using
      congrArg Subtype.val (congrFun hFlift (u, s))
  have hFzero (s : I) : F (0, s) = φ₀ s := by
    simpa [F] using Complex.isCoveringMap_exp.liftHomotopy_zero G φ₀ hstart s
  let φ₁ : C(I, ℂ) := ⟨fun s => F (1, s), by fun_prop⟩
  have hφ₁ (s : I) : Complex.exp (φ₁ s) = L₁ s - w := by
    simpa [φ₁, hH₁ s] using hFexp 1 s
  let d : I → ℂ := fun u => F (u, 1) - F (u, 0)
  have hd : Continuous d := by fun_prop
  have hdexp (u : I) : Complex.exp (d u) = 1 := by
    dsimp [d]
    rw [Complex.exp_sub, hFexp u 1, hFexp u 0, hloop u]
    exact div_self (sub_ne_zero.mpr (havoid u 0))
  let T := AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ)
  let : DiscreteTopology T := NormedSpace.discreteTopology_zmultiples _
  have hdmem (u : I) : d u ∈ T := by
    have heq : Complex.exp (d u) = Complex.exp (0 : ℂ) := by simpa using hdexp u
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
    change d u ∈ AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ)
    rw [AddSubgroup.mem_zmultiples_iff]
    exact ⟨k, by simpa [zsmul_eq_mul, mul_comm] using hk.symm⟩
  let dT : I → T := fun u => ⟨d u, hdmem u⟩
  have hdTc : Continuous dT := Continuous.subtype_mk hd hdmem
  have hd10 : d 1 = d 0 := congrArg Subtype.val
    (PreconnectedSpace.constant inferInstance hdTc)
  refine ⟨φ₁, hφ₁, ?_⟩
  calc
    φ₁ 1 - φ₁ 0 = d 1 := rfl
    _ = d 0 := hd10
    _ = φ₀ 1 - φ₀ 0 := by
      change F (0, 1) - F (0, 0) = φ₀ 1 - φ₀ 0
      rw [hFzero 1, hFzero 0]
    _ = 2 * Real.pi * Complex.I * n := hinc₀

/-- Helper toward Proposition 5.16: two freely homotopic loops in a
punctured plane have equal winding integers. -/
theorem hasWinding_eq_of_freeHomotopy {z₀ z₁ w : ℂ}
    {L₀ : Path z₀ z₀} {L₁ : Path z₁ z₁} {m n : ℤ}
    (H : C(I × I, ℂ))
    (hH₀ : ∀ s, H (0, s) = L₀ s) (hH₁ : ∀ s, H (1, s) = L₁ s)
    (hloop : ∀ u, H (u, 1) = H (u, 0))
    (havoid : ∀ u s, H (u, s) ≠ w)
    (hm : HasWinding L₀ w m) (hn : HasWinding L₁ w n) : m = n :=
  hasWinding_unique (hasWinding_freeHomotopy H hH₀ hH₁ hloop havoid hm) hn

/-- Helper toward Proposition 5.16: loops with the same winding about a
point are freely homotopic in the complement of that point. -/
theorem exists_freeHomotopy_of_hasWinding {z₀ z₁ w : ℂ}
    {L₀ : Path z₀ z₀} {L₁ : Path z₁ z₁} {n : ℤ}
    (h₀ : HasWinding L₀ w n) (h₁ : HasWinding L₁ w n) :
    ∃ H : C(I × I, ℂ),
      (∀ s, H (0, s) = L₀ s) ∧ (∀ s, H (1, s) = L₁ s) ∧
      (∀ u, H (u, 1) = H (u, 0)) ∧ (∀ u s, H (u, s) ≠ w) := by
  obtain ⟨φ₀, hφ₀, hi₀⟩ := h₀
  obtain ⟨φ₁, hφ₁, hi₁⟩ := h₁
  let F : C(I × I, ℂ) :=
    ⟨fun p => (1 - (p.1 : ℝ) : ℂ) * φ₀ p.2 + (p.1 : ℝ) * φ₁ p.2,
      by fun_prop⟩
  have hi (u : I) : F (u, 1) = F (u, 0) + 2 * Real.pi * Complex.I * n := by
    have he₀ := eq_add_of_sub_eq hi₀
    have he₁ := eq_add_of_sub_eq hi₁
    dsimp [F]
    rw [he₀, he₁]
    ring
  have hperiod : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
    rw [mul_comm (2 * Real.pi * Complex.I), Complex.exp_int_mul,
      Complex.exp_two_pi_mul_I, one_zpow]
  refine ⟨⟨fun p => w + Complex.exp (F p), by fun_prop⟩, ?_, ?_, ?_, ?_⟩
  · intro s
    change w + Complex.exp (F (0, s)) = L₀ s
    simp only [F, ContinuousMap.coe_mk, Set.Icc.coe_zero, Complex.ofReal_zero,
      sub_zero, one_mul, zero_mul, add_zero, hφ₀]
    ring
  · intro s
    change w + Complex.exp (F (1, s)) = L₁ s
    simp only [F, ContinuousMap.coe_mk, Set.Icc.coe_one, Complex.ofReal_one,
      sub_self, zero_mul, one_mul, zero_add, hφ₁]
    ring
  · intro u
    change w + Complex.exp (F (u, 1)) = w + Complex.exp (F (u, 0))
    rw [hi u, Complex.exp_add, hperiod, mul_one]
  · intro u s he
    apply Complex.exp_ne_zero (F (u, s))
    exact add_left_cancel (he.trans (add_zero w).symm)

/-- Helper toward Proposition 5.16: free homotopies through omitted loops
preserve winding after applying a plane homeomorphism. -/
theorem hasWinding_map_freeHomotopy (h : ℂ ≃ₜ ℂ) {z₀ z₁ w : ℂ}
    {L₀ : Path z₀ z₀} {L₁ : Path z₁ z₁} {n : ℤ}
    (H : C(I × I, ℂ))
    (hH₀ : ∀ s, H (0, s) = L₀ s) (hH₁ : ∀ s, H (1, s) = L₁ s)
    (hloop : ∀ u, H (u, 1) = H (u, 0))
    (havoid : ∀ u s, H (u, s) ≠ w)
    (hw : HasWinding (L₀.map h.continuous) (h w) n) :
    HasWinding (L₁.map h.continuous) (h w) n := by
  apply hasWinding_freeHomotopy
    (⟨fun p => h (H p), h.continuous.comp H.continuous⟩ : C(I × I, ℂ))
    (fun s => congrArg h (hH₀ s)) (fun s => congrArg h (hH₁ s))
    (fun u => congrArg h (hloop u)) _ hw
  intro u s he
  exact havoid u s (h.injective he)

/-- Helper toward Proposition 5.16: equal winding classes have equal winding
classes after applying a plane homeomorphism. -/
theorem hasWinding_map_of_same_winding (h : ℂ ≃ₜ ℂ) {z₀ z₁ w : ℂ}
    {L₀ : Path z₀ z₀} {L₁ : Path z₁ z₁} {n m : ℤ}
    (h₀ : HasWinding L₀ w n) (h₁ : HasWinding L₁ w n)
    (hm : HasWinding (L₀.map h.continuous) (h w) m) :
    HasWinding (L₁.map h.continuous) (h w) m := by
  obtain ⟨H, hH₀, hH₁, hloop, havoid⟩ := exists_freeHomotopy_of_hasWinding h₀ h₁
  exact hasWinding_map_freeHomotopy h H hH₀ hH₁ hloop havoid hm

/-- Helper toward Proposition 5.16: the exponential has period `2πin` for
every integer `n`. -/
theorem exp_windingPeriod (n : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
  rw [mul_comm (2 * Real.pi * Complex.I), Complex.exp_int_mul,
    Complex.exp_two_pi_mul_I, one_zpow]

/-- Helper toward Proposition 5.16: the standard unit circle traversed an
integer number of times around a specified center. -/
@[expose] def windingCircle (w : ℂ) (n : ℤ) : Path (w + 1) (w + 1) where
  toFun t := w + Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℝ))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp only [Set.Icc.coe_one, Complex.ofReal_one, mul_one,
    exp_windingPeriod]

/-- Helper toward Proposition 5.16: the standard integer circle has its
specified winding integer. -/
theorem hasWinding_windingCircle (w : ℂ) (n : ℤ) :
    HasWinding (windingCircle w n) w n := by
  refine ⟨⟨fun t => 2 * Real.pi * Complex.I * (n : ℂ) * (t : ℝ),
    by fun_prop⟩, ?_, ?_⟩
  · intro t
    change Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℝ)) =
      w + Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℝ)) - w
    ring
  · simp

/-- Helper toward Proposition 5.16: the standard circles avoid their centers. -/
theorem windingCircle_ne_center (w : ℂ) (n : ℤ) (t : I) :
    windingCircle w n t ≠ w := by
  intro he
  apply Complex.exp_ne_zero (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℝ))
  exact add_left_cancel (he.trans (add_zero w).symm)

/-- Helper toward Proposition 5.16: the image of each standard circle has a
winding integer, so no default value is needed in choosing it. -/
theorem windingCircle_map_hasWinding_exists (h : ℂ ≃ₜ ℂ) (w : ℂ) (n : ℤ) :
    ∃ m : ℤ, HasWinding ((windingCircle w n).map h.continuous) (h w) m := by
  apply hasWinding_exists
  rintro ⟨t, ht⟩
  exact windingCircle_ne_center w n t (h.injective ht)

/-- Helper toward Proposition 5.16: the winding integer of the image of a
standard integer circle under a plane homeomorphism. -/
@[expose] def windingMap (h : ℂ ≃ₜ ℂ) (w : ℂ) (n : ℤ) : ℤ :=
  Classical.choose (windingCircle_map_hasWinding_exists h w n)

/-- Helper toward Proposition 5.16: characterization of the chosen image
winding integer. -/
theorem hasWinding_windingMap (h : ℂ ≃ₜ ℂ) (w : ℂ) (n : ℤ) :
    HasWinding ((windingCircle w n).map h.continuous) (h w) (windingMap h w n) :=
  Classical.choose_spec (windingCircle_map_hasWinding_exists h w n)

/-- Helper toward Proposition 5.16: complete characterization of the chosen
image winding integer of a standard integer circle. -/
theorem hasWinding_windingMap_iff (h : ℂ ≃ₜ ℂ) (w : ℂ) (n m : ℤ) :
    HasWinding ((windingCircle w n).map h.continuous) (h w) m ↔
      m = windingMap h w n := by
  constructor
  · intro hm
    exact hasWinding_unique hm (hasWinding_windingMap h w n)
  · rintro rfl
    exact hasWinding_windingMap h w n

/-- Helper toward Proposition 5.16: the image winding depends only on the
source winding, with no constraint on the source base point. -/
theorem hasWinding_map_windingMap (h : ℂ ≃ₜ ℂ) {z w : ℂ}
    {L : Path z z} {n : ℤ} (hn : HasWinding L w n) :
    HasWinding (L.map h.continuous) (h w) (windingMap h w n) :=
  hasWinding_map_of_same_winding h (hasWinding_windingCircle w n) hn
    (hasWinding_windingMap h w n)

/-- Helper toward Proposition 5.16: image winding is additive in source
winding. -/
theorem windingMap_add (h : ℂ ≃ₜ ℂ) (w : ℂ) (m n : ℤ) :
    windingMap h w (m + n) = windingMap h w m + windingMap h w n := by
  have hm := hasWinding_windingMap h w m
  have hn := hasWinding_windingMap h w n
  have hs := hasWinding_map_windingMap h
    (hasWinding_additive (hasWinding_windingCircle w m) (hasWinding_windingCircle w n))
  have heq : ((windingCircle w m).trans (windingCircle w n)).map h.continuous =
      ((windingCircle w m).map h.continuous).trans
        ((windingCircle w n).map h.continuous) := by
    exact Path.map_trans _ _ _
  rw [heq] at hs
  exact hasWinding_unique hs (hasWinding_additive hm hn)

/-- Helper toward Proposition 5.16: the degree at a point is the winding of
the image of its positively oriented unit circle. -/
@[expose] def windingDegree (h : ℂ ≃ₜ ℂ) (w : ℂ) : ℤ := windingMap h w 1

/-- Helper toward Proposition 5.16: a plane homeomorphism multiplies every
winding about a fixed point by its degree at that point. -/
theorem hasWinding_map_degree (h : ℂ ≃ₜ ℂ) {z w : ℂ}
    {L : Path z z} {n : ℤ} (hn : HasWinding L w n) :
    HasWinding (L.map h.continuous) (h w) (windingDegree h w * n) := by
  let F : ℤ →+ ℤ :=
    { toFun := windingMap h w
      map_zero' := by
        have he := windingMap_add h w 0 0
        simp only [add_zero] at he
        omega
      map_add' := windingMap_add h w }
  have he := map_zsmul F n (1 : ℤ)
  have hn' : windingMap h w n = windingDegree h w * n := by
    simpa [zsmul_eq_mul, F, windingDegree, mul_comm] using he
  rw [← hn']
  exact hasWinding_map_windingMap h hn

/-- Helper toward Proposition 5.16: the degrees of a homeomorphism and its
inverse at corresponding points multiply to one. -/
theorem windingDegree_symm_mul (h : ℂ ≃ₜ ℂ) (w : ℂ) :
    windingDegree h.symm (h w) * windingDegree h w = 1 := by
  have hback := hasWinding_map_degree h.symm (hasWinding_windingMap h w 1)
  have hback' : HasWinding (windingCircle w 1) w
      (windingDegree h.symm (h w) * windingDegree h w) := by
    obtain ⟨φ, hφ, hinc⟩ := hback
    refine ⟨φ, ?_, hinc⟩
    intro t
    simpa using hφ t
  exact hasWinding_unique hback' (hasWinding_windingCircle w 1)

/-- Helper toward Proposition 5.16: the degree of a plane homeomorphism at
each point is either one or minus one. -/
theorem windingDegree_eq_one_or_neg_one (h : ℂ ≃ₜ ℂ) (w : ℂ) :
    windingDegree h w = 1 ∨ windingDegree h w = -1 := by
  apply Int.eq_one_or_neg_one_of_mul_eq_one
  rw [mul_comm]
  exact windingDegree_symm_mul h w

/-- Helper toward Proposition 5.16: the degree of a plane homeomorphism is
locally constant as the omitted point varies. -/
theorem isLocallyConstant_windingDegree (h : ℂ ≃ₜ ℂ) :
    IsLocallyConstant (windingDegree h) := by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro w
  let L := windingCircle w 1
  have hw : HasWinding L w 1 := hasWinding_windingCircle w 1
  have hi : HasWinding (L.map h.continuous) (h w) (windingDegree h w) := by
    simpa only [mul_one] using hasWinding_map_degree h hw
  have ha (t : I) : L t ≠ w := windingCircle_ne_center w 1 t
  have hai (t : I) : (L.map h.continuous) t ≠ h w := by
    intro he
    exact ha t (h.injective he)
  obtain ⟨ε, hε, hs⟩ := hasWinding_stable_nearby L w 1 ha hw
  obtain ⟨δ, hδ, ht⟩ := hasWinding_stable_nearby
    (L.map h.continuous) (h w) (windingDegree h w) hai hi
  have hnh : ∀ᶠ w' in 𝓝 w, h w' ∈ Metric.ball (h w) δ :=
    h.continuous.continuousAt.tendsto.eventually (Metric.ball_mem_nhds (h w) hδ)
  filter_upwards [Metric.ball_mem_nhds w hε, hnh] with w' hw' hi'
  have hsource := hs w' hw'
  have htarget := ht (h w') hi'
  have hdegree := hasWinding_map_degree h hsource
  simp only [mul_one] at hdegree
  exact hasWinding_unique hdegree htarget

/-- Helper toward Proposition 5.16: the degree of a plane homeomorphism
is independent of the omitted point. -/
theorem windingDegree_eq (h : ℂ ≃ₜ ℂ) (w w' : ℂ) :
    windingDegree h w = windingDegree h w' :=
  (isLocallyConstant_windingDegree h).apply_eq_of_preconnectedSpace w w'

/-- Helper toward Proposition 5.16: at any omitted point, the winding
predicate transforms by multiplication by the degree, in both directions. -/
theorem hasWinding_map_degree_iff (h : ℂ ≃ₜ ℂ) {z : ℂ}
    (L : Path z z) (w : ℂ) (hw : w ∉ Set.range L) (n : ℤ) :
    HasWinding L w n ↔
      HasWinding (L.map h.continuous) (h w) (windingDegree h w * n) := by
  constructor
  · exact hasWinding_map_degree h
  · intro hn
    obtain ⟨m, hm⟩ := hasWinding_exists L w hw
    have he := hasWinding_unique (hasWinding_map_degree h hm) hn
    have hd : windingDegree h w ≠ 0 := by
      rcases windingDegree_eq_one_or_neg_one h w with hd | hd <;> omega
    have hmn : m = n := mul_left_cancel₀ hd he
    simpa only [hmn] using hm

/-- Helper toward Proposition 5.16: every plane homeomorphism either
preserves all winding integers or reverses all winding integers. -/
theorem orientationPreserving_or_reverses (h : ℂ ≃ₜ ℂ) :
    OrientationPreserving h ∨
      (∀ {z : ℂ} (L : Path z z) (w : ℂ), w ∉ Set.range L → ∀ n : ℤ,
        HasWinding L w n ↔ HasWinding (L.map h.continuous) (h w) (-n)) := by
  rcases windingDegree_eq_one_or_neg_one h 0 with hd | hd
  · left
    intro z L w hw n
    have hwdeg : windingDegree h w = 1 := (windingDegree_eq h w 0).trans hd
    simpa only [hwdeg, one_mul] using hasWinding_map_degree_iff h L w hw n
  · right
    intro z L w hw n
    have hwdeg : windingDegree h w = -1 := (windingDegree_eq h w 0).trans hd
    simpa only [hwdeg, neg_one_mul] using hasWinding_map_degree_iff h L w hw n

/-- Helper toward Proposition 5.16: preserving the winding of one loop
with winding one forces a plane homeomorphism to preserve every winding. -/
theorem orientationPreserving_of_hasWinding_one (h : ℂ ≃ₜ ℂ)
    {z : ℂ} (L : Path z z) (w : ℂ) (hw : w ∉ Set.range L)
    (h₁ : HasWinding L w 1)
    (h₂ : HasWinding (L.map h.continuous) (h w) 1) :
    OrientationPreserving h := by
  have hi := (hasWinding_map_degree_iff h L w hw 1).mp h₁
  simp only [mul_one] at hi
  have hd : windingDegree h w = 1 := hasWinding_unique hi h₂
  intro z' L' w' hw' n
  have hd' : windingDegree h w' = 1 := (windingDegree_eq h w' w).trans hd
  simpa only [hd', one_mul] using hasWinding_map_degree_iff h L' w' hw' n

end DirectedDistances.PlanarMap

end
