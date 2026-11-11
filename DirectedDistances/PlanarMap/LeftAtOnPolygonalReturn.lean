/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact16
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact14
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact13
import DirectedDistances.PlanarMap.D39WindingDegree
import DirectedDistances.PlanarMap.D39BallOrbitComponents4
import DirectedDistances.PlanarMap.D39PLOrientedPlaneHomeomorph
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Close return paths toward Definition 3.2

Dyadic sampling gives endpoint-preserving uniform polygonal approximations.
For a path compactly contained in an open set, the straight homotopy stays in
that set. Canonical polyline traversal preserves the same lift increments.
For a boundary-to-boundary `LeftAtOn` return the proved global result allows
arbitrary endpoint neighborhoods. Exact face containment and simplicity are
integration belong to the sole coordinator. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric
open scoped Topology

/-- Helper toward Definition 3.2: pointwise perturbations smaller than the
distance to the reference point preserve precisely the winding integers. -/
theorem hasWinding_iff_of_pointwise_close32 {x y w : ℂ}
    (L : Path x x) (L' : Path y y)
    (hclose : ∀ t : I, dist (L' t) (L t) < dist (L t) w) (n : ℤ) :
    HasWinding L w n ↔ HasWinding L' w n := by
  have havoid (t : I) : L t ≠ w := by
    intro h
    have hlt := hclose t
    rw [h, dist_self] at hlt
    exact (not_lt_of_ge (dist_nonneg : 0 ≤ dist (L' t) w)) hlt
  have havoid' (t : I) : L' t ≠ w := by
    intro h
    have hlt := hclose t
    rw [h, dist_comm w (L t)] at hlt
    exact (lt_irrefl _ hlt)
  let H : C(I × I, ℂ) :=
    ⟨fun p => L p.2 + (p.1 : ℝ) • (L' p.2 - L p.2), by fun_prop⟩
  have hH0 (t : I) : H (0, t) = L t := by simp [H]
  have hH1 (t : I) : H (1, t) = L' t := by simp [H]
  have hloop (u : I) : H (u, 1) = H (u, 0) := by simp [H]
  have hav (u t : I) : H (u, t) ≠ w := by
    intro heq
    have hdist : dist (H (u, t)) (L t) ≤ dist (L' t) (L t) := by
      rw [dist_eq_norm, dist_eq_norm]
      change ‖L t + (u : ℝ) • (L' t - L t) - L t‖ ≤ ‖L' t - L t‖
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg u.2.1]
      exact (mul_le_mul_of_nonneg_right u.2.2 (norm_nonneg _)).trans_eq (one_mul _)
    rw [heq, dist_comm w (L t)] at hdist
    exact (not_lt_of_ge hdist) (hclose t)
  constructor
  · exact fun hw => hasWinding_freeHomotopy H hH0 hH1 hloop hav hw
  · intro hw
    let H' : C(I × I, ℂ) := ⟨fun p => H (σ p.1, p.2), by fun_prop⟩
    apply hasWinding_freeHomotopy H' (fun t => ?_) (fun t => ?_)
      (fun u => ?_) (fun u t => ?_) hw
    · simpa only [H', ContinuousMap.coe_mk, symm_zero] using hH1 t
    · simpa only [H', ContinuousMap.coe_mk, symm_one] using hH0 t
    · exact hloop (σ u)
    · exact hav (σ u) t

/-- Helper toward Definition 3.2: replacing only a return path by a close
path preserves winding about every point farther away than the perturbation.
The unchanged arc does not need to be polygonal. -/
theorem hasWinding_trans_iff_of_close_return32 {x y w : ℂ}
    (α : Path x y) (q q' : Path y x) (ε : ℝ)
    (hclose : ∀ t : I, dist (q' t) (q t) < ε)
    (hfar : ∀ t : I, ε ≤ dist (q t) w)
    (hα : ∀ t : I, α t ≠ w) (n : ℤ) :
    HasWinding (α.trans q) w n ↔ HasWinding (α.trans q') w n := by
  apply hasWinding_iff_of_pointwise_close32
  intro t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with ht
  · exact (dist_self _).trans_lt (dist_pos.mpr (hα _))
  · exact (hclose _).trans_le (hfar _)

/-- Helper toward Definition 3.2: every compact path in an open set has a
uniform radius of convex disks contained in that set. -/
theorem exists_uniform_path_ball_subset32 {x y : ℂ} {U : Set ℂ}
    (γ : Path x y) (hU : IsOpen U) (hγ : Set.range γ ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : I, ball (γ t) δ ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ :=
    (isCompact_range γ.continuous).exists_thickening_subset_open hU hγ
  exact ⟨δ, hδ, fun t => (ball_subset_thickening (mem_range_self t) δ).trans hsub⟩

/-- Helper toward Definition 3.2: paths sufficiently close to a compact
path in an open set admit the explicit straight homotopy relative to both
endpoints, entirely inside that open set. -/
theorem exists_straight_homotopy_in_open32 {x y : ℂ} {U : Set ℂ}
    (γ : Path x y) (hU : IsOpen U) (hγ : Set.range γ ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : Path x y,
      (∀ t : I, dist (q t) (γ t) < δ) →
      ∃ H : C(I × I, ℂ),
        (∀ t : I, H (0, t) = γ t) ∧
        (∀ t : I, H (1, t) = q t) ∧
        (∀ u : I, H (u, 0) = x) ∧
        (∀ u : I, H (u, 1) = y) ∧ Set.range H ⊆ U := by
  obtain ⟨δ, hδ, hball⟩ := exists_uniform_path_ball_subset32 γ hU hγ
  refine ⟨δ, hδ, fun q hq => ?_⟩
  let H : C(I × I, ℂ) :=
    ⟨fun p => γ p.2 + (p.1 : ℝ) • (q p.2 - γ p.2), by fun_prop⟩
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; simp [H]
  · intro t; simp [H]
  · intro u; simp [H]
  · intro u; simp [H]
  · rintro z ⟨⟨u, t⟩, rfl⟩
    apply hball t
    rw [mem_ball, dist_eq_norm]
    change ‖γ t + (u : ℝ) • (q t - γ t) - γ t‖ < δ
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg u.2.1]
    exact ((mul_le_mul_of_nonneg_right u.2.2 (norm_nonneg _)).trans_eq
      (one_mul _)).trans_lt (by simpa only [dist_eq_norm] using hq t)

private def leftHalfParam32 (t : I) : I :=
  ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

private def rightHalfParam32 (t : I) : I :=
  ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

private def midpointParam32 : I := ⟨1 / 2, by norm_num⟩

private def leftHalfPath32 {x y : ℂ} (γ : Path x y) :
    Path x (γ midpointParam32) where
  toFun t := γ (leftHalfParam32 t)
  continuous_toFun := by unfold leftHalfParam32; fun_prop
  source' := by
    have h : leftHalfParam32 0 = 0 := by apply Subtype.ext; norm_num [leftHalfParam32]
    change γ (leftHalfParam32 0) = x
    rw [h, γ.source]
  target' := rfl

private def rightHalfPath32 {x y : ℂ} (γ : Path x y) :
    Path (γ midpointParam32) y where
  toFun t := γ (rightHalfParam32 t)
  continuous_toFun := by unfold rightHalfParam32; fun_prop
  source' := by congr 1; apply Subtype.ext; norm_num [rightHalfParam32, midpointParam32]
  target' := by
    have h : rightHalfParam32 1 = 1 := by apply Subtype.ext; norm_num [rightHalfParam32]
    change γ (rightHalfParam32 1) = y
    rw [h, γ.target]

/-- Helper toward Definition 3.2: dyadic polygonal approximation joins the
path's samples by straight segments, concatenated in their original order.
At level `n` it traverses `2 ^ n` segments with equal time intervals. -/
def dyadicPolygonalApprox32 : (n : ℕ) → {x y : ℂ} → Path x y → Path x y
  | 0, x, y, _ => Path.segment x y
  | n + 1, _, _, γ =>
      (dyadicPolygonalApprox32 n (leftHalfPath32 γ)).trans
        (dyadicPolygonalApprox32 n (rightHalfPath32 γ))

private theorem halfParam_dist32 (s t : I) :
    dist (leftHalfParam32 s) (leftHalfParam32 t) = dist s t / 2 ∧
    dist (rightHalfParam32 s) (rightHalfParam32 t) = dist s t / 2 := by
  simp only [Subtype.dist_eq, Real.dist_eq, leftHalfParam32, rightHalfParam32]
  constructor
  · rw [← sub_div, abs_div]; norm_num
  · rw [show ((s : ℝ) + 1) / 2 - ((t : ℝ) + 1) / 2 = ((s : ℝ) - t) / 2 by ring,
      abs_div]
    norm_num

private theorem dyadicPolygonalApprox_close32 (n : ℕ) {x y : ℂ}
    (γ : Path x y) (ε : ℝ)
    (hosc : ∀ s t : I, dist s t ≤ (1 / 2 : ℝ) ^ n → dist (γ s) (γ t) < ε) :
    ∀ t : I, dist (dyadicPolygonalApprox32 n γ t) (γ t) < ε := by
  induction n generalizing x y with
  | zero =>
    intro t
    have h0 : x ∈ ball (γ t) ε := by
      have h := hosc 0 t (by
        simp only [pow_zero, Subtype.dist_eq, Real.dist_eq, Set.Icc.coe_zero]
        rw [abs_sub_comm, sub_zero, abs_of_nonneg t.2.1]
        exact t.2.2)
      simpa only [Path.source, mem_ball] using h
    have h1 : y ∈ ball (γ t) ε := by
      have h := hosc 1 t (by
        simp only [pow_zero, Subtype.dist_eq, Real.dist_eq, Set.Icc.coe_one]
        rw [abs_of_nonneg (sub_nonneg.mpr t.2.2)]
        linarith [t.2.1])
      simpa only [Path.target, mem_ball] using h
    exact (convex_ball (γ t) ε).segment_subset h0 h1
      ((Path.range_segment x y) ▸ mem_range_self t)
  | succ n ih =>
    have hleft := ih (leftHalfPath32 γ) (fun s t hst =>
      hosc (leftHalfParam32 s) (leftHalfParam32 t) (by
        rw [(halfParam_dist32 s t).1, pow_succ]
        linarith))
    have hright := ih (rightHalfPath32 γ) (fun s t hst =>
      hosc (rightHalfParam32 s) (rightHalfParam32 t) (by
        rw [(halfParam_dist32 s t).2, pow_succ]
        linarith))
    intro t
    change dist
      (((dyadicPolygonalApprox32 n (leftHalfPath32 γ)).trans
        (dyadicPolygonalApprox32 n (rightHalfPath32 γ))) t) (γ t) < ε
    rw [Path.trans_apply]
    split_ifs with ht
    · let u : I := ⟨2 * (t : ℝ), (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
      have hu : leftHalfParam32 u = t := by
        apply Subtype.ext
        dsimp [leftHalfParam32, u]
        ring
      have h := hleft u
      change dist (dyadicPolygonalApprox32 n (leftHalfPath32 γ) u)
        (γ (leftHalfParam32 u)) < ε at h
      rw [hu] at h
      exact h
    · let u : I := ⟨2 * (t : ℝ) - 1,
        two_mul_sub_one_mem_iff.2 ⟨(not_le.mp ht).le, t.2.2⟩⟩
      have hu : rightHalfParam32 u = t := by
        apply Subtype.ext
        dsimp [rightHalfParam32, u]
        ring
      have h := hright u
      change dist (dyadicPolygonalApprox32 n (rightHalfPath32 γ) u)
        (γ (rightHalfParam32 u)) < ε at h
      rw [hu] at h
      exact h

private theorem image_twoPointPolyline32 (x y : ℂ) :
    (⟨[x, y], by simp⟩ : Polyline).image = segment ℝ x y := by
  ext z
  constructor
  · rintro (hz | ⟨i, hi, hz⟩)
    · have hzx : z = x := hz
      exact hzx ▸ left_mem_segment ℝ z y
    · have hi0 : i = 0 := by change i + 1 < 2 at hi; omega
      subst i
      simpa [Polyline.segmentAt, Polyline.point, Polyline.start] using hz
  · intro hz
    exact Or.inr ⟨0, by simp,
      by simpa [Polyline.segmentAt, Polyline.point, Polyline.start] using hz⟩

/-- Helper toward Definition 3.2: every dyadic approximation has the image
and endpoints of a finite polyline. This does not assert simplicity. -/
theorem dyadicPolygonalApprox_exists_polyline32 (n : ℕ) {x y : ℂ} (γ : Path x y) :
    ∃ p : Polyline, p.start = x ∧ p.finish = y ∧
      p.image = Set.range (dyadicPolygonalApprox32 n γ) := by
  induction n generalizing x y with
  | zero =>
    refine ⟨⟨[x, y], by simp⟩, rfl, rfl, ?_⟩
    rw [image_twoPointPolyline32]
    exact (Path.range_segment x y).symm
  | succ n ih =>
    obtain ⟨p, hps, hpf, hpim⟩ := ih (leftHalfPath32 γ)
    obtain ⟨q, hqs, hqf, hqim⟩ := ih (rightHalfPath32 γ)
    have hjoin : p.finish = q.start := hpf.trans hqs.symm
    refine ⟨Polyline.boundaryConcat p q, ?_, ?_, ?_⟩
    · exact (Polyline.start_boundaryConcat p q).trans hps
    · exact (Polyline.finish_boundaryConcat_of_join p q hjoin).trans hqf
    · rw [Polyline.image_boundaryConcat p q hjoin, hpim, hqim]
      exact (Path.trans_range _ _).symm

/-- Helper toward Definition 3.2: continuous paths admit uniformly close
dyadic polygonal approximations with exactly the same endpoints. -/
theorem exists_dyadicPolygonalApprox_close32 {x y : ℂ}
    (γ : Path x y) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ t : I, dist (dyadicPolygonalApprox32 n γ t) (γ t) < ε := by
  obtain ⟨δ, hδ, hosc⟩ :=
    Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous γ.continuous) ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < δ :=
    exists_pow_lt_of_lt_one hδ (by norm_num)
  exact ⟨n, dyadicPolygonalApprox_close32 n γ ε
    (fun s t hst => hosc (hst.trans_lt hn))⟩

/-- Helper toward Definition 3.2: a path whose entire image is in an open
set has arbitrarily close polygonal approximations there, with an explicit
endpoint-fixing straight homotopy in that same open set. -/
theorem exists_polygonal_approx_homotopy_in_open32 {x y : ℂ} {U : Set ℂ}
    (γ : Path x y) (hU : IsOpen U) (hγ : Set.range γ ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ p : Polyline,
      p.start = x ∧ p.finish = y ∧
      p.image = Set.range (dyadicPolygonalApprox32 n γ) ∧ p.image ⊆ U ∧
      (∀ t : I, dist (dyadicPolygonalApprox32 n γ t) (γ t) < ε) ∧
      ∃ H : C(I × I, ℂ),
        (∀ t : I, H (0, t) = γ t) ∧
        (∀ t : I, H (1, t) = dyadicPolygonalApprox32 n γ t) ∧
        (∀ u : I, H (u, 0) = x) ∧
        (∀ u : I, H (u, 1) = y) ∧ Set.range H ⊆ U := by
  obtain ⟨δ, hδ, hhom⟩ := exists_straight_homotopy_in_open32 γ hU hγ
  obtain ⟨n, hn⟩ := exists_dyadicPolygonalApprox_close32 γ (lt_min hε hδ)
  obtain ⟨p, hps, hpf, hpim⟩ := dyadicPolygonalApprox_exists_polyline32 n γ
  obtain ⟨H, hH0, hH1, hHx, hHy, hHU⟩ :=
    hhom (dyadicPolygonalApprox32 n γ) (fun t => (hn t).trans_le (min_le_right _ _))
  refine ⟨n, p, hps, hpf, hpim, ?_,
    (fun t => (hn t).trans_le (min_le_left _ _)), H, hH0, hH1, hHx, hHy, hHU⟩
  rw [hpim]
  rintro z ⟨t, rfl⟩
  exact hH1 t ▸ hHU (mem_range_self (1, t))

/-- Helper toward Definition 3.2: for a loop in an open set, the same
polygonal approximation preserves every winding integer about every point
outside that set. Simple connectedness is not required. -/
theorem exists_polygonal_loop_approx_winding32 {x : ℂ} {U : Set ℂ}
    (γ : Path x x) (hU : IsOpen U) (hγ : Set.range γ ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ p : Polyline,
      p.start = x ∧ p.finish = x ∧
      p.image = Set.range (dyadicPolygonalApprox32 n γ) ∧ p.image ⊆ U ∧
      (∀ t : I, dist (dyadicPolygonalApprox32 n γ t) (γ t) < ε) ∧
      ∀ w : ℂ, w ∉ U → ∀ k : ℤ,
        (HasWinding γ w k ↔ HasWinding (dyadicPolygonalApprox32 n γ) w k) := by
  obtain ⟨n, p, hps, hpf, hpim, hpU, hn, H, hH0, hH1, hHx, hHy, hHU⟩ :=
    exists_polygonal_approx_homotopy_in_open32 γ hU hγ hε
  refine ⟨n, p, hps, hpf, hpim, hpU, hn, fun w hw k => ?_⟩
  have hloop (u : I) : H (u, 1) = H (u, 0) := (hHy u).trans (hHx u).symm
  have hav (u t : I) : H (u, t) ≠ w := by
    intro heq
    exact hw (heq ▸ hHU (mem_range_self (u, t)))
  constructor
  · exact fun hk => hasWinding_freeHomotopy H hH0 hH1 hloop hav hk
  · intro hk
    let H' : C(I × I, ℂ) := ⟨fun p => H (σ p.1, p.2), by fun_prop⟩
    apply hasWinding_freeHomotopy H' (fun t => ?_) (fun t => ?_)
      (fun u => hloop (σ u)) (fun u t => hav (σ u) t) hk
    · simpa only [H', ContinuousMap.coe_mk, symm_zero] using hH1 t
    · simpa only [H', ContinuousMap.coe_mk, symm_one] using hH0 t

/-- Helper toward Definition 3.2: an interior return path admits a
polygonal replacement in the open set which preserves winding of its
concatenation with any fixed arc, about every point outside the open set
and off the fixed arc. The same replacement works for all such points. -/
theorem exists_polygonal_return_approx_winding32 {x y : ℂ} {U : Set ℂ}
    (α : Path x y) (q : Path y x) (hU : IsOpen U) (hq : Set.range q ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ p : Polyline,
      p.start = y ∧ p.finish = x ∧
      p.image = Set.range (dyadicPolygonalApprox32 n q) ∧ p.image ⊆ U ∧
      (∀ t : I, dist (dyadicPolygonalApprox32 n q t) (q t) < ε) ∧
      ∀ w : ℂ, w ∉ U → w ∉ Set.range α → ∀ k : ℤ,
        (HasWinding (α.trans q) w k ↔
          HasWinding (α.trans (dyadicPolygonalApprox32 n q)) w k) := by
  obtain ⟨δ, hδ, hball⟩ := exists_uniform_path_ball_subset32 q hU hq
  obtain ⟨n, hn⟩ := exists_dyadicPolygonalApprox_close32 q (lt_min hε hδ)
  obtain ⟨p, hps, hpf, hpim⟩ := dyadicPolygonalApprox_exists_polyline32 n q
  refine ⟨n, p, hps, hpf, hpim, ?_,
    (fun t => (hn t).trans_le (min_le_left _ _)), fun w hw hα k => ?_⟩
  · rw [hpim]
    rintro z ⟨t, rfl⟩
    exact hball t ((hn t).trans_le (min_le_right _ _))
  · apply hasWinding_trans_iff_of_close_return32 α q _ δ
      (fun t => (hn t).trans_le (min_le_right _ _)) _ _ k
    · intro t
      by_contra hdist
      exact hw (hball t (by simpa only [mem_ball, dist_comm] using lt_of_not_ge hdist))
    · intro t ht
      exact hα ⟨t, ht⟩

/-- Helper toward Definition 3.2: restricting a return path to a closed
parameter interval strictly inside its open traversal puts its entire
restricted image in the open set. -/
theorem range_edgeSubarc_subset_of_open_traversal32 {x y : ℂ} {U : Set ℂ}
    (q : Path x y) (hq : ∀ t : I, t ∈ openParams → q t ∈ U)
    (a b : I) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    Set.range (edgeSubarc q a b hab) ⊆ U := by
  rintro z ⟨t, rfl⟩
  rw [edgeSubarc_apply_clamp]
  apply hq
  exact ⟨lt_of_lt_of_le ha (le_min (le_max_right _ _) hab),
    lt_of_le_of_lt (min_le_right _ _) hb⟩

/-- Helper toward Definition 3.2: every closed interior portion of a
`LeftAtOn` return has arbitrarily close polygonal replacements and an
endpoint-fixing homotopy in the face. The original return and winding-one
accumulation are retained; no winding claim for the full replacement is
inferred from this interior statement. -/
theorem exists_leftAtOn_interior_polygonal_homotopy32 {x y : ℂ}
    (U : Set ℂ) (γ : Path x y) (s : {t : I // t ∈ openParams})
    (hU : IsOpen U) (hleft : LeftAtOn U γ s) :
    ∃ a b : I, ∃ (_ha : 0 < a) (_has : a < s.1) (_hsb : s.1 < b)
      (_hb : b < 1), ∃ q : Path (γ b) (γ a),
      Function.Injective q ∧
      (∀ t : I, t ∈ openParams → q t ∈ U) ∧
      γ s.1 ∈ closure {w : ℂ | w ∈ U ∧ HasWinding
        ((edgeSubarc γ a b (le_of_lt (lt_trans _has _hsb))).trans q) w 1} ∧
      ∀ c d : I, ∀ (_hc : 0 < c) (_hd : d < 1) (hcd : c ≤ d),
        ∀ ε : ℝ, 0 < ε →
        ∃ n : ℕ, ∃ p : Polyline,
          p.start = q c ∧ p.finish = q d ∧
          p.image = Set.range (dyadicPolygonalApprox32 n (edgeSubarc q c d hcd)) ∧
          p.image ⊆ U ∧
          (∀ t : I, dist (dyadicPolygonalApprox32 n (edgeSubarc q c d hcd) t)
            (edgeSubarc q c d hcd t) < ε) ∧
          ∃ H : C(I × I, ℂ),
            (∀ t : I, H (0, t) = edgeSubarc q c d hcd t) ∧
            (∀ t : I, H (1, t) = dyadicPolygonalApprox32 n (edgeSubarc q c d hcd) t) ∧
            (∀ u : I, H (u, 0) = q c) ∧
            (∀ u : I, H (u, 1) = q d) ∧ Set.range H ⊆ U := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hqi, hq, hcl⟩ := hleft
  refine ⟨a, b, ha, has, hsb, hb, q, hqi, hq, hcl, ?_⟩
  intro c d hc hd hcd ε hε
  exact exists_polygonal_approx_homotopy_in_open32 (edgeSubarc q c d hcd) hU
    (range_edgeSubarc_subset_of_open_traversal32 q hq c d hc hd hcd) hε

/-- Helper toward Definition 3.2: a close change of the return path
preserves winding accumulation at a point separated from the whole return. -/
theorem mem_closure_winding_trans_of_close_return32 {x y z : ℂ}
    (α : Path x y) (q q' : Path y x) (U : Set ℂ) (k : ℤ)
    {r : ℝ} (hr : 0 < r)
    (hdisj : Disjoint (ball z (2 * r)) (Set.range q))
    (hclose : ∀ t : I, dist (q' t) (q t) < r)
    (hcl : z ∈ closure {w : ℂ | w ∈ U ∧ HasWinding (α.trans q) w k}) :
    z ∈ closure {w : ℂ | w ∈ U ∧ HasWinding (α.trans q') w k} := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨w, ⟨hwU, hw⟩, hwnear⟩ :=
    Metric.mem_closure_iff.mp hcl (min ε r) (lt_min hε hr)
  have hwr : dist z w < r := hwnear.trans_le (min_le_right _ _)
  have hfar (t : I) : r ≤ dist (q t) w := by
    by_contra hlt
    have hdist : dist (q t) z < 2 * r := calc
      dist (q t) z ≤ dist (q t) w + dist w z := dist_triangle _ _ _
      _ < 2 * r := by rw [dist_comm w z]; linarith [lt_of_not_ge hlt]
    exact Set.disjoint_left.mp hdisj hdist (mem_range_self t)
  have hα (t : I) : α t ≠ w := by
    intro heq
    apply hw.not_mem_range
    rw [Path.trans_range]
    exact Or.inl ⟨t, heq⟩
  exact ⟨w, ⟨hwU, (hasWinding_trans_iff_of_close_return32 α q q' r
    hclose hfar hα k).mp hw⟩, hwnear.trans_le (min_le_left _ _)⟩

/-- Helper toward Definition 3.2: a `LeftAtOn` return in an actual drawn
face has an endpoint-preserving polygonal approximation retaining its
winding-one accumulation. Its image stays in the face apart from arbitrary
small neighborhoods of the two original boundary endpoints. Neither
simplicity nor endpoint-only intersection is asserted for this approximation. -/
theorem exists_leftAtOn_polygonal_return_endpoint_neighborhoods32
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (hF : IsOpen F.val) (s : {t : I // t ∈ openParams})
    (hleft : LeftAtOn F.val (P.arc d).toPath s)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ a b : I, ∃ (_ha : 0 < a) (_has : a < s.1) (_hsb : s.1 < b)
      (_hb : b < 1), ∃ q : Path ((P.arc d).toPath b) ((P.arc d).toPath a),
      Function.Injective q ∧
      (∀ t : I, t ∈ openParams → q t ∈ F.val) ∧
      ∃ n : ℕ, ∃ p : Polyline,
        p.start = (P.arc d).toPath b ∧ p.finish = (P.arc d).toPath a ∧
        p.image = Set.range (dyadicPolygonalApprox32 n q) ∧
        p.image ⊆ F.val ∪ ball ((P.arc d).toPath b) η ∪ ball ((P.arc d).toPath a) η ∧
        (∀ t : I, dist (dyadicPolygonalApprox32 n q t) (q t) < ε) ∧
        (P.arc d).toPath s.1 ∈ closure {w : ℂ | w ∈ F.val ∧ HasWinding
          ((edgeSubarc (P.arc d).toPath a b (le_of_lt (lt_trans _has _hsb))).trans
            (dyadicPolygonalApprox32 n q)) w 1} := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, hcl⟩ := hleft
  obtain ⟨R, hR, hdisj⟩ := P.exists_ball_disjoint_returnPath32 d F a b s has hsb q hqF
  let O := F.val ∪ ball ((P.arc d).toPath b) η ∪ ball ((P.arc d).toPath a) η
  have hO : IsOpen O := (hF.union isOpen_ball).union isOpen_ball
  have hqO : Set.range q ⊆ O := by
    rintro z ⟨t, rfl⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl (Or.inr (by simpa only [Path.source] using mem_ball_self hη))
    by_cases ht1 : t = 1
    · subst t
      exact Or.inr (by simpa only [Path.target] using mem_ball_self hη)
    exact Or.inl (Or.inl (hqF t
      ⟨unitInterval.pos_iff_ne_zero.mpr ht0, unitInterval.lt_one_iff_ne_one.mpr ht1⟩))
  obtain ⟨n, p, hps, hpf, hpim, hpO, hn, _⟩ :=
    exists_polygonal_approx_homotopy_in_open32 q hO hqO (lt_min hε (half_pos hR))
  refine ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, n, p, hps, hpf, hpim, hpO,
    (fun t => (hn t).trans_le (min_le_left _ _)), ?_⟩
  apply mem_closure_winding_trans_of_close_return32 _ q _ F.val 1 (half_pos hR)
    (by convert hdisj using 1; congr 2; ring)
    (fun t => (hn t).trans_le (min_le_right _ _)) hcl

/-- Helper toward Definition 3.2: the finite polyline for a dyadic
approximation has the same logarithmic lift increments under its canonical
traversal. Thus the different time allocations introduce no winding gap. -/
theorem dyadicPolygonalApprox_exists_polyline_lift32 (n : ℕ) {x y : ℂ}
    (γ : Path x y) :
    ∃ p : Polyline, p.start = x ∧ p.finish = y ∧ 2 ≤ p.points.length ∧
      p.image = Set.range (dyadicPolygonalApprox32 n γ) ∧
      ∀ w v : ℂ, HasLiftIncrement p.toPath w v ↔
        HasLiftIncrement (dyadicPolygonalApprox32 n γ) w v := by
  induction n generalizing x y with
  | zero =>
    refine ⟨⟨[x, y], by simp⟩, rfl, rfl, by simp, ?_, ?_⟩
    · rw [image_twoPointPolyline32]
      exact (Path.range_segment x y).symm
    · intro w v
      rfl
  | succ n ih =>
    obtain ⟨p, hps, hpf, hplen, hpim, hplift⟩ := ih (leftHalfPath32 γ)
    obtain ⟨q, hqs, hqf, hqlen, hqim, hqlift⟩ := ih (rightHalfPath32 γ)
    have hjoin : p.finish = q.start := hpf.trans hqs.symm
    refine ⟨p.boundaryConcat q, (Polyline.start_boundaryConcat p q).trans hps,
      (Polyline.finish_boundaryConcat_of_join p q hjoin).trans hqf, ?_, ?_, ?_⟩
    · rw [Polyline.length_boundaryConcat]
      omega
    · rw [Polyline.image_boundaryConcat p q hjoin, hpim, hqim]
      exact (Path.trans_range _ _).symm
    · intro w v
      have hcat := hasLiftIncrement_boundaryConcat_iff
        (ContinuousMap.id ℂ) p q hplen hqlen hjoin w v
      simp only [ContinuousMap.coe_id, Path.map_id] at hcat
      rw [hcat]
      change (∃ v₁ v₂ : ℂ, HasLiftIncrement p.toPath w v₁ ∧
        HasLiftIncrement q.toPath w v₂ ∧ v = v₁ + v₂) ↔
        HasLiftIncrement ((dyadicPolygonalApprox32 n (leftHalfPath32 γ)).trans
          (dyadicPolygonalApprox32 n (rightHalfPath32 γ))) w v
      rw [hasLiftIncrement_trans_iff]
      simp only [hplift, hqlift]

/- Helper toward Definition 3.2: a `LeftAtOn` return in a drawn face
admits a finite polyline with its two boundary endpoints and the full
winding-one accumulation for the canonical `Polyline.toPath` traversal.
The image is in the face except within prescribed endpoint neighborhoods; -/
theorem exists_leftAtOn_polyline_return_endpoint_neighborhoods32
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (hF : IsOpen F.val) (s : {t : I // t ∈ openParams})
    (hleft : LeftAtOn F.val (P.arc d).toPath s)
    {η : ℝ} (hη : 0 < η) :
    ∃ a b : I, ∃ (_ha : 0 < a) (_has : a < s.1) (_hsb : s.1 < b)
      (_hb : b < 1), ∃ p : Polyline,
      ∃ (hstart : (P.arc d).toPath b = p.start)
        (hfinish : (P.arc d).toPath a = p.finish),
        2 ≤ p.points.length ∧
        p.image ⊆ F.val ∪ ball ((P.arc d).toPath b) η ∪ ball ((P.arc d).toPath a) η ∧
        (P.arc d).toPath s.1 ∈ closure {w : ℂ | w ∈ F.val ∧ HasWinding
          ((edgeSubarc (P.arc d).toPath a b (le_of_lt (lt_trans _has _hsb))).trans
            (p.toPath.cast hstart hfinish)) w 1} := by
  obtain ⟨a, b, ha, has, hsb, hb, q, _, _, n, p₀, _, _, hp₀im, hp₀O, _, hcl⟩ :=
    exists_leftAtOn_polygonal_return_endpoint_neighborhoods32 P d F hF s hleft
      hη (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨p, hps, hpf, hplen, hpim, hplift⟩ :=
    dyadicPolygonalApprox_exists_polyline_lift32 n q
  have hpO : p.image ⊆ F.val ∪ ball ((P.arc d).toPath b) η ∪
      ball ((P.arc d).toPath a) η := by
    rw [hpim, ← hp₀im]
    exact hp₀O
  refine ⟨a, b, ha, has, hsb, hb, p, hps.symm, hpf.symm, hplen, hpO, ?_⟩
  apply closure_mono _ hcl
  rintro w ⟨hwF, hw⟩
  refine ⟨hwF, ?_⟩
  change HasLiftIncrement _ w (2 * Real.pi * Complex.I * (1 : ℤ))
  have hcast (v : ℂ) : HasLiftIncrement (p.toPath.cast hps.symm hpf.symm) w v ↔
      HasLiftIncrement (dyadicPolygonalApprox32 n q) w v :=
    (hasLiftIncrement_congr_fun _ p.toPath (fun _ => rfl)).trans (hplift w v)
  rw [hasLiftIncrement_trans_iff]
  change HasLiftIncrement _ w (2 * Real.pi * Complex.I * (1 : ℤ)) at hw
  obtain ⟨v₁, v₂, hv₁, hv₂, hv⟩ := (hasLiftIncrement_trans_iff _ _).mp hw
  exact ⟨v₁, v₂, hv₁, (hcast v₂).mpr hv₂, hv⟩





















































end DirectedDistances.PlanarMap

end
