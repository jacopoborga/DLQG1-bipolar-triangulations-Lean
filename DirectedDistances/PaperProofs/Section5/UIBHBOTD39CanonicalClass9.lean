/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass8
public import DirectedDistances.PlanarMap.HasWindingTransfer
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Helper toward Definition 3.8 (consumer).

# Orientation under a vertical seam transfer -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open unitInterval

/-- Helper toward Definition 3.8 (consumer): center a loop at the image of a
point under a plane homeomorphism. -/
private def uibhbotCenteredLoop {z : ℂ} (L : Path z z) (h : ℂ ≃ₜ ℂ) (w : ℂ) :
    Path (h z - h w) (h z - h w) :=
  L.map (h.continuous.sub continuous_const)

/-- Helper toward Definition 3.8 (consumer): translating the image loop's
base point into the origin does not change its logarithmic winding lift. -/
private theorem uibhbotHasWinding_centered_iff {z : ℂ} (L : Path z z)
    (h : ℂ ≃ₜ ℂ) (w : ℂ) (n : ℤ) :
    HasWinding (uibhbotCenteredLoop L h w) 0 n ↔
      HasWinding (L.map h.continuous) (h w) n := by
  unfold HasWinding
  constructor
  · rintro ⟨φ, hφ, hinc⟩
    refine ⟨φ, ?_, hinc⟩
    intro t
    have heq : (uibhbotCenteredLoop L h w) t = (L.map h.continuous) t - h w := by
      rfl
    calc
      Complex.exp (φ t) = (uibhbotCenteredLoop L h w) t - 0 := hφ t
      _ = (L.map h.continuous) t - h w := by rw [heq]; simp
  · rintro ⟨φ, hφ, hinc⟩
    refine ⟨φ, ?_, hinc⟩
    intro t
    have heq : (uibhbotCenteredLoop L h w) t = (L.map h.continuous) t - h w := by
      rfl
    calc
      Complex.exp (φ t) = (L.map h.continuous) t - h w := hφ t
      _ = (uibhbotCenteredLoop L h w) t - 0 := by rw [heq]; simp

/-- Helper toward Definition 3.8 (consumer): a continuous family of plane
homeomorphisms beginning at the identity preserves every logarithmic winding
number. Joint continuity is stated on the time and plane variables. -/
theorem uibhbotHasWinding_of_continuous_isotopy
    (H : I → ℂ ≃ₜ ℂ)
    (hH : Continuous (fun p : I × ℂ => H p.1 p.2))
    (hH0 : H 0 = Homeomorph.refl ℂ) :
    {z : ℂ} → (L : Path z z) → (w : ℂ) → w ∉ Set.range L → (n : ℤ) →
      (HasWinding L w n ↔ HasWinding (L.map (H 1).continuous) (H 1 w) n) := by
  intro z L w hw n
  let displacement : I × I → ℂ := fun p => H p.1 (L p.2) - H p.1 w
  have hdisplacement_cont : Continuous displacement := by
    dsimp [displacement]
    exact (hH.comp (continuous_fst.prodMk
      (L.continuous.comp continuous_snd))).sub
      (hH.comp (continuous_fst.prodMk continuous_const))
  have hdisplacement_ne : ∀ p, displacement p ≠ 0 := by
    rintro ⟨t, s⟩ hz
    have hLs : L s ≠ w := fun heq => hw ⟨s, heq⟩
    apply hLs
    apply (H t).injective
    exact sub_eq_zero.mp hz
  let ratio : (I × I) × I → ℂ := fun p =>
    displacement (p.1.2, p.2) / displacement (p.1.1, p.2)
  have hratio_cont : Continuous ratio := by
    dsimp [ratio]
    apply Continuous.div
    · exact hdisplacement_cont.comp (continuous_fst.snd.prodMk continuous_snd)
    · exact hdisplacement_cont.comp (continuous_fst.fst.prodMk continuous_snd)
    · intro p
      exact hdisplacement_ne (p.1.1, p.2)
  have hratio_uniform : UniformContinuous ratio :=
    CompactSpace.uniformContinuous_of_continuous hratio_cont
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.uniformContinuous_iff.mp hratio_uniform) 1 zero_lt_one
  have hratio_near (t u : I) (htu : dist t u < δ) (s : I) :
      ratio ((t, u), s) ∈ Complex.slitPlane := by
    have hinput : dist ((t, u), s) ((t, t), s) < δ := by
      simpa only [dist_prod_same_right, dist_prod_same_left, dist_comm] using htu
    have hclose := hδ hinput
    have hbase : ratio ((t, t), s) = 1 := by
      simp [ratio, hdisplacement_ne]
    rw [hbase] at hclose
    have hnorm : ‖ratio ((t, u), s) - 1‖ < 1 := by
      simpa only [dist_eq_norm] using hclose
    have hmem := Complex.mem_slitPlane_of_norm_lt_one hnorm
    convert hmem using 1
    ring
  have hstep (t u : I) (htu : dist t u < δ) :
      HasWinding (uibhbotCenteredLoop L (H t) w) 0 n ↔
        HasWinding (uibhbotCenteredLoop L (H u) w) 0 n := by
    constructor
    · intro hwind
      apply hasWinding_of_ratio_mem_slitPlane
          (uibhbotCenteredLoop L (H t) w)
          (uibhbotCenteredLoop L (H u) w) 0 n
      · intro s
        have hne : H t (L s) - H t w ≠ 0 := by
          apply sub_ne_zero.mpr
          intro heq
          have hLs : L s ≠ w := fun heq' => hw ⟨s, heq'⟩
          exact hLs ((H t).injective heq)
        simpa [uibhbotCenteredLoop] using hne
      · intro s
        have hne : H u (L s) - H u w ≠ 0 := by
          apply sub_ne_zero.mpr
          intro heq
          have hLs : L s ≠ w := fun heq' => hw ⟨s, heq'⟩
          exact hLs ((H u).injective heq)
        simpa [uibhbotCenteredLoop] using hne
      · intro s
        have hmem := hratio_near t u htu s
        simpa [ratio, displacement, uibhbotCenteredLoop] using hmem
      · exact hwind
    · intro hwind
      apply hasWinding_of_ratio_mem_slitPlane
          (uibhbotCenteredLoop L (H u) w)
          (uibhbotCenteredLoop L (H t) w) 0 n
      · intro s
        have hne : H u (L s) - H u w ≠ 0 := by
          apply sub_ne_zero.mpr
          intro heq
          have hLs : L s ≠ w := fun heq' => hw ⟨s, heq'⟩
          exact hLs ((H u).injective heq)
        simpa [uibhbotCenteredLoop] using hne
      · intro s
        have hne : H t (L s) - H t w ≠ 0 := by
          apply sub_ne_zero.mpr
          intro heq
          have hLs : L s ≠ w := fun heq' => hw ⟨s, heq'⟩
          exact hLs ((H t).injective heq)
        simpa [uibhbotCenteredLoop] using hne
      · intro s
        have hmem := hratio_near u t (by simpa [dist_comm] using htu) s
        simpa [ratio, displacement, uibhbotCenteredLoop] using hmem
      · exact hwind
  have hNreal : ∃ N : ℕ, (1 : ℝ) / δ < (N : ℝ) := exists_nat_gt (1 / δ)
  obtain ⟨N, hN⟩ := hNreal
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℝ) < 1 / δ := one_div_pos.mpr hδpos
    linarith
  have hgrid : (1 : ℝ) / (N : ℝ) < δ := by
    have hmul : (1 : ℝ) < δ * (N : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hδpos).mp hN
    apply (div_lt_iff₀ hNpos).mpr
    simpa [mul_comm] using hmul
  let τ : ℕ → I := fun k =>
    ⟨((min k N : ℕ) : ℝ) / (N : ℝ),
      ⟨by positivity,
        (div_le_one₀ hNpos).mpr (by exact_mod_cast (Nat.min_le_right k N))⟩⟩
  have hτdist (k : ℕ) (hk : k < N) : dist (τ k) (τ (k + 1)) < δ := by
    have hmin₁ : min k N = k := Nat.min_eq_left (Nat.le_of_lt hk)
    have hmin₂ : min (k + 1) N = k + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hk)
    change dist (((min k N : ℕ) : ℝ) / (N : ℝ))
      (((min (k + 1) N : ℕ) : ℝ) / (N : ℝ)) < δ
    rw [Real.dist_eq]
    simp only [hmin₁, hmin₂, Nat.cast_succ]
    rw [show ↑k / (N : ℝ) - (↑k + 1) / (N : ℝ) = -(1 / (N : ℝ)) by
      field_simp
      ring]
    rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
    exact hgrid
  have hτN : τ N = 1 := by
    have hNne : N ≠ 0 := by exact_mod_cast (ne_of_gt hNpos)
    apply Subtype.ext
    simp [τ, hNne]
  let Q : I → Prop := fun t => HasWinding (uibhbotCenteredLoop L (H t) w) 0 n
  have hchain : ∀ k, Q 0 ↔ Q (τ k) := by
    intro k
    induction k with
    | zero =>
        simp [τ, Q]
    | succ k ih =>
        by_cases hk : k < N
        · exact ih.trans (hstep (τ k) (τ (k + 1)) (hτdist k hk))
        · have hkN : N ≤ k := Nat.le_of_not_gt hk
          have htau : τ (k + 1) = τ k := by
            apply Subtype.ext
            simp only [τ]
            rw [Nat.min_eq_right hkN,
              Nat.min_eq_right (Nat.le_trans hkN (Nat.le_succ k))]
          simpa [htau] using ih
  have hQends : Q 0 ↔ Q 1 := by
    simpa [hτN] using hchain N
  have hstart : Q 0 ↔ HasWinding L w n := by
    dsimp [Q]
    rw [hH0]
    unfold HasWinding
    constructor
    · rintro ⟨φ, hφ, hinc⟩
      refine ⟨φ, ?_, hinc⟩
      intro t
      have heq : (uibhbotCenteredLoop L (Homeomorph.refl ℂ) w) t = L t - w := by rfl
      calc
        Complex.exp (φ t) = (uibhbotCenteredLoop L (Homeomorph.refl ℂ) w) t - 0 := hφ t
        _ = L t - w := by rw [heq]; simp
    · rintro ⟨φ, hφ, hinc⟩
      refine ⟨φ, ?_, hinc⟩
      intro t
      have heq : (uibhbotCenteredLoop L (Homeomorph.refl ℂ) w) t = L t - w := by rfl
      calc
        Complex.exp (φ t) = L t - w := hφ t
        _ = (uibhbotCenteredLoop L (Homeomorph.refl ℂ) w) t - 0 := by rw [heq]; simp
  have hend : Q 1 ↔ HasWinding (L.map (H 1).continuous) (H 1 w) n := by
    exact uibhbotHasWinding_centered_iff L (H 1) w n
  exact hstart.symm.trans (hQends.trans hend)

/-- Helper toward Definition 3.8 (consumer): a continuous family of plane
homeomorphisms beginning at the identity is orientation-preserving at its
endpoint. -/
theorem uibhbotOrientationPreserving_of_continuous_isotopy
    (H : I → ℂ ≃ₜ ℂ)
    (hH : Continuous (fun p : I × ℂ => H p.1 p.2))
    (hH0 : H 0 = Homeomorph.refl ℂ) :
    OrientationPreserving (H 1) := by
  change ∀ {z : ℂ} (L : Path z z) (w : ℂ), w ∉ Set.range L →
    ∀ n : ℤ, HasWinding L w n ↔ HasWinding (L.map (H 1).continuous) (H 1 w) n
  intro z L w hw n
  exact uibhbotHasWinding_of_continuous_isotopy H hH hH0 L w hw n

/-- Helper toward Definition 3.8 (consumer): the vertical seam transfer
preserves winding numbers, so it is orientation-preserving. -/
theorem uibhbotVerticalSeamTransfer_orientationPreserving
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    OrientationPreserving (uibhbotVerticalSeamTransfer f g hf hg) := by
  let ψ : I → ℝ → ℝ := fun t x => (1 - (t : ℝ)) * f x + (t : ℝ) * g x
  have hψ : ∀ t, Continuous (ψ t) := by
    intro t
    dsimp [ψ]
    fun_prop
  let H : I → ℂ ≃ₜ ℂ := fun t =>
    uibhbotVerticalSeamTransfer f (ψ t) hf (hψ t)
  have hH0 : H 0 = Homeomorph.refl ℂ := by
    apply Homeomorph.ext
    intro z
    apply Complex.ext <;> simp [H, ψ, uibhbotVerticalSeamTransfer]
  have hH1 : H 1 = uibhbotVerticalSeamTransfer f g hf hg := by
    apply Homeomorph.ext
    intro z
    apply Complex.ext <;> simp [H, ψ, uibhbotVerticalSeamTransfer]
  have hH : Continuous (fun p : I × ℂ => H p.1 p.2) := by
    simp_rw [H, uibhbotVerticalSeamTransfer]
    dsimp [ψ]
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  rw [← hH1]
  change ∀ {z : ℂ} (L : Path z z) (w : ℂ), w ∉ Set.range L →
    ∀ n : ℤ, HasWinding L w n ↔ HasWinding (L.map (H 1).continuous) (H 1 w) n
  intro z L w hw n
  exact uibhbotHasWinding_of_continuous_isotopy H hH hH0 L w hw n

end DirectedDistances.PaperProofs.Section5

end
