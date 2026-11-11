module

public import DirectedDistances.PlanarMap.D39DrawingRepresentation3Transport







public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

/-- Helper toward Proposition 5.16. The closed radial segment in direction
`u`, including its initial point. -/
def d39_radial_segment (u : ℂ) : Set ℂ :=
  {z | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ z = (r : ℂ) * u}

/-- Helper toward Proposition 5.16. If one nonzero radial segment is contained
in another, their directions have the same complex argument. -/
theorem d39_arg_eq_of_radial_segment_subset {u v : ℂ}
    (hu : u ≠ 0) (hsub : d39_radial_segment u ⊆ d39_radial_segment v) :
    Complex.arg u = Complex.arg v := by
  have hu_mem : u ∈ d39_radial_segment u := by
    refine ⟨1, by norm_num, by norm_num, ?_⟩
    simp
  obtain ⟨r, hr0, hr1, hur⟩ := hsub hu_mem
  have hr : 0 < r := by
    by_contra h
    have hr' : r = 0 := by linarith
    subst r
    simp at hur
    exact hu hur
  rw [hur, Complex.arg_real_mul v hr]

/-- Helper toward Proposition 5.16. Two successor witnesses using the same
straightening map and the same arcs have the same successor, even if their
radial direction functions were named separately. -/
theorem d39_topological_ccw_successor_unique_of_shared_straightener
    {D : Type*} {star : Set D} {arc : D → I → ℂ} {d e f : D}
    (H : ℂ ≃ₜ ℂ) (dir₁ dir₂ : D → ℂ)
    (hdir₁ : ∀ x ∈ star, dir₁ x ≠ 0)
    (hdir₂ : ∀ x ∈ star, dir₂ x ≠ 0)
    (harg₁ : ∀ x ∈ star, ∀ y ∈ star,
      Complex.arg (dir₁ x) = Complex.arg (dir₁ y) → x = y)
    (hsucc₁ : CcwSuccessor star dir₁ d e)
    (hsucc₂ : CcwSuccessor star dir₂ d f)
    (hstraight₁ : ∀ x ∈ star, ∃ t : I, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
      H '' (arc x '' Set.Icc (0 : I) t) = d39_radial_segment (dir₁ x))
    (hstraight₂ : ∀ x ∈ star, ∃ t : I, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
      H '' (arc x '' Set.Icc (0 : I) t) = d39_radial_segment (dir₂ x)) :
    e = f := by
  have harg : ∀ x ∈ star, Complex.arg (dir₁ x) = Complex.arg (dir₂ x) := by
    intro x hx
    obtain ⟨t₁, ht₁0, ht₁1, hs₁⟩ := hstraight₁ x hx
    obtain ⟨t₂, ht₂0, ht₂1, hs₂⟩ := hstraight₂ x hx
    rcases le_total t₁ t₂ with h12 | h21
    · have hprefix : arc x '' Set.Icc (0 : I) t₁ ⊆
          arc x '' Set.Icc (0 : I) t₂ :=
        Set.image_mono (Set.Icc_subset_Icc le_rfl h12)
      have hray : d39_radial_segment (dir₁ x) ⊆ d39_radial_segment (dir₂ x) := by
        rw [← hs₁, ← hs₂]
        exact Set.image_mono hprefix
      exact d39_arg_eq_of_radial_segment_subset (hdir₁ x hx) hray
    · have hprefix : arc x '' Set.Icc (0 : I) t₂ ⊆
          arc x '' Set.Icc (0 : I) t₁ :=
        Set.image_mono (Set.Icc_subset_Icc le_rfl h21)
      have hray : d39_radial_segment (dir₂ x) ⊆ d39_radial_segment (dir₁ x) := by
        rw [← hs₂, ← hs₁]
        exact Set.image_mono hprefix
      exact (d39_arg_eq_of_radial_segment_subset (hdir₂ x hx) hray).symm
  have hsucc₂' : CcwSuccessor star dir₁ d f := by
    rcases hsucc₂ with ⟨hfinite, hd, hf, hcase⟩
    refine ⟨hfinite, hd, hf, ?_⟩
    rcases hcase with ⟨hfd, hsingleton⟩ | ⟨hfd, hmin⟩
    · exact Or.inl ⟨hfd, hsingleton⟩
    · refine Or.inr ⟨hfd, ?_⟩
      intro g hg hgne
      have hdarg := harg d hd
      have hfarg := harg f hf
      have hgarg := harg g hg
      simpa [ccwTurn, hdarg, hfarg, hgarg] using hmin g hg hgne
  exact d39CcwSuccessor_unique harg₁ hsucc₁ hsucc₂'

















































end DirectedDistances.PlanarMap

end
