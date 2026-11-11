module

public import DirectedDistances.PlanarMap.InfiniteRayStrip

/-! Supporting lemmas for paper labels `lem-geo-exist` (see CORRESPONDENCE.md). -/











public section
namespace DirectedDistances.PlanarMap

open Set
open Filter

/-- The half-open abscissa domain `[x₀, X)`, where `X : WithTop ℝ` may be `⊤`.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
@[expose] def rayDomain (x₀ : ℝ) (X : WithTop ℝ) : Set ℝ :=
  {t | x₀ ≤ t ∧ (t : WithTop ℝ) < X}

/-- `S` is a proper graph ray from `x₀`: for some right end `X > x₀` (possibly `⊤`) and some
height function `h` continuous on `[x₀, X)`, the set `S` is exactly the graph of `h` over
`[x₀, X)`, and `h` eventually exceeds every real bound as the abscissa approaches `X`.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
@[expose] def ProperGraphRay (S : Set ℂ) (x₀ : ℝ) : Prop :=
  ∃ (X : WithTop ℝ) (h : ℝ → ℝ), (x₀ : WithTop ℝ) < X ∧
    ContinuousOn h (rayDomain x₀ X) ∧
    S = {z | z.re ∈ rayDomain x₀ X ∧ z.im = h z.re} ∧
    ∀ M : ℝ, ∃ a ∈ rayDomain x₀ X, ∀ t ∈ rayDomain x₀ X, a ≤ t → M ≤ h t

/-- The graph over `[x₀, ∞)` of a continuous height function tending to `+∞` is a proper graph
ray; in particular the notion is not vacuous.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem properGraphRay_of_isGraphRay {S : Set ℂ} {x₀ : ℝ} {h : ℝ → ℝ}
    (hS : IsGraphRay S x₀ h) (hh : Continuous h) (hlim : Tendsto h atTop atTop) :
    ProperGraphRay S x₀ := by
  refine ⟨⊤, h, WithTop.coe_lt_top x₀, hh.continuousOn, ?_, ?_⟩
  · rw [hS]
    ext z
    simp [rayDomain]
  · intro M
    obtain ⟨b, hb⟩ := tendsto_atTop_atTop.mp hlim M
    refine ⟨max b x₀, by simp [rayDomain], ?_⟩
    intro t _ hat
    exact hb t (le_trans (le_max_left b x₀) hat)

end DirectedDistances.PlanarMap
