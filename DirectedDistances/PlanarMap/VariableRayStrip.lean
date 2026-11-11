module

public import DirectedDistances.PlanarMap.ProperGraphRay

/-! # Closed regions between proper graph rays

Helpers toward Lemma 4.6 (lem-geo-exist); not a paper result. Source context: -/

public section
namespace DirectedDistances.PlanarMap

open Set Filter
open scoped Topology

/-- Closed region on or above the lower ray `T` and on or below the upper ray `S`
(where `S` is defined).
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
@[expose] def closedBetween (S T : Set ℂ) : Set ℂ :=
  {z | (∃ r ∈ T, r.re = z.re ∧ r.im ≤ z.im) ∧ (∀ p ∈ S, p.re = z.re → z.im ≤ p.im)}

/-- Membership in the region between two graph rays, in terms of the height functions.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem mem_closedBetween_iff {S T : Set ℂ} {x₀ : ℝ} {XS XT : WithTop ℝ} {hS hT : ℝ → ℝ}
    (eS : S = {z | z.re ∈ rayDomain x₀ XS ∧ z.im = hS z.re})
    (eT : T = {z | z.re ∈ rayDomain x₀ XT ∧ z.im = hT z.re}) (z : ℂ) :
    z ∈ closedBetween S T ↔
      z.re ∈ rayDomain x₀ XT ∧ hT z.re ≤ z.im ∧
        (z.re ∈ rayDomain x₀ XS → z.im ≤ hS z.re) := by
  subst eS eT
  constructor
  · rintro ⟨⟨r, ⟨hr, hri⟩, hre, him⟩, hup⟩
    rw [hre] at hr
    refine ⟨hr, ?_, fun h => ?_⟩
    · rw [hre] at hri
      rw [← hri]; exact him
    · exact hup ⟨z.re, hS z.re⟩ ⟨h, rfl⟩ rfl
  · rintro ⟨hr, hl, hu⟩
    refine ⟨⟨⟨z.re, hT z.re⟩, ⟨hr, rfl⟩, rfl, hl⟩, ?_⟩
    rintro p ⟨hp, hpi⟩ hpre
    rw [hpi, hpre]
    exact hu (hpre ▸ hp)

private theorem eventually_mem_rayDomain {x₀ : ℝ} {X : WithTop ℝ} {z : ℝ} {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 z)) (hz : z ∈ rayDomain x₀ X) (hx : ∀ n, x₀ ≤ u n) :
    ∀ᶠ n in atTop, u n ∈ rayDomain x₀ X := by
  obtain ⟨_, hlt⟩ := hz
  induction X using WithTop.recTopCoe with
  | top => exact Eventually.of_forall fun n => ⟨hx n, WithTop.coe_lt_top _⟩
  | coe b =>
    have hz' : z < b := WithTop.coe_lt_coe.mp hlt
    exact (hu.eventually (gt_mem_nhds hz')).mono fun n hn => ⟨hx n, WithTop.coe_lt_coe.mpr hn⟩

/-- The region between two proper graph rays is closed.
Helper toward Lemma 4.6 (lem-geo-exist); not a paper result. -/
theorem isClosed_closedBetween {S T : Set ℂ} {x₀ : ℝ} (hS : ProperGraphRay S x₀)
    (hT : ProperGraphRay T x₀) : IsClosed (closedBetween S T) := by
  obtain ⟨XS, fS, -, fSc, eS, -⟩ := hS
  obtain ⟨XT, fT, -, fTc, eT, fTesc⟩ := hT
  apply IsSeqClosed.isClosed
  intro u z hu hz
  have hmem := fun n => (mem_closedBetween_iff eS eT (u n)).mp (hu n)
  have hre : Tendsto (fun n => (u n).re) atTop (𝓝 z.re) :=
    (Complex.continuous_re.tendsto z).comp hz
  have him : Tendsto (fun n => (u n).im) atTop (𝓝 z.im) :=
    (Complex.continuous_im.tendsto z).comp hz
  obtain ⟨M, hM⟩ := him.bddAbove_range
  have hMn : ∀ n, (u n).im ≤ M := fun n => hM ⟨n, rfl⟩
  obtain ⟨a, ha, hbig⟩ := fTesc (M + 1)
  have hlt : ∀ n, (u n).re < a := by
    intro n
    by_contra hcon
    have h1 := hbig _ (hmem n).1 (not_lt.mp hcon)
    have h2 := (hmem n).2.1
    have h3 := hMn n
    linarith
  have hza : z.re ≤ a := le_of_tendsto' hre fun n => (hlt n).le
  have hx₀ : ∀ n, x₀ ≤ (u n).re := fun n => (hmem n).1.1
  have hzx : x₀ ≤ z.re := ge_of_tendsto' hre hx₀
  have hzT : z.re ∈ rayDomain x₀ XT :=
    ⟨hzx, lt_of_le_of_lt (WithTop.coe_le_coe.mpr hza) ha.2⟩
  rw [mem_closedBetween_iff eS eT]
  refine ⟨hzT, ?_, fun hzS => ?_⟩
  · have hlim : Tendsto (fun n => fT (u n).re) atTop (𝓝 (fT z.re)) :=
      (fTc z.re hzT).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hre, Eventually.of_forall fun n => (hmem n).1⟩)
    exact le_of_tendsto_of_tendsto' hlim him fun n => (hmem n).2.1
  · have hev := eventually_mem_rayDomain hre hzS hx₀
    have hlim : Tendsto (fun n => fS (u n).re) atTop (𝓝 (fS z.re)) :=
      (fSc z.re hzS).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hre, hev⟩)
    exact le_of_tendsto_of_tendsto him hlim (hev.mono fun n hn => (hmem n).2.2 hn)

end DirectedDistances.PlanarMap
