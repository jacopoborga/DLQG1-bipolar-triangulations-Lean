/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion3
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers54And57

/-! # Components between ordered graph rays

and the second ray is the lower graph. The results below classify the
components inside the strict strip, allowing the graphs to coincide on
arbitrary closed sets. Winding-side identification and the source-ray
application are separate obligations; no intrinsic-object qualifier is removed. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 Set
open scoped Topology

/-- Helper toward Proposition 3.9: the strict strip between two continuous
graphs is open, with the common starting vertical line excluded. -/
theorem intrinsicBetween4_isOpen_strictStrip {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hcP : Continuous fP) (hcR : Continuous fR) :
    IsOpen {z : ℂ | x₀ < z.re ∧ fR z.re < z.im ∧ z.im < fP z.re} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt (hcR.comp Complex.continuous_re) Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im (hcP.comp Complex.continuous_re)))

/-- Helper toward Proposition 3.9: the boundary of the strict strip lies
on the two graph rays, when they start at the same point. This includes all
later coincidences and does not require strict ordering of the graphs. -/
theorem intrinsicBetween4_closure_strictStrip_inter_compl_subset
    {P R : Set ℂ} {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay P x₀ fP) (hR : IsGraphRay R x₀ fR)
    (hcP : Continuous fP) (hcR : Continuous fR)
    (hstart : fP x₀ = fR x₀) :
    closure {z : ℂ | x₀ < z.re ∧ fR z.re < z.im ∧ z.im < fP z.re} ∩
        (P ∪ R)ᶜ ⊆
      {z : ℂ | x₀ < z.re ∧ fR z.re < z.im ∧ z.im < fP z.re} := by
  have hcl : closure {z : ℂ | x₀ < z.re ∧ fR z.re < z.im ∧ z.im < fP z.re} ⊆
      closedRayStrip x₀ fR fP :=
    closure_minimal (fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩)
      (isClosed_closedRayStrip hcR hcP)
  rintro z ⟨hz, hn⟩
  obtain ⟨hx, hlo, hhi⟩ := hcl hz
  have hneP : z.im ≠ fP z.re := fun he => hn (Or.inl (hP ▸ ⟨hx, he⟩))
  have hneR : z.im ≠ fR z.re := fun he => hn (Or.inr (hR ▸ ⟨hx, he⟩))
  have hxne : x₀ ≠ z.re := by
    intro he
    have hh : fP z.re = fR z.re := he ▸ hstart
    exact hneP (le_antisymm hhi (hh.symm ▸ hlo))
  exact ⟨lt_of_le_of_ne hx hxne, lt_of_le_of_ne hlo hneR.symm,
    lt_of_le_of_ne hhi hneP⟩

/-- Helper toward Proposition 3.9: a complementary component meeting the
strict strip stays inside it. In particular it cannot escape around the
common starting point or through a later coincidence of the graphs. -/
theorem intrinsicBetween4_component_subset_strictStrip
    {P R : Set ℂ} {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay P x₀ fP) (hR : IsGraphRay R x₀ fR)
    (hcP : Continuous fP) (hcR : Continuous fR)
    (hstart : fP x₀ = fR x₀) {z : ℂ}
    (hz : x₀ < z.re ∧ fR z.re < z.im ∧ z.im < fP z.re) :
    connectedComponentIn (P ∪ R)ᶜ z ⊆
      {q : ℂ | x₀ < q.re ∧ fR q.re < q.im ∧ q.im < fP q.re} := by
  have hn : z ∈ (P ∪ R)ᶜ := by
    rw [hP, hR]
    rintro (⟨_, he⟩ | ⟨_, he⟩)
    · exact (ne_of_lt hz.2.2) he
    · exact (ne_of_gt hz.2.1) he
  apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
    (intrinsicBetween4_isOpen_strictStrip hcP hcR) ⟨z, mem_connectedComponentIn hn, hz⟩
  intro q hq
  exact intrinsicBetween4_closure_strictStrip_inter_compl_subset hP hR hcP hcR hstart
    ⟨hq.1, connectedComponentIn_subset _ _ hq.2⟩

/-- Helper toward Proposition 3.9: interpolation over any preconnected
set of abscissas gives a preconnected open band between two continuous
heights. The strict height gap is checked only on those abscissas. -/
theorem intrinsicBetween4_isPreconnected_band
    {J : Set ℝ} {fP fR : ℝ → ℝ} (hJ : IsPreconnected J)
    (hcP : Continuous fP) (hcR : Continuous fR)
    (hgap : ∀ x ∈ J, fR x < fP x) :
    IsPreconnected {z : ℂ | z.re ∈ J ∧ fR z.re < z.im ∧ z.im < fP z.re} := by
  let T : ℝ × ℝ → ℂ := fun p => ⟨p.1, fR p.1 + p.2 * (fP p.1 - fR p.1)⟩
  have hcT : Continuous T :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_fst.prodMk ((hcR.comp continuous_fst).add
        (continuous_snd.mul ((hcP.comp continuous_fst).sub (hcR.comp continuous_fst)))))
  have heq : T '' (J ×ˢ Ioo (0 : ℝ) 1) =
      {z : ℂ | z.re ∈ J ∧ fR z.re < z.im ∧ z.im < fP z.re} := by
    ext z
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht0, ht1⟩, rfl⟩
      change x ∈ J ∧ fR x < fR x + t * (fP x - fR x) ∧
        fR x + t * (fP x - fR x) < fP x
      have hg := hgap x hx
      refine ⟨hx, ?_, ?_⟩ <;> nlinarith only [hg, ht0, ht1]
    · rintro ⟨hx, hlo, hhi⟩
      have hg : 0 < fP z.re - fR z.re := sub_pos.mpr (hgap z.re hx)
      refine ⟨(z.re, (z.im - fR z.re) / (fP z.re - fR z.re)),
        ⟨hx, div_pos (sub_pos.mpr hlo) hg, (div_lt_one hg).mpr ?_⟩, ?_⟩
      · linarith only [hhi]
      · apply Complex.ext
        · rfl
        · change fR z.re + (z.im - fR z.re) / (fP z.re - fR z.re) *
            (fP z.re - fR z.re) = z.im
          rw [div_mul_cancel₀ _ (ne_of_gt hg)]
          ring
  rw [← heq]
  exact (hJ.prod isPreconnected_Ioo).image T hcT.continuousOn

/-- Helper toward Proposition 3.9: components inside the strict strip
are exactly the bands over components of the open set of positive height
gaps. Arbitrary closed coincidence sets are permitted. The first graph
is the upper ray, in the argument order of `closedBetween`. -/
theorem intrinsicBetween4_component_eq_band
    {P R : Set ℂ} {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay P x₀ fP) (hR : IsGraphRay R x₀ fR)
    (hcP : Continuous fP) (hcR : Continuous fR)
    (hstart : fP x₀ = fR x₀) {z : ℂ}
    (hz : x₀ < z.re ∧ fR z.re < z.im ∧ z.im < fP z.re) :
    connectedComponentIn (P ∪ R)ᶜ z =
      {q : ℂ | q.re ∈ connectedComponentIn
        {x : ℝ | x₀ < x ∧ fR x < fP x} z.re ∧
        fR q.re < q.im ∧ q.im < fP q.re} := by
  let J : Set ℝ := {x | x₀ < x ∧ fR x < fP x}
  let C := connectedComponentIn (P ∪ R)ᶜ z
  have hzJ : z.re ∈ J := ⟨hz.1, hz.2.1.trans hz.2.2⟩
  have hC := intrinsicBetween4_component_subset_strictStrip hP hR hcP hcR hstart hz
  have hn : z ∈ (P ∪ R)ᶜ := by
    rw [hP, hR]
    rintro (⟨_, he⟩ | ⟨_, he⟩)
    · exact (ne_of_lt hz.2.2) he
    · exact (ne_of_gt hz.2.1) he
  have himage : Complex.re '' C ⊆ connectedComponentIn J z.re := by
    apply (isPreconnected_connectedComponentIn.image Complex.re
      Complex.continuous_re.continuousOn).subset_connectedComponentIn
      ⟨z, mem_connectedComponentIn hn, rfl⟩
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨(hC hq).1, (hC hq).2.1.trans (hC hq).2.2⟩
  apply subset_antisymm
  · intro q hq
    exact ⟨himage ⟨q, hq, rfl⟩, (hC hq).2⟩
  · apply (intrinsicBetween4_isPreconnected_band isPreconnected_connectedComponentIn
      hcP hcR (fun x hx => (connectedComponentIn_subset J z.re hx).2)).subset_connectedComponentIn
      ⟨mem_connectedComponentIn hzJ, hz.2⟩
    rintro q ⟨hq, hlo, hhi⟩
    rw [hP, hR]
    rintro (⟨_, he⟩ | ⟨_, he⟩)
    · exact (ne_of_lt hhi) he
    · exact (ne_of_gt hlo) he

/-- Helper toward Proposition 3.9: two points of the strict strip belong
to the same complementary component exactly when every abscissa between
them has a positive height gap. This describes the components without
choosing endpoints of the intervals complementary to the coincidence set. -/
theorem intrinsicBetween4_mem_component_iff
    {P R : Set ℂ} {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay P x₀ fP) (hR : IsGraphRay R x₀ fR)
    (hcP : Continuous fP) (hcR : Continuous fR)
    (hstart : fP x₀ = fR x₀) {z q : ℂ}
    (hz : x₀ < z.re ∧ fR z.re < z.im ∧ z.im < fP z.re)
    (hq : x₀ < q.re ∧ fR q.re < q.im ∧ q.im < fP q.re) :
    q ∈ connectedComponentIn (P ∪ R)ᶜ z ↔
      ∀ x ∈ uIcc z.re q.re, x₀ < x ∧ fR x < fP x := by
  rw [intrinsicBetween4_component_eq_band hP hR hcP hcR hstart hz]
  let J : Set ℝ := {x | x₀ < x ∧ fR x < fP x}
  have hzJ : z.re ∈ J := ⟨hz.1, hz.2.1.trans hz.2.2⟩
  change (q.re ∈ connectedComponentIn J z.re ∧ _) ↔ _
  constructor
  · rintro ⟨hm, _⟩
    exact (isPreconnected_connectedComponentIn.ordConnected.uIcc_subset
      (mem_connectedComponentIn hzJ) hm).trans
      (connectedComponentIn_subset J z.re)
  · intro hall
    refine ⟨?_, hq.2⟩
    exact ((isPreconnected_uIcc : IsPreconnected (uIcc z.re q.re)).subset_connectedComponentIn
      left_mem_uIcc (fun x hx => hall x hx))
      right_mem_uIcc

/-- Helper toward Proposition 3.9: adding the complete graph traces to
the strict strip gives exactly the source vertical-fiber region, with its
upper first and lower second argument order and all coincidence points. -/
theorem intrinsicBetween4_strictStrip_union_traces
    {P R : Set ℂ} {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay P x₀ fP) (hR : IsGraphRay R x₀ fR)
    (hstart : fP x₀ = fR x₀)
    (horder : ∀ x : ℝ, x₀ ≤ x → fR x ≤ fP x) :
    {z : ℂ | x₀ < z.re ∧ fR z.re < z.im ∧ z.im < fP z.re} ∪ (P ∪ R) =
      closedBetween P R := by
  ext z
  rw [intrinsicBetween3_mem_closedBetween_graphRays hP hR]
  constructor
  · rintro (hz | hz)
    · exact ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
    · rw [hP, hR] at hz
      rcases hz with ⟨hx, he⟩ | ⟨hx, he⟩
      · exact ⟨hx, he ▸ horder z.re hx, he.le⟩
      · exact ⟨hx, he.ge, he ▸ horder z.re hx⟩
  · rintro ⟨hx, hlo, hhi⟩
    by_cases hp : z.im = fP z.re
    · exact Or.inr (Or.inl (hP ▸ ⟨hx, hp⟩))
    by_cases hr : z.im = fR z.re
    · exact Or.inr (Or.inr (hR ▸ ⟨hx, hr⟩))
    have hxne : x₀ ≠ z.re := by
      intro he
      have hh : fP z.re = fR z.re := he ▸ hstart
      exact hp (le_antisymm hhi (hh.symm ▸ hlo))
    exact Or.inl ⟨lt_of_le_of_ne hx hxne, lt_of_le_of_ne hlo (Ne.symm hr),
      lt_of_le_of_ne hhi hp⟩

/-- Helper toward Proposition 3.9: the closure of the strict strip and
both boundary traces is the correctly ordered `closedBetween` region.
No winding-side incidence assertion is used as a hypothesis. -/
theorem intrinsicBetween4_closure_strictStrip_union_traces
    {P R : Set ℂ} {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay P x₀ fP) (hR : IsGraphRay R x₀ fR)
    (hcP : Continuous fP) (hcR : Continuous fR)
    (hstart : fP x₀ = fR x₀)
    (horder : ∀ x : ℝ, x₀ ≤ x → fR x ≤ fP x) :
    closure ({z : ℂ | x₀ < z.re ∧ fR z.re < z.im ∧ z.im < fP z.re} ∪ (P ∪ R)) =
      closedBetween P R := by
  rw [intrinsicBetween4_strictStrip_union_traces hP hR hstart horder]
  have heq : closedBetween P R = closedRayStrip x₀ fR fP := by
    ext z
    exact intrinsicBetween3_mem_closedBetween_graphRays hP hR z
  exact (heq ▸ isClosed_closedRayStrip hcR hcP).closure_eq

private theorem intrinsicBetween4_graph_upper_connected (f : ℝ → ℝ)
    (hf : Continuous f) : IsConnected {z : ℂ | f z.re < z.im} := by
  let T : ℝ × ℝ → ℂ := fun p => ⟨p.1, p.2 + f p.1⟩
  have hT : Continuous T :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_fst.prodMk (continuous_snd.add (hf.comp continuous_fst)))
  have heq : T '' ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) =
      {z : ℂ | f z.re < z.im} := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, ⟨_, hy⟩, rfl⟩
      exact lt_add_of_pos_left _ hy
    · intro hz
      exact ⟨(z.re, z.im - f z.re), ⟨mem_univ _, sub_pos.mpr hz⟩,
        Complex.ext rfl (sub_add_cancel _ _)⟩
  rw [← heq]
  exact (isConnected_univ.prod isConnected_Ioi).image T hT.continuousOn

private theorem intrinsicBetween4_graph_lower_connected (f : ℝ → ℝ)
    (hf : Continuous f) : IsConnected {z : ℂ | z.im < f z.re} := by
  let T : ℝ × ℝ → ℂ := fun p => ⟨p.1, p.2 + f p.1⟩
  have hT : Continuous T :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_fst.prodMk (continuous_snd.add (hf.comp continuous_fst)))
  have heq : T '' ((univ : Set ℝ) ×ˢ Iio (0 : ℝ)) =
      {z : ℂ | z.im < f z.re} := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, ⟨_, hy⟩, rfl⟩
      exact add_lt_of_neg_left _ hy
    · intro hz
      exact ⟨(z.re, z.im - f z.re), ⟨mem_univ _, sub_neg.mpr hz⟩,
        Complex.ext rfl (sub_add_cancel _ _)⟩
  rw [← heq]
  exact (isConnected_univ.prod isConnected_Iio).image T hT.continuousOn

/-- Helper toward Proposition 3.9: the exterior of the vertical-fiber
region is connected. Its upper and lower parts join to the left of the
common starting vertical line, even when the graphs coincide later. -/
theorem intrinsicBetween4_exterior_isConnected
    {P R : Set ℂ} {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay P x₀ fP) (hR : IsGraphRay R x₀ fR)
    (hcP : Continuous fP) (hcR : Continuous fR) :
    IsConnected (closedBetween P R)ᶜ := by
  let L : Set ℂ := {z | z.re < x₀}
  let U : Set ℂ := {z | fP z.re < z.im}
  let B : Set ℂ := {z | z.im < fR z.re}
  have hL : IsConnected L := (convex_halfSpace_re_lt x₀).isConnected
    ⟨⟨x₀ - 1, 0⟩, by change x₀ - 1 < x₀; linarith⟩
  have hLU : (L ∩ U).Nonempty :=
    ⟨⟨x₀ - 1, fP (x₀ - 1) + 1⟩, by
      change x₀ - 1 < x₀ ∧ fP (x₀ - 1) < fP (x₀ - 1) + 1
      constructor <;> linarith⟩
  have hLUB : ((L ∪ U) ∩ B).Nonempty :=
    ⟨⟨x₀ - 1, fR (x₀ - 1) - 1⟩, Or.inl (by change x₀ - 1 < x₀; linarith),
      by change fR (x₀ - 1) - 1 < fR (x₀ - 1); linarith⟩
  have heq : (closedBetween P R)ᶜ = (L ∪ U) ∪ B := by
    ext z
    rw [mem_compl_iff, intrinsicBetween3_mem_closedBetween_graphRays hP hR]
    change ¬ (x₀ ≤ z.re ∧ fR z.re ≤ z.im ∧ z.im ≤ fP z.re) ↔
      (z.re < x₀ ∨ fP z.re < z.im) ∨ z.im < fR z.re
    constructor
    · intro hn
      by_cases hx : x₀ ≤ z.re
      · by_cases hlo : fR z.re ≤ z.im
        · exact Or.inl (Or.inr (not_le.mp (fun hhi => hn ⟨hx, hlo, hhi⟩)))
        · exact Or.inr (not_le.mp hlo)
      · exact Or.inl (Or.inl (not_le.mp hx))
    · rintro ((hx | hhi) | hlo) ⟨hx', hlo', hhi'⟩
      · exact hx.not_ge hx'
      · exact hhi.not_ge hhi'
      · exact hlo.not_ge hlo'
  rw [heq]
  exact ((hL.union hLU (intrinsicBetween4_graph_upper_connected fP hcP)).union
    hLUB (intrinsicBetween4_graph_lower_connected fR hcR))

/-- Helper toward Proposition 3.9: the exterior is exactly one
complementary component of two ordered graph rays with a common start.
This is the component which the winding-side exclusions must discard. -/
theorem intrinsicBetween4_component_eq_exterior
    {P R : Set ℂ} {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay P x₀ fP) (hR : IsGraphRay R x₀ fR)
    (hcP : Continuous fP) (hcR : Continuous fR)
    (hstart : fP x₀ = fR x₀)
    (horder : ∀ x : ℝ, x₀ ≤ x → fR x ≤ fP x)
    {z : ℂ} (hz : z ∉ closedBetween P R) :
    connectedComponentIn (P ∪ R)ᶜ z = (closedBetween P R)ᶜ := by
  let V : Set ℂ := {q | x₀ < q.re ∧ fR q.re < q.im ∧ q.im < fP q.re}
  have heq := intrinsicBetween4_strictStrip_union_traces hP hR hstart horder
  have hclosed : IsClosed (closedBetween P R) := by
    have he : closedBetween P R = closedRayStrip x₀ fR fP := by
      ext q
      exact intrinsicBetween3_mem_closedBetween_graphRays hP hR q
    exact he ▸ isClosed_closedRayStrip hcR hcP
  have hsub : (closedBetween P R)ᶜ ⊆ (P ∪ R)ᶜ := by
    intro q hq htrace
    exact hq (heq ▸ Or.inr htrace)
  apply subset_antisymm
  · apply isPreconnected_connectedComponentIn.subset_left_of_subset_union
      hclosed.isOpen_compl (intrinsicBetween4_isOpen_strictStrip hcP hcR)
    · apply disjoint_left.mpr
      intro q hq hv
      exact hq (heq ▸ Or.inl hv)
    · intro q hq
      by_cases hbetween : q ∈ closedBetween P R
      · have hh : q ∈ V ∪ (P ∪ R) := heq.symm ▸ hbetween
        rcases hh with hv | ht
        · exact Or.inr hv
        · exact False.elim (connectedComponentIn_subset _ _ hq ht)
      · exact Or.inl hbetween
    · exact ⟨z, mem_connectedComponentIn (hsub hz), hz⟩
  · exact (intrinsicBetween4_exterior_isConnected hP hR hcP hcR).isPreconnected.subset_connectedComponentIn
      hz hsub

/-- Helper toward Proposition 3.9: every component of the complement
of two ordered graph rays is either their single exterior component or a
band over an interval component of their strict height-gap set. This is a
topological classification, before the four winding-side incidence tests. -/
theorem intrinsicBetween4_component_cases
    {P R : Set ℂ} {x₀ : ℝ} {fP fR : ℝ → ℝ}
    (hP : IsGraphRay P x₀ fP) (hR : IsGraphRay R x₀ fR)
    (hcP : Continuous fP) (hcR : Continuous fR)
    (hstart : fP x₀ = fR x₀)
    (horder : ∀ x : ℝ, x₀ ≤ x → fR x ≤ fP x)
    {z : ℂ} (hz : z ∉ P ∪ R) :
    (z ∉ closedBetween P R ∧
      connectedComponentIn (P ∪ R)ᶜ z = (closedBetween P R)ᶜ) ∨
    (x₀ < z.re ∧ fR z.re < z.im ∧ z.im < fP z.re) ∧
      connectedComponentIn (P ∪ R)ᶜ z =
        {q : ℂ | q.re ∈ connectedComponentIn
          {x : ℝ | x₀ < x ∧ fR x < fP x} z.re ∧
          fR q.re < q.im ∧ q.im < fP q.re} := by
  by_cases hb : z ∈ closedBetween P R
  · have hs := intrinsicBetween4_strictStrip_union_traces hP hR hstart horder
    have hh : z ∈ {q : ℂ | x₀ < q.re ∧ fR q.re < q.im ∧ q.im < fP q.re} ∪
        (P ∪ R) := hs.symm ▸ hb
    rcases hh with hh | hh
    · exact Or.inr ⟨hh, intrinsicBetween4_component_eq_band hP hR hcP hcR hstart hh⟩
    · exact False.elim (hz hh)
  · exact Or.inl ⟨hb,
      intrinsicBetween4_component_eq_exterior hP hR hcP hcR hstart horder hb⟩

/- EXACT REMAINING STATEMENTS (comments, not declarations or assumptions).

The topological component and boundary classifications above are proved for
continuous graphs over [x₀, ∞), with upper first and lower second. The missing
step is their identification with the four winding-side tests for actual
source edges. In addition, the source proper-ray API permits finite limiting
abscissas; no infinite-abscissa assertion is made here. The following exact
Their notation also opens DirectedDistances.PaperProofs.Section5,
DirectedDistances.PaperProofs.Section7, DirectedDistances.Paper.Section4,
DirectedDistances.RandomWalk, MeasureTheory, and Filter, with Classical scope.

(1) IntrinsicBetweenRegion2.lean:280, full binders:

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
  (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h (k - 1))))
let D := m0CutData W H h hLL
let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
∀ (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root)
  (longest : Bool) (k : ℤ)
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (T : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
  (_ : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
  (_ : T.edge = R.edge),
nativeBetween A
  (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n)))
  (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (T.edge n))) =
  I.h '' closedBetween
    (pathTrace G (fun n => wholePlaneDartι W 0 (P.codePath.edge n, false)))
    (pathTrace G (fun n => wholePlaneDartι W 0 (T.edge n, false))).

(2) IntrinsicBetweenRegion2.lean:316, full binders and shared clauses:

∀ᵐ U ∂wholePlaneIIDCodeMeasure,
  let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U
  let W := uibotRecoveredCode z
  ∃ (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
  let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (k - 1))))
  let D := m0CutData W H h hLL
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∃ s : ∀ x : XDP, M0CutGeodesicSliceWitness W x,
  z = Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
  ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
    Nonempty (D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root) ∧
    ∀ I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root,
    ∀ x : XDP,
    (if x = XDP.ldp then
      IsIntrinsicBusemannLDP A (intrinsicBusemannImageCut W H G hp D A I)
        (fun k => I.vertexEquiv (D.x k)) (identifiedLDPBusemann W)
    else IsIntrinsicBusemannSDP A (intrinsicBusemannImageCut W H G hp D A I)
        (fun k => I.vertexEquiv (D.x k)) (identifiedSDPBusemann W)) ∧
    let P := fun j => intrinsicGeodesicOfCode W H h hLL G hp A I ((s x).P j)
    (∀ k k' : ℤ, ∃ a b : ℕ, IntrinsicEdgeTailsCoalesce (P k).val (P k').val a b) ∧
    (∀ k : ℤ,
      let X := if x = XDP.ldp then identifiedLDPBusemann W else identifiedSDPBusemann W
      IntrinsicLeastEdgeCoalescence (P (k - 1)).val (P k).val
        ((s x).thetaMinus k) ((s x).theta k) ∧
      uibotGeomCoalescenceOffsets z x k = ((s x).thetaMinus k, (s x).theta k) ∧
      uibotCodeCoalescenceOffsets W x k = ((s x).thetaMinus k, (s x).theta k) ∧
      (uibotGeomSideSliceObservables z x k).2 =
        some (geometricSideClass (m0CutGeodesicSlice (hp := (s x).hp) (s x).P k
          ((s x).thetaMinus k) ((s x).theta k) ((s x).least k))) ∧
      X k - X (k - 1) = (((s x).theta k : ℕ) : ℤ) -
        (((s x).thetaMinus k : ℕ) : ℤ)) ∧
    ∀ k : ℤ,
      let S := intrinsicBusemannImageCut W H G hp D A I
      let v := I.vertexEquiv (D.x k)
      let longest := if x = XDP.ldp then true else false
      ∃ T : IntrinsicInfiniteDirectedPath A S v,
        RightmostInCut A S v T ∧
        ∀ Q : IntrinsicInfiniteXDPGeodesic A S v longest,
          IntrinsicLeftmostInRegion A S v longest Q T ↔ Q = P k.

(3) IntrinsicConsumers54And57.lean:242, full binders:

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
  (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h (k - 1))))
let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
∀ (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root)
  (longest : Bool) (k : ℤ)
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (T : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
  (_ : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
  (_ : T.edge = R.edge),
nativeBetween A
  (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n)))
  (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (T.edge n))) =
  I.h '' closedBetween
    (pathTrace G (fun n => wholePlaneDartι W 0 (P.codePath.edge n, false)))
    (pathTrace G (fun n => wholePlaneDartι W 0 (T.edge n, false))).

(4) IntrinsicConsumers54And57.lean:274, full binders:

∀ᵐ U ∂wholePlaneIIDCodeMeasure,
  let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U
  let W := uibotRecoveredCode z
  ∃ (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
  let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (k - 1))))
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∃ s : ∀ x : XDP, M0CutGeodesicSliceWitness W x,
  z = Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
  ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
    Nonempty (D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root) ∧
    ∀ I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root,
    let C := intrinsicFutureCut2Pushforward I (uibotCut2Source W H h hpast hp)
    let S := intrinsicConsumersBusemannCut C
    ∀ (x : XDP) (k : ℤ),
    let longest := if x = XDP.ldp then true else false
    let P := intrinsicConsumersGeodesicOfCode W H h hpast hp A I ((s x).P k)
    IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest P ∧
    ∀ Q : IntrinsicInfiniteXDPGeodesic A S (C.x k) longest,
      IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest Q → Q = P.

The last strengthening must retain every clause of
intrinsicConsumers54And57_sample_ae with the same H, h, hpast, hp, s.
No common-event or native-region conclusion is counted as proved here. -/

end DirectedDistances.PaperProofs.Section3
end
