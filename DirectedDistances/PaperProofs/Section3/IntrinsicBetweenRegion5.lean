/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion4
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart5
import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect6
import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact9
import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact20







public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 Set Filter
open DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk
open scoped Topology

/-- Helper toward Proposition 3.9: the epigraph over a proper ray's
half-open domain is closed, even at a finite limiting abscissa, because
the heights escape to positive infinity there. -/
theorem intrinsicBetween5_isClosed_epigraph
    {x₀ : ℝ} {X : WithTop ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (rayDomain x₀ X))
    (hesc : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ X,
      ∀ t ∈ rayDomain x₀ X, a ≤ t → M ≤ f t) :
    IsClosed {z : ℂ | z.re ∈ rayDomain x₀ X ∧ f z.re ≤ z.im} := by
  apply IsSeqClosed.isClosed
  intro u z hu hz
  have hre := (Complex.continuous_re.tendsto z).comp hz
  have him := (Complex.continuous_im.tendsto z).comp hz
  obtain ⟨M, hM⟩ := him.bddAbove_range
  obtain ⟨a, ha, hbig⟩ := hesc (M + 1)
  have hlt : ∀ n, (u n).re < a := by
    intro n
    by_contra hn
    have h₁ := hbig _ (hu n).1 (le_of_not_gt hn)
    have h₂ := (hu n).2
    have h₃ := hM (mem_range_self n)
    change (u n).im ≤ M at h₃
    linarith only [h₁, h₂, h₃]
  have hza : z.re ≤ a := le_of_tendsto' hre (fun n => (hlt n).le)
  have hzx : x₀ ≤ z.re := ge_of_tendsto' hre (fun n => (hu n).1.1)
  have hzd : z.re ∈ rayDomain x₀ X :=
    ⟨hzx, lt_of_le_of_lt (WithTop.coe_le_coe.mpr hza) ha.2⟩
  refine ⟨hzd, ?_⟩
  have hlim := (hf z.re hzd).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr
      ⟨hre, Eventually.of_forall (fun n => (hu n).1)⟩)
  exact le_of_tendsto_of_tendsto' hlim him (fun n => (hu n).2)

/-- Helper toward Proposition 3.9: the hypograph with no height
restriction beyond a ray's limiting abscissa is closed. This preserves the
conditional upper bound in the definition of `closedBetween`. -/
theorem intrinsicBetween5_isClosed_extendedHypograph
    {x₀ : ℝ} {X : WithTop ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (rayDomain x₀ X)) :
    IsClosed {z : ℂ | x₀ ≤ z.re ∧
      (z.re ∈ rayDomain x₀ X → z.im ≤ f z.re)} := by
  apply IsSeqClosed.isClosed
  intro u z hu hz
  have hre := (Complex.continuous_re.tendsto z).comp hz
  have him := (Complex.continuous_im.tendsto z).comp hz
  refine ⟨ge_of_tendsto' hre (fun n => (hu n).1), ?_⟩
  intro hzd
  have hev : ∀ᶠ n in atTop, (u n).re ∈ rayDomain x₀ X := by
    induction X using WithTop.recTopCoe with
    | top =>
      exact Eventually.of_forall (fun n => ⟨(hu n).1, WithTop.coe_lt_top _⟩)
    | coe b =>
      have hzb : z.re < b := WithTop.coe_lt_coe.mp hzd.2
      exact (hre.eventually (gt_mem_nhds hzb)).mono
        (fun n hn => ⟨(hu n).1, WithTop.coe_lt_coe.mpr hn⟩)
  have hlim := (hf z.re hzd).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hre, hev⟩)
  exact le_of_tendsto_of_tendsto him hlim (hev.mono (fun n hn => (hu n).2 hn))

/-- Helper toward Proposition 3.9: the strict region between proper
graph rays is open. The upper inequality applies only where the upper ray
is defined; the two limiting abscissas need not be equal or infinite. -/
theorem intrinsicBetween5_isOpen_strictRegion
    {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hcR : ContinuousOn fR (rayDomain x₀ XR))
    (hescP : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XP,
      ∀ t ∈ rayDomain x₀ XP, a ≤ t → M ≤ fP t) :
    IsOpen {z : ℂ | x₀ < z.re ∧ z.re ∈ rayDomain x₀ XR ∧
      fR z.re < z.im ∧ (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)} := by
  have heq : {z : ℂ | x₀ < z.re ∧ z.re ∈ rayDomain x₀ XR ∧
      fR z.re < z.im ∧ (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)} =
      ({z : ℂ | z.re ≤ x₀} ∪
        {z : ℂ | z.re ∈ rayDomain x₀ XP ∧ fP z.re ≤ z.im})ᶜ ∩
      {z : ℂ | x₀ ≤ z.re ∧
        (z.re ∈ rayDomain x₀ XR → z.im ≤ fR z.re)}ᶜ := by
    ext z
    constructor
    · rintro ⟨hx, hdR, hlo, hhi⟩
      refine ⟨?_, ?_⟩
      · rintro (hx' | ⟨hdP, hle⟩)
        · exact hx.not_ge hx'
        · exact (hhi hdP).not_ge hle
      · rintro ⟨_, hle⟩
        exact hlo.not_ge (hle hdR)
    · rintro ⟨hnP, hnR⟩
      have hx : x₀ < z.re := lt_of_not_ge (fun h => hnP (Or.inl h))
      have hdR : z.re ∈ rayDomain x₀ XR := by
        by_contra hn
        exact hnR ⟨hx.le, fun hd => False.elim (hn hd)⟩
      refine ⟨hx, hdR, ?_, ?_⟩
      · exact lt_of_not_ge (fun h => hnR ⟨hx.le, fun _ => h⟩)
      · intro hdP
        exact lt_of_not_ge (fun h => hnP (Or.inr ⟨hdP, h⟩))
  rw [heq]
  exact ((isClosed_le Complex.continuous_re continuous_const).union
    (intrinsicBetween5_isClosed_epigraph hcP hescP)).isOpen_compl.inter
      (intrinsicBetween5_isClosed_extendedHypograph hcR).isOpen_compl

/-- Helper toward Proposition 3.9: after removing the two traces,
the closed fiber region is exactly its strict region, for rays with a common
start. This includes a finite endpoint of the upper graph. -/
theorem intrinsicBetween5_closedBetween_diff_traces
    {P R : Set ℂ} {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : P = {z | z.re ∈ rayDomain x₀ XP ∧ z.im = fP z.re})
    (hR : R = {z | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
    (hXP : (x₀ : WithTop ℝ) < XP) (hstart : fP x₀ = fR x₀) :
    closedBetween P R \ (P ∪ R) =
      {z : ℂ | x₀ < z.re ∧ z.re ∈ rayDomain x₀ XR ∧
        fR z.re < z.im ∧ (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)} := by
  ext z
  rw [Set.mem_sdiff, mem_closedBetween_iff hP hR]
  constructor
  · rintro ⟨⟨hdR, hlo, hhi⟩, hn⟩
    have hneR : z.im ≠ fR z.re := fun he => hn (Or.inr (hR ▸ ⟨hdR, he⟩))
    have hstrictR : fR z.re < z.im := lt_of_le_of_ne hlo hneR.symm
    have hxne : x₀ ≠ z.re := by
      intro he
      have hdP : z.re ∈ rayDomain x₀ XP := he ▸ ⟨le_refl _, hXP⟩
      have hsame : fP z.re = fR z.re := he ▸ hstart
      exact hstrictR.not_ge (hsame ▸ hhi hdP)
    refine ⟨lt_of_le_of_ne hdR.1 hxne, hdR, hstrictR, ?_⟩
    intro hdP
    exact lt_of_le_of_ne (hhi hdP) (fun he => hn (Or.inl (hP ▸ ⟨hdP, he⟩)))
  · rintro ⟨hx, hdR, hlo, hhi⟩
    refine ⟨⟨hdR, hlo.le, fun hdP => (hhi hdP).le⟩, ?_⟩
    rw [hP, hR]
    rintro (⟨hdP, he⟩ | ⟨_, he⟩)
    · exact (hhi hdP).ne he
    · exact hlo.ne' he

/-- Helper toward Proposition 3.9: a component meeting the strict
region between two proper graph rays stays in that region, with no assertion
that the rays' limiting abscissas are infinite. -/
theorem intrinsicBetween5_component_subset_strictRegion
    {P R : Set ℂ} {x₀ : ℝ} {XP XR : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : P = {z | z.re ∈ rayDomain x₀ XP ∧ z.im = fP z.re})
    (hR : R = {z | z.re ∈ rayDomain x₀ XR ∧ z.im = fR z.re})
    (hXP : (x₀ : WithTop ℝ) < XP)
    (hcP : ContinuousOn fP (rayDomain x₀ XP))
    (hcR : ContinuousOn fR (rayDomain x₀ XR))
    (hescP : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ XP,
      ∀ t ∈ rayDomain x₀ XP, a ≤ t → M ≤ fP t)
    (hproperR : ProperGraphRay R x₀) (hstart : fP x₀ = fR x₀)
    {z : ℂ} (hz : x₀ < z.re ∧ z.re ∈ rayDomain x₀ XR ∧
      fR z.re < z.im ∧ (z.re ∈ rayDomain x₀ XP → z.im < fP z.re)) :
    connectedComponentIn (P ∪ R)ᶜ z ⊆
      {q : ℂ | x₀ < q.re ∧ q.re ∈ rayDomain x₀ XR ∧
        fR q.re < q.im ∧ (q.re ∈ rayDomain x₀ XP → q.im < fP q.re)} := by
  let V : Set ℂ := {q | x₀ < q.re ∧ q.re ∈ rayDomain x₀ XR ∧
    fR q.re < q.im ∧ (q.re ∈ rayDomain x₀ XP → q.im < fP q.re)}
  have heq : closedBetween P R \ (P ∪ R) = V :=
    intrinsicBetween5_closedBetween_diff_traces hP hR hXP hstart
  have hproperP : ProperGraphRay P x₀ := ⟨XP, fP, hXP, hcP, hP, hescP⟩
  have hcl : closure V ⊆ closedBetween P R :=
    closure_minimal (fun q hq => ((heq.symm ▸ hq) :
      q ∈ closedBetween P R \ (P ∪ R)).1)
      (isClosed_closedBetween hproperP hproperR)
  have hn : z ∈ (P ∪ R)ᶜ := ((heq.symm ▸ hz) :
    z ∈ closedBetween P R \ (P ∪ R)).2
  apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
    (intrinsicBetween5_isOpen_strictRegion hcP hcR hescP)
    ⟨z, mem_connectedComponentIn hn, hz⟩
  intro q hq
  have hqV : q ∈ V := heq ▸ ⟨hcl hq.1, connectedComponentIn_subset _ _ hq.2⟩
  exact hqV

/-- Helper toward Proposition 3.9: interpolation over a preconnected
abscissa set needs continuity only on that set, so applies inside finite
half-open ray domains without extending their divergent heights. -/
theorem intrinsicBetween5_isPreconnected_band
    {J : Set ℝ} {fP fR : ℝ → ℝ} (hJ : IsPreconnected J)
    (hcP : ContinuousOn fP J) (hcR : ContinuousOn fR J)
    (hgap : ∀ x ∈ J, fR x < fP x) :
    IsPreconnected {z : ℂ | z.re ∈ J ∧ fR z.re < z.im ∧ z.im < fP z.re} := by
  let T : ℝ × ℝ → ℂ := fun p => ⟨p.1, fR p.1 + p.2 * (fP p.1 - fR p.1)⟩
  have hcP' : ContinuousOn (fun p : ℝ × ℝ => fP p.1) (J ×ˢ Ioo (0 : ℝ) 1) :=
    hcP.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hcR' : ContinuousOn (fun p : ℝ × ℝ => fR p.1) (J ×ˢ Ioo (0 : ℝ) 1) :=
    hcR.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hcT : ContinuousOn T (J ×ˢ Ioo (0 : ℝ) 1) :=
    Complex.equivRealProdCLM.symm.continuous.comp_continuousOn
      (continuous_fst.continuousOn.prodMk
        (hcR'.add (continuous_snd.continuousOn.mul (hcP'.sub hcR'))))
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
  exact (hJ.prod isPreconnected_Ioo).image T hcT

/-- Helper toward Proposition 3.9: for a common half-open domain,
including a finite limiting abscissa, every strict-region component is the
band over the corresponding component of the positive height-gap set.
Arbitrary closed coincidence sets are allowed. No winding-side test is
assumed or concluded. -/
theorem intrinsicBetween5_component_eq_band
    {P R : Set ℂ} {x₀ : ℝ} {X : WithTop ℝ} {fP fR : ℝ → ℝ}
    (hP : P = {z | z.re ∈ rayDomain x₀ X ∧ z.im = fP z.re})
    (hR : R = {z | z.re ∈ rayDomain x₀ X ∧ z.im = fR z.re})
    (hX : (x₀ : WithTop ℝ) < X)
    (hcP : ContinuousOn fP (rayDomain x₀ X))
    (hcR : ContinuousOn fR (rayDomain x₀ X))
    (hescP : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ X,
      ∀ t ∈ rayDomain x₀ X, a ≤ t → M ≤ fP t)
    (hescR : ∀ M : ℝ, ∃ a ∈ rayDomain x₀ X,
      ∀ t ∈ rayDomain x₀ X, a ≤ t → M ≤ fR t)
    (hstart : fP x₀ = fR x₀) {z : ℂ}
    (hz : x₀ < z.re ∧ z.re ∈ rayDomain x₀ X ∧
      fR z.re < z.im ∧ z.im < fP z.re) :
    connectedComponentIn (P ∪ R)ᶜ z =
      {q : ℂ | q.re ∈ connectedComponentIn
        {x : ℝ | x₀ < x ∧ x ∈ rayDomain x₀ X ∧ fR x < fP x} z.re ∧
        fR q.re < q.im ∧ q.im < fP q.re} := by
  let J : Set ℝ := {x | x₀ < x ∧ x ∈ rayDomain x₀ X ∧ fR x < fP x}
  let C := connectedComponentIn (P ∪ R)ᶜ z
  have hzJ : z.re ∈ J := ⟨hz.1, hz.2.1, hz.2.2.1.trans hz.2.2.2⟩
  have hC := intrinsicBetween5_component_subset_strictRegion hP hR hX hcP hcR
    hescP ⟨X, fR, hX, hcR, hR, hescR⟩ hstart
    ⟨hz.1, hz.2.1, hz.2.2.1, fun _ => hz.2.2.2⟩
  have hn : z ∈ (P ∪ R)ᶜ := by
    rw [hP, hR]
    rintro (⟨_, he⟩ | ⟨_, he⟩)
    · exact hz.2.2.2.ne he
    · exact hz.2.2.1.ne' he
  have himage : Complex.re '' C ⊆ connectedComponentIn J z.re := by
    apply (isPreconnected_connectedComponentIn.image Complex.re
      Complex.continuous_re.continuousOn).subset_connectedComponentIn
      ⟨z, mem_connectedComponentIn hn, rfl⟩
    rintro _ ⟨q, hq, rfl⟩
    have hh := hC hq
    exact ⟨hh.1, hh.2.1, hh.2.2.1.trans (hh.2.2.2 hh.2.1)⟩
  have hdom : connectedComponentIn J z.re ⊆ rayDomain x₀ X :=
    fun _ hx => (connectedComponentIn_subset J z.re hx).2.1
  apply subset_antisymm
  · intro q hq
    have hh := hC hq
    exact ⟨himage ⟨q, hq, rfl⟩, hh.2.2.1, hh.2.2.2 hh.2.1⟩
  · apply (intrinsicBetween5_isPreconnected_band isPreconnected_connectedComponentIn
      (hcP.mono hdom) (hcR.mono hdom)
      (fun x hx => (connectedComponentIn_subset J z.re hx).2.2)).subset_connectedComponentIn
      ⟨mem_connectedComponentIn hzJ, hz.2.2⟩
    rintro q ⟨_, hlo, hhi⟩
    rw [hP, hR]
    rintro (⟨_, he⟩ | ⟨_, he⟩)
    · exact hhi.ne he
    · exact hlo.ne' he

/-- Helper toward Proposition 3.9: a set disjoint from a simple
winding-positive left-side test. The return may cross other drawing edges;
the set need not be a face of the entire drawing. -/
theorem intrinsicBetween5_not_leftAtOn_of_locally_right
    (p : Polyline) (hlen : 2 ≤ p.points.length) (hsimple : p.IsSimple)
    (F : Set ℂ) (hdisj : Disjoint F p.image)
    {i : ℕ} (hi : i + 1 < p.points.length) {z : ℂ}
    (hz : z ∈ openSegment ℝ (p.point i) (p.point (i + 1)))
    (s : {t : unitInterval // t ∈ openParams}) (hsz : p.toPath s.1 = z)
    (ε : ℝ) (hε : 0 < ε)
    (hright : ∀ w ∈ F, dist w z < ε →
      (star (p.point (i + 1) - p.point i) * (w - z)).im < 0) :
    ¬ LeftAtOn F p.toPath s := by
  intro hleft
  let γ := p.toPath
  have hγ : Function.Injective γ := p.toPath_injective hlen hsimple
  obtain ⟨hαs, hsβ⟩ :=
    DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk.parameter_in_segment_of_toPath_eq
      p hlen hsimple hi hz s.1 hsz
  let α : unitInterval := ⟨Polyline.segmentParameterStart i,
    Polyline.segmentParameterStart_mem_Icc i⟩
  let β : unitInterval := ⟨Polyline.segmentParameterEnd p.points.length i,
    Polyline.segmentParameterEnd_mem_Icc p.points.length i⟩
  have hαsI : α < s.1 := hαs
  have hsβI : s.1 < β := hsβ
  obtain ⟨a, b, _ha, has, hsb, _hb, q, hqi, hqF, hcl⟩ := hleft
  have hqends (w : ℂ) (hwq : w ∈ range q) (hwp : w ∈ p.image) :
      w = γ a ∨ w = γ b := by
    obtain ⟨t, rfl⟩ := hwq
    by_cases ht : t ∈ openParams
    · exact False.elim (disjoint_left.mp hdisj (hqF t ht) hwp)
    · have hend : t = 0 ∨ t = 1 := by
        change ¬ (0 < (t : ℝ) ∧ (t : ℝ) < 1) at ht
        rcases eq_or_lt_of_le t.2.1 with h0 | h0
        · exact Or.inl (Subtype.ext h0.symm)
        · exact Or.inr (Subtype.ext (le_antisymm t.2.2
            (le_of_not_gt (fun h1 => ht ⟨h0, h1⟩))))
      rcases hend with rfl | rfl
      · exact Or.inr q.source
      · exact Or.inl q.target
  have hinter : range (edgeSubarc γ a b (has.trans hsb).le) ∩ range q =
      ({γ a, γ b} : Set ℂ) := by
    ext w
    constructor
    · rintro ⟨hwγ, hwq⟩
      rw [range_edgeSubarc_eq_image_Icc32] at hwγ
      obtain ⟨t, _, rfl⟩ := hwγ
      exact hqends _ hwq ((Polyline.range_toPath p) ▸ mem_range_self t)
    · rintro (rfl | rfl)
      · exact ⟨⟨0, (edgeSubarc γ a b (has.trans hsb).le).source⟩, ⟨1, q.target⟩⟩
      · exact ⟨⟨1, (edgeSubarc γ a b (has.trans hsb).le).target⟩, ⟨0, q.source⟩⟩
  have hbound (w : ℂ) (n : ℤ)
      (hw : HasWinding ((edgeSubarc γ a b (has.trans hsb).le).trans q) w n) :
      -1 ≤ n ∧ n ≤ 1 :=
    edgeSubarc_simple_polyline_injective_return_hasWinding_bounds32
      p hsimple hlen a b (has.trans hsb) q hqi hinter w n hw
  obtain ⟨u, hu, hus⟩ := exists_between (max_lt has hαsI)
  obtain ⟨v, hsv, hv⟩ := exists_between (lt_min hsb hsβI)
  have hau : a < u := (le_max_left a α).trans_lt hu
  have hαu : α < u := (le_max_right a α).trans_lt hu
  have hvb : v < b := hv.trans_le (min_le_left b β)
  have hvβ : v < β := hv.trans_le (min_le_right b β)
  have huv : u < v := hus.trans hsv
  let R := (affineSubarc γ v b).trans (q.trans (affineSubarc γ a u))
  have hS : affineSubarc γ u v = Path.segment (γ u) (γ v) :=
    DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk.affineSubarc_eq_segment_of_subinterval
      p hi u v huv hαu.le hvβ.le
  have hzchord : z ∈ openSegment ℝ (γ u) (γ v) := by
    rw [← hsz]
    exact DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk.toPath_mem_openSegment_subinterval
      p hi u s.1 v hus hsv hαu.le hvβ.le
  have hchord : γ u ≠ γ v := fun h => huv.ne (hγ h)
  have hrebase (w : ℂ) (n : ℤ) :
      HasWinding ((edgeSubarc γ a b (has.trans hsb).le).trans q) w n ↔
        HasWinding ((Path.segment (γ u) (γ v)).trans R) w n := by
    have hh :=
      DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk.hasWinding_edgeSubarc_trans_iff_cyclic_rebase
        γ hγ a u v b hau huv hvb q w n
    rw [hS] at hh
    exact hh
  have hzq : z ∉ range q := by
    intro hzq
    have hzp : z ∈ p.image := hsz ▸ ((Polyline.range_toPath p) ▸ mem_range_self s.1)
    rcases hqends z hzq hzp with h | h
    · exact has.ne (hγ (h.symm.trans hsz.symm))
    · exact hsb.ne (hγ (hsz.trans h))
  have havoidpiece (l r : unitInterval) (hlr : l < r) (hout : s.1 ∉ Icc l r) :
      z ∉ range (affineSubarc γ l r) := by
    rw [affineSubarc_range_eq_edgeSubarc γ l r hlr,
      range_edgeSubarc_eq_image_Icc32]
    rintro ⟨t, ht, htz⟩
    have hts : t = s.1 := hγ (htz.trans hsz.symm)
    exact hout (hts ▸ ht)
  have hzR : z ∉ range R := by
    dsimp only [R]
    rw [Path.trans_range, Path.trans_range]
    rintro (hT | hq | hA)
    · exact havoidpiece v b hvb (fun h => hsv.not_ge h.1) hT
    · exact hzq hq
    · exact havoidpiece a u hau (fun h => hus.not_ge h.2) hA
  have hclosed : IsClosed (range R) := (isCompact_range R.continuous).isClosed
  have hr : 0 < Metric.infDist z (range R) :=
    (hclosed.notMem_iff_infDist_pos (range_nonempty R)).mp hzR
  have hball : Disjoint (Metric.ball z (Metric.infDist z (range R))) (range R) := by
    apply disjoint_left.mpr
    intro w hw hwr
    have hdist := Metric.infDist_le_dist_of_mem (x := z) hwr
    exact hdist.not_gt (by simpa only [Metric.mem_ball, dist_comm] using hw)
  obtain ⟨c, hc, hdir⟩ :=
    DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk.toPath_subinterval_direction
      p hi u v huv hαu.le hvβ.le
  have hsign (w : ℂ) : (star (γ v - γ u) * (w - z)).im =
      c * (star (p.point (i + 1) - p.point i) * (w - z)).im := by
    rw [hdir]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    rw [mul_assoc, Complex.mul_im]
    simp
    ring
  have hwrong : z ∈ closure {w : ℂ |
      HasWinding ((Path.segment (γ u) (γ v)).trans R) w 1 ∧
        (star (γ v - γ u) * (w - z)).im < 0} := by
    rw [hsz] at hcl
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨w, hw, hd⟩ := Metric.mem_closure_iff.mp hcl (min ε δ) (lt_min hε hδ)
    have hwε : dist w z < ε := by
      exact (show dist w z < min ε δ by simpa only [dist_comm] using hd).trans_le
        (min_le_left ε δ)
    refine ⟨w, ⟨(hrebase w 1).mp hw.2, ?_⟩, hd.trans_le (min_le_right ε δ)⟩
    rw [hsign]
    exact mul_neg_of_pos_of_neg hc (hright w hw.1 hwε)
  have htwo := (mem_closure_segment_return_winding_iff32 hchord hzchord hr R hball 1).mpr hwrong
  obtain ⟨w, hw, _⟩ := Metric.mem_closure_iff.mp htwo 1 (by norm_num)
  have hbnd := hbound w 2 ((hrebase w 2).mpr hw.1)
  norm_num at hbnd

/-- Helper toward Proposition 3.9: a set strictly below a graph on
its domain fails the simultaneous left winding tests on any west-to-east
simple polygonal edge of that graph. No assumption on the graph's behavior
at its limiting abscissa is needed for this local assertion. -/
theorem intrinsicBetween5_not_forall_leftAtOn_of_below_graph
    (p : Polyline) (hlen : 2 ≤ p.points.length) (hsimple : p.IsSimple)
    (hp : p.XMonotone) {D : Set ℝ} {f : ℝ → ℝ}
    (htrace : p.image ⊆ {z : ℂ | z.re ∈ D ∧ z.im = f z.re})
    (F : Set ℂ) (hbelow : ∀ w ∈ F, w.re ∈ D → w.im < f w.re) :
    ¬ ∀ s, LeftAtOn F p.toPath s := by
  have hi : 0 + 1 < p.points.length := by omega
  let α := Polyline.segmentParameterStart 0
  let β := Polyline.segmentParameterEnd p.points.length 0
  have hαβ : α < β := Polyline.segmentParameterStart_lt_end _ _
  let tval : ℝ := (α + β) / 2
  have hαt : α < tval := by dsimp only [tval]; linarith only [hαβ]
  have htβ : tval < β := by dsimp only [tval]; linarith only [hαβ]
  have hα0 : 0 ≤ α := (Polyline.segmentParameterStart_mem_Icc 0).1
  have hβ1 : β ≤ 1 := (Polyline.segmentParameterEnd_mem_Icc p.points.length 0).2
  let t : unitInterval := ⟨tval, hα0.trans hαt.le, htβ.le.trans hβ1⟩
  let s : {t : unitInterval // t ∈ openParams} :=
    ⟨t, hα0.trans_lt hαt, htβ.trans_le hβ1⟩
  let z := p.toPath t
  let a := p.point 0
  let b := p.point 1
  have hab : a.re < b.re := p.point_re_lt hp (by omega) hi
  have hz : z ∈ openSegment ℝ a b :=
    Polyline.toPath_mem_openSegment_of_parameter p hi t hαt htβ
  have hzseg : z ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hz
  have hzheight := (mem_segment_iff_height hab).mp hzseg
  have hxz : a.re < z.re ∧ z.re < b.re := by
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨r, hr, heq⟩ := hz
    have hre := congrArg Complex.re heq
    simp only [AffineMap.lineMap_apply_module', Complex.add_re,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, zero_mul, sub_zero] at hre
    constructor <;> nlinarith only [hr.1, hr.2, hab, hre]
  have hdisj : Disjoint F p.image := by
    apply disjoint_left.mpr
    intro w hw hwp
    have hh := htrace hwp
    exact (hbelow w hw hh.1).ne hh.2
  let ε := min (z.re - a.re) (b.re - z.re)
  have hε : 0 < ε := lt_min (sub_pos.mpr hxz.1) (sub_pos.mpr hxz.2)
  have hright (w : ℂ) (hw : w ∈ F) (hwdist : dist w z < ε) :
      (star (p.point (0 + 1) - p.point 0) * (w - z)).im < 0 := by
    have hre : |w.re - z.re| ≤ dist w z := by
      simpa only [Complex.sub_re, Complex.dist_eq] using Complex.abs_re_le_norm (w - z)
    have hleft := neg_le_abs (w.re - z.re)
    have hright := le_abs_self (w.re - z.re)
    have hεa : ε ≤ z.re - a.re := min_le_left _ _
    have hεb : ε ≤ b.re - z.re := min_le_right _ _
    have hwa : a.re ≤ w.re := by linarith only [hre, hleft, hwdist, hεa]
    have hwb : w.re ≤ b.re := by linarith only [hre, hright, hwdist, hεb]
    let q : ℂ := ⟨w.re, segmentHeight a b w.re⟩
    have hqseg : q ∈ segment ℝ a b :=
      (mem_segment_iff_height hab).mpr ⟨hwa, hwb, rfl⟩
    have hqp : q ∈ p.image := Or.inr ⟨0, hi, hqseg⟩
    have hqf := htrace hqp
    have hwlt : w.im < segmentHeight a b w.re := by
      have hh := hbelow w hw hqf.1
      exact hh.trans_eq hqf.2.symm
    have hden : b.re - a.re ≠ 0 := sub_ne_zero.mpr hab.ne'
    have hzlin : (b.re - a.re) * (z.im - a.im) =
        (b.im - a.im) * (z.re - a.re) := by
      rw [hzheight.2.2]
      unfold segmentHeight
      field_simp
      ring
    have hflin : (b.re - a.re) * (segmentHeight a b w.re - a.im) =
        (b.im - a.im) * (w.re - a.re) := by
      unfold segmentHeight
      field_simp
      ring
    have hmul := mul_lt_mul_of_pos_left hwlt (sub_pos.mpr hab)
    change (star (b - a) * (w - z)).im < 0
    simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im]
    nlinarith only [hmul, hzlin, hflin]
  intro h
  exact intrinsicBetween5_not_leftAtOn_of_locally_right p hlen hsimple F hdisj hi hz
    s rfl ε hε hright (h s)

/-- Helper toward Proposition 3.9: for an actual source present ray,
no component strictly below its graph can touch its left side. The graph
domain is unrestricted, and may have a finite limiting abscissa. This is
one of the four incidence tests, not the native-region identification. -/
theorem intrinsicBetween5_source_not_left_of_below_graph
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    {v : PresentVertex (shiftedStream W 0)}
    (P : InfinitePresentPath (shiftedStream W 0) v)
    {D : Set ℝ} {f : ℝ → ℝ}
    (hgraph : intrinsicEdgeRayTrace
      (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (fun n => wholePlaneEdgeι W 0 (P.edge n)) =
        {z : ℂ | z.re ∈ D ∧ z.im = f z.re})
    (F : Set ℂ) (hbelow : ∀ w ∈ F, w.re ∈ D → w.im < f w.re) :
    ¬ intrinsicRayTouchesSide
      (uibotWholePlaneSourceDomain W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (fun n => wholePlaneEdgeι W 0 (P.edge n)) F false := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let M := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  intro hside
  obtain ⟨n, hn⟩ :=
    (intrinsicBetween_source_ray_touches_side_iff W H h hpast hp P F false).mp hside
  have harc := WholePlanePastGlueM0Restriction.restrict_arc W h hpast H (P.edge n, false)
  change G.arc (wholePlaneDartι W 0 (P.edge n, false)) = M.arc (P.edge n, false) at harc
  rw [harc] at hn
  have htrace : (M.arc (P.edge n, false)).image ⊆
      {z : ℂ | z.re ∈ D ∧ z.im = f z.re} := by
    intro z hz
    rw [← hgraph, intrinsicGeodesicSource_trace W H G hp]
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change z ∈ (G.arc (wholePlaneDartι W 0 (P.edge n, false))).image
    rw [harc]
    exact hz
  have hmono : (M.arc (P.edge n, false)).XMonotone :=
    infinitePresentPath_arc_xMonotone (H.1 0)
      (fun j => ⟨monotoneLayoutDrawing (shiftedStream W 0) j
        ((monotone_family_all (shiftedStream W 0)) j).choose,
        ((monotone_family_all (shiftedStream W 0)) j).choose_spec⟩) P n
  exact intrinsicBetween5_not_forall_leftAtOn_of_below_graph
    (M.arc (P.edge n, false)) (M.arc_length _) (M.arc_simple _) hmono htrace F hbelow hn































































































































































end DirectedDistances.PaperProofs.Section3
end
