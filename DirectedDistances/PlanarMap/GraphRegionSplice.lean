module

public import DirectedDistances.PlanarMap.GraphRegion
public import DirectedDistances.PlanarMap.GraphRegionClosure
public import DirectedDistances.PlanarMap.GraphRegionWedge
public import DirectedDistances.KMSW.MonotoneStageCertificate
import Mathlib.Topology.Piecewise
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Splicing an upper graph

Helpers toward the plane-realization obligation of adjudication n308; not paper results. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap

open Set
open scoped Topology

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] def spliceFn (f g : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  fun x => if x ∈ Icc a b then g x else f x

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem spliceFn_of_mem {f g : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ Icc a b) :
    spliceFn f g a b x = g x := by
  simp only [spliceFn, ite_eq_left hx]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem spliceFn_of_not_mem {f g : ℝ → ℝ} {a b x : ℝ} (hx : x ∉ Icc a b) :
    spliceFn f g a b x = f x := by
  simp only [spliceFn, ite_eq_right hx]

private theorem upper_le_cap {upper g : ℝ → ℝ} {a b : ℝ}
    (ha : g a = upper a) (hb : g b = upper b)
    (hgap : ∀ x ∈ Ioo a b, upper x < g x) :
    ∀ x ∈ Icc a b, upper x ≤ g x := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hxa | hxa
  · subst x
    exact ha.ge
  · rcases lt_or_eq_of_le hx.2 with hxb | hxb
    · exact (hgap x ⟨hxa, hxb⟩).le
    · subst x
      exact hb.ge

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem le_spliceFn {upper g : ℝ → ℝ} {a b : ℝ}
    (ha : g a = upper a) (hb : g b = upper b)
    (hgap : ∀ x ∈ Ioo a b, upper x < g x) (x : ℝ) :
    upper x ≤ spliceFn upper g a b x := by
  by_cases hx : x ∈ Icc a b
  · rw [spliceFn_of_mem hx]
    exact upper_le_cap ha hb hgap x hx
  · rw [spliceFn_of_not_mem hx]

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem lower_le_spliceFn {xmin xmax a b : ℝ} {lower upper g : ℝ → ℝ}
    (hlower : ∀ x ∈ Icc xmin xmax, lower x ≤ upper x)
    (ha : g a = upper a) (hb : g b = upper b)
    (hgap : ∀ x ∈ Ioo a b, upper x < g x) :
    ∀ x ∈ Icc xmin xmax, lower x ≤ spliceFn upper g a b x := by
  intro x hx
  exact (hlower x hx).trans (le_spliceFn ha hb hgap x)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem continuousOn_spliceFn {xmin xmax a b : ℝ} {upper g : ℝ → ℝ}
    (hab : a ≤ b) (hu : ContinuousOn upper (Icc xmin xmax))
    (hg : ContinuousOn g (Icc a b)) (ha : g a = upper a) (hb : g b = upper b) :
    ContinuousOn (spliceFn upper g a b) (Icc xmin xmax) := by
  apply ContinuousOn.piecewise (t := Icc a b)
  · intro x hx
    rw [frontier_Icc hab] at hx
    rcases hx.2 with h | h
    · simpa only [mem_singleton_iff] using h ▸ ha
    · simpa only [mem_singleton_iff] using h ▸ hb
  · rw [isClosed_Icc.closure_eq]
    exact hg.mono inter_subset_right
  · exact hu.mono inter_subset_left

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] def spliceCap {a b : ℝ} (upper g : ℝ → ℝ) (hab : a < b)
    (hu : ContinuousOn upper (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hgap : ∀ x ∈ Ioo a b, upper x < g x)
    (ha : g a = upper a) (hb : g b = upper b) : KMSW.GraphCap where
  a := a
  b := b
  low := upper
  high := g
  ab := hab
  low_continuous := hu
  high_continuous := hg
  separated := hgap
  left_join := ha.symm
  right_join := hb.symm

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem spliceCap_region {a b : ℝ} (upper g : ℝ → ℝ) (hab : a < b)
    (hu : ContinuousOn upper (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hgap : ∀ x ∈ Ioo a b, upper x < g x)
    (ha : g a = upper a) (hb : g b = upper b) :
    (spliceCap upper g hab hu hg hgap ha hb).region = graphRegion a b upper g := rfl

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem graphRegion_cap_inter_closedGraphRegion {xmin xmax a b : ℝ}
    (lower upper g : ℝ → ℝ) :
    graphRegion a b upper g ∩ closedGraphRegion xmin xmax lower upper = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact (not_le_of_gt hz.1.2.2.1) hz.2.2.2.2

private theorem spliceFn_eq_of_not_mem_Ioo {upper g : ℝ → ℝ} {a b x : ℝ}
    (ha : g a = upper a) (hb : g b = upper b) (hx : x ∉ Ioo a b) :
    spliceFn upper g a b x = upper x := by
  by_cases hxc : x ∈ Icc a b
  · rw [spliceFn_of_mem hxc]
    by_cases hxa : x = a
    · simpa only [hxa] using ha
    · have hxb : x = b := by
        by_contra hxb
        exact hx ⟨lt_of_le_of_ne hxc.1 (Ne.symm hxa), lt_of_le_of_ne hxc.2 hxb⟩
      simpa only [hxb] using hb
  · exact spliceFn_of_not_mem hxc

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem graphOver_spliceFn {xmin xmax a b : ℝ} {upper g : ℝ → ℝ}
    (hmin : xmin ≤ a) (hmax : b ≤ xmax)
    (ha : g a = upper a) (hb : g b = upper b) :
    graphOver xmin xmax (spliceFn upper g a b) =
      (graphOver xmin xmax upper ∩ {z | z.re ∉ Ioo a b}) ∪ graphOver a b g := by
  ext z
  constructor
  · intro hz
    by_cases hx : z.re ∈ Icc a b
    · exact Or.inr ⟨hx.1, hx.2, hz.2.2.trans (spliceFn_of_mem hx)⟩
    · refine Or.inl ⟨⟨hz.1, hz.2.1, hz.2.2.trans (spliceFn_of_not_mem hx)⟩, ?_⟩
      exact fun h => hx ⟨h.1.le, h.2.le⟩
  · rintro (⟨hz, hx⟩ | hz)
    · exact ⟨hz.1, hz.2.1, hz.2.2.trans (spliceFn_eq_of_not_mem_Ioo ha hb hx).symm⟩
    · exact ⟨hmin.trans hz.1, hz.2.1.trans hmax,
        hz.2.2.trans (spliceFn_of_mem ⟨hz.1, hz.2.1⟩).symm⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem graphOver_upper_subset_splice {xmin xmax a b : ℝ} {lower upper g : ℝ → ℝ}
    (hmin : xmin ≤ a) (hmax : b ≤ xmax)
    (hlower : ∀ x ∈ Icc xmin xmax, lower x ≤ upper x)
    (ha : g a = upper a) (hb : g b = upper b)
    (hgap : ∀ x ∈ Ioo a b, upper x < g x) :
    graphOver a b upper ⊆ closedGraphRegion xmin xmax lower (spliceFn upper g a b) := by
  intro z hz
  have hx : z.re ∈ Icc xmin xmax := ⟨hmin.trans hz.1, hz.2.1.trans hmax⟩
  refine ⟨hx.1, hx.2, ?_, ?_⟩
  · rw [hz.2.2]
    exact hlower z.re hx
  · rw [hz.2.2]
    exact le_spliceFn ha hb hgap z.re

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem closedGraphRegion_spliceFn {xmin xmax a b : ℝ} {lower upper g : ℝ → ℝ}
    (hmin : xmin ≤ a) (hmax : b ≤ xmax)
    (hlower : ∀ x ∈ Icc xmin xmax, lower x ≤ upper x)
    (ha : g a = upper a) (hb : g b = upper b)
    (hgap : ∀ x ∈ Ioo a b, upper x < g x) :
    closedGraphRegion xmin xmax lower (spliceFn upper g a b) =
      closedGraphRegion xmin xmax lower upper ∪ closedGraphRegion a b upper g := by
  ext z
  constructor
  · intro hz
    by_cases hu : z.im ≤ upper z.re
    · exact Or.inl ⟨hz.1, hz.2.1, hz.2.2.1, hu⟩
    · have hx : z.re ∈ Icc a b := by
        by_contra hx
        have hbound := hz.2.2.2
        rw [spliceFn_of_not_mem hx] at hbound
        exact hu hbound
      exact Or.inr ⟨hx.1, hx.2, (lt_of_not_ge hu).le,
        by simpa only [spliceFn_of_mem hx] using hz.2.2.2⟩
  · rintro (hz | hz)
    · exact ⟨hz.1, hz.2.1, hz.2.2.1,
        hz.2.2.2.trans (le_spliceFn ha hb hgap z.re)⟩
    · have hx : z.re ∈ Icc xmin xmax := ⟨hmin.trans hz.1, hz.2.1.trans hmax⟩
      exact ⟨hx.1, hx.2, (hlower z.re hx).trans hz.2.2.1,
        by simpa only [spliceFn_of_mem ⟨hz.1, hz.2.1⟩] using hz.2.2.2⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem closure_splice_cap {xmin xmax a b : ℝ} {upper g : ℝ → ℝ}
    (hmin : xmin ≤ a) (hab : a < b) (hmax : b ≤ xmax)
    (hu : ContinuousOn upper (Icc xmin xmax)) (hg : ContinuousOn g (Icc a b))
    (ha : g a = upper a) (hb : g b = upper b)
    (hgap : ∀ x ∈ Ioo a b, upper x < g x) :
    closure (graphRegion a b upper g) = closedGraphRegion a b upper g := by
  apply closure_graphRegion_eq_closedGraphRegion hab (hu.mono ?_) hg hgap ha.symm hb.symm
  intro x hx
  exact ⟨hmin.trans hx.1, hx.2.trans hmax⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem closedGraphRegion_spliceFn_eq_union_closure {xmin xmax a b : ℝ}
    {lower upper g : ℝ → ℝ}
    (hmin : xmin ≤ a) (hab : a < b) (hmax : b ≤ xmax)
    (hu : ContinuousOn upper (Icc xmin xmax)) (hg : ContinuousOn g (Icc a b))
    (hlower : ∀ x ∈ Icc xmin xmax, lower x ≤ upper x)
    (ha : g a = upper a) (hb : g b = upper b)
    (hgap : ∀ x ∈ Ioo a b, upper x < g x) :
    closedGraphRegion xmin xmax lower (spliceFn upper g a b) =
      closedGraphRegion xmin xmax lower upper ∪ closure (graphRegion a b upper g) := by
  rw [closure_splice_cap hmin hab hmax hu hg ha hb hgap]
  exact closedGraphRegion_spliceFn hmin hmax hlower ha hb hgap

private theorem abs_sub_le_mul_via {u v w x y c L : ℝ} (hxc : x ≤ c) (hcy : c ≤ y)
    (hu : |u - w| ≤ L * |x - c|) (hv : |w - v| ≤ L * |c - y|) :
    |u - v| ≤ L * |x - y| := by
  calc
    |u - v| ≤ |u - w| + |w - v| := abs_sub_le u w v
    _ ≤ L * |x - c| + L * |c - y| := add_le_add hu hv
    _ = L * |x - y| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxc), abs_of_nonpos (sub_nonpos.mpr hcy),
        abs_of_nonpos (sub_nonpos.mpr (hxc.trans hcy))]
      ring

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem abs_spliceFn_sub_le {xmin xmax a b L : ℝ} {upper g : ℝ → ℝ}
    (hmin : xmin ≤ a) (hab : a ≤ b) (hmax : b ≤ xmax)
    (ha : g a = upper a) (hb : g b = upper b)
    (hu : ∀ x ∈ Icc xmin xmax, ∀ y ∈ Icc xmin xmax,
      |upper x - upper y| ≤ L * |x - y|)
    (hg : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |g x - g y| ≤ L * |x - y|) :
    ∀ x ∈ Icc xmin xmax, ∀ y ∈ Icc xmin xmax,
      |spliceFn upper g a b x - spliceFn upper g a b y| ≤ L * |x - y| := by
  have haBig : a ∈ Icc xmin xmax := ⟨hmin, hab.trans hmax⟩
  have hbBig : b ∈ Icc xmin xmax := ⟨hmin.trans hab, hmax⟩
  have ordered : ∀ x ∈ Icc xmin xmax, ∀ y ∈ Icc xmin xmax, x ≤ y →
      |spliceFn upper g a b x - spliceFn upper g a b y| ≤ L * |x - y| := by
    intro x hx y hy hxy
    by_cases hxc : x ∈ Icc a b
    · by_cases hyc : y ∈ Icc a b
      · rw [spliceFn_of_mem hxc, spliceFn_of_mem hyc]
        exact hg x hxc y hyc
      · have hby : b ≤ y := by
          by_contra h
          exact hyc ⟨hxc.1.trans hxy, (lt_of_not_ge h).le⟩
        rw [spliceFn_of_mem hxc, spliceFn_of_not_mem hyc]
        apply abs_sub_le_mul_via hxc.2 hby (w := upper b)
        · simpa only [hb] using hg x hxc b ⟨hab, le_rfl⟩
        · exact hu b hbBig y hy
    · by_cases hyc : y ∈ Icc a b
      · have hxa : x ≤ a := by
          by_contra h
          exact hxc ⟨(lt_of_not_ge h).le, hxy.trans hyc.2⟩
        rw [spliceFn_of_not_mem hxc, spliceFn_of_mem hyc]
        apply abs_sub_le_mul_via hxa hyc.1 (w := upper a)
        · exact hu x hx a haBig
        · simpa only [ha] using hg a ⟨le_rfl, hab⟩ y hyc
      · rw [spliceFn_of_not_mem hxc, spliceFn_of_not_mem hyc]
        exact hu x hx y hy
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact ordered x hx y hy hxy
  · simpa only [abs_sub_comm] using ordered y hy x hx hyx

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem lipschitzOnWith_spliceFn {xmin xmax a b : ℝ} {L : NNReal} {upper g : ℝ → ℝ}
    (hmin : xmin ≤ a) (hab : a ≤ b) (hmax : b ≤ xmax)
    (ha : g a = upper a) (hb : g b = upper b)
    (hu : LipschitzOnWith L upper (Icc xmin xmax))
    (hg : LipschitzOnWith L g (Icc a b)) :
    LipschitzOnWith L (spliceFn upper g a b) (Icc xmin xmax) := by
  rw [lipschitzOnWith_iff_dist_le_mul] at hu hg ⊢
  simp only [Real.dist_eq] at hu hg ⊢
  exact abs_spliceFn_sub_le hmin hab hmax ha hb hu hg

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem wedgeIn_compl_spliceFn_east_upper {xmin xmax a b : ℝ}
    {lower upper g : ℝ → ℝ} (p dir : ℂ) (η : ℝ)
    (ha : g a = upper a) (hb : g b = upper b)
    (hd : 0 < dir.re) (hη : 0 < η)
    (havoid : p.re + η ≤ a ∨ b ≤ p.re)
    (hu : ∀ x ∈ Icc p.re (p.re + η),
      upper x = p.im + (dir.im / dir.re) * (x - p.re)) :
    WedgeIn p dir (closedGraphRegion xmin xmax lower (spliceFn upper g a b))ᶜ := by
  apply wedgeIn_compl_closedGraphRegion_east_upper p dir η hd hη
  intro x hx
  have hxo : x ∉ Ioo a b := by
    rintro ⟨hax, hxb⟩
    rcases havoid with hleft | hright
    · linarith [hx.2]
    · linarith [hx.1]
  rw [spliceFn_eq_of_not_mem_Ioo ha hb hxo]
  exact hu x hx

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem wedgeIn_compl_spliceFn_of_below {xmin xmax a b : ℝ}
    {lower upper g : ℝ → ℝ} {p dir : ℂ}
    (h : WedgeIn p dir {z | z.im < lower z.re}) :
    WedgeIn p dir (closedGraphRegion xmin xmax lower (spliceFn upper g a b))ᶜ := by
  rcases h with ⟨δ, hδ, hmem⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htd hε hεδ hz
  exact (not_le_of_gt (hmem t ε ht htd hε hεδ)) hz.2.2.1

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem wedgeIn_compl_spliceFn_west_lower {xmin xmax a b : ℝ}
    {lower upper g : ℝ → ℝ} (p dir : ℂ) (η : ℝ)
    (hd : dir.re < 0) (hη : 0 < η)
    (hlower : ∀ x ∈ Icc (p.re - η) p.re,
      lower x = p.im + (dir.im / dir.re) * (x - p.re)) :
    WedgeIn p dir (closedGraphRegion xmin xmax lower (spliceFn upper g a b))ᶜ :=
  wedgeIn_compl_closedGraphRegion_west_lower p dir η hd hη hlower

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem wedgeIn_compl_spliceFn_east_right_endpoint {xmin xmax a b : ℝ}
    {lower upper g : ℝ → ℝ} (p dir : ℂ) (hd : 0 < dir.re) (hp : p.re = xmax) :
    WedgeIn p dir (closedGraphRegion xmin xmax lower (spliceFn upper g a b))ᶜ :=
  wedgeIn_compl_closedGraphRegion_east_right_endpoint p dir hd hp

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem wedgeIn_compl_spliceFn_west_left_endpoint {xmin xmax a b : ℝ}
    {lower upper g : ℝ → ℝ} (p dir : ℂ) (hd : dir.re < 0) (hp : p.re = xmin) :
    WedgeIn p dir (closedGraphRegion xmin xmax lower (spliceFn upper g a b))ᶜ :=
  wedgeIn_compl_closedGraphRegion_west_left_endpoint p dir hd hp

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem spliceCap_wedge_east_lower_slope {a b : ℝ} (upper g : ℝ → ℝ) (hab : a < b)
    (hu : ContinuousOn upper (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hgap : ∀ x ∈ Ioo a b, upper x < g x)
    (ha : g a = upper a) (hb : g b = upper b)
    (p dir : ℂ) (η s' : ℝ) (hd : 0 < dir.re) (hpa : a ≤ p.re)
    (hη : 0 < η) (hηb : p.re + η ≤ b)
    (hline : ∀ x ∈ Icc p.re (p.re + η),
      upper x = p.im + (dir.im / dir.re) * (x - p.re))
    (hs : dir.im / dir.re < s')
    (hhigh : ∀ x ∈ Icc p.re (p.re + η), p.im + s' * (x - p.re) ≤ g x) :
    WedgeIn p dir (spliceCap upper g hab hu hg hgap ha hb).region :=
  wedgeIn_graphRegion_east_lower_slope p dir η s' hd hpa hη hηb hline hs hhigh

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem spliceCap_wedge_east_lower_continuous {a b : ℝ} (upper g : ℝ → ℝ)
    (hab : a < b) (hu : ContinuousOn upper (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hgap : ∀ x ∈ Ioo a b, upper x < g x)
    (ha : g a = upper a) (hb : g b = upper b)
    (p dir : ℂ) (η : ℝ) (hd : 0 < dir.re) (hp : p.re ∈ Ioo a b)
    (hη : 0 < η) (hηb : p.re + η ≤ b)
    (hline : ∀ x ∈ Icc p.re (p.re + η),
      upper x = p.im + (dir.im / dir.re) * (x - p.re)) :
    WedgeIn p dir (spliceCap upper g hab hu hg hgap ha hb).region := by
  have hgp : ContinuousAt g p.re := hg.continuousAt (Icc_mem_nhds hp.1 hp.2)
  have hlinep := hline p.re ⟨le_rfl, by linarith⟩
  have hpg : p.im < g p.re := by
    have h := hgap p.re hp
    simpa only [hlinep, sub_self, mul_zero, add_zero] using h
  exact wedgeIn_graphRegion_east_lower_continuous p dir η hd hp.1.le hη hηb
    hline hgp hpg

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem spliceCap_wedge_west_upper_slope {a b : ℝ} (upper g : ℝ → ℝ) (hab : a < b)
    (hu : ContinuousOn upper (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hgap : ∀ x ∈ Ioo a b, upper x < g x)
    (ha : g a = upper a) (hb : g b = upper b)
    (p dir : ℂ) (η s' : ℝ) (hd : dir.re < 0) (hpb : p.re ≤ b)
    (hη : 0 < η) (hηa : a ≤ p.re - η)
    (hline : ∀ x ∈ Icc (p.re - η) p.re,
      g x = p.im + (dir.im / dir.re) * (x - p.re))
    (hs : dir.im / dir.re < s')
    (hlow : ∀ x ∈ Icc (p.re - η) p.re, upper x ≤ p.im + s' * (x - p.re)) :
    WedgeIn p dir (spliceCap upper g hab hu hg hgap ha hb).region :=
  wedgeIn_graphRegion_west_upper_slope p dir η s' hd hpb hη hηa hline hs hlow

end DirectedDistances.PlanarMap
