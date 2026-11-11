module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.ContinuousOn
import DirectedDistances.PlanarMap.TriangleGeometry






public section
namespace DirectedDistances.PlanarMap

open Set Filter Metric
open scoped Topology



@[expose] def graphRegion (a b : ℝ) (f g : ℝ → ℝ) : Set ℂ :=
  {z | a < z.re ∧ z.re < b ∧ f z.re < z.im ∧ z.im < g z.re}



@[expose] def closedGraphRegion (a b : ℝ) (f g : ℝ → ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ f z.re ≤ z.im ∧ z.im ≤ g z.re}



@[expose] def graphOver (a b : ℝ) (f : ℝ → ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ z.im = f z.re}



@[expose] def graphParam (f : ℝ → ℝ) : ℝ → ℂ :=
  fun x => (x : ℂ) + (f x : ℂ) * Complex.I



theorem graphOver_eq_image {a b : ℝ} (f : ℝ → ℝ) :
    graphOver a b f = graphParam f '' Icc a b := by
  ext z
  constructor
  · rintro ⟨ha, hb, hz⟩
    refine ⟨z.re, ⟨ha, hb⟩, ?_⟩
    apply Complex.ext
    · simp [graphParam]
    · simpa [graphParam] using hz.symm
  · rintro ⟨x, hx, rfl⟩
    simpa [graphOver, graphParam] using hx



theorem isCompact_graphOver {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) : IsCompact (graphOver a b f) := by
  by_cases hab : a ≤ b
  · rw [graphOver_eq_image]
    apply isCompact_Icc.image_of_continuousOn
    change ContinuousOn (fun x : ℝ => (x : ℂ) + (f x : ℂ) * Complex.I) (Icc a b)
    fun_prop
  · rw [graphOver_eq_image, Icc_eq_empty hab, image_empty]
    exact isCompact_empty



theorem isClosed_graphOver {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) : IsClosed (graphOver a b f) :=
  (isCompact_graphOver hf).isClosed



theorem isPathConnected_graphOver {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    IsPathConnected (graphOver a b f) := by
  rw [graphOver_eq_image]
  apply ((convex_Icc a b).isPathConnected ⟨a, le_rfl, hab⟩).image'
  change ContinuousOn (fun x : ℝ => (x : ℂ) + (f x : ℂ) * Complex.I) (Icc a b)
  fun_prop



theorem isOpen_graphRegion {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    IsOpen (graphRegion a b f g) := by
  let S : Set ℂ := {z | z.re ∈ Ioo a b}
  have hS : IsOpen S := by
    exact isOpen_Ioo.preimage (by fun_prop)
  have hfc : ContinuousOn (fun z : ℂ => f z.re) S := by
    apply continuousOn_of_forall_continuousAt
    intro z hz
    have hn : Icc a b ∈ 𝓝 z.re :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hz)
        (fun x hx => ⟨hx.1.le, hx.2.le⟩)
    exact (hf.continuousAt hn).comp (by fun_prop)
  have hgc : ContinuousOn (fun z : ℂ => g z.re) S := by
    apply continuousOn_of_forall_continuousAt
    intro z hz
    have hn : Icc a b ∈ 𝓝 z.re :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hz)
        (fun x hx => ⟨hx.1.le, hx.2.le⟩)
    exact (hg.continuousAt hn).comp (by fun_prop)
  have hlo : ContinuousOn (fun z : ℂ => z.im - f z.re) S := by
    exact Complex.continuous_im.continuousOn.sub hfc
  have hhi : ContinuousOn (fun z : ℂ => g z.re - z.im) S := by
    exact hgc.sub Complex.continuous_im.continuousOn
  have hloOpen : IsOpen (S ∩ {z | 0 < z.im - f z.re}) := by
    exact hlo.isOpen_inter_preimage hS isOpen_Ioi
  have hhiOpen : IsOpen (S ∩ {z | 0 < g z.re - z.im}) := by
    exact hhi.isOpen_inter_preimage hS isOpen_Ioi
  have heq : graphRegion a b f g =
      (S ∩ {z | 0 < z.im - f z.re}) ∩ (S ∩ {z | 0 < g z.re - z.im}) := by
    ext z
    simp [graphRegion, S, sub_pos, and_assoc, and_left_comm, and_comm]
  rw [heq]
  exact hloOpen.inter hhiOpen



theorem isPathConnected_graphRegion {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hgap : ∀ x ∈ Ioo a b, f x < g x) :
    IsPathConnected (graphRegion a b f g) := by
  let D : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo 0 1
  let H : ℝ × ℝ → ℝ := fun p => f p.1 + p.2 * (g p.1 - f p.1)
  let F : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (H p : ℂ) * Complex.I
  have hDconvex : Convex ℝ D := (convex_Ioo a b).prod (convex_Ioo 0 1)
  obtain ⟨x, hx⟩ := exists_between hab
  have hDne : D.Nonempty :=
    ⟨(x, (1 : ℝ) / 2), ⟨hx, by norm_num⟩⟩
  have hD : IsPathConnected D := hDconvex.isPathConnected hDne
  have hfc : ContinuousOn (fun p : ℝ × ℝ => f p.1) D := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    have hn : Icc a b ∈ 𝓝 p.1 :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hp.1) fun y hy =>
        ⟨hy.1.le, hy.2.le⟩
    exact (hf.continuousAt hn).comp (by fun_prop)
  have hgc : ContinuousOn (fun p : ℝ × ℝ => g p.1) D := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    have hn : Icc a b ∈ 𝓝 p.1 :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hp.1) fun y hy =>
        ⟨hy.1.le, hy.2.le⟩
    exact (hg.continuousAt hn).comp (by fun_prop)
  have hH : ContinuousOn H D := by
    dsimp [H]
    exact hfc.add (continuousOn_snd.mul (hgc.sub hfc))
  have hF : ContinuousOn F D := by
    dsimp [F]
    fun_prop
  have hEq : graphRegion a b f g = F '' D := by
    ext z
    constructor
    · rintro ⟨hax, hxb, hlow, hhigh⟩
      have hx : z.re ∈ Ioo a b := ⟨hax, hxb⟩
      have hd : 0 < g z.re - f z.re := sub_pos.mpr (hgap z.re hx)
      let t := (z.im - f z.re) / (g z.re - f z.re)
      have ht0 : 0 < t := by
        dsimp [t]
        exact div_pos (sub_pos.mpr hlow) hd
      have ht1 : t < 1 := by
        dsimp [t]
        rw [div_lt_one hd]
        linarith
      have hval : f z.re + t * (g z.re - f z.re) = z.im := by
        dsimp [t]
        field_simp [ne_of_gt hd]
        ring
      refine ⟨(z.re, t), ⟨hx, ht0, ht1⟩, ?_⟩
      apply Complex.ext
      · simp [F]
      · simpa [F, H] using hval
    · rintro ⟨⟨x, t⟩, ⟨hx, ht0, ht1⟩, rfl⟩
      have hd : 0 < g x - f x := sub_pos.mpr (hgap x hx)
      have hlow : f x < f x + t * (g x - f x) := by
        nlinarith [mul_pos ht0 hd]
      have hhigh : f x + t * (g x - f x) < g x := by
        nlinarith [mul_lt_mul_of_pos_right ht1 hd]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [F] using hx.1
      · simpa [F] using hx.2
      · simpa [F, H] using hlow
      · simpa [F, H] using hhigh
  rw [hEq]
  exact hD.image' hF



theorem isClosed_closedGraphRegion {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    IsClosed (closedGraphRegion a b f g) := by
  let S : Set ℂ := Complex.re ⁻¹' Icc a b
  have hS : IsClosed S := isClosed_Icc.preimage Complex.continuous_re
  have hfc : ContinuousOn (fun z : ℂ => f z.re) S :=
    hf.comp Complex.continuous_re.continuousOn fun _ hz => hz
  have hgc : ContinuousOn (fun z : ℂ => g z.re) S :=
    hg.comp Complex.continuous_re.continuousOn fun _ hz => hz
  have hlo : ContinuousOn (fun z : ℂ => z.im - f z.re) S :=
    Complex.continuous_im.continuousOn.sub hfc
  have hhi : ContinuousOn (fun z : ℂ => g z.re - z.im) S :=
    hgc.sub Complex.continuous_im.continuousOn
  have hloClosed : IsClosed (S ∩ {z | 0 ≤ z.im - f z.re}) :=
    hlo.preimage_isClosed_of_isClosed hS isClosed_Ici
  have hhiClosed : IsClosed (S ∩ {z | 0 ≤ g z.re - z.im}) :=
    hhi.preimage_isClosed_of_isClosed hS isClosed_Ici
  have hEq : closedGraphRegion a b f g =
      (S ∩ {z | 0 ≤ z.im - f z.re}) ∩ (S ∩ {z | 0 ≤ g z.re - z.im}) := by
    ext z
    simp [closedGraphRegion, S, sub_nonneg, and_assoc, and_left_comm, and_comm]
  rw [hEq]
  exact hloClosed.inter hhiClosed



theorem isBounded_closedGraphRegion {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (_hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    Bornology.IsBounded (closedGraphRegion a b f g) := by
  obtain ⟨Rf, hRf⟩ :=
    (isCompact_Icc.image_of_continuousOn hf).isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨Rg, hRg⟩ :=
    (isCompact_Icc.image_of_continuousOn hg).isBounded.subset_closedBall (0 : ℝ)
  let Rx := max |a| |b|
  let Ry := max Rf Rg
  have hball : closedGraphRegion a b f g ⊆ closedBall (0 : ℂ) (Rx + Ry) := by
    intro z hz
    have hx : z.re ∈ Icc a b := ⟨hz.1, hz.2.1⟩
    have hfb : |f z.re| ≤ Rf := by
      have hmem : f z.re ∈ closedBall (0 : ℝ) Rf := hRf ⟨z.re, hx, rfl⟩
      simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hmem
    have hgb : |g z.re| ≤ Rg := by
      have hmem : g z.re ∈ closedBall (0 : ℝ) Rg := hRg ⟨z.re, hx, rfl⟩
      simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hmem
    have hxabs : |z.re| ≤ Rx := by
      apply abs_le.mpr
      constructor
      · calc
          -Rx ≤ -|a| := neg_le_neg (le_max_left |a| |b|)
          _ ≤ a := neg_abs_le a
          _ ≤ z.re := hz.1
      · calc
          z.re ≤ b := hz.2.1
          _ ≤ |b| := le_abs_self b
          _ ≤ Rx := le_max_right |a| |b|
    have hylo : -Ry ≤ z.im := by
      calc
        -Ry ≤ -Rf := neg_le_neg (le_max_left Rf Rg)
        _ ≤ f z.re := (abs_le.mp hfb).1
        _ ≤ z.im := hz.2.2.1
    have hyhi : z.im ≤ Ry := by
      calc
        z.im ≤ g z.re := hz.2.2.2
        _ ≤ Rg := (abs_le.mp hgb).2
        _ ≤ Ry := le_max_right Rf Rg
    have hyabs : |z.im| ≤ Ry := abs_le.mpr ⟨hylo, hyhi⟩
    have hnorm : ‖z‖ ≤ Rx + Ry := by
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ Rx + Ry := add_le_add hxabs hyabs
    simpa only [mem_closedBall, dist_zero_right] using hnorm
  exact isBounded_closedBall.subset hball



theorem isCompact_closedGraphRegion {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    IsCompact (closedGraphRegion a b f g) :=
  isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_closedGraphRegion hf hg, isBounded_closedGraphRegion hf hg hfg⟩

private theorem segment_subset_re_lt {a : ℝ} {x y : ℂ}
    (hx : x.re < a) (hy : y.re < a) :
    segment ℝ x y ⊆ {z | z.re < a} :=
  (convex_halfSpace_re_lt a).segment_subset hx hy

private theorem segment_subset_re_gt {b : ℝ} {x y : ℂ}
    (hx : b < x.re) (hy : b < y.re) :
    segment ℝ x y ⊆ {z | b < z.re} :=
  (convex_halfSpace_re_gt b).segment_subset hx hy



theorem isPathConnected_compl_closedGraphRegion {a b : ℝ} {f g : ℝ → ℝ}
    (_hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (_hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    IsPathConnected (closedGraphRegion a b f g)ᶜ := by
  obtain ⟨Rf, hRf⟩ :=
    (isCompact_Icc.image_of_continuousOn hf).isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨Rg, hRg⟩ :=
    (isCompact_Icc.image_of_continuousOn hg).isBounded.subset_closedBall (0 : ℝ)
  have hfBound : ∀ x ∈ Icc a b, |f x| ≤ Rf := by
    intro x hx
    have hx' : f x ∈ closedBall (0 : ℝ) Rf := hRf ⟨x, hx, rfl⟩
    simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hx'
  have hgBound : ∀ x ∈ Icc a b, |g x| ≤ Rg := by
    intro x hx
    have hx' : g x ∈ closedBall (0 : ℝ) Rg := hRg ⟨x, hx, rfl⟩
    simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hx'
  let M := max Rf Rg
  let H := M + 1
  let K := closedGraphRegion a b f g
  let base : ℂ := (a - 1 : ℝ)
  let top (x : ℝ) : ℂ := (x : ℂ) + (H : ℂ) * Complex.I
  let bottom (x : ℝ) : ℂ := (x : ℂ) + (-H : ℂ) * Complex.I
  have hbase : base.re < a := by simp [base]
  have htopRe (x : ℝ) : (top x).re = x := by simp [top]
  have hbottomRe (x : ℝ) : (bottom x).re = x := by simp [bottom]
  have htopIm (x : ℝ) : (top x).im = H := by simp [top]
  have hbottomIm (x : ℝ) : (bottom x).im = -H := by simp [bottom]
  have htop (x : ℝ) (hx : x ∈ Icc a b) : g x < H := by
    dsimp [H, M]
    calc
      g x ≤ |g x| := le_abs_self _
      _ ≤ Rg := hgBound x hx
      _ ≤ max Rf Rg := le_max_right _ _
      _ < max Rf Rg + 1 := by linarith
  have hbottom (x : ℝ) (hx : x ∈ Icc a b) : -H < f x := by
    dsimp [H, M]
    calc
      -(max Rf Rg + 1) < -max Rf Rg := by linarith
      _ ≤ -|f x| := neg_le_neg (le_trans (hfBound x hx) (le_max_left _ _))
      _ ≤ f x := neg_abs_le _
  have hleft {x y : ℂ} (hx : x.re < a) (hy : y.re < a) :
      JoinedIn Kᶜ x y := by
    apply JoinedIn.of_segment_subset
    exact (segment_subset_re_lt hx hy).trans (by
      intro q hq hqK
      exact not_le_of_gt hq hqK.1)
  have hright {x y : ℂ} (hx : b < x.re) (hy : b < y.re) :
      JoinedIn Kᶜ x y := by
    apply JoinedIn.of_segment_subset
    exact (segment_subset_re_gt hx hy).trans (by
      intro q hq hqK
      exact not_le_of_gt hq hqK.2.1)
  have htopVertical {x : ℝ} (hx : x ∈ Icc a b) {z : ℂ}
      (hzRe : z.re = x) (hzIm : g x < z.im) : JoinedIn Kᶜ z (top x) := by
    apply JoinedIn.of_segment_subset
    intro q hq hqK
    have hzReLe : z ∈ {q : ℂ | q.re ≤ x} := by
      simpa only [Set.mem_ofPred_eq] using hzRe.le
    have htReLe : top x ∈ {q : ℂ | q.re ≤ x} := by
      change (top x).re ≤ x
      rw [htopRe]
    have hqReLe : q.re ≤ x :=
      (convex_halfSpace_re_le x).segment_subset hzReLe htReLe hq
    have hzReGe : z ∈ {q : ℂ | x ≤ q.re} := by
      simpa only [Set.mem_ofPred_eq] using hzRe.ge
    have htReGe : top x ∈ {q : ℂ | x ≤ q.re} := by
      change x ≤ (top x).re
      rw [htopRe]
    have hqReGe : x ≤ q.re :=
      (convex_halfSpace_re_ge x).segment_subset hzReGe htReGe hq
    have hzIm' : z ∈ {q : ℂ | g x < q.im} := by
      simpa only [Set.mem_ofPred_eq] using hzIm
    have htIm' : top x ∈ {q : ℂ | g x < q.im} := by
      change g x < (top x).im
      rw [htopIm]
      exact htop x hx
    have hqIm : g x < q.im :=
      (convex_halfSpace_im_gt (g x)).segment_subset hzIm' htIm' hq
    have hqRe : q.re = x := le_antisymm hqReLe hqReGe
    have hqHigh : q.im ≤ g x := by simpa only [hqRe] using hqK.2.2.2
    exact not_le_of_gt hqIm hqHigh
  have hbottomVertical {x : ℝ} (hx : x ∈ Icc a b) {z : ℂ}
      (hzRe : z.re = x) (hzIm : z.im < f x) :
      JoinedIn Kᶜ z (bottom x) := by
    apply JoinedIn.of_segment_subset
    intro q hq hqK
    have hzReLe : z ∈ {q : ℂ | q.re ≤ x} := by
      simpa only [Set.mem_ofPred_eq] using hzRe.le
    have hbReLe : bottom x ∈ {q : ℂ | q.re ≤ x} := by
      change (bottom x).re ≤ x
      rw [hbottomRe]
    have hqReLe : q.re ≤ x :=
      (convex_halfSpace_re_le x).segment_subset hzReLe hbReLe hq
    have hzReGe : z ∈ {q : ℂ | x ≤ q.re} := by
      simpa only [Set.mem_ofPred_eq] using hzRe.ge
    have hbReGe : bottom x ∈ {q : ℂ | x ≤ q.re} := by
      change x ≤ (bottom x).re
      rw [hbottomRe]
    have hqReGe : x ≤ q.re :=
      (convex_halfSpace_re_ge x).segment_subset hzReGe hbReGe hq
    have hzIm' : z ∈ {q : ℂ | q.im < f x} := by
      simpa only [Set.mem_ofPred_eq] using hzIm
    have hbIm' : bottom x ∈ {q : ℂ | q.im < f x} := by
      change (bottom x).im < f x
      rw [hbottomIm]
      exact hbottom x hx
    have hqIm : q.im < f x :=
      (convex_halfSpace_im_lt (f x)).segment_subset hzIm' hbIm' hq
    have hqRe : q.re = x := le_antisymm hqReLe hqReGe
    have hqLow : f x ≤ q.im := by simpa only [hqRe] using hqK.2.2.1
    exact not_le_of_gt hqIm hqLow
  have htopHorizontal (x : ℝ) :
      JoinedIn Kᶜ (top x) (top (a - 1)) := by
    apply JoinedIn.of_segment_subset
    have hline : segment ℝ (top x) (top (a - 1)) ⊆ {q | q.im = H} := by
      intro q hq
      apply le_antisymm
      · exact (convex_halfSpace_im_le H).segment_subset
          (by change (top x).im ≤ H; rw [htopIm])
          (by change (top (a - 1)).im ≤ H; rw [htopIm]) hq
      · exact (convex_halfSpace_im_ge H).segment_subset
          (by change H ≤ (top x).im; rw [htopIm])
          (by change H ≤ (top (a - 1)).im; rw [htopIm]) hq
    exact hline.trans (by
      intro q hq hqK
      change q.im = H at hq
      have hx : q.re ∈ Icc a b := ⟨hqK.1, hqK.2.1⟩
      have hqHigh : H ≤ g q.re := by simpa only [hq] using hqK.2.2.2
      exact not_le_of_gt (htop q.re hx) hqHigh)
  have hbottomHorizontal (x : ℝ) :
      JoinedIn Kᶜ (bottom x) (bottom (a - 1)) := by
    apply JoinedIn.of_segment_subset
    have hline : segment ℝ (bottom x) (bottom (a - 1)) ⊆ {q | q.im = -H} := by
      intro q hq
      apply le_antisymm
      · exact (convex_halfSpace_im_le (-H)).segment_subset
          (by change (bottom x).im ≤ -H; rw [hbottomIm])
          (by change (bottom (a - 1)).im ≤ -H; rw [hbottomIm]) hq
      · exact (convex_halfSpace_im_ge (-H)).segment_subset
          (by change -H ≤ (bottom x).im; rw [hbottomIm])
          (by change -H ≤ (bottom (a - 1)).im; rw [hbottomIm]) hq
    exact hline.trans (by
      intro q hq hqK
      change q.im = -H at hq
      have hx : q.re ∈ Icc a b := ⟨hqK.1, hqK.2.1⟩
      have hqLow : f q.re ≤ -H := by simpa only [hq] using hqK.2.2.1
      exact not_le_of_gt (hbottom q.re hx) hqLow)
  have hbaseTop : (top (a - 1)).re < a := by rw [htopRe]; linarith
  have hbaseBottom : (bottom (a - 1)).re < a := by rw [hbottomRe]; linarith
  have hjoin : ∀ z ∈ Kᶜ, JoinedIn Kᶜ z base := by
    intro z hz
    by_cases hxLeft : z.re < a
    · exact hleft hxLeft hbase
    · by_cases hxRight : b < z.re
      · have hrightTop : JoinedIn Kᶜ z (top z.re) :=
          hright (x := z) (y := top z.re) hxRight (by
            rw [htopRe]
            exact hxRight)
        exact hrightTop.trans
          ((htopHorizontal z.re).trans (hleft hbaseTop hbase))
      · have hx : z.re ∈ Icc a b := ⟨le_of_not_gt hxLeft, le_of_not_gt hxRight⟩
        have hfiber : ¬ (f z.re ≤ z.im ∧ z.im ≤ g z.re) := by
          intro h
          exact hz ⟨hx.1, hx.2, h.1, h.2⟩
        rcases not_and_or.mp hfiber with hlo | hhi
        · have hlo' : z.im < f z.re := lt_of_not_ge hlo
          exact (hbottomVertical hx rfl hlo').trans
            ((hbottomHorizontal z.re).trans (hleft hbaseBottom hbase))
        · have hhi' : g z.re < z.im := lt_of_not_ge hhi
          exact (htopVertical hx rfl hhi').trans
            ((htopHorizontal z.re).trans (hleft hbaseTop hbase))
  apply isPathConnected_iff.mpr
  refine ⟨⟨base, ?_⟩, ?_⟩
  · intro hb
    exact not_le_of_gt hbase hb.1
  · intro x hx y hy
    exact (hjoin x hx).trans (hjoin y hy).symm



theorem exists_norm_gt_compl_closedGraphRegion {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) (R : ℝ) :
    ∃ z ∈ (closedGraphRegion a b f g)ᶜ, R < ‖z‖ :=
  exists_norm_gt_compl_of_isCompact (isCompact_closedGraphRegion hf hg hfg) R



theorem isBounded_graphRegion {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    Bornology.IsBounded (graphRegion a b f g) := by
  apply (isBounded_closedGraphRegion hf hg hfg).subset
  intro z hz
  exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩



theorem frontier_graphRegion_subset {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    frontier (graphRegion a b f g) ⊆
      graphOver a b f ∪ graphOver a b g ∪
        {z | (z.re = a ∨ z.re = b) ∧ f z.re ≤ z.im ∧ z.im ≤ g z.re} := by
  let U := graphRegion a b f g
  have hsub : U ⊆ closedGraphRegion a b f g := by
    intro z hz
    exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  have hcl : closure U ⊆ closedGraphRegion a b f g :=
    closure_minimal hsub (isClosed_closedGraphRegion hf hg)
  have hopen : IsOpen U := isOpen_graphRegion hf hg
  have hdisj : Disjoint (frontier U) U :=
    disjoint_frontier_iff_isOpen.mpr hopen
  intro z hz
  have hclosed : z ∈ closedGraphRegion a b f g :=
    hcl (frontier_subset_closure hz)
  have hnot : z ∉ U := fun hu => (Set.disjoint_left.mp hdisj) hz hu
  rcases hclosed with ⟨hax, hxb, hlow, hhigh⟩
  by_cases hend : z.re = a ∨ z.re = b
  · exact Or.inr ⟨hend, hlow, hhigh⟩
  · have ha : a < z.re := by
      rcases lt_or_eq_of_le hax with h | h
      · exact h
      · exact False.elim (hend (Or.inl h.symm))
    have hb : z.re < b := by
      rcases lt_or_eq_of_le hxb with h | h
      · exact h
      · exact False.elim (hend (Or.inr h))
    by_cases hstrict : f z.re < z.im
    · have heq : z.im = g z.re := by
        rcases lt_or_eq_of_le hhigh with h | h
        · exact False.elim (hnot ⟨ha, hb, hstrict, h⟩)
        · exact h
      exact Or.inl (Or.inr ⟨hax, hxb, heq⟩)
    · have heq : z.im = f z.re := le_antisymm (le_of_not_gt hstrict) hlow
      exact Or.inl (Or.inl ⟨hax, hxb, heq⟩)



theorem frontier_graphRegion_subset_of_endpoint_eq {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfa : f a = g a) (hfb : f b = g b) :
    frontier (graphRegion a b f g) ⊆ graphOver a b f ∪ graphOver a b g := by
  intro z hz
  rcases frontier_graphRegion_subset hf hg hz with hfg | hv
  · exact hfg
  · rcases hv with ⟨hend, hlow, hhigh⟩
    have hcl : closure (graphRegion a b f g) ⊆ closedGraphRegion a b f g :=
      closure_minimal (fun w hw =>
        ⟨hw.1.le, hw.2.1.le, hw.2.2.1.le, hw.2.2.2.le⟩)
        (isClosed_closedGraphRegion hf hg)
    have hclosed : z ∈ closedGraphRegion a b f g :=
      hcl (frontier_subset_closure hz)
    rcases hend with ha | hb
    · have hya : z.im = f a := by
        apply le_antisymm
        · calc z.im ≤ g z.re := hhigh
            _ = f a := by simp [ha, hfa]
        · calc f a = f z.re := by simp [ha]
            _ ≤ z.im := hlow
      exact Or.inl ⟨hclosed.1, hclosed.2.1, by simpa [ha] using hya⟩
    · have hyb : z.im = f b := by
        apply le_antisymm
        · calc z.im ≤ g z.re := hhigh
            _ = f b := by simp [hb, hfb]
        · calc f b = f z.re := by simp [hb]
            _ ≤ z.im := hlow
      exact Or.inl ⟨hclosed.1, hclosed.2.1, by simpa [hb] using hyb⟩



theorem connectedComponentIn_compl_eq_of_open_connected {U X : Set ℂ}
    (hopen : IsOpen U) (hconn : IsConnected U) (_hne : U.Nonempty)
    (hdisj : U ∩ X = ∅) (hfrontier : frontier U ⊆ X) {z : ℂ} (hz : z ∈ U) :
    connectedComponentIn Xᶜ z = U := by
  have hdisj' : Disjoint U X := Set.disjoint_iff_inter_eq_empty.mpr hdisj
  have hUX : U ⊆ Xᶜ := by
    intro x hxU hxX
    exact (Set.disjoint_left.mp hdisj') hxU hxX
  have hclose : closure U ∩ Xᶜ ⊆ U := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact hxU
    · have hfr : x ∈ frontier U := by
        rw [frontier, hopen.interior_eq]
        exact ⟨hx.1, hxU⟩
      exact False.elim (hx.2 (hfrontier hfr))
  let V : Set (↥(Xᶜ)) := (Subtype.val : ↥(Xᶜ) → ℂ) ⁻¹' U
  have hVopen : IsOpen V := hopen.preimage continuous_subtype_val
  have hVcomp : Vᶜ = (Subtype.val : ↥(Xᶜ) → ℂ) ⁻¹' (closure U)ᶜ := by
    ext x
    simp only [V, Set.mem_compl_iff, Set.mem_preimage]
    constructor
    · intro hxV hxcl
      exact hxV (hclose ⟨hxcl, x.property⟩)
    · intro hxcl hxU
      exact hxcl (subset_closure hxU)
  have hVclosed : IsClosed V := by
    rw [← isOpen_compl_iff, hVcomp]
    exact isClosed_closure.isOpen_compl.preimage continuous_subtype_val
  have hV : IsClopen V := ⟨hVclosed, hVopen⟩
  let zX : ↥(Xᶜ) := ⟨z, hUX hz⟩
  have hzV : zX ∈ V := by simpa [V, zX] using hz
  have hcomponent : connectedComponent zX ⊆ V :=
    isPreconnected_connectedComponent.subset_isClopen hV
      ⟨zX, ⟨mem_connectedComponent, hzV⟩⟩
  have hcomponentIn : connectedComponentIn Xᶜ z ⊆ U := by
    rw [connectedComponentIn_eq_image (hUX hz)]
    rintro y ⟨x, hx, rfl⟩
    simpa [V] using hcomponent hx
  have hUcomponent : U ⊆ connectedComponentIn Xᶜ z :=
    hconn.isPreconnected.subset_connectedComponentIn hz hUX
  exact hcomponentIn.antisymm hUcomponent

end DirectedDistances.PlanarMap
