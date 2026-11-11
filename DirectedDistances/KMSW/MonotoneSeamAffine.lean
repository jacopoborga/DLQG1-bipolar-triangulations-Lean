module

public import DirectedDistances.KMSW.MonotoneSeamCuts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Classical

noncomputable section



private theorem affine_point_mem (p : Polyline) (i : ℕ) (hi : i < p.points.length) :
    p.point i ∈ p.points := by
  change p.points.getD i p.start ∈ p.points
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi




private theorem affine_segment_spans {a b z : ℂ} {s t : ℝ}
    (hz : z ∈ segment ℝ a b) (hmid : z.re ∈ Ioo s t)
    (ha : a.re ∉ Ioo s t) (hb : b.re ∉ Ioo s t) :
    (a.re ≤ s ∧ t ≤ b.re) ∨ (b.re ≤ s ∧ t ≤ a.re) := by
  by_cases hab : a.re ≤ b.re
  · have hbounds := Polyline.segment_re_bounds hab hz
    left
    constructor
    · exact le_of_not_gt (fun hs => ha ⟨hs, hbounds.1.trans_lt hmid.2⟩)
    · exact le_of_not_gt (fun ht => hb ⟨hmid.1.trans_le hbounds.2, ht⟩)
  · have hz' : z ∈ segment ℝ b a := by
      rwa [segment_symm]
    have hbounds := Polyline.segment_re_bounds (le_of_not_ge hab) hz'
    right
    constructor
    · exact le_of_not_gt (fun hs => hb ⟨hs, hbounds.1.trans_lt hmid.2⟩)
    · exact le_of_not_gt (fun ht => ha ⟨hmid.1.trans_le hbounds.2, ht⟩)




private theorem affine_of_segment_graph (f : ℝ → ℝ) (a b : ℂ) (s t : ℝ)
    (hst : s < t) (ha : a.re ≤ s) (hb : t ≤ b.re)
    (hgraph : ∀ z ∈ segment ℝ a b, z.im = f z.re) :
    ∃ m c0 : ℝ, ∀ x ∈ Icc s t, f x = m * x + c0 := by
  have hdx : 0 < b.re - a.re := by linarith only [hst, ha, hb]
  let m := (b.im - a.im) / (b.re - a.re)
  let c0 := a.im - m * a.re
  refine ⟨m, c0, ?_⟩
  intro x hx
  let r := (x - a.re) / (b.re - a.re)
  let z : ℂ := (1 - r) • a + r • b
  have hr : r ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr (ha.trans hx.1)) hdx.le
    · exact (div_le_one hdx).mpr (by linarith only [hx.2, hb])
  have hz : z ∈ segment ℝ a b := by
    rw [segment_eq_image]
    exact ⟨r, hr, rfl⟩
  have hrx : r * (b.re - a.re) = x - a.re := div_mul_cancel₀ _ hdx.ne'
  have hre : z.re = x := by
    dsimp [z]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linarith only [hrx]
  have him : z.im = m * x + c0 := by
    have hmul : r * (b.im - a.im) = m * (x - a.re) := by
      dsimp [r, m]
      ring
    dsimp [z, c0]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    linarith only [hmul]
  have hh := hgraph z hz
  rw [hre] at hh
  exact hh.symm.trans him

variable (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)




private theorem affine_vertex_cut (k : ℤ) (z : ℂ)
    (hz : z ∈ ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (futureMapBoundaryDart w h k)).points) : z.re ∈ seamCutSet w h hfin := by
  apply mem_iUnion.mpr
  refine ⟨k, ?_⟩
  change z.re ∈ (_ : List ℝ).toFinset
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨z, hz, rfl⟩)




theorem seamFun_affine_of_noCut (s t : ℝ) (hst : s < t)
    (hno : ∀ c ∈ seamCutSet w h hfin, c ∉ Ioo s t) :
    ∃ m c0 : ℝ, ∀ x ∈ Icc s t, seamFun w h hfin x = m * x + c0 := by
  let q := (s + t) / 2
  let z : ℂ := ⟨q, seamFun w h hfin q⟩
  have hmid : z.re ∈ Ioo s t := by
    change s < (s + t) / 2 ∧ (s + t) / 2 < t
    constructor <;> linarith only [hst]
  have hzgraph : z ∈ {v : ℂ | v.im = seamFun w h hfin v.re} := rfl
  rw [seamFun_graph w h hfin] at hzgraph
  obtain ⟨k, hk⟩ := mem_iUnion.mp hzgraph
  let p := (monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
    (futureMapBoundaryDart w h k)
  have hcut : ∀ v ∈ p.points, v.re ∈ seamCutSet w h hfin :=
    fun v hv => affine_vertex_cut w h hfin k v hv
  have himage : ∀ v ∈ p.image, v.im = seamFun w h hfin v.re := by
    intro v hv
    have hg : v ∈ ⋃ j : ℤ,
        ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
          (futureMapBoundaryDart w h j)).image := mem_iUnion.mpr ⟨k, hv⟩
    rw [← seamFun_graph w h hfin] at hg
    exact hg
  change z ∈ p.image at hk
  rcases hk with hzstart | ⟨i, hi, hzseg⟩
  · have heq : z = p.start := hzstart
    have hc := hcut p.start (List.head_mem p.nonempty)
    exact (hno z.re (heq.symm ▸ hc) hmid).elim
  · have ha := affine_point_mem p i (by omega)
    have hb := affine_point_mem p (i + 1) hi
    have hspan := affine_segment_spans hzseg hmid
      (hno _ (hcut _ ha)) (hno _ (hcut _ hb))
    have hg : ∀ v ∈ segment ℝ (p.point i) (p.point (i + 1)),
        v.im = seamFun w h hfin v.re := by
      intro v hv
      exact himage v (Or.inr ⟨i, hi, hv⟩)
    rcases hspan with hspan | hspan
    · exact affine_of_segment_graph (seamFun w h hfin) _ _ s t hst
        hspan.1 hspan.2 hg
    · apply affine_of_segment_graph (seamFun w h hfin)
        (p.point (i + 1)) (p.point i) s t hst hspan.1 hspan.2
      intro v hv
      exact hg v (by rwa [segment_symm])





theorem seamFun_neg_orderIso_affine_of_noCut (phi : ℝ ≃o ℝ) (c d m0 c0 : ℝ)
    (hm0 : 0 < m0) (hphi : ∀ x ∈ Icc c d, phi x = m0 * x + c0)
    (hno : ∀ y ∈ seamCutSet w h hfin, y ∉ (fun x => -(phi x)) '' Ioo c d) :
    ∃ m c1 : ℝ, ∀ x ∈ Icc c d, seamFun w h hfin (-(phi x)) = m * x + c1 := by
  by_cases hcd : c < d
  · have hst : -(phi d) < -(phi c) := by
      rw [hphi d ⟨hcd.le, le_rfl⟩, hphi c ⟨le_rfl, hcd.le⟩]
      nlinarith only [hm0, hcd]
    have hno' : ∀ y ∈ seamCutSet w h hfin, y ∉ Ioo (-(phi d)) (-(phi c)) := by
      intro y hy hiy
      have hpre : phi.symm (-y) ∈ Ioo c d := by
        constructor
        · apply phi.lt_iff_lt.mp
          rw [phi.apply_symm_apply]
          linarith only [hiy.2]
        · apply phi.lt_iff_lt.mp
          rw [phi.apply_symm_apply]
          linarith only [hiy.1]
      apply hno y hy
      refine ⟨phi.symm (-y), hpre, ?_⟩
      change -(phi (phi.symm (-y))) = y
      rw [phi.apply_symm_apply, neg_neg]
    obtain ⟨m, b, hf⟩ := seamFun_affine_of_noCut w h hfin _ _ hst hno'
    refine ⟨-m * m0, b - m * c0, ?_⟩
    intro x hx
    have hinter : -(phi x) ∈ Icc (-(phi d)) (-(phi c)) :=
      ⟨neg_le_neg (phi.monotone hx.2), neg_le_neg (phi.monotone hx.1)⟩
    rw [hf _ hinter, hphi x hx]
    ring
  · refine ⟨0, seamFun w h hfin (-(phi c)), ?_⟩
    intro x hx
    have heq : x = c := by linarith only [hx.1, hx.2, hcd]
    rw [heq, zero_mul, zero_add]




theorem seamFun_neg_orderIso_affine_of_noCut_preimage (phi : ℝ ≃o ℝ)
    (c d m0 c0 : ℝ) (hm0 : 0 < m0)
    (hphi : ∀ x ∈ Icc c d, phi x = m0 * x + c0)
    (hno : ∀ x ∈ Ioo c d, -(phi x) ∉ seamCutSet w h hfin) :
    ∃ m c1 : ℝ, ∀ x ∈ Icc c d, seamFun w h hfin (-(phi x)) = m * x + c1 := by
  apply seamFun_neg_orderIso_affine_of_noCut w h hfin phi c d m0 c0 hm0 hphi
  rintro y hy ⟨x, hx, rfl⟩
  exact hno x hx hy

end

end DirectedDistances.KMSW
