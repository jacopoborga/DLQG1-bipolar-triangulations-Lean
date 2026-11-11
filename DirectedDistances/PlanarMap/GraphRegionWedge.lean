module

public import DirectedDistances.PlanarMap.GraphRegion






public section
namespace DirectedDistances.PlanarMap

open Set



@[expose] def wedgePoint (p dir : ℂ) (t ε : ℝ) : ℂ :=
  p + (t : ℂ) * (dir + (ε : ℂ) * Complex.I * dir)



@[expose] def WedgeIn (p dir : ℂ) (S : Set ℂ) : Prop :=
  ∃ δ > 0, ∀ t ε, 0 < t → t < δ → 0 < ε → ε < δ →
    wedgePoint p dir t ε ∈ S



theorem wedgePoint_re (p dir : ℂ) (t ε : ℝ) :
    (wedgePoint p dir t ε).re = p.re + t * (dir.re - ε * dir.im) := by
  simp only [wedgePoint, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring



theorem wedgePoint_im (p dir : ℂ) (t ε : ℝ) :
    (wedgePoint p dir t ε).im = p.im + t * (dir.im + ε * dir.re) := by
  simp only [wedgePoint, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

private theorem eastWedgeDeltaPos (d m η gap B : ℝ) (hd : 0 < d)
    (hη : 0 < η) (hgap : 0 < gap) :
    0 < min 1 (min (η / (d + |m| + 1))
      (min (d / (2 * (|m| + 1))) (d * gap / (2 * (|B| + 1))))) := by
  positivity





theorem wedgeIn_graphRegion_east_lower_slope {a b : ℝ} {f g : ℝ → ℝ}
    (p dir : ℂ) (η s' : ℝ)
    (hd : 0 < dir.re) (hpa : a ≤ p.re)
    (hη : 0 < η) (hηb : p.re + η ≤ b)
    (hf : ∀ x ∈ Icc p.re (p.re + η),
      f x = p.im + (dir.im / dir.re) * (x - p.re))
    (hs : dir.im / dir.re < s')
    (hg : ∀ x ∈ Icc p.re (p.re + η),
      p.im + s' * (x - p.re) ≤ g x) :
    WedgeIn p dir (graphRegion a b f g) := by
  let d := dir.re
  let m := dir.im
  let s := m / d
  let gap := s' - s
  let B := s' * m + d
  let δ := min 1 (min (η / (d + |m| + 1))
    (min (d / (2 * (|m| + 1))) (d * gap / (2 * (|B| + 1)))))
  have hd' : 0 < d := by dsimp [d]; exact hd
  have hgap : 0 < gap := by dsimp [gap, s, m, d]; exact sub_pos.mpr hs
  have hδ : 0 < δ := by
    dsimp [δ]
    exact eastWedgeDeltaPos d m η gap B hd' hη hgap
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htd hε hεδ
  have hδ1 : δ ≤ 1 := by dsimp [δ]; exact min_le_left _ _
  have hδx : δ ≤ η / (d + |m| + 1) := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδd : δ ≤ d / (2 * (|m| + 1)) := by
    dsimp [δ]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδs : δ ≤ d * gap / (2 * (|B| + 1)) := by
    dsimp [δ]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have hε1 : ε < 1 := lt_of_lt_of_le hεδ hδ1
  have hεd : ε < d / (2 * (|m| + 1)) := lt_of_lt_of_le hεδ hδd
  have hεs : ε < d * gap / (2 * (|B| + 1)) := lt_of_lt_of_le hεδ hδs
  have hεmul : ε * (2 * (|m| + 1)) < d := by
    calc
      ε * (2 * (|m| + 1)) <
          (d / (2 * (|m| + 1))) * (2 * (|m| + 1)) :=
            mul_lt_mul_of_pos_right hεd (by positivity)
      _ = d := by field_simp
  have hεm : ε * |m| < d := by
    have hle : ε * |m| ≤ ε * (2 * (|m| + 1)) := by
      nlinarith [hε.le, abs_nonneg m]
    exact lt_of_le_of_lt hle hεmul
  have hq : 0 < d - ε * m := by
    have hm : ε * m ≤ ε * |m| :=
      mul_le_mul_of_nonneg_left (le_abs_self m) hε.le
    linarith
  have hqUpper : d - ε * m ≤ d + |m| := by
    have hm : -ε * m ≤ ε * |m| := by
      nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs m) hε.le]
    have he : ε * |m| ≤ |m| := by nlinarith [hε1.le, abs_nonneg m]
    linarith
  have htdx : t * (d + |m| + 1) < η := by
    calc
      t * (d + |m| + 1) <
          (η / (d + |m| + 1)) * (d + |m| + 1) :=
            mul_lt_mul_of_pos_right (lt_of_lt_of_le htd hδx) (by positivity)
      _ = η := by field_simp
  have hεB : ε * (|B| + 1) < d * gap / 2 := by
    calc
      ε * (|B| + 1) <
          (d * gap / (2 * (|B| + 1))) * (|B| + 1) :=
            mul_lt_mul_of_pos_right hεs (by positivity)
      _ = d * gap / 2 := by field_simp
  have hεB' : ε * B < d * gap := by
    have hB : ε * B ≤ ε * |B| :=
      mul_le_mul_of_nonneg_left (le_abs_self B) hε.le
    have hεabs : ε * |B| < d * gap / 2 := by
      have hle : ε * |B| ≤ ε * (|B| + 1) := by nlinarith [hε.le]
      exact lt_of_le_of_lt hle hεB
    nlinarith [mul_pos hd' hgap]
  let z := wedgePoint p dir t ε
  have hx : z.re = p.re + t * (d - ε * m) := by
    rw [wedgePoint_re]
  have hy : z.im = p.im + t * (m + ε * d) := by
    rw [wedgePoint_im]
  have hpx : p.re < z.re := by rw [hx]; nlinarith
  have hxd : z.re < p.re + η := by
    have hq' : d - ε * m < d + |m| + 1 := by nlinarith [hqUpper]
    rw [hx]
    have htq := mul_lt_mul_of_pos_left hq' ht
    nlinarith [htq, htdx]
  have hxIcc : z.re ∈ Icc p.re (p.re + η) := ⟨hpx.le, hxd.le⟩
  have hfz := hf z.re hxIcc
  have hlowCoeff : 0 < (m + ε * d) - s * (d - ε * m) := by
    have hiden : (m + ε * d) - s * (d - ε * m) =
        ε * (d * d + m * m) / d := by
      dsimp [s]
      field_simp [ne_of_gt hd']
      ring
    rw [hiden]
    exact div_pos (mul_pos hε
      (add_pos_of_pos_of_nonneg (mul_pos hd' hd') (by nlinarith [sq_nonneg m]))) hd'
  have huCoeff : 0 < s' * (d - ε * m) - (m + ε * d) := by
    have hiden : s' * (d - ε * m) - (m + ε * d) =
        d * gap - ε * B := by
      dsimp [gap, s, B]
      field_simp [ne_of_gt hd']
      ring
    rw [hiden]
    exact sub_pos.mpr hεB'
  have hzlow : p.im + s * (z.re - p.re) < z.im := by
    rw [hx, hy]
    have hcancel : s * (p.re + t * (d - ε * m) - p.re) =
        s * (t * (d - ε * m)) := by ring
    rw [hcancel]
    calc
      p.im + s * (t * (d - ε * m)) =
          p.im + t * (s * (d - ε * m)) := by congr 1; ring
      _ < p.im + t * (m + ε * d) :=
        add_lt_add_right
          (mul_lt_mul_of_pos_left (sub_pos.mp hlowCoeff) ht) _
  have hzhigh : z.im < p.im + s' * (z.re - p.re) := by
    rw [hx, hy]
    have hcancel : s' * (p.re + t * (d - ε * m) - p.re) =
        s' * (t * (d - ε * m)) := by ring
    rw [hcancel]
    calc
      p.im + t * (m + ε * d) <
          p.im + t * (s' * (d - ε * m)) :=
        add_lt_add_right
          (mul_lt_mul_of_pos_left (sub_pos.mp huCoeff) ht) _
      _ = p.im + s' * (t * (d - ε * m)) := by congr 1; ring
  have hlow : f z.re < z.im := by rw [hfz]; exact hzlow
  have hhigh : z.im < g z.re := lt_of_lt_of_le hzhigh (hg z.re hxIcc)
  change a < z.re ∧ z.re < b ∧ f z.re < z.im ∧ z.im < g z.re
  exact ⟨lt_of_le_of_lt hpa hpx, lt_of_lt_of_le hxd hηb, hlow, hhigh⟩




theorem wedgeIn_graphRegion_east_lower_continuous {a b : ℝ} {f g : ℝ → ℝ}
    (p dir : ℂ) (η : ℝ)
    (hd : 0 < dir.re) (hpa : a ≤ p.re) (hη : 0 < η)
    (hηb : p.re + η ≤ b)
    (hf : ∀ x ∈ Icc p.re (p.re + η),
      f x = p.im + (dir.im / dir.re) * (x - p.re))
    (hg : ContinuousAt g p.re) (hgap : p.im < g p.re) :
    WedgeIn p dir (graphRegion a b f g) := by
  let s := dir.im / dir.re
  let s' := s + 1
  let gap := g p.re - p.im
  obtain ⟨r, hr, hrmap⟩ :=
    Metric.continuousAt_iff.mp hg (gap / 3) (by dsimp [gap]; linarith)
  let η' := min η (min (r / 2) (gap / (3 * (|s'| + 1))))
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hη' : 0 < η' := by
    dsimp [η']
    positivity
  have hη'η : η' ≤ η := by dsimp [η']; exact min_le_left _ _
  have hη'r : η' ≤ r / 2 := by
    dsimp [η']
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη'gap : η' ≤ gap / (3 * (|s'| + 1)) := by
    dsimp [η']
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hgLine : ∀ x ∈ Icc p.re (p.re + η'),
      p.im + s' * (x - p.re) ≤ g x := by
    intro x hx
    have hdistx : dist x p.re < r := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
      have hxη : x - p.re ≤ η' := by linarith [hx.2]
      linarith
    have hclose := hrmap hdistx
    have hclose' : |g x - g p.re| < gap / 3 := by
      simpa [Real.dist_eq] using hclose
    have hgx : p.im + 2 * gap / 3 < g x := by
      dsimp [gap] at hclose' ⊢
      rw [abs_lt] at hclose'
      linarith
    have hline : s' * (x - p.re) ≤ |s'| * η' := by
      have hxs : 0 ≤ x - p.re := sub_nonneg.mpr hx.1
      calc
        s' * (x - p.re) ≤ |s'| * (x - p.re) :=
          mul_le_mul_of_nonneg_right (le_abs_self s') hxs
        _ ≤ |s'| * η' :=
          mul_le_mul_of_nonneg_left (by linarith [hx.2]) (abs_nonneg s')
    have hlineBound : |s'| * η' ≤ gap / 3 := by
      calc
        |s'| * η' ≤ |s'| * (gap / (3 * (|s'| + 1))) :=
          mul_le_mul_of_nonneg_left hη'gap (abs_nonneg s')
        _ ≤ gap / 3 := by
          field_simp
          nlinarith [hgap, abs_nonneg s']
    have hline' : p.im + s' * (x - p.re) ≤ p.im + gap / 3 := by
      have := le_trans hline hlineBound
      linarith
    linarith
  have hη'b : p.re + η' ≤ b := by linarith
  apply wedgeIn_graphRegion_east_lower_slope p dir η' s' hd hpa hη'
    hη'b ?_ ?_ hgLine
  · intro x hx
    have hxη : x ∈ Icc p.re (p.re + η) := by
      refine ⟨hx.1, ?_⟩
      have := hx.2
      linarith [hη'η]
    exact hf x hxη
  · dsimp [s', s]
    linarith

private theorem wedgePoint_neg (p dir : ℂ) (t ε : ℝ) :
    wedgePoint (-p) (-dir) t ε = -wedgePoint p dir t ε := by
  simp [wedgePoint]
  ring





theorem wedgeIn_graphRegion_west_upper_slope {a b : ℝ} {f g : ℝ → ℝ}
    (p dir : ℂ) (η s' : ℝ)
    (hd : dir.re < 0) (hpb : p.re ≤ b)
    (hη : 0 < η) (hηa : a ≤ p.re - η)
    (hg : ∀ x ∈ Icc (p.re - η) p.re,
      g x = p.im + (dir.im / dir.re) * (x - p.re))
    (hs : dir.im / dir.re < s')
    (hf : ∀ x ∈ Icc (p.re - η) p.re,
      f x ≤ p.im + s' * (x - p.re)) :
    WedgeIn p dir (graphRegion a b f g) := by
  let F : ℝ → ℝ := fun x => -g (-x)
  let G : ℝ → ℝ := fun x => -f (-x)
  have hd' : 0 < (-dir).re := by simpa using neg_pos.mpr hd
  have hpa' : -b ≤ (-p).re := by simp; linarith
  have hηa' : (-p).re + η ≤ -a := by simp; linarith
  have hratio : (-dir).im / (-dir).re = dir.im / dir.re := by
    simp [Complex.neg_re, Complex.neg_im]
  have hF : ∀ x ∈ Icc (-p).re ((-p).re + η),
      F x = (-p).im + ((-dir).im / (-dir).re) * (x - (-p).re) := by
    intro x hx
    have hy : -x ∈ Icc (p.re - η) p.re := by
      simp only [mem_Icc, Complex.neg_re] at hx ⊢
      constructor <;> linarith
    have hgy := hg (-x) hy
    change -g (-x) = _
    rw [hgy]
    rw [hratio]
    simp only [Complex.neg_re, Complex.neg_im]
    ring
  have hG : ∀ x ∈ Icc (-p).re ((-p).re + η),
      (-p).im + s' * (x - (-p).re) ≤ G x := by
    intro x hx
    have hy : -x ∈ Icc (p.re - η) p.re := by
      simp only [mem_Icc, Complex.neg_re] at hx ⊢
      constructor <;> linarith
    have hfx := hf (-x) hy
    change _ ≤ -f (-x)
    have heq : (-p).im + s' * (x - (-p).re) =
        -(p.im + s' * ((-x) - p.re)) := by
      simp only [Complex.neg_re, Complex.neg_im]
      ring
    rw [heq]
    exact neg_le_neg hfx
  have hηb' : (-p).re + η ≤ -a := hηa'
  have hwest := wedgeIn_graphRegion_east_lower_slope
    (-p) (-dir) η s' hd' hpa' hη hηb' hF (by rw [hratio]; exact hs) hG
  rcases hwest with ⟨δ, hδ, hmem⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htd hε hεδ
  let z := wedgePoint p dir t ε
  have hm := hmem t ε ht htd hε hεδ
  rw [wedgePoint_neg] at hm
  have hz : -b < -z.re ∧ -z.re < -a ∧ -g z.re < -z.im ∧
      -z.im < -f z.re := by
    simpa [graphRegion, F, G, z] using hm
  change a < z.re ∧ z.re < b ∧ f z.re < z.im ∧ z.im < g z.re
  rcases hz with ⟨hb, ha, hupper, hlower⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩




theorem wedgeIn_compl_closedGraphRegion_east_upper {a b : ℝ}
    {f g : ℝ → ℝ} (p dir : ℂ) (η : ℝ)
    (hd : 0 < dir.re) (hη : 0 < η)
    (hg : ∀ x ∈ Icc p.re (p.re + η),
      g x = p.im + (dir.im / dir.re) * (x - p.re)) :
    WedgeIn p dir (closedGraphRegion a b f g)ᶜ := by
  let s := dir.im / dir.re
  let fl : ℝ → ℝ := fun x => p.im + s * (x - p.re)
  let gu : ℝ → ℝ := fun x => p.im + (s + 1) * (x - p.re)
  have hinside := wedgeIn_graphRegion_east_lower_slope
    (a := p.re) (b := p.re + η) (f := fl) (g := gu)
    p dir η (s + 1) hd le_rfl hη le_rfl
    (by intro x hx; rfl) (by dsimp [s]; linarith)
    (by intro x hx; rfl)
  rcases hinside with ⟨δ, hδ, hmem⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htd hε hεδ
  let z := wedgePoint p dir t ε
  have hz := hmem t ε ht htd hε hεδ
  change p.re < z.re ∧ z.re < p.re + η ∧ fl z.re < z.im ∧
    z.im < gu z.re at hz
  have hzIcc : z.re ∈ Icc p.re (p.re + η) := by
    exact ⟨hz.1.le, hz.2.1.le⟩
  have htop := hg z.re hzIcc
  have hline : g z.re < z.im := by
    rw [htop]
    simpa [fl, s] using hz.2.2.1
  have hnot : z ∉ closedGraphRegion a b f g := by
    intro hclosed
    exact (not_le_of_gt hline) hclosed.2.2.2
  change z ∈ (closedGraphRegion a b f g)ᶜ
  exact hnot




theorem wedgeIn_compl_closedGraphRegion_east_right_endpoint {a b : ℝ}
    {f g : ℝ → ℝ} (p dir : ℂ) (hd : 0 < dir.re)
    (hp : p.re = b) :
    WedgeIn p dir (closedGraphRegion a b f g)ᶜ := by
  let d := dir.re
  let m := dir.im
  let δ := min 1 (d / (2 * (|m| + 1)))
  have hδ : 0 < δ := by dsimp [δ, d]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htd hε hεδ
  have hεd : ε < d / (2 * (|m| + 1)) :=
    lt_of_lt_of_le hεδ (by dsimp [δ]; exact min_le_right _ _)
  have hεm : ε * |m| < d := by
    have h := mul_lt_mul_of_pos_right hεd (by positivity)
    field_simp at h
    nlinarith [abs_nonneg m]
  have hq : 0 < d - ε * m := by
    have hm := mul_le_mul_of_nonneg_left (le_abs_self m) hε.le
    linarith
  have hx : (wedgePoint p dir t ε).re = p.re + t * (d - ε * m) := by
    rw [wedgePoint_re]
  have hxgt : b < (wedgePoint p dir t ε).re := by
    rw [hx, hp]
    exact lt_add_of_pos_right _ (mul_pos ht hq)
  have hnot : wedgePoint p dir t ε ∉ closedGraphRegion a b f g := by
    intro hclosed
    exact (not_le_of_gt hxgt) hclosed.2.1
  exact hnot




theorem wedgeIn_compl_closedGraphRegion_west_lower {a b : ℝ}
    {f g : ℝ → ℝ} (p dir : ℂ) (η : ℝ)
    (hd : dir.re < 0) (hη : 0 < η)
    (hf : ∀ x ∈ Icc (p.re - η) p.re,
      f x = p.im + (dir.im / dir.re) * (x - p.re)) :
    WedgeIn p dir (closedGraphRegion a b f g)ᶜ := by
  let F : ℝ → ℝ := fun x => -g (-x)
  let G : ℝ → ℝ := fun x => -f (-x)
  have hd' : 0 < (-dir).re := by simpa using neg_pos.mpr hd
  have hratio : (-dir).im / (-dir).re = dir.im / dir.re := by
    simp [Complex.neg_re, Complex.neg_im]
  have hG : ∀ x ∈ Icc (-p).re ((-p).re + η),
      G x = (-p).im + ((-dir).im / (-dir).re) * (x - (-p).re) := by
    intro x hx
    have hy : -x ∈ Icc (p.re - η) p.re := by
      simp only [mem_Icc, Complex.neg_re] at hx ⊢
      constructor <;> linarith
    have hfx := hf (-x) hy
    change -f (-x) = _
    rw [hfx, hratio]
    simp only [Complex.neg_re, Complex.neg_im]
    ring
  have hwest := wedgeIn_compl_closedGraphRegion_east_upper
    (a := -b) (b := -a) (f := F) (g := G) (-p) (-dir) η hd' hη hG
  rcases hwest with ⟨δ, hδ, hmem⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htd hε hεδ
  let z := wedgePoint p dir t ε
  have hnot := hmem t ε ht htd hε hεδ
  rw [wedgePoint_neg] at hnot
  have hnot' : -z ∉ closedGraphRegion (-b) (-a) F G := by
    simpa [z] using hnot
  have hz : z ∉ closedGraphRegion a b f g := by
    intro hz
    have hneg : -z ∈ closedGraphRegion (-b) (-a) F G := by
      simp only [closedGraphRegion, Set.mem_ofPred_eq]
      rcases hz with ⟨hleft, hright, hlow, hhigh⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [Complex.neg_re] using neg_le_neg hright
      · simpa only [Complex.neg_re] using neg_le_neg hleft
      · simpa [F, Complex.neg_re, Complex.neg_im] using neg_le_neg hhigh
      · simpa [G, Complex.neg_re, Complex.neg_im] using neg_le_neg hlow
    exact hnot' hneg
  exact hz




theorem wedgeIn_compl_closedGraphRegion_west_left_endpoint {a b : ℝ}
    {f g : ℝ → ℝ} (p dir : ℂ) (hd : dir.re < 0)
    (hp : p.re = a) :
    WedgeIn p dir (closedGraphRegion a b f g)ᶜ := by
  let d := -dir.re
  let m := dir.im
  let δ := min 1 (d / (2 * (|m| + 1)))
  have hd' : 0 < d := by dsimp [d]; linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htd hε hεδ
  have hεd : ε < d / (2 * (|m| + 1)) :=
    lt_of_lt_of_le hεδ (by dsimp [δ]; exact min_le_right _ _)
  have hεm : ε * |m| < d := by
    have hfactor : 0 < 2 * (|m| + 1) := by positivity
    have h := mul_lt_mul_of_pos_right hεd hfactor
    field_simp at h
    nlinarith [abs_nonneg m]
  have hqm : -ε * m ≤ ε * |m| := by
    rw [neg_mul, ← mul_neg]
    exact mul_le_mul_of_nonneg_left (neg_le_abs m) hε.le
  have hq : dir.re - ε * m < 0 := by dsimp [d] at hd'; linarith
  have hx : (wedgePoint p dir t ε).re = p.re + t * (dir.re - ε * m) := by
    rw [wedgePoint_re]
  have hxlt : (wedgePoint p dir t ε).re < a := by
    rw [hx, hp]
    have hstep : t * (dir.re - ε * m) < 0 :=
      mul_neg_of_pos_of_neg ht hq
    linarith
  have hnot : wedgePoint p dir t ε ∉ closedGraphRegion a b f g := by
    intro hclosed
    exact (not_le_of_gt hxlt) hclosed.1
  exact hnot

end DirectedDistances.PlanarMap
