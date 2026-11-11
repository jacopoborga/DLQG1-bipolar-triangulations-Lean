module

public import DirectedDistances.PlanarMap.GraphRegion
public import Mathlib.Topology.Closure
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Order.DenselyOrdered

public section
namespace DirectedDistances.PlanarMap

open Set
open scoped Topology

private theorem closedGraphRegion_subset_closure_graphRegion {a b : ℝ}
    {f g : ℝ → ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hgap : ∀ x ∈ Ioo a b, f x < g x)
    (hfa : f a = g a) (hfb : f b = g b) :
    closedGraphRegion a b f g ⊆ closure (graphRegion a b f g) := by
  let D : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo 0 1
  let E : Set (ℝ × ℝ) := Icc a b ×ˢ Icc 0 1
  let H : ℝ × ℝ → ℝ := fun p => f p.1 + p.2 * (g p.1 - f p.1)
  let F : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (H p : ℂ) * Complex.I
  have hDclosure : closure D = E := by
    change closure (Ioo a b ×ˢ Ioo 0 1) = Icc a b ×ˢ Icc 0 1
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_Ioo (by norm_num)]
  have hfc : ContinuousOn (fun p : ℝ × ℝ => f p.1) E := by
    exact hf.comp continuous_fst.continuousOn fun p hp => hp.1
  have hgc : ContinuousOn (fun p : ℝ × ℝ => g p.1) E := by
    exact hg.comp continuous_fst.continuousOn fun p hp => hp.1
  have hH : ContinuousOn H E := by
    dsimp [H]
    exact hfc.add (continuousOn_snd.mul (hgc.sub hfc))
  have hF : ContinuousOn F E := by
    dsimp [F]
    fun_prop
  have hDimage : F '' D ⊆ graphRegion a b f g := by
    rintro z ⟨⟨x, t⟩, ⟨hx, ht0, ht1⟩, rfl⟩
    have hd : 0 < g x - f x := sub_pos.mpr (hgap x hx)
    have hlo : f x < f x + t * (g x - f x) := by
      nlinarith [mul_pos ht0 hd]
    have hhi : f x + t * (g x - f x) < g x := by
      nlinarith [mul_lt_mul_of_pos_right ht1 hd]
    have hloPos : 0 < t * (g x - f x) := mul_pos ht0 hd
    simpa [graphRegion, F, H] using ⟨hx.1, hx.2, hloPos, hhi⟩
  have hclosedImage : closedGraphRegion a b f g ⊆ F '' E := by
    intro z hz
    rcases hz with ⟨hax, hxb, hlow, hhigh⟩
    by_cases hxa : z.re = a
    · have him : z.im = f a := by
        apply le_antisymm
        · calc z.im ≤ g z.re := hhigh
            _ = f a := by simp [hxa, hfa]
        · calc f a = f z.re := by simp [hxa]
            _ ≤ z.im := hlow
      refine ⟨(z.re, 0), ⟨⟨hax, hxb⟩, by norm_num⟩, ?_⟩
      apply Complex.ext
      · simp [F]
      · simp [F, H, hxa, hfa, him]
    · by_cases hxb' : z.re = b
      · have him : z.im = f b := by
          apply le_antisymm
          · calc z.im ≤ g z.re := hhigh
              _ = f b := by simp [hxb', hfb]
          · calc f b = f z.re := by simp [hxb']
              _ ≤ z.im := hlow
        refine ⟨(z.re, 0), ⟨⟨hax, hxb⟩, by norm_num⟩, ?_⟩
        apply Complex.ext
        · simp [F]
        · simp [F, H, hxb', hfb, him]
      · have hx : z.re ∈ Ioo a b := by
          constructor
          · rcases lt_or_eq_of_le hax with h | h
            · exact h
            · exact (hxa h.symm).elim
          · rcases lt_or_eq_of_le hxb with h | h
            · exact h
            · exact (hxb' h).elim
        have hd : 0 < g z.re - f z.re := sub_pos.mpr (hgap z.re hx)
        let t := (z.im - f z.re) / (g z.re - f z.re)
        have ht0 : 0 ≤ t := by
          dsimp [t]
          exact div_nonneg (sub_nonneg.mpr hlow) (le_of_lt hd)
        have ht1 : t ≤ 1 := by
          dsimp [t]
          rw [div_le_one hd]
          linarith
        have hval : f z.re + t * (g z.re - f z.re) = z.im := by
          dsimp [t]
          field_simp [ne_of_gt hd]
          ring
        refine ⟨(z.re, t), ⟨⟨hax, hxb⟩, ht0, ht1⟩, ?_⟩
        apply Complex.ext
        · simp [F]
        · simpa [F, H] using hval
  have hFcl : ContinuousOn F (closure D) := by
    rw [hDclosure]
    exact hF
  have hmem : ∀ p ∈ E, F p ∈ closure (graphRegion a b f g) := by
    intro p hp
    have hpcl : p ∈ closure D := by rw [hDclosure]; exact hp
    have hmap : F p ∈ closure (F '' D) := hFcl.image_closure ⟨p, hpcl, rfl⟩
    exact closure_mono hDimage hmap
  intro z hz
  rcases hclosedImage hz with ⟨p, hp, rfl⟩
  exact hmem p hp



theorem closure_graphRegion_eq_closedGraphRegion {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hgap : ∀ x ∈ Ioo a b, f x < g x)
    (hfa : f a = g a) (hfb : f b = g b) :
    closure (graphRegion a b f g) = closedGraphRegion a b f g := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun z hz =>
      ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩)
      (isClosed_closedGraphRegion hf hg)
  · exact closedGraphRegion_subset_closure_graphRegion hab hf hg hgap hfa hfb



theorem graphRegion_subset_interior_closedGraphRegion {a b : ℝ}
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) :
    graphRegion a b f g ⊆ interior (closedGraphRegion a b f g) := by
  apply interior_maximal
  · intro z hz
    exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  · exact isOpen_graphRegion hf hg



theorem mem_graphRegion_of_mem_closedGraphRegion_of_not_mem_graphOver
    {a b : ℝ} {f g : ℝ → ℝ} {z : ℂ}
    (hz : z ∈ closedGraphRegion a b f g) (hx : z.re ∈ Ioo a b)
    (hlow : z ∉ graphOver a b f) (hhigh : z ∉ graphOver a b g) :
    z ∈ graphRegion a b f g := by
  rcases hz with ⟨hax, hxb, hlo, hhi⟩
  have hlo' : f z.re < z.im := by
    rcases eq_or_lt_of_le hlo with h | h
    · exact (hlow ⟨hax, hxb, h.symm⟩).elim
    · exact h
  have hhi' : z.im < g z.re := by
    rcases eq_or_lt_of_le hhi with h | h
    · exact (hhigh ⟨hax, hxb, h⟩).elim
    · exact h
  exact ⟨hx.1, hx.2, hlo', hhi'⟩



theorem frontier_graphRegion_eq {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hgap : ∀ x ∈ Ioo a b, f x < g x)
    (hfa : f a = g a) (hfb : f b = g b) :
    frontier (graphRegion a b f g) =
      graphOver a b f ∪ graphOver a b g := by
  have hfg : ∀ x ∈ Icc a b, f x ≤ g x := by
    intro x hx
    rcases lt_or_eq_of_le hx.1 with hax | hax
    · rcases lt_or_eq_of_le hx.2 with hxb | hxb
      · exact (hgap x ⟨hax, hxb⟩).le
      · rw [hxb, hfb]
    · rw [← hax, hfa]
  apply Set.Subset.antisymm
  · exact frontier_graphRegion_subset_of_endpoint_eq hf hg hfa hfb
  · intro z hz
    rcases hz with hlow | hhigh
    · have hcl : z ∈ closure (graphRegion a b f g) := by
        rw [closure_graphRegion_eq_closedGraphRegion hab hf hg hgap hfa hfb]
        refine ⟨hlow.1, hlow.2.1, le_of_eq hlow.2.2.symm, ?_⟩
        calc
          z.im = f z.re := hlow.2.2
          _ ≤ g z.re := hfg z.re ⟨hlow.1, hlow.2.1⟩
      have hnot : z ∉ graphRegion a b f g := by
        rintro ⟨_, _, hlo, _⟩
        exact (not_lt_of_ge (le_of_eq hlow.2.2)) hlo
      rw [frontier, (isOpen_graphRegion hf hg).interior_eq]
      exact ⟨hcl, hnot⟩
    · have hcl : z ∈ closure (graphRegion a b f g) := by
        rw [closure_graphRegion_eq_closedGraphRegion hab hf hg hgap hfa hfb]
        refine ⟨hhigh.1, hhigh.2.1, ?_, le_of_eq hhigh.2.2⟩
        calc
          f z.re ≤ g z.re := hfg z.re ⟨hhigh.1, hhigh.2.1⟩
          _ = z.im := hhigh.2.2.symm
      have hnot : z ∉ graphRegion a b f g := by
        rintro ⟨_, _, _, hhi⟩
        exact (not_lt_of_ge (le_of_eq hhigh.2.2.symm)) hhi
      rw [frontier, (isOpen_graphRegion hf hg).interior_eq]
      exact ⟨hcl, hnot⟩

end DirectedDistances.PlanarMap
