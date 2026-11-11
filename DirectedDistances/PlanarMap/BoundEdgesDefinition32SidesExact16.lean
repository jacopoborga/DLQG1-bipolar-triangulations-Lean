/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact14
import DirectedDistances.PlanarMap.D39PLSimpleArcInOpen3








public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval

/-- Helper toward Definition 3.2: two interior points on a `LeftAtOn` return
path can be joined by a simple polyline in the open connected face, while
retaining the return path's injectivity and winding-one accumulation data. -/
theorem exists_leftAtOn_interior_simple_polyline32 {x y : ℂ}
    (U : Set ℂ) (γ : Path x y) (s : {t : I // t ∈ openParams})
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hleft : LeftAtOn U γ s) :
    ∃ a b : I, ∃ (_ha : 0 < a) (_has : a < s.1) (_hsb : s.1 < b)
      (_hb : b < 1),
      ∃ q : Path (γ b) (γ a),
        Function.Injective q ∧
        (∀ t : I, t ∈ openParams → q t ∈ U) ∧
        γ s.1 ∈ closure
          {w : ℂ | w ∈ U ∧
            HasWinding
              ((edgeSubarc γ a b (le_of_lt (lt_trans _has _hsb))).trans q)
              w 1} ∧
        ∃ t₁ t₂ : I, t₁ ∈ openParams ∧ t₂ ∈ openParams ∧ t₁ ≠ t₂ ∧
          ∃ u v : ℂ, u = q t₁ ∧ v = q t₂ ∧ u ∈ U ∧ v ∈ U ∧ u ≠ v ∧
            ∃ r : Polyline,
              r.IsSimple ∧ r.start = u ∧ r.finish = v ∧ r.image ⊆ U := by
  rcases hleft with ⟨a, b, ha, has, hsb, hb, q, hqi, hq, hcl⟩
  let t₁ : I := ⟨(1 : ℝ) / 3, by norm_num⟩
  let t₂ : I := ⟨(2 : ℝ) / 3, by norm_num⟩
  have ht₁ : t₁ ∈ openParams := by
    change 0 < (t₁ : ℝ) ∧ (t₁ : ℝ) < 1
    norm_num [t₁]
  have ht₂ : t₂ ∈ openParams := by
    change 0 < (t₂ : ℝ) ∧ (t₂ : ℝ) < 1
    norm_num [t₂]
  have htne : t₁ ≠ t₂ := by
    norm_num [t₁, t₂]
  let u := q t₁
  let v := q t₂
  have hu : u ∈ U := hq t₁ ht₁
  have hv : v ∈ U := hq t₂ ht₂
  have huv : u ≠ v := by
    intro huv
    exact htne (hqi huv)
  obtain ⟨r, hrsimple, hrstart, hrfinish, hrimage⟩ :=
    exists_simple_polyline_in_open_connected hUopen hUconn hu hv huv
  refine ⟨a, b, ha, has, hsb, hb, q, hqi, hq, hcl, t₁, t₂, ht₁, ht₂,
    htne, u, v, rfl, rfl, hu, hv, huv, r, hrsimple, hrstart, hrfinish,
    hrimage⟩
























































































end DirectedDistances.PlanarMap

end
