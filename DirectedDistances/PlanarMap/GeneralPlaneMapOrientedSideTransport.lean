/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralPlaneMapOrientedEquiv
public import DirectedDistances.PlanarMap.GeneralPlaneMapSideReversal

/-! # Orientation-preserving side transport for general plane maps

The drawing equivalence records images of edges, rather than parameterized
paths. Parameter correspondence therefore requires a separate proof.
The open-arc correspondence extends across the endpoints, also for self-loops.
Winding-side transport then gives invariance of side multiplicity, side degree,
and `IsBipolarTriangulationBySides`. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace PlaneGraphDrawing

variable {V E V' E' : Type*}

/-- Helper toward Definition 1.1: an interior edge point has a unique
parameter, including when the edge is a self-loop. -/
theorem arc_eq_at_interior_iff (D : PlaneGraphDrawing V E) (a : E)
    (s t : I) (hs : s ∈ openParams) :
    D.arc a t = D.arc a s ↔ t = s := by
  constructor
  · intro h
    have ht0 : t ≠ 0 := by
      intro ht
      have hp : D.pos (D.src a) ∈ D.arc a '' openParams := by
        refine ⟨s, hs, ?_⟩
        simpa [ht] using h.symm
      exact D.openArc_avoids a (D.src a) hp
    have ht1 : t ≠ 1 := by
      intro ht
      have hp : D.pos (D.tgt a) ∈ D.arc a '' openParams := by
        refine ⟨s, hs, ?_⟩
        simpa [ht] using h.symm
      exact D.openArc_avoids a (D.tgt a) hp
    have ht : t ∈ openParams := by
      change 0 < (t : ℝ) ∧ (t : ℝ) < 1
      constructor
      · exact lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm))
      · exact lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))
    exact D.arc_injOn a ht hs h
  · rintro rfl
    rfl

/-- Helper toward Definition 1.1: the preimage of the geometric open arc
is precisely the open parameter interval, also for self-loops. -/
theorem preimage_openArc (D : PlaneGraphDrawing V E) (a : E) :
    D.arc a ⁻¹' D.openArc a = openParams := by
  ext t
  constructor
  · rintro ⟨s, hs, heq⟩
    exact (D.arc_eq_at_interior_iff a s t hs).mp heq.symm ▸ hs
  · intro ht
    exact ⟨t, ht, rfl⟩

/-- Helper toward Definition 1.1: the open parameter interval is
homeomorphic to the geometric open arc. Compactness of the full parameter
interval supplies continuity of the inverse without identifying loop endpoints. -/
@[expose] def openArcParamHomeomorph (D : PlaneGraphDrawing V E) (a : E) :
    openParams ≃ₜ D.openArc a := by
  let f := (D.openArc a).restrictPreimage (D.arc a)
  have hf : Function.Bijective f := by
    constructor
    · intro s t hst
      apply Subtype.ext
      have hs : s.val ∈ openParams := by
        rw [← D.preimage_openArc a]
        exact s.property
      exact (D.arc_eq_at_interior_iff a s.val t.val hs).mp
        (congrArg Subtype.val hst).symm |>.symm
    · intro z
      obtain ⟨t, ht, htz⟩ := z.property
      exact ⟨⟨t, show D.arc a t ∈ D.openArc a from htz.symm ▸ z.property⟩,
        Subtype.ext htz⟩
  have hclosed : IsClosedMap f := by
    intro t ht
    obtain ⟨u, hu, heq⟩ := isClosed_induced_iff.mp ht
    apply isClosed_induced_iff.mpr
    refine ⟨D.arc a '' u, (D.arc a).continuous.isClosedMap u hu, ?_⟩
    simp [f, ← heq, Set.image_restrictPreimage]
  exact (Homeomorph.setCongr (D.preimage_openArc a).symm).trans
    ((Equiv.ofBijective f hf).toHomeomorphOfContinuousClosed
      (D.arc a).continuous.restrictPreimage hclosed)

/-- Helper toward Definition 1.1: the open-arc parameter homeomorphism
evaluates to the stored edge path. -/
theorem openArcParamHomeomorph_apply (D : PlaneGraphDrawing V E) (a : E)
    (t : openParams) :
    (D.openArcParamHomeomorph a t).val = D.arc a t.val := rfl

/-- Helper toward Definition 1.1: a drawing equivalence induces a
homeomorphism between the interior parameter intervals of corresponding edges. -/
@[expose] def HomeoEquiv.openParamHomeomorph
    {D : PlaneGraphDrawing V E} {D' : PlaneGraphDrawing V' E'}
    (e : HomeoEquiv D D') (a : E) : openParams ≃ₜ openParams :=
  (D.openArcParamHomeomorph a).trans
    ((e.h.image (D.openArc a)).trans
      ((Homeomorph.setCongr (e.openArc_map a)).trans
        (D'.openArcParamHomeomorph (e.σE a)).symm))

/-- Helper toward Definition 1.1: the interior parameter correspondence
intertwines the plane homeomorphism and the two edge paths. -/
theorem HomeoEquiv.openParamHomeomorph_arc
    {D : PlaneGraphDrawing V E} {D' : PlaneGraphDrawing V' E'}
    (e : HomeoEquiv D D') (a : E) (t : openParams) :
    D'.arc (e.σE a) (e.openParamHomeomorph a t).val = e.h (D.arc a t.val) := by
  have h := (D'.openArcParamHomeomorph (e.σE a)).apply_symm_apply
    ((Homeomorph.setCongr (e.openArc_map a))
      ((e.h.image (D.openArc a)) (D.openArcParamHomeomorph a t)))
  exact congrArg Subtype.val h

/-- Helper toward Definition 1.1: an interior parameter homeomorphism is
either strictly increasing or strictly decreasing. -/
theorem openParamHomeomorph_strictMono_or_strictAnti
    (ψ : openParams ≃ₜ openParams) : StrictMono ψ ∨ StrictAnti ψ := by
  classical
  let f : I → I := fun t => if ht : t ∈ openParams then (ψ ⟨t, ht⟩).val else t
  have hf (t : openParams) : f t.val = (ψ t).val := by
    simp [f, t.property]
  have hc : ContinuousOn f (Set.Ioo (0 : I) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : openParams => f t.val)
    have heq : (fun t : openParams => f t.val) = Subtype.val ∘ ψ := funext hf
    rw [heq]
    exact continuous_subtype_val.comp ψ.continuous
  have hi : Set.InjOn f (Set.Ioo (0 : I) 1) := by
    intro x hx y hy hxy
    have h := ψ.injective (Subtype.ext (by
      exact (hf ⟨x, hx⟩).symm.trans (hxy.trans (hf ⟨y, hy⟩)) :
        (ψ ⟨x, hx⟩).val = (ψ ⟨y, hy⟩).val))
    exact congrArg Subtype.val h
  rcases hc.strictMonoOn_of_injOn_Ioo (by exact zero_lt_one) hi with hm | hm
  · left
    intro x y hxy
    have h := hm x.property y.property hxy
    change (ψ x).val < (ψ y).val
    rw [← hf x, ← hf y]
    exact h
  · right
    intro x y hxy
    have h := hm x.property y.property hxy
    change (ψ y).val < (ψ x).val
    rw [← hf y, ← hf x]
    exact h

/-- Helper toward Definition 1.1: an increasing homeomorphism of the open
parameter interval extends to an endpoint-fixing interval homeomorphism. -/
theorem exists_homeomorph_of_strictMono_openParams
    (ψ : openParams ≃ₜ openParams) (hm : StrictMono ψ) :
    ∃ φ : I ≃ₜ I, φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t : openParams, φ t.val = (ψ t).val := by
  classical
  let f : I → I := fun t => if ht : t ∈ openParams then (ψ ⟨t, ht⟩).val else t
  have hf (t : openParams) : f t.val = (ψ t).val := by
    simp [f, t.property]
  have hf0 : f 0 = 0 := by simp [f, openParams]
  have hf1 : f 1 = 1 := by simp [f, openParams]
  have hend (t : I) (ht : t ∉ openParams) : t = 0 ∨ t = 1 := by
    rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
    · exact (ht h).elim
  have hmono : StrictMono f := by
    intro x y hxy
    by_cases hx : x ∈ openParams
    · by_cases hy : y ∈ openParams
      · have h := hm (show (⟨x, hx⟩ : openParams) < ⟨y, hy⟩ from hxy)
        change (ψ ⟨x, hx⟩).val < (ψ ⟨y, hy⟩).val at h
        simpa only [f, dite_eq_left hx, dite_eq_left hy] using h
      · rcases hend y hy with rfl | rfl
        · exact (not_lt_of_ge (bot_le : (0 : I) ≤ x) hxy).elim
        · rw [hf1, hf ⟨x, hx⟩]
          exact (ψ ⟨x, hx⟩).property.2
    · rcases hend x hx with rfl | rfl
      · by_cases hy : y ∈ openParams
        · rw [hf0, hf ⟨y, hy⟩]
          exact (ψ ⟨y, hy⟩).property.1
        · rcases hend y hy with rfl | rfl
          · exact (lt_irrefl _ hxy).elim
          · rw [hf0, hf1]
            exact zero_lt_one
      · exact (not_lt_of_ge (le_top : y ≤ (1 : I)) hxy).elim
  have hsurj : Function.Surjective f := by
    intro y
    by_cases hy : y ∈ openParams
    · obtain ⟨x, hx⟩ := ψ.surjective ⟨y, hy⟩
      exact ⟨x.val, (hf x).trans (congrArg Subtype.val hx)⟩
    · rcases hend y hy with rfl | rfl
      · exact ⟨0, hf0⟩
      · exact ⟨1, hf1⟩
  exact ⟨(hmono.orderIsoOfSurjective f hsurj).toHomeomorph, hf0, hf1, hf⟩

/-- Helper toward Definition 1.1: every homeomorphism of the open
parameter interval extends to the closed interval, either fixing or swapping
the endpoints. -/
theorem exists_homeomorph_of_openParams (ψ : openParams ≃ₜ openParams) :
    ∃ φ : I ≃ₜ I,
      ((φ 0 = 0 ∧ φ 1 = 1) ∨ (φ 0 = 1 ∧ φ 1 = 0)) ∧
      ∀ t : openParams, φ t.val = (ψ t).val := by
  rcases openParamHomeomorph_strictMono_or_strictAnti ψ with hm | hm
  · obtain ⟨φ, h0, h1, hext⟩ := exists_homeomorph_of_strictMono_openParams ψ hm
    exact ⟨φ, Or.inl ⟨h0, h1⟩, hext⟩
  · let rev : openParams ≃ₜ openParams := unitInterval.symmHomeomorph.subtype
      (fun _ => symm_mem_openParams_iff.symm)
    let ψ' := ψ.trans rev
    have hm' : StrictMono ψ' := by
      intro x y hxy
      change σ (ψ x).val < σ (ψ y).val
      exact unitInterval.strictAnti_symm (hm hxy)
    obtain ⟨φ, h0, h1, hext⟩ := exists_homeomorph_of_strictMono_openParams ψ' hm'
    refine ⟨φ.trans unitInterval.symmHomeomorph, Or.inr ⟨?_, ?_⟩, ?_⟩
    · change σ (φ 0) = 1
      rw [h0, unitInterval.symm_zero]
    · change σ (φ 1) = 0
      rw [h1, unitInterval.symm_one]
    · intro t
      change σ (φ t.val) = (ψ t).val
      rw [hext t]
      exact unitInterval.symm_symm (ψ t).val

/-- Helper toward Definition 1.1: the open edge parameters are dense in
the full parameter interval. -/
theorem dense_openParams : Dense openParams := by
  intro t
  change t ∈ closure (Set.Ioo (0 : I) 1)
  rw [closure_Ioo (by exact zero_ne_one)]
  exact ⟨bot_le, le_top⟩

/-- Helper toward Definition 1.1: a drawing equivalence transports every
parameterized edge through an interval homeomorphism. It fixes or swaps the
endpoints and carries interior parameters to interior parameters. The proof
also covers self-loops, by extending the open-arc parameter correspondence. -/
theorem HomeoEquiv.exists_arc_reparam
    {D : PlaneGraphDrawing V E} {D' : PlaneGraphDrawing V' E'}
    (e : HomeoEquiv D D') (a : E) :
    ∃ φ : I ≃ₜ I,
      ((φ 0 = 0 ∧ φ 1 = 1) ∨ (φ 0 = 1 ∧ φ 1 = 0)) ∧
      (∀ t ∈ openParams, φ t ∈ openParams) ∧
      ∀ t : I, e.h (D.arc a t) = D'.arc (e.σE a) (φ t) := by
  let ψ := e.openParamHomeomorph a
  obtain ⟨φ, hends, hext⟩ := exists_homeomorph_of_openParams ψ
  refine ⟨φ, hends, ?_, ?_⟩
  · intro t ht
    rw [hext ⟨t, ht⟩]
    exact (ψ ⟨t, ht⟩).property
  · have heq : (fun t => e.h (D.arc a t)) =
        (fun t => D'.arc (e.σE a) (φ t)) := by
      apply Continuous.ext_on dense_openParams
        (e.h.continuous.comp (D.arc a).continuous)
        ((D'.arc (e.σE a)).continuous.comp φ.continuous)
      intro t ht
      change e.h (D.arc a t) = D'.arc (e.σE a) (φ t)
      rw [hext ⟨t, ht⟩]
      exact (e.openParamHomeomorph_arc a ⟨t, ht⟩).symm
    exact congrFun heq

end PlaneGraphDrawing

/-- Helper toward Definition 1.1: the winding lift excludes points on the
loop, since a complex exponential never vanishes. -/
theorem HasWinding.not_mem_range {z : ℂ} {L : Path z z} {w : ℂ} {n : ℤ}
    (hw : HasWinding L w n) : w ∉ Set.range L := by
  obtain ⟨φ, hφ, _⟩ := hw
  rintro ⟨t, ht⟩
  have hn := Complex.exp_ne_zero (φ t)
  rw [hφ t, ht, sub_self] at hn
  exact hn rfl

/-- Helper toward Definition 1.1: winding preservation also holds without
an explicit off-loop hypothesis; on-loop winding predicates are false. -/
theorem OrientationPreserving.hasWinding_map_iff {h : ℂ ≃ₜ ℂ}
    (hh : OrientationPreserving h) {z : ℂ} (L : Path z z) (w : ℂ) (n : ℤ) :
    HasWinding L w n ↔ HasWinding (L.map h.continuous) (h w) n := by
  by_cases hw : w ∉ Set.range L
  · exact hh L w hw n
  · have hwm : h w ∈ Set.range (L.map h.continuous) := by
      obtain ⟨t, ht⟩ := Classical.not_not.mp hw
      exact ⟨t, congrArg h ht⟩
    constructor
    · intro hn
      exact (hw hn.not_mem_range).elim
    · intro hn
      exact (hn.not_mem_range hwm).elim

/-- Helper toward Definition 1.1: mapping an edge subarc commutes with its
truncation, including the constant pauses in `edgeSubarc`. -/
theorem edgeSubarc_map {x y : ℂ} (γ : Path x y) (a b : I) (hab : a ≤ b)
    (h : ℂ ≃ₜ ℂ) :
    (edgeSubarc γ a b hab).map h.continuous =
      edgeSubarc (γ.map h.continuous) a b hab := by
  apply Path.ext
  funext t
  rfl

/- Exact unfolding of `LeftAtOn F γ s`:
∃ a b : I, ∃ (_ha : 0 < a) (_has : a < s.1) (_hsb : s.1 < b) (_hb : b < 1),
  ∃ q : Path (γ b) (γ a), Function.Injective q ∧
    (∀ t : I, t ∈ openParams → q t ∈ F) ∧
    γ s.1 ∈ closure {w : ℂ | w ∈ F ∧
      HasWinding ((edgeSubarc γ a b (le_of_lt (lt_trans _has _hsb))).trans q) w 1}.
`RightAtOn` has the identical binders and uses winding number `-1`. -/

/-- Helper toward Definition 1.1: a winding-side chord and its accumulating
points transport under a winding-preserving plane homeomorphism. -/
theorem chord_winding_closure_map {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (s a b : I) (hab : a ≤ b) (q : Path (γ b) (γ a)) (n : ℤ)
    (h : ℂ ≃ₜ ℂ) (hh : OrientationPreserving h)
    (hcl : γ s ∈ closure
      {w : ℂ | w ∈ F ∧ HasWinding ((edgeSubarc γ a b hab).trans q) w n}) :
    (γ.map h.continuous) s ∈ closure
      {w : ℂ | w ∈ h '' F ∧ HasWinding
        ((edgeSubarc (γ.map h.continuous) a b hab).trans (q.map h.continuous)) w n} := by
  have hloop : ∀ t, (((edgeSubarc γ a b hab).trans q).map h.continuous) t =
      ((edgeSubarc (γ.map h.continuous) a b hab).trans (q.map h.continuous)) t := by
    intro t
    rw [Path.map_trans]
    rfl
  have hsubset : h '' {w : ℂ | w ∈ F ∧
        HasWinding ((edgeSubarc γ a b hab).trans q) w n} ⊆
      {w : ℂ | w ∈ h '' F ∧ HasWinding
        ((edgeSubarc (γ.map h.continuous) a b hab).trans (q.map h.continuous)) w n} := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨⟨w, hw.1, rfl⟩, ?_⟩
    exact (hasWinding_congr_fun _ _ (h w) n hloop).mp
      ((hh.hasWinding_map_iff _ w n).mp hw.2)
  apply closure_mono hsubset
  rw [← h.image_closure]
  exact ⟨γ s, hcl, rfl⟩

/-- Helper toward Definition 1.1: the left winding-side test transports
forward with the plane homeomorphism at the same parameter. -/
theorem LeftAtOn.map {x y : ℂ} {F : Set ℂ} {γ : Path x y}
    {s : {t : I // t ∈ openParams}} (hs : LeftAtOn F γ s)
    (h : ℂ ≃ₜ ℂ) (hh : OrientationPreserving h) :
    LeftAtOn (h '' F) (γ.map h.continuous) s := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hq, hqF, hcl⟩ := hs
  refine ⟨a, b, ha, has, hsb, hb, q.map h.continuous, ?_, ?_, ?_⟩
  · intro u v huv
    exact hq (h.injective huv)
  · intro t ht
    exact ⟨q t, hqF t ht, rfl⟩
  · exact chord_winding_closure_map F γ s.val a b _ q 1 h hh hcl

/-- Helper toward Definition 1.1: the right winding-side test transports
forward with the plane homeomorphism at the same parameter. -/
theorem RightAtOn.map {x y : ℂ} {F : Set ℂ} {γ : Path x y}
    {s : {t : I // t ∈ openParams}} (hs : RightAtOn F γ s)
    (h : ℂ ≃ₜ ℂ) (hh : OrientationPreserving h) :
    RightAtOn (h '' F) (γ.map h.continuous) s := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hq, hqF, hcl⟩ := hs
  refine ⟨a, b, ha, has, hsb, hb, q.map h.continuous, ?_, ?_, ?_⟩
  · intro u v huv
    exact hq (h.injective huv)
  · intro t ht
    exact ⟨q t, hqF t ht, rfl⟩
  · exact chord_winding_closure_map F γ s.val a b _ q (-1) h hh hcl

/-- Helper toward Definition 1.1: the left test depends on the underlying
path function, including when its endpoints have different expressions. -/
theorem leftAtOn_congr_fun {x y x' y' : ℂ} (F : Set ℂ)
    (γ : Path x y) (γ' : Path x' y') (s : {t : I // t ∈ openParams})
    (heq : ∀ t, γ t = γ' t) : LeftAtOn F γ s ↔ LeftAtOn F γ' s := by
  have hx : x = x' := by simpa using heq 0
  have hy : y = y' := by simpa using heq 1
  subst x'
  subst y'
  have hp : γ = γ' := Path.ext (funext heq)
  rw [hp]

/-- Helper toward Definition 1.1: the right test depends on the underlying
path function, including when its endpoints have different expressions. -/
theorem rightAtOn_congr_fun {x y x' y' : ℂ} (F : Set ℂ)
    (γ : Path x y) (γ' : Path x' y') (s : {t : I // t ∈ openParams})
    (heq : ∀ t, γ t = γ' t) : RightAtOn F γ s ↔ RightAtOn F γ' s := by
  have hx : x = x' := by simpa using heq 0
  have hy : y = y' := by simpa using heq 1
  subst x'
  subst y'
  have hp : γ = γ' := Path.ext (funext heq)
  rw [hp]

/-- Helper toward Definition 1.1: an orientation-preserving plane
homeomorphism preserves the left winding-side test along the image path. -/
theorem leftAtOn_map_iff {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (s : {t : I // t ∈ openParams}) (h : ℂ ≃ₜ ℂ)
    (hh : OrientationPreserving h) :
    LeftAtOn F γ s ↔ LeftAtOn (h '' F) (γ.map h.continuous) s := by
  constructor
  · intro hs
    exact hs.map h hh
  · intro hs
    have hs' := hs.map h.symm hh.symm
    have hF : h.symm '' (h '' F) = F := by ext w; simp
    rw [hF] at hs'
    exact (leftAtOn_congr_fun F _ γ s (fun t => h.symm_apply_apply (γ t))).mp hs'

/-- Helper toward Definition 1.1: an orientation-preserving plane
homeomorphism preserves the right winding-side test along the image path. -/
theorem rightAtOn_map_iff {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (s : {t : I // t ∈ openParams}) (h : ℂ ≃ₜ ℂ)
    (hh : OrientationPreserving h) :
    RightAtOn F γ s ↔ RightAtOn (h '' F) (γ.map h.continuous) s := by
  constructor
  · intro hs
    exact hs.map h hh
  · intro hs
    have hs' := hs.map h.symm hh.symm
    have hF : h.symm '' (h '' F) = F := by ext w; simp
    rw [hF] at hs'
    exact (rightAtOn_congr_fun F _ γ s (fun t => h.symm_apply_apply (γ t))).mp hs'



theorem HasWinding.reparam {z : ℂ} {L : Path z z} {w : ℂ} {n : ℤ}
    (hw : HasWinding L w n) (f : I → I) (hc : Continuous f)
    (h0 : f 0 = 0) (h1 : f 1 = 1) :
    HasWinding (L.reparam f hc h0 h1) w n := by
  obtain ⟨φ, hφ, hinc⟩ := hw
  refine ⟨φ.comp ⟨f, hc⟩, ?_, ?_⟩
  · intro t
    exact hφ (f t)
  · change φ (f 1) - φ (f 0) = _
    rw [h0, h1]
    exact hinc

/-- Helper toward Definition 1.1: changing only the first path parameter
in a two-path loop preserves winding. -/
theorem HasWinding.trans_reparam_left {x y : ℂ} {α : Path x y} {β : Path y x}
    {w : ℂ} {n : ℤ} (hw : HasWinding (α.trans β) w n)
    (f : I → I) (hc : Continuous f) (h0 : f 0 = 0) (h1 : f 1 = 1) :
    HasWinding ((α.reparam f hc h0 h1).trans β) w n := by
  let half : I := ⟨(1 / 2 : ℝ), by norm_num⟩
  let low : Path (0 : I) half := {
    toFun := fun t => ⟨(f t : ℝ) / 2,
      by have hl := (f t).property.1; have hu := (f t).property.2
         constructor <;> linarith⟩
    continuous_toFun := by fun_prop
    source' := by apply Subtype.ext; simp [h0]
    target' := by apply Subtype.ext; simp [h1, half] }
  let high : Path half (1 : I) := {
    toFun := fun t => ⟨((t : ℝ) + 1) / 2,
      by have hl := t.property.1; have hu := t.property.2
         constructor <;> linarith⟩
    continuous_toFun := by fun_prop
    source' := by apply Subtype.ext; norm_num [half]
    target' := by apply Subtype.ext; norm_num }
  let χ := low.trans high
  have heq : ∀ t, (α.trans β) (χ t) =
      ((α.reparam f hc h0 h1).trans β) t := by
    intro t
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · let u : I := ⟨2 * (t : ℝ), by
        have hl := t.property.1; constructor <;> linarith⟩
      have hχ : χ t = low u := by
        change (if (t : ℝ) ≤ 1 / 2 then low.extend (2 * (t : ℝ))
          else high.extend (2 * (t : ℝ) - 1)) = low u
        rw [ite_eq_left ht]
        exact Path.extend_apply low u.property
      have hχle : (χ t : ℝ) ≤ 1 / 2 := by
        rw [hχ]
        change (f u : ℝ) / 2 ≤ 1 / 2
        have := (f u).property.2
        linarith
      change (if (χ t : ℝ) ≤ 1 / 2 then α.extend (2 * (χ t : ℝ))
        else β.extend (2 * (χ t : ℝ) - 1)) =
        (if (t : ℝ) ≤ 1 / 2 then (α.reparam f hc h0 h1).extend (2 * (t : ℝ))
          else β.extend (2 * (t : ℝ) - 1))
      rw [ite_eq_left hχle, ite_eq_left ht]
      rw [Path.extend_apply (α.reparam f hc h0 h1) u.property]
      change α.extend (2 * (χ t : ℝ)) = α (f u)
      have harg : 2 * (χ t : ℝ) = (f u : ℝ) := by
        rw [hχ]
        change 2 * ((f u : ℝ) / 2) = (f u : ℝ)
        ring
      rw [harg, Path.extend_extends']
    · have ht' : 1 / 2 ≤ (t : ℝ) := le_of_lt (lt_of_not_ge ht)
      let u : I := ⟨2 * (t : ℝ) - 1,
        by have hu := t.property.2; constructor <;> linarith⟩
      have hχ : χ t = t := by
        change (if (t : ℝ) ≤ 1 / 2 then low.extend (2 * (t : ℝ))
          else high.extend (2 * (t : ℝ) - 1)) = t
        rw [ite_eq_right ht, Path.extend_apply high u.property]
        apply Subtype.ext
        change ((2 * (t : ℝ) - 1) + 1) / 2 = (t : ℝ)
        ring
      rw [hχ]
      change (if (t : ℝ) ≤ 1 / 2 then α.extend (2 * (t : ℝ))
        else β.extend (2 * (t : ℝ) - 1)) =
        (if (t : ℝ) ≤ 1 / 2 then (α.reparam f hc h0 h1).extend (2 * (t : ℝ))
          else β.extend (2 * (t : ℝ) - 1))
      simp only [ite_eq_right ht]
  have hnew := hw.reparam χ χ.continuous χ.source χ.target
  exact (hasWinding_congr_fun _ _ w n heq).mp hnew

/-- Helper toward Definition 1.1: reparametrizing the first path of a
two-path loop by an endpoint-fixing homeomorphism preserves winding in both
directions. -/
theorem hasWinding_trans_reparam_left_iff {x y : ℂ} (α : Path x y) (β : Path y x)
    (w : ℂ) (n : ℤ) (φ : I ≃ₜ I) (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    HasWinding ((α.reparam φ φ.continuous h0 h1).trans β) w n ↔
      HasWinding (α.trans β) w n := by
  have hi0 : φ.symm 0 = 0 := by apply φ.injective; simp [h0]
  have hi1 : φ.symm 1 = 1 := by apply φ.injective; simp [h1]
  constructor
  · intro hw
    have hnew := hw.trans_reparam_left φ.symm φ.symm.continuous hi0 hi1
    have heq : (α.reparam φ φ.continuous h0 h1).reparam
        φ.symm φ.symm.continuous hi0 hi1 = α := by
      apply Path.ext
      funext t
      exact congrArg α (φ.apply_symm_apply t)
    rw [heq] at hnew
    exact hnew
  · intro hw
    exact hw.trans_reparam_left φ φ.continuous h0 h1

/-- Helper toward Definition 1.1: an edge subarc evaluates by clamping its
parameter between its two chosen endpoints. -/
theorem edgeSubarc_apply_clamp {x y : ℂ} (γ : Path x y) (a b : I)
    (hab : a ≤ b) (t : I) :
    edgeSubarc γ a b hab t = γ (min (max t a) b) := by
  change γ.extend (min (max (t : ℝ) (a : ℝ)) (b : ℝ)) = _
  exact γ.extend_extends' (min (max t a) b)

/-- Helper toward Definition 1.1: an increasing change of parameter
commutes with the paused edge subarc, with its endpoints transported. -/
theorem edgeSubarc_reparam {x y : ℂ} (γ : Path x y) (φ : I ≃ₜ I)
    (h0 : φ 0 = 0) (h1 : φ 1 = 1) (hm : StrictMono φ)
    (a b : I) (hab : a ≤ b) :
    edgeSubarc (γ.reparam φ φ.continuous h0 h1) a b hab =
      (edgeSubarc γ (φ a) (φ b) (hm.monotone hab)).reparam
        φ φ.continuous h0 h1 := by
  apply Path.ext
  funext t
  rw [edgeSubarc_apply_clamp]
  change γ (φ (min (max t a) b)) =
    edgeSubarc γ (φ a) (φ b) (hm.monotone hab) (φ t)
  rw [edgeSubarc_apply_clamp, hm.monotone.map_min, hm.monotone.map_max]

/-- Helper toward Definition 1.1: the chord loop used by a side test has
the same winding after an increasing parameter change, including its pauses. -/
theorem chord_winding_reparam_iff {x y : ℂ} (γ : Path x y) (φ : I ≃ₜ I)
    (h0 : φ 0 = 0) (h1 : φ 1 = 1) (hm : StrictMono φ)
    (a b : I) (hab : a ≤ b) (q : Path (γ (φ b)) (γ (φ a)))
    (w : ℂ) (n : ℤ) :
    HasWinding ((edgeSubarc (γ.reparam φ φ.continuous h0 h1) a b hab).trans q) w n ↔
      HasWinding ((edgeSubarc γ (φ a) (φ b) (hm.monotone hab)).trans q) w n := by
  have heq := edgeSubarc_reparam γ φ h0 h1 hm a b hab
  have hfun : ∀ t,
      ((edgeSubarc (γ.reparam φ φ.continuous h0 h1) a b hab).trans q) t =
      (((edgeSubarc γ (φ a) (φ b) (hm.monotone hab)).reparam
        φ φ.continuous h0 h1).trans q) t := by
    intro t
    exact congrArg (fun p : Path (γ (φ a)) (γ (φ b)) => (p.trans q) t) heq
  exact (hasWinding_congr_fun _ _ w n hfun).trans
    (hasWinding_trans_reparam_left_iff _ q w n φ h0 h1)

/-- Helper toward Definition 1.1: an increasing reparametrization carries
a left-side witness to its image parameter. -/
theorem LeftAtOn.reparam_forward {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (φ : I ≃ₜ I) (h0 : φ 0 = 0) (h1 : φ 1 = 1) (hm : StrictMono φ)
    (s s' : {t : I // t ∈ openParams}) (hs' : φ s.val = s'.val)
    (hs : LeftAtOn F (γ.reparam φ φ.continuous h0 h1) s) :
    LeftAtOn F γ s' := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hq, hqF, hcl⟩ := hs
  have ha' : 0 < φ a := by rw [← h0]; exact hm ha
  have hb' : φ b < 1 := by rw [← h1]; exact hm hb
  refine ⟨φ a, φ b, ha', ?_, ?_, hb', q, hq, hqF, ?_⟩
  · rw [← hs']; exact hm has
  · rw [← hs']; exact hm hsb
  · have hsubset : {w : ℂ | w ∈ F ∧ HasWinding
        ((edgeSubarc (γ.reparam φ φ.continuous h0 h1) a b
          (le_of_lt (lt_trans has hsb))).trans q) w 1} ⊆
      {w : ℂ | w ∈ F ∧ HasWinding
        ((edgeSubarc γ (φ a) (φ b) (hm.monotone (le_of_lt (lt_trans has hsb)))).trans q) w 1} := by
      intro w hw
      exact ⟨hw.1, (chord_winding_reparam_iff γ φ h0 h1 hm a b _ q w 1).mp hw.2⟩
    have hnew := closure_mono hsubset hcl
    change γ (φ s.val) ∈ _ at hnew
    rw [hs'] at hnew
    exact hnew

/-- Helper toward Definition 1.1: an increasing reparametrization carries
a right-side witness to its image parameter. -/
theorem RightAtOn.reparam_forward {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (φ : I ≃ₜ I) (h0 : φ 0 = 0) (h1 : φ 1 = 1) (hm : StrictMono φ)
    (s s' : {t : I // t ∈ openParams}) (hs' : φ s.val = s'.val)
    (hs : RightAtOn F (γ.reparam φ φ.continuous h0 h1) s) :
    RightAtOn F γ s' := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hq, hqF, hcl⟩ := hs
  have ha' : 0 < φ a := by rw [← h0]; exact hm ha
  have hb' : φ b < 1 := by rw [← h1]; exact hm hb
  refine ⟨φ a, φ b, ha', ?_, ?_, hb', q, hq, hqF, ?_⟩
  · rw [← hs']; exact hm has
  · rw [← hs']; exact hm hsb
  · have hsubset : {w : ℂ | w ∈ F ∧ HasWinding
        ((edgeSubarc (γ.reparam φ φ.continuous h0 h1) a b
          (le_of_lt (lt_trans has hsb))).trans q) w (-1)} ⊆
      {w : ℂ | w ∈ F ∧ HasWinding
        ((edgeSubarc γ (φ a) (φ b) (hm.monotone (le_of_lt (lt_trans has hsb)))).trans q) w (-1)} := by
      intro w hw
      exact ⟨hw.1, (chord_winding_reparam_iff γ φ h0 h1 hm a b _ q w (-1)).mp hw.2⟩
    have hnew := closure_mono hsubset hcl
    change γ (φ s.val) ∈ _ at hnew
    rw [hs'] at hnew
    exact hnew

/-- Helper toward Definition 1.1: an endpoint-fixing interval
homeomorphism preserves the left test at the corresponding parameter. -/
theorem leftAtOn_reparam_iff {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (φ : I ≃ₜ I) (h0 : φ 0 = 0) (h1 : φ 1 = 1)
    (s s' : {t : I // t ∈ openParams}) (hs' : φ s.val = s'.val) :
    LeftAtOn F (γ.reparam φ φ.continuous h0 h1) s ↔ LeftAtOn F γ s' := by
  have hm : StrictMono φ := φ.continuous.strictMono_of_inj_boundedOrder
    (by change φ 0 ≤ φ 1; rw [h0, h1]; exact zero_le_one) φ.injective
  have hi0 : φ.symm 0 = 0 := by apply φ.injective; simp [h0]
  have hi1 : φ.symm 1 = 1 := by apply φ.injective; simp [h1]
  have hmi : StrictMono φ.symm := φ.symm.continuous.strictMono_of_inj_boundedOrder
    (by change φ.symm 0 ≤ φ.symm 1; rw [hi0, hi1]; exact zero_le_one) φ.symm.injective
  constructor
  · exact LeftAtOn.reparam_forward F γ φ h0 h1 hm s s' hs'
  · intro hs
    let δ := γ.reparam φ φ.continuous h0 h1
    have hd : ∀ t, (δ.reparam φ.symm φ.symm.continuous hi0 hi1) t = γ t :=
      fun t => congrArg γ (φ.apply_symm_apply t)
    have hs0 := (leftAtOn_congr_fun F _ γ s' hd).mpr hs
    exact LeftAtOn.reparam_forward F δ φ.symm hi0 hi1 hmi s' s
      (by rw [← hs']; exact φ.symm_apply_apply s.val) hs0

/-- Helper toward Definition 1.1: an endpoint-fixing interval
homeomorphism preserves the right test at the corresponding parameter. -/
theorem rightAtOn_reparam_iff {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (φ : I ≃ₜ I) (h0 : φ 0 = 0) (h1 : φ 1 = 1)
    (s s' : {t : I // t ∈ openParams}) (hs' : φ s.val = s'.val) :
    RightAtOn F (γ.reparam φ φ.continuous h0 h1) s ↔ RightAtOn F γ s' := by
  have hm : StrictMono φ := φ.continuous.strictMono_of_inj_boundedOrder
    (by change φ 0 ≤ φ 1; rw [h0, h1]; exact zero_le_one) φ.injective
  have hi0 : φ.symm 0 = 0 := by apply φ.injective; simp [h0]
  have hi1 : φ.symm 1 = 1 := by apply φ.injective; simp [h1]
  have hmi : StrictMono φ.symm := φ.symm.continuous.strictMono_of_inj_boundedOrder
    (by change φ.symm 0 ≤ φ.symm 1; rw [hi0, hi1]; exact zero_le_one) φ.symm.injective
  constructor
  · exact RightAtOn.reparam_forward F γ φ h0 h1 hm s s' hs'
  · intro hs
    let δ := γ.reparam φ φ.continuous h0 h1
    have hd : ∀ t, (δ.reparam φ.symm φ.symm.continuous hi0 hi1) t = γ t :=
      fun t => congrArg γ (φ.apply_symm_apply t)
    have hs0 := (rightAtOn_congr_fun F _ γ s' hd).mpr hs
    exact RightAtOn.reparam_forward F δ φ.symm hi0 hi1 hmi s' s
      (by rw [← hs']; exact φ.symm_apply_apply s.val) hs0

/-- Helper toward Definition 1.1: a decreasing interval change of
parameter factors as an increasing change followed by reversal, and swaps
the left test with the right test at its image parameter. -/
theorem leftAtOn_decreasing_reparam_iff {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (φ : I ≃ₜ I) (h0 : φ 0 = 1) (h1 : φ 1 = 0)
    (s s' : {t : I // t ∈ openParams}) (hs' : φ s.val = s'.val) :
    LeftAtOn F
      (γ.symm.reparam (φ.trans unitInterval.symmHomeomorph)
        (unitInterval.continuous_symm.comp φ.continuous)
        (by change σ (φ 0) = 0; rw [h0, unitInterval.symm_one])
        (by change σ (φ 1) = 1; rw [h1, unitInterval.symm_zero])) s ↔
      RightAtOn F γ s' := by
  let ψ := φ.trans unitInterval.symmHomeomorph
  have hp0 : ψ 0 = 0 := by change σ (φ 0) = 0; rw [h0, unitInterval.symm_one]
  have hp1 : ψ 1 = 1 := by change σ (φ 1) = 1; rw [h1, unitInterval.symm_zero]
  let sr : {t : I // t ∈ openParams} :=
    ⟨σ s'.val, symm_mem_openParams_iff.mpr s'.property⟩
  have hps : ψ s.val = sr.val := congrArg σ hs'
  have hr : LeftAtOn F γ.symm sr ↔ RightAtOn F γ s' := by
    have hc : (sr.val : ℝ) + (s'.val : ℝ) = 1 := by
      change (σ s'.val : ℝ) + (s'.val : ℝ) = 1
      rw [unitInterval.coe_symm_eq]; ring
    exact ⟨leftAtOn_symm_to_rightAtOn F γ s' sr hc,
      rightAtOn_to_leftAtOn_symm F γ s' sr hc⟩
  exact (leftAtOn_reparam_iff F γ.symm ψ hp0 hp1 s sr hps).trans hr

/-- Helper toward Definition 1.1: a decreasing change of parameter swaps
the right test with the left test at its image parameter. -/
theorem rightAtOn_decreasing_reparam_iff {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (φ : I ≃ₜ I) (h0 : φ 0 = 1) (h1 : φ 1 = 0)
    (s s' : {t : I // t ∈ openParams}) (hs' : φ s.val = s'.val) :
    RightAtOn F
      (γ.symm.reparam (φ.trans unitInterval.symmHomeomorph)
        (unitInterval.continuous_symm.comp φ.continuous)
        (by change σ (φ 0) = 0; rw [h0, unitInterval.symm_one])
        (by change σ (φ 1) = 1; rw [h1, unitInterval.symm_zero])) s ↔
      LeftAtOn F γ s' := by
  let ψ := φ.trans unitInterval.symmHomeomorph
  have hp0 : ψ 0 = 0 := by change σ (φ 0) = 0; rw [h0, unitInterval.symm_one]
  have hp1 : ψ 1 = 1 := by change σ (φ 1) = 1; rw [h1, unitInterval.symm_zero]
  let sr : {t : I // t ∈ openParams} :=
    ⟨σ s'.val, symm_mem_openParams_iff.mpr s'.property⟩
  have hps : ψ s.val = sr.val := congrArg σ hs'
  have hc : (s'.val : ℝ) + (sr.val : ℝ) = 1 := by
    change (s'.val : ℝ) + (σ s'.val : ℝ) = 1
    rw [unitInterval.coe_symm_eq]; ring
  have hr : RightAtOn F γ.symm sr ↔ LeftAtOn F γ s' := by
    constructor
    · intro hs
      simpa only [Path.symm_symm] using
        rightAtOn_to_leftAtOn_symm F γ.symm sr s' hc hs
    · intro hs
      apply leftAtOn_symm_to_rightAtOn F γ.symm sr s' hc
      simpa only [Path.symm_symm] using hs
  exact (rightAtOn_reparam_iff F γ.symm ψ hp0 hp1 s sr hps).trans hr

/-- Helper toward Definition 1.1: a homeomorphism fixing the interval
endpoints preserves the open parameter interval in both directions. -/
theorem mem_openParams_homeomorph_iff (φ : I ≃ₜ I)
    (h0 : φ 0 = 0) (h1 : φ 1 = 1) (t : I) :
    φ t ∈ openParams ↔ t ∈ openParams := by
  have hm : StrictMono φ := φ.continuous.strictMono_of_inj_boundedOrder
    (by change φ 0 ≤ φ 1; rw [h0, h1]; exact zero_le_one) φ.injective
  change (0 < (φ t : ℝ) ∧ (φ t : ℝ) < 1) ↔
    (0 < (t : ℝ) ∧ (t : ℝ) < 1)
  change ((0 : I) < φ t ∧ φ t < 1) ↔ ((0 : I) < t ∧ t < 1)
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨hm.lt_iff_lt.mp (by simpa only [h0] using ha),
      hm.lt_iff_lt.mp (by simpa only [h1] using hb)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨by simpa only [h0] using hm ha, by simpa only [h1] using hm hb⟩

/-- Helper toward Definition 1.1: simultaneous left-side tests at every
interior point are unchanged by an endpoint-fixing reparametrization. -/
theorem forall_leftAtOn_reparam_iff {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (φ : I ≃ₜ I) (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    (∀ s : {t : I // t ∈ openParams},
      LeftAtOn F (γ.reparam φ φ.continuous h0 h1) s) ↔
      ∀ s : {t : I // t ∈ openParams}, LeftAtOn F γ s := by
  constructor
  · intro hs t
    let s : {t : I // t ∈ openParams} := ⟨φ.symm t.val,
      (mem_openParams_homeomorph_iff φ h0 h1 _).mp
        (by rw [φ.apply_symm_apply]; exact t.property)⟩
    exact (leftAtOn_reparam_iff F γ φ h0 h1 s t (φ.apply_symm_apply _)).mp (hs s)
  · intro hs s
    let t : {t : I // t ∈ openParams} :=
      ⟨φ s.val, (mem_openParams_homeomorph_iff φ h0 h1 _).mpr s.property⟩
    exact (leftAtOn_reparam_iff F γ φ h0 h1 s t rfl).mpr (hs t)

/-- Helper toward Definition 1.1: simultaneous right-side tests at every
interior point are unchanged by an endpoint-fixing reparametrization. -/
theorem forall_rightAtOn_reparam_iff {x y : ℂ} (F : Set ℂ) (γ : Path x y)
    (φ : I ≃ₜ I) (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    (∀ s : {t : I // t ∈ openParams},
      RightAtOn F (γ.reparam φ φ.continuous h0 h1) s) ↔
      ∀ s : {t : I // t ∈ openParams}, RightAtOn F γ s := by
  constructor
  · intro hs t
    let s : {t : I // t ∈ openParams} := ⟨φ.symm t.val,
      (mem_openParams_homeomorph_iff φ h0 h1 _).mp
        (by rw [φ.apply_symm_apply]; exact t.property)⟩
    exact (rightAtOn_reparam_iff F γ φ h0 h1 s t (φ.apply_symm_apply _)).mp (hs s)
  · intro hs s
    let t : {t : I // t ∈ openParams} :=
      ⟨φ s.val, (mem_openParams_homeomorph_iff φ h0 h1 _).mpr s.property⟩
    exact (rightAtOn_reparam_iff F γ φ h0 h1 s t rfl).mpr (hs t)

/-- Helper toward Definition 1.1: reversing a path interchanges the
simultaneous left and right side tests over all interior parameters. -/
theorem forall_leftAtOn_symm_iff {x y : ℂ} (F : Set ℂ) (γ : Path x y) :
    (∀ s : {t : I // t ∈ openParams}, LeftAtOn F γ.symm s) ↔
      ∀ s : {t : I // t ∈ openParams}, RightAtOn F γ s := by
  constructor
  · intro hs s
    let sr : {t : I // t ∈ openParams} :=
      ⟨σ s.val, symm_mem_openParams_iff.mpr s.property⟩
    apply leftAtOn_symm_to_rightAtOn F γ s sr _ (hs sr)
    change (σ s.val : ℝ) + (s.val : ℝ) = 1
    rw [unitInterval.coe_symm_eq]; ring
  · intro hs sr
    let s : {t : I // t ∈ openParams} :=
      ⟨σ sr.val, symm_mem_openParams_iff.mpr sr.property⟩
    apply rightAtOn_to_leftAtOn_symm F γ s sr _ (hs s)
    change (sr.val : ℝ) + (σ sr.val : ℝ) = 1
    rw [unitInterval.coe_symm_eq]; ring

/-- Helper toward Definition 1.1: the right-to-left simultaneous reversal
law follows by applying the left-to-right law to the reversed path. -/
theorem forall_rightAtOn_symm_iff {x y : ℂ} (F : Set ℂ) (γ : Path x y) :
    (∀ s : {t : I // t ∈ openParams}, RightAtOn F γ.symm s) ↔
      ∀ s : {t : I // t ∈ openParams}, LeftAtOn F γ s := by
  simpa only [Path.symm_symm] using (forall_leftAtOn_symm_iff F γ.symm).symm

namespace PlaneGraphDrawing.HomeoEquiv

variable {V E V' E' : Type*}
variable {D : PlaneGraphDrawing V E} {D' : PlaneGraphDrawing V' E'}

/-- Helper toward Definition 1.1: the two edge sides transport together.
The witnessing interval homeomorphism fixes the endpoints and preserves both
sides, or swaps the endpoints and swaps the sides. -/
theorem exists_arc_reparam_sides (e : HomeoEquiv D D')
    (hh : OrientationPreserving e.h) (F : D.Face) (a : E) :
    ∃ φ : I ≃ₜ I,
      (∀ t : I, e.h (D.arc a t) = D'.arc (e.σE a) (φ t)) ∧
      ((φ 0 = 0 ∧ φ 1 = 1 ∧
          (D'.SideLeftOf (e.faceMap F) (e.σE a) ↔ D.SideLeftOf F a) ∧
          (D'.SideRightOf (e.faceMap F) (e.σE a) ↔ D.SideRightOf F a)) ∨
        (φ 0 = 1 ∧ φ 1 = 0 ∧
          (D'.SideLeftOf (e.faceMap F) (e.σE a) ↔ D.SideRightOf F a) ∧
          (D'.SideRightOf (e.faceMap F) (e.σE a) ↔ D.SideLeftOf F a))) := by
  obtain ⟨φ, hends, _, hp⟩ := e.exists_arc_reparam a
  refine ⟨φ, hp, ?_⟩
  rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hl : D.SideLeftOf F a ↔ D'.SideLeftOf (e.faceMap F) (e.σE a) := by
      change (∀ s, LeftAtOn F.val (D.arc a) s) ↔
        ∀ s, LeftAtOn (e.h '' F.val) (D'.arc (e.σE a)) s
      refine Iff.trans ?_ (forall_leftAtOn_reparam_iff _ _ φ h0 h1)
      apply forall_congr'
      intro s
      exact (leftAtOn_map_iff _ _ s e.h hh).trans
        (leftAtOn_congr_fun _ _ _ s hp)
    have hr : D.SideRightOf F a ↔ D'.SideRightOf (e.faceMap F) (e.σE a) := by
      change (∀ s, RightAtOn F.val (D.arc a) s) ↔
        ∀ s, RightAtOn (e.h '' F.val) (D'.arc (e.σE a)) s
      refine Iff.trans ?_ (forall_rightAtOn_reparam_iff _ _ φ h0 h1)
      apply forall_congr'
      intro s
      exact (rightAtOn_map_iff _ _ s e.h hh).trans
        (rightAtOn_congr_fun _ _ _ s hp)
    exact Or.inl ⟨h0, h1, hl.symm, hr.symm⟩
  · let ψ := φ.trans unitInterval.symmHomeomorph
    have hp0 : ψ 0 = 0 := by change σ (φ 0) = 0; rw [h0, unitInterval.symm_one]
    have hp1 : ψ 1 = 1 := by change σ (φ 1) = 1; rw [h1, unitInterval.symm_zero]
    let δ := (D'.arc (e.σE a)).symm.reparam ψ ψ.continuous hp0 hp1
    have hδ : ∀ t, ((D.arc a).map e.h.continuous) t = δ t := by
      intro t
      change e.h (D.arc a t) = D'.arc (e.σE a) (σ (σ (φ t)))
      rw [unitInterval.symm_symm]
      exact hp t
    have hl : D.SideLeftOf F a ↔ D'.SideRightOf (e.faceMap F) (e.σE a) := by
      change (∀ s, LeftAtOn F.val (D.arc a) s) ↔
        ∀ s, RightAtOn (e.h '' F.val) (D'.arc (e.σE a)) s
      refine Iff.trans ?_ ((forall_leftAtOn_reparam_iff _ _ ψ hp0 hp1).trans
        (forall_leftAtOn_symm_iff _ _))
      apply forall_congr'
      intro s
      exact (leftAtOn_map_iff _ _ s e.h hh).trans
        (leftAtOn_congr_fun _ _ δ s hδ)
    have hr : D.SideRightOf F a ↔ D'.SideLeftOf (e.faceMap F) (e.σE a) := by
      change (∀ s, RightAtOn F.val (D.arc a) s) ↔
        ∀ s, LeftAtOn (e.h '' F.val) (D'.arc (e.σE a)) s
      refine Iff.trans ?_ ((forall_rightAtOn_reparam_iff _ _ ψ hp0 hp1).trans
        (forall_rightAtOn_symm_iff _ _))
      apply forall_congr'
      intro s
      exact (rightAtOn_map_iff _ _ s e.h hh).trans
        (rightAtOn_congr_fun _ _ δ s hδ)
    exact Or.inr ⟨h0, h1, hr.symm, hl.symm⟩

/-- Helper toward Definition 1.1: an orientation-preserving drawing
equivalence preserves the total multiplicity of the two sides of an edge,
including when a loop's parameter direction is reversed. -/
theorem sideMult_map (e : HomeoEquiv D D') (hh : OrientationPreserving e.h)
    (a : E) (F : D.Face) :
    D.sideMult a F = D'.sideMult (e.σE a) (e.faceMap F) := by
  classical
  obtain ⟨_, _, hsides⟩ := e.exists_arc_reparam_sides hh F a
  unfold PlaneGraphDrawing.sideMult
  rcases hsides with ⟨_, _, hl, hr⟩ | ⟨_, _, hl, hr⟩
  · simp only [hl, hr]
  · simp only [hl, hr]
    exact add_comm _ _

/-- Helper toward Definition 1.1: the side degree is invariant under an
orientation-preserving drawing equivalence, by reindexing all finite edge
sums through the edge bijection. -/
theorem sideDegree_map (e : HomeoEquiv D D') (hh : OrientationPreserving e.h)
    (F : D.Face) : D.sideDegree F = D'.sideDegree (e.faceMap F) := by
  classical
  unfold PlaneGraphDrawing.sideDegree
  apply (Equiv.finsetCongr e.σE).iSup_congr
  intro s
  rw [Equiv.finsetCongr_apply]
  symm
  apply Finset.sum_bij (fun x _ => e.σE x)
  · intro x hx
    exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
  · intro x hx y hy hxy
    exact e.σE.injective hxy
  · intro y hy
    rcases Finset.mem_map.mp hy with ⟨x, hx, hxy⟩
    exact ⟨x, hx, hxy⟩
  · intro x hx
    exact e.sideMult_map hh x F

end PlaneGraphDrawing.HomeoEquiv

/-- Helper toward Definition 1.1: bipolar triangulation defined by winding
sides is invariant under an orientation-preserving directed drawing
equivalence. This uses the proved side-degree transport for every face. -/
theorem DirectedPlaneMap.OrientedHomeoEquiv.isBipolarTriangulationBySides_iff
    {V E V' E' : Type*} {M : DirectedPlaneMap V E} {M' : DirectedPlaneMap V' E'}
    (e : DirectedPlaneMap.OrientedHomeoEquiv M M') :
    M.IsBipolarTriangulationBySides ↔ M'.IsBipolarTriangulationBySides := by
  let f := e.toHomeoEquiv
  unfold DirectedPlaneMap.IsBipolarTriangulationBySides
  constructor
  · rintro ⟨hb, htri⟩
    refine ⟨f.isBipolar_map_iff.mp hb, ?_⟩
    intro F' hInt
    let F := f.drawing.faceEquiv.symm F'
    have hFace : f.drawing.faceMap F = F' :=
      f.drawing.faceEquiv.apply_symm_apply F'
    have hIntMap : M'.toPlaneGraphDrawing.IsInternal (f.drawing.faceMap F) := by
      simpa only [hFace] using hInt
    have hIntSource := (f.drawing.isInternal_faceMap_iff F).mp hIntMap
    calc
      M'.toPlaneGraphDrawing.sideDegree F' =
          M'.toPlaneGraphDrawing.sideDegree (f.drawing.faceMap F) :=
        congrArg M'.toPlaneGraphDrawing.sideDegree hFace.symm
      _ = M.toPlaneGraphDrawing.sideDegree F :=
        (f.drawing.sideDegree_map e.orientationPreserving F).symm
      _ = 3 := htri F hIntSource
  · rintro ⟨hb, htri⟩
    refine ⟨f.isBipolar_map_iff.mpr hb, ?_⟩
    intro F hInt
    have hIntMap : M'.toPlaneGraphDrawing.IsInternal (f.drawing.faceMap F) :=
      (f.drawing.isInternal_faceMap_iff F).mpr hInt
    calc
      M.toPlaneGraphDrawing.sideDegree F =
          M'.toPlaneGraphDrawing.sideDegree (f.drawing.faceMap F) :=
        f.drawing.sideDegree_map e.orientationPreserving F
      _ = 3 := htri (f.drawing.faceMap F) hIntMap

end DirectedDistances.PlanarMap

end
