/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact25
import DirectedDistances.PlanarMap.D39PLCornerAccessArc

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric

private theorem path_point_mem_segment32 (p : Polyline) {i : ℕ}
    (hi : i + 1 < p.points.length) (t : I)
    (ht0 : Polyline.segmentParameterStart i ≤ (t : ℝ))
    (ht1 : (t : ℝ) ≤ Polyline.segmentParameterEnd p.points.length i) :
    p.toPath t ∈ p.segmentAt i := by
  let u : ℝ := ((t : ℝ) - Polyline.segmentParameterStart i) /
    (Polyline.segmentParameterEnd p.points.length i -
      Polyline.segmentParameterStart i)
  have hlen : Polyline.segmentParameterStart i <
      Polyline.segmentParameterEnd p.points.length i :=
    Polyline.segmentParameterStart_lt_end _ _
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr ht0)
    (sub_nonneg.mpr hlen.le)
  have hu1 : u ≤ 1 := by
    dsimp [u]
    apply (div_le_one (sub_pos.mpr hlen)).2
    linarith
  rw [Polyline.segmentAt, segment_eq_image']
  refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
  have hparam := Polyline.toPath_segment_affine_apply p hi t ht0 ht1
  rw [hparam]
  simp only [u, Complex.real_smul]

private theorem image_intervalPolyline_subinterval32 (p : Polyline)
    (i n j m : ℕ) (hfirst : i ≤ j) (hlast : j + m ≤ i + n) :
    (p.intervalPolyline j m).image ⊆ (p.intervalPolyline i n).image := by
  intro z hz
  rcases hz with hz | ⟨k, hk, hzk⟩
  · rw [mem_singleton_iff, Polyline.start_intervalPolyline] at hz
    have hidx : j - i ≤ n := by omega
    have hpoint : (p.intervalPolyline i n).point (j - i) = p.point j := by
      rw [Polyline.point_intervalPolyline p i n (j - i) hidx]
      congr 1
      omega
    rw [hz]
    rw [← hpoint]
    exact (p.intervalPolyline i n).point_mem_image (by
      simpa only [Polyline.length_intervalPolyline] using Nat.lt_succ_of_le hidx)
  · rw [Polyline.length_intervalPolyline] at hk
    have hk' : k < m := by omega
    have hparent : j - i + k < n := by omega
    refine Or.inr ⟨j - i + k, ?_, ?_⟩
    · rw [Polyline.length_intervalPolyline]
      omega
    · rw [Polyline.segmentAt_intervalPolyline p i n (j - i + k) hparent]
      rw [Polyline.segmentAt_intervalPolyline p j m k hk'] at hzk
      have hidx : j + k = i + (j - i + k) := by omega
      simpa only [hidx] using hzk

private theorem exists_simple_polyline_image_edgeSubarc_vertices32_of_indices
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (a b : I) (hab : a < b) (i j : ℕ) (hij : i ≤ j)
    (hi : i + 2 ≤ p.points.length) (hj : j + 2 ≤ p.points.length)
    (ha : Polyline.segmentParameterStart i ≤ (a : ℝ) ∧
      (a : ℝ) < Polyline.segmentParameterEnd p.points.length i)
    (hb : Polyline.segmentParameterStart j < (b : ℝ) ∧
      (b : ℝ) ≤ Polyline.segmentParameterEnd p.points.length j) :
    ∃ r : Polyline, r.IsSimple ∧ r.start = p.toPath a ∧
      r.finish = p.toPath b ∧ 2 ≤ r.points.length ∧
      r.points = (p.toPath a ::
        List.ofFn (fun k : Fin (j - i) => p.point (i + k.val + 1))) ++
          [p.toPath b] ∧
      r.image = Set.range (edgeSubarc p.toPath a b hab.le) ∧
      r.segmentAt 0 ⊆ p.segmentAt i := by
  by_cases hji : j = i
  · subst j
    obtain ⟨r, hrs, hstart, hfinish, hrlen, hrpoints, hrimage, hrsegment⟩ :=
      p.exists_simple_polyline_image_edgeSubarc_within_segment32 hp hlen i
        (by omega) a b hab ha.1 hb.2
    refine ⟨r, hrs, hstart, hfinish, hrlen, ?_, hrimage, hrsegment⟩
    simpa using hrpoints
  · by_cases hji1 : j = i + 1
    · subst j
      obtain ⟨r, hrs, hstart, hfinish, hrlen, hrpoints, hrimage, hrsegment⟩ :=
        Polyline.exists_simple_polyline_image_edgeSubarc_twoSegments32
          p hp hlen a b hab i (by omega) ha hb
      refine ⟨r, hrs, hstart, hfinish, hrlen, ?_, hrimage, hrsegment⟩
      simpa using hrpoints
    · have hgap : 2 ≤ j - i := by omega
      have hiSeg : i + 1 < p.points.length := by omega
      have hiStrict : i + 2 < p.points.length := by omega
      have hjSeg : j + 1 < p.points.length := by omega
      have hpi : Function.Injective p.toPath := p.toPath_injective hlen hp
      let c : I := ⟨Polyline.segmentParameterEnd p.points.length i,
        Polyline.segmentParameterEnd_mem_Icc p.points.length i⟩
      have hcval : (c : ℝ) = Polyline.segmentParameterEnd p.points.length i := rfl
      have hmid : Polyline.segmentParameterEnd p.points.length i =
          Polyline.segmentParameterStart (i + 1) :=
        Polyline.segmentParameterEnd_eq_start_succ (by omega)
      have hmidparam : p.toPath c = p.point (i + 1) := by
        have hparam := Polyline.toPath_segment_affine_apply p hiSeg c
          (by rw [hcval]; exact Polyline.segmentParameterStart_le_end _ _)
          (by rw [hcval])
        have hden : Polyline.segmentParameterEnd p.points.length i -
            Polyline.segmentParameterStart i ≠ 0 :=
          ne_of_gt (sub_pos.mpr (Polyline.segmentParameterStart_lt_end _ _))
        have h' : p.toPath c = p.point i +
            (p.point (i + 1) - p.point i) := by
          calc
            p.toPath c = p.point i +
                (((((c : ℝ) - Polyline.segmentParameterStart i) /
                  (Polyline.segmentParameterEnd p.points.length i -
                    Polyline.segmentParameterStart i) : ℝ) : ℂ) *
                    (p.point (i + 1) - p.point i)) := hparam
            _ = p.point i + (p.point (i + 1) - p.point i) := by
              rw [hcval]
              simp only [div_self hden, Complex.ofReal_one, one_mul]
        calc
          p.toPath c = p.point i + (p.point (i + 1) - p.point i) := h'
          _ = p.point (i + 1) := by abel
      have hac : (a : ℝ) < (c : ℝ) := by
        rw [hcval]
        exact ha.2
      let d : I := ⟨Polyline.segmentParameterStart j,
        Polyline.segmentParameterStart_mem_Icc j⟩
      have hdval : (d : ℝ) = Polyline.segmentParameterStart j := rfl
      have hdparam : p.toPath d = p.point j := by
        have hparam := Polyline.toPath_segment_affine_apply p hjSeg d
          (by rw [hdval])
          (by rw [hdval]; exact_mod_cast
            (Polyline.segmentParameterStart_le_end p.points.length j))
        simpa only [d, sub_self, zero_div, Complex.ofReal_zero, zero_mul,
          add_zero] using hparam
      have hdb : (d : ℝ) < (b : ℝ) := by
        rw [hdval]
        exact hb.1
      have hq1ne : p.toPath a ≠ p.point (i + 1) := by
        intro heq
        have htime : a = c := hpi (heq.trans hmidparam.symm)
        exact hac.ne (congrArg Subtype.val htime)
      have hq2ne : p.point j ≠ p.toPath b := by
        intro heq
        have htime : d = b := hpi (hdparam.trans heq)
        exact hdb.ne (congrArg Subtype.val htime)
      have hpa : p.toPath a ∈ p.segmentAt i :=
        path_point_mem_segment32 p hiSeg a ha.1 ha.2.le
      have hpb : p.toPath b ∈ p.segmentAt j :=
        path_point_mem_segment32 p hjSeg b hb.1.le hb.2
      have hright : p.point (i + 1) ∈ p.segmentAt i := by
        rw [Polyline.segmentAt]
        exact right_mem_segment ℝ _ _
      have hleft : p.point j ∈ p.segmentAt j := by
        rw [Polyline.segmentAt]
        exact left_mem_segment ℝ _ _
      let q₁ : Polyline := Polyline.cornerSegment (p.toPath a) (p.point (i + 1))
      let m : ℕ := j - i - 1
      let s : Polyline := p.intervalPolyline (i + 1) m
      let q₂ : Polyline := Polyline.cornerSegment (p.point j) (p.toPath b)
      have hq₁start : q₁.start = p.toPath a :=
        (Polyline.cornerSegment_data _ _).1
      have hq₁finish : q₁.finish = p.point (i + 1) :=
        (Polyline.cornerSegment_data _ _).2.1
      have hq₂start : q₂.start = p.point j :=
        (Polyline.cornerSegment_data _ _).1
      have hq₂finish : q₂.finish = p.toPath b :=
        (Polyline.cornerSegment_data _ _).2.1
      have hq₁image : q₁.image ⊆ p.segmentAt i := by
        rw [Polyline.image_cornerSegment]
        exact (convex_segment _ _).segment_subset hpa hright
      have hq₂image : q₂.image ⊆ p.segmentAt j := by
        rw [Polyline.image_cornerSegment]
        exact (convex_segment _ _).segment_subset hleft hpb
      have hq₁simple : q₁.IsSimple := Polyline.isSimple_cornerSegment hq1ne
      have hq₂simple : q₂.IsSimple := Polyline.isSimple_cornerSegment hq2ne
      have hmadd : i + 1 + m = j := by dsimp [m]; omega
      have hsbound : i + 1 + m < p.points.length := by omega
      have hssimple : s.IsSimple := by
        exact p.isSimple_intervalPolyline hp (i + 1) m hsbound
      have hslen : 2 ≤ s.points.length := by
        rw [Polyline.length_intervalPolyline]
        dsimp [m]
        omega
      have hsstart : s.start = p.point (i + 1) := by
        rw [Polyline.start_intervalPolyline]
      have hsfinish : s.finish = p.point j := by
        rw [Polyline.finish_intervalPolyline, hmadd]
      have hjoin₁ : q₁.finish = s.start := by
        rw [hq₁finish, hsstart]
      let nsuffix := p.points.length - (i + 1) - 1
      let suffix := p.intervalPolyline (i + 1) nsuffix
      have hsuffixSub : s.image ⊆ suffix.image := by
        apply image_intervalPolyline_subinterval32 p (i + 1) nsuffix
          (i + 1) m le_rfl
        dsimp [nsuffix, m]
        omega
      have hinter₁ : q₁.image ∩ s.image = {q₁.finish} := by
        have hsubset : q₁.image ∩ s.image ⊆ {p.point (i + 1)} := by
          intro z hz
          have hz' : z ∈ p.segmentAt i ∩ suffix.image :=
            ⟨hq₁image hz.1, hsuffixSub hz.2⟩
          have hsingle := p.segment_inter_suffix hp i hiSeg
          have hzpoint : z ∈ ({p.point (i + 1)} : Set ℂ) := by
            rw [← hsingle]
            exact hz'
          simpa using hzpoint
        have hsubset' : q₁.image ∩ s.image ⊆ {q₁.finish} := by
          simpa [hq₁finish] using hsubset
        apply Set.Subset.antisymm hsubset'
        intro z hz
        have hzu : z = q₁.finish := by
          simpa [hq₁finish] using hz
        subst z
        constructor
        · rw [Polyline.image_cornerSegment]
          rw [hq₁finish]
          exact right_mem_segment ℝ _ _
        · exact Or.inl hjoin₁
      let r₀ : Polyline := Polyline.boundaryConcat q₁ s
      have hr₀simple : r₀.IsSimple := by
        apply Polyline.isSimple_boundaryConcat q₁ s hq₁simple hssimple
          (by simp [q₁, Polyline.cornerSegment]) hslen hjoin₁ hinter₁
      have hr₀start : r₀.start = p.toPath a := by
        rw [Polyline.start_boundaryConcat, hq₁start]
      have hr₀finish : r₀.finish = p.point j := by
        rw [Polyline.finish_boundaryConcat q₁ s hslen, hsfinish]
      have hr₀image : r₀.image = q₁.image ∪ s.image :=
        Polyline.image_boundaryConcat q₁ s hjoin₁
      let pre := p.intervalPolyline 0 j
      have hq₁pre : q₁.image ⊆ pre.image := by
        apply hq₁image.trans
        intro z hz
        refine Or.inr ⟨i, ?_, ?_⟩
        · rw [Polyline.length_intervalPolyline]
          omega
        · change z ∈ (p.intervalPolyline 0 j).segmentAt i
          rw [Polyline.segmentAt_intervalPolyline p 0 j i (by omega)]
          simpa using hz
      have hsPre : s.image ⊆ pre.image := by
        apply image_intervalPolyline_subinterval32 p 0 j (i + 1) m (by omega)
        dsimp [m]
        omega
      have hr₀pre : r₀.image ⊆ pre.image := by
        rw [hr₀image]
        exact union_subset hq₁pre hsPre
      have hq₂join : r₀.finish = q₂.start := by
        rw [hr₀finish, hq₂start]
      have hinter₂ : r₀.image ∩ q₂.image = {r₀.finish} := by
        have hsubset : r₀.image ∩ q₂.image ⊆ {p.point j} := by
          intro z hz
          have hz' : z ∈ pre.image ∩ p.segmentAt j :=
            ⟨hr₀pre hz.1, hq₂image hz.2⟩
          have hsingle := p.prefix_inter_segment hp j hjSeg
          have hzpoint : z ∈ ({p.point j} : Set ℂ) := by
            rw [← hsingle]
            exact hz'
          exact hzpoint
        have hsubset' : r₀.image ∩ q₂.image ⊆ {r₀.finish} := by
          simpa [hr₀finish] using hsubset
        apply Set.Subset.antisymm hsubset'
        intro z hz
        have hzj : z = r₀.finish := by
          simpa [hr₀finish] using hz
        subst z
        constructor
        · rw [hr₀finish, hr₀image]
          right
          rw [← hsfinish]
          exact s.finish_mem_image_cornerAccess
        · rw [hr₀finish, Polyline.image_cornerSegment]
          exact left_mem_segment ℝ _ _
      let r : Polyline := Polyline.boundaryConcat r₀ q₂
      have hq₁len : 2 ≤ q₁.points.length := by
        simp [q₁, Polyline.cornerSegment]
      have hr₀len : 2 ≤ r₀.points.length := by
        rw [Polyline.length_boundaryConcat]
        omega
      have hrsimple : r.IsSimple := by
        apply Polyline.isSimple_boundaryConcat r₀ q₂ hr₀simple hq₂simple
          hr₀len
          (by simp [q₂, Polyline.cornerSegment]) hq₂join hinter₂
      have hrs : r.start = p.toPath a := by
        rw [Polyline.start_boundaryConcat, hr₀start]
      have hrf : r.finish = p.toPath b := by
        rw [Polyline.finish_boundaryConcat r₀ q₂ (by simp [q₂, Polyline.cornerSegment]),
          hq₂finish]
      have hrsub : r.image ⊆ p.image := by
        rw [Polyline.image_boundaryConcat r₀ q₂ hq₂join, hr₀image]
        apply union_subset
        · apply union_subset
          · exact hq₁image.trans (p.segmentAt_subset_image hiSeg)
          · exact p.image_intervalPolyline_subset (i + 1) m hsbound
        · exact hq₂image.trans (p.segmentAt_subset_image hjSeg)
      have hrlen : 2 ≤ r.points.length :=
        Polyline.length_two_of_start_ne_finish r (by
          rw [hrs, hrf]
          intro heq
          exact hab.ne (hpi heq))
      let δ : Path (p.toPath a) (p.toPath b) := r.toPath.cast hrs.symm hrf.symm
      have hδinj : Function.Injective δ := by
        simpa only [δ, Path.cast_coe] using r.toPath_injective hrlen hrsimple
      have hδsub : Set.range δ ⊆ Set.range p.toPath := by
        simpa only [δ, Path.cast_coe, Polyline.range_toPath] using hrsub
      have hδim := range_injective_path_subset_arc_eq_image_Icc32 p.toPath hpi
        a b hab.le δ hδinj hδsub
      have hrim : r.image = Set.range (edgeSubarc p.toPath a b hab.le) := by
        rw [range_edgeSubarc_eq_image_Icc32]
        simpa only [δ, Path.cast_coe, Polyline.range_toPath] using hδim
      have hfirst₁ : q₁.segmentAt 0 =
          segment ℝ (p.toPath a) (p.point (i + 1)) := by
        simp [q₁, Polyline.cornerSegment, Polyline.segmentAt, Polyline.point,
          Polyline.start]
      have hfirst : r.segmentAt 0 = q₁.segmentAt 0 := by
        calc
          r.segmentAt 0 = r₀.segmentAt 0 :=
            Polyline.segmentAt_boundaryConcat_left r₀ q₂ 0 (by
              rw [Polyline.length_boundaryConcat]
              omega)
          _ = q₁.segmentAt 0 :=
            Polyline.segmentAt_boundaryConcat_left q₁ s 0 (by
              simp [q₁, Polyline.cornerSegment])
      have hrpoints : r.points = (p.toPath a ::
          List.ofFn (fun k : Fin (j - i) => p.point (i + k.val + 1))) ++
            [p.toPath b] := by
        have hmidpoints : s.points =
            List.ofFn (fun k : Fin (j - i) => p.point (i + k.val + 1)) := by
          dsimp [s, Polyline.intervalPolyline]
          have hnum : j - i - 1 + 1 = j - i := by omega
          rw [hnum]
          congr 1
          funext k
          congr 1
          omega
        have hdecomp :
            List.ofFn (fun k : Fin (j - i) => p.point (i + k.val + 1)) =
              p.point (i + 1) ::
                (List.ofFn (fun k : Fin (j - i) => p.point (i + k.val + 1))).tail := by
          have hnum : j - i = j - i - 1 + 1 := by omega
          conv_lhs => rw [hnum, List.ofFn_succ]
          conv_rhs => rw [hnum, List.ofFn_succ]
          simp [Nat.add_assoc]
        dsimp [r, r₀, Polyline.boundaryConcat, q₁, q₂, Polyline.cornerSegment]
        rw [hmidpoints]
        conv_rhs => rw [hdecomp]
        simp
      refine ⟨r, hrsimple, hrs, hrf, hrlen, hrpoints, hrim, ?_⟩
      rw [hfirst, hfirst₁]
      exact (convex_segment _ _).segment_subset hpa hright

/-- Helper toward Definition 3.2: a simple polyline restricted to any
nondegenerate parameter interval has the exact list of intervening original
vertices and the same edge-subarc image. -/
theorem Polyline.exists_simple_polyline_image_edgeSubarc_vertices32
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (a b : I) (hab : a < b) :
    ∃ i j : ℕ, i ≤ j ∧
      Polyline.segmentParameterStart i ≤ (a : ℝ) ∧
      (a : ℝ) < Polyline.segmentParameterEnd p.points.length i ∧
      Polyline.segmentParameterStart j < (b : ℝ) ∧
      (b : ℝ) ≤ Polyline.segmentParameterEnd p.points.length j ∧
    ∃ r : Polyline, r.IsSimple ∧ r.start = p.toPath a ∧
      r.finish = p.toPath b ∧ 2 ≤ r.points.length ∧
      r.points = (p.toPath a ::
        List.ofFn (fun k : Fin (j - i) => p.point (i + k.val + 1))) ++
          [p.toPath b] ∧
      r.image = Set.range (edgeSubarc p.toPath a b hab.le) ∧
      r.segmentAt 0 ⊆ p.segmentAt i := by
  have ha1 : (a : ℝ) < 1 := lt_of_lt_of_le hab b.2.2
  have hb0 : 0 < (b : ℝ) := lt_of_le_of_lt a.2.1 hab
  obtain ⟨i, hi, _⟩ :=
    Polyline.exists_unique_segmentParameterStartIndex32 p.points.length hlen a ha1
  obtain ⟨j, hj, _⟩ :=
    Polyline.exists_unique_segmentParameterEndIndex32 p.points.length hlen b hb0
  have hij : i ≤ j :=
    Polyline.segmentParameterStartIndex_le_endIndex32 p.points.length hab
      hi.1 hi.2.1 hj.2.2
  refine ⟨i, j, hij, hi.2.1, hi.2.2, hj.2.1, hj.2.2, ?_⟩
  exact exists_simple_polyline_image_edgeSubarc_vertices32_of_indices
    p hp hlen a b hab i j hij hi.1 hj.1 ⟨hi.2.1, hi.2.2⟩ ⟨hj.2.1, hj.2.2⟩

end DirectedDistances.PlanarMap

end
