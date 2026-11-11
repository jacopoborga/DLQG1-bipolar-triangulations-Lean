/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BoundEdgesDefinition32SidesExact24
import DirectedDistances.PlanarMap.D39PLCornerAccessArc

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval Set Metric

/-- Helper toward Definition 3.2: the segment starts are monotone in their
index. -/
theorem Polyline.segmentParameterStart_le_of_le {i j : ℕ} (hij : i ≤ j) :
    Polyline.segmentParameterStart i ≤ Polyline.segmentParameterStart j := by
  have hsucc (k : ℕ) : Polyline.segmentParameterStart k <
      Polyline.segmentParameterStart (k + 1) := by
    rw [Polyline.segmentParameterStart_succ]
    have hk : Polyline.segmentParameterStart k < 1 := by
      simp only [Polyline.segmentParameterStart]
      linarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) k]
    linarith
  induction hij with
  | refl => exact le_rfl
  | @step j hij ih => exact ih.trans (le_of_lt (hsucc j))

/-- Helper toward Definition 3.2: every parameter below one belongs to a
unique half-open segment interval of a polyline with at least two points. -/
theorem Polyline.exists_unique_segmentParameterStartIndex32 (n : ℕ)
    (hn : 2 ≤ n) (a : I) (ha : (a : ℝ) < 1) :
    ∃! i : ℕ, i + 2 ≤ n ∧
      Polyline.segmentParameterStart i ≤ (a : ℝ) ∧
      (a : ℝ) < Polyline.segmentParameterEnd n i := by
  have hlastidx : (n - 2) + 2 = n := by omega
  have hcover : ∃ k : ℕ, (a : ℝ) < Polyline.segmentParameterEnd n k := by
    refine ⟨n - 2, ?_⟩
    rw [Polyline.segmentParameterEnd_last hlastidx]
    exact ha
  have hiend : (a : ℝ) < Polyline.segmentParameterEnd n (Nat.find hcover) :=
    Nat.find_spec hcover
  have hile : Nat.find hcover ≤ n - 2 := by
    apply Nat.find_min' hcover
    rw [Polyline.segmentParameterEnd_last hlastidx]
    exact ha
  have hiv : Nat.find hcover + 2 ≤ n := by omega
  have histart : Polyline.segmentParameterStart (Nat.find hcover) ≤ (a : ℝ) := by
    by_cases hi0 : Nat.find hcover = 0
    · rw [hi0, Polyline.segmentParameterStart_zero]
      exact a.2.1
    · have hprev : Nat.find hcover - 1 < Nat.find hcover := by omega
      have hnot : ¬ (a : ℝ) < Polyline.segmentParameterEnd n (Nat.find hcover - 1) :=
        Nat.find_min hcover hprev
      have hprevle : Polyline.segmentParameterEnd n (Nat.find hcover - 1) ≤
          (a : ℝ) :=
        le_of_not_gt hnot
      have hprevfinal : (Nat.find hcover - 1) + 2 ≠ n := by omega
      rw [Polyline.segmentParameterEnd_eq_start_succ hprevfinal] at hprevle
      have hidx : (Nat.find hcover - 1) + 1 = Nat.find hcover := by omega
      simpa only [hidx] using hprevle
  refine ⟨Nat.find hcover, ⟨hiv, histart, hiend⟩, ?_⟩
  intro j hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hji | hij
  · have hjfinal : j + 2 ≠ n := by omega
    rw [Polyline.segmentParameterEnd_eq_start_succ hjfinal] at hj
    have hjmono : Polyline.segmentParameterStart (j + 1) ≤
        Polyline.segmentParameterStart (Nat.find hcover) :=
      Polyline.segmentParameterStart_le_of_le (by omega)
    exact (not_lt_of_ge (hjmono.trans histart)) hj.2.2
  · have hifinal : Nat.find hcover + 2 ≠ n := by omega
    have hiend' : Polyline.segmentParameterEnd n (Nat.find hcover) =
        Polyline.segmentParameterStart (Nat.find hcover + 1) :=
      Polyline.segmentParameterEnd_eq_start_succ hifinal
    rw [hiend'] at hiend
    have himono : Polyline.segmentParameterStart (Nat.find hcover + 1) ≤
        Polyline.segmentParameterStart j :=
      Polyline.segmentParameterStart_le_of_le (by omega)
    exact (not_lt_of_ge (himono.trans hj.2.1)) hiend

/-- Helper toward Definition 3.2: every positive parameter belongs to a
unique interval open at its initial endpoint and closed at its terminal
endpoint. -/
theorem Polyline.exists_unique_segmentParameterEndIndex32 (n : ℕ)
    (hn : 2 ≤ n) (b : I) (hb : 0 < (b : ℝ)) :
    ∃! j : ℕ, j + 2 ≤ n ∧
      Polyline.segmentParameterStart j < (b : ℝ) ∧
      (b : ℝ) ≤ Polyline.segmentParameterEnd n j := by
  have hlastidx : (n - 2) + 2 = n := by omega
  have hcover : ∃ k : ℕ, (b : ℝ) ≤ Polyline.segmentParameterEnd n k := by
    refine ⟨n - 2, ?_⟩
    rw [Polyline.segmentParameterEnd_last hlastidx]
    exact b.2.2
  have hjend : (b : ℝ) ≤ Polyline.segmentParameterEnd n (Nat.find hcover) :=
    Nat.find_spec hcover
  have hjle : Nat.find hcover ≤ n - 2 := by
    apply Nat.find_min' hcover
    rw [Polyline.segmentParameterEnd_last hlastidx]
    exact b.2.2
  have hjv : Nat.find hcover + 2 ≤ n := by omega
  have hjstart : Polyline.segmentParameterStart (Nat.find hcover) < (b : ℝ) := by
    by_cases hj0 : Nat.find hcover = 0
    · rw [hj0, Polyline.segmentParameterStart_zero]
      exact hb
    · have hprev : Nat.find hcover - 1 < Nat.find hcover := by omega
      have hnot : ¬ (b : ℝ) ≤ Polyline.segmentParameterEnd n (Nat.find hcover - 1) :=
        Nat.find_min hcover hprev
      have hprevlt : Polyline.segmentParameterEnd n (Nat.find hcover - 1) <
          (b : ℝ) :=
        lt_of_not_ge hnot
      have hprevfinal : (Nat.find hcover - 1) + 2 ≠ n := by omega
      rw [Polyline.segmentParameterEnd_eq_start_succ hprevfinal] at hprevlt
      have hidx : (Nat.find hcover - 1) + 1 = Nat.find hcover := by omega
      simpa only [hidx] using hprevlt
  refine ⟨Nat.find hcover, ⟨hjv, hjstart, hjend⟩, ?_⟩
  intro k hk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkn | hnk
  · have hkfinal : k + 2 ≠ n := by omega
    rw [Polyline.segmentParameterEnd_eq_start_succ hkfinal] at hk
    have hkle : Polyline.segmentParameterStart (k + 1) ≤
        Polyline.segmentParameterStart (Nat.find hcover) :=
      Polyline.segmentParameterStart_le_of_le (by omega)
    exact (not_lt_of_ge (le_trans hk.2.2 hkle)) hjstart
  · have hjfinal : Nat.find hcover + 2 ≠ n := by omega
    rw [Polyline.segmentParameterEnd_eq_start_succ hjfinal] at hjend
    have hjle : Polyline.segmentParameterStart (Nat.find hcover + 1) ≤
        Polyline.segmentParameterStart k :=
      Polyline.segmentParameterStart_le_of_le (by omega)
    exact (not_lt_of_ge hjend) (lt_of_le_of_lt hjle hk.2.1)

/-- Helper toward Definition 3.2: a subarc crossing exactly two consecutive
segments has the explicit three-vertex list and the same edge-subarc image. -/
theorem Polyline.exists_simple_polyline_image_edgeSubarc_twoSegments32
    (p : Polyline) (hp : p.IsSimple) (hlen : 2 ≤ p.points.length)
    (a b : I) (hab : a < b) (i : ℕ) (hi : i + 2 < p.points.length)
    (ha : Polyline.segmentParameterStart i ≤ (a : ℝ) ∧
      (a : ℝ) < Polyline.segmentParameterEnd p.points.length i)
    (hb : Polyline.segmentParameterStart (i + 1) < (b : ℝ) ∧
      (b : ℝ) ≤ Polyline.segmentParameterEnd p.points.length (i + 1)) :
    ∃ r : Polyline, r.IsSimple ∧ r.start = p.toPath a ∧
      r.finish = p.toPath b ∧ 2 ≤ r.points.length ∧
      r.points = [p.toPath a, p.point (i + 1), p.toPath b] ∧
      r.image = Set.range (edgeSubarc p.toPath a b hab.le) ∧
      r.segmentAt 0 ⊆ p.segmentAt i := by
  have hpi : Function.Injective p.toPath := p.toPath_injective hlen hp
  have hi0 : i + 1 < p.points.length := by omega
  have hi1 : (i + 1) + 1 < p.points.length := by omega
  have hnotlast : i + 2 ≠ p.points.length := by omega
  have hmid : Polyline.segmentParameterEnd p.points.length i =
      Polyline.segmentParameterStart (i + 1) :=
    Polyline.segmentParameterEnd_eq_start_succ hnotlast
  let c : I := ⟨Polyline.segmentParameterEnd p.points.length i,
    Polyline.segmentParameterEnd_mem_Icc p.points.length i⟩
  have hcval : (c : ℝ) = Polyline.segmentParameterEnd p.points.length i := rfl
  have hmidparam : p.toPath c = p.point (i + 1) := by
    have hparam := Polyline.toPath_segment_affine_apply p hi0 c
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
  have hstart_lt : (a : ℝ) < (c : ℝ) := by
    rw [hcval]
    exact ha.2
  have hmid_lt : (c : ℝ) < (b : ℝ) := by
    rw [hcval, hmid]
    exact hb.1
  have hpoint_mem (k : ℕ) (hk : k + 1 < p.points.length) (t : I)
      (ht0 : Polyline.segmentParameterStart k ≤ (t : ℝ))
      (ht1 : (t : ℝ) ≤ Polyline.segmentParameterEnd p.points.length k) :
      p.toPath t ∈ p.segmentAt k := by
    let u : ℝ := ((t : ℝ) - Polyline.segmentParameterStart k) /
      (Polyline.segmentParameterEnd p.points.length k -
        Polyline.segmentParameterStart k)
    have hlenp : Polyline.segmentParameterStart k <
        Polyline.segmentParameterEnd p.points.length k :=
      Polyline.segmentParameterStart_lt_end _ _
    have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr ht0)
      (sub_nonneg.mpr hlenp.le)
    have hu1 : u ≤ 1 := by
      dsimp [u]
      apply (div_le_one (sub_pos.mpr hlenp)).2
      linarith
    rw [Polyline.segmentAt, segment_eq_image']
    refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
    have hparam := Polyline.toPath_segment_affine_apply p hk t ht0 ht1
    rw [hparam]
    simp only [u, Complex.real_smul]
  have haPoint : p.toPath a ∈ p.segmentAt i :=
    hpoint_mem i hi0 a ha.1 ha.2.le
  have hbPoint : p.toPath b ∈ p.segmentAt (i + 1) :=
    hpoint_mem (i + 1) hi1 b hb.1.le hb.2
  let v : ℂ := p.point (i + 1)
  have hq1ne : p.toPath a ≠ v := by
    intro heq
    have htime : a = c := hpi (heq.trans hmidparam.symm)
    exact (not_lt_of_ge (le_of_eq (congrArg Subtype.val htime).symm)) hstart_lt
  have hq2ne : v ≠ p.toPath b := by
    intro heq
    have htime : c = b := hpi (hmidparam.trans heq)
    exact (not_lt_of_ge (le_of_eq (congrArg Subtype.val htime).symm)) hmid_lt
  let q₁ : Polyline := Polyline.cornerSegment (p.toPath a) v
  let q₂ : Polyline := Polyline.cornerSegment v (p.toPath b)
  have hq₁mem : q₁.image ⊆ p.segmentAt i := by
    rw [Polyline.image_cornerSegment]
    exact (convex_segment _ _).segment_subset haPoint
      (by simpa [v] using right_mem_segment ℝ _ _)
  have hq₂mem : q₂.image ⊆ p.segmentAt (i + 1) := by
    rw [Polyline.image_cornerSegment]
    exact (convex_segment _ _).segment_subset
      (by simpa [v] using left_mem_segment ℝ _ _)
      hbPoint
  have hint : q₁.image ∩ q₂.image = {v} := by
    apply Set.Subset.antisymm
    · intro z hz
      have h := hp.2.1 i hi1
      have hz' : z ∈ p.segmentAt i ∩ p.segmentAt (i + 1) :=
        ⟨hq₁mem hz.1, hq₂mem hz.2⟩
      have hz'' : z ∈ ({p.point (i + 1)} : Set ℂ) := by
        rw [← h]
        exact hz'
      simpa [v] using hz''
    · intro z hz
      have hzv : z = v := mem_singleton_iff.mp hz
      subst z
      constructor
      · rw [Polyline.image_cornerSegment]
        exact right_mem_segment ℝ _ _
      · rw [Polyline.image_cornerSegment]
        exact left_mem_segment ℝ _ _
  have hjoin : q₁.finish = q₂.start := by
    simp [q₁, q₂, v, Polyline.cornerSegment, Polyline.finish, Polyline.start]
  let r : Polyline := Polyline.boundaryConcat q₁ q₂
  have hrs : r.start = p.toPath a := by
    calc
      r.start = q₁.start := Polyline.start_boundaryConcat _ _
      _ = p.toPath a := (Polyline.cornerSegment_data _ _).1
  have hrf : r.finish = p.toPath b := by
    calc
      r.finish = q₂.finish :=
        Polyline.finish_boundaryConcat _ _ (by simp [q₂, Polyline.cornerSegment])
      _ = p.toPath b := (Polyline.cornerSegment_data _ _).2.1
  have hrlen : 2 ≤ r.points.length := by
    simp [r, Polyline.boundaryConcat, q₁, q₂, Polyline.cornerSegment]
  have hrpoints : r.points = [p.toPath a, p.point (i + 1), p.toPath b] := by
    simp [r, Polyline.boundaryConcat, q₁, q₂, Polyline.cornerSegment, v]
  have hrsimple : r.IsSimple := by
    apply Polyline.isSimple_boundaryConcat q₁ q₂
      (Polyline.isSimple_cornerSegment hq1ne)
      (Polyline.isSimple_cornerSegment hq2ne)
      (by simp [q₁, Polyline.cornerSegment])
      (by simp [q₂, Polyline.cornerSegment]) hjoin hint
  have hrsub : r.image ⊆ p.image := by
    rw [Polyline.image_boundaryConcat q₁ q₂ hjoin]
    apply union_subset
    · exact hq₁mem.trans (p.segmentAt_subset_image hi0)
    · exact hq₂mem.trans (p.segmentAt_subset_image hi1)
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
  have hfirst : r.segmentAt 0 = segment ℝ (p.toPath a) v := by
    rw [Polyline.segmentAt_boundaryConcat_left q₁ q₂ 0 (by
      simp [q₁, Polyline.cornerSegment])]
    simp [q₁, Polyline.cornerSegment, Polyline.segmentAt, Polyline.point,
      Polyline.start, v]
  refine ⟨r, hrsimple, hrs, hrf, hrlen, hrpoints, hrim, ?_⟩
  rw [hfirst]
  exact (convex_segment _ _).segment_subset haPoint
    (by simpa [v] using right_mem_segment ℝ _ _)

/-- Helper toward Definition 3.2: the unique start-index for `a` does not
exceed the unique end-index for `b` when `a < b`. -/
theorem Polyline.segmentParameterStartIndex_le_endIndex32 (n : ℕ)
    {a b : I} (hab : (a : ℝ) < (b : ℝ))
    {i j : ℕ} (hi : i + 2 ≤ n)
    (hia : Polyline.segmentParameterStart i ≤ (a : ℝ))
    (hjb' : (b : ℝ) ≤ Polyline.segmentParameterEnd n j) : i ≤ j := by
  by_contra h
  have hji : j < i := by omega
  have hjfinal : j + 2 ≠ n := by omega
  rw [Polyline.segmentParameterEnd_eq_start_succ hjfinal] at hjb'
  have hmono : Polyline.segmentParameterStart (j + 1) ≤
      Polyline.segmentParameterStart i :=
    Polyline.segmentParameterStart_le_of_le (by omega)
  linarith [hab]































end DirectedDistances.PlanarMap

end
