module

public import DirectedDistances.Probability.SkorokhodJ1WindowDEvalMeasurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity






@[expose] public section
namespace DirectedDistances.Probability

open Set

private theorem exists_timeChange_of_dist_lt {T : ℝ} (hT : 0 < T)
    (x y : J1WindowD T hT) {δ : ℝ} (hδ : dist y x < δ) :
    ∃ φ : J1TimeChange T,
      (∀ s, |(φ s : ℝ) - (s : ℝ)| < δ) ∧
      (∀ s, |y.path.1 (φ s) - x.path.1 s| < δ) := by
  change (⨅ φ : J1TimeChange T,
    max (⨆ s : J1Window T, |((φ s : ℝ) - (s : ℝ))|)
      (⨆ s : J1Window T, |y.path.1 (φ s) - x.path.1 s|)) < δ at hδ
  obtain ⟨φ, hcost⟩ := exists_lt_of_ciInf_lt hδ
  refine ⟨φ, ?_, ?_⟩
  · intro s
    exact ((le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove φ) s le_rfl).trans
      (le_max_left _ _)).trans_lt hcost
  · intro s
    exact ((le_ciSup_of_le (j1WindowValueError_bddAbove y.path x.path φ) s le_rfl).trans
      (le_max_right _ _)).trans_lt hcost




theorem isOpen_j1WindowD_exists_eval_gt {T : ℝ} (hT : 0 < T) (a b c : ℝ) :
    IsOpen {x : J1WindowD T hT |
      ∃ s : J1Window T, a < (s : ℝ) ∧ (s : ℝ) < b ∧ c < x.path.1 s} := by
  rw [Metric.isOpen_iff]
  rintro x ⟨s, has, hsb, hcs⟩
  let δ := min ((s : ℝ) - a) (min (b - (s : ℝ)) (x.path.1 s - c))
  have hδ : 0 < δ := lt_min (sub_pos.mpr has)
    (lt_min (sub_pos.mpr hsb) (sub_pos.mpr hcs))
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  obtain ⟨φ, htime, hvalue⟩ := exists_timeChange_of_dist_lt hT x y hy
  refine ⟨φ s, ?_, ?_, ?_⟩
  · have h := (abs_lt.mp (htime s)).1
    have hd : δ ≤ (s : ℝ) - a := min_le_left _ _
    linarith
  · have h := (abs_lt.mp (htime s)).2
    have hd : δ ≤ b - (s : ℝ) := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  · have h := (abs_lt.mp (hvalue s)).1
    have hd : δ ≤ x.path.1 s - c := (min_le_right _ _).trans (min_le_right _ _)
    linarith

private theorem eval_gt_iff_open_hits {T : ℝ} (hT : 0 < T)
    (x : J1WindowD T hT) (t : J1Window T) (ht : (t : ℝ) < T) (a : ℝ) :
    a < x.path.1 t ↔ ∃ q : ℚ, a < (q : ℝ) ∧ ∀ n : ℕ,
      ∃ s : J1Window T, (t : ℝ) < (s : ℝ) ∧
        (s : ℝ) < (t : ℝ) + 1 / (n + 1 : ℝ) ∧ (q : ℝ) < x.path.1 s := by
  constructor
  · intro ha
    obtain ⟨q, haq, hqx⟩ := exists_rat_btwn ha
    refine ⟨q, haq, ?_⟩
    obtain ⟨r, hr, hnear⟩ := Metric.continuousWithinAt_iff.mp
      (x.path.2.isRightContinuous t) (x.path.1 t - (q : ℝ)) (sub_pos.mpr hqx)
    intro n
    have hn : 0 < 1 / (n + 1 : ℝ) := by positivity
    have hroom : (t : ℝ) < min T
        (min ((t : ℝ) + r) ((t : ℝ) + 1 / (n + 1 : ℝ))) :=
      lt_min ht (lt_min (lt_add_of_pos_right _ hr) (lt_add_of_pos_right _ hn))
    obtain ⟨u, htu, hu⟩ := exists_between hroom
    have huT : u < T := hu.trans_le (min_le_left _ _)
    have hur : u < (t : ℝ) + r :=
      (hu.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
    have hun : u < (t : ℝ) + 1 / (n + 1 : ℝ) :=
      (hu.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
    let s : J1Window T := ⟨u, t.property.1.trans htu.le, huT.le⟩
    have hdist : dist s t < r := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.mpr htu)]
      linarith
    have hclose := hnear (show s ∈ Ioi t from htu) hdist
    rw [Real.dist_eq] at hclose
    have hlow := (abs_lt.mp hclose).1
    refine ⟨s, htu, hun, ?_⟩
    linarith
  · rintro ⟨q, haq, hhit⟩
    have hqx : (q : ℝ) ≤ x.path.1 t := by
      by_contra hnot
      have hxq : x.path.1 t < (q : ℝ) := lt_of_not_ge hnot
      obtain ⟨r, hr, hnear⟩ := Metric.continuousWithinAt_iff.mp
        (x.path.2.isRightContinuous t) ((q : ℝ) - x.path.1 t) (sub_pos.mpr hxq)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
      obtain ⟨s, hts, hsn, hqs⟩ := hhit n
      have hdist : dist s t < r := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.mpr hts)]
        have hsub : (s : ℝ) - (t : ℝ) < 1 / (n + 1 : ℝ) :=
          by linarith
        exact hsub.trans hn
      have hclose := hnear (show s ∈ Ioi t from hts) hdist
      rw [Real.dist_eq] at hclose
      have hu := (abs_lt.mp hclose).2
      linarith
    exact haq.trans_le hqx




theorem measurable_j1WindowD_eval {T : ℝ} (hT : 0 < T)
    [MeasurableSpace (J1WindowD T hT)] [BorelSpace (J1WindowD T hT)]
    (t : J1Window T) :
    Measurable (fun x : J1WindowD T hT => x.path.1 t) := by
  by_cases ht : (t : ℝ) = T
  · have heq : t = ⟨T, hT.le, le_rfl⟩ := Subtype.ext ht
    subst t
    exact measurable_j1WindowD_eval_endpoint hT
  · have htT : (t : ℝ) < T := lt_of_le_of_ne t.property.2 ht
    apply measurable_of_Ioi
    intro a
    have heq : (fun x : J1WindowD T hT => x.path.1 t) ⁻¹' Ioi a =
        ⋃ q : ℚ, ⋃ (_ : a < (q : ℝ)), ⋂ n : ℕ,
          {x : J1WindowD T hT | ∃ s : J1Window T,
            (t : ℝ) < (s : ℝ) ∧ (s : ℝ) < (t : ℝ) + 1 / (n + 1 : ℝ) ∧
              (q : ℝ) < x.path.1 s} := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_iInter, mem_ofPred_eq]
      constructor
      · intro hx
        obtain ⟨q, haq, hq⟩ := (eval_gt_iff_open_hits hT x t htT a).mp hx
        exact ⟨q, haq, hq⟩
      · rintro ⟨q, haq, hq⟩
        exact (eval_gt_iff_open_hits hT x t htT a).mpr ⟨q, haq, hq⟩
    rw [heq]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iInter fun n =>
        (isOpen_j1WindowD_exists_eval_gt hT (t : ℝ)
          ((t : ℝ) + 1 / (n + 1 : ℝ)) (q : ℝ)).measurableSet

end DirectedDistances.Probability
