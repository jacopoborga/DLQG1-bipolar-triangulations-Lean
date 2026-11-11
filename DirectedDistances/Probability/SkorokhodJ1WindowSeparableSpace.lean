module

public import DirectedDistances.Probability.SkorokhodJ1WindowPolish
public import Mathlib.Topology.MetricSpace.Polish

import Mathlib.Topology.Order.IntermediateValue

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-conv` (see CORRESPONDENCE.md). -/

@[expose] public section
namespace DirectedDistances.Probability




noncomputable def windowPartitionBlockIndicator {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (i : Fin p.n) : J1Window T → ℝ := fun t =>
  thresholdStep (p.time i.castSucc).val 1 t -
    thresholdStep (p.time i.succ).val 1 t

private theorem isCadlag_fin_sum {T : ℝ} :
    ∀ n : ℕ, ∀ f : Fin n → J1Window T → ℝ,
      (∀ i, IsCadlag (f i)) → IsCadlag (fun t => ∑ i : Fin n, f i t) := by
  intro n
  induction n with
  | zero =>
    intro f hf
    change IsCadlag (fun _ : J1Window T => (0 : ℝ))
    exact IsCadlag.const
  | succ n ih =>
    intro f hf
    have hdecomp :
        (fun t => ∑ i : Fin (n + 1), f i t) =
          fun t => f 0 t + ∑ i : Fin n, f i.succ t := by
      funext t
      simp only [Fin.sum_univ_succ]
    rw [hdecomp]
    exact (hf 0).continuous_comp₂
      (ih (fun i => f i.succ) (fun i => hf i.succ)) continuous_add




noncomputable def windowPartitionStepFunction {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (x : CadlagWindow T) : J1Window T → ℝ :=
  fun t =>
    (∑ i : Fin p.n, x.1 (p.time i.castSucc) *
      windowPartitionBlockIndicator p i t) +
    thresholdStep T (x.1 ⟨T, hT.le, le_rfl⟩) t

private theorem windowPartitionBlockIndicator_isCadlag {T : ℝ}
    {hT : 0 < T} (p : WindowPartition T hT) (i : Fin p.n) :
    IsCadlag (windowPartitionBlockIndicator p i) := by
  exact (thresholdStep_isCadlag _ _).continuous_comp₂
    (thresholdStep_isCadlag _ _) continuous_sub




theorem windowPartitionStepFunction_isCadlag {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (x : CadlagWindow T) :
    IsCadlag (windowPartitionStepFunction p x) := by
  apply (isCadlag_fin_sum p.n _ ?_).continuous_comp₂
    (thresholdStep_isCadlag _ _) continuous_add
  intro i
  exact (IsCadlag.const (c := x.1 (p.time i.castSucc))).continuous_comp₂
    (windowPartitionBlockIndicator_isCadlag p i) continuous_mul




noncomputable def windowPartitionStepPath {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (x : CadlagWindow T) : CadlagWindow T :=
  ⟨windowPartitionStepFunction p x, windowPartitionStepFunction_isCadlag p x⟩




noncomputable def windowPartitionValueStepFunction {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (v : Fin (p.n + 1) → ℝ) : J1Window T → ℝ :=
  fun t =>
    (∑ i : Fin p.n, v i.castSucc * windowPartitionBlockIndicator p i t) +
      thresholdStep T (v (Fin.last p.n)) t




theorem windowPartitionValueStepFunction_isCadlag {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (v : Fin (p.n + 1) → ℝ) :
    IsCadlag (windowPartitionValueStepFunction p v) := by
  apply (isCadlag_fin_sum p.n _ ?_).continuous_comp₂
    (thresholdStep_isCadlag _ _) continuous_add
  intro i
  exact (IsCadlag.const (c := v i.castSucc)).continuous_comp₂
    (windowPartitionBlockIndicator_isCadlag p i) continuous_mul




noncomputable def windowPartitionValueStepPath {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (v : Fin (p.n + 1) → ℝ) : CadlagWindow T :=
  ⟨windowPartitionValueStepFunction p v,
    windowPartitionValueStepFunction_isCadlag p v⟩

private theorem windowPartition_exists_half_open_block
    {T : ℝ} {hT : 0 < T} (p : WindowPartition T hT)
    (s : J1Window T) (hsT : (s : ℝ) < T) :
    ∃ i : Fin p.n, p.time i.castSucc ≤ s ∧ s < p.time i.succ := by
  classical
  let q : Finset (Fin (p.n + 1)) :=
    Finset.univ.filter fun j => (s : ℝ) < (p.time j : ℝ)
  have hq : q.Nonempty := by
    refine ⟨Fin.last p.n, ?_⟩
    simp only [q, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [p.last]
    exact hsT
  let j := q.min' hq
  have hjq : j ∈ q := Finset.min'_mem q hq
  have hjs : (s : ℝ) < (p.time j : ℝ) := by
    simpa only [q, Finset.mem_filter, Finset.mem_univ, true_and] using hjq
  have hjpos : 0 < j.val := by
    by_contra hj
    have hjzero : j.val = 0 := by omega
    have htime : p.time j = p.time 0 := by
      apply congrArg p.time
      apply Fin.ext
      exact hjzero
    rw [htime, p.first] at hjs
    exact (not_lt_of_ge s.property.1) hjs
  let i : Fin p.n := ⟨j.val - 1, by have := j.isLt; omega⟩
  have hji : i.succ = j := by
    apply Fin.ext
    simp only [Fin.val_succ]
    dsimp [i]
    omega
  have hleft : p.time i.castSucc ≤ s := by
    by_contra hnot
    have hprev : (s : ℝ) < (p.time i.castSucc : ℝ) := by
      exact_mod_cast (lt_of_not_ge hnot)
    have hprev_mem : i.castSucc ∈ q := by
      simp only [q, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hprev
    have hmin := Finset.min'_le q i.castSucc hprev_mem
    have hmin' : i.succ ≤ i.castSucc := by simpa [hji] using hmin
    have hvals : (i.succ).val ≤ (i.castSucc).val := by exact_mod_cast hmin'
    simp only [Fin.val_succ, Fin.val_castSucc] at hvals
    omega
  refine ⟨i, hleft, ?_⟩
  rw [hji]
  exact_mod_cast hjs

private theorem windowPartitionBlockIndicator_eq_zero_of_ne
    {T : ℝ} {hT : 0 < T} (p : WindowPartition T hT)
    (i j : Fin p.n) (t : J1Window T)
    (htl : p.time i.castSucc ≤ t) (htr : t < p.time i.succ)
    (hji : j ≠ i) : windowPartitionBlockIndicator p j t = 0 := by
  have hstrict : StrictMono p.time := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro k
    exact_mod_cast p.strict k
  have horder : j.val < i.val ∨ i.val < j.val := by omega
  rcases horder with hj | hj
  · have hnode : p.time j.succ ≤ p.time i.castSucc := by
      apply hstrict.monotone
      exact_mod_cast (show j.val + 1 ≤ i.val by omega)
    have hnode' : (p.time j.succ).val ≤ (p.time i.castSucc).val := by
      exact_mod_cast hnode
    have htl' : (p.time i.castSucc).val ≤ (t : ℝ) := by
      exact_mod_cast htl
    have hb : (p.time j.succ).val ≤ (t : ℝ) := hnode'.trans htl'
    have hstrictj : (p.time j.castSucc).val < (p.time j.succ).val := by
      exact_mod_cast p.strict j
    have ha : (p.time j.castSucc).val ≤ (t : ℝ) := hstrictj.le.trans hb
    simp [windowPartitionBlockIndicator, thresholdStep, hb, ha]
  · have hnode : p.time i.succ ≤ p.time j.castSucc := by
      apply hstrict.monotone
      exact_mod_cast (show i.val + 1 ≤ j.val by omega)
    have hnode' : (p.time i.succ).val ≤ (p.time j.castSucc).val := by
      exact_mod_cast hnode
    have htr' : (t : ℝ) < (p.time i.succ).val := by
      exact_mod_cast htr
    have ha : (t : ℝ) < (p.time j.castSucc).val :=
      lt_of_lt_of_le htr' hnode'
    have hstrictj : (p.time j.castSucc).val < (p.time j.succ).val := by
      exact_mod_cast p.strict j
    have hb : (t : ℝ) < (p.time j.succ).val := lt_trans ha hstrictj
    simp [windowPartitionBlockIndicator, thresholdStep,
      not_le_of_gt ha, not_le_of_gt hb]

private theorem windowPartitionStepFunction_eq_node_of_block
    {T : ℝ} {hT : 0 < T} (p : WindowPartition T hT)
    (x : CadlagWindow T) (i : Fin p.n) (t : J1Window T)
    (htl : p.time i.castSucc ≤ t) (htr : t < p.time i.succ) :
    windowPartitionStepFunction p x t = x.1 (p.time i.castSucc) := by
  classical
  have hindicator (j : Fin p.n) :
      windowPartitionBlockIndicator p j t = if j = i then 1 else 0 := by
    by_cases hji : j = i
    · subst j
      simp [windowPartitionBlockIndicator, thresholdStep,
        (show (p.time i.castSucc).val ≤ (t : ℝ) by exact_mod_cast htl),
        (show ¬(p.time i.succ).val ≤ (t : ℝ) by
          exact not_le_of_gt (by exact_mod_cast htr))]
    · rw [windowPartitionBlockIndicator_eq_zero_of_ne p i j t htl htr hji]
      simp [hji]
  have hsum :
      (∑ j : Fin p.n, x.1 (p.time j.castSucc) *
        windowPartitionBlockIndicator p j t) = x.1 (p.time i.castSucc) := by
    calc
      _ = ∑ j : Fin p.n, if j = i then x.1 (p.time i.castSucc) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hindicator j]
        by_cases hji : j = i <;> simp [hji]
      _ = x.1 (p.time i.castSucc) := by simp
  have htop : ¬ T ≤ (t : ℝ) := by
    apply not_le_of_gt
    exact lt_of_lt_of_le htr (p.time i.succ).property.2
  simp [windowPartitionStepFunction, hsum, thresholdStep, htop]

private theorem windowPartitionStepFunction_at_top {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (x : CadlagWindow T) :
    windowPartitionStepFunction p x ⟨T, hT.le, le_rfl⟩ =
      x.1 ⟨T, hT.le, le_rfl⟩ := by
  classical
  have hzero (i : Fin p.n) :
      windowPartitionBlockIndicator p i ⟨T, hT.le, le_rfl⟩ = 0 := by
    have ha : (p.time i.castSucc).val ≤ T :=
      (p.time i.castSucc).property.2
    have hb : (p.time i.succ).val ≤ T :=
      (p.time i.succ).property.2
    simp [windowPartitionBlockIndicator, thresholdStep, ha, hb]
  have hsum :
      (∑ i : Fin p.n, x.1 (p.time i.castSucc) *
        windowPartitionBlockIndicator p i ⟨T, hT.le, le_rfl⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero]
    simp
  simp [windowPartitionStepFunction, hsum, thresholdStep]

private theorem windowPartitionValueStepFunction_eq_node_of_block
    {T : ℝ} {hT : 0 < T} (p : WindowPartition T hT)
    (v : Fin (p.n + 1) → ℝ) (i : Fin p.n) (t : J1Window T)
    (htl : p.time i.castSucc ≤ t) (htr : t < p.time i.succ) :
    windowPartitionValueStepFunction p v t = v i.castSucc := by
  classical
  have hindicator (j : Fin p.n) :
      windowPartitionBlockIndicator p j t = if j = i then 1 else 0 := by
    by_cases hji : j = i
    · subst j
      simp [windowPartitionBlockIndicator, thresholdStep,
        (show (p.time i.castSucc).val ≤ (t : ℝ) by exact_mod_cast htl),
        (show ¬(p.time i.succ).val ≤ (t : ℝ) by
          exact not_le_of_gt (by exact_mod_cast htr))]
    · rw [windowPartitionBlockIndicator_eq_zero_of_ne p i j t htl htr hji]
      simp [hji]
  have hsum :
      (∑ j : Fin p.n, v j.castSucc *
        windowPartitionBlockIndicator p j t) = v i.castSucc := by
    calc
      _ = ∑ j : Fin p.n, if j = i then v i.castSucc else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hindicator j]
        by_cases hji : j = i <;> simp [hji]
      _ = v i.castSucc := by simp
  have htop : ¬ T ≤ (t : ℝ) := by
    apply not_le_of_gt
    exact lt_of_lt_of_le htr (p.time i.succ).property.2
  simp [windowPartitionValueStepFunction, hsum, thresholdStep, htop]

private theorem windowPartitionValueStepFunction_at_top {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (v : Fin (p.n + 1) → ℝ) :
    windowPartitionValueStepFunction p v ⟨T, hT.le, le_rfl⟩ =
      v (Fin.last p.n) := by
  classical
  have hzero (i : Fin p.n) :
      windowPartitionBlockIndicator p i ⟨T, hT.le, le_rfl⟩ = 0 := by
    have ha : (p.time i.castSucc).val ≤ T := (p.time i.castSucc).property.2
    have hb : (p.time i.succ).val ≤ T := (p.time i.succ).property.2
    simp [windowPartitionBlockIndicator, thresholdStep, ha, hb]
  have hsum :
      (∑ i : Fin p.n, v i.castSucc *
        windowPartitionBlockIndicator p i ⟨T, hT.le, le_rfl⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero]
    simp
  simp [windowPartitionValueStepFunction, hsum, thresholdStep]




theorem windowPartitionStepPath_valueApproximation {T : ℝ} (hT : 0 < T)
    (p : WindowPartition T hT) (x : CadlagWindow T)
    (v : Fin (p.n + 1) → ℝ) {ε : ℝ} (_hε : 0 ≤ ε)
    (hv : ∀ i, |x.1 (p.time i) - v i| ≤ ε) :
    j1WindowDist hT (windowPartitionStepPath p x)
      (windowPartitionValueStepPath p v) ≤ ε := by
  have hpoint (t : J1Window T) :
      |(windowPartitionStepPath p x).1 t -
        (windowPartitionValueStepPath p v).1 t| ≤ ε := by
    change |windowPartitionStepFunction p x t -
      windowPartitionValueStepFunction p v t| ≤ ε
    by_cases htT : (t : ℝ) = T
    · have ht : t = (⟨T, hT.le, le_rfl⟩ : J1Window T) := Subtype.ext htT
      subst t
      rw [windowPartitionStepFunction_at_top p x,
        windowPartitionValueStepFunction_at_top p v]
      have hlast := hv (Fin.last p.n)
      rw [p.last] at hlast
      exact hlast
    · have htlt : (t : ℝ) < T := lt_of_le_of_ne t.property.2 htT
      obtain ⟨i, hleft, hright⟩ :=
        windowPartition_exists_half_open_block p t htlt
      rw [windowPartitionStepFunction_eq_node_of_block p x i t hleft hright,
        windowPartitionValueStepFunction_eq_node_of_block p v i t hleft hright]
      exact hv i.castSucc
  have hsup :
      (⨆ t : J1Window T,
        |(windowPartitionStepPath p x).1 t -
          (windowPartitionValueStepPath p v).1 t|) ≤ ε := by
    change sSup (Set.range fun t : J1Window T =>
      |(windowPartitionStepPath p x).1 t -
        (windowPartitionValueStepPath p v).1 t|) ≤ _
    apply csSup_le
    · refine ⟨|((windowPartitionStepPath p x).1 ⟨0, le_rfl, hT.le⟩) -
        (windowPartitionValueStepPath p v).1 ⟨0, le_rfl, hT.le⟩|, ?_⟩
      exact ⟨⟨0, le_rfl, hT.le⟩, rfl⟩
    · rintro z ⟨t, rfl⟩
      exact hpoint t
  exact (j1WindowDist_le_sup_dist hT
    (windowPartitionStepPath p x) (windowPartitionValueStepPath p v)).trans hsup




theorem exists_rationalWindowPartitionValues {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (x : CadlagWindow T) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ q : Fin (p.n + 1) → ℚ,
      ∀ i, |x.1 (p.time i) - (q i : ℝ)| < ε := by
  classical
  choose q hq using fun i : Fin (p.n + 1) =>
    exists_rat_near (x.1 (p.time i)) hε
  exact ⟨q, hq⟩




theorem exists_rationalValueStepPath_close {T : ℝ} (hT : 0 < T)
    (p : WindowPartition T hT) (x : CadlagWindow T) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ q : Fin (p.n + 1) → ℚ,
      j1WindowDist hT (windowPartitionStepPath p x)
        (windowPartitionValueStepPath p (fun i => (q i : ℝ))) < ε := by
  obtain ⟨q, hq⟩ := exists_rationalWindowPartitionValues p x
    (show 0 < ε / 2 by positivity)
  refine ⟨q, ?_⟩
  have hv (i : Fin (p.n + 1)) :
      |x.1 (p.time i) - (q i : ℝ)| ≤ ε / 2 := (hq i).le
  have hdist := windowPartitionStepPath_valueApproximation hT p x
    (fun i => (q i : ℝ)) (by positivity) hv
  exact hdist.trans_lt (by linarith)





theorem exists_partitionStepPath_uniform_close {T : ℝ} (hT : 0 < T)
    (x : CadlagWindow T) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : CadlagWindow T,
      (⨆ t : J1Window T, |x.1 t - g.1 t|) < ε ∧
        j1WindowDist hT x g < ε := by
  obtain ⟨p, hp⟩ := exists_partition_oscillation_lt hT x
    (show 0 < ε / 2 by positivity)
  let g := windowPartitionStepPath p x
  have hpoint (t : J1Window T) : |x.1 t - g.1 t| ≤ ε / 2 := by
    by_cases htT : (t : ℝ) = T
    · have ht : t = (⟨T, hT.le, le_rfl⟩ : J1Window T) := Subtype.ext htT
      subst t
      simp only [g, windowPartitionStepPath]
      rw [windowPartitionStepFunction_at_top]
      simpa using (show 0 ≤ ε / 2 by positivity)
    · have htlt : (t : ℝ) < T := lt_of_le_of_ne t.property.2 htT
      obtain ⟨i, hleft, hright⟩ :=
        windowPartition_exists_half_open_block p t htlt
      have hstep := windowPartitionStepFunction_eq_node_of_block
        p x i t hleft hright
      have hosc : |x.1 t - x.1 (p.time i.castSucc)| ≤
          blockOscillation x (p.time i.castSucc) (p.time i.succ) := by
        apply le_csSup (blockOscillation_values_bddAbove x _ _)
        refine ⟨t, p.time i.castSucc, ?_, ?_, ?_, ?_, rfl⟩
        · exact_mod_cast hleft
        · exact_mod_cast hright
        · exact le_rfl
        · exact_mod_cast (p.strict i)
      change |x.1 t - windowPartitionStepFunction p x t| ≤ ε / 2
      rw [hstep]
      exact hosc.trans (hp i).le
  have hsup : (⨆ t : J1Window T, |x.1 t - g.1 t|) ≤ ε / 2 := by
    change sSup (Set.range fun t : J1Window T => |x.1 t - g.1 t|) ≤ _
    apply csSup_le
    · exact ⟨|x.1 ⟨0, le_rfl, hT.le⟩ - g.1 ⟨0, le_rfl, hT.le⟩|,
        ⟨⟨0, le_rfl, hT.le⟩, rfl⟩⟩
    · rintro z ⟨t, rfl⟩
      exact hpoint t
  refine ⟨g, hsup.trans_lt (by linarith), ?_⟩
  exact (j1WindowDist_le_sup_dist hT x g).trans_lt
    (hsup.trans_lt (by linarith))




theorem rationalStepPathD_range_countable {T : ℝ} (hT : 0 < T) :
    (Set.range fun p : ℚ × (List (ℚ × ℚ) × ℚ) =>
      toJ1WindowD (hT := hT)
        (rationalStepPath hT p.1 p.2.1 p.2.2)).Countable := by
  exact Set.countable_range _





theorem windowPartitionValueStepPath_timeChange_bound {T : ℝ} (hT : 0 < T)
    (p : WindowPartition T hT)
    (s : Fin (p.n + 1) → Set.Icc (0 : ℝ) T)
    (hsfirst : s 0 = ⟨0, by simp [hT.le]⟩)
    (hslast : s (Fin.last p.n) = ⟨T, hT.le, le_rfl⟩)
    (hsstrict : ∀ i : Fin p.n, (s i.castSucc).val < (s i.succ).val)
    (v : Fin (p.n + 1) → ℝ) (φ : J1TimeChange T) {η : ℝ}
    (hη : 0 ≤ η)
    (hnodes : ∀ i, φ (s i) = p.time i)
    (hdisp : ∀ t, |(φ t : ℝ) - (t : ℝ)| ≤ η) :
    let q : WindowPartition T hT :=
      { n := p.n, n_pos := p.n_pos, time := s, first := hsfirst,
        last := hslast, strict := hsstrict }
    j1WindowDist hT (windowPartitionValueStepPath p v)
      (windowPartitionValueStepPath q v) ≤ η := by
  dsimp only
  let q : WindowPartition T hT :=
    { n := p.n, n_pos := p.n_pos, time := s, first := hsfirst,
      last := hslast, strict := hsstrict }
  change j1WindowDist hT (windowPartitionValueStepPath p v)
    (windowPartitionValueStepPath q v) ≤ η
  dsimp only [q] at *
  let f := windowPartitionValueStepPath p v
  let g := windowPartitionValueStepPath q v
  let top : J1Window T := ⟨T, hT.le, le_rfl⟩
  have hpoint : ∀ t : J1Window T, f.1 (φ t) = g.1 t := by
    intro t
    change windowPartitionValueStepFunction p v (φ t) =
      windowPartitionValueStepFunction q v t
    by_cases ht : (t : ℝ) = T
    · have hteq : t = top := Subtype.ext ht
      subst t
      have hφtop : φ top = top := by
        have hn := hnodes (Fin.last p.n)
        rw [hslast, p.last] at hn
        exact hn
      rw [hφtop, windowPartitionValueStepFunction_at_top p v,
        windowPartitionValueStepFunction_at_top q v]
    · have htlt : (t : ℝ) < T := lt_of_le_of_ne t.property.2 ht
      obtain ⟨i, hleft, hright⟩ := windowPartition_exists_half_open_block q t htlt
      have hleft' : p.time i.castSucc ≤ φ t := by
        rw [← hnodes]
        exact φ.monotone hleft
      have hright' : φ t < p.time i.succ := by
        rw [← hnodes]
        exact φ.strictMono hright
      rw [windowPartitionValueStepFunction_eq_node_of_block q v i t hleft hright,
        windowPartitionValueStepFunction_eq_node_of_block p v i (φ t)
          hleft' hright']
  have hdispSup :
      (⨆ t : J1Window T, |(φ t : ℝ) - (t : ℝ)|) ≤ η := by
    change sSup (Set.range fun t : J1Window T =>
      |(φ t : ℝ) - (t : ℝ)|) ≤ η
    apply csSup_le
    · exact ⟨|(φ top : ℝ) - (top : ℝ)|, ⟨top, rfl⟩⟩
    · rintro z ⟨t, rfl⟩
      exact hdisp t
  have hvalueSup : (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|) ≤ 0 := by
    change sSup (Set.range fun t : J1Window T => |f.1 (φ t) - g.1 t|) ≤ 0
    apply csSup_le
    · exact ⟨0, ⟨top, by simp [hpoint]⟩⟩
    · rintro z ⟨t, rfl⟩
      change |f.1 (φ t) - g.1 t| ≤ 0
      rw [hpoint t]
      simp
  have hcosts : BddBelow (Set.range fun ψ : J1TimeChange T =>
      max (⨆ t : J1Window T, |(ψ t : ℝ) - (t : ℝ)|)
        (⨆ t : J1Window T,
          |(windowPartitionValueStepPath p v).1 (ψ t) -
            (windowPartitionValueStepPath q v).1 t|)) := by
    refine ⟨0, ?_⟩
    rintro z ⟨ψ, rfl⟩
    apply le_max_of_le_left
    exact le_ciSup_of_le (j1WindowTimeChangeDistortion_bddAbove ψ) top
      (abs_nonneg _)
  change (⨅ ψ : J1TimeChange T,
    max (⨆ t : J1Window T, |(ψ t : ℝ) - (t : ℝ)|)
      (⨆ t : J1Window T,
        |(windowPartitionValueStepPath p v).1 (ψ t) -
          (windowPartitionValueStepPath q v).1 t|)) ≤ η
  calc
    _ ≤ max (⨆ t : J1Window T, |(φ t : ℝ) - (t : ℝ)|)
        (⨆ t : J1Window T, |f.1 (φ t) - g.1 t|) :=
      ciInf_le hcosts φ
    _ ≤ η := max_le hdispSup (hvalueSup.trans hη)

end DirectedDistances.Probability

namespace DirectedDistances.Probability

private noncomputable def nodeInterpolant {T : ℝ} {hT : 0 < T}
    (q : WindowPartition T hT) (v : Fin (q.n + 1) → ℝ) (t : J1Window T) : ℝ :=
  ∑ i : Fin q.n, ((v i.succ - v i.castSucc) /
    ((q.time i.succ : ℝ) - (q.time i.castSucc : ℝ))) *
      (min (t : ℝ) (q.time i.succ : ℝ) - min (t : ℝ) (q.time i.castSucc : ℝ))

private theorem nodeInterpolant_continuous {T : ℝ} {hT : 0 < T}
    (q : WindowPartition T hT) (v : Fin (q.n + 1) → ℝ) :
    Continuous (nodeInterpolant q v) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul
    ((continuous_subtype_val.min continuous_const).sub
      (continuous_subtype_val.min continuous_const))

private theorem node_sum_adjacent (n : ℕ) :
    ∀ f : Fin (n + 1) → ℝ,
      (Finset.univ.sum (fun i : Fin n => f i.succ - f (Fin.castSucc i))) =
        f (Fin.last n) - f 0 := by
  induction n with
  | zero =>
    intro f
    simp
  | succ n ih =>
    intro f
    rw [Fin.sum_univ_castSucc]
    have hih := ih (fun j => f (Fin.castSucc j))
    have hfirst :
        Finset.univ.sum (fun i : Fin n =>
          f (Fin.castSucc (Fin.succ i)) - f (Fin.castSucc (Fin.castSucc i))) =
          f (Fin.castSucc (Fin.last n)) - f 0 := by
      simpa using hih
    have hsum :
        Finset.univ.sum (fun i : Fin n =>
          f (Fin.succ (Fin.castSucc i)) - f (Fin.castSucc (Fin.castSucc i))) =
        Finset.univ.sum (fun i : Fin n =>
          f (Fin.castSucc (Fin.succ i)) - f (Fin.castSucc (Fin.castSucc i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show Fin.succ (Fin.castSucc i) = Fin.castSucc i.succ by
        exact Fin.ext (by simp)]
    rw [hsum, hfirst]
    have hlast : f (Fin.last n).succ = f (Fin.last (n + 1)) := by
      congr 1
    rw [hlast]
    ring

private theorem node_increment_nonneg {a b s t : ℝ}
    (hab : a ≤ b) (hst : s ≤ t) :
    0 ≤ (min t b - min t a) - (min s b - min s a) := by
  by_cases hsa : s ≤ a
  · by_cases hta : t ≤ a
    · rw [min_eq_left hta, min_eq_left hsa,
        min_eq_left (le_trans hta hab), min_eq_left (le_trans hsa hab)]
      simp
    · have hat : a < t := lt_of_not_ge hta
      have ham : a ≤ min t b := le_min hat.le hab
      rw [min_eq_left hsa, min_eq_left (le_trans hsa hab), min_eq_right hat.le]
      linarith
  · have has : a < s := lt_of_not_ge hsa
    have hat : a < t := lt_of_lt_of_le has hst
    rw [min_eq_right has.le, min_eq_right hat.le]
    have hmin : min s b ≤ min t b := min_le_min hst le_rfl
    linarith

private theorem node_increment_sum {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) {s t : ℝ}
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hsT : s ≤ T) (htT : t ≤ T) :
    Finset.univ.sum (fun i : Fin p.n =>
      (min t (p.time i.succ : ℝ) - min t (p.time i.castSucc : ℝ)) -
        (min s (p.time i.succ : ℝ) - min s (p.time i.castSucc : ℝ))) = t - s := by
  let f : Fin (p.n + 1) → ℝ := fun j =>
    min t (p.time j : ℝ) - min s (p.time j : ℝ)
  calc
    _ = Finset.univ.sum (fun i : Fin p.n => f i.succ - f i.castSucc) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [f]
      ring
    _ = f (Fin.last p.n) - f 0 := node_sum_adjacent p.n f
    _ = t - s := by
      dsimp [f]
      simp only [p.last, p.first, Subtype.coe_mk]
      rw [min_eq_left htT, min_eq_left hsT,
        min_eq_right ht0, min_eq_right hs0]
      ring


private theorem nodeInterpolant_node {T : ℝ} {hT : 0 < T}
    (q : WindowPartition T hT) (v : Fin (q.n + 1) → ℝ)
    (hv0 : v 0 = 0) (k : Fin (q.n + 1)) :
    nodeInterpolant q v (q.time k) = v k := by
  have hmono : StrictMono (fun j => (q.time j : ℝ)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact q.strict i
  have hterm (i : Fin q.n) :
      ((v i.succ - v i.castSucc) /
          ((q.time i.succ : ℝ) - (q.time i.castSucc : ℝ))) *
        (min (q.time k : ℝ) (q.time i.succ : ℝ) -
          min (q.time k : ℝ) (q.time i.castSucc : ℝ)) =
        v (min k i.succ) - v (min k i.castSucc) := by
    by_cases hi : i.val < k.val
    · have his : i.succ ≤ k := by exact_mod_cast (show i.val + 1 ≤ k.val by omega)
      have hic : i.castSucc ≤ k := by exact_mod_cast (show i.val ≤ k.val by omega)
      rw [min_eq_right (hmono.monotone his), min_eq_right (hmono.monotone hic),
        min_eq_right his, min_eq_right hic]
      exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr (q.strict i)))
    · have hic : k ≤ i.castSucc := by exact_mod_cast (show k.val ≤ i.val by omega)
      have his : k ≤ i.succ := hic.trans (Fin.castSucc_le_succ i)
      rw [min_eq_left (hmono.monotone his), min_eq_left (hmono.monotone hic),
        min_eq_left his, min_eq_left hic]
      simp
  unfold nodeInterpolant
  simp_rw [hterm]
  rw [node_sum_adjacent q.n (fun j => v (min k j))]
  rw [min_eq_left (Fin.le_last k), min_eq_right (Fin.zero_le k), hv0, sub_zero]

private theorem nodeInterpolant_strictMono {T : ℝ} {hT : 0 < T}
    (p : WindowPartition T hT) (v : Fin (p.n + 1) → ℝ)
    (hv : StrictMono v) :
    StrictMono (nodeInterpolant p v) := by
  let slopes : Fin p.n → ℝ := fun i => ((v i.succ - v i.castSucc) /
    ((p.time i.succ : ℝ) - (p.time i.castSucc : ℝ)))
  let S : Finset ℝ := Finset.univ.image slopes
  have hS : S.Nonempty := by
    refine ⟨slopes ⟨0, p.n_pos⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, p.n_pos⟩, Finset.mem_univ _, rfl⟩
  let c : ℝ := S.min' hS
  have hc_mem : c ∈ S := Finset.min'_mem S hS
  have hcpos : 0 < c := by
    rcases Finset.mem_image.mp hc_mem with ⟨i, _, hci⟩
    rw [← hci]
    exact div_pos (sub_pos.mpr (hv (i.castSucc_lt_succ)))
        (sub_pos.mpr (p.strict i))
  have hcle (i : Fin p.n) : c ≤ slopes i := by
    exact Finset.min'_le S _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  intro x y hxy
  let s : ℝ := x
  let t : ℝ := y
  let increment : Fin p.n → ℝ := fun i =>
    (min t (p.time i.succ : ℝ) - min t (p.time i.castSucc : ℝ)) -
      (min s (p.time i.succ : ℝ) - min s (p.time i.castSucc : ℝ))
  have hst : s < t := by exact_mod_cast hxy
  have hinc (i : Fin p.n) : 0 ≤ increment i := by
    apply node_increment_nonneg
    · exact (p.strict i).le
    · exact hst.le
  have hsuminc : ∑ i : Fin p.n, increment i = t - s := by
    exact node_increment_sum p
      (by exact_mod_cast x.property.1)
      (by exact_mod_cast y.property.1)
      (by exact_mod_cast x.property.2)
      (by exact_mod_cast y.property.2)
  have hdiff :
      nodeInterpolant p v y -
          nodeInterpolant p v x =
        ∑ i : Fin p.n, slopes i * increment i := by
    change (∑ i : Fin p.n, slopes i *
      (min (y : ℝ) (p.time i.succ : ℝ) - min (y : ℝ) (p.time i.castSucc : ℝ))) -
      (∑ i : Fin p.n, slopes i *
      (min (x : ℝ) (p.time i.succ : ℝ) - min (x : ℝ) (p.time i.castSucc : ℝ))) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [slopes, increment, s, t]
    ring
  have hsumle :
      (∑ i : Fin p.n, c * increment i) ≤
        ∑ i : Fin p.n, slopes i * increment i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hcle i) (hinc i)
  have hconstsum :
      (∑ i : Fin p.n, c * increment i) = c * (t - s) := by
    rw [← Finset.mul_sum, hsuminc]
  have hdiffpos :
      0 < nodeInterpolant p v y -
        nodeInterpolant p v x := by
    have hpos : 0 < c * (t - s) := mul_pos hcpos (sub_pos.mpr hst)
    calc
      0 < c * (t - s) := hpos
      _ ≤ nodeInterpolant p v y -
          nodeInterpolant p v x := by
        calc
          c * (t - s) = ∑ i : Fin p.n, c * increment i := hconstsum.symm
          _ ≤ ∑ i : Fin p.n, slopes i * increment i := hsumle
          _ = nodeInterpolant p v y -
              nodeInterpolant p v x := hdiff.symm
  exact sub_pos.mp hdiffpos


private theorem nodeInterpolant_block {T : ℝ} {hT : 0 < T}
    (q : WindowPartition T hT) (v : Fin (q.n + 1) → ℝ) (hv0 : v 0 = 0)
    (i : Fin q.n) (t : J1Window T)
    (hl : q.time i.castSucc ≤ t) (hr : t ≤ q.time i.succ) :
    nodeInterpolant q v t = v i.castSucc +
      ((v i.succ - v i.castSucc) /
        ((q.time i.succ : ℝ) - (q.time i.castSucc : ℝ))) *
          ((t : ℝ) - (q.time i.castSucc : ℝ)) := by
  classical
  change (q.time i.castSucc : ℝ) ≤ (t : ℝ) at hl
  change (t : ℝ) ≤ (q.time i.succ : ℝ) at hr
  have hm : StrictMono (fun j => (q.time j : ℝ)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    exact q.strict j
  have heq : nodeInterpolant q v t - nodeInterpolant q v (q.time i.castSucc) =
      ((v i.succ - v i.castSucc) /
        ((q.time i.succ : ℝ) - (q.time i.castSucc : ℝ))) *
          ((t : ℝ) - (q.time i.castSucc : ℝ)) := by
    unfold nodeInterpolant
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · rw [min_eq_left hr, min_eq_right hl,
        min_eq_left (q.strict i).le, min_self]
      ring
    · intro j _ hji
      have hij : j.val < i.val ∨ i.val < j.val := by omega
      rcases hij with hij | hij
      · have hnode : (q.time j.succ : ℝ) ≤ (q.time i.castSucc : ℝ) :=
          hm.monotone (by exact_mod_cast (show j.val + 1 ≤ i.val by omega))
        have hnode' := hnode.trans hl
        have hjl := hm.monotone (Fin.castSucc_le_succ j)
        rw [min_eq_right hnode', min_eq_right (hjl.trans hnode'),
          min_eq_right hnode, min_eq_right (hjl.trans hnode)]
        ring
      · have hnode : (q.time i.succ : ℝ) ≤ (q.time j.castSucc : ℝ) :=
          hm.monotone (by exact_mod_cast (show i.val + 1 ≤ j.val by omega))
        have hnode' := hr.trans hnode
        have hjl := hm.monotone (Fin.castSucc_le_succ j)
        have hil := hm.monotone (Fin.castSucc_le_succ i)
        rw [min_eq_left (hnode'.trans hjl), min_eq_left hnode',
          min_eq_left (hil.trans (hnode.trans hjl)),
          min_eq_left (hil.trans hnode)]
        ring
    · simp
  rw [nodeInterpolant_node q v hv0] at heq
  linarith only [heq]





theorem exists_windowPartition_nodeTimeChange {T : ℝ} (hT : 0 < T)
    (p : WindowPartition T hT)
    (s : Fin (p.n + 1) → Set.Icc (0 : ℝ) T)
    (hsfirst : s 0 = ⟨0, by simp [hT.le]⟩)
    (hslast : s (Fin.last p.n) = ⟨T, hT.le, le_rfl⟩)
    (hsstrict : ∀ i : Fin p.n, (s i.castSucc).val < (s i.succ).val) :
    ∃ φ : J1TimeChange T, (∀ i, φ (s i) = p.time i) ∧
      ∀ t, |(φ t : ℝ) - (t : ℝ)| ≤
        Finset.univ.sup' (Finset.univ_nonempty)
          (fun i : Fin (p.n + 1) => |(s i : ℝ) - (p.time i : ℝ)|) := by
  classical
  let q : WindowPartition T hT :=
    { n := p.n, n_pos := p.n_pos, time := s, first := hsfirst,
      last := hslast, strict := hsstrict }
  let v : Fin (q.n + 1) → ℝ := fun i => p.time i
  have hv0 : v 0 = 0 := congrArg Subtype.val p.first
  have hvl : v (Fin.last q.n) = T := congrArg Subtype.val p.last
  have hv : StrictMono v := by
    apply Fin.strictMono_iff_lt_succ.mpr
    exact p.strict
  let F := nodeInterpolant q v
  have hFm : StrictMono F := nodeInterpolant_strictMono q v hv
  have hF0 : F ⟨0, le_rfl, hT.le⟩ = 0 := by
    rw [← q.first]
    exact (nodeInterpolant_node q v hv0 0).trans hv0
  have hFT : F ⟨T, hT.le, le_rfl⟩ = T := by
    rw [← q.last]
    exact (nodeInterpolant_node q v hv0 (Fin.last q.n)).trans hvl
  have hmem (t : J1Window T) : F t ∈ Set.Icc 0 T := by
    constructor
    · rw [← hF0]
      exact hFm.monotone t.property.1
    · rw [← hFT]
      exact hFm.monotone t.property.2
  let G : J1Window T → J1Window T := fun t => ⟨F t, hmem t⟩
  have hGm : StrictMono G := hFm
  have hGs : Function.Surjective G := by
    let : PreconnectedSpace (J1Window T) := Subtype.preconnectedSpace isPreconnected_Icc
    intro y
    have hy : (y : ℝ) ∈ Set.Icc (F ⟨0, le_rfl, hT.le⟩)
        (F ⟨T, hT.le, le_rfl⟩) := by
      rw [hF0, hFT]
      exact y.property
    obtain ⟨x, hx⟩ := intermediate_value_univ
      (⟨0, le_rfl, hT.le⟩ : J1Window T) ⟨T, hT.le, le_rfl⟩
      (nodeInterpolant_continuous q v) hy
    exact ⟨x, Subtype.ext hx⟩
  let φ : J1TimeChange T := StrictMono.orderIsoOfSurjective G hGm hGs
  have hφ (t : J1Window T) : (φ t : ℝ) = F t := rfl
  refine ⟨φ, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    rw [hφ]
    exact nodeInterpolant_node q v hv0 i
  · intro t
    let M := Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin (p.n + 1) => |(s i : ℝ) - (p.time i : ℝ)|)
    have hM (i : Fin (p.n + 1)) : |v i - (q.time i : ℝ)| ≤ M := by
      rw [abs_sub_comm]
      exact Finset.le_sup'
        (fun j : Fin (p.n + 1) => |(s j : ℝ) - (p.time j : ℝ)|)
        (Finset.mem_univ i)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    rw [hφ]
    change |F t - (t : ℝ)| ≤ M
    by_cases ht : (t : ℝ) = T
    · have hteq : t = ⟨T, hT.le, le_rfl⟩ := Subtype.ext ht
      rw [hteq, hFT]
      simpa using hM0
    · obtain ⟨i, hl, hr⟩ := windowPartition_exists_half_open_block q t
        (lt_of_le_of_ne t.property.2 ht)
      have hf := nodeInterpolant_block q v hv0 i t hl hr.le
      let a : ℝ := q.time i.castSucc
      let b : ℝ := q.time i.succ
      let θ : ℝ := ((t : ℝ) - a) / (b - a)
      have hab : 0 < b - a := sub_pos.mpr (q.strict i)
      have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hl) hab.le
      have hθ1 : θ ≤ 1 := (div_le_one hab).mpr
        (sub_le_sub_right (show (t : ℝ) ≤ b from hr.le) a)
      have hθt : θ * (b - a) = (t : ℝ) - a := div_mul_cancel₀ _ hab.ne'
      have hf' : F t = v i.castSucc + θ * (v i.succ - v i.castSucc) := by
        change F t = _ at hf
        rw [hf]
        dsimp [θ, a, b]
        ring
      have hleft := abs_le.mp (hM i.castSucc)
      have hright := abs_le.mp (hM i.succ)
      change -M ≤ v i.castSucc - a ∧ v i.castSucc - a ≤ M at hleft
      change -M ≤ v i.succ - b ∧ v i.succ - b ≤ M at hright
      rw [hf']
      apply abs_le.mpr
      constructor
      · nlinarith only [mul_nonneg hθ0 (sub_nonneg.mpr hright.1),
          mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr hleft.1), hθt]
      · nlinarith only [mul_nonneg hθ0 (sub_nonneg.mpr hright.2),
          mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr hleft.2), hθt]


private def rationalNodeMap {n : ℕ} (T : ℝ) (r : Fin (n + 1) → ℚ)
    (i : Fin (n + 1)) : ℝ :=
  if i = 0 then 0 else if i = Fin.last n then T else (r i : ℝ)

private def RationalNodeData (T : ℝ) :=
  {d : Σ n : ℕ, (Fin (n + 1) → ℚ) × (Fin (n + 1) → ℚ) //
    0 < d.1 ∧ (∀ i, rationalNodeMap T d.2.1 i ∈ Set.Icc 0 T) ∧
      ∀ i : Fin d.1,
        rationalNodeMap T d.2.1 i.castSucc < rationalNodeMap T d.2.1 i.succ}

private noncomputable def rationalNodePartition {T : ℝ} (hT : 0 < T)
    (d : RationalNodeData T) : WindowPartition T hT where
  n := d.val.1
  n_pos := d.property.1
  time i := ⟨rationalNodeMap T d.val.2.1 i, d.property.2.1 i⟩
  first := by apply Subtype.ext; simp [rationalNodeMap]
  last := by
    apply Subtype.ext
    have hn : (Fin.last d.val.1 : Fin (d.val.1 + 1)) ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_last, Fin.val_zero] at this
      exact (Nat.ne_of_gt d.property.1) this
    simp [rationalNodeMap, hn]
  strict := d.property.2.2

private noncomputable def rationalNodeFamily {T : ℝ} (hT : 0 < T)
    (d : RationalNodeData T) : J1WindowD T hT :=
  toJ1WindowD (windowPartitionValueStepPath (rationalNodePartition hT d)
    (fun i => (d.val.2.2 i : ℝ)))

private theorem rationalNodeFamily_countable {T : ℝ} (hT : 0 < T) :
    (Set.range (rationalNodeFamily hT)).Countable := by
  have : Countable (RationalNodeData T) := by
    unfold RationalNodeData
    infer_instance
  exact Set.countable_range _

private theorem exists_rationalNodeMap_close {T : ℝ} (hT : 0 < T)
    (p : WindowPartition T hT) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : Fin (p.n + 1) → ℚ,
      (∀ i, rationalNodeMap T r i ∈ Set.Icc 0 T) ∧
      (∀ i : Fin p.n, rationalNodeMap T r i.castSucc < rationalNodeMap T r i.succ) ∧
      ∀ i, |rationalNodeMap T r i - (p.time i : ℝ)| < ε := by
  classical
  let gaps := Finset.univ.image (fun i : Fin p.n =>
    (p.time i.succ : ℝ) - (p.time i.castSucc : ℝ))
  have hne : gaps.Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨⟨0, p.n_pos⟩, Finset.mem_univ _, rfl⟩⟩
  let g := gaps.min' hne
  have hg : 0 < g := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem gaps hne)
    change 0 < gaps.min' hne
    rw [← hi]
    exact sub_pos.mpr (p.strict i)
  have hgap (i : Fin p.n) : g ≤ (p.time i.succ : ℝ) - (p.time i.castSucc : ℝ) :=
    Finset.min'_le gaps _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let δ := min ε (g / 3)
  have hδ : 0 < δ := lt_min hε (by positivity)
  choose r hr using fun i : Fin (p.n + 1) => exists_rat_near (p.time i : ℝ) hδ
  have hclose (i : Fin (p.n + 1)) :
      |rationalNodeMap T r i - (p.time i : ℝ)| < δ := by
    by_cases hi0 : i = 0
    · subst i
      simp [rationalNodeMap, p.first, hδ]
    · by_cases hil : i = Fin.last p.n
      · subst i
        simp [rationalNodeMap, hi0, p.last, hδ]
      · simpa [rationalNodeMap, hi0, hil, abs_sub_comm] using hr i
  have hm : StrictMono (rationalNodeMap T r) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have hl := abs_lt.mp (hclose i.castSucc)
    have hu := abs_lt.mp (hclose i.succ)
    have hd : δ ≤ g / 3 := min_le_right _ _
    linarith [hgap i]
  have hfirst : rationalNodeMap T r 0 = 0 := by simp [rationalNodeMap]
  have hlast : rationalNodeMap T r (Fin.last p.n) = T := by
    have hn : (Fin.last p.n : Fin (p.n + 1)) ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_last, Fin.val_zero] at this
      exact (Nat.ne_of_gt p.n_pos) this
    simp [rationalNodeMap, hn]
  refine ⟨r, ?_, (fun i => hm i.castSucc_lt_succ), ?_⟩
  · intro i
    constructor
    · rw [← hfirst]
      exact hm.monotone (Fin.zero_le i)
    · exact (hm.monotone (Fin.le_last i)).trans_eq hlast
  · intro i
    exact (hclose i).trans_le (min_le_left _ _)

private theorem exists_partitionStepPath_close {T : ℝ} (hT : 0 < T)
    (x : CadlagWindow T) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : WindowPartition T hT, j1WindowDist hT x (windowPartitionStepPath p x) < ε := by
  obtain ⟨p, hp⟩ := exists_partition_oscillation_lt hT x
    (show 0 < ε / 2 by positivity)
  let g := windowPartitionStepPath p x
  have hpoint (t : J1Window T) : |x.1 t - g.1 t| ≤ ε / 2 := by
    by_cases htT : (t : ℝ) = T
    · have ht : t = (⟨T, hT.le, le_rfl⟩ : J1Window T) := Subtype.ext htT
      subst t
      simp only [g, windowPartitionStepPath]
      rw [windowPartitionStepFunction_at_top]
      simpa using (show 0 ≤ ε / 2 by positivity)
    · have htlt : (t : ℝ) < T := lt_of_le_of_ne t.property.2 htT
      obtain ⟨i, hleft, hright⟩ :=
        windowPartition_exists_half_open_block p t htlt
      have hstep := windowPartitionStepFunction_eq_node_of_block
        p x i t hleft hright
      have hosc : |x.1 t - x.1 (p.time i.castSucc)| ≤
          blockOscillation x (p.time i.castSucc) (p.time i.succ) := by
        apply le_csSup (blockOscillation_values_bddAbove x _ _)
        refine ⟨t, p.time i.castSucc, ?_, ?_, ?_, ?_, rfl⟩
        · exact_mod_cast hleft
        · exact_mod_cast hright
        · exact le_rfl
        · exact_mod_cast (p.strict i)
      change |x.1 t - windowPartitionStepFunction p x t| ≤ ε / 2
      rw [hstep]
      exact hosc.trans (hp i).le
  have hsup : (⨆ t : J1Window T, |x.1 t - g.1 t|) ≤ ε / 2 := by
    change sSup (Set.range fun t : J1Window T => |x.1 t - g.1 t|) ≤ _
    apply csSup_le
    · exact ⟨|x.1 ⟨0, le_rfl, hT.le⟩ - g.1 ⟨0, le_rfl, hT.le⟩|,
        ⟨⟨0, le_rfl, hT.le⟩, rfl⟩⟩
    · rintro z ⟨t, rfl⟩
      exact hpoint t
  refine ⟨p, ?_⟩
  exact (j1WindowDist_le_sup_dist hT x g).trans_lt
    (hsup.trans_lt (by linarith))


private theorem exists_rationalNodeFamily_close {T : ℝ} (hT : 0 < T)
    (x : CadlagWindow T) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : RationalNodeData T,
      j1WindowDist hT x (rationalNodeFamily hT d).path < ε := by
  have he : 0 < ε / 3 := by positivity
  obtain ⟨p, hp⟩ := exists_partitionStepPath_close hT x he
  obtain ⟨v, hv⟩ := exists_rationalValueStepPath_close hT p x he
  obtain ⟨r, hrmem, hrstrict, hrclose⟩ := exists_rationalNodeMap_close hT p he
  let d : RationalNodeData T := ⟨⟨p.n, r, v⟩, p.n_pos, hrmem, hrstrict⟩
  let q := rationalNodePartition hT d
  obtain ⟨φ, hnodes, hdisp⟩ := exists_windowPartition_nodeTimeChange hT p
    q.time q.first q.last q.strict
  have hmax : Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin (p.n + 1) => |(q.time i : ℝ) - (p.time i : ℝ)|) ≤ ε / 3 := by
    apply Finset.sup'_le
    intro i _
    exact (hrclose i).le
  have hmove : j1WindowDist hT
      (windowPartitionValueStepPath p (fun i => (v i : ℝ)))
      (windowPartitionValueStepPath q (fun i => (v i : ℝ))) ≤ ε / 3 := by
    exact windowPartitionValueStepPath_timeChange_bound hT p q.time q.first q.last
      q.strict (fun i => (v i : ℝ)) φ he.le hnodes (fun t => (hdisp t).trans hmax)
  refine ⟨d, ?_⟩
  have htri := j1WindowDist_triangle hT x (windowPartitionStepPath p x)
    (windowPartitionValueStepPath p (fun i => (v i : ℝ)))
  have htri' := j1WindowDist_triangle hT x
    (windowPartitionValueStepPath p (fun i => (v i : ℝ)))
    (windowPartitionValueStepPath q (fun i => (v i : ℝ)))
  change j1WindowDist hT x
    (windowPartitionValueStepPath q (fun i => (v i : ℝ))) < ε
  linarith only [hp, hv, hmove, htri, htri']




theorem exists_countable_dense_j1WindowD {T : ℝ} (hT : 0 < T) :
    ∃ S : Set (J1WindowD T hT), S.Countable ∧ Dense S := by
  refine ⟨Set.range (rationalNodeFamily hT), rationalNodeFamily_countable hT, ?_⟩
  apply Metric.dense_iff.mpr
  intro x ε hε
  obtain ⟨d, hd⟩ := exists_rationalNodeFamily_close hT x.path hε
  refine ⟨rationalNodeFamily hT d, ?_, ⟨d, rfl⟩⟩
  change dist (rationalNodeFamily hT d) x < ε
  rw [dist_comm]
  exact hd




instance j1WindowDSeparableSpace {T : ℝ} (hT : 0 < T) :
    TopologicalSpace.SeparableSpace (J1WindowD T hT) :=
  ⟨exists_countable_dense_j1WindowD hT⟩





instance j1WindowCircSeparableSpace {T : ℝ} (hT : 0 < T) :
    TopologicalSpace.SeparableSpace (J1WindowCirc T hT) :=
  (j1WindowCircHomeomorphD hT).symm.surjective.denseRange.separableSpace
    (j1WindowCircHomeomorphD hT).symm.continuous




instance j1WindowCircPolishSpace {T : ℝ} (hT : 0 < T) :
    PolishSpace (J1WindowCirc T hT) := by
  infer_instance




instance j1WindowDPolishSpace {T : ℝ} (hT : 0 < T) :
    PolishSpace (J1WindowD T hT) :=
  (j1WindowCircHomeomorphD hT).symm.isClosedEmbedding.polishSpace

end DirectedDistances.Probability
