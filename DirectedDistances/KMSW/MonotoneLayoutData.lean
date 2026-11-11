module

public import DirectedDistances.KMSW.StageIncidenceChains
public import Mathlib.Analysis.Complex.Basic
import DirectedDistances.KMSW.CutEquivalenceConverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.KMSW
open scoped BigOperators



@[expose] noncomputable def layoutHeight (w : ℕ → Fin 3) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, v =>
    if v = (kmswStage w n).nextVertex ∧
        (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex + 1
    then (n + 1 : ℕ) else layoutHeight w n v



@[expose] noncomputable def layoutPos (w : ℕ → Fin 3) (n v : ℕ) : ℂ :=
  ⟨(kmswStageRank w n v : ℝ), layoutHeight w n v⟩



theorem layoutRank_old_vertex (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    kmswStageRank w (n + 1) v = kmswStageRank w n v := by
  have hne : v ≠ (kmswStage w n).nextVertex := by omega
  simp [kmswStageRank, hne]



theorem layoutHeight_old_vertex (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    layoutHeight w (n + 1) v = layoutHeight w n v := by
  have hne : v ≠ (kmswStage w n).nextVertex := by omega
  simp [layoutHeight, hne]



theorem layoutPos_old_vertex (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    layoutPos w (n + 1) v = layoutPos w n v := by
  simp only [layoutPos, layoutRank_old_vertex w n v hv, layoutHeight_old_vertex w n v hv]



theorem layoutHeight_nonneg (w : ℕ → Fin 3) (n v : ℕ) :
    0 ≤ layoutHeight w n v := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    simp only [layoutHeight]
    split
    · positivity
    · exact ih

private theorem height_le_stage (w : ℕ → Fin 3) (n v : ℕ) :
    layoutHeight w n v ≤ n := by
  induction n with
  | zero => simp only [layoutHeight, Nat.cast_zero, le_refl]
  | succ n ih =>
    simp only [layoutHeight]
    split
    · exact le_refl _
    · exact ih.trans (by exact_mod_cast Nat.le_succ n)



theorem layoutHeight_le (w : ℕ → Fin 3) (n v : ℕ)
    (_hv : v < (kmswStage w n).nextVertex) :
    layoutHeight w n v ≤ n :=
  height_le_stage w n v



theorem layoutHeight_created_vertex (w : ℕ → Fin 3) (n : ℕ)
    (hgrow : (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex + 1) :
    layoutHeight w (n + 1) (kmswStage w n).nextVertex = (n + 1 : ℕ) := by
  simp [layoutHeight, hgrow]

private theorem nextVertex_le_succ (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w (n + 1)).nextVertex ≤ (kmswStage w n).nextVertex + 1 := by
  rw [kmswStage, kmswStep]
  cases kmswCodeStep (w n) with
  | down =>
    cases hs : (kmswStage w n).UR <;> simp [kmswStepOfStep, hs, State.addEdge]
  | left =>
    cases hs : (kmswStage w n).UL.dropLast.reverse <;>
      simp [kmswStepOfStep, hs, State.addEdge]
  | up => simp [kmswStepOfStep, State.addEdge]

private theorem new_vertex_eq (w : ℕ → Fin 3) (n v : ℕ)
    (hv : v < (kmswStage w (n + 1)).nextVertex)
    (hold : ¬v < (kmswStage w n).nextVertex) :
    v = (kmswStage w n).nextVertex ∧
      (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex + 1 := by
  have hb := nextVertex_le_succ w n
  omega



theorem layoutPos_injective (w : ℕ → Fin 3) (n : ℕ) :
    ∀ v v', v < (kmswStage w n).nextVertex → v' < (kmswStage w n).nextVertex →
      layoutPos w n v = layoutPos w n v' → v = v' := by
  induction n with
  | zero =>
    intro v v' hv hv' h
    change v < 2 at hv
    change v' < 2 at hv'
    have hr := congrArg Complex.re h
    have hcases : (v = 0 ∨ v = 1) ∧ (v' = 0 ∨ v' = 1) := by omega
    rcases hcases with ⟨h0 | h1, h0' | h1'⟩ <;>
      subst_vars <;> first | rfl | norm_num [layoutPos, kmswStageRank] at hr
  | succ n ih =>
    intro v v' hv hv' h
    by_cases ho : v < (kmswStage w n).nextVertex
    · by_cases ho' : v' < (kmswStage w n).nextVertex
      · rw [layoutPos_old_vertex w n v ho, layoutPos_old_vertex w n v' ho'] at h
        exact ih v v' ho ho' h
      · obtain ⟨heq, hgrow⟩ := new_vertex_eq w n v' hv' ho'
        have hh := congrArg Complex.im h
        change layoutHeight w (n + 1) v = layoutHeight w (n + 1) v' at hh
        rw [layoutHeight_old_vertex w n v ho, heq,
          layoutHeight_created_vertex w n hgrow] at hh
        have hb := height_le_stage w n v
        push_cast at hh
        linarith
    · obtain ⟨heq, hgrow⟩ := new_vertex_eq w n v hv ho
      by_cases ho' : v' < (kmswStage w n).nextVertex
      · have hh := congrArg Complex.im h
        change layoutHeight w (n + 1) v = layoutHeight w (n + 1) v' at hh
        rw [layoutHeight_old_vertex w n v' ho', heq,
          layoutHeight_created_vertex w n hgrow] at hh
        have hb := height_le_stage w n v'
        push_cast at hh
        linarith
      · exact heq.trans (new_vertex_eq w n v' hv' ho').1.symm



@[expose] def freshEdges (w : ℕ → Fin 3) (n : ℕ) : Finset ℕ :=
  Finset.Ico (kmswStage w n).nextEdge (kmswStage w (n + 1)).nextEdge

private theorem rank_gap_pos (w : ℕ → Fin 3) (n e : ℕ)
    (he : e < (kmswStage w n).nextEdge) :
    0 < (kmswStageRank w n ((kmswStage w n).east e) : ℝ) -
      (kmswStageRank w n ((kmswStage w n).west e) : ℝ) := by
  apply sub_pos.mpr
  exact_mod_cast kmswStageRank_strict w n e he



@[expose] noncomputable def freshRampBudget (w : ℕ → Fin 3) (n : ℕ) : ℝ :=
  ∑ e ∈ freshEdges w n, 2 * (n + 1 : ℝ) /
    ((kmswStageRank w (n + 1) ((kmswStage w (n + 1)).east e) : ℝ) -
      (kmswStageRank w (n + 1) ((kmswStage w (n + 1)).west e) : ℝ))

private theorem freshRampBudget_nonneg (w : ℕ → Fin 3) (n : ℕ) :
    0 ≤ freshRampBudget w n := by
  apply Finset.sum_nonneg
  intro e he
  have he' := (Finset.mem_Ico.mp he).2
  exact div_nonneg (by positivity) (rank_gap_pos w (n + 1) e he').le





@[expose] noncomputable def rampSlope (w : ℕ → Fin 3) : ℕ → ℝ
  | 0 => 1 + 2 + freshRampBudget w 0
  | n + 1 => rampSlope w n + 1 + (n + 3 : ℝ) + freshRampBudget w (n + 1)



theorem rampSlope_pos (w : ℕ → Fin 3) (n : ℕ) : 0 < rampSlope w n := by
  induction n with
  | zero =>
    have hb := freshRampBudget_nonneg w 0
    simp only [rampSlope]
    linarith
  | succ n ih =>
    have hb := freshRampBudget_nonneg w (n + 1)
    simp only [rampSlope]
    positivity



theorem rampSlope_lt (w : ℕ → Fin 3) {m n : ℕ} (hmn : m < n) :
    rampSlope w m < rampSlope w n := by
  apply strictMono_nat_of_lt_succ (f := rampSlope w) ?_ hmn
  intro k
  have hb := freshRampBudget_nonneg w (k + 1)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [rampSlope]
  linarith



theorem rampSlope_roof_lt (w : ℕ → Fin 3) (n : ℕ) :
    (n + 1 : ℝ) < rampSlope w n := by
  cases n with
  | zero =>
    have hb := freshRampBudget_nonneg w 0
    simp only [rampSlope, Nat.cast_zero]
    linarith
  | succ n =>
    have hb := freshRampBudget_nonneg w (n + 1)
    have hp := rampSlope_pos w n
    simp only [rampSlope, Nat.cast_add, Nat.cast_one]
    linarith

private theorem freshRampBudget_lt (w : ℕ → Fin 3) (n : ℕ) :
    freshRampBudget w n < rampSlope w n := by
  cases n with
  | zero => simp only [rampSlope]; linarith
  | succ n =>
    have hp := rampSlope_pos w n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [rampSlope]
    linarith

private theorem fresh_edge_term_lt (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ freshEdges w n) :
    2 * (n + 1 : ℝ) /
      ((kmswStageRank w (n + 1) ((kmswStage w (n + 1)).east e) : ℝ) -
        (kmswStageRank w (n + 1) ((kmswStage w (n + 1)).west e) : ℝ)) <
      rampSlope w n := by
  apply lt_of_le_of_lt (b := freshRampBudget w n) ?_ (freshRampBudget_lt w n)
  apply Finset.single_le_sum ?_ he
  intro f hf
  have hf' := (Finset.mem_Ico.mp hf).2
  exact div_nonneg (by positivity) (rank_gap_pos w (n + 1) f hf').le



theorem freshEdges_endpoint_heights (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ freshEdges w n) :
    (layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)).im ≤ (n + 1 : ℝ) ∧
      (layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)).im ≤ (n + 1 : ℝ) := by
  have he' := (Finset.mem_Ico.mp he).2
  have hb := kmswStage_endpoints_lt_nextVertex w (n + 1) e he'
  constructor
  · simpa only [layoutPos, Nat.cast_add, Nat.cast_one] using
      layoutHeight_le w (n + 1) _ hb.1
  · simpa only [layoutPos, Nat.cast_add, Nat.cast_one] using
      layoutHeight_le w (n + 1) _ hb.2



theorem freshEdges_ramp_widths_lt (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ freshEdges w n) :
    ((n + 1 : ℝ) - (layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)).im) /
        rampSlope w n +
      ((n + 1 : ℝ) - (layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)).im) /
        rampSlope w n <
      (layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)).re -
        (layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)).re := by
  have he' := (Finset.mem_Ico.mp he).2
  have hg := rank_gap_pos w (n + 1) e he'
  have ht := (div_lt_iff₀ hg).mp (fresh_edge_term_lt w n e he)
  have hw := layoutHeight_nonneg w (n + 1) ((kmswStage w (n + 1)).west e)
  have hh := layoutHeight_nonneg w (n + 1) ((kmswStage w (n + 1)).east e)
  simp only [layoutPos]
  rw [← add_div]
  apply (div_lt_iff₀ (rampSlope_pos w n)).mpr
  nlinarith only [ht, hw, hh]

private theorem fresh_left_missing_endpoints (w : ℕ → Fin 3) (n : ℕ)
    (hleft : w n = 0) (hfresh : (kmswStage w n).UL.dropLast.reverse = []) :
    (kmswStage w (n + 1)).west ((kmswStage w n).nextEdge + 1) =
        (kmswStage w n).nextVertex ∧
      (kmswStage w (n + 1)).east ((kmswStage w n).nextEdge + 1) =
        (kmswStage w n).west (kmswStage w n).active ∧
      (kmswStage w (n + 1)).nextVertex = (kmswStage w n).nextVertex + 1 := by
  simp [kmswStage, kmswStep, kmswCodeStep, hleft, kmswStepOfStep, hfresh,
    State.addEdge]

/-- The new missing side in a fresh-left `def-kmsw` step has horizontal gap one
obligation of adjudication n308; not a paper result. -/
theorem freshLeft_missing_edge_rank_gap (w : ℕ → Fin 3) (n : ℕ)
    (hleft : w n = 0) (hfresh : (kmswStage w n).UL.dropLast.reverse = []) :
    let e := (kmswStage w n).nextEdge + 1
    let a := layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)
    let b := layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)
    b.re - a.re = 1 := by
  obtain ⟨hw, he, _⟩ := fresh_left_missing_endpoints w n hleft hfresh
  have hv := (kmswStage_endpoints_lt_nextVertex w n (kmswStage w n).active
    (kmswStage_boundary_ids_lt_nextEdge w n).1).1
  have hr : kmswStageRank w (n + 1) (kmswStage w n).nextVertex =
      kmswStageRank w n ((kmswStage w n).west (kmswStage w n).active) - 1 := by
    simp [kmswStageRank, hleft, hfresh]
  dsimp only
  rw [hw, he]
  simp only [layoutPos, layoutRank_old_vertex w n _ hv, hr, Rat.cast_sub, Rat.cast_one]
  ring

/-- The new missing side in a fresh-left `def-kmsw` step has vertical gap at most
obligation of adjudication n308; not a paper result. -/
theorem freshLeft_missing_edge_height_gap_le (w : ℕ → Fin 3) (n : ℕ)
    (hleft : w n = 0) (hfresh : (kmswStage w n).UL.dropLast.reverse = []) :
    let e := (kmswStage w n).nextEdge + 1
    let a := layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)
    let b := layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)
    |b.im - a.im| ≤ (n + 1 : ℝ) := by
  obtain ⟨hw, he, hgrow⟩ := fresh_left_missing_endpoints w n hleft hfresh
  have hv := (kmswStage_endpoints_lt_nextVertex w n (kmswStage w n).active
    (kmswStage_boundary_ids_lt_nextEdge w n).1).1
  have hnonneg := layoutHeight_nonneg w n ((kmswStage w n).west (kmswStage w n).active)
  have hbound := height_le_stage w n ((kmswStage w n).west (kmswStage w n).active)
  dsimp only
  rw [hw, he]
  simp only [layoutPos, layoutHeight_old_vertex w n _ hv,
    layoutHeight_created_vertex w n hgrow, Nat.cast_add, Nat.cast_one]
  apply abs_le.mpr
  constructor <;> linarith only [hnonneg, hbound]

/-- Every roof slope from time `n` onward dominates the straight new missing side
the plane-realization obligation of adjudication n308; not a paper result. -/
theorem freshLeft_missing_edge_slope_lt (w : ℕ → Fin 3) (n m : ℕ)
    (hleft : w n = 0) (hfresh : (kmswStage w n).UL.dropLast.reverse = [])
    (hnm : n ≤ m) :
    let e := (kmswStage w n).nextEdge + 1
    let a := layoutPos w (n + 1) ((kmswStage w (n + 1)).west e)
    let b := layoutPos w (n + 1) ((kmswStage w (n + 1)).east e)
    |b.im - a.im| / (b.re - a.re) < rampSlope w m := by
  dsimp only
  rw [freshLeft_missing_edge_rank_gap w n hleft hfresh, div_one]
  have hgap := freshLeft_missing_edge_height_gap_le w n hleft hfresh
  have hroof := rampSlope_roof_lt w n
  have hmono : rampSlope w n ≤ rampSlope w m := by
    rcases hnm.eq_or_lt with heq | hlt
    · exact heq ▸ le_refl _
    · exact (rampSlope_lt w hlt).le
  exact hgap.trans_lt (hroof.trans_le hmono)

end DirectedDistances.KMSW
