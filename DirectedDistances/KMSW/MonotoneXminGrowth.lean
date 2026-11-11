module

public import DirectedDistances.KMSW.MonotoneLRGrowth
public import DirectedDistances.KMSW.MonotoneStepInvLFR
public import DirectedDistances.KMSW.MonotoneLimitExternalDarts
public import Mathlib.Data.Nat.Count

/-! Supporting lemmas for paper labels `def-kmsw` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.KMSW



theorem MonotoneStageInvariant.xmin_le_vertex_re {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) (v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) : G.xmin ≤ (layoutPos w n v).re := by
  have hmem : P.pos ⟨v, hv⟩ ∈ P.image := Or.inl ⟨⟨v, hv⟩, rfl⟩
  have hb := (G.image_bounds hmem).1
  rwa [G.pos_layout] at hb



theorem MonotoneStageInvariant.xmin_eq_vertex {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∃ v, v < (kmswStage w n).nextVertex ∧ G.xmin = (layoutPos w n v).re := by
  refine ⟨_, ?_, G.xmin_eq_upper_start⟩
  apply (kmswStage_endpoints_lt_nextVertex w n _ ?_).1
  apply (kmswStage_boundary_ids_lt_nextEdge w n).2
  have hmem := List.head_mem (kmswStage_boundary_nonempty w n).1
  exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hmem)))



theorem monotoneStage_xmin_succ_anti (w : ℕ → Fin 3) (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) :
    (G (n + 1)).xmin ≤ (G n).xmin := by
  obtain ⟨v, hv, hx⟩ := (G n).xmin_eq_vertex
  have hv' : v < (kmswStage w (n + 1)).nextVertex :=
    lt_of_lt_of_le hv (CutConverse.nextVertex_mono w (Nat.le_succ n))
  have hle := (G (n + 1)).xmin_le_vertex_re v hv'
  rw [layoutPos_old_vertex w n v hv] at hle
  rw [hx]
  exact hle



theorem monotoneStage_xmin_succ_lfr (w : ℕ → Fin 3) (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) (hc : w n = 0)
    (hUL : (kmswStage w n).UL.dropLast.reverse = []) :
    (G (n + 1)).xmin + 1 ≤ (G n).xmin := by
  have hcount := (invariant_succ_lfr_counts w n hc hUL).2
  have hv : (kmswStage w n).nextVertex < (kmswStage w (n + 1)).nextVertex := by omega
  have hle := (G (n + 1)).xmin_le_vertex_re _ hv
  have hrank := invariant_succ_lfr_new_vertex_rank w n hc hUL
  rw [(G n).xmin_eq_active_west_of_UL_dropLast_reverse_nil hUL]
  linarith



@[expose] noncomputable def freshLeftCount (w : ℕ → Fin 3) (n : ℕ) : ℕ :=
  @Nat.count (fun k => w k = 0 ∧ (kmswStage w k).UL.dropLast.reverse = [])
    (Classical.decPred _) n



theorem monotoneStage_xmin_le_count (w : ℕ → Fin 3) (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) :
    (G n).xmin + (freshLeftCount w n : ℝ) ≤ (G 0).xmin := by
  classical
  induction n with
  | zero => simp [freshLeftCount]
  | succ n ih =>
    by_cases h : w n = 0 ∧ (kmswStage w n).UL.dropLast.reverse = []
    · have hs : freshLeftCount w (n + 1) = freshLeftCount w n + 1 := by
        unfold freshLeftCount
        rw [Nat.count_succ]
        simp [h]
      have hx := monotoneStage_xmin_succ_lfr w Q G n h.1 h.2
      rw [hs]
      push_cast
      linarith
    · have hs : freshLeftCount w (n + 1) = freshLeftCount w n := by
        unfold freshLeftCount
        rw [Nat.count_succ]
        simp only [h, ↓reduceIte, add_zero]
      have hx := monotoneStage_xmin_succ_anti w Q G n
      rw [hs]
      linarith



theorem freshLeftCount_unbounded (w : ℕ → Fin 3) (hinf : InfinitelyManyFreshLeft w)
    (K : ℕ) : ∃ N, ∀ n, N ≤ n → K ≤ freshLeftCount w n := by
  classical
  obtain ⟨t, hts, htc⟩ := hinf.exists_subset_card_eq K
  refine ⟨t.sup id + 1, fun n hn => ?_⟩
  have hsub : t ⊆ (Finset.range n).filter
      (fun k => w k = 0 ∧ (kmswStage w k).UL.dropLast.reverse = []) := by
    intro k hk
    have hkS := hts hk
    have hkle : k ≤ t.sup id := Finset.le_sup (f := id) hk
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hkS⟩
  have hcard := Finset.card_le_card hsub
  unfold freshLeftCount
  rw [Nat.count_eq_card_filter_range]
  convert hcard using 2
  · exact htc.symm
  · ext x
    simp only [Finset.mem_filter]



theorem monotoneStage_xmin_unbounded_below (w : ℕ → Fin 3) (hinf : InfinitelyManyFreshLeft w)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n)) :
    ∀ b : ℝ, ∃ N, ∀ n, N ≤ n → (G n).xmin ≤ b := by
  intro b
  obtain ⟨K, hK⟩ := exists_nat_ge ((G 0).xmin - b)
  obtain ⟨N, hN⟩ := freshLeftCount_unbounded w hinf K
  refine ⟨N, fun n hn => ?_⟩
  have h1 := monotoneStage_xmin_le_count w Q G n
  have h2 : (K : ℝ) ≤ freshLeftCount w n := by exact_mod_cast hN n hn
  linarith

end DirectedDistances.KMSW
