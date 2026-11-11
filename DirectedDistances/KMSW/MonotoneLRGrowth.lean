module

public import DirectedDistances.KMSW.BoundaryDynamics
public import DirectedDistances.KMSW.MonotoneStepCommon
public import DirectedDistances.KMSW.MonotoneStepInvPEN
public import DirectedDistances.KMSW.CutEquivalenceConverse

/-! # Growth of the lower-right boundary list and of the layout's right end

Helper toward the plane-realization obligation of adjudication n308 (limit exterior of the
x-monotone layout); not a paper result. If the vertical coordinate `R w` is unbounded below,
the lower-right boundary list of the KMSW stages grows without bound (`lem-kmsw-bdy`(ii),
monotone stage invariants: each down-pendant step adds one edge to the lower-right list and
moves the right end by at least one, and no other step changes the list or decreases `xmax`. -/

public section
namespace DirectedDistances.KMSW

/-- If `R w` is unbounded below, the lower-right boundary list eventually exceeds every
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem kmswStage_LR_length_unbounded (w : ℕ → Fin 3) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (K : ℕ) : ∃ N, ∀ n, N ≤ n → K ≤ (kmswStage w n).LR.length := by
  obtain ⟨N, hN⟩ := hR (-(K : ℤ))
  refine ⟨N, fun n hn => ?_⟩
  have hlen := kmswStage_LR_length w n
  have hmin : minR w n ≤ R w N := runningMin_le (R w) n N hn
  have hK : (K : ℤ) ≤ ((kmswStage w n).LR.length : ℤ) := by
    rw [hlen]
    omega
  exact_mod_cast hK

private theorem step_snd_cases (c : Fin 3) :
    (RandomWalk.lazyTwoDimensionalStep c).2 = 0 ∨
      (RandomWalk.lazyTwoDimensionalStep c).2 = 1 ∨
      (c = 2 ∧ (RandomWalk.lazyTwoDimensionalStep c).2 = -1) := by
  revert c
  decide

/-- One KMSW step adds at most one edge to the lower-right boundary list, and adds none
unless it is a down step with empty upper-right list (`def-kmsw`, `lem-kmsw-bdy`(ii),
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem kmswStage_LR_length_succ (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w (n + 1)).LR.length ≤ (kmswStage w n).LR.length + 1 ∧
      (¬ (w n = 2 ∧ (kmswStage w n).UR = []) →
        (kmswStage w (n + 1)).LR.length ≤ (kmswStage w n).LR.length) := by
  have hRs : R w (n + 1) = R w n + (RandomWalk.lazyTwoDimensionalStep (w n)).2 :=
    Finset.sum_range_succ _ _
  have hmin : minR w (n + 1) = min (minR w n) (R w (n + 1)) := rfl
  have h0 := kmswStage_LR_length w n
  have h1 := kmswStage_LR_length w (n + 1)
  have hUR := kmswStage_UR_length w n
  have hle : minR w n ≤ R w n := runningMin_le (R w) n n le_rfl
  have hlow : ∀ c : ℤ, c ≤ minR w n → c ≤ R w (n + 1) → c ≤ minR w (n + 1) := by
    intro c ha hb
    rw [hmin]
    exact le_min ha hb
  rcases step_snd_cases (w n) with hs | hs | ⟨hc, hs⟩
  · have hm := hlow (minR w n) le_rfl (by rw [hRs, hs]; omega)
    exact ⟨by omega, fun _ => by omega⟩
  · have hm := hlow (minR w n) le_rfl (by rw [hRs, hs]; omega)
    exact ⟨by omega, fun _ => by omega⟩
  · have hm := hlow (minR w n - 1) (by omega) (by rw [hRs, hs]; omega)
    refine ⟨by omega, fun hnot => ?_⟩
    have hne : (kmswStage w n).UR ≠ [] := fun h => hnot ⟨hc, h⟩
    have hpos : 0 < (kmswStage w n).UR.length := by
      rcases hl : (kmswStage w n).UR with _ | ⟨a, l⟩
      · exact absurd hl hne
      · simp
    have hm' := hlow (minR w n) le_rfl (by rw [hRs, hs]; omega)
    omega

/-- Every allocated vertex lies at or left of the right end of a monotone stage invariant
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem MonotoneStageInvariant.vertex_re_le_xmax {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) (v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) : (layoutPos w n v).re ≤ G.xmax := by
  have hmem : P.pos ⟨v, hv⟩ ∈ P.image := Or.inl ⟨⟨v, hv⟩, rfl⟩
  have hb := (G.image_bounds hmem).2.1
  rwa [G.pos_layout] at hb

/-- The right end of a monotone stage invariant is the abscissa of an allocated vertex
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem MonotoneStageInvariant.xmax_eq_vertex {w : ℕ → Fin 3} {n : ℕ}
    {P : StageDrawing w n} (G : MonotoneStageInvariant w n P) :
    ∃ v, v < (kmswStage w n).nextVertex ∧ G.xmax = (layoutPos w n v).re := by
  refine ⟨_, ?_, G.xmax_eq_upper_end⟩
  apply (kmswStage_endpoints_lt_nextVertex w n _ ?_).2
  apply (kmswStage_boundary_ids_lt_nextEdge w n).2
  have hmem := List.getLast_mem (kmswStage_boundary_nonempty w n).1
  exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hmem)))

/-- The right end never decreases along a family of monotone stage invariants
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneStage_xmax_succ_mono (w : ℕ → Fin 3) (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) :
    (G n).xmax ≤ (G (n + 1)).xmax := by
  obtain ⟨v, hv, hx⟩ := (G n).xmax_eq_vertex
  have hv' : v < (kmswStage w (n + 1)).nextVertex :=
    lt_of_lt_of_le hv (CutConverse.nextVertex_mono w (Nat.le_succ n))
  have hle := (G (n + 1)).vertex_re_le_xmax v hv'
  rw [layoutPos_old_vertex w n v hv] at hle
  rw [hx]
  exact hle

/-- A down-pendant step moves the right end by at least one (`def-kmsw`,
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneStage_xmax_succ_pen (w : ℕ → Fin 3) (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) (hc : w n = 2)
    (hUR : (kmswStage w n).UR = []) : (G n).xmax + 1 ≤ (G (n + 1)).xmax := by
  have hcount := (invariant_succ_pen_counts w n hc hUR).2
  have hv : (kmswStage w n).nextVertex < (kmswStage w (n + 1)).nextVertex := by omega
  have hle := (G (n + 1)).vertex_re_le_xmax _ hv
  have hre : (layoutPos w (n + 1) (kmswStage w n).nextVertex).re =
      (layoutPos w n ((kmswStage w n).east (kmswStage w n).active)).re + 1 := by
    rw [invariant_succ_pen_new_vertex_position w n hc hUR]
  rw [hre] at hle
  rw [(G n).xmax_eq_active_east_of_UR_nil hUR]
  exact hle

/-- Along a family of monotone stage invariants the right end grows at least as fast as the
lower-right boundary list (`def-kmsw`, `lem-kmsw-bdy`(ii),
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneStage_xmax_ge_LR (w : ℕ → Fin 3) (Q : ∀ n, StageDrawing w n)
    (G : ∀ n, MonotoneStageInvariant w n (Q n)) (n : ℕ) :
    (G 0).xmax + ((kmswStage w n).LR.length : ℝ) ≤
      (G n).xmax + ((kmswStage w 0).LR.length : ℝ) := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    have hLR := kmswStage_LR_length_succ w n
    by_cases hpen : w n = 2 ∧ (kmswStage w n).UR = []
    · have hx := monotoneStage_xmax_succ_pen w Q G n hpen.1 hpen.2
      have h1 : ((kmswStage w (n + 1)).LR.length : ℝ) ≤
          (kmswStage w n).LR.length + 1 := by
        exact_mod_cast hLR.1
      linarith
    · have hx := monotoneStage_xmax_succ_mono w Q G n
      have h1 : ((kmswStage w (n + 1)).LR.length : ℝ) ≤ (kmswStage w n).LR.length := by
        exact_mod_cast hLR.2 hpen
      linarith

/-- If `R w` is unbounded below, the right end of every family of monotone stage
invariants eventually exceeds every bound (`lem-kmsw-bdy`(ii),
Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneStage_xmax_unbounded (w : ℕ → Fin 3) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n)) :
    ∀ b : ℝ, ∃ N, ∀ n, N ≤ n → b ≤ (G n).xmax := by
  intro b
  obtain ⟨K, hK⟩ := exists_nat_ge (b - (G 0).xmax + (kmswStage w 0).LR.length)
  obtain ⟨N, hN⟩ := kmswStage_LR_length_unbounded w hR K
  refine ⟨N, fun n hn => ?_⟩
  have h1 := monotoneStage_xmax_ge_LR w Q G n
  have h2 : (K : ℝ) ≤ (kmswStage w n).LR.length := by exact_mod_cast hN n hn
  linarith

end DirectedDistances.KMSW
