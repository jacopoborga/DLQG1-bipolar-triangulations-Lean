module

public import DirectedDistances.PaperProofs.Section7.CellSDPUpperOscillation
public import DirectedDistances.PaperProofs.Section7.CellSDPReverseCell

/-! The zero and one step cases, shared boundary vertices, and unreachable reversed
pairs are discharged here. Whole-cell reversal for the remaining pairs is OPEN.
No reversal obligation is asserted without a proof. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver
open DirectedDistances.KMSW

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
the lower boundary, so this boundary is nonempty for every deterministic code. -/
private theorem reversal_lower_zero (w : ℕ → Fin 3) (n : ℕ) :
    ∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
      (kmswStage w n).west e = 0 ∨ (kmswStage w n).east e = 0 := by
  have he : 0 ∈ (kmswStage w n).LR := by
    rw [kmswStage_LR_eq]
    apply List.mem_map.mpr
    refine ⟨0, ?_, rfl⟩
    simp
  have hw := (kmswStage_endpoints_stable w (Nat.zero_le n)
    (e := 0) (by change 0 < 1; omega)).1
  exact ⟨0, List.mem_append_right _ he, Or.inl hw⟩



private theorem reversal_shared_endpoint (n : ℕ) (ω : ℕ → Fin 3) (y : ℕ)
    (hy : ∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LL ++
        (kmswStage (fun i => ω (i + 1)) n).LR,
      (kmswStage (fun i => ω (i + 1)) n).west e = y ∨
        (kmswStage (fun i => ω (i + 1)) n).east e = y) :
    ∃ yr : ℕ,
      (∃ e ∈ (kmswStage (fun i => codeReversal n ω (i + 1)) n).LL ++
          (kmswStage (fun i => codeReversal n ω (i + 1)) n).LR,
        (kmswStage (fun i => codeReversal n ω (i + 1)) n).west e = yr ∨
          (kmswStage (fun i => codeReversal n ω (i + 1)) n).east e = yr) ∧
      ∀ xr : ℕ,
        (∃ e ∈ (kmswStage (fun i => codeReversal n ω (i + 1)) n).UL ++
            (kmswStage (fun i => codeReversal n ω (i + 1)) n).UR,
          (kmswStage (fun i => codeReversal n ω (i + 1)) n).west e = xr ∨
            (kmswStage (fun i => codeReversal n ω (i + 1)) n).east e = xr) →
        ∃ x : ℕ,
          (∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LL ++
              (kmswStage (fun i => ω (i + 1)) n).LR,
            (kmswStage (fun i => ω (i + 1)) n).west e = x ∨
              (kmswStage (fun i => ω (i + 1)) n).east e = x) ∧
          sdp (⟨x⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨y⟩ ≤
            sdp (⟨yr⟩ : StagePresentVertex
              (fun i => codeReversal n ω (i + 1)) n) ⟨xr⟩ := by
  refine ⟨0, reversal_lower_zero _ _, fun xr _ => ⟨y, hy, ?_⟩⟩
  rw [sdp_self]
  exact zero_le

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
uses only the coinciding single-edge upper and lower boundaries. -/
private theorem reversal_zero_endpoint (ω : ℕ → Fin 3) :
    let w := fun i => ω (i + 1)
    let wr := fun i => codeReversal 0 ω (i + 1)
    ∀ y : ℕ,
      (∃ e ∈ (kmswStage w 0).UL ++ (kmswStage w 0).UR,
        (kmswStage w 0).west e = y ∨ (kmswStage w 0).east e = y) →
      ∃ yr : ℕ,
        (∃ e ∈ (kmswStage wr 0).LL ++ (kmswStage wr 0).LR,
          (kmswStage wr 0).west e = yr ∨ (kmswStage wr 0).east e = yr) ∧
        ∀ xr : ℕ,
          (∃ e ∈ (kmswStage wr 0).UL ++ (kmswStage wr 0).UR,
            (kmswStage wr 0).west e = xr ∨ (kmswStage wr 0).east e = xr) →
          ∃ x : ℕ,
            (∃ e ∈ (kmswStage w 0).LL ++ (kmswStage w 0).LR,
              (kmswStage w 0).west e = x ∨ (kmswStage w 0).east e = x) ∧
            sdp (⟨x⟩ : StagePresentVertex w 0) ⟨y⟩ ≤
              sdp (⟨yr⟩ : StagePresentVertex wr 0) ⟨xr⟩ := by
  dsimp only
  intro y hy
  exact reversal_shared_endpoint 0 ω y hy

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
an upper endpoint outside the lower boundary. Its new edge has length one. -/
private theorem reversal_one_endpoint (ω : ℕ → Fin 3) :
    let w := fun i => ω (i + 1)
    let wr := fun i => codeReversal 1 ω (i + 1)
    ∀ y : ℕ,
      (∃ e ∈ (kmswStage w 1).UL ++ (kmswStage w 1).UR,
        (kmswStage w 1).west e = y ∨ (kmswStage w 1).east e = y) →
      ∃ yr : ℕ,
        (∃ e ∈ (kmswStage wr 1).LL ++ (kmswStage wr 1).LR,
          (kmswStage wr 1).west e = yr ∨ (kmswStage wr 1).east e = yr) ∧
        ∀ xr : ℕ,
          (∃ e ∈ (kmswStage wr 1).UL ++ (kmswStage wr 1).UR,
            (kmswStage wr 1).west e = xr ∨ (kmswStage wr 1).east e = xr) →
          ∃ x : ℕ,
            (∃ e ∈ (kmswStage w 1).LL ++ (kmswStage w 1).LR,
              (kmswStage w 1).west e = x ∨ (kmswStage w 1).east e = x) ∧
            sdp (⟨x⟩ : StagePresentVertex w 1) ⟨y⟩ ≤
              sdp (⟨yr⟩ : StagePresentVertex wr 1) ⟨xr⟩ := by
  dsimp only
  intro y hy
  classical
  by_cases hyl : ∃ e ∈ (kmswStage (fun i => ω (i + 1)) 1).LL ++
      (kmswStage (fun i => ω (i + 1)) 1).LR,
    (kmswStage (fun i => ω (i + 1)) 1).west e = y ∨
      (kmswStage (fun i => ω (i + 1)) 1).east e = y
  · exact reversal_shared_endpoint 1 ω y hyl
  have hc : ω 1 = 0 ∨ ω 1 = 1 ∨ ω 1 = 2 := by
    have hb := (ω 1).isLt
    omega
  rcases hc with hc | hc | hc
  · apply False.elim
    simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit,
      State.addEdge, hc] at hy hyl
    omega
  · have hy2 : y = 2 := by
      simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit,
        State.addEdge, hc] at hy hyl
      omega
    subst y
    have hr : codeReversal 1 ω 1 = 0 := by
      simp [codeReversal, hc]
    refine ⟨0, reversal_lower_zero _ _, fun xr hxr =>
      ⟨0, reversal_lower_zero _ _, ?_⟩⟩
    have hxr0 : xr ≠ 0 := by
      simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit,
        State.addEdge, hr] at hxr
      omega
    let e : (⟨0⟩ : StagePresentVertex (fun i => ω (i + 1)) 1) ⟶ ⟨2⟩ :=
      ⟨1, by
        simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit,
          State.addEdge, hc]⟩
    have hdist : sdp (⟨0⟩ : StagePresentVertex (fun i => ω (i + 1)) 1) ⟨2⟩ ≤ 1 :=
      sdp_le_length (Path.nil.cons e)
    apply hdist.trans
    apply Order.one_le_iff_ne_zero.mpr
    intro hz
    have heq := sdp_eq_zero_iff.mp hz
    exact hxr0 (congrArg StagePresentVertex.id heq).symm
  · apply False.elim
    simp [kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit,
      State.addEdge, hc] at hy hyl
    omega

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
restricted to sizes at least two and original upper endpoints outside the lower
boundary. Only actual reversed boundary-to-boundary paths require transport;
no assertion is made for unreachable pairs. The original lower endpoint may
depend on the reversed path. This proposition is defined, not assumed or proved. -/
@[expose] def cellSdpUpper_reversalInteriorPathTransport : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ ω : ℕ → Fin 3,
    let w := fun i => ω (i + 1)
    let wr := fun i => codeReversal n ω (i + 1)
    ∀ y : ℕ,
      (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
        (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
      (¬ ∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
        (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
      ∃ yr : ℕ,
        (∃ e ∈ (kmswStage wr n).LL ++ (kmswStage wr n).LR,
          (kmswStage wr n).west e = yr ∨ (kmswStage wr n).east e = yr) ∧
        ∀ xr : ℕ,
          (∃ e ∈ (kmswStage wr n).UL ++ (kmswStage wr n).UR,
            (kmswStage wr n).west e = xr ∨ (kmswStage wr n).east e = xr) →
          ∀ p : Path (⟨yr⟩ : StagePresentVertex wr n) ⟨xr⟩,
            ∃ x : ℕ,
              (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
                (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) ∧
              ∃ q : Path (⟨x⟩ : StagePresentVertex w n) ⟨y⟩,
                q.length ≤ p.length

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
path obligation: all omitted endpoint cases are proved, and shortest-path
attainment handles the path-dependent lower endpoint without exchanging witnesses. -/
theorem cellSdpUpper_reversalEndpointTransport_iff_interiorPathTransport :
    cellSdpUpper_reversalEndpointTransport ↔
      cellSdpUpper_reversalInteriorPathTransport := by
  classical
  constructor
  · intro h n _ ω
    dsimp only
    intro y hy _
    obtain ⟨yr, hyr, ht⟩ := h n ω y hy
    refine ⟨yr, hyr, fun xr hxr p => ?_⟩
    obtain ⟨x, hx, hd⟩ := ht xr hxr
    have hle := hd.trans (sdp_le_length p)
    have hreach : Reachable (⟨x⟩ : StagePresentVertex (fun i => ω (i + 1)) n)
        ⟨y⟩ := by
      by_contra hn
      have htop := sdp_eq_top_iff_not_reachable.mpr hn
      have hlt := lt_of_le_of_lt hle (ENat.natCast_lt_top p.length)
      rw [htop] at hlt
      exact (lt_irrefl _ hlt)
    obtain ⟨q, hq⟩ := exists_length_eq_sdp hreach
    refine ⟨x, hx, q, ENat.natCast_le_natCast.mp ?_⟩
    rw [hq]
    exact hle
  · intro h n ω
    dsimp only
    intro y hy
    by_cases hyl : ∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LL ++
        (kmswStage (fun i => ω (i + 1)) n).LR,
      (kmswStage (fun i => ω (i + 1)) n).west e = y ∨
        (kmswStage (fun i => ω (i + 1)) n).east e = y
    · exact reversal_shared_endpoint n ω y hyl
    by_cases hn : 2 ≤ n
    · obtain ⟨yr, hyr, ht⟩ := h n hn ω y hy hyl
      refine ⟨yr, hyr, fun xr hxr => ?_⟩
      by_cases hr : Reachable
          (⟨yr⟩ : StagePresentVertex (fun i => codeReversal n ω (i + 1)) n) ⟨xr⟩
      · obtain ⟨p, hp⟩ := exists_length_eq_sdp hr
        obtain ⟨x, hx, q, hq⟩ := ht xr hxr p
        refine ⟨x, hx, (sdp_le_length q).trans ?_⟩
        rw [← hp]
        exact ENat.natCast_le_natCast.mpr hq
      · refine ⟨0, reversal_lower_zero _ _, ?_⟩
        rw [sdp_eq_top_iff_not_reachable.mpr hr]
        exact le_top
    · have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with rfl | rfl
      · exact reversal_zero_endpoint ω y hy
      · exact reversal_one_endpoint ω y hy



theorem cell_sdp_upper_of_reversalInteriorPathTransport
    (h : cellSdpUpper_reversalInteriorPathTransport) : cellSdpUpperConclusion :=
  cell_sdp_upper_corrected
    (cellSdpUpper_reversalEndpointTransport_iff_interiorPathTransport.mpr h)

end DirectedDistances.PaperProofs.Section7
