module

public import DirectedDistances.PaperProofs.Section7.CellSDPUpperReversal2
public import DirectedDistances.PaperProofs.Section7.CellSDPUpperReversal
public import DirectedDistances.PaperProofs.Section7.CellSDPReversalLaw
public import DirectedDistances.KMSW.StageSubgraph

/-! Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
of the reversal correspondence is open, so this file does not prove Lemma 7.8. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver
open DirectedDistances.KMSW

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
stage reversal correspondence, with boundary membership defined by edge endpoints. -/
@[expose] def cellSdpRevCorr (w wr : ℕ → Fin 3) (n : ℕ) (φ : ℕ → ℕ) : Prop :=
  (∀ e < (kmswStage wr n).nextEdge, (kmswStage wr n).present e = true →
    ∃ f < (kmswStage w n).nextEdge, (kmswStage w n).present f = true ∧
      (kmswStage w n).west f = φ ((kmswStage wr n).east e) ∧
      (kmswStage w n).east f = φ ((kmswStage wr n).west e)) ∧
  (∀ y, (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
      (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
    ¬ (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
      (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
    ∃ yr, (∃ e ∈ (kmswStage wr n).LL ++ (kmswStage wr n).LR,
      (kmswStage wr n).west e = yr ∨ (kmswStage wr n).east e = yr) ∧
      φ yr = y) ∧
  (∀ x, (∃ e ∈ (kmswStage wr n).UL ++ (kmswStage wr n).UR,
      (kmswStage wr n).west e = x ∨ (kmswStage wr n).east e = x) →
    ∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
      (kmswStage w n).west e = φ x ∨ (kmswStage w n).east e = φ x)

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
stage vertices and preserves their lengths. -/
private theorem revCorrPath_vertices (w wr : ℕ → Fin 3) (n : ℕ) (φ : ℕ → ℕ)
    (hA : ∀ e < (kmswStage wr n).nextEdge,
      (kmswStage wr n).present e = true →
      ∃ f < (kmswStage w n).nextEdge, (kmswStage w n).present f = true ∧
        (kmswStage w n).west f = φ ((kmswStage wr n).east e) ∧
        (kmswStage w n).east f = φ ((kmswStage wr n).west e))
    {a b : StagePresentVertex wr n} (p : Path a b) :
    ∃ q : Path (⟨φ b.id⟩ : StagePresentVertex w n) ⟨φ a.id⟩,
      q.length = p.length := by
  induction p with
  | nil => exact ⟨Path.nil, rfl⟩
  | @cons b' c p e ih =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨f, hf, hfp, hfw, hfe⟩ :=
      hA e.val e.property.1 e.property.2.1
    let f' : (⟨φ c.id⟩ : StagePresentVertex w n) ⟶ ⟨φ b'.id⟩ :=
      ⟨f, hf, hfp, by rw [hfw, e.property.2.2.2],
        by rw [hfe, e.property.2.2.1]⟩
    refine ⟨(Hom.toPath f').comp q, ?_⟩
    rw [Path.length_comp, Path.length_toPath, hq, Path.length_cons]
    omega

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
so the reversed path has the same length. -/
theorem cellSdpRevCorr_path (w wr : ℕ → Fin 3) (n : ℕ) (φ : ℕ → ℕ)
    (hA : ∀ e < (kmswStage wr n).nextEdge,
      (kmswStage wr n).present e = true →
      ∃ f < (kmswStage w n).nextEdge, (kmswStage w n).present f = true ∧
        (kmswStage w n).west f = φ ((kmswStage wr n).east e) ∧
        (kmswStage w n).east f = φ ((kmswStage wr n).west e))
    {a b : ℕ} (p : Path (⟨a⟩ : StagePresentVertex wr n) ⟨b⟩) :
    ∃ q : Path (⟨φ b⟩ : StagePresentVertex w n) ⟨φ a⟩,
      q.length = p.length := by
  let va : StagePresentVertex wr n := ⟨a⟩
  let vb : StagePresentVertex wr n := ⟨b⟩
  obtain ⟨q, hq⟩ := revCorrPath_vertices w wr n φ hA
    (a := va) (b := vb) p
  exact ⟨q, hq⟩

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
relevant stage, then the shortest-exit transport obligation follows. This remains
conditional: existence of the correspondence is open. -/
theorem cellSdpUpper_reversalShortestExitTransport_of_revCorr
    (h : ∀ n, 4 ≤ n → ∀ ω : ℕ → Fin 3,
      ∃ φ, cellSdpRevCorr (fun i => ω (i + 1))
        (fun i => codeReversal n ω (i + 1)) n φ) :
    cellSdpUpper_reversalShortestExitTransport := by
  intro n hn ω
  dsimp only
  intro y hy hyl
  obtain ⟨φ, hφ⟩ := h n hn ω
  obtain ⟨yr, hyr, hyrφ⟩ := hφ.2.1 y hy hyl
  subst y
  refine ⟨yr, hyr, fun xr hxr p _ => ?_⟩
  obtain ⟨q, hq⟩ := cellSdpRevCorr_path _ _ _ _ hφ.1 p
  exact ⟨φ xr, hφ.2.2 xr hxr, q, le_of_eq hq⟩

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
shortest-exit equivalence. Since existence of the correspondence is open, this does
not prove Lemma 7.8. -/
theorem cell_sdp_upper_of_revCorr
    (h : ∀ n, 4 ≤ n → ∀ ω : ℕ → Fin 3,
      ∃ φ, cellSdpRevCorr (fun i => ω (i + 1))
        (fun i => codeReversal n ω (i + 1)) n φ) :
    cellSdpUpperConclusion := by
  apply cell_sdp_upper_of_reversalInteriorPathTransport
  exact cellSdpUpper_reversalInteriorPathTransport_iff_shortestExitTransport.mpr
    (cellSdpUpper_reversalShortestExitTransport_of_revCorr h)

end DirectedDistances.PaperProofs.Section7
