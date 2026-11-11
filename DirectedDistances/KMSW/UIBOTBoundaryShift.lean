module

public import DirectedDistances.KMSW.BoundaryAEExistence
public import DirectedDistances.KMSW.UIBOTBoundaryM0
public import DirectedDistances.KMSW.KMSWShiftAllTimes
public import DirectedDistances.KMSW.DirectedContainLaw1

/-! # One-sided iid boundary properties after deterministic shifts

The full finite-stage boundary package and the source/sink clauses of
`lem-uibot-bdy` transfer to every deterministic shift of the iid code word
the iid combinatorial carrier is one-sided. This file does not include the
rightmost-path coalescence clause or identify these edges with those of
`M_{-∞,∞}`.

The inherited LL clause uses the older k - 1 indexing and covers missing edges x_j - x_{j+1} only for j <= -2; it omits x_{-1} - x_0. The corrected clause is in UIBOTBoundaryAssembly (n = 0). -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open scoped Classical

/-- The random tail code word beginning after coordinate `n` has the same law
as the ordinary random tail code word. This follows from stationarity of the
iid code measure under `RandomWalk.codeShift` (`lem-directed-contain`, -/
theorem iidCodeMeasure_map_shiftedTail (n : ℕ) :
    RandomWalk.iidCodeMeasure.map (fun ω : ℕ → Fin 3 => fun i => ω (n + i + 1)) =
      RandomWalk.iidCodeMeasure.map (fun ω => fun i => ω (i + 1)) := by
  let tail : (ℕ → Fin 3) → (ℕ → Fin 3) := fun ω i => ω (i + 1)
  have htail : Measurable tail := by
    exact measurable_pi_iff.mpr fun i => measurable_pi_apply (i + 1)
  have hcomp : (fun ω : ℕ → Fin 3 => fun i => ω (n + i + 1)) =
      tail ∘ RandomWalk.codeShift n := by
    funext ω i
    simp [tail, RandomWalk.codeShift, Nat.add_assoc]
  rw [hcomp, ← Measure.map_map htail (RandomWalk.measurable_codeShift n),
    RandomWalk.map_codeShift]

private theorem ae_comp_codeShift {p : (ℕ → Fin 3) → Prop} (n : ℕ)
    (h : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, p ω) :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, p (RandomWalk.codeShift n ω) := by
  have hp : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure.map (RandomWalk.codeShift n), p ω := by
    simpa only [RandomWalk.map_codeShift] using h
  exact (Measure.tendsto_ae_map
    (RandomWalk.measurable_codeShift n).aemeasurable).eventually hp

/-- Almost surely, simultaneously for every `n ≥ 0`, the shifted one-sided
code word `w i = ω (n + i + 1)` has the full finite-stage boundary properties
of `iidCodes_ae_boundaryProperties`, has no allocated sinks, and has exactly
the left-boundary sources of `iidCodes_ae_sources` (`lem-uibot-bdy`,
combinatorial model. The boundary witness, finite-incidence condition,
right/left boundary edge clauses, source characterization, and common
reachable sequence are transferred. This statement does not include
rightmost-path coalescence or the identification with `M_{-∞,∞}`; negative
shifts are not defined on this carrier. The inherited LL clause uses the older k - 1 indexing and covers missing edges x_j - x_{j+1} only for j <= -2; it omits x_{-1} - x_0. The corrected clause is in UIBOTBoundaryAssembly (n = 0). -/
theorem iidCodes_ae_uibotBoundary_allTimes :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, ∀ n : ℕ,
      let w := fun i => ω (n + i + 1)
      (∃ _hfin : ∀ v : ℕ,
          {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
            ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite,
        ∃ h : BoundaryHitWitnesses w,
          Function.Injective (boundaryVertex w h) ∧
          (kmswStage w 0).LR = [0] ∧
          (kmswStage w 0).west 0 = boundaryVertex w h 0 ∧
          (kmswStage w 0).east 0 = boundaryVertex w h 1 ∧
          (kmswStage w 0).present 0 = true ∧
          (∀ k : ℤ, 1 ≤ k →
            ∃ N, boundaryHitTime w h k ≤ N ∧
              ∀ m, N ≤ m →
                act w (boundaryHitTime w h k) ∈ (kmswStage w m).LR ∧
                (kmswStage w m).present (act w (boundaryHitTime w h k)) = true ∧
                (kmswStage w m).west (act w (boundaryHitTime w h k)) =
                  boundaryVertex w h k ∧
                (kmswStage w m).east (act w (boundaryHitTime w h k)) =
                  boundaryVertex w h (k + 1)) ∧
          (∀ k : ℤ, k ≤ -1 →
            let e := kmswLLCreatedEdge w (boundaryHitTime w h (k - 1));
            (kmswStage w (boundaryHitTime w h (k - 1))).west e =
              boundaryVertex w h (k - 1) ∧
            (kmswStage w (boundaryHitTime w h (k - 1))).east e =
              boundaryVertex w h k ∧
            (kmswStage w (boundaryHitTime w h (k - 1))).present e = false) ∧
          (∀ v : ℕ,
            (∃ m e, (e ∈ (kmswStage w m).LL ∨ e ∈ (kmswStage w m).LR) ∧
              ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)) →
            ∃ k : ℤ, boundaryVertex w h k = v) ∧
          (∀ v : ℕ,
            (∃ m, v < (kmswStage w m).nextVertex) →
              ((¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
                ∃ k : ℤ, k ≤ 0 ∧ v = boundaryVertex w h k)) ∧
          (∀ v : ℕ,
            (∃ m, v < (kmswStage w m).nextVertex) →
              ∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
          BusemannCommonSequenceHypothesis
            (fun k : ℤ => (⟨boundaryVertex w h k⟩ : PresentVertex w))) ∧
      (∀ v : ℕ,
        (∃ m, v < (kmswStage w m).nextVertex) →
          ∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
      (∃ h : BoundaryHitWitnesses w, ∀ v : ℕ,
        (∃ m, v < (kmswStage w m).nextVertex) →
          ((¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
            ∃ k : ℤ, k ≤ 0 ∧ v = boundaryVertex w h k)) := by
  rw [ae_all_iff]
  intro n
  have hb := ae_comp_codeShift n iidCodes_ae_boundaryProperties
  have hn := ae_comp_codeShift n iidCodes_ae_no_sink
  have hs := ae_comp_codeShift n iidCodes_ae_sources
  simp only [RandomWalk.codeShift] at hb hn hs
  filter_upwards [hb, hn, hs] with ω hboundary hnosink hsources
  exact ⟨hboundary, hnosink, hsources⟩

/-- Under the all-times shifted simulation, the shifted root edge maps to the
global active edge at the shift time `t` (`def-kmsw`, -/
theorem kmswShift_root_edge_maps_to_active (w : ℕ → Fin 3) (t : ℕ) :
    kmswShiftEdgeMapAll w t 0 0 = act w t := by
  change kmswShiftEdgeMapAll w t 0
      (kmswStage (fun i => w (t + i)) 0).active =
    (kmswStage w (t + 0)).active
  exact (kmswShift_sim2_all w t 0).sim.active

/-- A shifted positive-index boundary LR edge maps to a present edge of the
global limit graph, with its endpoints given by the shifted vertex map. The
finite-stage edge is taken at a stage where `boundaryVertex_right_edge`
certifies its LR membership and presence (`lem-uibot-bdy`, -/
theorem kmswShift_rightBoundary_edge_maps_present
    (w : ℕ → Fin 3) (t : ℕ)
    (h : BoundaryHitWitnesses (fun i => w (t + i)))
    {k : ℤ} (hk : 1 ≤ k) :
    let u := fun i => w (t + i)
    ∃ N, boundaryHitTime u h k ≤ N ∧
      EdgePresent w
        (kmswShiftEdgeMapAll w t N (act u (boundaryHitTime u h k))) ∧
      edgeWest w (kmswShiftEdgeMapAll w t N (act u (boundaryHitTime u h k))) =
        kmswShiftVertexMapAll w t N (boundaryVertex u h k) ∧
      edgeEast w (kmswShiftEdgeMapAll w t N (act u (boundaryHitTime u h k))) =
        kmswShiftVertexMapAll w t N (boundaryVertex u h (k + 1)) := by
  let u : ℕ → Fin 3 := fun i => w (t + i)
  obtain ⟨N, hN, hright⟩ := boundaryVertex_right_edge u h hk
  have hstage := hright N le_rfl
  let e := act u (boundaryHitTime u h k)
  have he : e < (kmswStage u N).nextEdge := by
    dsimp [e]
    exact act_lt_nextEdge u hN
  have hmap := kmswShift_present_edge_maps w t N e he hstage.2.1
  have hwest : edgeWest u e = boundaryVertex u h k := by
    calc
      edgeWest u e = (kmswStage u N).west e := (edge_endpoints_eq u he).1.symm
      _ = boundaryVertex u h k := hstage.2.2.1
  have heast : edgeEast u e = boundaryVertex u h (k + 1) := by
    calc
      edgeEast u e = (kmswStage u N).east e := (edge_endpoints_eq u he).2.symm
      _ = boundaryVertex u h (k + 1) := hstage.2.2.2
  refine ⟨N, hN, hmap.1, ?_, ?_⟩
  · simpa [u, e, hwest] using hmap.2.1
  · simpa [u, e, heast] using hmap.2.2

end DirectedDistances.KMSW
