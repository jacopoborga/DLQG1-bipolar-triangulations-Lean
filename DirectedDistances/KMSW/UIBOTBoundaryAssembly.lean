module

public import DirectedDistances.KMSW.BoundaryAEExistence
public import DirectedDistances.KMSW.RightmostStability

/-! # Combined almost-sure UIBOT boundary lemma (`n = 0`)

combinatorial carrier. General `n` (via the shift embedding) and the
identification of the LR / LL chains with the rightmost / leftmost paths of
`m_{-∞,∞}` are not proved here. -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open scoped Classical

/-- Almost surely, for `w = fun i => ω (i + 1)`, with one common boundary witness
`h`: the boundary structure (present root edge `(x₀, x₁)`, present LR edges
`x_k → x_{k+1}` for `k ≥ 1`, for every `k ≤ -1` the missing LL edge created at
`boundaryHitTime w h k` joins `x_k, x_{k+1}` (so `k = -1` gives `x_{-1} - x₀`),
injectivity of `k ↦ x_k`), every allocated vertex has a present outgoing edge,
an allocated vertex has no present incoming edge iff it is some `x_k` with
`k ≤ 0`, and the last component proves coalescence of the LEAST-ID outgoing
paths (`RightmostStability`) from any two boundary vertices. Their
identification with the geometric rightmost paths of `lem-uibot-bdy` is not
proved (see `KMSW/RightBoundaryRightmost.lean` and `KMSW/RightmostBridge.lean`,
open). -/
theorem iidCodes_ae_uibotBoundary :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ hfin : ∀ v : ℕ,
          {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
            ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∃ h : BoundaryHitWitnesses w,
          (Function.Injective (boundaryVertex w h) ∧
            (kmswStage w 0).LR = [0] ∧
            (kmswStage w 0).west 0 = boundaryVertex w h 0 ∧
            (kmswStage w 0).east 0 = boundaryVertex w h 1 ∧
            (kmswStage w 0).present 0 = true ∧
            (∀ k : ℤ, 1 ≤ k →
              ∃ N, boundaryHitTime w h k ≤ N ∧
                ∀ n, N ≤ n →
                  act w (boundaryHitTime w h k) ∈ (kmswStage w n).LR ∧
                  (kmswStage w n).present (act w (boundaryHitTime w h k)) = true ∧
                  (kmswStage w n).west (act w (boundaryHitTime w h k)) =
                    boundaryVertex w h k ∧
                  (kmswStage w n).east (act w (boundaryHitTime w h k)) =
                    boundaryVertex w h (k + 1)) ∧
            (∀ k : ℤ, k ≤ -1 →
              let e := kmswLLCreatedEdge w (boundaryHitTime w h k);
              (kmswStage w (boundaryHitTime w h k)).west e =
                boundaryVertex w h k ∧
              (kmswStage w (boundaryHitTime w h k)).east e =
                boundaryVertex w h (k + 1) ∧
              (kmswStage w (boundaryHitTime w h k)).present e = false)) ∧
          (∀ v : ℕ,
            (∃ n, v < (kmswStage w n).nextVertex) →
              ∃ e, EdgePresent w e ∧ edgeWest w e = v) ∧
          (∀ v : ℕ,
            (∃ n, v < (kmswStage w n).nextVertex) →
              ((¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
                ∃ k : ℤ, k ≤ 0 ∧ v = boundaryVertex w h k)) ∧
          (∀ k k' : ℤ, ∃ i j, 0 < i ∧ 0 < j ∧ ∀ t,
            ((kmswM0RightmostPathOfFiniteIncidence w hfin h.R_unbounded_below
              (boundaryVertex w h k)).initial (i + t)).1.id =
            ((kmswM0RightmostPathOfFiniteIncidence w hfin h.R_unbounded_below
              (boundaryVertex w h k')).initial (j + t)).1.id) := by
  filter_upwards [iidCodes_ae_boundaryProperties,
    iidCodes_ae_boundaryRightmostPaths_coalesce] with ω hp hc
  obtain ⟨_, h1, hinj, hLR, hw, he, hpr, hright, _, _, hsrc, hsink, _⟩ := hp
  obtain ⟨hfin, h2, hco⟩ := hc
  have hh : h1 = h2 := Subsingleton.elim _ _
  subst hh
  exact ⟨hfin, h1, ⟨hinj, hLR, hw, he, hpr, hright,
    fun k hk => boundaryVertex_left_missing_edge _ h1 hk⟩, hsink, hsrc, hco⟩

end DirectedDistances.KMSW
