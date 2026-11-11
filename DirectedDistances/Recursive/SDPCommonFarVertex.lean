module

public import DirectedDistances.Recursive.BusemannCommonFarVertex
public import DirectedDistances.KMSW.BusemannM0Unconditional
import Mathlib.Order.Filter.Finite

/-! # A common far vertex for the two SDP Busemann functions

Helpers for `lem:SDP-relating-X1-X`, specifically `eqn-SDP-relating-w`
`thm-busemann` is synchronized over the finite window in both maps, using
`boundary_rightTail_common_shift` unchanged to supply a common sequence.

These are helpers on the hit-indexed exploration carrier, subject to the
and the `thm-busemann` data. Every SDP value converted with `toNat` has
reachable endpoints, hence is finite by `present_sdp_ne_top`. The underlying
SDP retains the value `+∞` on unreachable pairs. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver MeasureTheory Filter

private theorem window_sdp_eventually {w : ℕ → Fin 3}
    (x : ℤ → PresentVertex w) (X : ℤ → ℤ)
    (hX : IsBoundaryBusemannSDP x X)
    (s : Finset ℤ) (y : ℕ → PresentVertex w) (hy : Function.Injective y)
    (hr : ∀ k ∈ s, ∀ j, Reachable (x k) (y j)) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ k (_hk : k ∈ s) k' (_hk' : k' ∈ s),
      ((sdp (x k') (y j)).toNat : ℤ) -
        ((sdp (x k) (y j)).toNat : ℤ) = X k' - X k := by
  have hh : ∀ᶠ j : ℕ in atTop,
      ∀ k k' : {k : ℤ // k ∈ s},
        ((sdp (x k'.val) (y j)).toNat : ℤ) -
          ((sdp (x k.val) (y j)).toNat : ℤ) = X k'.val - X k.val := by
    apply eventually_all.mpr
    intro k
    apply eventually_all.mpr
    intro k'
    obtain ⟨N, hN⟩ := hX.2 k.val k'.val y hy
      (fun j => ⟨hr k.val k.property j, hr k'.val k'.property j⟩)
    exact eventually_atTop.mpr ⟨N, fun j hj => (hN j hj).symm⟩
  exact eventually_atTop.mp (hh.mono fun j hj k hk k' hk' => hj ⟨k, hk⟩ ⟨k', hk'⟩)

private theorem reachable_target_allocated {w : ℕ → Fin 3}
    {a b : PresentVertex w} (ha : kmswVertexAllocated w a)
    (hr : Reachable a b) : kmswVertexAllocated w b := by
  obtain ⟨p⟩ := hr
  cases p with
  | nil => exact ha
  | cons p e =>
    obtain ⟨n, hn, _⟩ := e.property.1
    have hb := (kmswStage_endpoints_lt_nextVertex w n e.val hn).2
    rw [(edge_endpoints_eq w hn).2, e.property.2.2] at hb
    exact ⟨n, hb⟩

/-- Finite synchronization of the SDP characterization of `thm-busemann`:
along a common reachable injective sequence, both maps satisfy all the
identities of `eqn-SDP-relating-w` eventually, with a single threshold.
Helper for `lem:SDP-relating-X1-X`
The reachability hypotheses ensure every SDP value below is finite. -/
theorem boundaryBusemannSDP_commonFarVertex_eventually
    (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (1 + i)))
    (X0 X1 : ℤ → ℤ)
    (hX0 : IsBoundaryBusemannSDP (boundaryPresentVertex w h0) X0)
    (hX1 : IsBoundaryBusemannSDP
      (boundaryPresentVertex (fun i => w (1 + i)) h1) X1)
    (y : ℕ → PresentVertex (fun i => w (1 + i)))
    (hy : Function.Injective y)
    (hr0 : ∀ k ∈ Finset.Icc (-2 : ℤ) 2, ∀ j,
      Reachable (boundaryPresentVertex w h0 k) (shiftLimitVertex w 1 (y j)))
    (hr1 : ∀ k ∈ Finset.Icc (-2 : ℤ) 2, ∀ j,
      Reachable (boundaryPresentVertex (fun i => w (1 + i)) h1 k) (y j)) :
    ∃ N : ℕ, ∀ j, N ≤ j →
      (∀ k (_hk : k ∈ Finset.Icc (-2 : ℤ) 2)
          k' (_hk' : k' ∈ Finset.Icc (-2 : ℤ) 2),
        ((sdp (boundaryPresentVertex w h0 k') (shiftLimitVertex w 1 (y j))).toNat : ℤ) -
          ((sdp (boundaryPresentVertex w h0 k) (shiftLimitVertex w 1 (y j))).toNat : ℤ) =
            X0 k' - X0 k) ∧
      (∀ k (_hk : k ∈ Finset.Icc (-2 : ℤ) 2)
          k' (_hk' : k' ∈ Finset.Icc (-2 : ℤ) 2),
        ((sdp (boundaryPresentVertex (fun i => w (1 + i)) h1 k') (y j)).toNat : ℤ) -
          ((sdp (boundaryPresentVertex (fun i => w (1 + i)) h1 k) (y j)).toNat : ℤ) =
            X1 k' - X1 k) := by
  have ha : ∀ j, kmswVertexAllocated (fun i => w (1 + i)) (y j) := by
    intro j
    exact reachable_target_allocated (boundaryVertex_allocated _ h1 0)
      (hr1 0 (by decide) j)
  have hy0 : Function.Injective (fun j => shiftLimitVertex w 1 (y j)) := by
    intro i j hij
    exact hy (shiftLimitVertex_injective w 1 (ha i) (ha j) hij)
  obtain ⟨N0, hN0⟩ := window_sdp_eventually _ X0 hX0 _ _ hy0 hr0
  obtain ⟨N1, hN1⟩ := window_sdp_eventually _ X1 hX1 _ _ hy hr1
  exact ⟨max N0 N1, fun j hj =>
    ⟨hN0 j ((Nat.le_max_left _ _).trans hj),
      hN1 j ((Nat.le_max_right _ _).trans hj)⟩⟩

/-- A common shifted vertex realizes both finite families of SDP Busemann
differences. This is the deterministic `eqn-SDP-relating-w` helper for
`lem:SDP-relating-X1-X`, obtained from `thm-busemann`'s characterization
Reachability witnesses keep all distances in the differences finite. -/
theorem boundaryBusemannSDP_commonFarVertex (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (1 + i)))
    (X0 X1 : ℤ → ℤ)
    (hX0 : IsBoundaryBusemannSDP (boundaryPresentVertex w h0) X0)
    (hX1 : IsBoundaryBusemannSDP
      (boundaryPresentVertex (fun i => w (1 + i)) h1) X1) :
    ∃ z : PresentVertex (fun i => w (1 + i)),
      kmswVertexAllocated (fun i => w (1 + i)) z ∧
      ∃ (_hr0 : ∀ k ∈ Finset.Icc (-2 : ℤ) 2,
          Reachable (boundaryPresentVertex w h0 k) (shiftLimitVertex w 1 z))
        (_hr1 : ∀ k ∈ Finset.Icc (-2 : ℤ) 2,
          Reachable (boundaryPresentVertex (fun i => w (1 + i)) h1 k) z),
      (∀ k (_hk : k ∈ Finset.Icc (-2 : ℤ) 2)
          k' (_hk' : k' ∈ Finset.Icc (-2 : ℤ) 2),
        ((sdp (boundaryPresentVertex w h0 k') (shiftLimitVertex w 1 z)).toNat : ℤ) -
          ((sdp (boundaryPresentVertex w h0 k) (shiftLimitVertex w 1 z)).toNat : ℤ) =
            X0 k' - X0 k) ∧
      (∀ k (_hk : k ∈ Finset.Icc (-2 : ℤ) 2)
          k' (_hk' : k' ∈ Finset.Icc (-2 : ℤ) 2),
        ((sdp (boundaryPresentVertex (fun i => w (1 + i)) h1 k') z).toNat : ℤ) -
          ((sdp (boundaryPresentVertex (fun i => w (1 + i)) h1 k) z).toNat : ℤ) =
            X1 k' - X1 k) := by
  obtain ⟨B, hy, ha, hr0, hr1⟩ := boundary_rightTail_common_shift w h0 h1
  obtain ⟨N, hN⟩ := boundaryBusemannSDP_commonFarVertex_eventually
    w h0 h1 X0 X1 hX0 hX1 _ hy hr0 hr1
  exact ⟨_, ha N, (fun k hk => hr0 k hk N), (fun k hk => hr1 k hk N), hN N le_rfl⟩

private theorem ae_comp_one_codeShift {p : (ℕ → Fin 3) → Prop}
    (hp : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, p ω) :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, p (RandomWalk.codeShift 1 ω) := by
  have hp' : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure.map (RandomWalk.codeShift 1), p ω := by
    simpa only [RandomWalk.map_codeShift] using hp
  exact (Measure.tendsto_ae_map
    (RandomWalk.measurable_codeShift 1).aemeasurable).eventually hp'

/-- Almost surely, the SDP Busemann functions for `ω(i+1)` and `ω(i+2)`
have a common shifted vertex realizing all differences in `[-2,2]`.
The second code is written `w(1+i)` to match the limit embedding.
Shift invariance applies `iidCodes_ae_boundaryBusemannSDP` twice.
Helper for `lem:SDP-relating-X1-X` and `eqn-SDP-relating-w`
the `thm-busemann` data apply. All converted SDP values are reachable. -/
theorem iidCodes_ae_boundaryBusemannSDP_commonFarVertex :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ h0 : BoundaryHitWitnesses w,
      ∃ h1 : BoundaryHitWitnesses (fun i => w (1 + i)),
      ∃ X0 X1 : ℤ → ℤ,
        IsBoundaryBusemannSDP (boundaryPresentVertex w h0) X0 ∧
        IsBoundaryBusemannSDP
          (boundaryPresentVertex (fun i => w (1 + i)) h1) X1 ∧
        ∃ z : PresentVertex (fun i => w (1 + i)),
          kmswVertexAllocated (fun i => w (1 + i)) z ∧
          ∃ (_hr0 : ∀ k ∈ Finset.Icc (-2 : ℤ) 2,
              Reachable (boundaryPresentVertex w h0 k) (shiftLimitVertex w 1 z))
            (_hr1 : ∀ k ∈ Finset.Icc (-2 : ℤ) 2,
              Reachable (boundaryPresentVertex (fun i => w (1 + i)) h1 k) z),
          (∀ k (_hk : k ∈ Finset.Icc (-2 : ℤ) 2)
              k' (_hk' : k' ∈ Finset.Icc (-2 : ℤ) 2),
            ((sdp (boundaryPresentVertex w h0 k') (shiftLimitVertex w 1 z)).toNat : ℤ) -
              ((sdp (boundaryPresentVertex w h0 k) (shiftLimitVertex w 1 z)).toNat : ℤ) =
                X0 k' - X0 k) ∧
          (∀ k (_hk : k ∈ Finset.Icc (-2 : ℤ) 2)
              k' (_hk' : k' ∈ Finset.Icc (-2 : ℤ) 2),
            ((sdp (boundaryPresentVertex (fun i => w (1 + i)) h1 k') z).toNat : ℤ) -
              ((sdp (boundaryPresentVertex (fun i => w (1 + i)) h1 k) z).toNat : ℤ) =
                X1 k' - X1 k) := by
  have hs := ae_comp_one_codeShift iidCodes_ae_boundaryBusemannSDP
  filter_upwards [iidCodes_ae_boundaryBusemannSDP, hs] with ω hω hsω
  have heq : (fun i => RandomWalk.codeShift 1 ω (i + 1)) =
      (fun i => ω ((1 + i) + 1)) := by
    funext i
    change (if i + 1 = 0 then 0 else ω (1 + (i + 1))) = ω ((1 + i) + 1)
    rw [ite_eq_right (by omega : ¬ i + 1 = 0)]
    rfl
  rw [heq] at hsω
  obtain ⟨h0, X0, hX0, -, -, -⟩ := hω
  obtain ⟨h1, X1, hX1, -, -, -⟩ := hsω
  refine ⟨h0, h1, X0, X1, hX0, hX1, ?_⟩
  exact boundaryBusemannSDP_commonFarVertex (fun i => ω (i + 1))
    h0 h1 X0 X1 hX0 hX1

end DirectedDistances.Recursive
