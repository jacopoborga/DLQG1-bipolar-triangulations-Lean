module

public import DirectedDistances.Recursive.LDPRelatingAssembly
public import DirectedDistances.Recursive.BusemannCommonFarVertex

/-! # First-step relations for the LDP boundary Busemann functions

Helper forms of `lem:LDP-relating-X1-X` and `eqn-ldp-relating1-3`
The common far vertex is supplied by the proved Busemann characterization;
only finite distances on reachable pairs are subtracted.

the hit-indexed boundary labelling, the almost-sure interpretation, and
the identification of the exploration graph with the paper's map remain -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver MeasureTheory

private theorem boundary_pair_of_busemann
    (w : ℕ → Fin 3)
    (hb0 : PresentPathLengthsBounded (w := w))
    (hb1 : PresentPathLengthsBounded (w := fun i => w (1 + i)))
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (1 + i)))
    (X0 X1 : ℤ → ℤ)
    (hX0 : IsBoundaryBusemannLDP hb0 (boundaryPresentVertex w h0) X0)
    (hX1 : IsBoundaryBusemannLDP hb1
      (boundaryPresentVertex (fun i => w (1 + i)) h1) X1) :
    (w 0 = 2 → (X0 (-1), X0 1) =
      (X1 (-2) - max (X1 (-1)) 1, -max (X1 (-1)) 1)) ∧
    (w 0 = 0 → (X0 (-1), X0 1) = (-X1 1 - 1, -1)) ∧
    (w 0 = 1 → (X0 (-1), X0 1) = (X1 (-1), X1 2)) := by
  obtain ⟨z, hz, hr0, hr1, hc0, hc1⟩ :=
    boundaryBusemannLDP_commonFarVertex w hb0 hb1 h0 h1 X0 X1 hX0 hX1
  have h1' : BoundaryHitWitnesses (fun i => w (i + 1)) := by
    simpa only [Nat.add_comm] using h1
  have hr0' : ∀ k : ℤ, k ∈ Set.Icc (-2 : ℤ) 2 →
      Reachable (⟨boundaryVertex w h0 k⟩ : PresentVertex w)
        (shiftLimitVertex w 1 z) := by
    intro k hk
    exact hr0 k (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hk)
  have hr1' : ∀ k : ℤ, k ∈ Set.Icc (-2 : ℤ) 2 →
      Reachable (⟨boundaryVertex (fun i => w (i + 1)) h1' k⟩ :
        PresentVertex (fun i => w (1 + i))) z := by
    intro k hk
    simpa only [boundaryPresentVertex, Nat.add_comm] using
      hr1 k (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hk)
  apply firstStep_boundary_pair_of_common_vertex w h0 h1' hb0 hb1 z hz
    hr0' hr1' X0 X1 hX0.1 hX1.1
  constructor
  · intro k k' hk hk'
    exact hc0 k (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hk)
      k' (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hk')
  · intro k k' hk hk'
    simpa only [Nat.add_comm, boundaryPresentVertex] using
      hc1 k (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hk)
        k' (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hk')

private theorem ae_comp_one_codeShift {p : (ℕ → Fin 3) → Prop}
    (hp : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, p ω) :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, p (RandomWalk.codeShift 1 ω) := by
  have hp' : ∀ᵐ ω ∂RandomWalk.iidCodeMeasure.map (RandomWalk.codeShift 1), p ω := by
    simpa only [RandomWalk.map_codeShift] using hp
  exact (Measure.tendsto_ae_map
    (RandomWalk.measurable_codeShift 1).aemeasurable).eventually hp'

/-- Almost-sure iid-code helper for `lem:LDP-relating-X1-X`, with both
normalized LDP Busemann functions and their uniqueness, followed by
`w i = ω (i + 1)`, so the first step is `ω 1`; codes `2`, `0`, `1`
represent `(1,-1)`, `(-1,0)`, `(0,1)`, respectively. The second map uses
the F1/F4 qualifications in the module docstring apply. -/
theorem iidCodes_ae_ldp_relating_X1_X :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ hfin0 : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
      ∃ hfin1 : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => w (1 + i)) n).nextEdge ∧
          ((kmswStage (fun i => w (1 + i)) n).west e = v ∨
            (kmswStage (fun i => w (1 + i)) n).east e = v)}.Finite,
      ∃ h0 : BoundaryHitWitnesses w,
      ∃ h1 : BoundaryHitWitnesses (fun i => w (1 + i)),
      ∃ X0 X1 : ℤ → ℤ,
        IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin0)
          (boundaryPresentVertex w h0) X0 ∧
        IsBoundaryBusemannLDP
          (presentPathLengthsBounded_of_hfin (fun i => w (1 + i)) hfin1)
          (boundaryPresentVertex (fun i => w (1 + i)) h1) X1 ∧
        (∀ X0' : ℤ → ℤ,
          IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin0)
            (boundaryPresentVertex w h0) X0' → X0' = X0) ∧
        (∀ X1' : ℤ → ℤ,
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin (fun i => w (1 + i)) hfin1)
            (boundaryPresentVertex (fun i => w (1 + i)) h1) X1' → X1' = X1) ∧
        (ω 1 = 2 → (X0 (-1), X0 1) =
          (X1 (-2) - max (X1 (-1)) 1, -max (X1 (-1)) 1)) ∧
        (ω 1 = 0 → (X0 (-1), X0 1) = (-X1 1 - 1, -1)) ∧
        (ω 1 = 1 → (X0 (-1), X0 1) = (X1 (-1), X1 2)) := by
  have hs := ae_comp_one_codeShift iidCodes_ae_boundaryBusemannLDP_existsUnique
  filter_upwards [iidCodes_ae_boundaryBusemannLDP_existsUnique, hs] with ω hω hsω
  have heq : (fun i => RandomWalk.codeShift 1 ω (i + 1)) =
      (fun i => ω ((1 + i) + 1)) := by
    funext i
    change (if i + 1 = 0 then 0 else ω (1 + (i + 1))) = ω ((1 + i) + 1)
    rw [ite_eq_right (by omega : ¬ i + 1 = 0)]
    rfl
  rw [heq] at hsω
  obtain ⟨hfin0, h0, X0, hX0, hu0⟩ := hω
  obtain ⟨hfin1, h1, X1, hX1, hu1⟩ := hsω
  refine ⟨hfin0, hfin1, h0, h1, X0, X1, hX0, hX1, hu0, hu1, ?_⟩
  exact boundary_pair_of_busemann (fun i => ω (i + 1))
    (presentPathLengthsBounded_of_hfin _ hfin0)
    (presentPathLengthsBounded_of_hfin _ hfin1) h0 h1 X0 X1 hX0 hX1

/-- Simultaneous version of the iid-code helper for
`lem:LDP-relating-X1-X`, `eqn-ldp-relating1-3`
both Busemann functions exist and the three formulas hold for every pair
satisfying their characterizations. Uniqueness identifies each such pair
with the witnesses in `iidCodes_ae_ldp_relating_X1_X`. The F1/F4 -/
theorem iidCodes_ae_ldp_relating_X1_X_all :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ hfin0 : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
      ∃ hfin1 : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => w (1 + i)) n).nextEdge ∧
          ((kmswStage (fun i => w (1 + i)) n).west e = v ∨
            (kmswStage (fun i => w (1 + i)) n).east e = v)}.Finite,
      ∃ h0 : BoundaryHitWitnesses w,
      ∃ h1 : BoundaryHitWitnesses (fun i => w (1 + i)),
        (∃ X0 : ℤ → ℤ,
          IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin0)
            (boundaryPresentVertex w h0) X0) ∧
        (∃ X1 : ℤ → ℤ,
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin (fun i => w (1 + i)) hfin1)
            (boundaryPresentVertex (fun i => w (1 + i)) h1) X1) ∧
        ∀ X0' X1' : ℤ → ℤ,
          IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin0)
            (boundaryPresentVertex w h0) X0' →
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin (fun i => w (1 + i)) hfin1)
            (boundaryPresentVertex (fun i => w (1 + i)) h1) X1' →
          (ω 1 = 2 → (X0' (-1), X0' 1) =
            (X1' (-2) - max (X1' (-1)) 1, -max (X1' (-1)) 1)) ∧
          (ω 1 = 0 → (X0' (-1), X0' 1) = (-X1' 1 - 1, -1)) ∧
          (ω 1 = 1 → (X0' (-1), X0' 1) = (X1' (-1), X1' 2)) := by
  filter_upwards [iidCodes_ae_ldp_relating_X1_X] with ω hω
  obtain ⟨hfin0, hfin1, h0, h1, X0, X1, hX0, hX1, hu0, hu1, hp⟩ := hω
  refine ⟨hfin0, hfin1, h0, h1, ⟨X0, hX0⟩, ⟨X1, hX1⟩, ?_⟩
  intro X0' X1' hX0' hX1'
  obtain rfl := hu0 X0' hX0'
  obtain rfl := hu1 X1' hX1'
  exact hp

end DirectedDistances.Recursive
