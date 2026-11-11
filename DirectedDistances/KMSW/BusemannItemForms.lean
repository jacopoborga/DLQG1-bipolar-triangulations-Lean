/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BusemannM0Unconditional









public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory

/-- Helper form of `lem-sdp-tri`
the finiteness needed for the `toNat` distance expression. This is not an -/
theorem lem_sdp_tri :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∀ (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (X : ℤ → ℤ),
        IsBoundaryBusemannSDP
          (boundaryPresentVertex (fun i => ω (i + 1)) h) X →
        ∀ l k : ℤ, 0 ≤ l → l < k →
          Reachable (boundaryPresentVertex (fun i => ω (i + 1)) h l)
            (boundaryPresentVertex (fun i => ω (i + 1)) h k) ∧
          X l - X k ≤
            ((sdp (boundaryPresentVertex (fun i => ω (i + 1)) h l)
              (boundaryPresentVertex (fun i => ω (i + 1)) h k)).toNat : ℤ) := by
  filter_upwards [iidCodes_ae_boundaryBusemannSDP] with ω hω
  obtain ⟨h0, X0, hX0, huniq, htri, _⟩ := hω
  intro h X hX
  have hh : h = h0 := Subsingleton.elim _ _
  subst h
  have hXeq : X = X0 := huniq X hX
  subst X
  intro l k hl hlk
  refine ⟨boundaryVertex_nonneg_reachable _ h0 hl hlk.le, ?_⟩
  exact htri l k hl hlk

/-- Helper form of item-busemann-pos in the SDP case
almost-sure SDP function; it does not close the joint
`thm-busemann-property`. The F1/F4 caveats in -/
theorem item_busemann_pos_sdp :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∀ (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (X : ℤ → ℤ),
        IsBoundaryBusemannSDP
          (boundaryPresentVertex (fun i => ω (i + 1)) h) X →
        ∀ k : ℤ, 1 ≤ k → -1 ≤ X k - X (k - 1) := by
  filter_upwards [iidCodes_ae_boundaryBusemannSDP] with ω hω
  obtain ⟨h0, X0, hX0, huniq, _, hpos⟩ := hω
  intro h X hX
  have hh : h = h0 := Subsingleton.elim _ _
  subst h
  have hXeq : X = X0 := huniq X hX
  subst X
  exact hpos

/-- Helper form of item-busemann-pos in the LDP case
finiteness witness; proof irrelevance identifies every other such witness.
This proves only this item, not the joint `thm-busemann-property`. The F1/F4 -/
theorem item_busemann_pos_ldp :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∀ (hfin : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
          ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
            (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite)
        (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (X : ℤ → ℤ),
        IsBoundaryBusemannLDP
          (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
          (boundaryPresentVertex (fun i => ω (i + 1)) h) X →
        ∀ k : ℤ, 1 ≤ k → X k - X (k - 1) ≤ -1 := by
  filter_upwards [iidCodes_ae_boundaryBusemannLDP] with ω hω
  obtain ⟨hfin0, h0, X0, hX0, huniq, _, hpos⟩ := hω
  intro hfin h X hX
  have hhfin : hfin = hfin0 := Subsingleton.elim _ _
  subst hfin
  have hh : h = h0 := Subsingleton.elim _ _
  subst h
  have hXeq : X = X0 := huniq X hX
  subst X
  exact hpos

end DirectedDistances.KMSW
