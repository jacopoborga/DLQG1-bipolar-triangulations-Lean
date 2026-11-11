/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.CutWindowP1FamilyGlue
public import DirectedDistances.KMSW.HatInputAssembly
public import DirectedDistances.KMSW.HatNoFreshLeft

/-! Supporting lemmas for paper labels `lem-quad-kmsw`, `lem-sdp-tri`, `thm-busemann` (see CORRESPONDENCE.md). -/























public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory

/-- The deterministic M-hat simulation statement on the M-hat side of
sequence with flow-line hits, the exit-replaced stream supplies a
`HatImageLimitInput`. The witnesses are the limit maps of the all-stage
simulation, and the structural incidence field comes from
`noFreshLeftSource_hatCodes`. This is a graph-level identification, with no
face or rotation claim. -/
theorem hatInputExists : HatInputExists := by
  unfold HatInputExists
  intro w h
  exact hatImageLimitInput_exists_of_incident w h
    (hatCodes_allocated_nonroot_incident w h)










theorem iidCodes_ae_boundaryBusemannSDP :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∃ X : ℤ → ℤ,
          IsBoundaryBusemannSDP
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X ∧
          (∀ X' : ℤ → ℤ,
            IsBoundaryBusemannSDP
              (boundaryPresentVertex (fun i => ω (i + 1)) h) X' → X' = X) ∧
          (∀ l k : ℤ, 0 ≤ l → l < k →
            X l - X k ≤
              ((sdp (boundaryPresentVertex (fun i => ω (i + 1)) h l)
                (boundaryPresentVertex (fun i => ω (i + 1)) h k)).toNat : ℤ)) ∧
          (∀ k : ℤ, 1 ≤ k → -1 ≤ X k - X (k - 1)) :=
  iidCodes_ae_boundaryBusemannSDP_of_hatInput hatInputExists










theorem iidCodes_ae_boundaryBusemannLDP :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
          ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
            (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∃ X : ℤ → ℤ,
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X ∧
          (∀ X' : ℤ → ℤ,
            IsBoundaryBusemannLDP
              (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
              (boundaryPresentVertex (fun i => ω (i + 1)) h) X' → X' = X) ∧
          (∀ l k : ℤ, 0 ≤ l → l < k →
            ∀ hr : Reachable
              (boundaryPresentVertex (fun i => ω (i + 1)) h l)
              (boundaryPresentVertex (fun i => ω (i + 1)) h k),
              (presentLdpFiniteNat
                (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin) hr : ℤ) ≤
                X l - X k) ∧
          (∀ k : ℤ, 1 ≤ k → X k - X (k - 1) ≤ -1) :=
  iidCodes_ae_boundaryBusemannLDP_of_hatInput hatInputExists

/-- Existence and uniqueness only, for the SDP boundary Busemann function
of `M_{0,∞}`, almost surely for iid codes. This is the shape of the
candidate statement `thm_busemann_sdp` in -/
theorem iidCodes_ae_boundaryBusemannSDP_existsUnique :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∃ X : ℤ → ℤ,
          IsBoundaryBusemannSDP
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X ∧
          (∀ X' : ℤ → ℤ,
            IsBoundaryBusemannSDP
              (boundaryPresentVertex (fun i => ω (i + 1)) h) X' → X' = X) := by
  filter_upwards [iidCodes_ae_boundaryBusemannSDP] with ω hω
  obtain ⟨h, X, hX, huniq, -, -⟩ := hω
  exact ⟨h, X, hX, huniq⟩

/-- Local finiteness, then existence and uniqueness only, for the LDP
boundary Busemann function of `M_{0,∞}`, almost surely for iid codes. This
is the shape of the candidate statement `thm_busemann_ldp` in -/
theorem iidCodes_ae_boundaryBusemannLDP_existsUnique :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
          ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
            (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∃ X : ℤ → ℤ,
          IsBoundaryBusemannLDP
            (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
            (boundaryPresentVertex (fun i => ω (i + 1)) h) X ∧
          (∀ X' : ℤ → ℤ,
            IsBoundaryBusemannLDP
              (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
              (boundaryPresentVertex (fun i => ω (i + 1)) h) X' → X' = X) := by
  filter_upwards [iidCodes_ae_boundaryBusemannLDP] with ω hω
  obtain ⟨hfin, h, X, hX, huniq, -, -⟩ := hω
  exact ⟨hfin, h, X, hX, huniq⟩

end DirectedDistances.KMSW
