/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.BusemannM0Unconditional

/-! # A canonical code-space representative of the LDP boundary Busemann function

The definition below chooses the eventual value of finite LDP differences along a
common reachable boundary sequence. The eventual-value characterization is the
uses the law of its increments and independence from the first step in the
`prop:LDP-recursive-equation`). This file supplies a code-space representative
of the almost-surely unique function. It is a helper, not a paper statement. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW
open Quiver MeasureTheory

/-- Existence of the auxiliary data under which the canonical LDP limit is
defined. -/
@[expose]
def HasIidBoundaryLdpData (ω : ℕ → Fin 3) : Prop :=
  ∃ hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
      ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
        (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite,
    ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
      True

/-- The value selected from an eventually constant integer sequence, with
zero as a default when no eventual value exists. -/
@[expose] noncomputable def eventualIntegerValue (f : ℕ → ℤ) : ℤ := by
  classical
  exact if hval : ∃ z : ℤ, ∃ N, ∀ j, N ≤ j → f j = z then
    Classical.choose hval
  else 0

/-- The selected eventual value agrees with every eventual tail value. -/
theorem eventualIntegerValue_eq (f : ℕ → ℤ) (x : ℤ)
    (hx : ∃ N, ∀ j, N ≤ j → f j = x) :
    eventualIntegerValue f = x := by
  classical
  unfold eventualIntegerValue
  let hval : ∃ z : ℤ, ∃ N, ∀ j, N ≤ j → f j = z := ⟨x, hx⟩
  rw [dif_pos hval]
  obtain ⟨N, hN⟩ := hx
  obtain ⟨M, hM⟩ := Classical.choose_spec hval
  have heq := hM (max N M) (le_max_right N M)
  have hx' := hN (max N M) (le_max_left N M)
  exact heq.symm.trans hx'

/-- The finite-distance limit from fixed LDP data, following the -/
@[expose] noncomputable def canonicalBusemannLDPFromData
    (ω : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
      ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
        (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (k : ℤ) : ℤ := by
  classical
  let hseq := boundaryEnumeration_commonSequence (fun i => ω (i + 1)) h 0 k
  let y := Classical.choose hseq
  let hy := Classical.choose_spec hseq
  let f : ℕ → ℤ := fun j =>
    (presentLdpFiniteNat
      (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
      (hy.2 j).2 : ℤ) -
      (presentLdpFiniteNat
        (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
        (hy.2 j).1 : ℤ)
  exact eventualIntegerValue f

/-- The finite-distance limit recovers the Busemann function supplied by its
characterization. -/
theorem canonicalBusemannLDPFromData_eq
    (ω : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
      ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
        (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (X : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP
      (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
      (boundaryPresentVertex (fun i => ω (i + 1)) h)
      X)
    (k : ℤ) :
    canonicalBusemannLDPFromData ω hfin h k = X k := by
  classical
  let hseq := boundaryEnumeration_commonSequence (fun i => ω (i + 1)) h 0 k
  let y := Classical.choose hseq
  let hy := Classical.choose_spec hseq
  let f : ℕ → ℤ := fun j =>
    (presentLdpFiniteNat
      (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
      (hy.2 j).2 : ℤ) -
      (presentLdpFiniteNat
        (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
        (hy.2 j).1 : ℤ)
  obtain ⟨N, hN⟩ := hX.2 0 k y hy.1 hy.2
  have hstable : ∀ j, N ≤ j → f j = X k := by
    intro j hj
    have heq := hN j hj
    have hzero : X k - X 0 = X k := by rw [hX.1]; simp
    calc
      f j = X k - X 0 := heq.symm
      _ = X k := hzero
  change eventualIntegerValue f = X k
  exact eventualIntegerValue_eq f (X k) ⟨N, hstable⟩

/-- The canonical LDP boundary Busemann value at index `k`, defined from the
code sequence alone as the eventual difference of finite LDP distances to a
common reachable boundary sequence. The value is `0` junk if `HasIidBoundaryLdpData ω` fails, or if the finite differences along the chosen sequence are not eventually constant. Its only meaning is via `canonicalBusemannLDP_eq_of_data` and `iidCodes_ae_existsUnique_eq_canonicalBusemannLDP`. It is a choice-defined representative, not a paper statement, and must not appear in a paper-facing statement without that characterization. This
is a helper definition. -/
@[expose] noncomputable def canonicalBusemannLDP (ω : ℕ → Fin 3) (k : ℤ) : ℤ := by
  classical
  by_cases hgood : HasIidBoundaryLdpData ω
  · exact canonicalBusemannLDPFromData ω
      (Classical.choose hgood)
      (Classical.choose (Classical.choose_spec hgood))
      k
  · exact 0

/-- Under fixed LDP data, the code-space selector agrees with the supplied
Busemann function. -/
theorem canonicalBusemannLDP_eq_of_data
    (ω : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
      ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
        (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (X : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP
      (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
      (boundaryPresentVertex (fun i => ω (i + 1)) h) X)
    (k : ℤ) : canonicalBusemannLDP ω k = X k := by
  classical
  have hgood : HasIidBoundaryLdpData ω := ⟨hfin, h, True.intro⟩
  unfold canonicalBusemannLDP
  simp only [dif_pos hgood]
  exact canonicalBusemannLDPFromData_eq ω hfin h X hX k

/-- Almost surely the unique LDP boundary Busemann function agrees with the
code-defined canonical representative. The Busemann characterization is
Measurability is not proved here (open). -/
theorem iidCodes_ae_existsUnique_eq_canonicalBusemannLDP :
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
          X = canonicalBusemannLDP ω := by
  filter_upwards [iidCodes_ae_boundaryBusemannLDP] with ω hω
  obtain ⟨hfin, h, X, hX, huniq, -, -⟩ := hω
  refine ⟨hfin, h, X, hX, huniq, ?_⟩
  funext k
  exact (canonicalBusemannLDP_eq_of_data ω hfin h X hX k).symm

end DirectedDistances.Recursive
