/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusCorrectedDecoder
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusClassAE
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusIndexFree
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55LeftObservable

/-! Formalization-internal reader correction for Lemma 5.5, not a manuscript
change. No paper-completion claim is made. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "LPlusCode" =>
  (ℕ → Fin 3) × (ℕ → Option FiniteThinMap) × (ℕ → Fin 3)

/-- Helper toward Lemma 5.5. Read the corrected decoder-4 side class when a
nonnegative-index source witness exists; absent guards return `none`. -/
@[expose] noncomputable def LPlusSidePresentation.classOptionAt4
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x) :
    Option GeometricSideClass :=
  if hk : 0 ≤ k then
    if hw : Nonempty (LPlusSidePresentationSourceWitness x k r) then
      let s := Classical.choice hw
      some (geometricSideClass
        (lPlusCodeBlockSide4 (W := s.W) (h := s.h) (k := k) (H := s.H)
          (hLL := s.hLL) (longest := s.longest) s.hτ s.hp s.P s.hqMode
          s.Tpath s.hfin s.hleft hk))
    else none
  else none

/-- Helper toward Lemma 5.5. On a source-witness guard, the corrected reader
returns that witness's decoder-4 code-block class. -/
theorem LPlusSidePresentation.classOptionAt4_eq_some
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x) (hk : 0 ≤ k)
    (hw : Nonempty (LPlusSidePresentationSourceWitness x k r)) :
    LPlusSidePresentation.classOptionAt4 x k r =
      some (geometricSideClass
        (lPlusCodeBlockSide4 (W := (Classical.choice hw).W)
          (h := (Classical.choice hw).h) (k := k)
          (H := (Classical.choice hw).H)
          (hLL := (Classical.choice hw).hLL)
          (longest := (Classical.choice hw).longest)
          (Classical.choice hw).hτ (Classical.choice hw).hp
          (Classical.choice hw).P (Classical.choice hw).hqMode
          (Classical.choice hw).Tpath (Classical.choice hw).hfin
          (Classical.choice hw).hleft hk)) := by
  classical
  simp [LPlusSidePresentation.classOptionAt4, hk, hw]

/-- Helper toward Lemma 5.5. Equal complete codes give equal corrected
class-reader values at a fixed boundary index. -/
theorem LPlusSidePresentation.classOptionAt4_eq_of_code_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (hcode : r.code = r'.code) :
    LPlusSidePresentation.classOptionAt4 x k r =
      LPlusSidePresentation.classOptionAt4 x k r' := by
  have hr : r = r' :=
    (lPlusSidePresentation_ext_iff_code_eq x r r').2 hcode
  cases hr
  rfl

/-- Helper toward Lemma 5.5. Read the corrected decoder-4 class reader from
a complete nonnegative left presentation code. -/
@[expose] noncomputable def lPlusSidePresentationClassOptionCode4
    (x : XDP) (k : ℤ) (c : LPlusCode) : Option GeometricSideClass :=
  LPlusSidePresentation.classOptionAt4 x k (decodeLPlus x k c)

/-- Helper toward Lemma 5.5. The corrected class reader factors through the
complete three-coordinate code, retaining the boundary index. -/
theorem lPlusSidePresentation_classOptionAt4_eq_codeReader
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x) :
    LPlusSidePresentation.classOptionAt4 x k r =
      lPlusSidePresentationClassOptionCode4 x k r.code := by
  change LPlusSidePresentation.classOptionAt4 x k r =
    LPlusSidePresentation.classOptionAt4 x k (decodeLPlus x k r.code)
  rw [LPlusSidePresentation.decode_code]

/-- Helper toward Lemma 5.5. A decoded code is read by the code-level
corrected class reader applied to that same code. -/
theorem lPlusSidePresentation_classOptionAt4_decodeLPlus
    (x : XDP) (k : ℤ) (c : LPlusCode) :
    LPlusSidePresentation.classOptionAt4 x k (decodeLPlus x k c) =
      lPlusSidePresentationClassOptionCode4 x k c := rfl

/-- Helper toward Lemma 5.5. The indexed interface uses the corrected
decoder-4 reader at its stored boundary index. -/
@[expose] noncomputable def LPlusIndexedSidePresentation.classOption4
    (x : XDP) (r : LPlusIndexedSidePresentation x) :
    Option GeometricSideClass :=
  LPlusSidePresentation.classOptionAt4 x r.boundaryIndex r.presentation

/-- Helper toward Lemma 5.5. Reading an indexed decoded observation is the
corrected reader at the index carried by that observation. -/
theorem LPlusIndexedSidePresentation.classOption4_decodeLPlusWithIndex
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) (c : LPlusCode) :
    LPlusIndexedSidePresentation.classOption4 x
        (decodeLPlusWithIndex x k hk c) =
      LPlusSidePresentation.classOptionAt4 x k (decodeLPlus x k c) := rfl

/-- Helper toward Lemma 5.5. Every observed nonnegative left presentation
has a present corrected class almost surely, for either XDP mode. -/
theorem ae_decodeLPlus_leftSideObsNonneg_classOptionAt4_isSome
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (LPlusSidePresentation.classOptionAt4 x k
        (decodeLPlus x k (leftSideObsNonneg x k W))).isSome := by
  filter_upwards [Xdp.m0Cut_ae_leftmost_xdp_and_pairwise_coalescence,
    wholePlane_ae_boundaryGluing_inputs] with W hgeo hglue
  obtain ⟨H, h, hLL, hp, hpaths⟩ := hgeo
  let longest : Bool := if x = XDP.ldp then true else false
  have hmode : (if longest then XDP.ldp else XDP.sdp) = x := by
    cases x <;> rfl
  obtain ⟨R, T, P, _, hleft, _, _⟩ := hpaths longest
  obtain ⟨hτ, hfin, _, hcoherent⟩ := hglue h k
  let r := decodeLPlus x k (leftSideObsNonneg x k W)
  have hw : Nonempty (LPlusSidePresentationSourceWitness x k r) := by
    refine ⟨⟨W, h, H, hLL, longest, hτ, hp, P k, ?_, T k, hfin,
      hleft k, rfl, rfl, rfl⟩⟩
    rw [hmode]
    exact hcoherent x
  rw [LPlusSidePresentation.classOptionAt4_eq_some x k r hk hw]
  exact Option.isSome_some

/-- Helper toward Lemma 5.5. The indexed corrected reader is present almost
surely on the observed nonnegative left code. -/
theorem ae_decodeLPlus_leftSideObsNonneg_classOption4_isSome
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (LPlusIndexedSidePresentation.classOption4 x
        (decodeLPlusWithIndex x k hk (leftSideObsNonneg x k W))).isSome := by
  filter_upwards [ae_decodeLPlus_leftSideObsNonneg_classOptionAt4_isSome x k hk]
    with W hW
  simpa [LPlusIndexedSidePresentation.classOption4, decodeLPlusWithIndex] using hW












































end DirectedDistances.PaperProofs.Section5
