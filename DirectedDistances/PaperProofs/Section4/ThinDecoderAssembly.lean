module

public import DirectedDistances.PaperProofs.Section4.ThinIndependenceAssembly
public import DirectedDistances.PaperProofs.Section4.ThinCutCompatibility
public import DirectedDistances.PaperProofs.Section4.ThinCylinderCodes

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap MeasureTheory ProbabilityTheory
open scoped Classical

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "CutHalf" => Option (Σ n : ℕ, AllBoltzmannSpace n)
local notation "ThinCode" => (ℕ → Option FiniteThinMap)

/-- Helper toward Proposition 4.7 (prop-thin-ind); conditional on
HalfTruncateCutEqLeastGood; not a paper result. Source:
with the truncation at every other good cut, with the source's `s + 1` threshold. -/
@[expose] def HalfTruncateCutEqLeastGood
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) : Prop :=
  ∀ (a : ThinMapSide) (s k : ℕ) (q : selectedCutCoherentDomain x T hT),
    (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
    halfTruncate a s (match a with
      | .left => (selectedCutPastCuts x T
          (leastGoodCut x T hT s q + 1) q.1).1
      | .right => (selectedCutPastCuts x T
          (leastGoodCut x T hT s q + 1) q.1).2) =
    halfTruncate a s (match a with
      | .left => (selectedCutPastCuts x T (k + 1) q.1).1
      | .right => (selectedCutPastCuts x T (k + 1) q.1).2)

/-- Helper toward Proposition 4.7 (prop-thin-ind); conditional on
HalfTruncateCutEqLeastGood; not a paper result. Source: -/
@[expose] noncomputable def thinCumulativeCode
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (s : ℕ) (q : selectedCutCoherentDomain x T hT) : ThinCode :=
  cumulativeCode (thinTruncationAt x T hT a) none s q

/-- Helper toward Proposition 4.7 (prop-thin-ind); conditional on
HalfTruncateCutEqLeastGood; not a paper result. Source: -/
@[expose] noncomputable def thinCutCumulativeDecoder
    (a : ThinMapSide) (s : ℕ) (_k : ℕ) (h : CutHalf) : ThinCode :=
  cumulativeDecoder (fun i h => halfTruncate a i h) none s h

/-- Helper toward Proposition 4.7 (prop-thin-ind); conditional on
HalfTruncateCutEqLeastGood; not a paper result. Source:
canonical least-good-cut definition. -/
theorem thinTruncationAt_decode_leastGood
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (HalfTruncateCutEqLeastGood : HalfTruncateCutEqLeastGood x T hT)
    (a : ThinMapSide) (s k : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    thinTruncationAt x T hT a s q =
      halfTruncate a s (selectedCutSide x T a k q.1) := by
  unfold thinTruncationAt selectedCutSide
  exact HalfTruncateCutEqLeastGood a s k q hk

/-- Helper toward Proposition 4.7 (prop-thin-ind); conditional on
HalfTruncateCutEqLeastGood; not a paper result. Source:
threshold implies the decoder's `i + 1` threshold. -/
theorem thinCumulativeCode_decode_leastGood
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (HalfTruncateCutEqLeastGood : HalfTruncateCutEqLeastGood x T hT)
    (a : ThinMapSide) (s k : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    thinCumulativeCode x T hT a s q =
      thinCutCumulativeDecoder a s k (selectedCutSide x T a k q.1) := by
  change cumulativeCode (thinTruncationAt x T hT a) none s q =
    cumulativeDecoder (fun i h => halfTruncate a i h) none s
      (selectedCutSide x T a k q.1)
  apply cumulativeCode_eq_decoder
  intro i his
  apply thinTruncationAt_decode_leastGood x T hT HalfTruncateCutEqLeastGood a i k q
  omega

/-- Helper toward Proposition 4.7 (prop-thin-ind); conditional on
HalfTruncateCutEqLeastGood; not a paper result. Source:
assembly for the cumulative left and right truncation codes. The remaining inputs are
measurability of the two limiting code-valued maps for their generated sigma-algebras. -/
theorem thinIndependence_of_cumulativeThinCodes
    {L' R' : Type*} [MeasurableSpace L'] [MeasurableSpace R']
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (HalfTruncateCutEqLeastGood : HalfTruncateCutEqLeastGood x T hT)
    (XLlim : selectedCutCoherentDomain x T hT → L')
    (XRlim : selectedCutCoherentDomain x T hT → R')
    (hXLlim : Measurable[⨆ s, MeasurableSpace.comap
      (thinCumulativeCode x T hT .left s) inferInstance] XLlim)
    (hXRlim : Measurable[⨆ s, MeasurableSpace.comap
      (thinCumulativeCode x T hT .right s) inferInstance] XRlim) :
    IndepFun XLlim XRlim ((conditionedVectorPathLaw 0 0).comap
      (Subtype.val : selectedCutCoherentDomain x T hT → Ω)) := by
  have hXL : ∀ s, Measurable (thinCumulativeCode x T hT .left s) := by
    intro s
    change Measurable (cumulativeCode (thinTruncationAt x T hT .left) none s)
    exact measurable_cumulativeCode none
      (fun i => measurable_thinTruncationAt x T hT .left i) s
  have hXR : ∀ s, Measurable (thinCumulativeCode x T hT .right s) := by
    intro s
    change Measurable (cumulativeCode (thinTruncationAt x T hT .right) none s)
    exact measurable_cumulativeCode none
      (fun i => measurable_thinTruncationAt x T hT .right i) s
  have hmonoL : Monotone (fun s => MeasurableSpace.comap
      (thinCumulativeCode x T hT .left s) inferInstance) := by
    change Monotone (fun s => MeasurableSpace.comap
      (cumulativeCode (thinTruncationAt x T hT .left) none s) inferInstance)
    exact comap_cumulativeCode_monotone (thinTruncationAt x T hT .left) none
  have hmonoR : Monotone (fun s => MeasurableSpace.comap
      (thinCumulativeCode x T hT .right s) inferInstance) := by
    change Monotone (fun s => MeasurableSpace.comap
      (cumulativeCode (thinTruncationAt x T hT .right) none s) inferInstance)
    exact comap_cumulativeCode_monotone (thinTruncationAt x T hT .right) none
  have hgL : ∀ s k, Measurable (thinCutCumulativeDecoder .left s k) := by
    intro s k
    change Measurable (cumulativeDecoder
      (fun i h => halfTruncate .left i h) none s)
    exact measurable_cumulativeDecoder none (fun i => measurable_halfTruncate .left i) s
  have hgR : ∀ s k, Measurable (thinCutCumulativeDecoder .right s k) := by
    intro s k
    change Measurable (cumulativeDecoder
      (fun i h => halfTruncate .right i h) none s)
    exact measurable_cumulativeDecoder none (fun i => measurable_halfTruncate .right i) s
  have hdecodeL : ∀ (s k : ℕ) (q : selectedCutCoherentDomain x T hT),
      (s : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
      thinCumulativeCode x T hT .left s q =
        thinCutCumulativeDecoder .left s k (selectedCutPastCuts x T (k + 1) q.1).1 := by
    intro s k q hk
    simpa [selectedCutSide] using
      (thinCumulativeCode_decode_leastGood x T hT HalfTruncateCutEqLeastGood
        .left s k q hk)
  have hdecodeR : ∀ (s k : ℕ) (q : selectedCutCoherentDomain x T hT),
      (s : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
      thinCumulativeCode x T hT .right s q =
        thinCutCumulativeDecoder .right s k (selectedCutPastCuts x T (k + 1) q.1).2 := by
    intro s k q hk
    simpa [selectedCutSide] using
      (thinCumulativeCode_decode_leastGood x T hT HalfTruncateCutEqLeastGood
        .right s k q hk)
  exact thinIndependence_of_cutDecoders
    (L := ThinCode) (R := ThinCode) (L' := L') (R' := R')
    x T hT (thinCumulativeCode x T hT .left) (thinCumulativeCode x T hT .right)
    hXL hXR hmonoL hmonoR (thinCutCumulativeDecoder .left)
    (thinCutCumulativeDecoder .right) hgL hgR hdecodeL hdecodeR XLlim XRlim
    hXLlim hXRlim

end DirectedDistances.PaperProofs.Section4
