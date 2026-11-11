module

public import DirectedDistances.PaperProofs.Section4.ThinCutSideImageEquality
public import DirectedDistances.PaperProofs.Section4.ThinDecoderAssembly

/-! Conditional assembly of the good-cut truncation decoder, toward Proposition 4.7.
The selected-geodesic common-prefix family remains an upstream obligation. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open scoped Classical

local notation "Ω" => (ℕ → ℤ × ℤ)

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Common selected prefixes for actual selected-cut representative pairs at ordered good cuts.
Both complete cut outputs must be represented by the supplied witnesses; the dart embeddings
are into the later stage, and the vertex embeddings record permanent stage vertex IDs. -/
@[expose] def SelectedCutCommonPrefixFamily
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) : Prop :=
  ∀ (q : selectedCutCoherentDomain x T hT) (s k K : ℕ), k ≤ K →
    (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
    (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (K + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2) →
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat - 1
    let N := (selectedCutTime T (K + 1) q.1).toNat - 1
    ∀ (ha : t ≤ N) {ℓ d ℓ' d' : ℕ}
      (R : KMSWMapRep ℓ
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2).toNat
        (selectedCutTime T (k + 1) q.1).toNat)
      (hR : xdpLengthBase R.B x = d)
      (S : KMSWMapRep ℓ'
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2).toNat
        (selectedCutTime T (K + 1) q.1).toNat)
      (hS : xdpLengthBase S.B x = d')
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
      (J : DirectedMapWithMissingIso S.B.map (kmswStageDirectedMap w N)),
      selectedCutPastCuts x T (k + 1) q.1 =
        (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
         some ⟨_, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩) →
      selectedCutPastCuts x T (K + 1) q.1 =
        (some ⟨d', ⟨ℓ', ⟨(cutLRep S hS).1, KMSWMapIsoClass.mk (cutLRep S hS).2⟩⟩⟩,
         some ⟨_, ⟨d', ⟨(cutRRep S hS).1, KMSWMapIsoClass.mk (cutRRep S hS).2⟩⟩⟩) →
      CommonSelectedPrefix R hR S hS
        (outerSucc_castDart (kmswStage_nextEdge_mono w ha) ∘ I.toEquiv) J.toEquiv
        (fun v => (stageMapVertex w t (cutMapIsoVertexEquiv I v)).id)
        (fun v => (stageMapVertex w N (cutMapIsoVertexEquiv J v)).id)

private theorem selectedCut_past_time_mono
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k K : ℕ) (hkK : k ≤ K) :
    (selectedCutTime T (k + 1) q.1).toNat - 1 ≤
      (selectedCutTime T (K + 1) q.1).toNat - 1 := by
  rcases hkK.lt_or_eq with hlt | heq
  · obtain ⟨o, _, ho⟩ := selectedCutTime_future_recovery x T hT k K hlt
    have ht := (ho q).1
    omega
  · rw [heq]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
At ordered good cuts the actual half truncations agree, conditional on the selected-prefix
family. The source threshold is exactly `s + 1` on both sides. -/
theorem selectedCutPastCuts_halfTruncate_eq_of_commonPrefixFamily
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (hprefix : SelectedCutCommonPrefixFamily x T hT)
    (a : ThinMapSide) (s k K : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hkK : k ≤ K)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (hK : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (K + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2)) :
    halfTruncate a s (match a with
      | .left => (selectedCutPastCuts x T (k + 1) q.1).1
      | .right => (selectedCutPastCuts x T (k + 1) q.1).2) =
    halfTruncate a s (match a with
      | .left => (selectedCutPastCuts x T (K + 1) q.1).1
      | .right => (selectedCutPastCuts x T (K + 1) q.1).2) := by
  have ha := selectedCut_past_time_mono x T hT q k K hkK
  cases a with
  | left =>
    obtain ⟨ℓ, d, ℓ', d', R, hR, S, hS, I, J, v, v', _, _, _, _, heq, hc, hc'⟩ :=
      selectedCutPastCuts_representatives_left_halfTruncate_eq
        x T hT q s k K hk hK ha (β := ℕ)
    exact heq _ _ (hprefix q s k K hkK hk hK ha R hR S hS I J hc hc')
  | right =>
    obtain ⟨ℓ, d, ℓ', d', R, hR, S, hS, I, J, v, v', _, _, _, _, heq, hc, hc'⟩ :=
      selectedCutPastCuts_representatives_right_halfTruncate_eq
        x T hT q s k K hk hK ha (β := ℕ)
    exact heq _ _ (hprefix q s k K hkK hk hK ha R hR S hS I J hc hc')

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The selected-prefix family implies the decoder assembly's least-good-cut compatibility. -/
theorem halfTruncateCutEqLeastGood_of_commonPrefixFamily
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (hprefix : SelectedCutCommonPrefixFamily x T hT) :
    HalfTruncateCutEqLeastGood x T hT := by
  intro a s k q hk
  exact selectedCutPastCuts_halfTruncate_eq_of_commonPrefixFamily x T hT hprefix
    a s (leastGoodCut x T hT s q) k q (leastGoodCut_le x T hT s k q hk)
    (leastGoodCut_spec x T hT s q) hk

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Conditional decoder at every good cut, from common prefixes of the actual representatives. -/
theorem thinTruncationAt_decode_of_commonPrefixFamily
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (hprefix : SelectedCutCommonPrefixFamily x T hT)
    (a : ThinMapSide) (s k : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    thinTruncationAt x T hT a s q =
      halfTruncate a s (selectedCutSide x T a k q.1) := by
  exact thinTruncationAt_decode_leastGood x T hT
    (halfTruncateCutEqLeastGood_of_commonPrefixFamily x T hT hprefix) a s k q hk

end DirectedDistances.PaperProofs.Section4
