module

public import DirectedDistances.PaperProofs.Section4.ThinGoodCutExists
public import DirectedDistances.PaperProofs.Section4.ThinHalfTruncate

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open scoped Classical

local notation "Ω" => (ℕ → ℤ × ℤ)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The selected component of the selected-cut output at cut index `k + 1`: `.1` for the left
side and `.2` for the right side. -/
@[expose] noncomputable def selectedCutSide
    (x : XDP) (T : ℕ → Ω → ℕ∞) (a : ThinMapSide) (k : ℕ) (p : Ω) :
    Option (Σ r : ℕ, AllBoltzmannSpace r) :=
  match a with
  | .left => (selectedCutPastCuts x T (k + 1) p).1
  | .right => (selectedCutPastCuts x T (k + 1) p).2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The truncation of side `a` at boundary index `s`, read from the selected cut at the least
good index `leastGoodCut x T hT s q`. -/
@[expose] noncomputable def thinTruncationAt
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (s : ℕ) (q : selectedCutCoherentDomain x T hT) :
    Option FiniteThinMap :=
  halfTruncate a s (selectedCutSide x T a (leastGoodCut x T hT s q) q.1)

private theorem measurable_leastGoodCut_aux
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) (s : ℕ) :
    Measurable (leastGoodCut x T hT s) := by
  have hF : ∀ k, selectedCutConditioningSigma x T hT k ≤
      (inferInstance : MeasurableSpace (selectedCutCoherentDomain x T hT)) := fun k =>
    ((selectedCutConditioningVersion_measurable_ae_eq x T hT k).1.comp
      measurable_subtype_coe).comap_le
  have hE : ∀ k, MeasurableSet {q : selectedCutCoherentDomain x T hT | (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)} := fun k =>
    hF k _ (measurableSet_selectedCutCoherent_good_event x T hT s k)
  refine measurable_to_countable' (fun k => ?_)
  have : leastGoodCut x T hT s ⁻¹' {k} =
      {q | (s : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)} ∩
      ⋂ j ∈ Finset.range k, {q : selectedCutCoherentDomain x T hT | (s : ℤ) + 1 ≤
        min ((q.1 (selectedCutTime T (j + 1) q.1).toNat).1)
          (-(q.1 (selectedCutTime T (j + 1) q.1).toNat).2)}ᶜ := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]
    unfold leastGoodCut
    rw [Nat.find_eq_iff]
  rw [this]
  exact (hE k).inter (MeasurableSet.biInter (Set.to_countable _)
    (fun j _ => (hE j).compl))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The least good cut index is measurable on the coherent domain. -/
theorem measurable_leastGoodCut
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) (s : ℕ) :
    Measurable (leastGoodCut x T hT s) :=
  measurable_leastGoodCut_aux x T hT s

private theorem measurable_selectedCutSide
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (k : ℕ) :
    Measurable (fun q : selectedCutCoherentDomain x T hT => selectedCutSide x T a k q.1) := by
  have hv : Measurable (Subtype.val : selectedCutCoherentDomain x T hT → Ω) :=
    measurable_subtype_coe
  have h : Measurable (fun q : selectedCutCoherentDomain x T hT =>
      selectedCutPastCuts x T (k + 1) q.1) :=
    (measurable_selectedCutPastCuts x T (k + 1) hT).comp hv
  cases a
  · exact measurable_fst.comp h
  · exact measurable_snd.comp h

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The side truncation read from the least good cut is measurable. -/
theorem measurable_thinTruncationAt
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (s : ℕ) :
    Measurable (thinTruncationAt x T hT a s) := by
  have hside : ∀ k, Measurable (fun q : selectedCutCoherentDomain x T hT =>
      selectedCutSide x T a k q.1) := fun k => measurable_selectedCutSide x T hT a k
  have hG : Measurable (fun z : ℕ × selectedCutCoherentDomain x T hT =>
      halfTruncate a s (selectedCutSide x T a z.1 z.2.1)) :=
    measurable_from_prod_countable_right (fun k => (measurable_halfTruncate a s).comp (hside k))
  have hpair : Measurable (fun q : selectedCutCoherentDomain x T hT =>
      (leastGoodCut x T hT s q, q)) :=
    (measurable_leastGoodCut x T hT s).prodMk measurable_id
  have hc := hG.comp hpair
  unfold thinTruncationAt
  exact hc

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
CONDITIONAL decoder: if the truncations at any two good cuts agree (hypothesis `hcompat`,
to be proved separately), then on a good cut `k` the truncation `thinTruncationAt` equals
the truncation of that cut's side. -/
theorem thinTruncationAt_decode_of_compat
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (s : ℕ)
    (hcompat : ∀ (k K : ℕ) (q : selectedCutCoherentDomain x T hT),
      (s : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
      (s : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (K + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (K + 1) q.1).toNat).2) →
      halfTruncate a s (selectedCutSide x T a k q.1) =
        halfTruncate a s (selectedCutSide x T a K q.1))
    (k : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (s : ℤ) + 1 ≤ min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
      (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    thinTruncationAt x T hT a s q = halfTruncate a s (selectedCutSide x T a k q.1) :=
  hcompat _ k q (leastGoodCut_spec x T hT s q) hk

end DirectedDistances.PaperProofs.Section4
