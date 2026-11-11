module

public import DirectedDistances.Probability.ScaledPartialSumWindow
public import DirectedDistances.Probability.SkorokhodModulus

/-! # Deterministic modulus estimates for scaled partial sums

The partition gaps, including the last gap, are strictly greater than the sparsity
scale. Oscillation is measured on half-open blocks, so the terminal value is excluded.
The probabilistic separation estimates are not asserted by this module. -/

public section
namespace DirectedDistances.Probability

open MeasureTheory ProbabilityTheory

private theorem partition_oscillation_nonneg {T : ℝ} {hT : 0 < T}
    (f : CadlagWindow T) (p : WindowPartition T hT) :
    0 ≤ sSup (Set.range fun i : Fin p.n =>
      blockOscillation f (p.time i.castSucc) (p.time i.succ)) := by
  let i : Fin p.n := ⟨0, p.n_pos⟩
  have hblock : 0 ≤ blockOscillation f (p.time i.castSucc) (p.time i.succ) := by
    apply le_csSup (blockOscillation_values_bddAbove f _ _)
    refine ⟨p.time i.castSucc, p.time i.castSucc, le_rfl, p.strict i,
      le_rfl, p.strict i, ?_⟩
    simp
  exact hblock.trans (le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩)

/-- a sparse partition bounds the modulus by its block bounds
(Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem cadlagModulus_le_of_sparse_partition {T : ℝ} {hT : 0 < T}
    (f : CadlagWindow T) {δ ε : ℝ} (p : WindowPartition T hT)
    (hp : p.IsSparse δ)
    (hblock : ∀ i : Fin p.n,
      blockOscillation f (p.time i.castSucc) (p.time i.succ) ≤ ε) :
    cadlagModulus (hT := hT) f δ ≤ ε := by
  have hδT : δ < T :=
    (windowPartition_sparse_nonempty_iff hT δ).1 ⟨⟨p, hp⟩⟩
  have hbounded : BddBelow
      (Set.range fun q : {q : WindowPartition T hT // q.IsSparse δ} =>
        sSup (Set.range fun i : Fin q.1.n =>
          blockOscillation f (q.1.time i.castSucc) (q.1.time i.succ))) := by
    refine ⟨0, ?_⟩
    rintro x ⟨q, rfl⟩
    exact partition_oscillation_nonneg f q.1
  have hsup : sSup (Set.range fun i : Fin p.n =>
      blockOscillation f (p.time i.castSucc) (p.time i.succ)) ≤ ε := by
    apply csSup_le
    · exact ⟨_, ⟨⟨0, p.n_pos⟩, rfl⟩⟩
    · rintro x ⟨i, rfl⟩
      exact hblock i
  unfold cadlagModulus
  rw [dite_eq_left hδT]
  exact (csInf_le hbounded ⟨⟨p, hp⟩, rfl⟩).trans hsup

/-- a blockwise constant part leaves oscillation controlled by twice the remainder bound
(Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem blockOscillation_le_of_constant_add {T : ℝ}
    (f : CadlagWindow T) (g : J1Window T → ℝ)
    (a b : J1Window T) (hab : (a : ℝ) < b) (c r : ℝ)
    (hdecomp : ∀ t : J1Window T, (a : ℝ) ≤ t → (t : ℝ) < b →
      f.1 t = c + g t)
    (hbound : ∀ t : J1Window T, (a : ℝ) ≤ t → (t : ℝ) < b → |g t| ≤ r) :
    blockOscillation f a b ≤ 2 * r := by
  unfold blockOscillation
  apply csSup_le
  · refine ⟨0, a, a, le_rfl, hab, le_rfl, hab, ?_⟩
    simp
  · rintro x ⟨s, t, has, hsb, hat, htb, rfl⟩
    rw [hdecomp s has hsb, hdecomp t hat htb]
    calc |c + g s - (c + g t)| = |g s - g t| := by congr 1; ring
      _ ≤ |g s| + |g t| := abs_sub _ _
      _ ≤ r + r := add_le_add (hbound s has hsb) (hbound t hat htb)
      _ = 2 * r := by ring

/-- the scaled step path splits exactly into its small and large increments
(Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem scaledPartialSumWindow_truncation {Ω : Type*}
    (X : ℕ → Ω → ℝ) (ν a : ℝ) (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : Ω) (t : J1Window T) :
    (scaledPartialSumWindow X ν n hT ω).path.1 t =
      (scaledPartialSumWindow (fun j ω => if |X j ω| ≤ a then X j ω else 0)
        ν n hT ω).path.1 t +
      (scaledPartialSumWindow (fun j ω => if a < |X j ω| then X j ω else 0)
        ν n hT ω).path.1 t := by
  rw [scaledPartialSumWindow_apply, scaledPartialSumWindow_apply,
    scaledPartialSumWindow_apply, ← mul_add]
  congr 1
  unfold partialSumZ
  split_ifs with hm
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : |X j ω| ≤ a
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  · simp

private theorem partialSumZ_nat_eq {Ω : Type*}
    (X : ℕ → Ω → ℝ) (ω : Ω) (k : ℕ) :
    partialSumZ X ω (k : ℤ) = ∑ j ∈ Finset.range k, X j ω := by
  cases k with
  | zero => simp [partialSumZ]
  | succ k => simp [partialSumZ]

private theorem scaled_window_apply_nat {Ω : Type*}
    (X : ℕ → Ω → ℝ) (ν : ℝ) (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : Ω) (t : J1Window T) :
    (scaledPartialSumWindow X ν n hT ω).path.1 t =
      ((n + 1 : ℕ) : ℝ) ^ (-(1 / ν)) *
        ∑ j ∈ Finset.range ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊, X j ω := by
  rw [scaledPartialSumWindow_apply,
    ← Int.natCast_floor_eq_floor (mul_nonneg (by positivity) t.property.1),
    partialSumZ_nat_eq]

/-- large-increment partial sums are constant until the next large increment
(Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem scaledPartialSumWindow_large_eq_of_no_large_increment {Ω : Type*}
    (X : ℕ → Ω → ℝ) (ν a : ℝ) (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : Ω) (s t : J1Window T) (hst : (s : ℝ) ≤ t)
    (hno : ∀ j : ℕ, ⌊((n + 1 : ℕ) : ℝ) * (s : ℝ)⌋₊ ≤ j →
      j < ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ → |X j ω| ≤ a) :
    (scaledPartialSumWindow (fun j ω => if a < |X j ω| then X j ω else 0)
      ν n hT ω).path.1 t =
    (scaledPartialSumWindow (fun j ω => if a < |X j ω| then X j ω else 0)
      ν n hT ω).path.1 s := by
  rw [scaled_window_apply_nat, scaled_window_apply_nat]
  congr 1
  symm
  apply Finset.sum_subset
  · exact Finset.range_subset_range.mpr
      (Nat.floor_mono (mul_le_mul_of_nonneg_left hst (by positivity)))
  · intro j hjt hjs
    have hjlo : ⌊((n + 1 : ℕ) : ℝ) * (s : ℝ)⌋₊ ≤ j := by
      simpa only [Finset.mem_range, not_lt] using hjs
    have hsmall := hno j hjlo (Finset.mem_range.mp hjt)
    simp only [not_lt.mpr hsmall, ite_false]

/-- a sparse partition with no interior large increment bounds the step-path modulus
by twice its small-increment supremum
(Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem scaledPartialSumWindow_modulus_le_of_no_large_increment {Ω : Type*}
    (X : ℕ → Ω → ℝ) (ν a : ℝ) (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : Ω) {δ r : ℝ} (p : WindowPartition T hT) (hp : p.IsSparse δ)
    (hRem : ∀ t : J1Window T,
      |(scaledPartialSumWindow (fun j ω => if |X j ω| ≤ a then X j ω else 0)
        ν n hT ω).path.1 t| ≤ r)
    (hno : ∀ i : Fin p.n, ∀ t : J1Window T,
      (p.time i.castSucc : ℝ) ≤ t → (t : ℝ) < p.time i.succ →
      ∀ j : ℕ, ⌊((n + 1 : ℕ) : ℝ) * (p.time i.castSucc : ℝ)⌋₊ ≤ j →
        j < ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ → |X j ω| ≤ a) :
    cadlagModulus (hT := hT) (scaledPartialSumWindow X ν n hT ω).path δ ≤ 2 * r := by
  apply cadlagModulus_le_of_sparse_partition _ p hp
  intro i
  let small := fun t : J1Window T =>
    (scaledPartialSumWindow (fun j ω => if |X j ω| ≤ a then X j ω else 0)
      ν n hT ω).path.1 t
  let large := fun t : J1Window T =>
    (scaledPartialSumWindow (fun j ω => if a < |X j ω| then X j ω else 0)
      ν n hT ω).path.1 t
  apply blockOscillation_le_of_constant_add _ small _ _ (p.strict i)
    (large (p.time i.castSucc)) r
  · intro t hat htb
    have hconst : large t = large (p.time i.castSucc) :=
      scaledPartialSumWindow_large_eq_of_no_large_increment X ν a n hT ω
        (p.time i.castSucc) t hat (hno i t hat htb)
    have hsplit := scaledPartialSumWindow_truncation X ν a n hT ω t
    change _ = small t + large t at hsplit
    rw [hsplit, hconst, add_comm]
  · intro t _ _
    exact hRem t

private theorem exists_partition_of_separated_cuts {T : ℝ} (hT : 0 < T)
    (s : Finset (J1Window T))
    (h0 : ⟨0, le_rfl, hT.le⟩ ∈ s) (hTs : ⟨T, hT.le, le_rfl⟩ ∈ s)
    {δ : ℝ} (hsep : ∀ a ∈ s, ∀ b ∈ s, (a : ℝ) < b → δ < (b : ℝ) - a) :
    ∃ p : WindowPartition T hT, p.IsSparse δ ∧
      ∀ i : Fin p.n, ∀ c ∈ s,
        ¬ ((p.time i.castSucc : ℝ) < c ∧ (c : ℝ) < p.time i.succ) := by
  classical
  let k := s.card
  have hk : 2 ≤ k := by
    apply Finset.one_lt_card.mpr
    refine ⟨_, h0, _, hTs, ?_⟩
    intro h
    have heq := congrArg Subtype.val h
    exact hT.ne' heq.symm
  have hlen : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
  let e := s.orderEmbOfFin (show s.card = k from rfl)
  let p : WindowPartition T hT :=
    { n := k - 1
      n_pos := by omega
      time := fun i => e (Fin.cast hlen i)
      first := by
        apply Subtype.ext
        have hi : Fin.cast hlen (0 : Fin (k - 1 + 1)) = ⟨0, by omega⟩ := by
          ext
          rfl
        rw [hi, Finset.orderEmbOfFin_zero (show s.card = k from rfl) (by omega)]
        apply le_antisymm
        · exact Finset.min'_le _ _ h0
        · exact (s.min' ⟨_, h0⟩).property.1
      last := by
        apply Subtype.ext
        have hi : Fin.cast hlen (Fin.last (k - 1)) = ⟨k - 1, by omega⟩ := by
          ext
          rfl
        rw [hi, Finset.orderEmbOfFin_last (show s.card = k from rfl) (by omega)]
        apply le_antisymm
        · exact (s.max' ⟨_, hTs⟩).property.2
        · exact Finset.le_max' _ _ hTs
      strict := by
        intro i
        apply e.strictMono
        change Fin.cast hlen i.castSucc < Fin.cast hlen i.succ
        simp only [Fin.lt_def, Fin.val_cast]
        exact i.castSucc_lt_succ }
  have hmem (i : Fin (p.n + 1)) : p.time i ∈ s :=
    Finset.orderEmbOfFin_mem s _ _
  refine ⟨p, ?_, ?_⟩
  · intro i
    exact hsep _ (hmem i.castSucc) _ (hmem i.succ) (p.strict i)
  · intro i c hc hbetween
    have hc_range : c ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact hc
    obtain ⟨j, rfl⟩ := hc_range
    have hleft : Fin.cast hlen i.castSucc < j := e.lt_iff_lt.mp hbetween.1
    have hright : j < Fin.cast hlen i.succ := e.lt_iff_lt.mp hbetween.2
    simp only [Fin.lt_def, Fin.val_cast, Fin.val_castSucc, Fin.val_succ] at hleft hright
    omega

/-- separated cuts containing every large-jump time give the deterministic modulus bound
(Billingsley 1999, Thm 13.2, window form); not the paper result. -/
theorem scaledPartialSumWindow_modulus_le_of_separated_cuts {Ω : Type*}
    (X : ℕ → Ω → ℝ) (ν a : ℝ) (n : ℕ) {T : ℝ} (hT : 0 < T)
    (ω : Ω) {δ r : ℝ} (s : Finset (J1Window T))
    (h0 : ⟨0, le_rfl, hT.le⟩ ∈ s) (hTs : ⟨T, hT.le, le_rfl⟩ ∈ s)
    (hsep : ∀ u ∈ s, ∀ v ∈ s, (u : ℝ) < v → δ < (v : ℝ) - u)
    (hcuts : ∀ j : ℕ, j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ → a < |X j ω| →
      ∃ c ∈ s, (c : ℝ) = (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ))
    (hRem : ∀ t : J1Window T,
      |(scaledPartialSumWindow (fun j ω => if |X j ω| ≤ a then X j ω else 0)
        ν n hT ω).path.1 t| ≤ r) :
    cadlagModulus (hT := hT) (scaledPartialSumWindow X ν n hT ω).path δ ≤ 2 * r := by
  obtain ⟨p, hp, hbetween⟩ := exists_partition_of_separated_cuts hT s h0 hTs hsep
  apply scaledPartialSumWindow_modulus_le_of_no_large_increment X ν a n hT ω p hp hRem
  intro i t hat htb j hjlo hjhi
  by_contra hnot
  have hbig : a < |X j ω| := lt_of_not_ge hnot
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hjK : j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ :=
    hjhi.trans_le (Nat.floor_mono (mul_le_mul_of_nonneg_left t.property.2 hN.le))
  obtain ⟨c, hc, hctime⟩ := hcuts j hjK hbig
  apply hbetween i c hc
  constructor
  · rw [hctime, lt_div_iff₀ hN]
    have hfloor := Nat.lt_floor_add_one (((n + 1 : ℕ) : ℝ) *
      (p.time i.castSucc : ℝ))
    have hcast : (⌊((n + 1 : ℕ) : ℝ) * (p.time i.castSucc : ℝ)⌋₊ : ℝ) ≤ j :=
      Nat.cast_le.mpr hjlo
    nlinarith only [hfloor, hcast]
  · have hcle : (c : ℝ) ≤ t := by
      rw [hctime, div_le_iff₀ hN]
      have hcast : (j + 1 : ℝ) ≤
          ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ := by
        exact_mod_cast hjhi
      have hfloor := Nat.floor_le (mul_nonneg hN.le t.property.1)
      nlinarith only [hcast, hfloor]
    exact hcle.trans_lt htb

/-- small-jump and separated-cut failure bounds imply a modulus probability bound
(Billingsley 1999, Thm 13.2, window form); not the paper result.
The two probability estimates are explicit inputs; no iid separation estimate is claimed. -/
theorem scaledPartialSumWindow_modulus_prob_le_of_bad_event_bounds {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (ν a : ℝ) (n : ℕ) {T : ℝ} (hT : 0 < T)
    (δ r ηRem ηBad : ℝ)
    (hRem : P.real {ω | ∃ t : J1Window T,
      r < |(scaledPartialSumWindow
        (fun j ω => if |X j ω| ≤ a then X j ω else 0) ν n hT ω).path.1 t|} ≤ ηRem)
    (hBad : P.real {ω | ¬ ∃ s : Finset (J1Window T),
      ⟨0, le_rfl, hT.le⟩ ∈ s ∧ ⟨T, hT.le, le_rfl⟩ ∈ s ∧
      (∀ u ∈ s, ∀ v ∈ s, (u : ℝ) < v → δ < (v : ℝ) - u) ∧
      (∀ j : ℕ, j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ → a < |X j ω| →
        ∃ c ∈ s, (c : ℝ) = (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ))} ≤ ηBad) :
    P.real {ω | 2 * r <
      cadlagModulus (hT := hT) (scaledPartialSumWindow X ν n hT ω).path δ} ≤
        ηRem + ηBad := by
  classical
  have hsubset : {ω | 2 * r <
      cadlagModulus (hT := hT) (scaledPartialSumWindow X ν n hT ω).path δ} ⊆
      {ω | ∃ t : J1Window T,
        r < |(scaledPartialSumWindow
          (fun j ω => if |X j ω| ≤ a then X j ω else 0) ν n hT ω).path.1 t|} ∪
      {ω | ¬ ∃ s : Finset (J1Window T),
        ⟨0, le_rfl, hT.le⟩ ∈ s ∧ ⟨T, hT.le, le_rfl⟩ ∈ s ∧
        (∀ u ∈ s, ∀ v ∈ s, (u : ℝ) < v → δ < (v : ℝ) - u) ∧
        (∀ j : ℕ, j < ⌊((n + 1 : ℕ) : ℝ) * T⌋₊ → a < |X j ω| →
          ∃ c ∈ s, (c : ℝ) = (j + 1 : ℝ) / ((n + 1 : ℕ) : ℝ))} := by
    intro ω hω
    by_cases hr : ∃ t : J1Window T,
        r < |(scaledPartialSumWindow
          (fun j ω => if |X j ω| ≤ a then X j ω else 0) ν n hT ω).path.1 t|
    · exact Or.inl hr
    · right
      rintro ⟨s, h0, hTs, hsep, hcuts⟩
      have hpoint : ∀ t : J1Window T,
          |(scaledPartialSumWindow
            (fun j ω => if |X j ω| ≤ a then X j ω else 0) ν n hT ω).path.1 t| ≤ r := by
        intro t
        exact le_of_not_gt (fun ht => hr ⟨t, ht⟩)
      exact (not_lt_of_ge
        (scaledPartialSumWindow_modulus_le_of_separated_cuts
          X ν a n hT ω s h0 hTs hsep hcuts hpoint)) hω
  exact (measureReal_mono hsubset).trans
    ((measureReal_union_le _ _).trans (add_le_add hRem hBad))

end DirectedDistances.Probability
