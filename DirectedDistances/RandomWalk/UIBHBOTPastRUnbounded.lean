module

public import DirectedDistances.RandomWalk.UIBHBOTEncodingWalk
public import DirectedDistances.Probability.HewittSavage

/-! # Backward R-coordinate helpers for the UIBHBOT walk

a.s. divergence of the coordinates, asserted without proof in the source); not the paper result. -/

public section
namespace DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory







@[expose] def uibhbotWordRDisplacement (v : List (Fin 3)) : ℤ :=
  ((v.map lazyTwoDimensionalStep).sum).2




@[expose] noncomputable def uibhbotWordRDisplacementLaw : Measure ℤ :=
  excursionWordLaw.map uibhbotWordRDisplacement




theorem iIndepFun_uibhbotWordFamilyRDisplacement :
    iIndepFun (fun k w => uibhbotWordRDisplacement (w k)) uibhbotWordFamilyLaw := by
  exact iIndepFun_uibhbotWordFamilyEval.comp (fun _ => uibhbotWordRDisplacement)
    (fun _ => measurable_of_countable _)




theorem uibhbotWordFamilyLaw_map_RDisplacement (k : ℤ) :
    uibhbotWordFamilyLaw.map (fun w => uibhbotWordRDisplacement (w k)) =
      uibhbotWordRDisplacementLaw := by
  calc
    uibhbotWordFamilyLaw.map (fun w => uibhbotWordRDisplacement (w k)) =
        (uibhbotWordFamilyLaw.map (fun w => w k)).map uibhbotWordRDisplacement := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_uibhbotWordFamilyEval k)]
      rfl
    _ = excursionWordLaw.map uibhbotWordRDisplacement := by
      rw [uibhbotWordFamilyLaw_map_eval]
    _ = uibhbotWordRDisplacementLaw := rfl

/- Helper toward Proposition 5.16 (UIBHBOT M^♭: a.s. liminf_{n→−∞} R^♭(n) = −∞,
result. -/

/-- The backward block R-displacements are independent and identically distributed under the
canonical two-sided stopped-word family law. Helper toward Proposition 5.16 (UIBHBOT M^♭:
the source); not the paper result. -/
theorem iIndepFun_uibhbotBackwardWordRDisplacement :
    iIndepFun
      (fun k w => uibhbotWordRDisplacement (w (-(k : ℤ) - 1))) uibhbotWordFamilyLaw := by
  apply iIndepFun_uibhbotWordFamilyRDisplacement.precomp
  intro i j hij
  have hneg : -(i : ℤ) = -(j : ℤ) := by
    have h := congrArg (fun z : ℤ => z + 1) hij
    simpa using h
  exact_mod_cast (neg_injective hneg)

/-- Every backward block R-displacement has the one-word R-displacement law. Helper toward
Proposition 5.16 (UIBHBOT M^♭: a.s. liminf_{n→−∞} R^♭(n) = −∞,
result. -/
theorem uibhbotWordFamilyLaw_map_backwardRDisplacement (k : ℕ) :
    uibhbotWordFamilyLaw.map
      (fun w => uibhbotWordRDisplacement (w (-(k : ℤ) - 1))) =
      uibhbotWordRDisplacementLaw := by
  exact uibhbotWordFamilyLaw_map_RDisplacement (-(k : ℤ) - 1)

/-- The partial sum of the first `k` backward block R-displacements. Helper toward Proposition
5.16 (UIBHBOT M^♭: a.s. liminf_{n→−∞} R^♭(n) = −∞,
result. -/
@[expose] def uibhbotBackwardRPartialSum (w : ℤ → List (Fin 3)) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range k, uibhbotWordRDisplacement (w (-(j : ℤ) - 1))

/-- One additional block adds its backward R-displacement to the partial sum. Helper toward
Proposition 5.16 (UIBHBOT M^♭: a.s. liminf_{n→−∞} R^♭(n) = −∞,
result. -/
theorem uibhbotBackwardRPartialSum_succ (w : ℤ → List (Fin 3)) (k : ℕ) :
    uibhbotBackwardRPartialSum w (k + 1) =
      uibhbotBackwardRPartialSum w k +
        uibhbotWordRDisplacement (w (-(k : ℤ) - 1)) := by
  simp [uibhbotBackwardRPartialSum, Finset.sum_range_succ]




@[expose] def uibhbotBackwardWordSequence (w : ℤ → List (Fin 3)) :
    ℕ → List (Fin 3) := fun j => w (-(j : ℤ) - 1)




theorem measurable_uibhbotBackwardWordSequence :
    Measurable (uibhbotBackwardWordSequence :
      (ℤ → List (Fin 3)) → ℕ → List (Fin 3)) := by
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_pi_apply (-(j : ℤ) - 1)




theorem uibhbotWordFamilyLaw_map_backwardWordSequence :
    uibhbotWordFamilyLaw.map uibhbotBackwardWordSequence =
      Measure.infinitePi (fun _ : ℕ => excursionWordLaw) := by
  have hIndep :
      iIndepFun (fun (j : ℕ) w => w (-(j : ℤ) - 1)) uibhbotWordFamilyLaw := by
    apply iIndepFun_uibhbotWordFamilyEval.precomp
    intro i j hij
    have hneg : -(i : ℤ) = -(j : ℤ) := by
      have h := congrArg (fun z : ℤ => z + 1) hij
      simpa using h
    exact_mod_cast (neg_injective hneg)
  have hmap := hIndep.map_fun_eq_infinitePi_map
    (fun (j : ℕ) => measurable_pi_apply (-(j : ℤ) - 1))
  have hmarginal (j : ℕ) :
      uibhbotWordFamilyLaw.map (fun w => w (-(j : ℤ) - 1)) = excursionWordLaw := by
    exact uibhbotWordFamilyLaw_map_eval (-(j : ℤ) - 1)
  calc
    uibhbotWordFamilyLaw.map uibhbotBackwardWordSequence =
        uibhbotWordFamilyLaw.map
          (fun (w : ℤ → List (Fin 3)) (j : ℕ) => w (-(j : ℤ) - 1)) := rfl
    _ = Measure.infinitePi
        (fun j : ℕ => uibhbotWordFamilyLaw.map (fun w => w (-(j : ℤ) - 1))) := hmap
    _ = Measure.infinitePi (fun _ : ℕ => excursionWordLaw) := by
      congr 1
      funext j
      exact hmarginal j




@[expose] def uibhbotBackwardWordUnboundedEvent : Set (ℕ → List (Fin 3)) :=
  {u | ∀ A : ℤ, ∃ k : ℕ,
    A < ∑ j ∈ Finset.range k, uibhbotWordRDisplacement (u j)}




theorem measurableSet_uibhbotBackwardWordUnboundedEvent :
    MeasurableSet uibhbotBackwardWordUnboundedEvent := by
  unfold uibhbotBackwardWordUnboundedEvent
  have hsum (k : ℕ) : Measurable (fun u : ℕ → List (Fin 3) =>
      ∑ j ∈ Finset.range k, uibhbotWordRDisplacement (u j)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have heq : (fun u : ℕ → List (Fin 3) =>
          ∑ j ∈ Finset.range (k + 1), uibhbotWordRDisplacement (u j)) =
        (fun u => ∑ j ∈ Finset.range k, uibhbotWordRDisplacement (u j)) +
          (fun u => uibhbotWordRDisplacement (u k)) := by
        funext u
        simp [Finset.sum_range_succ]
      rw [heq]
      exact ih.add ((measurable_of_countable fun v : List (Fin 3) =>
        uibhbotWordRDisplacement v).comp (measurable_pi_apply k))
  rw [Set.ofPred_forall]
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iInter fun A => MeasurableSet.iUnion fun k =>
    measurableSet_lt measurable_const (hsum k)




theorem uibhbotBackwardWordUnboundedEvent_preimage :
    uibhbotBackwardWordSequence ⁻¹' uibhbotBackwardWordUnboundedEvent =
      {w | ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k} := by
  ext w
  simp [uibhbotBackwardWordUnboundedEvent, uibhbotBackwardWordSequence,
    uibhbotBackwardRPartialSum]




theorem uibhbotBackwardWordUnboundedEvent_invariant (σ : Equiv.Perm ℕ)
    (hσ : {i | σ i ≠ i}.Finite) :
    (fun u (i : ℕ) => u (σ i)) ⁻¹' uibhbotBackwardWordUnboundedEvent =
      uibhbotBackwardWordUnboundedEvent := by
  classical
  let S (u : ℕ → List (Fin 3)) (k : ℕ) : ℤ :=
    ∑ j ∈ Finset.range k, uibhbotWordRDisplacement (u j)
  have hsucc (u : ℕ → List (Fin 3)) (k : ℕ) :
      S u (k + 1) = S u k + uibhbotWordRDisplacement (u k) := by
    simp [S, Finset.sum_range_succ]
  have hforward (τ : Equiv.Perm ℕ) (hτ : {i | τ i ≠ i}.Finite)
      (u : ℕ → List (Fin 3)) (hu : u ∈ uibhbotBackwardWordUnboundedEvent) :
      (fun i => u (τ i)) ∈ uibhbotBackwardWordUnboundedEvent := by
    change ∀ A : ℤ, ∃ k : ℕ, A < S u k at hu
    let N : ℕ := hτ.toFinset.sup id + 1
    have hfix (i : ℕ) (hi : N ≤ i) : τ i = i := by
      by_contra hne
      have hmem : i ∈ hτ.toFinset := hτ.mem_toFinset.mpr hne
      have hle : i ≤ hτ.toFinset.sup id := Finset.le_sup (f := id) hmem
      dsimp [N] at hi
      omega
    let v : ℕ → List (Fin 3) := fun i => u (τ i)
    let C : ℤ := S v N - S u N
    have hdiff (m : ℕ) : S v (N + m) = S u (N + m) + C := by
      induction m with
      | zero =>
        simp only [Nat.add_zero]
        dsimp [C]
        omega
      | succ m ih =>
        have hidx : N + (m + 1) = (N + m) + 1 := by omega
        have htail : v (N + m) = u (N + m) := by
          dsimp [v]
          rw [hfix (N + m) (by omega)]
        calc
          S v (N + (m + 1)) = S v (N + m) +
              uibhbotWordRDisplacement (v (N + m)) := by
            rw [hidx, hsucc]
          _ = S u (N + m) + C +
              uibhbotWordRDisplacement (u (N + m)) := by rw [ih, htail]
          _ = S u (N + (m + 1)) + C := by
            rw [hidx, hsucc u (N + m)]
            ring
    have hcofinal (B : ℤ) : ∃ k : ℕ, N ≤ k ∧ B < S u k := by
      let M : ℤ := (Finset.range (N + 1)).sup' (by simp) (fun k => S u k)
      obtain ⟨k, hk⟩ := hu (max B M)
      have hkN : N ≤ k := by
        by_contra hnot
        have hklt : k < N := Nat.lt_of_not_ge hnot
        have hle : S u k ≤ M := by
          dsimp [M]
          exact Finset.le_sup' (f := fun j => S u j)
            (Finset.mem_range.mpr (by omega : k < N + 1))
        exact (not_lt_of_ge hle) (lt_of_le_of_lt (le_max_right B M) hk)
      exact ⟨k, hkN, lt_of_le_of_lt (le_max_left B M) hk⟩
    change ∀ A : ℤ, ∃ k : ℕ, A < S v k
    intro A
    obtain ⟨k, hkN, hk⟩ := hcofinal (A - C)
    have hidx : N + (k - N) = k := by omega
    have hsum : S v k = S u k + C := by
      simpa [hidx] using hdiff (k - N)
    refine ⟨k, ?_⟩
    rw [hsum]
    omega
  have hσinv : {i | σ.symm i ≠ i}.Finite := by
    apply hσ.subset
    intro i hi
    change σ.symm i ≠ i at hi
    change σ i ≠ i
    intro heq
    apply hi
    have h := congrArg σ.symm heq
    simpa using h.symm
  ext u
  change (fun i => u (σ i)) ∈ uibhbotBackwardWordUnboundedEvent ↔
    u ∈ uibhbotBackwardWordUnboundedEvent
  constructor
  · intro hTu
    have hback := hforward σ.symm hσinv (fun i => u (σ i)) hTu
    have hcancel : (fun i => (fun j => u (σ j)) (σ.symm i)) = u := by
      funext i
      simp
    rw [hcancel] at hback
    exact hback
  · exact hforward σ hσ u




theorem uibhbotWordFamilyLaw_backwardRUnbounded_zero_one :
    uibhbotWordFamilyLaw
        {w | ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k} = 0 ∨
      uibhbotWordFamilyLaw
        {w | ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k} = 1 := by
  let E' := uibhbotBackwardWordUnboundedEvent
  have hzero := DirectedDistances.Probability.infinitePi_hs_zero_one excursionWordLaw E'
    measurableSet_uibhbotBackwardWordUnboundedEvent
    uibhbotBackwardWordUnboundedEvent_invariant
  have htransfer :
      uibhbotWordFamilyLaw
          {w | ∀ A : ℤ, ∃ k : ℕ, A < uibhbotBackwardRPartialSum w k} =
        Measure.infinitePi (fun _ : ℕ => excursionWordLaw) E' := by
    rw [← uibhbotBackwardWordUnboundedEvent_preimage,
      ← Measure.map_apply measurable_uibhbotBackwardWordSequence
        measurableSet_uibhbotBackwardWordUnboundedEvent,
      uibhbotWordFamilyLaw_map_backwardWordSequence]
  rcases hzero with h0 | h1
  · left
    rw [htransfer]
    exact h0
  · right
    rw [htransfer]
    exact h1

end DirectedDistances.RandomWalk
