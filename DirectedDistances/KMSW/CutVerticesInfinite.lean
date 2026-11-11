module

public import DirectedDistances.KMSW.CutEquivalence
public import DirectedDistances.RandomWalk.PitmanCodes
public import DirectedDistances.RandomWalk.SuccessInfinitelyOften
import DirectedDistances.RandomWalk.ConditionedTransience
import DirectedDistances.RandomWalk.PitmanPrefixCompatibility

/-! # Infinitely many cut vertices in the KMSW bookkeeping

bookkeeping boundaries (`IsCutVertex`), conditional on the block bound -/

public section
namespace DirectedDistances.KMSW

open MeasureTheory
open DirectedDistances.RandomWalk

private theorem measurable_vectorPitman' : Measurable vectorPitman := by
  have hf : Measurable (fun z : ℕ → ℤ × ℤ => fun k => (z k).1) := by fun_prop
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hf).prodMk
    (((measurable_pi_apply n).snd).add ((measurable_globalLazyRunningMinimum n).comp hf))

/-- Almost surely the Pitman-flipped iid code sequence has infinitely many cut vertices -/
theorem pitmanCodes_ae_infinite_cutVertices_of_blockProb
    (q : ℝ) (hq : 0 < q)
    (hE : ∀ N : ℕ, 100 ≤ N → q ≤ (conditionedVectorPathLaw 0 0).real {p : ℕ → ℤ × ℤ |
      (∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        Real.sqrt n / 100 ≤ ((p n).1 : ℝ) ∧ ((p n).1 : ℝ) ≤ 100 * Real.sqrt n) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (N : ℝ) / 2 → -Real.sqrt N ≤ ((p n).2 : ℝ)) ∧
      ((p N).2 : ℝ) ≤ -2 * Real.sqrt N}) :
    ∀ᵐ ω ∂iidCodeMeasure,
      {v : ℕ | IsCutVertex (pitmanCode (fun i => ω (i + 1))) v}.Infinite := by
  have hmeas : Measurable (fun ω : ℕ → Fin 3 => fun k => vectorPitman (codeWalk ω) k) :=
    measurable_vectorPitman'.comp measurable_codeWalk
  have hS := ae_of_ae_map hmeas.aemeasurable
    (by rw [map_vectorPitman_codeWalk]
        exact conditionedVectorPathLaw_ae_infinite_success_of_blockProb q hq hE)
  have hT := ae_of_ae_map hmeas.aemeasurable
    (by rw [map_vectorPitman_codeWalk]
        exact conditionedVectorPathLaw_tendsto_fst_atTop 0 0)
  filter_upwards [hS, hT] with ω hS hT
  set w : ℕ → Fin 3 := pitmanCode (fun i => ω (i + 1)) with hw
  have hPw : ∀ n, vectorPitman (codeWalk ω) n = integrateCodes w n := by
    intro n
    rw [hw, integrateCodes_pitmanCode]
    rfl
  have htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop := by
    have : L w = fun j => (vectorPitman (codeWalk ω) j).1 := by
      funext j
      rw [kmsw_L_eq, hPw]
    rw [this]
    exact hT
  set S : Set ℕ := {n : ℕ | (∀ k, k < n + 1 →
      (vectorPitman (codeWalk ω) (n + 1)).2 ≤ (vectorPitman (codeWalk ω) k).2 - 1) ∧
    ∀ i, n + 1 ≤ i →
      (vectorPitman (codeWalk ω) (n + 1)).1 ≤ (vectorPitman (codeWalk ω) i).1} with hSdef
  have hSinf : S.Infinite := hS
  have key : ∀ n ∈ S, IsCutVertex w (activeInitial w (n + 1)) ∧
      ∀ j < n + 1, activeInitial w j ≠ activeInitial w (n + 1) := by
    intro n hn
    apply cut_and_first_visit_of_records w htrans
    · intro j hj
      rw [kmsw_R_eq, kmsw_R_eq, ← hPw, ← hPw]
      exact hn.1 j hj
    · intro j hj
      rw [kmsw_L_eq, kmsw_L_eq, ← hPw, ← hPw]
      exact hn.2 j hj
  have hinj : Set.InjOn (fun n => activeInitial w (n + 1)) S := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab ((key b hb).2 (a + 1) (by omega))
    · exact h
    · exact absurd hab.symm ((key a ha).2 (b + 1) (by omega))
  refine (hSinf.image hinj).mono ?_
  rintro _ ⟨n, hn, rfl⟩
  exact (key n hn).1

end DirectedDistances.KMSW
