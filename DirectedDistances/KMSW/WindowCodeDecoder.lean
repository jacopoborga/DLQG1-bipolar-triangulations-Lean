module

public import DirectedDistances.KMSW.MeasurableCutEvents
public import DirectedDistances.RandomWalk.LazyTwoDimensionalPrefixRange
public import DirectedDistances.RandomWalk.Lemma518Cemetery

/-! # Deterministic decoding of a finite centered walk window

Helper toward Proposition 5.16 (`prop-disk-bs-conv`, -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk
open MeasureTheory

/-- Decode each valid adjacent displacement to its unique source letter, using `0` when the
displacement is not a source step or the index is outside the window. Helper toward
deterministic; not the paper result. -/
@[expose] noncomputable def windowCodeDecode (N : ℕ)
    (x : Fin (2 * N + 1) → ℤ × ℤ) : ℕ → Fin 3 := by
  classical
  exact fun i =>
    if hi : i < 2 * N then
      let a : Fin (2 * N + 1) := ⟨i, by omega⟩
      let b : Fin (2 * N + 1) := ⟨i + 1, by omega⟩
      if h : ∃ c : Fin 3, lazyTwoDimensionalStep c = x b - x a then
        Classical.choose h
      else 0
    else 0

/-- Measurability in the window input of the total finite-window decoder. Helper toward
deterministic; not the paper result. -/
theorem measurable_windowCodeDecode (N : ℕ) :
    Measurable (fun x : Fin (2 * N + 1) → ℤ × ℤ =>
      windowCodeDecode N x) := by
  exact measurable_of_countable _

/-- Every source step in a valid centered bridge window decodes to its one-based transition
letter. Here `T = (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat`. Helper toward Proposition 5.16
result. -/
theorem windowCodeDecode_bridge {n N : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    ∀ i < 2 * N, windowCodeDecode N x i =
      p.1 ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + i + 1) := by
  classical
  intro i hi
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  have hvalid : codeFstFirstHit (-(p.2 : ℤ)) p.1 ≠ ⊤ ∧
      N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n := by
    unfold bridgeOptionWindow at h
    split at h
    · assumption
    · contradiction
  have hT : N ≤ T := by simpa [T] using hvalid.2.1
  have hx := bridgeOptionWindow_some_eq h
  have hia : i + 1 < 2 * N + 1 := by omega
  have hdiff : lazyTwoDimensionalStep (p.1 (T - N + i + 1)) =
      x ⟨i + 1, hia⟩ - x ⟨i, by omega⟩ := by
    rw [hx]
    unfold bridgeRawWindow
    have hidx1 : T + (i + 1) - N = T - N + i + 1 := by omega
    have hidx0 : T + i - N = T - N + i := by omega
    rw [hidx1, hidx0]
    have hs := codeWalk_succ_sub p.1 (T - N + i)
    calc
      lazyTwoDimensionalStep (p.1 (T - N + i + 1)) =
          codeWalk p.1 (T - N + i + 1) - codeWalk p.1 (T - N + i) := hs.symm
      _ = (codeWalk p.1 (T - N + i + 1) - codeWalk p.1 T) -
          (codeWalk p.1 (T - N + i) - codeWalk p.1 T) := by abel
  have hex : ∃ c : Fin 3,
      lazyTwoDimensionalStep c = x ⟨i + 1, hia⟩ - x ⟨i, by omega⟩ :=
    ⟨p.1 (T - N + i + 1), hdiff⟩
  have hdecode : windowCodeDecode N x i = Classical.choose hex := by
    unfold windowCodeDecode
    rw [dite_eq_left hi, dite_eq_left hex]
  rw [hdecode]
  apply lazyTwoDimensionalStep_injective
  calc
    lazyTwoDimensionalStep (Classical.choose hex) =
        x ⟨i + 1, hia⟩ - x ⟨i, by omega⟩ := Classical.choose_spec hex
    _ = lazyTwoDimensionalStep (p.1 (T - N + i + 1)) := hdiff.symm

/-- The decoded window and the shifted source word give the same KMSW stage through time
`2 * N`. Helper toward Proposition 5.16 (`prop-disk-bs-conv`, -/
theorem kmswStage_windowCodeDecode_bridge {n N : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    ∀ j ≤ 2 * N, kmswStage (windowCodeDecode N x) j =
      kmswStage (fun i => p.1
        ((codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N + i + 1)) j := by
  intro j hj
  apply kmswStage_congr
  intro i hi
  exact windowCodeDecode_bridge h i (by omega)

end DirectedDistances.KMSW
