module

public import DirectedDistances.KMSW.BoundaryDynamics
public import DirectedDistances.RandomWalk.IIDWalkMaximalTailBound
public import DirectedDistances.PaperProofs.Section7.CellLDPLowerAlignment

/-! Supporting lemmas for paper labels `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/

/-! # Boundary length tail helper for the cell LDP upper bound

these are not the paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk




theorem shifted_codeWalk_snd_eq_R (ω : ℕ → Fin 3) (n : ℕ) :
    R (fun i => ω (i + 1)) n = (codeWalk ω n).2 := by
  simp [R, codeWalk, Prod.snd_sum]



theorem kmswBoundary_lengths_le_of_coordinate_bounds
    (w : ℕ → Fin 3) (n : ℕ) (B : ℝ)
    (hL : ∀ j ≤ n, |(L w j : ℝ)| < B)
    (hR : ∀ j ≤ n, |(R w j : ℝ)| < B) :
    ((kmswStage w n).UL.length : ℝ) ≤ 2 * B + 1 ∧
    ((kmswStage w n).UR.length : ℝ) ≤ 2 * B ∧
    ((kmswStage w n).LL.length : ℝ) ≤ B ∧
    ((kmswStage w n).LR.length : ℝ) ≤ B + 1 := by
  obtain ⟨jL, hjL, hminL⟩ := runningMin_attained (L w) n
  obtain ⟨jR, hjR, hminR⟩ := runningMin_attained (R w) n
  have hLmin : -B < (minL w n : ℝ) := by
    rw [minL, hminL]
    exact (abs_lt.mp (hL jL hjL)).1
  have hRmin : -B < (minR w n : ℝ) := by
    rw [minR, hminR]
    exact (abs_lt.mp (hR jR hjR)).1
  have hLn : (L w n : ℝ) < B := (abs_lt.mp (hL n le_rfl)).2
  have hRn : (R w n : ℝ) < B := (abs_lt.mp (hR n le_rfl)).2
  have hUL : ((kmswStage w n).UL.length : ℝ) =
      (L w n : ℝ) - (minL w n : ℝ) + 1 := by
    exact_mod_cast kmswStage_UL_length w n
  have hUR : ((kmswStage w n).UR.length : ℝ) =
      (R w n : ℝ) - (minR w n : ℝ) := by
    exact_mod_cast kmswStage_UR_length w n
  have hLL : ((kmswStage w n).LL.length : ℝ) = -(minL w n : ℝ) := by
    exact_mod_cast kmswStage_LL_length w n
  have hLR : ((kmswStage w n).LR.length : ℝ) = -(minR w n : ℝ) + 1 := by
    exact_mod_cast kmswStage_LR_length w n
  constructor
  · rw [hUL]
    linarith
  constructor
  · rw [hUR]
    linarith
  constructor
  · rw [hLL]
    linarith
  · rw [hLR]
    linarith

private theorem shifted_codeWalk_coordinate_bounds_measurable (n : ℕ) (B : ℝ) :
    MeasurableSet {ω : ℕ → Fin 3 | ∃ k ≤ n,
      (B ≤ |(((codeWalk ω k).1 : ℤ) : ℝ)| ∨
       B ≤ |(((codeWalk ω k).2 : ℤ) : ℝ)|)} := by
  let bad : Set (ℕ → Fin 3) := {ω | ∃ k ≤ n,
    (B ≤ |(((codeWalk ω k).1 : ℤ) : ℝ)| ∨
     B ≤ |(((codeWalk ω k).2 : ℤ) : ℝ)|)}
  have hbadEq : bad = ⋃ k : ℕ, {ω | k ≤ n ∧
      (B ≤ |(((codeWalk ω k).1 : ℤ) : ℝ)| ∨
       B ≤ |(((codeWalk ω k).2 : ℤ) : ℝ)|)} := by
    ext ω
    simp [bad]
  change MeasurableSet bad
  rw [hbadEq]
  refine MeasurableSet.iUnion fun k => ?_
  by_cases hk : k ≤ n
  · have hwalk : Measurable (fun ω : ℕ → Fin 3 => codeWalk ω k) :=
      (measurable_pi_apply k).comp measurable_codeWalk
    have hfst : Measurable (fun ω : ℕ → Fin 3 =>
        |(((codeWalk ω k).1 : ℤ) : ℝ)|) :=
      continuous_abs.measurable.comp ((measurable_of_countable Int.cast).comp hwalk.fst)
    have hsnd : Measurable (fun ω : ℕ → Fin 3 =>
        |(((codeWalk ω k).2 : ℤ) : ℝ)|) :=
      continuous_abs.measurable.comp ((measurable_of_countable Int.cast).comp hwalk.snd)
    have hset : MeasurableSet {ω : ℕ → Fin 3 |
        B ≤ |(((codeWalk ω k).1 : ℤ) : ℝ)| ∨
        B ≤ |(((codeWalk ω k).2 : ℤ) : ℝ)|} :=
      (measurableSet_le measurable_const hfst).union
        (measurableSet_le measurable_const hsnd)
    simpa [hk] using hset
  · simp [hk]




theorem kmswBoundary_lengths_tail
    (n : ℕ) (hn : 0 < n) (B : ℝ) (hB : 0 < B) :
    1 - 4 * Real.exp (-(B ^ 2) / (2 * (n : ℝ))) ≤
      iidCodeMeasure.real {ω : ℕ → Fin 3 |
        ((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤ 2 * B + 1 ∧
        ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤ 2 * B ∧
        ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤ B ∧
        ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤ B + 1} := by
  let coordinateBad : Set (ℕ → Fin 3) := {ω | ∃ k ≤ n,
    (B ≤ |(((codeWalk ω k).1 : ℤ) : ℝ)| ∨
     B ≤ |(((codeWalk ω k).2 : ℤ) : ℝ)|)}
  let coordinateGood : Set (ℕ → Fin 3) := {ω | ∀ k ≤ n,
    |(((codeWalk ω k).1 : ℤ) : ℝ)| < B ∧
    |(((codeWalk ω k).2 : ℤ) : ℝ)| < B}
  let target : Set (ℕ → Fin 3) := {ω |
    ((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤ 2 * B + 1 ∧
    ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤ 2 * B ∧
    ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤ B ∧
    ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤ B + 1}
  have hcompSet : coordinateGood = coordinateBadᶜ := by
    ext ω
    simp [coordinateGood, coordinateBad, not_le]
  have hbadMeas : MeasurableSet coordinateBad :=
    shifted_codeWalk_coordinate_bounds_measurable n B
  have htail := iidCodeWalk_blockMax_tail 0 n hn B hB
  have htail' : iidCodeMeasure.real coordinateBad ≤
      4 * Real.exp (-(B ^ 2) / (2 * (n : ℝ))) := by
    simpa [coordinateBad, codeWalk_zero] using htail
  have hgoodProb : 1 - 4 * Real.exp (-(B ^ 2) / (2 * (n : ℝ))) ≤
      iidCodeMeasure.real coordinateGood := by
    have hcomp := MeasureTheory.measureReal_compl
      (μ := iidCodeMeasure) hbadMeas
    rw [probReal_univ] at hcomp
    rw [hcompSet, hcomp]
    linarith
  have hsubset : coordinateGood ⊆ target := by
    intro ω hω
    have hL : ∀ j ≤ n,
        |(L (fun i => ω (i + 1)) j : ℝ)| < B := by
      intro j hj
      rw [shifted_codeWalk_fst_eq_L]
      exact (hω j hj).1
    have hR : ∀ j ≤ n,
        |(R (fun i => ω (i + 1)) j : ℝ)| < B := by
      intro j hj
      rw [shifted_codeWalk_snd_eq_R]
      exact (hω j hj).2
    exact kmswBoundary_lengths_le_of_coordinate_bounds
      (fun i => ω (i + 1)) n B hL hR
  change 1 - 4 * Real.exp (-(B ^ 2) / (2 * (n : ℝ))) ≤ iidCodeMeasure.real target
  exact hgoodProb.trans (MeasureTheory.measureReal_mono hsubset)

private theorem sourceScale_sq_div (A ε : ℝ) (n : ℕ) (hn : 0 < n) :
    (A ^ ε * Real.sqrt (n : ℝ)) ^ 2 / (n : ℝ) = (A ^ ε) ^ 2 := by
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hns : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_nonneg
  have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [mul_pow, hns]
  field_simp [hnpos]




theorem kmswBoundary_lengths_source_scale_tail
    (A ε : ℝ) (n : ℕ) (hA : 1 < A) (hε : 0 < ε) (hn : 1 ≤ n) :
    1 - 4 * Real.exp (-((A ^ ε) ^ 2 / 32)) ≤
      iidCodeMeasure.real {ω : ℕ → Fin 3 |
        ((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤
            A ^ ε * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤
            A ^ ε * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
            A ^ ε * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
            A ^ ε * Real.sqrt (n : ℝ)} := by
  let T : ℝ := A ^ ε * Real.sqrt (n : ℝ)
  let target : Set (ℕ → Fin 3) := {ω |
    ((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤ T ∧
    ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤ T ∧
    ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤ T ∧
    ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤ T}
  have hn0 : 0 < n := by omega
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hAε : 1 < A ^ ε := Real.one_lt_rpow hA hε
  have hTpos : 0 < T := by
    dsimp [T]
    exact mul_pos (by linarith) (Real.sqrt_pos.2 (by positivity))
  have hscale := sourceScale_sq_div A ε n hn0
  have hscaleT : T ^ 2 / (n : ℝ) = (A ^ ε) ^ 2 := by
    simpa [T] using hscale
  have harg : (A ^ ε) ^ 2 / 32 = T ^ 2 / (32 * (n : ℝ)) := by
    rw [← hscaleT]
    field_simp [show (n : ℝ) ≠ 0 by positivity]
  change 1 - 4 * Real.exp (-((A ^ ε) ^ 2 / 32)) ≤ iidCodeMeasure.real target
  by_cases hT : 2 ≤ T
  · have hB : 0 < T / 4 := by positivity
    have htail := kmswBoundary_lengths_tail n hn0 (T / 4) hB
    have hsubset : {ω : ℕ → Fin 3 |
        ((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤ 2 * (T / 4) + 1 ∧
        ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤ 2 * (T / 4) ∧
        ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤ T / 4 ∧
        ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤ T / 4 + 1} ⊆ target := by
      intro ω hω
      change _ ∧ _ ∧ _ ∧ _ at hω
      change _ ∧ _ ∧ _ ∧ _
      constructor
      · dsimp [T]
        nlinarith [hω.1]
      constructor
      · dsimp [T]
        nlinarith [hω.2.1]
      constructor
      · dsimp [T]
        nlinarith [hω.2.2.1, hT]
      · dsimp [T]
        nlinarith [hω.2.2.2, hT]
    have htail' : 1 - 4 * Real.exp (-(T / 4) ^ 2 / (2 * (n : ℝ))) ≤
        iidCodeMeasure.real target := by
      exact htail.trans (MeasureTheory.measureReal_mono hsubset)
    have harg' : (T / 4) ^ 2 / (2 * (n : ℝ)) =
        (A ^ ε) ^ 2 / 32 := by
      rw [harg]
      field_simp [show (n : ℝ) ≠ 0 by positivity]
      ring
    have hargExp : (-(T / 4) ^ 2) / (2 * (n : ℝ)) =
        -((A ^ ε) ^ 2 / 32) := by
      rw [show (-(T / 4) ^ 2) / (2 * (n : ℝ)) =
          -((T / 4) ^ 2 / (2 * (n : ℝ))) by ring, harg']
    rw [hargExp] at htail'
    exact htail'
  · have hTlt : T < 2 := lt_of_not_ge hT
    have hx : (A ^ ε) ^ 2 / 32 < 1 / 8 := by
      have hsmall : T ^ 2 / (32 * (n : ℝ)) < 1 / 8 := by
        rw [div_lt_iff₀ (by positivity : 0 < 32 * (n : ℝ))]
        nlinarith [sq_nonneg T, hTlt, hTpos, hnR]
      rw [harg]
      exact hsmall
    have hexp : (1 : ℝ) / 4 < Real.exp (-((A ^ ε) ^ 2 / 32)) := by
      have he := Real.add_one_le_exp (-((A ^ ε) ^ 2 / 32))
      nlinarith
    have hnonneg : 0 ≤ iidCodeMeasure.real target := MeasureTheory.measureReal_nonneg
    have htrivial : 1 - 4 * Real.exp (-((A ^ ε) ^ 2 / 32)) ≤ 0 := by
      nlinarith
    exact htrivial.trans hnonneg

end DirectedDistances.PaperProofs.Section7

namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk





theorem kmswBoundary_offsets_source_scale_tail
    (A ε : ℝ) (n : ℕ) (hA : 1 < A) (hε : 0 < ε) (hn : 1 ≤ n) :
    1 - 4 * Real.exp (-((A ^ ε) ^ 2 / 32)) ≤
      iidCodeMeasure.real {ω : ℕ → Fin 3 |
        ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤
            A ^ ε * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) + 1 ≤
            A ^ ε * Real.sqrt (n : ℝ) ∧
        ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤
            A ^ ε * Real.sqrt (n : ℝ) ∧
        (((kmswStage (fun i => ω (i + 1)) n).UL.length - 1 : ℕ) : ℝ) ≤
            A ^ ε * Real.sqrt (n : ℝ)} := by
  let T : ℝ := A ^ ε * Real.sqrt (n : ℝ)
  let target : Set (ℕ → Fin 3) := {ω |
    ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤ T ∧
    ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) + 1 ≤ T ∧
    ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤ T ∧
    (((kmswStage (fun i => ω (i + 1)) n).UL.length - 1 : ℕ) : ℝ) ≤ T}
  have hn0 : 0 < n := by omega
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hAε : 1 < A ^ ε := Real.one_lt_rpow hA hε
  have hTpos : 0 < T := by
    dsimp [T]
    exact mul_pos (by linarith) (Real.sqrt_pos.2 (by positivity))
  have hscale := sourceScale_sq_div A ε n hn0
  have hscaleT : T ^ 2 / (n : ℝ) = (A ^ ε) ^ 2 := by
    simpa [T] using hscale
  have harg : (A ^ ε) ^ 2 / 32 = T ^ 2 / (32 * (n : ℝ)) := by
    rw [← hscaleT]
    field_simp [show (n : ℝ) ≠ 0 by positivity]
  change 1 - 4 * Real.exp (-((A ^ ε) ^ 2 / 32)) ≤
    iidCodeMeasure.real target
  by_cases hT : 2 ≤ T
  · have hB : 0 < T / 4 := by positivity
    have htail := kmswBoundary_lengths_tail n hn0 (T / 4) hB
    have hsubset : {ω : ℕ → Fin 3 |
        ((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) ≤ 2 * (T / 4) + 1 ∧
        ((kmswStage (fun i => ω (i + 1)) n).UR.length : ℝ) ≤ 2 * (T / 4) ∧
        ((kmswStage (fun i => ω (i + 1)) n).LL.length : ℝ) ≤ T / 4 ∧
        ((kmswStage (fun i => ω (i + 1)) n).LR.length : ℝ) ≤ T / 4 + 1} ⊆ target := by
      intro ω hω
      change _ ∧ _ ∧ _ ∧ _ at hω
      change _ ∧ _ ∧ _ ∧ _
      constructor
      · dsimp [T]
        nlinarith [hω.2.2.2, hT]
      constructor
      · dsimp [T]
        nlinarith [hω.2.1, hT]
      constructor
      · dsimp [T]
        nlinarith [hω.2.2.1, hT]
      · have hULsub :
            (((kmswStage (fun i => ω (i + 1)) n).UL.length - 1 : ℕ) : ℝ) ≤
              ((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) := by
          exact_mod_cast Nat.sub_le _ _
        calc
          (((kmswStage (fun i => ω (i + 1)) n).UL.length - 1 : ℕ) : ℝ) ≤
              ((kmswStage (fun i => ω (i + 1)) n).UL.length : ℝ) := hULsub
          _ ≤ 2 * (T / 4) + 1 := hω.1
          _ ≤ T := by
            dsimp [T]
            nlinarith [hT]
    have htail' : 1 - 4 * Real.exp (-(T / 4) ^ 2 / (2 * (n : ℝ))) ≤
        iidCodeMeasure.real target := by
      exact htail.trans (MeasureTheory.measureReal_mono hsubset)
    have harg' : (T / 4) ^ 2 / (2 * (n : ℝ)) =
        (A ^ ε) ^ 2 / 32 := by
      calc
        (T / 4) ^ 2 / (2 * (n : ℝ)) = T ^ 2 / (32 * (n : ℝ)) := by ring
        _ = (A ^ ε) ^ 2 / 32 := by rw [harg]
    have hargExp : (-(T / 4) ^ 2) / (2 * (n : ℝ)) =
        -((A ^ ε) ^ 2 / 32) := by
      rw [show (-(T / 4) ^ 2) / (2 * (n : ℝ)) =
          -((T / 4) ^ 2 / (2 * (n : ℝ))) by ring, harg']
    rw [hargExp] at htail'
    exact htail'
  · have hTlt : T < 2 := lt_of_not_ge hT
    have hx : (A ^ ε) ^ 2 / 32 < 1 / 8 := by
      have hsmall : T ^ 2 / (32 * (n : ℝ)) < 1 / 8 := by
        rw [div_lt_iff₀ (by positivity : 0 < 32 * (n : ℝ))]
        nlinarith [sq_nonneg T, hTlt, hTpos, hnR]
      rw [harg]
      exact hsmall
    have hexp : (1 : ℝ) / 4 < Real.exp (-((A ^ ε) ^ 2 / 32)) := by
      have he := Real.add_one_le_exp (-((A ^ ε) ^ 2 / 32))
      nlinarith
    have hnonneg : 0 ≤ iidCodeMeasure.real target :=
      MeasureTheory.measureReal_nonneg
    have htrivial : 1 - 4 * Real.exp (-((A ^ ε) ^ 2 / 32)) ≤ 0 := by
      nlinarith
    exact htrivial.trans hnonneg

end DirectedDistances.PaperProofs.Section7
