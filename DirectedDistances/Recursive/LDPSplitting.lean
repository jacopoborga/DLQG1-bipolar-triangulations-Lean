module

public import DirectedDistances.Recursive.BusemannShiftLaw
public import DirectedDistances.Recursive.LDPRelatingX1X

/-! Supporting lemmas for paper labels `lem:LDP-relating-X1-X`, `prop:LDP-recursive-equation`, `thm-busemann`, `thm-busemann-property` (see CORRESPONDENCE.md). -/














public section
namespace DirectedDistances.Recursive

open MeasureTheory ProbabilityTheory DirectedDistances.KMSW
open DirectedDistances.RandomWalk

private theorem ae_busemannVersion_all_data :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∀ (hfin : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => ω (i + 1)) n).nextEdge ∧
          ((kmswStage (fun i => ω (i + 1)) n).west e = v ∨
            (kmswStage (fun i => ω (i + 1)) n).east e = v)}.Finite)
        (h : BoundaryHitWitnesses (fun i => ω (i + 1))),
        IsBoundaryBusemannLDP
          (presentPathLengthsBounded_of_hfin (fun i => ω (i + 1)) hfin)
          (boundaryPresentVertex (fun i => ω (i + 1)) h)
          (busemannLDPMeasurableVersion ω) := by
  filter_upwards [iidCodes_ae_busemannLDPMeasurableVersion_eq,
    iidCodes_ae_existsUnique_eq_canonicalBusemannLDP] with ω heq hdata
  obtain ⟨hf, h, X, hX, -, hcanon⟩ := hdata
  intro hfin h'
  rw [heq, ← hcanon]
  exact hX





theorem iidCodes_ae_busemannLDPMeasurableVersion_relating_data :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      let X := busemannLDPMeasurableVersion ω
      let X1 := busemannLDPMeasurableVersion (fun i => ω (i + 1))
      ∃ hfin0 : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
      ∃ hfin1 : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage (fun i => w (1 + i)) n).nextEdge ∧
          ((kmswStage (fun i => w (1 + i)) n).west e = v ∨
            (kmswStage (fun i => w (1 + i)) n).east e = v)}.Finite,
      ∃ h0 : BoundaryHitWitnesses w,
      ∃ h1 : BoundaryHitWitnesses (fun i => w (1 + i)),
        IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin0)
          (boundaryPresentVertex w h0) X ∧
        IsBoundaryBusemannLDP
          (presentPathLengthsBounded_of_hfin (fun i => w (1 + i)) hfin1)
          (boundaryPresentVertex (fun i => w (1 + i)) h1) X1 ∧
        (ω 1 = 2 → (X (-1), X 1) =
          (X1 (-2) - max (X1 (-1)) 1, -max (X1 (-1)) 1)) ∧
        (ω 1 = 0 → (X (-1), X 1) = (-X1 1 - 1, -1)) ∧
        (ω 1 = 1 → (X (-1), X 1) = (X1 (-1), X1 2)) := by
  have hs := measurePreserving_codeShift_one.quasiMeasurePreserving.ae
    ae_busemannVersion_all_data
  filter_upwards [iidCodes_ae_ldp_relating_X1_X_all,
    ae_busemannVersion_all_data, hs] with ω hrel hbase hshift
  have heq : (fun i => codeShift 1 ω (i + 1)) =
      (fun i => ω ((1 + i) + 1)) := by
    funext i
    simp only [codeShift, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    rfl
  rw [heq, ← busemannLDPMeasurableVersion_shift_eq] at hshift
  obtain ⟨hfin0, hfin1, h0, h1, -, -, hall⟩ := hrel
  have hX := hbase hfin0 h0
  have hX1 := hshift hfin1 h1
  exact ⟨hfin0, hfin1, h0, h1, hX, hX1, hall _ _ hX hX1⟩

/-- The three first-step identities hold simultaneously for the measurable
representatives. Helper for `eq:splitting-proba` in -/
theorem iidCodes_ae_busemannLDPMeasurableVersion_firstStep :
    ∀ᵐ ω ∂iidCodeMeasure,
      let X := busemannLDPMeasurableVersion ω
      let X1 := busemannLDPMeasurableVersion (fun i => ω (i + 1))
      (ω 1 = 2 → (X (-1), X 1) =
        (X1 (-2) - max (X1 (-1)) 1, -max (X1 (-1)) 1)) ∧
      (ω 1 = 0 → (X (-1), X 1) = (-X1 1 - 1, -1)) ∧
      (ω 1 = 1 → (X (-1), X 1) = (X1 (-1), X1 2)) := by
  filter_upwards [iidCodes_ae_busemannLDPMeasurableVersion_relating_data] with ω hω
  obtain ⟨_, _, _, _, _, _, hp⟩ := hω
  exact hp

private theorem firstCode_mass (c : Fin 3) :
    iidCodeMeasure {ω | ω 1 = c} = (3 : ENNReal)⁻¹ := by
  have hinj : Function.Injective lazyTwoDimensionalStep := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [lazyTwoDimensionalStep]
  have hevent : {ω : ℕ → Fin 3 | ω 1 = c} =
      (fun ω => codeWalk ω (0 + 1) - codeWalk ω 0) ⁻¹'
        {lazyTwoDimensionalStep c} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
      codeWalk_succ_sub, zero_add]
    exact ⟨fun h => congrArg lazyTwoDimensionalStep h, fun h => hinj h⟩
  have hm : Measurable (fun ω : ℕ → Fin 3 =>
      codeWalk ω (0 + 1) - codeWalk ω 0) := by
    simp only [codeWalk_succ_sub]
    exact (measurable_of_countable lazyTwoDimensionalStep).comp (measurable_pi_apply 1)
  rw [hevent, ← Measure.map_apply hm (measurableSet_singleton _),
    map_codeWalk_increment, Measure.uniformOfFinset_apply_singleton]
  fin_cases c <;> norm_num [lazyTwoDimensionalStep]

private theorem measurable_shiftVersion :
    Measurable (fun ω : ℕ → Fin 3 =>
      busemannLDPMeasurableVersion (fun i => ω (i + 1))) :=
  (measurable_pi_iff.mpr measurable_busemannLDPMeasurableVersion).comp
    (measurable_pi_iff.mpr fun i => measurable_pi_apply (i + 1))

private theorem firstCode_inter_shiftVersion (c : Fin 3)
    (F : (ℤ → ℤ) → ℤ × ℤ) (hF : Measurable F) (p : ℤ × ℤ) :
    iidCodeMeasure {ω | ω 1 = c ∧
      F (busemannLDPMeasurableVersion (fun i => ω (i + 1))) = p} =
    (3 : ENNReal)⁻¹ * iidCodeMeasure {ω |
      F (busemannLDPMeasurableVersion (fun i => ω (i + 1))) = p} := by
  have h := indepFun_firstCode_busemannLDPMeasurableVersion_shift.measure_inter_preimage_eq_mul
    {c} (F ⁻¹' {p})
      (measurableSet_singleton c) (hF (measurableSet_singleton p))
  change iidCodeMeasure {ω | ω 1 = c ∧
      F (busemannLDPMeasurableVersion (fun i => ω (i + 1))) = p} =
    iidCodeMeasure {ω | ω 1 = c} * _ at h
  rw [firstCode_mass] at h
  exact h

/-- First-step splitting of the joint law, in `ENNReal`, for every integer
pair (no support restriction on `y`). This is `eq:splitting-proba`, a helper
in the proof of `prop:LDP-recursive-equation` -/
theorem iidCodeMeasure_busemannLDPMeasurableVersion_splitting (x y : ℤ) :
    iidCodeMeasure {ω | (busemannLDPMeasurableVersion ω (-1),
      busemannLDPMeasurableVersion ω 1) = (x, y)} =
    (3 : ENNReal)⁻¹ * iidCodeMeasure {ω |
      let X1 := busemannLDPMeasurableVersion (fun i => ω (i + 1))
      (X1 (-2) - max (X1 (-1)) 1, -max (X1 (-1)) 1) = (x, y)} +
    (3 : ENNReal)⁻¹ * iidCodeMeasure {ω |
      let X1 := busemannLDPMeasurableVersion (fun i => ω (i + 1))
      (-X1 1 - 1, -1) = (x, y)} +
    (3 : ENNReal)⁻¹ * iidCodeMeasure {ω |
      let X1 := busemannLDPMeasurableVersion (fun i => ω (i + 1))
      (X1 (-1), X1 2) = (x, y)} := by
  let F2 : (ℤ → ℤ) → ℤ × ℤ := fun X =>
    (X (-2) - max (X (-1)) 1, -max (X (-1)) 1)
  let F0 : (ℤ → ℤ) → ℤ × ℤ := fun X => (-X 1 - 1, -1)
  let F1 : (ℤ → ℤ) → ℤ × ℤ := fun X => (X (-1), X 2)
  have hm2 : Measurable F2 := by dsimp [F2]; fun_prop
  have hm0 : Measurable F0 := by dsimp [F0]; fun_prop
  have hm1 : Measurable F1 := by dsimp [F1]; fun_prop
  let A2 := {ω : ℕ → Fin 3 | ω 1 = 2 ∧
    F2 (busemannLDPMeasurableVersion (fun i => ω (i + 1))) = (x, y)}
  let A0 := {ω : ℕ → Fin 3 | ω 1 = 0 ∧
    F0 (busemannLDPMeasurableVersion (fun i => ω (i + 1))) = (x, y)}
  let A1 := {ω : ℕ → Fin 3 | ω 1 = 1 ∧
    F1 (busemannLDPMeasurableVersion (fun i => ω (i + 1))) = (x, y)}
  have hmA0 : MeasurableSet A0 :=
    ((measurable_pi_apply 1) (measurableSet_singleton 0)).inter
      ((hm0.comp measurable_shiftVersion) (measurableSet_singleton (x, y)))
  have hmA1 : MeasurableSet A1 :=
    ((measurable_pi_apply 1) (measurableSet_singleton 1)).inter
      ((hm1.comp measurable_shiftVersion) (measurableSet_singleton (x, y)))
  have hd20 : Disjoint A2 A0 := by
    apply Set.disjoint_left.mpr
    intro ω h2 h0
    have h := h2.1.symm.trans h0.1
    norm_num at h
  have hd1 : Disjoint (A2 ∪ A0) A1 := by
    apply Set.disjoint_left.mpr
    intro ω h h1
    rcases h with h2 | h0
    · have h := h2.1.symm.trans h1.1
      norm_num at h
    · have h := h0.1.symm.trans h1.1
      norm_num at h
  have hevent : {ω | (busemannLDPMeasurableVersion ω (-1),
      busemannLDPMeasurableVersion ω 1) = (x, y)} =ᵐ[iidCodeMeasure]
      (A2 ∪ A0) ∪ A1 := by
    filter_upwards [iidCodes_ae_busemannLDPMeasurableVersion_firstStep] with ω hω
    apply propext
    change _ ↔ ((ω 1 = 2 ∧ _) ∨ (ω 1 = 0 ∧ _)) ∨ (ω 1 = 1 ∧ _)
    have hc : ω 1 = 0 ∨ ω 1 = 1 ∨ ω 1 = 2 := by
      have hb := (ω 1).isLt
      omega
    rcases hc with hc | hc | hc
    · simp [hc, hω.2.1 hc, F0, F1, F2]
    · simp [hc, hω.2.2 hc, F0, F1, F2]
    · simp [hc, hω.1 hc, F0, F1, F2]
  calc
    _ = iidCodeMeasure ((A2 ∪ A0) ∪ A1) := measure_congr hevent
    _ = (iidCodeMeasure A2 + iidCodeMeasure A0) + iidCodeMeasure A1 := by
      rw [measure_union hd1 hmA1, measure_union hd20 hmA0]
    _ = _ := by
      rw [firstCode_inter_shiftVersion 2 F2 hm2 (x, y),
        firstCode_inter_shiftVersion 0 F0 hm0 (x, y),
        firstCode_inter_shiftVersion 1 F1 hm1 (x, y)]

private theorem shiftVersion_event_law (F : (ℤ → ℤ) → ℤ × ℤ)
    (hF : Measurable F) (p : ℤ × ℤ) :
    iidCodeMeasure {ω |
      F (busemannLDPMeasurableVersion (fun i => ω (i + 1))) = p} =
    iidCodeMeasure {ω | F (busemannLDPMeasurableVersion ω) = p} := by
  have h := congrArg (fun μ : Measure (ℤ → ℤ) => μ (F ⁻¹' {p}))
    iidCodeMeasure_map_busemannLDPMeasurableVersion_shift
  rw [Measure.map_apply measurable_shiftVersion (hF (measurableSet_singleton p)),
    Measure.map_apply (measurable_pi_iff.mpr measurable_busemannLDPMeasurableVersion)
      (hF (measurableSet_singleton p))] at h
  exact h

/-- The same splitting identity with `X` in every term on the right, by the
full process equality in law of `X¹` and `X`. Helper for `eq:splitting-proba`
This uses neither independence nor stationarity of Busemann increments. -/
theorem iidCodeMeasure_busemannLDPMeasurableVersion_splitting_self (x y : ℤ) :
    iidCodeMeasure {ω | (busemannLDPMeasurableVersion ω (-1),
      busemannLDPMeasurableVersion ω 1) = (x, y)} =
    (3 : ENNReal)⁻¹ * iidCodeMeasure {ω |
      let X := busemannLDPMeasurableVersion ω
      (X (-2) - max (X (-1)) 1, -max (X (-1)) 1) = (x, y)} +
    (3 : ENNReal)⁻¹ * iidCodeMeasure {ω |
      let X := busemannLDPMeasurableVersion ω
      (-X 1 - 1, -1) = (x, y)} +
    (3 : ENNReal)⁻¹ * iidCodeMeasure {ω |
      let X := busemannLDPMeasurableVersion ω
      (X (-1), X 2) = (x, y)} := by
  rw [iidCodeMeasure_busemannLDPMeasurableVersion_splitting]
  rw [shiftVersion_event_law (fun X =>
      (X (-2) - max (X (-1)) 1, -max (X (-1)) 1)) (by fun_prop),
    shiftVersion_event_law (fun X => (-X 1 - 1, -1)) (by fun_prop),
    shiftVersion_event_law (fun X => (X (-1), X 2)) (by fun_prop)]

end DirectedDistances.Recursive
