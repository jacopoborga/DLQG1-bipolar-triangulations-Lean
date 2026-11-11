module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperAssembly














public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory ProbabilityTheory Quiver
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap

attribute [local instance 1100] presentDartQuiver

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
probabilistic cell conclusion consumed below, with one threshold uniform in all
positive cell sizes. This is an input proposition, not an asserted proof of Lemma 7.8.
Its definition does not use the disproved selected-target confinement premise. -/
@[expose] def boltzmannSdpUpper_cellInput : Prop :=
    ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ n : ℕ, 1 ≤ n →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          let w := fun i => ω (i + 1)
          (∀ x : ℕ,
            (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
              (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
            ∃ y : ℕ,
              (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
                (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) ∧
              sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
                (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)) ∧
          (∀ y : ℕ,
            (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
              (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
            ∃ x : ℕ,
              (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
                (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) ∧
              sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
                (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞))}

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
supplies an actual path; unreachable distance remains infinity. -/
private theorem path_of_sdp_le {V : Type*} [Quiver V] {a b : V} {K : ℕ}
    (h : sdp a b ≤ (K : ℕ∞)) : ∃ P : Quiver.Path a b, P.length ≤ K := by
  have hr : Reachable a b := by
    by_contra hn
    rw [sdp_eq_top_iff_not_reachable.mpr hn] at h
    exact (ENat.natCast_lt_top K).not_ge h
  obtain ⟨P, hP⟩ := exists_length_eq_sdp hr
  refine ⟨P, ?_⟩
  exact_mod_cast hP.trans_le h

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result. -/
private theorem sdpUpper_hit_measurable (r n : ℕ) :
    MeasurableSet {ω : ℕ → Fin 3 | ∃ k ≤ n,
      R (fun i => ω (i + 1)) k = -(r : ℤ)} := by
  have heq (ω : ℕ → Fin 3) (k : ℕ) :
      R (fun i => ω (i + 1)) k = (codeWalk ω k).2 := by
    simp [R, codeWalk, Prod.snd_sum]
  simp_rw [heq]
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun k => ?_
  by_cases hk : k ≤ n
  · have hm : Measurable (fun ω : ℕ → Fin 3 => (codeWalk ω k).2) :=
      ((measurable_pi_apply k).comp measurable_codeWalk).snd
    simpa only [hk, true_and, Set.preimage_singleton] using
      (measurableSet_singleton (-(r : ℤ))).preimage hm
  · simp only [hk, false_and, Set.ofPred_false, MeasurableSet.empty]

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
cell exponent `3/8` to the right-length exponent `3/4`, with a uniform constant. -/
private theorem sdpUpper_time_scaling (κ : ℝ) (hκ : 0 ≤ κ) (r : ℕ) (hr : 1 ≤ r) :
    (⌈κ * (r : ℝ) ^ 2⌉₊ : ℝ) ^ (3 / 8 : ℝ) ≤
      (κ + 1) ^ (3 / 8 : ℝ) * (r : ℝ) ^ (3 / 4 : ℝ) := by
  have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hnr : (⌈κ * (r : ℝ) ^ 2⌉₊ : ℝ) ≤ (κ + 1) * (r : ℝ) ^ 2 := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ κ * (r : ℝ) ^ 2 by positivity)
    nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have hp := Real.rpow_le_rpow (by positivity) hnr
    (by norm_num : (0 : ℝ) ≤ 3 / 8)
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast (r : ℝ) 2,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (r : ℝ))] at hp
  norm_num at hp ⊢
  exact hp

/- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
explicit cell conclusion and the existing OPEN cell-path interception proposition. -/
theorem boltzmann_sdp_upper_half_of_cellBullets
    (hcellInput : boltzmannSdpUpper_cellInput)
    (hintercept : boltzmannSdpUpper_cellPathInterception) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 1 < C ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q | ∃ j : Fin (q.1.1 + 1), q.2 ≤ j ∧
          ∃ P : Quiver.Path q.1.2.2.out.B.source (boltzmannSdpUpper_leftVertex q j),
            (P.length : ℝ) ≤ C * (r : ℝ) ^ (3 / 4 : ℝ)} := by
  intro δ hδ
  let ε := min δ 1
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ 1 := min_le_right _ _
  obtain ⟨α, hα, hcell⟩ :=
    hcellInput (ε / 2) (by positivity)
  let β := 8 / ε
  let κ := β ^ 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let C := α * (κ + 1) ^ (3 / 8 : ℝ) + 1
  have hC : 1 < C := by
    have hp : 0 < α * (κ + 1) ^ (3 / 8 : ℝ) :=
      mul_pos (by linarith only [hα]) (Real.rpow_pos_of_pos (by positivity) _)
    dsimp only [C]
    linarith only [hp]
  refine ⟨C, hC, fun r hr => ?_⟩
  let n : ℕ := ⌈κ * (r : ℝ) ^ 2⌉₊
  have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hβ8 : 8 ≤ β := by
    dsimp [β]
    rw [le_div_iff₀ hε]
    linarith only [hε1]
  have hnlo : κ * (r : ℝ) ^ 2 ≤ (n : ℝ) := Nat.le_ceil _
  have hn : 1 ≤ n := by
    have hκ1 : 1 ≤ κ := by dsimp [κ]; nlinarith only [hβ8]
    have hrr : 1 ≤ (r : ℝ) ^ 2 := by nlinarith only [hr1]
    have : 1 ≤ (n : ℝ) := (one_le_mul_of_one_le_of_one_le hκ1 hrr).trans hnlo
    exact_mod_cast this
  have hhit : 4 * (r : ℝ) / Real.sqrt (n : ℝ) ≤ ε / 2 := by
    have hs : (β * (r : ℝ)) ^ 2 ≤ (n : ℝ) := by
      dsimp [κ] at hnlo
      nlinarith only [hnlo]
    have hroot : β * (r : ℝ) ≤ Real.sqrt (n : ℝ) :=
      (Real.le_sqrt (by positivity) (by positivity)).2 hs
    have hden : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hq : (r : ℝ) / Real.sqrt (n : ℝ) ≤ 1 / β := by
      rw [div_le_div_iff₀ hden hβ]
      nlinarith only [hroot]
    calc
      4 * (r : ℝ) / Real.sqrt (n : ℝ) =
          4 * ((r : ℝ) / Real.sqrt (n : ℝ)) := by ring
      _ ≤ 4 * (1 / β) := mul_le_mul_of_nonneg_left hq (by norm_num)
      _ = ε / 2 := by dsimp [β]; field_simp; ring
  let E : Set (ℕ → Fin 3) := {ω |
    let w := fun i => ω (i + 1)
    ∀ x : ℕ,
      (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
        (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
      ∃ y : ℕ,
        (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
          (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) ∧
        sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
          (⌊α * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)}
  let H : Set (ℕ → Fin 3) := {ω | ∃ k ≤ n,
    R (fun i => ω (i + 1)) k = -(r : ℤ)}
  have hpE : 1 - ε / 2 ≤ iidCodeMeasure.real E :=
    (hcell α le_rfl n hn).trans (measureReal_mono (fun _ h => h.1))
  have hpH : 1 - ε / 2 ≤ iidCodeMeasure.real H := by
    have hp := iidSourceRightHitByTime_probability r n hr hn
    change 1 - 4 * (r : ℝ) / Real.sqrt (n : ℝ) ≤ iidCodeMeasure.real H at hp
    linarith only [hp, hhit]
  have hsum := measureReal_union_add_inter (μ := iidCodeMeasure)
    (s := E) (sdpUpper_hit_measurable r n)
  have hu : iidCodeMeasure.real (E ∪ H) ≤ 1 := measureReal_le_one
  have hp : 1 - δ ≤ iidCodeMeasure.real (E ∩ H) := by
    linarith only [hsum, hu, hpE, hpH, hεδ]
  let f := fun ω => stoppedMarked r hr (quadrantHatWalk ω)
  let T : Set (RightVertexMarkedBoltzmannSpace r) :=
    {q | ∃ j : Fin (q.1.1 + 1), q.2 ≤ j ∧
      ∃ P : Quiver.Path q.1.2.2.out.B.source (boltzmannSdpUpper_leftVertex q j),
        (P.length : ℝ) ≤ C * (r : ℝ) ^ (3 / 4 : ℝ)}
  have hsub : E ∩ H ≤ᵐ[iidCodeMeasure] f ⁻¹' T := by
    filter_upwards [hintercept] with ω hω hmem
    have hroot : ∃ e ∈ (kmswStage (fun i => ω (i + 1)) n).LL ++
        (kmswStage (fun i => ω (i + 1)) n).LR,
        (kmswStage (fun i => ω (i + 1)) n).west e = 0 ∨
          (kmswStage (fun i => ω (i + 1)) n).east e = 0 := by
      have hzero : 0 ∈ (kmswStage (fun i => ω (i + 1)) n).LR := by
        induction n with
        | zero => simp [kmswStage, kmswInit]
        | succ n ih =>
          obtain ⟨es, hes⟩ := kmswStage_LR_succ_eq_append (fun i => ω (i + 1)) n
          rw [hes]
          exact List.mem_append_left _ ih
      exact ⟨0, List.mem_append_right _ hzero,
        Or.inl (initial_edge_endpoints (fun i => ω (i + 1)) n).1⟩
    obtain ⟨y, hy, hd⟩ := hmem.1 0 hroot
    obtain ⟨P, hP⟩ := path_of_sdp_le hd
    obtain ⟨j, hj, Q, hQ⟩ := hω r hr n hmem.2 y hy P
    refine ⟨j, hj, Q, ?_⟩
    have hfloor := Nat.floor_le
      (show 0 ≤ α * (n : ℝ) ^ (3 / 8 : ℝ) by positivity)
    have hscale := sdpUpper_time_scaling κ hκ.le r hr
    have hlen : (Q.length : ℝ) ≤ α * (n : ℝ) ^ (3 / 8 : ℝ) := by
      exact (show (Q.length : ℝ) ≤ ⌊α * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ by
        exact_mod_cast hQ.trans hP).trans hfloor
    have hscaled := mul_le_mul_of_nonneg_left hscale (le_of_lt (lt_trans
      (by norm_num : (0 : ℝ) < 1) hα))
    dsimp only [C]
    change (n : ℝ) ^ (3 / 8 : ℝ) ≤ _ at hscale
    nlinarith only [hlen, hscaled, Real.rpow_pos_of_pos (by positivity :
      (0 : ℝ) < (r : ℝ)) (3 / 4 : ℝ)]
  have hf : AEMeasurable f iidCodeMeasure :=
    (measurable_stoppedMarked r hr).comp_aemeasurable aemeasurable_quadrantHatWalk
  have hm := iidCodeMeasure_map_quadrantHatWalk_stoppedMarked r hr
  have hT : MeasurableSet T := (Set.to_countable _).measurableSet
  have hmap : iidCodeMeasure.real (f ⁻¹' T) =
      (rightVertexMarkedBoltzmannLaw r).real T := by
    change (iidCodeMeasure (f ⁻¹' T)).toReal = _
    rw [← hm, Measure.real, Measure.map_apply_of_aemeasurable hf hT]
  exact hp.trans ((ENNReal.toReal_mono (by finiteness)
    (measure_mono_ae hsub)).trans_eq hmap)

/-- Helper (code level, SDP) toward Lemma 7.13 (lem-boltzmann-sdp-upper); not a paper result.
the exact cell conclusion. All three original geometric/symmetry propositions remain
explicit OPEN premises. This does not establish Lemma 7.13 or discharge any of them. -/
theorem boltzmann_sdp_upper_of_cellBullets_and_openProps
    (hcellInput : boltzmannSdpUpper_cellInput)
    (hintercept : boltzmannSdpUpper_cellPathInterception)
    (hmarkedRev : boltzmannSdpUpper_markedReversal)
    (hcross : boltzmannSdpUpper_boundaryPathIntersection) :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 1 < A ∧ ∀ r : ℕ, 1 ≤ r →
      1 - δ ≤ (rightVertexMarkedBoltzmannLaw r).real
        {q | ENat.toENNReal (presentDartSDP q.1.2.2.out.B.map
            q.1.2.2.out.B.source q.1.2.2.out.B.sink) ≤
          ENNReal.ofReal (A * (r : ℝ) ^ (3 / 4 : ℝ))} := by
  intro δ hδ
  obtain ⟨C, hC, hhalf⟩ := boltzmann_sdp_upper_half_of_cellBullets
    hcellInput hintercept (δ / 2) (by positivity)
  refine ⟨2 * C, by linarith only [hC], fun r hr => ?_⟩
  let := rightVertexMarkedBoltzmannLaw_isProbabilityMeasure_procedureReading r hr
  let μ := rightVertexMarkedBoltzmannLaw r
  obtain ⟨ρ, hρ, htransport⟩ := hmarkedRev r hr
  let F : Set (RightVertexMarkedBoltzmannSpace r) :=
    {q | ∃ j : Fin (q.1.1 + 1), q.2 ≤ j ∧
      ∃ P : Quiver.Path q.1.2.2.out.B.source (boltzmannSdpUpper_leftVertex q j),
        (P.length : ℝ) ≤ C * (r : ℝ) ^ (3 / 4 : ℝ)}
  have hF : MeasurableSet F := (Set.to_countable _).measurableSet
  have hpF : 1 - δ / 2 ≤ μ.real F := hhalf r hr
  have hpR : 1 - δ / 2 ≤ μ.real (ρ ⁻¹' F) := by
    have heq := hρ.measure_preimage hF.nullMeasurableSet
    change 1 - δ / 2 ≤ (μ (ρ ⁻¹' F)).toReal
    rw [heq]
    exact hpF
  have hp := probability_intersection_lower_bound μ F (ρ ⁻¹' F) hF
    (hF.preimage hρ.measurable) (δ / 2) (δ / 2) hpF hpR
  have hp' : 1 - δ ≤ μ.real (F ∩ (ρ ⁻¹' F)) := by
    linarith only [hp]
  refine hp'.trans (measureReal_mono ?_)
  intro q hq
  obtain ⟨j, hj, P, hP⟩ := hq.1
  obtain ⟨k, hk, Prev, hPrev⟩ := hq.2
  obtain ⟨i, hi, Q, hQ⟩ := htransport q k hk Prev
  obtain ⟨S, hS⟩ := boltzmannSdpUpper_splice P Q (hcross r q i j hi hj P Q)
  have hlen : (S.length : ℝ) ≤ (2 * C) * (r : ℝ) ^ (3 / 4 : ℝ) := by
    have hS' : (S.length : ℝ) ≤ P.length + Q.length := by exact_mod_cast hS
    rw [hQ] at hS'
    linarith only [hS', hP, hPrev]
  change ENat.toENNReal (sdp q.1.2.2.out.B.source q.1.2.2.out.B.sink) ≤ _
  calc
    ENat.toENNReal (sdp q.1.2.2.out.B.source q.1.2.2.out.B.sink) ≤
        ENat.toENNReal (S.length : ℕ∞) := ENat.toENNReal_mono (sdp_le_length S)
    _ = ENNReal.ofReal (S.length : ℝ) := by
      rw [ENat.toENNReal_coe, ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hlen


end DirectedDistances.PaperProofs.Section7
