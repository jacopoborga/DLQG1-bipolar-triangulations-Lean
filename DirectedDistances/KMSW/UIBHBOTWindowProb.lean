module

public import DirectedDistances.KMSW.UIBHBOTWindowCaptureK
public import DirectedDistances.KMSW.WindowCodeDecoder
import DirectedDistances.RandomWalk.ExcursionBlockUniformTail
import DirectedDistances.RandomWalk.UIBHBOTForwardPrefixLaw
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Real

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.KMSW

open DirectedDistances.RandomWalk MeasureTheory Filter
open scoped Topology ENNReal

private theorem wordIntegral_succ_sub (W : ℤ → Fin 3) (t : ℤ) :
    wholePlaneWordIntegral W (t + 1) - wholePlaneWordIntegral W t =
      lazyTwoDimensionalStep (W t) := by
  have hcast (xs : List ℕ) :
      (Nat.cast <$> xs : List ℤ) = xs.map (fun i : ℕ => (i : ℤ)) := rfl
  have hp (n : ℕ) : wholePlaneWordIntegral W (n : ℤ) =
      ((List.range n).map (fun i : ℕ => lazyTwoDimensionalStep (W (i : ℤ)))).sum := by
    simp only [wholePlaneWordIntegral, ite_eq_left (by omega : 0 ≤ (n : ℤ)),
      Int.toNat_natCast, bind_pure_comp, hcast, List.map_map, Function.comp_def]
  have hn (n : ℕ) : wholePlaneWordIntegral W (-(n : ℤ)) =
      -((List.range n).map (fun i : ℕ => lazyTwoDimensionalStep (W (-(i : ℤ) - 1)))).sum := by
    cases n with
    | zero => simp [wholePlaneWordIntegral]
    | succ n =>
      have hz : ¬ 0 ≤ -((n + 1 : ℕ) : ℤ) := by omega
      simp only [wholePlaneWordIntegral, ite_eq_right hz, neg_neg, Int.toNat_natCast,
        bind_pure_comp, hcast, List.map_map, Function.comp_def]
  by_cases ht : 0 ≤ t
  · have ht' : t = (t.toNat : ℤ) := by omega
    rw [ht']
    rw [show (t.toNat : ℤ) + 1 = ((t.toNat + 1 : ℕ) : ℤ) by omega, hp, hp]
    simp [List.range_succ]
  · let n := (-t - 1).toNat
    have ht' : t = -((n + 1 : ℕ) : ℤ) := by dsimp [n]; omega
    have ht1 : t + 1 = -(n : ℤ) := by omega
    have harg : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
    rw [ht1, ht', hn, hn]
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [harg]
    abel





theorem windowCodeDecode_uibhbotConcatWalk (N : ℕ) (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) :
    ∀ i < 2 * N,
      windowCodeDecode N
        (fun j : Fin (2 * N + 1) => uibhbotConcatWalk w ((j : ℤ) - N)) i =
      shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N i := by
  classical
  intro i hi
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  let x := fun j : Fin (2 * N + 1) => uibhbotConcatWalk w ((j : ℤ) - N)
  have hdiff : lazyTwoDimensionalStep (shiftedStream W N i) =
      x ⟨i + 1, by omega⟩ - x ⟨i, by omega⟩ := by
    dsimp only [x, shiftedStream]
    rw [← wholePlaneWordIntegral_uibhbotCodeWord w (fun k => (hw k).1),
      ← wholePlaneWordIntegral_uibhbotCodeWord w (fun k => (hw k).1)]
    have htime : ((i + 1 : ℕ) : ℤ) - N = ((i : ℤ) - N) + 1 := by omega
    rw [htime]
    exact (wordIntegral_succ_sub W ((i : ℤ) - N)).symm
  have hex : ∃ c : Fin 3,
      lazyTwoDimensionalStep c = x ⟨i + 1, by omega⟩ - x ⟨i, by omega⟩ :=
    ⟨shiftedStream W N i, hdiff⟩
  change windowCodeDecode N x i = shiftedStream W N i
  unfold windowCodeDecode
  rw [dite_eq_left hi, dite_eq_left hex]
  exact lazyTwoDimensionalStep_injective ((Classical.choose_spec hex).trans hdiff.symm)





theorem kmswWindowCaptureEventK_windowCodeDecode_uibhbotConcatWalk
    (N r K0 : ℕ) (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k)) :
    kmswWindowCaptureEventK N r K0
        (windowCodeDecode N
          (fun j : Fin (2 * N + 1) => uibhbotConcatWalk w ((j : ℤ) - N))) ↔
      kmswWindowCaptureEventK N r K0
        (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) :=
  kmswWindowCaptureEventK_congr N r K0 _ _ (windowCodeDecode_uibhbotConcatWalk N w hw)

private theorem aemeasurable_concatWindow (N : ℕ) :
    AEMeasurable (fun w (j : Fin (2 * N + 1)) =>
      uibhbotConcatWalk w ((j : ℤ) - N)) uibhbotWordFamilyLaw := by
  let coords : (ℤ → List (Fin 3)) → Fin (2 * N) → List (Fin 3) := fun w i =>
    if i.val < N then w (i.val : ℤ) else w (-((i.val - N : ℕ) : ℤ) - 1)
  have hc : Measurable coords := by
    apply measurable_pi_iff.mpr
    intro i
    dsimp only [coords]
    split_ifs <;> exact measurable_pi_apply _
  apply ((measurable_uibhbotWindowFromWords N).comp hc).aemeasurable.congr
  filter_upwards [uibhbotWordFamilyLaw_ae_hP2] with w hw
  obtain ⟨hw, _⟩ := hw
  funext j
  exact (uibhbotConcatWalk_eq_uibhbotWindowFromWords N w
    (fun k _ _ => (hw k).1) j).symm




theorem uibhbot_prob_windowEventK_ge (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K0 N₀ : ℕ, ∀ N ≥ N₀,
      1 - ε ≤ (uibhbotEncodingWindowLaw N).real
        {x | kmswWindowCaptureEventK N r K0 (windowCodeDecode N x)} := by
  let A : ℕ → Set (ℤ → List (Fin 3)) := fun n =>
    {w | (∀ k, IsStoppedExcursionWord (w k)) ∧ ∀ N ≥ n,
      kmswWindowCaptureEventK N r n
        (windowCodeDecode N
          (fun j : Fin (2 * N + 1) => uibhbotConcatWalk w ((j : ℤ) - N)))}
  have hmono : Monotone A := by
    intro n m hnm w hw
    refine ⟨hw.1, ?_⟩
    intro N hN
    exact kmswWindowCaptureEventK_mono N r n m _ hnm (hw.2 N (hnm.trans hN))
  have hae : ∀ᵐ w ∂uibhbotWordFamilyLaw, w ∈ ⋃ n, A n := by
    filter_upwards [uibhbotWordFamilyLaw_ae_hP2,
      ae_uibhbotConcatWalk_snd_unbounded_below] with w hP2 hP1
    obtain ⟨hw, hP2⟩ := hP2
    obtain ⟨K, M, hKM⟩ := uibhbotCodeWord_eventualCaptureK w hw hP1 hP2 r
    refine Set.mem_iUnion.mpr ⟨max K M, hw, ?_⟩
    intro N hN
    apply (kmswWindowCaptureEventK_windowCodeDecode_uibhbotConcatWalk
      N r (max K M) w hw).mpr
    exact kmswWindowCaptureEventK_mono N r K (max K M) _ (Nat.le_max_left _ _)
      (hKM N ((Nat.le_max_right _ _).trans hN)).1
  have hunion : uibhbotWordFamilyLaw (⋃ n, A n) = 1 := by
    calc
      _ = uibhbotWordFamilyLaw Set.univ := measure_congr (by
        filter_upwards [hae] with w hw
        simp only [Set.mem_univ]
        exact eq_true hw)
      _ = 1 := measure_univ
  have hlim := tendsto_measure_iUnion_atTop (μ := uibhbotWordFamilyLaw) hmono
  rw [hunion] at hlim
  have hreal : Tendsto (fun n => uibhbotWordFamilyLaw.real (A n)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Measure.real, Function.comp_def, ENNReal.toReal_one] using
      (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hlim
  obtain ⟨n, hn⟩ := (hreal.eventually_const_lt (by linarith : 1 - ε < (1 : ℝ))).exists
  refine ⟨n, n, ?_⟩
  intro N hN
  rw [uibhbotEncodingWindowLaw, map_measureReal_apply_of_aemeasurable
    (aemeasurable_concatWindow N) (Set.to_countable _).measurableSet]
  exact hn.le.trans (measureReal_mono (fun w hw => hw.2 N hN))

end DirectedDistances.KMSW
