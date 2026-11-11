module

public import DirectedDistances.KMSW.UIBHBOTWindowProb
public import DirectedDistances.KMSW.UIBHBOTAlmostSure
public import DirectedDistances.PaperProofs.Section5.DiskWindowGoodEvent
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Real

/-! Supporting lemmas for paper labels `prop-disk-bs-conv` (see CORRESPONDENCE.md). -/






public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.RandomWalk DirectedDistances.KMSW MeasureTheory Filter
open scoped Topology ENNReal






theorem prop516_disk_ball_identification
    (A : ℝ) (hA : 1 < A) (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ _K0 N n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) →
      (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) → ℓ ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q) →
      1 - 3 * ε ≤ (bridgeLevelLaw n ℓ).real
        {p | ∃ x, bridgeOptionWindow n N p = some x ∧
          ∀ n' : ℕ, (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n' →
            let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
            let w := fun i => p.1 (i + 1)
            kmswStageBallVertices (fun _ _ => True) (kmswStage w n') r
                (activeInitial w T) =
              (kmswStageBallVertices (fun _ _ => True)
                (kmswStage (windowCodeDecode N x) (2 * N)) r
                (activeInitial (windowCodeDecode N x) N)).image
                  (kmswWindowPatchVertexMap w (T - N) (2 * N))} := by
  obtain ⟨K0, N₀, hE⟩ := uibhbot_prob_windowEventK_ge r ε hε
  obtain ⟨N, _, n₀, hball⟩ :=
    diskWindow_prob_ball_eq_image_ge A hA r K0 N₀ ε hε hE
  exact ⟨K0, N, n₀, hball⟩






theorem prop516_uibhbot_ball_identification (r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 - ε ≤ uibhbotWordFamilyLaw.real
      {w | ∃ hw : ∀ k, IsStoppedExcursionWord (w k),
        let W := uibhbotCodeWord w (fun k => (hw k).1)
        let c := activeInitial (shiftedStream W N) N
        let S := kmswStageBallVertices (fun _ _ => True)
          (kmswStage (shiftedStream W N) (2 * N)) r c
        wholePlaneBallVertices W r (wholePlaneVertexι W N c) =
            (wholePlaneVertexι W N) '' (S : Set ℕ) ∧
          Set.BijOn (fun e : Fin (kmswStage (shiftedStream W N) (2 * N)).nextEdge =>
            wholePlaneEdgeι W N e.val)
            {e | (kmswStage (shiftedStream W N) (2 * N)).west e.val ∈ S ∧
              (kmswStage (shiftedStream W N) (2 * N)).east e.val ∈ S}
            {e | wholePlaneEdgeWest W e ∈
                wholePlaneBallVertices W r (wholePlaneVertexι W N c) ∧
              wholePlaneEdgeEast W e ∈
                wholePlaneBallVertices W r (wholePlaneVertexι W N c)}} := by
  let B : ℕ → Set (ℤ → List (Fin 3)) := fun N =>
    {w | ∃ hw : ∀ k, IsStoppedExcursionWord (w k),
      let W := uibhbotCodeWord w (fun k => (hw k).1)
      let c := activeInitial (shiftedStream W N) N
      let S := kmswStageBallVertices (fun _ _ => True)
        (kmswStage (shiftedStream W N) (2 * N)) r c
      wholePlaneBallVertices W r (wholePlaneVertexι W N c) =
          (wholePlaneVertexι W N) '' (S : Set ℕ) ∧
        Set.BijOn (fun e : Fin (kmswStage (shiftedStream W N) (2 * N)).nextEdge =>
          wholePlaneEdgeι W N e.val)
          {e | (kmswStage (shiftedStream W N) (2 * N)).west e.val ∈ S ∧
            (kmswStage (shiftedStream W N) (2 * N)).east e.val ∈ S}
          {e | wholePlaneEdgeWest W e ∈
              wholePlaneBallVertices W r (wholePlaneVertexι W N c) ∧
            wholePlaneEdgeEast W e ∈
              wholePlaneBallVertices W r (wholePlaneVertexι W N c)}}
  let E : ℕ → Set (ℤ → List (Fin 3)) := fun n => {w | ∀ N ≥ n, w ∈ B N}
  have hmono : Monotone E := by
    intro n m hnm w hw N hN
    exact hw N (hnm.trans hN)
  have hae : ∀ᵐ w ∂uibhbotWordFamilyLaw, w ∈ ⋃ n, E n := by
    filter_upwards [uibhbotWordFamilyLaw_ae_eventualWholePlaneBall] with w hw
    obtain ⟨hw, hball⟩ := hw
    obtain ⟨n, hn⟩ := hball r
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    intro N hN
    exact ⟨hw, (hn N hN).2.2⟩
  have hunion : uibhbotWordFamilyLaw (⋃ n, E n) = 1 := by
    calc
      _ = uibhbotWordFamilyLaw Set.univ := measure_congr (by
        filter_upwards [hae] with w hw
        simp only [Set.mem_univ]
        exact eq_true hw)
      _ = 1 := measure_univ
  have hlim := tendsto_measure_iUnion_atTop (μ := uibhbotWordFamilyLaw) hmono
  rw [hunion] at hlim
  have hreal : Tendsto (fun n => uibhbotWordFamilyLaw.real (E n))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [Measure.real, Function.comp_def, ENNReal.toReal_one] using
      (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hlim
  obtain ⟨n, hn⟩ := (hreal.eventually_const_lt (by linarith : 1 - ε < (1 : ℝ))).exists
  refine ⟨n, ?_⟩
  intro N hN
  exact hn.le.trans (measureReal_mono (fun w hw => hw N hN))






theorem prop516_window_ball_law_close
    (A : ℝ) (hA : 1 < A) (N : ℕ) {β : Type*} (Φ : (ℕ → Fin 3) → β)
    (_hΦ : ∀ u u', (∀ i < 2 * N, u i = u' i) → Φ u = Φ u')
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) →
      (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) → ℓ ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q) →
      ∀ C : Set (Option β),
        |(bridgeLevelLaw n ℓ).real
            ((fun p => (bridgeOptionWindow n N p).map (Φ ∘ windowCodeDecode N)) ⁻¹' C) -
          (uibhbotEncodingWindowLaw N).real
            ((fun x => some (Φ (windowCodeDecode N x))) ⁻¹' C)| ≤ ε := by
  obtain ⟨n₀, htv⟩ := diskWindow_id_tv A hA N ε hε
  refine ⟨n₀, ?_⟩
  intro n hn ℓ hlo hhi hℓn hcong C
  exact htv n hn ℓ hlo hhi hℓn hcong
    ((Option.map (Φ ∘ windowCodeDecode N)) ⁻¹' C)







theorem prop516_window_ball_edge_law_close
    (A : ℝ) (hA : 1 < A) (N r : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let Φ : (ℕ → Fin 3) → Finset ℕ × Finset (ℕ × ℕ × ℕ) := fun u =>
      let s := kmswStage u (2 * N)
      let S := kmswStageBallVertices (fun _ _ => True) s r (activeInitial u N)
      (S, ((Finset.range s.nextEdge).filter
        (fun e => s.west e ∈ S ∧ s.east e ∈ S)).image
          (fun e => (e, s.west e, s.east e)))
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ℓ : ℕ,
      A⁻¹ * Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) →
      (ℓ : ℝ) ≤ A * Real.sqrt (n : ℝ) → ℓ ≤ n →
      (∃ q : ℤ, (n : ℤ) = (ℓ : ℤ) + 3 * q) →
      ∀ C : Set (Option (Finset ℕ × Finset (ℕ × ℕ × ℕ))),
        |(bridgeLevelLaw n ℓ).real
            ((fun p => (bridgeOptionWindow n N p).map (Φ ∘ windowCodeDecode N)) ⁻¹' C) -
          (uibhbotEncodingWindowLaw N).real
            ((fun x => some (Φ (windowCodeDecode N x))) ⁻¹' C)| ≤ ε := by
  dsimp only
  apply prop516_window_ball_law_close A hA N _ _ ε hε
  intro u u' h
  have hs := kmswStage_congr h
  have hc := activeInitial_congr (n := N) (fun i hi => h i (by omega))
  rw [hs, hc]

end DirectedDistances.PaperProofs.Section5
