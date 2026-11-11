module

public import DirectedDistances.KMSW.RawGeodesicTransport
import DirectedDistances.KMSW.DirectedContainClause2Graph
import DirectedDistances.KMSW.InfiniteGeodesicAnyStart
import DirectedDistances.KMSW.BusemannM0Unconditional

/-! Supporting lemmas for paper labels `lem-geo-infty` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory DirectedDistances.RandomWalk

private theorem measurable_records :
    MeasurableSet {w : ℕ → Fin 3 |
      {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j}.Infinite} := by
  have hR (n : ℕ) : Measurable (fun w : ℕ → Fin 3 => R w n) :=
    measurable_to_countable' (fun a => measurableSet_R n (fun b => b = a))
  have hL (n : ℕ) : Measurable (fun w : ℕ → Fin 3 => L w n) :=
    measurable_to_countable' (fun a => measurableSet_L n (fun b => b = a))
  have hm (n : ℕ) : MeasurableSet {w : ℕ → Fin 3 |
      (∀ j < n, R w n ≤ R w j - 1) ∧ ∀ j, n ≤ j → L w n ≤ L w j} := by
    have he : {w : ℕ → Fin 3 |
        (∀ j < n, R w n ≤ R w j - 1) ∧ ∀ j, n ≤ j → L w n ≤ L w j} =
        (⋂ j : ℕ, ⋂ (_ : j < n), {w | R w n ≤ R w j - 1}) ∩
          (⋂ j : ℕ, ⋂ (_ : n ≤ j), {w | L w n ≤ L w j}) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [he]
    exact (MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
      measurableSet_le (hR n) ((hR j).sub_const 1)))).inter
        (MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
          measurableSet_le (hL n) (hL j))))
  have he : {w : ℕ → Fin 3 |
      {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j}.Infinite} =
      ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N < n), {w : ℕ → Fin 3 |
        (∀ j < n, R w n ≤ R w j - 1) ∧ ∀ j, n ≤ j → L w n ≤ L w j} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    rw [Set.infinite_iff_exists_gt]
    constructor
    · intro hw N
      obtain ⟨n, hn, hN⟩ := hw N
      exact ⟨n, hN, hn⟩
    · intro hw N
      obtain ⟨n, hN, hn⟩ := hw N
      exact ⟨n, hn, hN⟩
  rw [he]
  exact MeasurableSet.iInter (fun _ => MeasurableSet.iUnion (fun n =>
    MeasurableSet.iUnion (fun _ => hm n)))

private theorem ae_extremal_of_code_law
    (F : (ℕ → Fin 3) → (ℕ → Fin 3)) (hF : Measurable F)
    (hlaw : iidCodeMeasure.map F =
      iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1)))) :
    ∀ᵐ ω ∂iidCodeMeasure,
      (∃ P : InfinitePresentPath (F ω) ⟨0⟩, P.HasLongestSegments) ∧
      (∃ P : InfinitePresentPath (F ω) ⟨0⟩, P.HasShortestSegments) := by
  have hrecords : ∀ᵐ w ∂iidCodeMeasure.map
      (fun ω => pitmanCode (fun i => ω (i + 1))),
      {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
        ∀ j, n ≤ j → L w n ≤ L w j}.Infinite :=
    (ae_map_iff measurable_pitmanCode_shift.aemeasurable measurable_records).2
      pitmanCodes_ae_infinite_cutSeparation_records
  have hpaths : ∀ᵐ w ∂iidCodeMeasure.map F,
      (∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments) ∧
      (∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) := by
    rw [hlaw]
    filter_upwards [hrecords] with w hw
    exact infinite_records_exists_allocated_infinite_extremal w hw ⟨0⟩
      (kmswVertexAllocated_all w ⟨0⟩)
  exact ae_of_ae_map hF.aemeasurable hpaths

private theorem ae_boundary_hat_extremal (k : ℤ) :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
      ∀ hτ : HasFlowLineHits
        (fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h k + i + 1)),
        let u := hatCodes
          (fun i => ω (boundaryHitTime (fun j => ω (j + 1)) h k + i + 1)) hτ
        (∃ P : InfinitePresentPath u ⟨0⟩, P.HasLongestSegments) ∧
        (∃ P : InfinitePresentPath u ⟨0⟩, P.HasShortestSegments) := by
  by_cases hk : k ≤ -1
  · have hF := measurable_rCodeSequence.comp
      (measurable_codeShift_toNat (codeFstFirstHit k)
        (measurableSet_codePast_codeFstFirstHit_eq k))
    have hp := ae_extremal_of_code_law _ hF
      (iidCodeMeasure_map_rCodeSequence_at_leftBoundaryHit_eq_pitmanCode k hk)
    filter_upwards [hp] with ω hω
    intro h hτ
    have ht : (codeFstFirstHit k ω).toNat =
        boundaryHitTime (fun i => ω (i + 1)) h k := by
      rw [codeFstFirstHit_eq_boundaryHitTime ω h hk]
      rfl
    dsimp only [Function.comp_def] at hω
    rw [ht, rCodeSequence_codeShift_boundaryHit_eq_hatCodes ω h k hτ] at hω
    exact hω
  · by_cases hk' : 1 ≤ k
    · have hF := measurable_rCodeSequence.comp
        (measurable_codeShift_toNat (codeSndFirstHit (-k))
          (measurableSet_codePast_codeSndFirstHit_eq (-k)))
      have hp := ae_extremal_of_code_law _ hF
        (iidCodeMeasure_map_rCodeSequence_at_rightBoundaryHit_eq_pitmanCode k hk')
      filter_upwards [hp] with ω hω
      intro h hτ
      have ht : (codeSndFirstHit (-k) ω).toNat =
          boundaryHitTime (fun i => ω (i + 1)) h k := by
        rw [codeSndFirstHit_eq_boundaryHitTime ω h hk']
        rfl
      dsimp only [Function.comp_def] at hω
      rw [ht, rCodeSequence_codeShift_boundaryHit_eq_hatCodes ω h k hτ] at hω
      exact hω
    · have hk0 : k = 0 := by omega
      subst k
      have hp := ae_extremal_of_code_law rCodeSequence
        measurable_rCodeSequence map_rCodeSequence
      filter_upwards [hp] with ω hω
      intro h hτ
      have he := rCodeSequence_codeShift_boundaryHit_eq_hatCodes ω h 0 hτ
      have hshift : rCodeSequence
          (codeShift (boundaryHitTime (fun i => ω (i + 1)) h 0) ω) =
          rCodeSequence ω := by
        apply rCodeSequence_eq_of_succ_eq
        intro i
        rw [boundaryHitTime_zero, codeShift_succ]
        simp only [Nat.zero_add]
      rw [hshift] at he
      rw [he] at hω
      exact hω



theorem iidCodes_ae_boundary_infinite_extremal :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
      ∀ k : ℤ,
        (∃ P : InfinitePresentPath (fun i => ω (i + 1))
          ⟨boundaryVertex (fun i => ω (i + 1)) h k⟩, P.HasLongestSegments) ∧
        (∃ P : InfinitePresentPath (fun i => ω (i + 1))
          ⟨boundaryVertex (fun i => ω (i + 1)) h k⟩, P.HasShortestSegments) := by
  have hall := ae_all_iff.mpr ae_boundary_hat_extremal
  filter_upwards [hall, iidCodes_ae_hasFlowLineHits_all_future_times] with ω hω hflow
  intro h k
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let hτ : HasFlowLineHits (fun i => w (boundaryHitTime w h k + i)) :=
    hflow (boundaryHitTime w h k)
  obtain ⟨⟨Q, hQ⟩, ⟨R, hR⟩⟩ := hω k h hτ
  obtain ⟨eφ, vφ, D⟩ := hatInputExists _ hτ
  obtain ⟨P, _, _, _, hlong, _⟩ := rawHat_infinitePath_transport w h k hτ D Q
  obtain ⟨S, _, _, _, _, hshort⟩ := rawHat_infinitePath_transport w h k hτ D R
  exact ⟨⟨P, hlong hQ⟩, ⟨S, hshort hR⟩⟩

end DirectedDistances.KMSW
