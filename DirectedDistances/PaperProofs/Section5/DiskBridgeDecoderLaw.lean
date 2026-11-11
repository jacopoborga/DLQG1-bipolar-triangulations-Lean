/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.DiskBridgeClassTransport
public import DirectedDistances.PaperProofs.Section5.DiskCodeMarkUniform
public import DirectedDistances.KMSW.KMSWDiskFiniteSample







public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory DirectedDistances.RandomWalk
  DirectedDistances.KMSW DirectedDistances.PlanarMap
open scoped ENNReal





def diskBridgePrefix (n : ℕ) (p : (ℕ → Fin 3) × ℕ) : Fin n → Fin 3 :=
  fun i => p.1 (i.val + 1)

private theorem measurable_diskBridgePrefix (n : ℕ) :
    Measurable (diskBridgePrefix n) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply (i.val + 1)).comp measurable_fst





noncomputable def diskBridgeDecoderCore
    (ell n : ℕ) (hell : 1 ≤ ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = ell + 3 * q) :
    (Fin n → Fin 3) × ℕ →
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} × Fin ell := by
  classical
  let F : KMSWLeftWalkClass (ell + 1) n ≃
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} :=
    kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let defaultWalk : KMSWLeftWalkClass (ell + 1) n :=
    Classical.choice (kmswLeftWalkClass_nonempty_of_domain ell n hell hle hmod)
  exact fun p =>
    if hc : KMSWLeftWalkAdmissible (ell + 1) n p.1 then
      if hk : 1 ≤ p.2 ∧ p.2 ≤ ell then
        (F ⟨p.1, hc⟩, ⟨p.2 - 1, by omega⟩)
      else (F defaultWalk, ⟨0, by omega⟩)
    else (F defaultWalk, ⟨0, by omega⟩)





@[expose] noncomputable def diskBridgeDecoder
    (ell n : ℕ) (hell : 1 ≤ ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = ell + 3 * q) :
    (ℕ → Fin 3) × ℕ →
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} × Fin ell :=
  diskBridgeDecoderCore ell n hell hle hmod ∘
    (fun p => (diskBridgePrefix n p, p.2))






theorem measurable_diskBridgeDecoder
    (ell n : ℕ) (hell : 1 ≤ ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = ell + 3 * q) :
    let F : KMSWLeftWalkClass (ell + 1) n ≃
        {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} :=
      kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
    letI : MeasurableSpace (KMSWLeftWalkClass (ell + 1) n) := ⊤
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    Measurable (diskBridgeDecoder ell n hell hle hmod) := by
  classical
  dsimp only
  let mQ : MeasurableSpace
      ({q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}) := ⊤
  let mK : MeasurableSpace (Fin ell) := ⊤
  let mOut : MeasurableSpace
      ({q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} × Fin ell) :=
        @Prod.instMeasurableSpace _ _ mQ mK
  have hcore : @Measurable ((Fin n → Fin 3) × ℕ)
      ({q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} × Fin ell)
      inferInstance mOut (diskBridgeDecoderCore ell n hell hle hmod) := by
    exact measurable_of_countable _
  exact hcore.comp (Measurable.prodMk (measurable_diskBridgePrefix n) measurable_snd)


private theorem measurableSet_diskBridgeCone (ell n : ℕ) :
    MeasurableSet (coneEvent (ell : ℤ) 0 n) := by
  simp only [coneEvent, Set.ofPred_and]
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
    have hj := (measurable_pi_apply j).comp measurable_codeWalk
    simp only [Set.ofPred_and]
    exact (measurableSet_le measurable_const (measurable_const.add hj.fst)).inter
      (measurableSet_le measurable_const (measurable_const.add hj.snd))
  · exact (measurable_const.add ((measurable_pi_apply n).comp measurable_codeWalk))
      (measurableSet_singleton (0, 0))

private theorem diskBridgePrefix_admissible (ell n : ℕ) (p : (ℕ → Fin 3) × ℕ)
    (hp : p.1 ∈ coneEvent (ell : ℤ) 0 n) :
    KMSWLeftWalkAdmissible (ell + 1) n (diskBridgePrefix n p) := by
  have hwalk (j : ℕ) (hj : j ≤ n) :
      integrateCodes (finiteCodeExtend (n := n + 1) (diskBridgePrefix n p)) j =
        codeWalk p.1 j := by
    rw [codeWalk_eq_integrateCodes]
    unfold integrateCodes
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
    simp [finiteCodeExtend, hin, diskBridgePrefix]
  change (∀ j ≤ n,
      0 ≤ (((ell : ℤ), (0 : ℤ)) + codeWalk p.1 j).1 ∧
        0 ≤ (((ell : ℤ), (0 : ℤ)) + codeWalk p.1 j).2) ∧
    ((ell : ℤ), (0 : ℤ)) + codeWalk p.1 n = (0, 0) at hp
  unfold KMSWLeftWalkAdmissible
  rw [show ((ell + 1 : ℕ) : ℤ) - 1 = (ell : ℤ) by omega]
  refine ⟨?_, ?_⟩
  · rw [hwalk n le_rfl]
    exact hp.2
  · intro j hj
    have hjn : j ≤ n := by
      have := Finset.mem_range.mp hj
      omega
    rw [hwalk j hjn]
    exact hp.1 j hjn

private theorem ae_diskBridge_support (ell n : ℕ) :
    ∀ᵐ p ∂bridgeLevelLaw n ell,
      p.1 ∈ coneEvent (ell : ℤ) 0 n ∧ 1 ≤ p.2 ∧ p.2 ≤ ell := by
  have hc : (cond iidCodeMeasure (coneEvent (ell : ℤ) 0 n))
      (coneEvent (ell : ℤ) 0 n)ᶜ = 0 := by
    rw [ProbabilityTheory.cond_apply (measurableSet_diskBridgeCone ell n)]
    simp
  have hk : Measure.uniformOfFinset (Finset.Icc 1 ell)
      (Finset.Icc 1 ell : Set ℕ)ᶜ = 0 := by
    rw [Measure.uniformOfFinset_apply]
    simp
  have hs := Measure.measure_prod_compl_eq_zero hc hk
  apply (ae_iff.mpr hs).mono
  intro p hp
  have hp' : p ∈ coneEvent (ell : ℤ) 0 n ×ˢ (Finset.Icc 1 ell : Set ℕ) := by
    simpa only [not_not] using hp
  exact ⟨hp'.1, Finset.mem_Icc.mp hp'.2⟩




theorem bridgeLevelLaw_map_diskBridgeDecoder
    (ell n : ℕ) (hell : 1 ≤ ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = ell + 3 * q) :
    let F : KMSWLeftWalkClass (ell + 1) n ≃
        {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} :=
      kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
    letI : MeasurableSpace (KMSWLeftWalkClass (ell + 1) n) := ⊤
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    (bridgeLevelLaw n ell).map (diskBridgeDecoder ell n hell hle hmod) =
      (uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell)) := by
  classical
  let F : KMSWLeftWalkClass (ell + 1) n ≃
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} :=
    kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace (KMSWLeftWalkClass (ell + 1) n) := ⊤
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  change (bridgeLevelLaw n ell).map (diskBridgeDecoder ell n hell hle hmod) =
    (uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))
  have hm : Measurable (diskBridgeDecoder ell n hell hle hmod) :=
    measurable_diskBridgeDecoder ell n hell hle hmod
  apply Measure.ext_of_singleton
  rintro ⟨q, k⟩
  rw [Measure.map_apply hm (measurableSet_singleton (q, k))]
  have hfiber :
      diskBridgeDecoder ell n hell hle hmod ⁻¹' { (q, k) } =ᵐ[bridgeLevelLaw n ell]
        {p | (∀ i : Fin n, p.1 (i.val + 1) = (F.symm q).val i) ∧
          p.2 = k.val + 1} := by
    filter_upwards [ae_diskBridge_support ell n] with p hp
    have ha := diskBridgePrefix_admissible ell n p hp.1
    have hd : diskBridgeDecoder ell n hell hle hmod p =
        (F ⟨diskBridgePrefix n p, ha⟩, ⟨p.2 - 1, by omega⟩) := by
      simp only [diskBridgeDecoder, Function.comp_apply, diskBridgeDecoderCore]
      rw [dite_eq_left ha, dite_eq_left hp.2]
    apply propext
    change (diskBridgeDecoder ell n hell hle hmod p = (q, k)) ↔ _
    rw [hd]
    constructor
    · intro he
      have hq := congrArg Prod.fst he
      have hk := congrArg (fun z : Q × Fin ell => z.2.val) he
      have hc : (⟨diskBridgePrefix n p, ha⟩ : KMSWLeftWalkClass (ell + 1) n) =
          F.symm q := F.injective (hq.trans (F.apply_symm_apply q).symm)
      refine ⟨?_, by dsimp at hk; omega⟩
      intro i
      exact congrFun (congrArg Subtype.val hc) i
    · rintro ⟨hc, hk⟩
      apply Prod.ext
      · have hcodes : diskBridgePrefix n p = (F.symm q).val := funext hc
        have hsub : (⟨diskBridgePrefix n p, ha⟩ : KMSWLeftWalkClass (ell + 1) n) =
            F.symm q := Subtype.ext hcodes
        exact (congrArg F hsub).trans (F.apply_symm_apply q)
      · apply Fin.ext
        dsimp
        omega
  rw [measure_congr hfiber]
  exact bridgeLevelLaw_diskClassMark_singleton ell n hell hle hmod q k




theorem bridgeLevelLaw_map_diskBridgeDecoder_symm
    (ell n : ℕ) (hell : 1 ≤ ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = ell + 3 * q) :
    let F : KMSWLeftWalkClass (ell + 1) n ≃
        {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} :=
      kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
    letI : MeasurableSpace (KMSWLeftWalkClass (ell + 1) n) := ⊤
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    (bridgeLevelLaw n ell).map (fun p =>
      let d := diskBridgeDecoder ell n hell hle hmod p
      (F.symm d.1, Fin.cast (by omega : ell = (ell + 1) - 1) d.2)) =
      (uniformCountingMeasure (KMSWLeftWalkClass (ell + 1) n)).prod
        (uniformCountingMeasure (Fin ((ell + 1) - 1))) := by
  classical
  let F : KMSWLeftWalkClass (ell + 1) n ≃
      {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled} :=
    kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) F
  let : MeasurableSpace (KMSWLeftWalkClass (ell + 1) n) := ⊤
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let g : Q × Fin ell → KMSWLeftWalkClass (ell + 1) n × Fin ((ell + 1) - 1) :=
    fun p => (F.symm p.1, Fin.cast (by omega : ell = (ell + 1) - 1) p.2)
  have hg : Measurable g := measurable_of_countable g
  have hm : Measurable (diskBridgeDecoder ell n hell hle hmod) :=
    measurable_diskBridgeDecoder ell n hell hle hmod
  have hu : ((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).map g =
      (uniformCountingMeasure (KMSWLeftWalkClass (ell + 1) n)).prod
        (uniformCountingMeasure (Fin ((ell + 1) - 1))) :=
    kmswDiskFiniteSample_uniform_prod (ell + 1) n (by omega)
  have h := congrArg (fun μ => μ.map g)
    (bridgeLevelLaw_map_diskBridgeDecoder ell n hell hle hmod)
  rw [Measure.map_map hg hm, hu] at h
  exact h

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem diskBridgePrefix_apply (n : ℕ) (p : (ℕ → Fin 3) × ℕ) (i : Fin n) :
    diskBridgePrefix n p i = p.1 (i.val + 1) := by
  unfold diskBridgePrefix
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem diskBridgeDecoderCore_eq_on_support
    (ell n : ℕ) (hell : 1 ≤ ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = ell + 3 * q)
    (p : (Fin n → Fin 3) × ℕ)
    (hadm : KMSWLeftWalkAdmissible (ell + 1) n p.1)
    (hlo : 1 ≤ p.2) (hhi : p.2 ≤ ell) :
    diskBridgeDecoderCore ell n hell hle hmod p =
      (kmswLeftEndpointSideEquiv (ell + 1) n (by omega) ⟨p.1, hadm⟩,
        ⟨p.2 - 1, by omega⟩) := by
  simp [diskBridgeDecoderCore, hadm, hlo, hhi]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem diskBridgeDecoder_eq_on_support
    (ell n : ℕ) (hell : 1 ≤ ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = ell + 3 * q)
    (p : (ℕ → Fin 3) × ℕ)
    (hadm : KMSWLeftWalkAdmissible (ell + 1) n (diskBridgePrefix n p))
    (hlo : 1 ≤ p.2) (hhi : p.2 ≤ ell) :
    diskBridgeDecoder ell n hell hle hmod p =
      (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
          ⟨diskBridgePrefix n p, hadm⟩,
        ⟨p.2 - 1, by omega⟩) := by
  change diskBridgeDecoderCore ell n hell hle hmod
      (diskBridgePrefix n p, p.2) = _
  rw [diskBridgeDecoderCore_eq_on_support ell n hell hle hmod
    (diskBridgePrefix n p, p.2)
    hadm hlo hhi]

end DirectedDistances.PaperProofs.Section5
