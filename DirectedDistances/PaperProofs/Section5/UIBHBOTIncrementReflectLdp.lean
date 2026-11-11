module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservableClose3

/-! LDP reflection via measurable mirror-closed finite-candidate events.
Reflection is proved first on code space, retaining finite-distance witnesses,
then transferred through the measurable equality event to the rooted-map law.
The faced-shell transport remains an explicit premise. No Close4 import is used. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter Quiver
open DirectedDistances.RandomWalk DirectedDistances.Recursive DirectedDistances.PlanarMap
open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The faced-ball topology underlying all measurable events in this module. -/
noncomputable local instance reflectLdp_Topology :
    TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The Borel measurable structure of the faced-ball topology. -/
noncomputable local instance reflectLdp_Measurable :
    MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The discrete measurable space for finite-increment options. -/
local instance reflectLdp_OptionMeasurable : MeasurableSpace (Option ℤ) := ⊤

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite-increment singleton sets are measurable. -/
local instance reflectLdp_OptionSingleton : MeasurableSingletonClass (Option ℤ) :=
  ⟨fun _ => trivial⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Intrinsic characterization and unbounded common reachable targets for the observable. -/
private def reflectLdp_ObservableData (M : RootedLocallyFinitePlanarMap) : Prop :=
  (∀ k : ℤ, ∃ N : ℕ, ∀ t : RootedLocallyFiniteVertex M.D M.rot,
    ¬ rootedLocallyFiniteWithinRadius M.toRootedLocallyFiniteMap N t →
    (∃ ds, incrementDartWalk M.toRootedLocallyFiniteMap ds
      (intrinsicIncrementSource M.toRootedLocallyFiniteMap k) t) →
    (∃ ds, incrementDartWalk M.toRootedLocallyFiniteMap ds
      (intrinsicIncrementSource M.toRootedLocallyFiniteMap (k - 1)) t) →
    ∃ a b : ℕ,
      intrinsicIncrementLdp M.toRootedLocallyFiniteMap
        (intrinsicIncrementSource M.toRootedLocallyFiniteMap k) t = ((a : ℕ∞) : WithBot ℕ∞) ∧
      intrinsicIncrementLdp M.toRootedLocallyFiniteMap
        (intrinsicIncrementSource M.toRootedLocallyFiniteMap (k - 1)) t =
          ((b : ℕ∞) : WithBot ℕ∞) ∧
      finiteBallIncrementObservable k M = (a : ℤ) - (b : ℤ)) ∧
  (∀ k : ℤ, ∀ T : Finset (RootedLocallyFiniteVertex M.D M.rot),
    ∃ t, t ∉ T ∧
      (∃ ds, incrementDartWalk M.toRootedLocallyFiniteMap ds
        (intrinsicIncrementSource M.toRootedLocallyFiniteMap k) t) ∧
      (∃ ds, incrementDartWalk M.toRootedLocallyFiniteMap ds
        (intrinsicIncrementSource M.toRootedLocallyFiniteMap (k - 1)) t))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Code-space intrinsic characterization, without any measurability premise on its data. -/
private theorem reflectLdp_ae_code_data
    (htransport : IncrementClose3FacedShellTransport) :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      reflectLdp_ObservableData (uibhbotRootedPlanarMapOfCode W) := by
  have hreal := finiteBallIncrementObservable_realization_of_ballShellStabilization
    (uibhbotIncrementBallShellStabilization_of_facedShellTransport htransport)
  filter_upwards [ae_incrementClose3_intrinsic_uniform_consensus,
    ae_incrementClose3_intrinsic_shell_nonempty, hreal,
    uibhbotRootedPlanarMapConullEvent_spec.2.1] with W hc hn hv hgood
  obtain ⟨H, hhit, C, hcap, hM⟩ :=
    (uibhbotRootedPlanarMapOfCode_on_event W hgood).1
  let M := uibhbotRootedLocallyFinitePlanarMap W H hhit C hcap
  have hvM (k : ℤ) : finiteBallIncrementObservable k M =
      uibhbotBusemannIncrement k W :=
    (congrArg (finiteBallIncrementObservable k) hM).symm.trans (hv k)
  rw [hM]
  constructor
  · intro k
    obtain ⟨N, hN⟩ := hc H hhit C k
    refine ⟨N, fun t ht h0 h1 => ?_⟩
    obtain ⟨a, b, ha, hb, hi⟩ := hN t ht h0 h1
    exact ⟨a, b, ha, hb, (hvM k).trans hi⟩
  · intro k T
    obtain ⟨R, _, hR⟩ := incrementClose3_vertexFinset_captured M.toRootedLocallyFiniteMap T 0
    obtain ⟨N, hN⟩ := hn H hhit C k
    obtain ⟨t, _, ht, h0, h1⟩ := hN (max N R) (le_max_left _ _)
    refine ⟨t, fun hmem => ht ?_, h0, h1⟩
    exact (mem_rootedLocallyFiniteRadiusVertices M.toRootedLocallyFiniteMap _ t).1
      (rootedLocallyFiniteRadiusVertices_mono M.toRootedLocallyFiniteMap (le_max_right N R)
        ((mem_rootedLocallyFiniteRadiusVertices M.toRootedLocallyFiniteMap R t).2
          (hR t hmem)))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every vertex outside a ball belongs to a later exact geometric shell. -/
private theorem reflectLdp_vertex_shell (M : RootedLocallyFiniteMap)
    (t : RootedLocallyFiniteVertex M.D M.rot) (N : ℕ)
    (ht : ¬ rootedLocallyFiniteWithinRadius M N t) :
    ∃ m ≥ N, rootedLocallyFiniteWithinRadius M (m + 1) t ∧
      ¬ rootedLocallyFiniteWithinRadius M m t := by
  classical
  have hex : ∃ r, rootedLocallyFiniteWithinRadius M r t := by
    obtain ⟨R, _, hR⟩ := incrementClose3_vertexFinset_captured M {t} 0
    exact ⟨R, hR t (Finset.mem_singleton_self _)⟩
  have hmin := Nat.find_spec hex
  have hlow : N < Nat.find hex := by
    by_contra! hn
    exact ht ((mem_rootedLocallyFiniteRadiusVertices M N t).1
      (rootedLocallyFiniteRadiusVertices_mono M hn
        ((mem_rootedLocallyFiniteRadiusVertices M (Nat.find hex) t).2 hmin)))
  refine ⟨Nat.find hex - 1, by omega, ?_, ?_⟩
  · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)] using hmin
  · exact Nat.find_min hex (by omega)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A finite candidate at every index is a countably specified event. -/
private def reflectLdp_CandidateEvent (M : RootedLocallyFinitePlanarMap) : Prop :=
  ∀ k : ℤ, ∃ z : ℤ, finiteBallIncrementCandidate k M = some z

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Countably many candidate fibers make the replacement data event measurable. -/
private theorem measurableSet_reflectLdp_CandidateEvent :
    MeasurableSet {M : RootedLocallyFinitePlanarMap | reflectLdp_CandidateEvent M} := by
  exact (Measurable.forall fun k : ℤ => Measurable.exists fun z : ℤ =>
    (measurable_finiteBallIncrementCandidate k).eq_const (some z)).setOf

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The proved shell stabilization realizes finite candidates simultaneously at all indices. -/
private theorem reflectLdp_ae_code_candidateEvent
    (htransport : IncrementClose3FacedShellTransport) :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      reflectLdp_CandidateEvent (uibhbotRootedPlanarMapOfCode W) := by
  filter_upwards [uibhbotIncrementBallShellStabilization_of_facedShellTransport htransport]
    with W hW k
  exact ⟨uibhbotBusemannIncrement k W,
    (finiteBallIncrementCandidate_eq_some_iff k _ _).2 (hW k)⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The measurable candidate event is conull for the existing rooted-map law. -/
private theorem ae_reflectLdp_CandidateEvent
    (htransport : IncrementClose3FacedShellTransport) :
    ∀ᵐ M ∂(uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap),
      reflectLdp_CandidateEvent M := by
  change ∀ᵐ M ∂((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    uibhbotRootedPlanarMapOfCode), reflectLdp_CandidateEvent M
  exact (ae_map_iff measurable_uibhbotRootedPlanarMapOfCode.aemeasurable
    measurableSet_reflectLdp_CandidateEvent).2 (reflectLdp_ae_code_candidateEvent htransport)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Intersect all forward mirror preimages to obtain a literally mirror-closed event.
This avoids identifying twice-reflected root dart representatives. -/
private def reflectLdp_MirrorClosedCandidateEvent (M : RootedLocallyFinitePlanarMap) : Prop :=
  ∀ n : ℕ, reflectLdp_CandidateEvent (mirrorRootedLocallyFinitePlanarMap^[n] M)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Countable intersections preserve measurability of the mirror-closed event. -/
private theorem measurableSet_reflectLdp_MirrorClosedCandidateEvent :
    MeasurableSet {M : RootedLocallyFinitePlanarMap |
      reflectLdp_MirrorClosedCandidateEvent M} := by
  exact (Measurable.forall fun n : ℕ =>
    (measurableSet_setOfPred.1 (measurableSet_reflectLdp_CandidateEvent.preimage
      (measurable_mirrorRootedLocallyFinitePlanarMap.iterate n)))).setOf

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The replacement event is closed under the actual mirror map. -/
private theorem reflectLdp_MirrorClosedCandidateEvent_mirror (M : RootedLocallyFinitePlanarMap)
    (h : reflectLdp_MirrorClosedCandidateEvent M) :
    reflectLdp_MirrorClosedCandidateEvent (mirrorRootedLocallyFinitePlanarMap M) := by
  intro n
  simpa only [Function.iterate_succ_apply] using h (n + 1)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Mirror-law invariance makes the countable mirror-closed event conull. -/
private theorem ae_reflectLdp_MirrorClosedCandidateEvent
    (htransport : IncrementClose3FacedShellTransport) :
    ∀ᵐ M ∂(uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap),
      reflectLdp_MirrorClosedCandidateEvent M := by
  apply ae_all_iff.mpr
  intro n
  induction n with
  | zero => exact ae_reflectLdp_CandidateEvent htransport
  | succ n ih =>
    have hmap : ∀ᵐ M ∂((uibhbotRootedPlanarMapLaw :
        Measure RootedLocallyFinitePlanarMap).map mirrorRootedLocallyFinitePlanarMap),
        reflectLdp_CandidateEvent (mirrorRootedLocallyFinitePlanarMap^[n] M) := by
      rw [uibhbotLaw_mirror_invariant
        DirectedDistances.PaperProofs.Section3.rootedPlanarMapLaw_hasOuterApproxClosed]
      exact ih
    have hm := ae_of_ae_map
      measurable_mirrorRootedLocallyFinitePlanarMap.aemeasurable hmap
    simpa only [Function.iterate_succ_apply] using hm

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A reachable finite extended LDP is attained by a finite directed dart walk. -/
private theorem reflectLdp_attaining (M : RootedLocallyFiniteMap)
    (s t : RootedLocallyFiniteVertex M.D M.rot) (n : ℕ)
    (hr : ∃ ds, incrementDartWalk M ds s t)
    (hn : intrinsicIncrementLdp M s t = ((n : ℕ∞) : WithBot ℕ∞)) :
    ∃ ds, incrementDartWalk M ds s t ∧ ds.length = n := by
  classical
  let S : Set ℕ := {l | ∃ ds, incrementDartWalk M ds s t ∧ ds.length = l}
  have hb : BddAbove S := by
    refine ⟨n, ?_⟩
    rintro l ⟨ds, hd, rfl⟩
    have he : ((ds.length : ℕ∞) : WithBot ℕ∞) ≤ intrinsicIncrementLdp M s t := by
      exact le_iSup_of_le ds (le_iSup_of_le hd le_rfl)
    exact_mod_cast he.trans_eq hn
  have hne : S.Nonempty := by
    obtain ⟨ds, hd⟩ := hr
    exact ⟨ds.length, ds, hd, rfl⟩
  obtain ⟨m, hm, hmax⟩ := hb.exists_isGreatest_of_nonempty hne
  obtain ⟨ds, hd, hl⟩ := hm
  have he : intrinsicIncrementLdp M s t = ((m : ℕ∞) : WithBot ℕ∞) := by
    apply le_antisymm
    · apply iSup_le
      intro es
      apply iSup_le
      intro hw
      exact WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr
        (hmax ⟨es, hw, rfl⟩))
    · rw [← hl]
      exact le_iSup_of_le ds (le_iSup_of_le hd le_rfl)
  have hmn : m = n := by exact_mod_cast he.symm.trans hn
  exact ⟨ds, hd, hl.trans hmn⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Intrinsic data on the original map and a finite reflected candidate force reflection.
Only genuinely finite ambient distances are compared with their restricted versions. -/
private theorem reflectLdp_reflection_of_data_and_candidate
    (htransport : IncrementClose3FacedShellTransport) (M : RootedLocallyFinitePlanarMap)
    (h : reflectLdp_ObservableData M)
    (hm : reflectLdp_CandidateEvent (mirrorRootedLocallyFinitePlanarMap M)) :
    finiteBallIncrementObservable 0 (mirrorRootedLocallyFinitePlanarMap M) =
      -finiteBallIncrementObservable 2 M := by
  classical
  let A := M.toRootedLocallyFiniteMap
  let B := mirrorRootedLocallyFiniteMap A
  let M' := mirrorRootedLocallyFinitePlanarMap M
  let e := incrementMirrorVertexEquiv A
  obtain ⟨z, hz⟩ := hm 0
  have hobs : finiteBallIncrementObservable 0 M' = z := by
    simp only [finiteBallIncrementObservable, hz, Option.getD_some, M']
  obtain ⟨R, hR⟩ := (finiteBallIncrementCandidate_eq_some_iff 0 M' z).1 hz
  obtain ⟨N, hN⟩ := h.1 2
  let T := rootedLocallyFiniteRadiusVertices A N ∪
    (rootedLocallyFiniteRadiusVertices B R).image e.symm
  obtain ⟨t, ht, h0, h1⟩ := h.2 2 T
  have htN : ¬ rootedLocallyFiniteWithinRadius A N t := by
    intro hn
    exact ht (Finset.mem_union_left _
      ((mem_rootedLocallyFiniteRadiusVertices A N t).2 hn))
  have htR : ¬ rootedLocallyFiniteWithinRadius B R (e t) := by
    intro hr
    apply ht
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨e t, (mem_rootedLocallyFiniteRadiusVertices B R (e t)).2 hr,
        e.symm_apply_apply t⟩
  obtain ⟨a, b, ha, hb, hi⟩ := hN t htN h0 h1
  have hm0 : ∃ ds, incrementDartWalk B ds (intrinsicIncrementSource B 0) (e t) := by
    obtain ⟨ds, hd⟩ := h1
    have hx := (incrementDartWalk_mirror A ds
      (intrinsicIncrementSource A (2 - 1)) t).2 hd
    refine ⟨ds, ?_⟩
    simpa only [intrinsicIncrementSource_mirror, sub_zero,
      show (2 : ℤ) - 1 = 1 from rfl, e, B] using hx
  have hm1 : ∃ ds, incrementDartWalk B ds (intrinsicIncrementSource B (0 - 1)) (e t) := by
    obtain ⟨ds, hd⟩ := h0
    have hx := (incrementDartWalk_mirror A ds (intrinsicIncrementSource A 2) t).2 hd
    refine ⟨ds, ?_⟩
    simpa only [intrinsicIncrementSource_mirror,
      show (1 : ℤ) - (0 - 1) = 2 from rfl, e, B] using hx
  have hmb : intrinsicIncrementLdp B (intrinsicIncrementSource B 0) (e t) =
      ((b : ℕ∞) : WithBot ℕ∞) := by
    simpa only [B, e, intrinsicIncrementSource_mirror, intrinsicIncrementLdp_mirror,
      sub_zero, show (2 : ℤ) - 1 = 1 from rfl] using hb
  have hma : intrinsicIncrementLdp B (intrinsicIncrementSource B (0 - 1)) (e t) =
      ((a : ℕ∞) : WithBot ℕ∞) := by
    simpa only [B, e, intrinsicIncrementSource_mirror, intrinsicIncrementLdp_mirror,
      show (1 : ℤ) - (0 - 1) = 2 from rfl] using ha
  obtain ⟨ds, hd, hl⟩ := reflectLdp_attaining B _ (e t) b hm0 hmb
  obtain ⟨es, he, hel⟩ := reflectLdp_attaining B _ (e t) a hm1 hma
  obtain ⟨S0, _, hS0⟩ := incrementClose_ballLdp_stabilizes_of_attaining B _ (e t) ds hd
    (hmb.trans (congrArg (fun n : ℕ => ((n : ℕ∞) : WithBot ℕ∞)) hl.symm)) 0
  obtain ⟨S1, _, hS1⟩ := incrementClose_ballLdp_stabilizes_of_attaining B _ (e t) es he
    (hma.trans (congrArg (fun n : ℕ => ((n : ℕ∞) : WithBot ℕ∞)) hel.symm)) 0
  obtain ⟨m, hmR, hnear, hfar⟩ := reflectLdp_vertex_shell B (e t) R htR
  obtain ⟨R0, hR0⟩ := hR m hmR
  obtain ⟨R1, hR1⟩ := htransport M' 0 m
  let r := max (max R0 R1) (max S0 S1)
  have hr0 : R0 ≤ r := (le_max_left _ _).trans (le_max_left _ _)
  have hr1 : R1 ≤ r := (le_max_right _ _).trans (le_max_left _ _)
  have hs0 : S0 ≤ r + 1 := by dsimp [r]; omega
  have hs1 : S1 ≤ r + 1 := by dsimp [r]; omega
  have hc := (hR1 r hr1 z).1
    ((finiteBallIncrementKernel_eq_some_iff 0 m _ z).1 (hR0 r hr0))
  have hdiff := hc.2 (e t) hnear hfar hm0 hm1
  change incrementClose3_finiteDifference
    (incrementClose_ballLdp B (r + 1) (intrinsicIncrementSource B 0) (e t))
    (incrementClose_ballLdp B (r + 1) (intrinsicIncrementSource B (0 - 1)) (e t)) =
      some z at hdiff
  rw [hS0 (r + 1) hs0, hS1 (r + 1) hs1] at hdiff
  change incrementClose3_intrinsicAt B 0 (e t) = some z at hdiff
  have horig : incrementClose3_intrinsicAt A 2 t =
      some (finiteBallIncrementObservable 2 M) := by
    apply (incrementClose3_finiteDifference_eq_some_iff _ _ _).2
    exact ⟨a, b, ha, hb, hi⟩
  have hmirror := incrementClose3_intrinsicAt_mirror A 0 t
  rw [sub_zero, horig] at hmirror
  have hzneg : z = -finiteBallIncrementObservable 2 M := by
    exact Option.some.inj (hdiff.symm.trans hmirror)
  exact hobs.trans hzneg

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Reflection follows from faced-shell transport alone. The measurable equality event
is transferred from code space, avoiding measurability of intrinsic data. -/
theorem uibhbotIncrementObservableReflection_ldpRoute2
    (htransport : IncrementClose3FacedShellTransport) :
    UIBHBOTIncrementObservableReflection finiteBallIncrementObservable := by
  have hm : MeasurableSet {M : RootedLocallyFinitePlanarMap |
      finiteBallIncrementObservable 0 (mirrorRootedLocallyFinitePlanarMap M) =
        -finiteBallIncrementObservable 2 M} :=
    (((finiteBallIncrementObservable_measurable 0).comp
      measurable_mirrorRootedLocallyFinitePlanarMap).eq
        (finiteBallIncrementObservable_measurable 2).neg).setOf
  change ∀ᵐ M ∂((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    uibhbotRootedPlanarMapOfCode), _
  apply (ae_map_iff measurable_uibhbotRootedPlanarMapOfCode.aemeasurable hm).2
  have hc := ae_of_ae_map measurable_uibhbotRootedPlanarMapOfCode.aemeasurable
    (ae_reflectLdp_MirrorClosedCandidateEvent htransport)
  filter_upwards [reflectLdp_ae_code_data htransport, hc] with W hW hC
  apply reflectLdp_reflection_of_data_and_candidate htransport _ hW
  exact (reflectLdp_MirrorClosedCandidateEvent_mirror _ hC) 0

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The measurable LDP increment at zero has symmetric law, conditional only on the
faced-shell transport. No transport or whole-paper completion is claimed here. -/
theorem hsym_ldp_of_facedShellTransport
    (htransport : IncrementClose3FacedShellTransport) :
    iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω) := by
  exact hsym_ldp_proved
    (uibhbotIncrementBallShellStabilization_of_facedShellTransport htransport)
    (uibhbotIncrementObservableReflection_ldpRoute2 htransport)

end DirectedDistances.PaperProofs.Section5
