module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservableClose2
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMirrorContinuity

/-! Uniform intrinsic distance stabilization toward finite faced-ball shell consensus.

The intrinsic results below retain the complete dart and extended-distance carriers.
They do not identify simple distances in faced-ball class representatives with
restricted intrinsic distances. The remaining finite-carrier obligations are recorded
explicitly below and are neither assumed nor asserted as proved. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter Quiver
open DirectedDistances.RandomWalk DirectedDistances.Recursive DirectedDistances.PlanarMap
open DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The topology used by the existing rooted-map law. -/
noncomputable local instance incrementClose3Topology :
    TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The Borel structure used by the existing rooted-map law. -/
noncomputable local instance incrementClose3MeasurableSpace :
    MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The measurable representative satisfies the full one-sided characterization. -/
private theorem incrementClose3_ae_busemann_data :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hb : PresentPathLengthsBounded (w := fun i => ω (i + 1)),
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        IsBoundaryBusemannLDP hb (boundaryPresentVertex _ h)
          (busemannLDPMeasurableVersion ω) := by
  filter_upwards [iidCodes_ae_busemannLDPMeasurableVersion_eq,
    iidCodes_ae_existsUnique_eq_canonicalBusemannLDP] with ω heq hdata
  obtain ⟨hfin, h, X, hX, _, hcanon⟩ := hdata
  refine ⟨presentPathLengthsBounded_of_hfin _ hfin, h, ?_⟩
  rw [heq, ← hcanon]
  exact hX

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
All future copies simultaneously satisfy the full characterization. -/
private theorem incrementClose3_ae_future_data :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∃ hb : PresentPathLengthsBounded (w := fun i => uibhbotFutureCode k W (i + 1)),
      ∃ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
        IsBoundaryBusemannLDP hb (boundaryPresentVertex _ h)
          (busemannLDPMeasurableVersion (uibhbotFutureCode k W)) := by
  apply ae_all_iff.mpr
  intro k
  have h := incrementClose3_ae_busemann_data
  rw [← uibhbotFutureCode_law k] at h
  exact ae_of_ae_map (measurable_uibhbotFutureCode k).aemeasurable h

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Reachable bounded path lengths give the stated finite extended distance. -/
private theorem incrementClose3_presentLdp_eq {w : ℕ → Fin 3}
    (hb : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (hr : Reachable a b) :
    presentLdp a b = ((presentLdpFiniteNat hb hr : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hb a b hr) hr
  rw [presentLdp_eq_length hp, presentLdpFiniteNat_eq_length hb hr hp]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every distinct common reachable target sequence characterizes the increment;
targets need not belong to the explicit boundary target sequence. -/
theorem ae_incrementClose3_sequence_characterization :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ z : ℕ → UIBHBOTPresentVertex W, Function.Injective z →
      (∀ m, Reachable (uibhbotBusemannSource k W) (z m) ∧
        Reachable (uibhbotBusemannSource (k - 1) W) (z m)) →
      ∃ N : ℕ, ∀ m ≥ N, ∃ a b : ℕ,
        uibhbotLdp (uibhbotBusemannSource k W) (z m) =
            ((a : ℕ∞) : WithBot ℕ∞) ∧
        uibhbotLdp (uibhbotBusemannSource (k - 1) W) (z m) =
            ((b : ℕ∞) : WithBot ℕ∞) ∧
        uibhbotBusemannIncrement k W = (a : ℤ) - (b : ℤ) := by
  classical
  filter_upwards [incrementClose3_ae_future_data, ae_uibhbotFutureBoundary_index,
    ae_uibhbotFuture_boundary_ldp, ae_uibhbotFuture_boundary_path_lift]
    with W hdata hi hd hl k z hz hr
  obtain ⟨hb, h, hX⟩ := hdata k
  let w := fun i => uibhbotFutureCode k W (i + 1)
  let x := boundaryPresentVertex w h
  let F := uibhbotFutureToGlobal k W
  have hs0 : F.obj (x 0) = uibhbotBusemannSource k W := by
    apply congrArg UIBHBOTPresentVertex.mk
    simpa only [x, w, boundaryPresentVertex, add_zero] using hi k h 0 (by omega)
  have hs1 : F.obj (x (-1)) = uibhbotBusemannSource (k - 1) W := by
    apply congrArg UIBHBOTPresentVertex.mk
    simpa only [x, w, boundaryPresentVertex, sub_eq_add_neg] using hi k h (-1) (by omega)
  have hp : ∀ m, ∃ c : PresentVertex w, F.obj c = z m ∧ Reachable (x 0) c := by
    intro m
    have hrm := (hr m).1
    rw [← hs0] at hrm
    obtain ⟨p⟩ := hrm
    obtain ⟨c, q, hc, _, _⟩ := hl k h 0 (by omega) (z m) p
    exact ⟨c, hc, ⟨q⟩⟩
  choose y hy hy0 using hp
  have hy1 : ∀ m, Reachable (x (-1)) (y m) := by
    intro m
    have hrm := (hr m).2
    rw [← hs1] at hrm
    obtain ⟨p⟩ := hrm
    obtain ⟨c, q, hc, _, _⟩ := hl k h (-1) (by omega) (z m) p
    have he : c = y m := uibhbotFutureToGlobal_obj_injective k W
      (hc.trans (hy m).symm)
    subst c
    exact ⟨q⟩
  have hiy : Function.Injective y := by
    intro a b hab
    apply hz
    rw [← hy a, ← hy b, hab]
  obtain ⟨N, hN⟩ := hX.2 (-1) 0 y hiy (fun m => ⟨hy1 m, hy0 m⟩)
  refine ⟨N, fun m hm =>
    ⟨presentLdpFiniteNat hb (hy0 m), presentLdpFiniteNat hb (hy1 m), ?_, ?_, ?_⟩⟩
  · rw [← hs0, ← hy m]
    exact (hd k h 0 (by omega) (y m)).trans
      (incrementClose3_presentLdp_eq hb (hy0 m))
  · rw [← hs1, ← hy m]
    exact (hd k h (-1) (by omega) (y m)).trans
      (incrementClose3_presentLdp_eq hb (hy1 m))
  · simpa only [uibhbotBusemannIncrement, ldpIncrement, zero_sub] using hN m hm

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
This upgrades sequential convergence to simultaneous consensus outside a finite set. -/
theorem ae_incrementClose3_finite_exceptions :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      {t : UIBHBOTPresentVertex W |
        Reachable (uibhbotBusemannSource k W) t ∧
        Reachable (uibhbotBusemannSource (k - 1) W) t ∧
        ¬ ∃ a b : ℕ,
          uibhbotLdp (uibhbotBusemannSource k W) t = ((a : ℕ∞) : WithBot ℕ∞) ∧
          uibhbotLdp (uibhbotBusemannSource (k - 1) W) t =
            ((b : ℕ∞) : WithBot ℕ∞) ∧
          uibhbotBusemannIncrement k W = (a : ℤ) - (b : ℤ)}.Finite := by
  classical
  filter_upwards [ae_incrementClose3_sequence_characterization] with W hW k
  by_contra hinf
  let S := {t : UIBHBOTPresentVertex W |
    Reachable (uibhbotBusemannSource k W) t ∧
    Reachable (uibhbotBusemannSource (k - 1) W) t ∧
    ¬ ∃ a b : ℕ,
      uibhbotLdp (uibhbotBusemannSource k W) t = ((a : ℕ∞) : WithBot ℕ∞) ∧
      uibhbotLdp (uibhbotBusemannSource (k - 1) W) t =
        ((b : ℕ∞) : WithBot ℕ∞) ∧
      uibhbotBusemannIncrement k W = (a : ℤ) - (b : ℤ)}
  let e : ℕ ↪ S := Set.Infinite.natEmbedding S hinf
  let z : ℕ → UIBHBOTPresentVertex W := fun m => (e m).val
  have hz : Function.Injective z := Subtype.val_injective.comp e.injective
  obtain ⟨N, hN⟩ := hW k z hz (fun m => ⟨(e m).property.1, (e m).property.2.1⟩)
  exact (e N).property.2.2 (hN N le_rfl)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every finite set of intrinsic vertices is captured by one geometric radius. -/
theorem incrementClose3_vertexFinset_captured (M : RootedLocallyFiniteMap)
    (T : Finset (RootedLocallyFiniteVertex M.D M.rot)) (r₀ : ℕ) :
    ∃ R : ℕ, r₀ ≤ R ∧ ∀ t ∈ T, rootedLocallyFiniteWithinRadius M R t := by
  classical
  obtain ⟨R, hR, hd⟩ := incrementDartList_captured M r₀ (T.toList.map Quotient.out)
  refine ⟨R, hR, fun t ht => ?_⟩
  have hmem : Quotient.out t ∈ T.toList.map Quotient.out :=
    List.mem_map.mpr ⟨t, Finset.mem_toList.mpr ht, rfl⟩
  have hr := ((mem_rootedLocallyFiniteBallDarts M R _).mp (hd _ hmem)).1
  have he : rootedLocallyFiniteVertexClassOf M (Quotient.out t) = t :=
    Quotient.out_eq' t
  rw [he] at hr
  exact (mem_rootedLocallyFiniteRadiusVertices M R t).mp hr

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
All common reachable intrinsic targets outside one radius have the same finite
distance difference. The radius is fixed before quantifying over targets. -/
theorem ae_incrementClose3_intrinsic_uniform_consensus :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ),
        ∃ N : ℕ,
          ∀ t : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H),
            ¬ rootedLocallyFiniteWithinRadius
                (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) N t →
            (∃ ds, incrementDartWalk (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C)
              ds (intrinsicIncrementSource
                (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) k) t) →
            (∃ ds, incrementDartWalk (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C)
              ds (intrinsicIncrementSource
                (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) (k - 1)) t) →
            ∃ a b : ℕ,
              intrinsicIncrementLdp (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C)
                  (intrinsicIncrementSource
                    (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) k) t =
                ((a : ℕ∞) : WithBot ℕ∞) ∧
              intrinsicIncrementLdp (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C)
                  (intrinsicIncrementSource
                    (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) (k - 1)) t =
                ((b : ℕ∞) : WithBot ℕ∞) ∧
              uibhbotBusemannIncrement k W = (a : ℤ) - (b : ℤ) := by
  classical
  filter_upwards [ae_incrementClose3_finite_exceptions,
    UIBHBOTIntrinsicIncrementBoundaryIdentification_proved] with W hfinite hs H hhit C k
  let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
  let S := {t : UIBHBOTPresentVertex W |
    Reachable (uibhbotBusemannSource k W) t ∧
    Reachable (uibhbotBusemannSource (k - 1) W) t ∧
    ¬ ∃ a b : ℕ,
      uibhbotLdp (uibhbotBusemannSource k W) t = ((a : ℕ∞) : WithBot ℕ∞) ∧
      uibhbotLdp (uibhbotBusemannSource (k - 1) W) t =
        ((b : ℕ∞) : WithBot ℕ∞) ∧
      uibhbotBusemannIncrement k W = (a : ℤ) - (b : ℤ)}
  have hpre : ((incrementOrbitVertex W H) ⁻¹' S).Finite :=
    Set.Finite.preimage (incrementOrbitVertex_injective W H).injOn (hfinite k)
  obtain ⟨N, _, hN⟩ := incrementClose3_vertexFinset_captured M hpre.toFinset 0
  refine ⟨N, fun t ht h0 h1 => ?_⟩
  have hr0 : Reachable (uibhbotBusemannSource k W) (incrementOrbitVertex W H t) := by
    obtain ⟨ds, hd⟩ := h0
    obtain ⟨p, _⟩ := incrementDartWalk_to_codePath W H hhit C ds _ t hd
    rw [hs H hhit C k] at p
    exact ⟨p⟩
  have hr1 : Reachable (uibhbotBusemannSource (k - 1) W)
      (incrementOrbitVertex W H t) := by
    obtain ⟨ds, hd⟩ := h1
    obtain ⟨p, _⟩ := incrementDartWalk_to_codePath W H hhit C ds _ t hd
    rw [hs H hhit C (k - 1)] at p
    exact ⟨p⟩
  have hg : ∃ a b : ℕ,
      uibhbotLdp (uibhbotBusemannSource k W) (incrementOrbitVertex W H t) =
          ((a : ℕ∞) : WithBot ℕ∞) ∧
      uibhbotLdp (uibhbotBusemannSource (k - 1) W) (incrementOrbitVertex W H t) =
          ((b : ℕ∞) : WithBot ℕ∞) ∧
      uibhbotBusemannIncrement k W = (a : ℤ) - (b : ℤ) := by
    by_contra hn
    exact ht (hN t (hpre.mem_toFinset.mpr ⟨hr0, hr1, hn⟩))
  obtain ⟨a, b, ha, hb, hi⟩ := hg
  refine ⟨a, b, ?_, ?_, hi⟩
  · have he := intrinsicIncrementLdp_eq_uibhbotLdp W H hhit C
      (intrinsicIncrementSource M k) t
    apply he.trans
    rw [hs H hhit C k]
    exact ha
  · have he := intrinsicIncrementLdp_eq_uibhbotLdp W H hhit C
      (intrinsicIncrementSource M (k - 1)) t
    apply he.trans
    rw [hs H hhit C (k - 1)]
    exact hb

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A finite set of eventual radius assertions has one shared eventual radius. -/
private theorem incrementClose3_uniform_radius {α : Type*} (T : Finset α)
    (P : α → ℕ → Prop) (hP : ∀ t ∈ T, ∃ R : ℕ, ∀ r ≥ R, P t r) :
    ∃ R : ℕ, ∀ r ≥ R, ∀ t ∈ T, P t r := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun _ _ _ ht => (Finset.notMem_empty _ ht).elim⟩
  | @insert t T _ ih =>
    obtain ⟨R0, hR0⟩ := hP t (Finset.mem_insert_self _ _)
    obtain ⟨R1, hR1⟩ := ih (fun u hu => hP u (Finset.mem_insert_of_mem hu))
    refine ⟨max R0 R1, fun r hr u hu => ?_⟩
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hR0 r ((le_max_left _ _).trans hr)
    · exact hR1 r ((le_max_right _ _).trans hr) u hu

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
For every sufficiently distant intrinsic shell, one enclosing radius works for
every common reachable target in that shell. Extra darts cannot increase either
restricted LDP beyond its full attained value. Nonemptiness and transport to the
simple distances in a faced-ball representative are not asserted here. -/
theorem ae_incrementClose3_intrinsic_shell_radius_consensus :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ),
        let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
        ∃ N : ℕ, ∀ m ≥ N, ∃ R : ℕ, ∀ r ≥ R,
          ∀ t : RootedLocallyFiniteVertex M.D M.rot,
            rootedLocallyFiniteWithinRadius M (m + 1) t →
            ¬ rootedLocallyFiniteWithinRadius M m t →
            (∃ ds, incrementDartWalk M ds (intrinsicIncrementSource M k) t) →
            (∃ ds, incrementDartWalk M ds (intrinsicIncrementSource M (k - 1)) t) →
            ∃ a b : ℕ,
              incrementClose_ballLdp M r (intrinsicIncrementSource M k) t =
                  ((a : ℕ∞) : WithBot ℕ∞) ∧
              incrementClose_ballLdp M r (intrinsicIncrementSource M (k - 1)) t =
                  ((b : ℕ∞) : WithBot ℕ∞) ∧
              uibhbotBusemannIncrement k W = (a : ℤ) - (b : ℤ) := by
  classical
  filter_upwards [ae_incrementClose3_intrinsic_uniform_consensus] with W hW H hhit C k
  let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
  obtain ⟨N, hN⟩ := hW H hhit C k
  refine ⟨N, fun m hm => ?_⟩
  let T := (rootedLocallyFiniteRadiusVertices M (m + 1)).filter fun t =>
    ¬ rootedLocallyFiniteWithinRadius M m t ∧
      (∃ ds, incrementDartWalk M ds (intrinsicIncrementSource M k) t) ∧
      (∃ ds, incrementDartWalk M ds (intrinsicIncrementSource M (k - 1)) t)
  let P := fun (t : RootedLocallyFiniteVertex M.D M.rot) (r : ℕ) =>
    ∃ a b : ℕ,
      incrementClose_ballLdp M r (intrinsicIncrementSource M k) t =
          ((a : ℕ∞) : WithBot ℕ∞) ∧
      incrementClose_ballLdp M r (intrinsicIncrementSource M (k - 1)) t =
          ((b : ℕ∞) : WithBot ℕ∞) ∧
      uibhbotBusemannIncrement k W = (a : ℤ) - (b : ℤ)
  have hP : ∀ t ∈ T, ∃ R : ℕ, ∀ r ≥ R, P t r := by
    intro t ht
    obtain ⟨_, hfar, h0, h1⟩ := Finset.mem_filter.mp ht
    have hfarN : ¬ rootedLocallyFiniteWithinRadius M N t := by
      intro hn
      apply hfar
      exact (mem_rootedLocallyFiniteRadiusVertices M m t).mp
        (rootedLocallyFiniteRadiusVertices_mono M hm
          ((mem_rootedLocallyFiniteRadiusVertices M N t).mpr hn))
    obtain ⟨a, b, ha, hb, hi⟩ := hN t hfarN h0 h1
    obtain ⟨ds, hd⟩ := h0
    obtain ⟨es, he⟩ := h1
    obtain ⟨p, _⟩ := incrementDartWalk_to_codePath W H hhit C ds _ t hd
    obtain ⟨q, _⟩ := incrementDartWalk_to_codePath W H hhit C es _ t he
    have ha' := (intrinsicIncrementLdp_eq_uibhbotLdp W H hhit C
      (intrinsicIncrementSource M k) t).symm.trans ha
    have hb' := (intrinsicIncrementLdp_eq_uibhbotLdp W H hhit C
      (intrinsicIncrementSource M (k - 1)) t).symm.trans hb
    obtain ⟨as, has, hla⟩ := incrementClose_intrinsic_attaining W H hhit C
      (intrinsicIncrementSource M k) t a ⟨p⟩ ha'
    obtain ⟨bs, hbs, hlb⟩ := incrementClose_intrinsic_attaining W H hhit C
      (intrinsicIncrementSource M (k - 1)) t b ⟨q⟩ hb'
    obtain ⟨R0, _, hR0⟩ := incrementClose_ballLdp_stabilizes_of_attaining M
      (intrinsicIncrementSource M k) t as has
      (ha.trans (congrArg (fun n : ℕ => ((n : ℕ∞) : WithBot ℕ∞)) hla.symm)) 0
    obtain ⟨R1, _, hR1⟩ := incrementClose_ballLdp_stabilizes_of_attaining M
      (intrinsicIncrementSource M (k - 1)) t bs hbs
      (hb.trans (congrArg (fun n : ℕ => ((n : ℕ∞) : WithBot ℕ∞)) hlb.symm)) 0
    refine ⟨max R0 R1, fun r hr => ⟨a, b, ?_, ?_, hi⟩⟩
    · exact (hR0 r ((le_max_left _ _).trans hr)).trans ha
    · exact (hR1 r ((le_max_right _ _).trans hr)).trans hb
  obtain ⟨R, hR⟩ := incrementClose3_uniform_radius T P hP
  refine ⟨R, fun r hr t hnear hfar h0 h1 => hR r hr t ?_⟩
  exact Finset.mem_filter.mpr
    ⟨(mem_rootedLocallyFiniteRadiusVertices M (m + 1) t).mpr hnear, hfar, h0, h1⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A finite integer difference is formed only when both extended distances are finite. -/
@[expose] noncomputable def incrementClose3_finiteDifference
    (a b : WithBot ℕ∞) : Option ℤ := by
  classical
  exact if h : ∃ n m : ℕ,
      a = ((n : ℕ∞) : WithBot ℕ∞) ∧ b = ((m : ℕ∞) : WithBot ℕ∞) then
    some ((h.choose : ℤ) - (h.choose_spec.choose : ℤ)) else none

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The finite difference has its complete characterization, including both finite witnesses. -/
theorem incrementClose3_finiteDifference_eq_some_iff (a b : WithBot ℕ∞) (z : ℤ) :
    incrementClose3_finiteDifference a b = some z ↔
      ∃ n m : ℕ, a = ((n : ℕ∞) : WithBot ℕ∞) ∧
        b = ((m : ℕ∞) : WithBot ℕ∞) ∧ z = (n : ℤ) - (m : ℤ) := by
  classical
  unfold incrementClose3_finiteDifference
  split_ifs with h
  · constructor
    · intro he
      exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
        h.choose_spec.choose_spec.2, (Option.some.inj he).symm⟩
    · rintro ⟨n, m, ha, hb, hz⟩
      have hn : h.choose = n := by
        exact_mod_cast h.choose_spec.choose_spec.1.symm.trans ha
      have hm : h.choose_spec.choose = m := by
        exact_mod_cast h.choose_spec.choose_spec.2.symm.trans hb
      apply congrArg some
      exact (congrArg₂ (fun n m : ℕ => (n : ℤ) - (m : ℤ)) hn hm).trans hz.symm
  · constructor
    · intro he
      cases he
    · rintro ⟨n, m, ha, hb, _⟩
      exact (h ⟨n, m, ha, hb⟩).elim

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Exchanging distances negates a finite difference and preserves failure of finiteness. -/
theorem incrementClose3_finiteDifference_swap (a b : WithBot ℕ∞) :
    incrementClose3_finiteDifference b a =
      (incrementClose3_finiteDifference a b).map (fun z => -z) := by
  classical
  cases he : incrementClose3_finiteDifference a b with
  | none =>
    cases hf : incrementClose3_finiteDifference b a with
    | none => rfl
    | some z =>
      obtain ⟨n, m, hb, ha, hz⟩ :=
        (incrementClose3_finiteDifference_eq_some_iff b a z).mp hf
      have hg := (incrementClose3_finiteDifference_eq_some_iff a b
        ((m : ℤ) - (n : ℤ))).mpr ⟨m, n, ha, hb, rfl⟩
      rw [he] at hg
      cases hg
  | some z =>
    obtain ⟨n, m, ha, hb, hz⟩ :=
      (incrementClose3_finiteDifference_eq_some_iff a b z).mp he
    apply (incrementClose3_finiteDifference_eq_some_iff b a (-z)).mpr
    refine ⟨m, n, hb, ha, ?_⟩
    omega

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The intrinsic increment at one target, with no subtraction involving infinity. -/
@[expose] noncomputable def incrementClose3_intrinsicAt (M : RootedLocallyFiniteMap)
    (k : ℤ) (t : RootedLocallyFiniteVertex M.D M.rot) : Option ℤ :=
  incrementClose3_finiteDifference
    (intrinsicIncrementLdp M (intrinsicIncrementSource M k) t)
    (intrinsicIncrementLdp M (intrinsicIncrementSource M (k - 1)) t)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Reflection negates the intrinsic target increment with exactly the index shift
`k ↦ 2-k`. This includes failure of finite distances; it does not assert reflection
of the finite faced-ball observable. -/
theorem incrementClose3_intrinsicAt_mirror (M : RootedLocallyFiniteMap) (k : ℤ)
    (t : RootedLocallyFiniteVertex M.D M.rot) :
    incrementClose3_intrinsicAt (mirrorRootedLocallyFiniteMap M) k
        (incrementMirrorVertexEquiv M t) =
      (incrementClose3_intrinsicAt M (2 - k) t).map (fun z => -z) := by
  have h0 : 1 - (k - 1) = 2 - k := by omega
  have h1 : (2 - k) - 1 = 1 - k := by omega
  simp only [incrementClose3_intrinsicAt, intrinsicIncrementSource_mirror,
    intrinsicIncrementLdp_mirror, h0, h1]
  exact incrementClose3_finiteDifference_swap _ _

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Restricted reflected distances are bounded by the original distances at radius
one larger. The full dart lists and unreachable values are retained. -/
theorem incrementClose3_ballLdp_mirror_le_shift (M : RootedLocallyFiniteMap)
    (r : ℕ) (s t : RootedLocallyFiniteVertex M.D M.rot) :
    incrementClose_ballLdp (mirrorRootedLocallyFiniteMap M) r
        (incrementMirrorVertexEquiv M s) (incrementMirrorVertexEquiv M t) ≤
      incrementClose_ballLdp M (r + 1) s t := by
  apply iSup_le
  intro ds
  apply iSup_le
  intro hw
  apply iSup_le
  intro hd
  exact le_iSup_of_le ds
    (le_iSup_of_le ((incrementDartWalk_mirror M ds s t).mp hw)
      (le_iSup_of_le
        (fun d hds => rootedMirrorBallDarts_shift M r d (hd d hds)) le_rfl))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The actual future boundary ID agrees with its witnessed boundary vertex. -/
private theorem incrementClose3_boundaryId_eq (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (j : ℤ) :
    busemannBoundaryIdTotal ω j = boundaryVertex (fun i => ω (i + 1)) h j := by
  unfold busemannBoundaryIdTotal
  rw [boundaryHitTimeTotal_eq_boundaryHitTime ω h j, ENat.toNat_natCast]
  rw [boundaryVertex_eq_edgeWest_hit]
  exact (edge_endpoints_eq _ (act_lt_nextEdge _ le_rfl)).1

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every explicit target reaches every later target in its future boundary sequence. -/
theorem ae_incrementClose3_target_tail_reachable :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ a b : ℕ, a ≤ b →
        Reachable (uibhbotBusemannTarget k W a) (uibhbotBusemannTarget k W b) := by
  filter_upwards [ae_uibhbotFuture_boundaryHitWitnesses] with W hW k a b hab
  let w := fun i => uibhbotFutureCode k W (i + 1)
  let h := hW k
  let F := uibhbotFutureToGlobal k W
  have ht (m : ℕ) : uibhbotBusemannTarget k W m =
      F.obj (boundaryPresentVertex w h (m : ℤ)) := by
    unfold uibhbotBusemannTarget
    rw [incrementClose3_boundaryId_eq _ h]
    rfl
  rw [ht a, ht b]
  obtain ⟨p⟩ := boundaryVertex_nonneg_reachable w h
    (show (0 : ℤ) ≤ (a : ℤ) by omega) (show (a : ℤ) ≤ (b : ℤ) by omega)
  exact ⟨F.mapPath p⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A finite directed walk leaving a ball crosses its next geometric shell, with
common reachability from both sources preserved along its initial segment. -/
theorem incrementClose3_walk_crosses_shell (M : RootedLocallyFiniteMap) (m : ℕ)
    (s0 s1 : RootedLocallyFiniteVertex M.D M.rot)
    (ds : List M.D) (v t : RootedLocallyFiniteVertex M.D M.rot)
    (hv : rootedLocallyFiniteWithinRadius M m v)
    (ht : ¬ rootedLocallyFiniteWithinRadius M m t)
    (h0 : ∃ es, incrementDartWalk M es s0 v)
    (h1 : ∃ es, incrementDartWalk M es s1 v)
    (hw : incrementDartWalk M ds v t) :
    ∃ u : RootedLocallyFiniteVertex M.D M.rot,
      rootedLocallyFiniteWithinRadius M (m + 1) u ∧
      ¬ rootedLocallyFiniteWithinRadius M m u ∧
      (∃ es, incrementDartWalk M es s0 u) ∧
      (∃ es, incrementDartWalk M es s1 u) := by
  induction ds generalizing v with
  | nil =>
    change v = t at hw
    exact (ht (hw ▸ hv)).elim
  | cons d ds ih =>
    obtain ⟨hd, htail, hs, hw⟩ := hw
    let u := rootedLocallyFiniteVertexClass M.rot (M.edgeInv d)
    have hedge : incrementDartWalk M [d] v u := ⟨hd, htail, hs, rfl⟩
    have hu0 : ∃ es, incrementDartWalk M es s0 u := by
      obtain ⟨es, he⟩ := h0
      exact ⟨es ++ [d], incrementDartWalk_append M es [d] s0 v u he hedge⟩
    have hu1 : ∃ es, incrementDartWalk M es s1 u := by
      obtain ⟨es, he⟩ := h1
      exact ⟨es ++ [d], incrementDartWalk_append M es [d] s1 v u he hedge⟩
    by_cases hu : rootedLocallyFiniteWithinRadius M m u
    · exact ih u hu hu0 hu1 hw
    · exact ⟨u, .edge hv ⟨d, hs, rfl⟩, hu, hu0, hu1⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every sufficiently distant intrinsic geometric shell has a target reachable
from both boundary sources. No radius is allowed to depend on the shell target. -/
theorem ae_incrementClose3_intrinsic_shell_nonempty :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ),
        let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
        ∃ N : ℕ, ∀ m ≥ N,
          ∃ t : RootedLocallyFiniteVertex M.D M.rot,
            rootedLocallyFiniteWithinRadius M (m + 1) t ∧
            ¬ rootedLocallyFiniteWithinRadius M m t ∧
            (∃ ds, incrementDartWalk M ds (intrinsicIncrementSource M k) t) ∧
            (∃ ds, incrementDartWalk M ds (intrinsicIncrementSource M (k - 1)) t) := by
  classical
  filter_upwards [ae_uibhbotBusemannIncrement_distance_realization,
    UIBHBOTIntrinsicIncrementBoundaryIdentification_proved,
    ae_incrementClose3_target_tail_reachable] with W hreal hs htail H hhit C k
  let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
  obtain ⟨hinj, B, hB⟩ := hreal k
  let v := incrementClose_intrinsicTarget W H k B
  have hv : incrementOrbitVertex W H v = uibhbotBusemannTarget k W B :=
    incrementClose_intrinsicTarget_image W H k B
  obtain ⟨p0⟩ := (hB B le_rfl).1
  obtain ⟨p1⟩ := (hB B le_rfl).2.1
  obtain ⟨ds0, hd0, _⟩ := codePath_to_incrementDartWalk W H hhit C p0
    (intrinsicIncrementSource M k) v (hs H hhit C k) hv
  obtain ⟨ds1, hd1, _⟩ := codePath_to_incrementDartWalk W H hhit C p1
    (intrinsicIncrementSource M (k - 1)) v (hs H hhit C (k - 1)) hv
  obtain ⟨N, _, hN⟩ := incrementClose3_vertexFinset_captured M {v} 0
  refine ⟨N, fun m hm => ?_⟩
  have hvm : rootedLocallyFiniteWithinRadius M m v :=
    (mem_rootedLocallyFiniteRadiusVertices M m v).mp
      (rootedLocallyFiniteRadiusVertices_mono M hm
        ((mem_rootedLocallyFiniteRadiusVertices M N v).mpr
          (hN v (Finset.mem_singleton_self _))))
  let f := fun j : ℕ => incrementClose_intrinsicTarget W H k (B + j)
  have hf : Function.Injective f := by
    intro a b hab
    have he := congrArg (incrementOrbitVertex W H) hab
    change incrementOrbitVertex W H (incrementClose_intrinsicTarget W H k (B + a)) =
      incrementOrbitVertex W H (incrementClose_intrinsicTarget W H k (B + b)) at he
    rw [incrementClose_intrinsicTarget_image, incrementClose_intrinsicTarget_image] at he
    have he' := hinj he
    omega
  have hout : ∃ j, ¬ rootedLocallyFiniteWithinRadius M m (f j) := by
    by_contra! hn
    have hfin := Set.Finite.preimage hf.injOn
      (rootedLocallyFiniteRadiusVertices M m).finite_toSet
    apply Set.infinite_univ (α := ℕ)
    exact hfin.subset (fun j _ =>
      (mem_rootedLocallyFiniteRadiusVertices M m (f j)).mpr (hn j))
  obtain ⟨j, hj⟩ := hout
  obtain ⟨p⟩ := htail k B (B + j) (by omega)
  obtain ⟨ds, hd, _⟩ := codePath_to_incrementDartWalk W H hhit C p v (f j) hv
    (incrementClose_intrinsicTarget_image W H k (B + j))
  exact incrementClose3_walk_crosses_shell M m _ _ ds v (f j) hvm hj
    ⟨ds0, hd0⟩ ⟨ds1, hd1⟩ hd

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Consensus for restricted intrinsic distances on a nonempty ambient shell.
The target set uses full common reachability; its finite distances are evaluated
inside the specified enclosing radius. -/
@[expose] def IncrementClose3IntrinsicShellConsensus (M : RootedLocallyFiniteMap)
    (k : ℤ) (m r : ℕ) (z : ℤ) : Prop :=
  (∃ t : RootedLocallyFiniteVertex M.D M.rot,
    rootedLocallyFiniteWithinRadius M (m + 1) t ∧
    ¬ rootedLocallyFiniteWithinRadius M m t ∧
    (∃ ds, incrementDartWalk M ds (intrinsicIncrementSource M k) t) ∧
    (∃ ds, incrementDartWalk M ds (intrinsicIncrementSource M (k - 1)) t)) ∧
  ∀ t : RootedLocallyFiniteVertex M.D M.rot,
    rootedLocallyFiniteWithinRadius M (m + 1) t →
    ¬ rootedLocallyFiniteWithinRadius M m t →
    (∃ ds, incrementDartWalk M ds (intrinsicIncrementSource M k) t) →
    (∃ ds, incrementDartWalk M ds (intrinsicIncrementSource M (k - 1)) t) →
    incrementClose3_finiteDifference
        (incrementClose_ballLdp M r (intrinsicIncrementSource M k) t)
        (incrementClose_ballLdp M r (intrinsicIncrementSource M (k - 1)) t) = some z

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Nonempty restricted intrinsic shell consensus is proved, with the enclosing
radius uniform over every common reachable target in the entire shell. -/
theorem ae_incrementClose3_intrinsic_shell_stabilization :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ),
        ∃ N : ℕ, ∀ m ≥ N, ∃ R : ℕ, ∀ r ≥ R,
          IncrementClose3IntrinsicShellConsensus
            (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) k m r
            (uibhbotBusemannIncrement k W) := by
  filter_upwards [ae_incrementClose3_intrinsic_shell_radius_consensus,
    ae_incrementClose3_intrinsic_shell_nonempty] with W hc hn H hhit C k
  obtain ⟨N0, hN0⟩ := hc H hhit C k
  obtain ⟨N1, hN1⟩ := hn H hhit C k
  refine ⟨max N0 N1, fun m hm => ?_⟩
  obtain ⟨R, hR⟩ := hN0 m ((le_max_left _ _).trans hm)
  refine ⟨R, fun r hr => ⟨hN1 m ((le_max_right _ _).trans hm), ?_⟩⟩
  intro t ht hfar h0 h1
  obtain ⟨a, b, ha, hb, hi⟩ := hR r hr t ht hfar h0 h1
  exact (incrementClose3_finiteDifference_eq_some_iff _ _ _).mpr ⟨a, b, ha, hb, hi⟩








@[expose] def IncrementClose3FacedShellTransport : Prop :=
  ∀ (M : RootedLocallyFinitePlanarMap) (k : ℤ) (m : ℕ),
    ∃ R : ℕ, ∀ r ≥ R, ∀ z : ℤ,
      FiniteBallIncrementConsensus
          (rootedLocallyFiniteFacedBallClass r M).out.toFramedBall k m z ↔
        IncrementClose3IntrinsicShellConsensus M.toRootedLocallyFiniteMap k m (r + 1) z





theorem uibhbotIncrementBallShellStabilization_of_facedShellTransport
    (htransport : IncrementClose3FacedShellTransport) :
    UIBHBOTIncrementBallShellStabilization := by
  filter_upwards [ae_incrementClose3_intrinsic_shell_stabilization,
    uibhbotRootedPlanarMapConullEvent_spec.2.1] with W hW hgood k
  obtain ⟨H, hhit, C, hcap, hM⟩ :=
    (uibhbotRootedPlanarMapOfCode_on_event W hgood).1
  let M := uibhbotRootedLocallyFinitePlanarMap W H hhit C hcap
  obtain ⟨N, hN⟩ := hW H hhit C k
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨R0, hR0⟩ := hN m hm
  obtain ⟨R1, hR1⟩ := htransport M k m
  refine ⟨max R0 R1, fun r hr => ?_⟩
  apply (finiteBallIncrementKernel_eq_some_iff k m _ _).mpr
  rw [hM]
  apply (hR1 r ((le_max_right _ _).trans hr) _).mpr
  exact hR0 (r + 1) (by omega)

end DirectedDistances.PaperProofs.Section5
