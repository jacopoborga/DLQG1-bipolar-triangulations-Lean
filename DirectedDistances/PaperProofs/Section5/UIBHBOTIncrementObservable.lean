module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementMirror
public import DirectedDistances.PlanarMap.MirrorFinitePathLengths

/-! Finite-ball candidates for the intrinsic increment observable. The finite distances below
retain their unreachable value. Only differences between two finite distances are selected.
The candidate's Borel measurability is unconditional. Its identification with the code
increment and its almost-sure reflection identity are not asserted by this construction. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter
open DirectedDistances.RandomWalk DirectedDistances.Recursive DirectedDistances.PlanarMap
open DirectedDistances.KMSW Quiver
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The helper faced-ball topology used by the imported UIBHBOT law. -/
noncomputable local instance incrementObservableTopology :
    TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The Borel structure on that topology. -/
noncomputable local instance incrementObservableMeasurableSpace :
    MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The discrete measurable structure on finite-increment options. -/
local instance incrementOptionMeasurableSpace : MeasurableSpace (Option ℤ) := ⊤

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Singleton finite-increment options are measurable. -/
local instance incrementOptionMeasurableSingleton : MeasurableSingletonClass (Option ℤ) :=
  ⟨fun _ => trivial⟩




@[expose] noncomputable def eventualFiniteIncrement (f : ℕ → Option ℤ) : Option ℤ := by
  classical
  exact if h : ∃ z : ℤ, ∃ N : ℕ, ∀ n ≥ N, f n = some z then
    some h.choose else none

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Uniqueness of an eventually constant value. -/
theorem eventualFiniteIncrement_eq_some_iff (f : ℕ → Option ℤ) (z : ℤ) :
    eventualFiniteIncrement f = some z ↔ ∃ N : ℕ, ∀ n ≥ N, f n = some z := by
  classical
  unfold eventualFiniteIncrement
  split_ifs with h
  · constructor
    · intro he
      have hz : h.choose = z := Option.some.inj he
      simpa only [hz] using h.choose_spec
    · rintro ⟨N, hN⟩
      obtain ⟨M, hM⟩ := h.choose_spec
      have he := (hM (max M N) (le_max_left _ _)).symm.trans
        (hN (max M N) (le_max_right _ _))
      exact congrArg some (Option.some.inj he)
  · constructor
    · intro he
      cases he
    · intro hz
      exact (h ⟨z, hz⟩).elim

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Countable unions and intersections make eventual finite-value selection measurable.
No convergence premise is needed for the full-space `Option` extension. -/
theorem measurable_eventualFiniteIncrement {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → Option ℤ) (hf : ∀ n, Measurable (f n)) :
    Measurable (fun x => eventualFiniteIncrement (fun n => f n x)) := by
  classical
  have hs (z : ℤ) : MeasurableSet
      {x | eventualFiniteIncrement (fun n => f n x) = some z} := by
    simp_rw [eventualFiniteIncrement_eq_some_iff]
    have hm := MeasurableSet.iUnion fun (N : ℕ) =>
      MeasurableSet.iInter fun (n : ℕ) => MeasurableSet.iInter fun (_hn : N ≤ n) =>
        (hf n) (measurableSet_singleton (some z))
    convert hm using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_preimage, Set.mem_singleton_iff]
  apply measurable_to_countable'
  intro z
  cases z with
  | some z => exact hs z
  | none =>
    have he : {x | eventualFiniteIncrement (fun n => f n x) = none} =
        (⋃ z : ℤ, {x | eventualFiniteIncrement (fun n => f n x) = some z})ᶜ := by
      ext x
      cases hq : eventualFiniteIncrement (fun n => f n x) <;> simp [hq]
    change MeasurableSet {x | eventualFiniteIncrement (fun n => f n x) = none}
    rw [he]
    exact (MeasurableSet.iUnion hs).compl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite-ball boundary source candidate, obtained by traversing the face on the
opposite side of the reversed root incidence. Identification with the code boundary
is a separate geometric obligation. -/
@[expose] def finiteBallIncrementSource (B : FramedBall) (k : ℤ) :
    MapVertex B.map :=
  vertexClass B.map.toCombinatorialMap
    (((B.map.rot * B.map.edgeInv) ^ k) B.frameEdgeDart)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The finite-ball distance difference at a specified target. Each unreachable LDP
remains `⊥`; the function returns `none` unless both distances are finite. The finite
simple-path definition agrees with all directed paths on acyclic balls. -/
@[expose] noncomputable def finiteBallIncrementAt (B : FramedBall) (k : ℤ) (d : B.D) :
    Option ℤ :=
  match simpleDirectedPathLDPLength B.map (finiteBallIncrementSource B k)
      (vertexClass B.map.toCombinatorialMap d),
    simpleDirectedPathLDPLength B.map (finiteBallIncrementSource B (k - 1))
      (vertexClass B.map.toCombinatorialMap d) with
  | some a, some b => some ((a : ℤ) - (b : ℤ))
  | _, _ => none

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Targets in one geometric shell, reachable from both boundary source candidates.
Using all darts retains edge identity; duplicate representations of a target vertex
have identical distance differences. Missing edges count in the geometric radius. -/
@[expose] def finiteBallIncrementShell (B : FramedBall) (k : ℤ) (m : ℕ)
    (d : B.D) : Prop :=
  framedBallWithinRadius B (m + 1)
      (vertexClass B.map.toCombinatorialMap B.rootDart)
      (vertexClass B.map.toCombinatorialMap d) ∧
    ¬ framedBallWithinRadius B m
      (vertexClass B.map.toCombinatorialMap B.rootDart)
      (vertexClass B.map.toCombinatorialMap d) ∧
    (finiteBallIncrementAt B k d).isSome

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A shell has consensus `z` if it contains a common reachable target and every
common reachable target in that shell has the same finite LDP difference `z`. -/
@[expose] def FiniteBallIncrementConsensus (B : FramedBall) (k : ℤ) (m : ℕ)
    (z : ℤ) : Prop :=
  (∃ d : B.D, finiteBallIncrementShell B k m d) ∧
    ∀ d : B.D, finiteBallIncrementShell B k m d → finiteBallIncrementAt B k d = some z

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A finite-ball kernel using a representative of the faced isomorphism class.
No code preimage is selected. Proving the source and distance identifications for
these kernels is still required before they can realize a paper increment. -/
@[expose] noncomputable def finiteBallIncrementKernel (k : ℤ) (m : ℕ)
    (q : FacedFramedBallClass) : Option ℤ := by
  classical
  exact if h : ∃ z, FiniteBallIncrementConsensus q.out.toFramedBall k m z then
    some h.choose else none

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every faced-ball class coordinate is measurable for the helper Borel structure. -/
theorem measurable_incrementFacedBallClass (r : ℕ) :
    @Measurable RootedLocallyFinitePlanarMap FacedFramedBallClass
      _ ⊤ (rootedLocallyFiniteFacedBallClass r) := by
  apply measurable_iff_comap_le.mpr
  change MeasurableSpace.comap (rootedLocallyFiniteFacedBallClass r) ⊤ ≤
    borel RootedLocallyFinitePlanarMap
  let S := rootedLocallyFiniteFacedBallSystem
  change MeasurableSpace.comap (S.ballClass r) ⊤ ≤
    @borel S.Object (bsLocalDistanceTopologyGeneric S)
  rw [borel_bsLocalDistanceTopology_eq_iSup_ballClass_generic S]
  exact le_iSup_of_le r le_rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
First take the eventual value as the distance ball grows, then as the target
shell escapes to infinity. `none` records failure of either eventual finite value. -/
@[expose] noncomputable def finiteBallIncrementCandidate (k : ℤ)
    (M : RootedLocallyFinitePlanarMap) : Option ℤ :=
  eventualFiniteIncrement fun m => eventualFiniteIncrement fun r =>
    finiteBallIncrementKernel k m (rootedLocallyFiniteFacedBallClass r M)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The actual finite-ball candidate is Borel measurable by two countable eventual
value selections. This does not assert its almost-sure geometric identification. -/
theorem measurable_finiteBallIncrementCandidate (k : ℤ) :
    Measurable (finiteBallIncrementCandidate k) := by
  apply measurable_eventualFiniteIncrement
  intro m
  apply measurable_eventualFiniteIncrement
  intro r
  let : MeasurableSpace FacedFramedBallClass := ⊤
  have hk : Measurable (finiteBallIncrementKernel k m) := measurable_from_top
  exact hk.comp (measurable_incrementFacedBallClass r)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Full-space integer extension of the eventual finite-ball candidate. The zero
default is used only when no eventual finite increment was selected; it is never
a value of an unreachable LDP. Its almost-sure irrelevance remains to be proved. -/
@[expose] noncomputable def finiteBallIncrementObservable (k : ℤ)
    (M : RootedLocallyFinitePlanarMap) : ℤ :=
  (finiteBallIncrementCandidate k M).getD 0

/- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Observable measurability is proved for this explicit finite-ball construction. -/
theorem finiteBallIncrementObservable_measurable :
    UIBHBOTIncrementObservableMeasurable finiteBallIncrementObservable := by
  intro k
  exact (measurable_of_countable (fun z : Option ℤ => z.getD 0)).comp
    (measurable_finiteBallIncrementCandidate k)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The boundary traversal candidate on the infinite carrier. This uses the opposite
face permutation at the first ordered frame incidence; it does not choose any code. -/
@[expose] def intrinsicIncrementSource (M : RootedLocallyFiniteMap) (k : ℤ) :
    RootedLocallyFiniteVertex M.D M.rot :=
  rootedLocallyFiniteVertexClass M.rot (((M.rot * M.edgeInv) ^ k) M.frameEdgeDart)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Reflection identifies rotation-orbit vertices while preserving the actual darts. -/
@[expose] def incrementMirrorVertexEquiv (M : RootedLocallyFiniteMap) :
    RootedLocallyFiniteVertex M.D M.rot ≃
      RootedLocallyFiniteVertex M.D M.rot.symm where
  toFun := Quotient.map id (fun _ _ h => Equiv.Perm.sameCycle_inv.mpr h)
  invFun := Quotient.map id (fun _ _ h => Equiv.Perm.sameCycle_inv.mp h)
  left_inv := by intro v; induction v using Quotient.inductionOn; rfl
  right_inv := by intro v; induction v using Quotient.inductionOn; rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A directed dart walk keeps every edge identity. A missing edge can never occur.
The natural length is the length of the supplied dart list, including the empty walk. -/
@[expose] def incrementDartWalk (M : RootedLocallyFiniteMap) :
    List M.D → RootedLocallyFiniteVertex M.D M.rot →
      RootedLocallyFiniteVertex M.D M.rot → Prop
  | [], s, t => s = t
  | d :: ds, s, t => ¬ M.missing d ∧ M.tail d ∧
      rootedLocallyFiniteVertexClass M.rot d = s ∧
      incrementDartWalk M ds (rootedLocallyFiniteVertexClass M.rot (M.edgeInv d)) t

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Mirror transport keeps the entire directed dart list, hence its length.
This is an equivalence, including unreachable endpoint pairs and parallel edges. -/
theorem incrementDartWalk_mirror (M : RootedLocallyFiniteMap) (ds : List M.D)
    (s t : RootedLocallyFiniteVertex M.D M.rot) :
    incrementDartWalk (mirrorRootedLocallyFiniteMap M) ds
        (incrementMirrorVertexEquiv M s) (incrementMirrorVertexEquiv M t) ↔
      incrementDartWalk M ds s t := by
  induction ds generalizing s t with
  | nil => exact (incrementMirrorVertexEquiv M).injective.eq_iff
  | cons d ds ih =>
    change (¬ M.missing d ∧ M.tail d ∧
      incrementMirrorVertexEquiv M (rootedLocallyFiniteVertexClass M.rot d) =
        incrementMirrorVertexEquiv M s ∧
      incrementDartWalk (mirrorRootedLocallyFiniteMap M) ds
        (incrementMirrorVertexEquiv M
          (rootedLocallyFiniteVertexClass M.rot (M.edgeInv d)))
        (incrementMirrorVertexEquiv M t)) ↔ _
    rw [ih, (incrementMirrorVertexEquiv M).injective.eq_iff]
    rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Extended LDP on the intrinsic dart-walk carrier. Unreachable distances are `⊥`
and unbounded path lengths give `⊤`; no finiteness is presumed here. -/
@[expose] noncomputable def intrinsicIncrementLdp (M : RootedLocallyFiniteMap)
    (s t : RootedLocallyFiniteVertex M.D M.rot) : WithBot ℕ∞ :=
  ⨆ ds : List M.D, ⨆ (_ : incrementDartWalk M ds s t),
    ((ds.length : ℕ∞) : WithBot ℕ∞)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Reflection preserves the extended intrinsic LDP, with its unreachable and
unbounded cases intact. No integer subtraction is performed before finiteness. -/
theorem intrinsicIncrementLdp_mirror (M : RootedLocallyFiniteMap)
    (s t : RootedLocallyFiniteVertex M.D M.rot) :
    intrinsicIncrementLdp (mirrorRootedLocallyFiniteMap M)
        (incrementMirrorVertexEquiv M s) (incrementMirrorVertexEquiv M t) =
      intrinsicIncrementLdp M s t := by
  simp only [intrinsicIncrementLdp, incrementDartWalk_mirror]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The inverse edge permutation equals itself. -/
private theorem increment_edgeInv_inv (M : RootedLocallyFiniteMap) :
    M.edgeInv⁻¹ = M.edgeInv := by
  ext d
  apply M.edgeInv.injective
  exact (M.edgeInv.apply_symm_apply d).trans (M.edgeInv_invol d).symm

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Conjugate face traversal across the edge incidence swap. -/
private theorem increment_face_power (M : RootedLocallyFiniteMap) (k : ℤ) :
    (M.rot.symm * M.edgeInv) ^ k * M.edgeInv =
      M.edgeInv * (M.rot * M.edgeInv) ^ (-k) := by
  calc
    _ = (M.edgeInv * M.rot) ^ (-k) * M.edgeInv := by
      simp only [zpow_neg, ← inv_zpow, mul_inv_rev, Equiv.Perm.inv_def]
      rw [show M.edgeInv.symm = M.edgeInv from increment_edgeInv_inv M]
    _ = _ := mul_zpow_mul M.edgeInv M.rot (-k)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The intrinsic boundary traversal reverses with the exact ordered-root shift
`k ↦ 1-k`. This deterministic statement does not yet identify code boundary labels. -/
theorem intrinsicIncrementSource_mirror (M : RootedLocallyFiniteMap) (k : ℤ) :
    intrinsicIncrementSource (mirrorRootedLocallyFiniteMap M) k =
      incrementMirrorVertexEquiv M (intrinsicIncrementSource M (1 - k)) := by
  apply (incrementMirrorVertexEquiv M).symm.injective
  change rootedLocallyFiniteVertexClass M.rot
      (((M.rot.symm * M.edgeInv) ^ k) (M.edgeInv M.frameEdgeDart)) =
    rootedLocallyFiniteVertexClass M.rot
      (((M.rot * M.edgeInv) ^ (1 - k)) M.frameEdgeDart)
  have hp := congrArg (fun p : Equiv.Perm M.D => p M.frameEdgeDart)
    (increment_face_power M k)
  change ((M.rot.symm * M.edgeInv) ^ k) (M.edgeInv M.frameEdgeDart) =
    M.edgeInv (((M.rot * M.edgeInv) ^ (-k)) M.frameEdgeDart) at hp
  rw [hp]
  apply Quotient.sound
  refine ⟨1, ?_⟩
  have he : 1 - k = 1 + -k := by omega
  rw [he, zpow_add, zpow_one, Equiv.Perm.mul_apply]
  rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Concatenating two intrinsic walks preserves the complete ordered dart lists. -/
theorem incrementDartWalk_append (M : RootedLocallyFiniteMap)
    (ds es : List M.D) (s u t : RootedLocallyFiniteVertex M.D M.rot)
    (hd : incrementDartWalk M ds s u) (he : incrementDartWalk M es u t) :
    incrementDartWalk M (ds ++ es) s t := by
  induction ds generalizing s with
  | nil =>
    change s = u at hd
    subst s
    exact he
  | cons d ds ih =>
    obtain ⟨hm, ht, hs, hd⟩ := hd
    exact ⟨hm, ht, hs, ih _ hd⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The orbit quotient of the source constructed map maps to its code vertex carrier.
This is geometric incidence, with no arbitrary code preimage or probabilistic choice. -/
@[expose] noncomputable def incrementOrbitVertex (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) :
    RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H) →
      UIBHBOTPresentVertex W :=
  fun v => ⟨Quotient.lift (wholePlaneDartVertex W) (fun d e h =>
    (wholePlaneRotation_sameCycle_dartVertex W H d e h).symm) v⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Distinct rotation-orbit vertices remain distinct in the code incidence carrier. -/
theorem incrementOrbitVertex_injective (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : Function.Injective (incrementOrbitVertex W H) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h d =>
    induction b using Quotient.inductionOn with
    | h e =>
      apply Quotient.sound
      exact wholePlaneRotation_sameVertex_sameCycle_proof W H d e
        (congrArg UIBHBOTPresentVertex.id hab)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
An intrinsic dart walk gives a code path of exactly the same length. -/
theorem incrementDartWalk_to_codePath (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0)
    (ds : List (WholePlaneDart W))
    (s t : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H))
    (hw : incrementDartWalk (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) ds s t) :
    ∃ p : Path (incrementOrbitVertex W H s) (incrementOrbitVertex W H t),
      p.length = ds.length := by
  dsimp only [uibhbotWholePlaneRootedLocallyFiniteMap] at hw ⊢
  induction ds generalizing s with
  | nil =>
    change s = t at hw
    subst s
    exact ⟨.nil, rfl⟩
  | cons d ds ih =>
    obtain ⟨_, ht, hs, hw⟩ := hw
    obtain ⟨p, hp⟩ := ih _ hw
    rcases d with ⟨q, b⟩
    cases b with
    | true => exact (ht.1 rfl).elim
    | false =>
      rw [← hs]
      let e : incrementOrbitVertex W H
          (rootedLocallyFiniteVertexClass (wholePlaneRotation W H) (q, false)) ⟶
          incrementOrbitVertex W H
            (rootedLocallyFiniteVertexClass (wholePlaneRotation W H) (q, true)) :=
        ⟨q, ht.2, rfl, rfl⟩
      change Path (incrementOrbitVertex W H
        (rootedLocallyFiniteVertexClass (wholePlaneRotation W H) (q, true)))
        (incrementOrbitVertex W H t) at p
      refine ⟨e.toPath.comp p, ?_⟩
      have hp' : p.length = ds.length := hp
      change (e.toPath.comp p).length = ds.length + 1
      rw [Path.length_comp, Path.length_toPath, hp']
      omega

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A code path lifts to an intrinsic dart walk with the same length and the same
geometric edge identities. The endpoint identifications use orbit injectivity. -/
theorem codePath_to_incrementDartWalk (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0)
    {a b : UIBHBOTPresentVertex W} (p : Path a b)
    (s t : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H))
    (hs : incrementOrbitVertex W H s = a) (ht : incrementOrbitVertex W H t = b) :
    ∃ ds : List (WholePlaneDart W),
      incrementDartWalk (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) ds s t ∧
        ds.length = p.length := by
  induction p generalizing s t with
  | nil =>
    have he : s = t := incrementOrbitVertex_injective W H (hs.trans ht.symm)
    exact ⟨[], he, rfl⟩
  | @cons b c p e ih =>
    let d : WholePlaneDart W := (e.val, false)
    let u := rootedLocallyFiniteVertexClass (wholePlaneRotation W H) d
    let v := rootedLocallyFiniteVertexClass (wholePlaneRotation W H) (e.val, true)
    have hu : incrementOrbitVertex W H u = b := by
      have he := e.property.2.1
      change wholePlaneEdgeWest W e.val = b.id at he
      cases b
      exact congrArg UIBHBOTPresentVertex.mk he
    have hv : incrementOrbitVertex W H v = c := by
      have he := e.property.2.2
      change wholePlaneEdgeEast W e.val = c.id at he
      cases c
      exact congrArg UIBHBOTPresentVertex.mk he
    have hvt : v = t := incrementOrbitVertex_injective W H (hv.trans ht.symm)
    obtain ⟨ds, hd, hlen⟩ := ih s u hs hu
    refine ⟨ds ++ [d], ?_, ?_⟩
    · apply incrementDartWalk_append
        (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) ds [d] s u t hd
      change ¬ ¬ wholePlaneEdgePresent W d.1 ∧ wholePlaneDartTail W d ∧
        rootedLocallyFiniteVertexClass (wholePlaneRotation W H) d = u ∧
        rootedLocallyFiniteVertexClass (wholePlaneRotation W H)
          (wholePlaneDartFlip W d) = t
      exact ⟨by exact fun hn => hn e.property.1,
        ⟨by simp only [d, Bool.false_eq_true, not_false_eq_true], e.property.1⟩, rfl, hvt⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, hlen,
        Path.length_cons]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The source map's intrinsic LDP equals the code-carrier LDP, including unreachable
and unbounded values. This closes the distance-carrier transport without assumptions
about the Busemann observable or its geometric boundary labelling. -/
theorem intrinsicIncrementLdp_eq_uibhbotLdp (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0)
    (s t : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H)) :
    intrinsicIncrementLdp (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) s t =
      uibhbotLdp (incrementOrbitVertex W H s) (incrementOrbitVertex W H t) := by
  unfold intrinsicIncrementLdp uibhbotLdp
  dsimp only [uibhbotWholePlaneRootedLocallyFiniteMap]
  apply le_antisymm
  · apply iSup_le
    intro ds
    apply iSup_le
    intro hw
    obtain ⟨p, hp⟩ := incrementDartWalk_to_codePath W H hhit C ds s t hw
    exact (congrArg (fun n : ℕ => ((n : ℕ∞) : WithBot ℕ∞)) hp.symm).le.trans
      (le_iSup (fun q : Path (incrementOrbitVertex W H s)
        (incrementOrbitVertex W H t) => ((q.length : ℕ∞) : WithBot ℕ∞)) p)
  · apply iSup_le
    intro p
    obtain ⟨ds, hd, hlen⟩ := codePath_to_incrementDartWalk W H hhit C p s t rfl rfl
    exact (congrArg (fun n : ℕ => ((n : ℕ∞) : WithBot ℕ∞)) hlen.symm).le.trans
      (le_iSup_of_le ds (le_iSup_of_le hd le_rfl))




theorem incrementDartList_captured (M : RootedLocallyFiniteMap) (r : ℕ)
    (ds : List M.D) :
    ∃ R, r ≤ R ∧ ∀ d ∈ ds, d ∈ rootedLocallyFiniteBallDarts M R := by
  classical
  obtain ⟨R, hrR, hR⟩ := d39BallDarts_capture_finite M.toD39RootedMap r ds.toFinset
  refine ⟨R, hrR, fun d hd => ?_⟩
  rw [← d39BallDarts_toD39RootedMap]
  exact hR d (List.mem_toFinset.mpr hd)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The precise two-stage stabilization criterion for the finite-ball candidate.
Its right side is a countable statement about actual finite-ball LDP differences. -/
theorem finiteBallIncrementCandidate_eq_some_iff (k : ℤ)
    (M : RootedLocallyFinitePlanarMap) (z : ℤ) :
    finiteBallIncrementCandidate k M = some z ↔
      ∃ N : ℕ, ∀ m ≥ N, ∃ R : ℕ, ∀ r ≥ R,
        finiteBallIncrementKernel k m (rootedLocallyFiniteFacedBallClass r M) = some z := by
  simp only [finiteBallIncrementCandidate, eventualFiniteIncrement_eq_some_iff]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Open boundary-index identification, isolated before any claim of observable
realization. Neither this proposition nor its instances are assumed in this file. -/
@[expose] def UIBHBOTIntrinsicIncrementBoundaryIdentification : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
    ∀ (H : WholePlaneRotationHypothesis W)
      (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ),
      incrementOrbitVertex W H
          (intrinsicIncrementSource (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) k) =
        uibhbotBusemannSource k W

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Open finite-ball shell stabilization on the source code event. This names the
remaining geometric convergence step, including nonempty common-reachable shells
and finite-distance stabilization. It is defined but never assumed or asserted. -/
@[expose] def UIBHBOTIncrementBallShellStabilization : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
    ∃ N : ℕ, ∀ m ≥ N, ∃ R : ℕ, ∀ r ≥ R,
      finiteBallIncrementKernel k m
          (rootedLocallyFiniteFacedBallClass r (uibhbotRootedPlanarMapOfCode W)) =
        some (uibhbotBusemannIncrement k W)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The nonempty-target clause makes a shell's finite increment consensus unique. -/
theorem finiteBallIncrementConsensus_unique (B : FramedBall) (k : ℤ) (m : ℕ)
    {z z' : ℤ} (hz : FiniteBallIncrementConsensus B k m z)
    (hz' : FiniteBallIncrementConsensus B k m z') : z = z' := by
  obtain ⟨d, hd⟩ := hz.1
  exact Option.some.inj ((hz.2 d hd).symm.trans (hz'.2 d hd))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The selected finite-ball value has exactly the full nonempty-target consensus
characterization. No arbitrary finite-distance value is admitted by the selector. -/
theorem finiteBallIncrementKernel_eq_some_iff (k : ℤ) (m : ℕ)
    (q : FacedFramedBallClass) (z : ℤ) :
    finiteBallIncrementKernel k m q = some z ↔
      FiniteBallIncrementConsensus q.out.toFramedBall k m z := by
  classical
  unfold finiteBallIncrementKernel
  split_ifs with h
  · constructor
    · intro he
      have hz : h.choose = z := Option.some.inj he
      simpa only [hz] using h.choose_spec
    · intro hz
      exact congrArg some (finiteBallIncrementConsensus_unique _ _ _ h.choose_spec hz)
  · constructor
    · intro he
      cases he
    · intro hz
      exact (h ⟨z, hz⟩).elim

end DirectedDistances.PaperProofs.Section5
