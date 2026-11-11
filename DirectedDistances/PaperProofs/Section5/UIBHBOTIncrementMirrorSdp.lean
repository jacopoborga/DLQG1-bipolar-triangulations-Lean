module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservable
public import DirectedDistances.PaperProofs.Section5.DiskRootedMirrorFacedCompat
public import DirectedDistances.PaperProofs.Section3.BSTopologyGenericMetrizable
public import DirectedDistances.Recursive.BusemannSDPMeasurable
public import DirectedDistances.Recursive.SDPMasterFromLaw

/-! SDP helpers for reflection symmetry. Unreachable shortest distances remain `⊤`.
The finite-ball construction is intrinsic and measurable. Its code realization and
almost-sure reflection remain explicit open geometric obligations. The final theorem
is conditional on precisely those obligations; it is not a numbered paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter Quiver
open DirectedDistances.RandomWalk DirectedDistances.Recursive DirectedDistances.PlanarMap
open DirectedDistances.KMSW DirectedMapWithMissing
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The helper faced-ball topology of the rooted-map law. -/
noncomputable local instance incrementSdpTopology :
    TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Its Borel measurable structure. -/
noncomputable local instance incrementSdpMeasurableSpace :
    MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Discrete measurable finite-increment options. -/
local instance incrementSdpOptionMeasurableSpace : MeasurableSpace (Option ℤ) := ⊤

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Singleton finite-increment options are measurable. -/
local instance incrementSdpOptionMeasurableSingleton :
    MeasurableSingletonClass (Option ℤ) := ⟨fun _ => trivial⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Reanchored reflected SDP profile; this is deterministic profile algebra. -/
@[expose] def reanchoredMirrorSdpBusemannProfile (X : ℤ → ℤ) (k : ℤ) : ℤ :=
  reanchoredMirrorBusemannProfile X k

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The reflected profile is normalized at zero. -/
theorem reanchoredMirrorSdpBusemannProfile_zero (X : ℤ → ℤ) :
    reanchoredMirrorSdpBusemannProfile X 0 = 0 :=
  reanchoredMirrorBusemannProfile_zero X

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The ordered frame reversal has shift two at the increment level. -/
theorem reanchoredMirrorSdpBusemannProfile_increment (X : ℤ → ℤ) (k : ℤ) :
    reanchoredMirrorSdpBusemannProfile X k -
        reanchoredMirrorSdpBusemannProfile X (k - 1) =
      -(X (2 - k) - X ((2 - k) - 1)) :=
  reanchoredMirrorBusemannProfile_increment X k

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The reflected profile reanchored at an arbitrary integer boundary label. -/
@[expose] def reanchoredMirrorSdpBusemannProfileAt (X : ℤ → ℤ) (r k : ℤ) : ℤ :=
  X (1 - k) - X (1 - r)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Reanchoring at `r` makes the profile zero there. -/
theorem reanchoredMirrorSdpBusemannProfileAt_self (X : ℤ → ℤ) (r : ℤ) :
    reanchoredMirrorSdpBusemannProfileAt X r r = 0 := sub_self _

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The increment reversal is independent of the additive anchoring constant. -/
theorem reanchoredMirrorSdpBusemannProfileAt_increment (X : ℤ → ℤ) (r k : ℤ) :
    reanchoredMirrorSdpBusemannProfileAt X r k -
        reanchoredMirrorSdpBusemannProfileAt X r (k - 1) =
      -(X (2 - k) - X ((2 - k) - 1)) := by
  have hleft : 1 - (k - 1) = 2 - k := by omega
  have hright : (2 - k) - 1 = 1 - k := by omega
  simp only [reanchoredMirrorSdpBusemannProfileAt, hleft, hright]
  omega

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Reflection swaps the ordered root incidence. -/
theorem incrementSdpMirror_rootDart (M : RootedLocallyFinitePlanarMap) :
    (mirrorRootedLocallyFinitePlanarMap M).rootDart = M.edgeInv M.frameEdgeDart := rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Intrinsic boundary-source candidate, with no code preimage selection. -/
@[expose] def intrinsicSdpIncrementSource (M : RootedLocallyFiniteMap) (k : ℤ) :
    RootedLocallyFiniteVertex M.D M.rot := intrinsicIncrementSource M k

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The vertex correspondence retains all dart identities. -/
@[expose] def incrementSdpMirrorVertexEquiv (M : RootedLocallyFiniteMap) :
    RootedLocallyFiniteVertex M.D M.rot ≃
      RootedLocallyFiniteVertex M.D M.rot.symm := incrementMirrorVertexEquiv M

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Directed walks retain parallel edges and exclude missing edges. -/
@[expose] def incrementSdpDartWalk (M : RootedLocallyFiniteMap)
    (ds : List M.D) (s t : RootedLocallyFiniteVertex M.D M.rot) : Prop :=
  incrementDartWalk M ds s t

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Reflection preserves every directed dart walk, and therefore its length. -/
theorem incrementSdpDartWalk_mirror (M : RootedLocallyFiniteMap) (ds : List M.D)
    (s t : RootedLocallyFiniteVertex M.D M.rot) :
    incrementSdpDartWalk (mirrorRootedLocallyFiniteMap M) ds
        (incrementSdpMirrorVertexEquiv M s) (incrementSdpMirrorVertexEquiv M t) ↔
      incrementSdpDartWalk M ds s t := incrementDartWalk_mirror M ds s t

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Intrinsic SDP is the infimum of all dart-walk lengths; the empty family gives infinity. -/
@[expose] noncomputable def intrinsicIncrementSdp (M : RootedLocallyFiniteMap)
    (s t : RootedLocallyFiniteVertex M.D M.rot) : ℕ∞ :=
  ⨅ ds : List M.D, ⨅ (_ : incrementSdpDartWalk M ds s t), (ds.length : ℕ∞)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Infinity is exactly the absence of an intrinsic directed walk. -/
theorem intrinsicIncrementSdp_eq_top_iff (M : RootedLocallyFiniteMap)
    (s t : RootedLocallyFiniteVertex M.D M.rot) :
    intrinsicIncrementSdp M s t = ⊤ ↔ ¬ ∃ ds, incrementSdpDartWalk M ds s t := by
  constructor
  · intro h
    rintro ⟨ds, hw⟩
    have hle : intrinsicIncrementSdp M s t ≤ (ds.length : ℕ∞) :=
      iInf_le_of_le ds (iInf_le_of_le hw le_rfl)
    rw [h] at hle
    exact ENat.natCast_ne_top ds.length (top_le_iff.mp hle)
  · intro h
    apply top_unique
    apply le_iInf
    intro ds
    apply le_iInf
    intro hw
    exact (h ⟨ds, hw⟩).elim

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every reachable intrinsic SDP is attained by a finite directed dart walk. -/
theorem intrinsicIncrementSdp_attained (M : RootedLocallyFiniteMap)
    (s t : RootedLocallyFiniteVertex M.D M.rot)
    (h : ∃ ds, incrementSdpDartWalk M ds s t) :
    ∃ ds, incrementSdpDartWalk M ds s t ∧
      (ds.length : ℕ∞) = intrinsicIncrementSdp M s t := by
  classical
  have hn : ∃ n : ℕ, ∃ ds, incrementSdpDartWalk M ds s t ∧ ds.length = n := by
    obtain ⟨ds, hw⟩ := h
    exact ⟨ds.length, ds, hw, rfl⟩
  obtain ⟨ds, hw, hlen⟩ := Nat.find_spec hn
  refine ⟨ds, hw, le_antisymm ?_ ?_⟩
  · apply le_iInf
    intro es
    apply le_iInf
    intro he
    apply ENat.natCast_le_natCast.mpr
    rw [hlen]
    exact Nat.find_min' hn ⟨es, he, rfl⟩
  · exact iInf_le_of_le ds (iInf_le_of_le hw le_rfl)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Reflection preserves intrinsic shortest distance, including unreachable pairs. -/
theorem intrinsicIncrementSdp_mirror (M : RootedLocallyFiniteMap)
    (s t : RootedLocallyFiniteVertex M.D M.rot) :
    intrinsicIncrementSdp (mirrorRootedLocallyFiniteMap M)
        (incrementSdpMirrorVertexEquiv M s) (incrementSdpMirrorVertexEquiv M t) =
      intrinsicIncrementSdp M s t := by
  simp only [intrinsicIncrementSdp, incrementSdpDartWalk_mirror]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The boundary traversal reverses with the ordered-root shift `k ↦ 1-k`. -/
theorem intrinsicSdpIncrementSource_mirror (M : RootedLocallyFiniteMap) (k : ℤ) :
    intrinsicSdpIncrementSource (mirrorRootedLocallyFiniteMap M) k =
      incrementSdpMirrorVertexEquiv M (intrinsicSdpIncrementSource M (1 - k)) :=
  intrinsicIncrementSource_mirror M k

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
An intrinsic walk gives a code path of exactly the same length. -/
theorem incrementSdpDartWalk_to_codePath (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0) (ds : List (WholePlaneDart W))
    (s t : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H))
    (hw : incrementSdpDartWalk
      (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) ds s t) :
    ∃ p : Path (incrementOrbitVertex W H s) (incrementOrbitVertex W H t),
      p.length = ds.length := incrementDartWalk_to_codePath W H hhit C ds s t hw

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every code path lifts to a dart walk preserving its endpoints and length. -/
theorem codePath_to_incrementSdpDartWalk (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0)
    {a b : UIBHBOTPresentVertex W} (p : Path a b)
    (s t : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H))
    (hs : incrementOrbitVertex W H s = a) (ht : incrementOrbitVertex W H t = b) :
    ∃ ds : List (WholePlaneDart W),
      incrementSdpDartWalk (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) ds s t ∧
        ds.length = p.length := codePath_to_incrementDartWalk W H hhit C p s t hs ht

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every finite dart list is captured in one geometric ball, including missing geometry. -/
theorem incrementSdpDartList_captured (M : RootedLocallyFiniteMap) (r : ℕ)
    (ds : List M.D) :
    ∃ R, r ≤ R ∧ ∀ d ∈ ds, d ∈ rootedLocallyFiniteBallDarts M R :=
  incrementDartList_captured M r ds

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Intrinsic SDP equals code SDP by the two length-preserving path transports. -/
theorem intrinsicIncrementSdp_eq_codeSdp (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0)
    (s t : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H)) :
    intrinsicIncrementSdp (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) s t =
      sdp (incrementOrbitVertex W H s) (incrementOrbitVertex W H t) := by
  unfold intrinsicIncrementSdp sdp
  apply le_antisymm
  · apply le_iInf
    intro p
    obtain ⟨ds, hd, hlen⟩ := codePath_to_incrementDartWalk W H hhit C p s t rfl rfl
    exact iInf_le_of_le ds (iInf_le_of_le hd
      (congrArg (fun n : ℕ => (n : ℕ∞)) hlen).le)
  · apply le_iInf
    intro ds
    apply le_iInf
    intro hw
    obtain ⟨p, hp⟩ := incrementDartWalk_to_codePath W H hhit C ds s t hw
    exact (iInf_le (fun p : Path (incrementOrbitVertex W H s)
      (incrementOrbitVertex W H t) => (p.length : ℕ∞)) p).trans
        (congrArg (fun n : ℕ => (n : ℕ∞)) hp).le

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Shortest intrinsic walks are transported to shortest intrinsic walks. -/
theorem intrinsicIncrementSdp_shortest_mirror (M : RootedLocallyFiniteMap)
    (ds : List M.D) (s t : RootedLocallyFiniteVertex M.D M.rot) :
    (incrementSdpDartWalk (mirrorRootedLocallyFiniteMap M) ds
        (incrementSdpMirrorVertexEquiv M s) (incrementSdpMirrorVertexEquiv M t) ∧
      (ds.length : ℕ∞) = intrinsicIncrementSdp (mirrorRootedLocallyFiniteMap M)
        (incrementSdpMirrorVertexEquiv M s) (incrementSdpMirrorVertexEquiv M t)) ↔
    (incrementSdpDartWalk M ds s t ∧ (ds.length : ℕ∞) = intrinsicIncrementSdp M s t) := by
  rw [incrementSdpDartWalk_mirror, intrinsicIncrementSdp_mirror]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite simple shortest distances also transport, with infinity retained. -/
theorem finiteIncrementSdp_mirror {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) (s t : MapVertex M) :
    simpleDirectedPathSDPLength M.mirror (mirrorVertexMap M s) (mirrorVertexMap M t) =
      simpleDirectedPathSDPLength M s t := simpleDirectedPathSDPLength_mirror M s t

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite-ball boundary source candidate, using the actual framed face traversal. -/
@[expose] def finiteBallSdpIncrementSource (B : FramedBall) (k : ℤ) : MapVertex B.map :=
  finiteBallIncrementSource B k

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Only finite SDP pairs are subtracted. Each unreachable SDP remains infinity. -/
@[expose] noncomputable def finiteBallSdpIncrementAt (B : FramedBall) (k : ℤ)
    (d : B.D) : Option ℤ :=
  match simpleDirectedPathSDPLength B.map (finiteBallSdpIncrementSource B k)
      (vertexClass B.map.toCombinatorialMap d),
    simpleDirectedPathSDPLength B.map (finiteBallSdpIncrementSource B (k - 1))
      (vertexClass B.map.toCombinatorialMap d) with
  | some a, some b => some ((a : ℤ) - (b : ℤ))
  | _, _ => none

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Common reachable targets in one geometric shell, retaining every edge identity. -/
@[expose] def finiteBallSdpIncrementShell (B : FramedBall) (k : ℤ) (m : ℕ)
    (d : B.D) : Prop :=
  framedBallWithinRadius B (m + 1)
      (vertexClass B.map.toCombinatorialMap B.rootDart)
      (vertexClass B.map.toCombinatorialMap d) ∧
    ¬ framedBallWithinRadius B m
      (vertexClass B.map.toCombinatorialMap B.rootDart)
      (vertexClass B.map.toCombinatorialMap d) ∧
    (finiteBallSdpIncrementAt B k d).isSome

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A nonempty shell has consensus when all common reachable targets agree. -/
@[expose] def FiniteBallSdpIncrementConsensus (B : FramedBall) (k : ℤ) (m : ℕ)
    (z : ℤ) : Prop :=
  (∃ d : B.D, finiteBallSdpIncrementShell B k m d) ∧
    ∀ d : B.D, finiteBallSdpIncrementShell B k m d →
      finiteBallSdpIncrementAt B k d = some z

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Nonempty-target consensus is unique. -/
theorem finiteBallSdpIncrementConsensus_unique (B : FramedBall) (k : ℤ) (m : ℕ)
    {z z' : ℤ} (hz : FiniteBallSdpIncrementConsensus B k m z)
    (hz' : FiniteBallSdpIncrementConsensus B k m z') : z = z' := by
  obtain ⟨d, hd⟩ := hz.1
  exact Option.some.inj ((hz.2 d hd).symm.trans (hz'.2 d hd))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Select the unique nonempty-shell consensus on the faced-class representative. -/
@[expose] noncomputable def finiteBallSdpIncrementKernel (k : ℤ) (m : ℕ)
    (q : FacedFramedBallClass) : Option ℤ := by
  classical
  exact if h : ∃ z, FiniteBallSdpIncrementConsensus q.out.toFramedBall k m z then
    some h.choose else none

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The kernel has the complete nonempty-shell consensus characterization. -/
theorem finiteBallSdpIncrementKernel_eq_some_iff (k : ℤ) (m : ℕ)
    (q : FacedFramedBallClass) (z : ℤ) :
    finiteBallSdpIncrementKernel k m q = some z ↔
      FiniteBallSdpIncrementConsensus q.out.toFramedBall k m z := by
  classical
  unfold finiteBallSdpIncrementKernel
  split_ifs with h
  · constructor
    · intro he
      have hz : h.choose = z := Option.some.inj he
      simpa only [hz] using h.choose_spec
    · intro hz
      exact congrArg some (finiteBallSdpIncrementConsensus_unique _ _ _ h.choose_spec hz)
  · constructor
    · intro he
      cases he
    · intro hz
      exact (h ⟨z, hz⟩).elim

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
First grow the enclosing ball, then let the target shell escape to infinity. -/
@[expose] noncomputable def finiteBallSdpIncrementCandidate (k : ℤ)
    (M : RootedLocallyFinitePlanarMap) : Option ℤ :=
  eventualFiniteIncrement fun m => eventualFiniteIncrement fun r =>
    finiteBallSdpIncrementKernel k m (rootedLocallyFiniteFacedBallClass r M)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Both eventual finite-value selections are Borel measurable. -/
theorem measurable_finiteBallSdpIncrementCandidate (k : ℤ) :
    Measurable (finiteBallSdpIncrementCandidate k) := by
  apply measurable_eventualFiniteIncrement
  intro m
  apply measurable_eventualFiniteIncrement
  intro r
  let : MeasurableSpace FacedFramedBallClass := ⊤
  have hk : Measurable (finiteBallSdpIncrementKernel k m) := measurable_from_top
  exact hk.comp (measurable_incrementFacedBallClass r)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Integer extension of the candidate. The default is not an unreachable distance.
Its almost-sure irrelevance is an open realization obligation. -/
@[expose] noncomputable def finiteBallSdpIncrementObservable (k : ℤ)
    (M : RootedLocallyFinitePlanarMap) : ℤ :=
  (finiteBallSdpIncrementCandidate k M).getD 0

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The intrinsic finite-ball integer observable is measurable at every index. -/
theorem finiteBallSdpIncrementObservable_measurable (k : ℤ) :
    Measurable (finiteBallSdpIncrementObservable k) := by
  exact (measurable_of_countable (fun z : Option ℤ => z.getD 0)).comp
    (measurable_finiteBallSdpIncrementCandidate k)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Exact two-stage eventual finite-value characterization. -/
theorem finiteBallSdpIncrementCandidate_eq_some_iff (k : ℤ)
    (M : RootedLocallyFinitePlanarMap) (z : ℤ) :
    finiteBallSdpIncrementCandidate k M = some z ↔
      ∃ N : ℕ, ∀ m ≥ N, ∃ R : ℕ, ∀ r ≥ R,
        finiteBallSdpIncrementKernel k m (rootedLocallyFiniteFacedBallClass r M) = some z := by
  simp only [finiteBallSdpIncrementCandidate, eventualFiniteIncrement_eq_some_iff]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The future-code SDP increment, without requiring a not-yet-built increment module. -/
@[expose] noncomputable def uibhbotMirrorSdpCodeIncrement (k : ℤ)
    (W : ℤ → Fin 3) : ℤ :=
  SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 (uibhbotFutureCode k W)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The future-code pushforward proves the SDP marginal law directly. -/
theorem uibhbotMirrorSdpCodeIncrement_law (k : ℤ) :
    (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map (uibhbotMirrorSdpCodeIncrement k) =
      iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) := by
  exact uibhbotFutureCode_map k
    ((measurable_busemannSDPMeasurableVersion 0).sub
      (measurable_busemannSDPMeasurableVersion (0 - 1)))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Open code realization at one specified index, kept separate from measurability. -/
@[expose] def UIBHBOTSdpIncrementObservableRealizationAt
    (Φ : ℤ → RootedLocallyFinitePlanarMap → ℤ) (k : ℤ) : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
    Φ k (uibhbotRootedPlanarMapOfCode W) = uibhbotMirrorSdpCodeIncrement k W

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Open almost-sure scalar reflection at exactly the two indices used for symmetry. -/
@[expose] def UIBHBOTSdpIncrementObservableReflection
    (Φ : ℤ → RootedLocallyFinitePlanarMap → ℤ) : Prop :=
  ∀ᵐ M ∂(uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap),
    Φ 0 (mirrorRootedLocallyFinitePlanarMap M) = -Φ 2 M

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Open shell stabilization at one index. It is defined, never asserted. -/
@[expose] def UIBHBOTSdpIncrementBallShellStabilizationAt (k : ℤ) : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
    ∃ N : ℕ, ∀ m ≥ N, ∃ R : ℕ, ∀ r ≥ R,
      finiteBallSdpIncrementKernel k m
          (rootedLocallyFiniteFacedBallClass r (uibhbotRootedPlanarMapOfCode W)) =
        some (uibhbotMirrorSdpCodeIncrement k W)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Open boundary identification, independent of the choice of directed distance.
This proposition is defined but is not assumed by the distance transport proofs. -/
@[expose] def UIBHBOTIntrinsicSdpIncrementBoundaryIdentificationAt (k : ℤ) : Prop :=
  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
    ∀ (H : WholePlaneRotationHypothesis W)
      (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
      (C : UIBHBOTCertifiedRootCapture W 0),
      incrementOrbitVertex W H
          (intrinsicSdpIncrementSource
            (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) k) =
        uibhbotBusemannSource k W

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Shell stabilization would give realization at that index; stabilization stays open. -/
theorem finiteBallSdpIncrementObservable_realization_of_ballShellStabilization
    (k : ℤ) (h : UIBHBOTSdpIncrementBallShellStabilizationAt k) :
    UIBHBOTSdpIncrementObservableRealizationAt finiteBallSdpIncrementObservable k := by
  filter_upwards [h] with W hW
  have he := (finiteBallSdpIncrementCandidate_eq_some_iff k
    (uibhbotRootedPlanarMapOfCode W) (uibhbotMirrorSdpCodeIncrement k W)).2 hW
  simp only [finiteBallSdpIncrementObservable, he, Option.getD_some]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Conditional transport from intrinsic realization to the proved SDP marginal law. -/
theorem uibhbotSdpIncrementObservable_law
    (Φ : ℤ → RootedLocallyFinitePlanarMap → ℤ) (k : ℤ)
    (hΦm : Measurable (Φ k)) (hΦr : UIBHBOTSdpIncrementObservableRealizationAt Φ k) :
    (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map (Φ k) =
      iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) := by
  change ((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    uibhbotRootedPlanarMapOfCode).map (Φ k) = _
  rw [Measure.map_map hΦm measurable_uibhbotRootedPlanarMapOfCode]
  calc
    _ = (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
        (uibhbotMirrorSdpCodeIncrement k) := Measure.map_congr hΦr
    _ = _ := uibhbotMirrorSdpCodeIncrement_law k




theorem hsymSdp_of_uibhbot_mirror_invariance
    (h0 : UIBHBOTSdpIncrementObservableRealizationAt finiteBallSdpIncrementObservable 0)
    (h2 : UIBHBOTSdpIncrementObservableRealizationAt finiteBallSdpIncrementObservable 2)
    (href : UIBHBOTSdpIncrementObservableReflection finiteBallSdpIncrementObservable) :
    iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω) := by
  have hinv := uibhbotLaw_mirror_invariant
    DirectedDistances.PaperProofs.Section3.rootedPlanarMapLaw_hasOuterApproxClosed
  have hscalar :
      (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
          (finiteBallSdpIncrementObservable 0) =
        (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
          (fun M => -finiteBallSdpIncrementObservable 2 M) := by
    calc
      _ = ((uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
          mirrorRootedLocallyFinitePlanarMap).map (finiteBallSdpIncrementObservable 0) := by
        rw [hinv]
      _ = (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
          (finiteBallSdpIncrementObservable 0 ∘ mirrorRootedLocallyFinitePlanarMap) :=
        Measure.map_map (finiteBallSdpIncrementObservable_measurable 0)
          measurable_mirrorRootedLocallyFinitePlanarMap
      _ = _ := Measure.map_congr href
  have hinc : Measurable
      (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) :=
    (measurable_busemannSDPMeasurableVersion 0).sub
      (measurable_busemannSDPMeasurableVersion (0 - 1))
  calc
    _ = (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
        (finiteBallSdpIncrementObservable 0) :=
      (uibhbotSdpIncrementObservable_law _ 0
        (finiteBallSdpIncrementObservable_measurable 0) h0).symm
    _ = (uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
        (fun M => -finiteBallSdpIncrementObservable 2 M) := hscalar
    _ = ((uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap).map
        (finiteBallSdpIncrementObservable 2)).map (fun z : ℤ => -z) :=
      (Measure.map_map measurable_neg (finiteBallSdpIncrementObservable_measurable 2)).symm
    _ = (iidCodeMeasure.map
        (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0)).map
          (fun z : ℤ => -z) := by
      rw [uibhbotSdpIncrementObservable_law _ 2
        (finiteBallSdpIncrementObservable_measurable 2) h2]
    _ = _ := Measure.map_map measurable_neg hinc

end DirectedDistances.PaperProofs.Section5
