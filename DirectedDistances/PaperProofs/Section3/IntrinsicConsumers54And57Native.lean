/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion8
public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion2
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumers54And57Final
public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56SideAlignment2

/-! # Native leftmost cut geodesics

belong to the sole coordinator. No intrinsic-object qualifier is removed. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section7 DirectedDistances.Paper.Section4
open DirectedDistances.RandomWalk MeasureTheory Filter Set
open scoped Classical

section Source

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "S" => uibotWholePlaneSourceDomain W H G hp
local notation "D" => m0CutData W H h (fun _ _ => hp _)
local notation "C" => intrinsicGeodesicSourceCut W H G hp D
local notation "E" => uibotCut2SourceDartEquiv W H h hpast hp

/-- Helper toward Proposition 3.9: the restricted intrinsic rightmost
selector reflects the code selector, including missing boundary darts. -/
theorem intrinsicConsumersNative_source_rightmost_iff (v e : ℕ) :
    intrinsicBetweenCutRightmostOutgoingAt S C
      (wholePlaneVertexι W 0 v) (wholePlaneEdgeι W 0 e) ↔
    kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0) v e := by
  constructor
  · rintro ⟨d, hd, hv, ht, a, hr, hn⟩
    obtain ⟨d, rfl⟩ := (E).surjective d
    have htail := (uibotCut2SourceDartEquiv_tail W H h hpast hp d).mp ht.2.2
    have hd' : d = wholePlaneDartι W 0 (e, false) := by
      apply Prod.ext hd
      change d.2 = false
      cases hb : d.2
      · rfl
      · exact (htail.1 hb).elim
    subst d
    have he := (intrinsicBetween_source_cut_tail_iff W H h hpast hp (e, false)).mp ht
    have hv' : edgeWest (shiftedStream W 0) e = v := by
      erw [uibotCut2SourceDartEquiv_vertex, wholePlaneDartVertex_ι] at hv
      exact wholePlaneVertexι_injective W 0 hv
    obtain ⟨a, rfl⟩ := (E).surjective a
    have hrot := (uibotCut2_source_rotation_iff W H h hpast hp
      (wholePlaneDartι W 0 (e, false)) a).mp hr
    have ha := (futureMap_rotation_iff D h (fun _ _ => hp _) (e, false) a).mp hrot.2.2
    subst a
    refine ⟨he.2, hv', 1, by omega, ?_, ?_⟩
    · rw [pow_one]
      exact fun hs => hn ((intrinsicBetween_source_cut_tail_iff W H h hpast hp _).mpr hs)
    · intro j hj hj1
      omega
  · exact intrinsicBetween_source_rightmost_outgoing W H h hpast hp

/-- Helper toward Proposition 3.9: every intrinsic rightmost ray at a
source boundary label equals the source image of the code reference ray. -/
theorem intrinsicConsumersNative_source_reference_unique (k : ℤ)
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
    (hstart : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
    (hedge : T.edge = R.edge)
    (Q : IntrinsicInfiniteDirectedPath S C ((D).x k))
    (hQ : RightmostInCut S C ((D).x k) Q) :
    Q = intrinsicSourceInfinitePathEquiv W H G hp D ((D).x k)
      (m0CutPathOfPresentPath W H h (fun _ _ => hp _) k T) := by
  obtain ⟨q, rfl⟩ := (intrinsicSourceInfinitePathEquiv W H G hp D ((D).x k)).surjective Q
  obtain ⟨q, rfl⟩ := m0Cut_infinitePath_surjective W H h (fun _ _ => hp _) k q
  have ht := intrinsicBetween_source_reference_rightmost W H h hpast hp k T R hstart hedge
  have hqmost (n : ℕ) : kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
      (q.initial n).1.id (q.edge n) := by
    have hh := hQ n
    rw [intrinsicSourceInfinitePathEquiv_vertex, m0CutPathOfPresentPath_vertex] at hh
    exact (intrinsicConsumersNative_source_rightmost_iff W H h hpast hp _ _).mp hh
  have htmost (n : ℕ) : kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
      (T.initial n).1.id (T.edge n) := by
    have hh := ht n
    rw [intrinsicSourceInfinitePathEquiv_vertex, m0CutPathOfPresentPath_vertex] at hh
    exact (intrinsicConsumersNative_source_rightmost_iff W H h hpast hp _ _).mp hh
  have he : ∀ n, q.edge n = T.edge n := by
    intro n
    induction n with
    | zero =>
      have hq0 := (q.initial 0).2.eq_of_length_zero (q.prefix_length 0)
      have ht0 := (T.initial 0).2.eq_of_length_zero (T.prefix_length 0)
      have hv : (q.initial 0).1.id = (T.initial 0).1.id :=
        congrArg PresentVertex.id (hq0.symm.trans ht0)
      exact kmswRunRightmostOutAt_unique _ _ _ (hqmost 0) (hv ▸ htmost 0)
    | succ n ih =>
      have hv : (q.initial (n + 1)).1.id = (T.initial (n + 1)).1.id :=
        (q.edge_incoming_at_succ (shiftedStream W 0) n).2.symm.trans
          ((congrArg (edgeEast (shiftedStream W 0)) ih).trans
            (T.edge_incoming_at_succ (shiftedStream W 0) n).2)
      exact kmswRunRightmostOutAt_unique _ _ _ (hqmost _) (hv ▸ htmost _)
  exact IntrinsicInfiniteDirectedPath.edge_ext
    (fun n => congrArg (wholePlaneEdgeι W 0) (he n))

/-- Helper toward Proposition 3.9: changing a code leftmost comparison to
the actual rightmost reference preserves all competitor containments. -/
theorem intrinsicConsumersNative_cutLeftmost_reference
    (longest : Bool) (k : ℤ)
    (P : M0CutInfiniteGeodesic W H h (fun _ _ => hp _) k longest)
    (U T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
    (hedge : T.edge = R.edge)
    (hleft : Xdp.CutLeftmostXdp W H h hpast (fun _ _ => hp _) longest k P U) :
    Xdp.CutLeftmostXdp W H h hpast (fun _ _ => hp _) longest k P T := by
  intro Q hQ
  obtain ⟨q, rfl⟩ := m0Cut_infinitePath_surjective W H h (fun _ _ => hp _) k Q
  have hu := hleft (m0CutPathOfPresentPath W H h (fun _ _ => hp _) k q) hQ
  have htmost (n : ℕ) : kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
      (T.initial n).1.id (T.edge n) := by
    have he := R.rightmost n
    rw [← hedge] at he
    exact (he.2.1.symm.trans (T.edge_outgoing_at_initial (shiftedStream W 0) n).2) ▸ he
  have hb := intrinsicBetween7_source_traces_subset_between_of_rightmost
    W H h hpast hp q T htmost
  dsimp only at hb
  rw [intrinsicGeodesicSource_trace, intrinsicGeodesicSource_trace] at hb
  intro z hz
  exact ⟨(hb (Or.inl hz)).1, (hu hz).2⟩

variable (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H))
      A.map A.root)

local notation "C'" => intrinsicBusemannImageCut W H G hp D A I

/-- Helper toward Proposition 3.9: every intrinsic cut-rightmost reference
in every representative is the image of the code rightmost reference. -/
theorem intrinsicConsumersNative_image_reference_unique (k : ℤ)
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
    (hstart : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
    (hedge : T.edge = R.edge)
    (Q : IntrinsicInfiniteDirectedPath A C' (I.vertexEquiv ((D).x k)))
    (hQ : RightmostInCut A C' (I.vertexEquiv ((D).x k)) Q) :
    Q = intrinsicImageInfinitePathEquiv W H G hp D A I ((D).x k)
      (m0CutPathOfPresentPath W H h (fun _ _ => hp _) k T) := by
  obtain ⟨q, rfl⟩ := (intrinsicInfiniteDirectedPathEquiv
    (A := S) (B := A) I C ((D).x k)).surjective Q
  have he := intrinsicConsumersNative_source_reference_unique W H h hpast hp k T R
    hstart hedge q ((rightmostInCut_map_iff I q).mp hQ)
  exact congrArg (intrinsicInfiniteDirectedPathMap I) he

/-- Helper toward Proposition 3.9: every intrinsic segment geodesic is
the image of a code segment geodesic, retaining its full edge stream. -/
theorem intrinsicConsumersNative_geodesic_surjective (longest : Bool) (k : ℤ) :
    Function.Surjective
      (intrinsicGeodesicOfCode W H h (fun _ _ => hp _) G hp A I
        (k := k) (longest := longest)) := by
  rintro ⟨Q, hQ⟩
  obtain ⟨q, rfl⟩ := (intrinsicImageInfinitePathEquiv W H G hp D A I ((D).x k)).surjective Q
  obtain ⟨q, rfl⟩ := m0Cut_infinitePath_surjective W H h (fun _ _ => hp _) k q
  have hopt := (intrinsicImageInfinitePathEquiv_optimal_iff W H G hp D A I _ _ longest).mp hQ
  have hq : if longest then q.HasLongestSegments else q.HasShortestSegments := by
    cases longest with
    | false => exact (Xdp.Sdp.m0Cut_hasShortestSegments_iff W H h (fun _ _ => hp _) k q).mp hopt
    | true => exact (m0Cut_hasLongestSegments_iff W H h (fun _ _ => hp _) k q).mp hopt
  have hstart : (q.initial 0).1.id = boundaryVertex (shiftedStream W 0) h k :=
    congrArg PresentVertex.id ((q.initial 0).2.eq_of_length_zero (q.prefix_length 0)).symm
  let P : M0CutInfiniteGeodesic W H h (fun _ _ => hp _) k longest := {
    codePath := q
    segments := hq
    startsAtCutBoundary := ((D).x_eq h (fun _ _ => hp _) k).trans
      (congrArg (wholePlaneVertexι W 0) hstart.symm)
    cutStep := fun n => by
      apply (m0Cut_identification_directedStep W H h (fun _ _ => hp _)
        (q.initial n).1.id (q.initial (n + 1)).1.id).mpr
      exact ⟨q.edge n, (q.edge_outgoing_at_initial (shiftedStream W 0) n).1,
        congrArg (wholePlaneVertexι W 0) (q.edge_outgoing_at_initial (shiftedStream W 0) n).2,
        congrArg (wholePlaneVertexι W 0) (q.edge_incoming_at_succ (shiftedStream W 0) n).2⟩ }
  refine ⟨P, ?_⟩
  apply Subtype.ext
  exact IntrinsicInfiniteDirectedPath.edge_ext (fun _ => rfl)

/-- Helper toward Proposition 3.9: native leftmostness against the image
rightmost reference is precisely the full source leftmost comparison. -/
theorem intrinsicConsumersNative_leftmost_iff
    (longest : Bool) (k : ℤ)
    (P : M0CutInfiniteGeodesic W H h (fun _ _ => hp _) k longest)
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
    (hstart : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
    (hedge : T.edge = R.edge) :
    IntrinsicLeftmostInRegion A C' (I.vertexEquiv ((D).x k)) longest
      (intrinsicGeodesicOfCode W H h (fun _ _ => hp _) G hp A I P)
      (intrinsicImageInfinitePathEquiv W H G hp D A I ((D).x k)
        (m0CutPathOfPresentPath W H h (fun _ _ => hp _) k T)) ↔
    Xdp.CutLeftmostXdp W H h hpast (fun _ _ => hp _) longest k P T := by
  have hn := intrinsicBetween8_native_eq_closedBetween W H h hpast hp A I
    longest k P T R hstart hedge
  have hi := intrinsicImage_leftmost_image_region_iff W H h hpast
    (fun _ _ => hp _) hp A I longest k P T
  constructor
  · intro hl
    apply hi.mp
    intro Q hQ
    have hh := hl ⟨Q, hQ⟩
    change intrinsicEdgeRayTrace A (fun n => (Q.edge n).val) ⊆
      nativeBetween A (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n)))
        (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (T.edge n))) at hh
    rwa [hn] at hh
  · intro hl Q
    have hh := hi.mpr hl Q.val Q.property
    change intrinsicEdgeRayTrace A (fun n => (Q.val.edge n).val) ⊆
      nativeBetween A (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n)))
        (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (T.edge n)))
    rwa [hn]

/-- Helper toward Proposition 3.9: every intrinsic geodesic lies in the
native region between the code leftmost image and any intrinsically
cut-rightmost reference, preserving individual geometric edge identities. -/
theorem intrinsicConsumersNative_containment
    (longest : Bool) (k : ℤ)
    (P : M0CutInfiniteGeodesic W H h (fun _ _ => hp _) k longest)
    (U : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : Xdp.CutLeftmostXdp W H h hpast (fun _ _ => hp _) longest k P U)
    (T : IntrinsicInfiniteDirectedPath A C' (I.vertexEquiv ((D).x k)))
    (hT : RightmostInCut A C' (I.vertexEquiv ((D).x k)) T)
    (Q : IntrinsicInfiniteXDPGeodesic A C' (I.vertexEquiv ((D).x k)) longest) :
    intrinsicEdgeRayTrace A (fun n => (Q.val.edge n).val) ⊆
      nativeBetween A
        (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n)))
        (fun n => (T.edge n).val) := by
  obtain ⟨R, hstart, _, t, hedge, _, _⟩ :=
    RightmostRay.m0Cut_rightmost_presentPath_exists W H h (fun _ _ => hp _) k
  rw [intrinsicConsumersNative_image_reference_unique W H h hpast hp A I k t R
    hstart hedge T hT]
  exact (intrinsicConsumersNative_leftmost_iff W H h hpast hp A I
    longest k P t R hstart hedge).mpr
      (intrinsicConsumersNative_cutLeftmost_reference W H h hpast hp
        longest k P U t R hedge hleft) Q

/-- Helper toward Proposition 3.9: the code leftmost geodesic is the unique
intrinsic leftmost geodesic, with every intrinsic reference quantified. -/
theorem intrinsicConsumersNative_leftmost_unique
    (longest : Bool) (k : ℤ)
    (P : M0CutInfiniteGeodesic W H h (fun _ _ => hp _) k longest)
    (U T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
    (hstart : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
    (hedge : T.edge = R.edge)
    (hleft : Xdp.CutLeftmostXdp W H h hpast (fun _ _ => hp _) longest k P U) :
    IsIntrinsicLeftmostXDPGeodesic A C' (I.vertexEquiv ((D).x k)) longest
      (intrinsicGeodesicOfCode W H h (fun _ _ => hp _) G hp A I P) ∧
    ∀ Q : IntrinsicInfiniteXDPGeodesic A C' (I.vertexEquiv ((D).x k)) longest,
      IsIntrinsicLeftmostXDPGeodesic A C' (I.vertexEquiv ((D).x k)) longest Q →
      Q = intrinsicGeodesicOfCode W H h (fun _ _ => hp _) G hp A I P := by
  have hPT := intrinsicConsumersNative_cutLeftmost_reference W H h hpast hp
    longest k P U T R hedge hleft
  constructor
  · exact ⟨_, intrinsicBetween_image_reference_rightmost W H h hpast hp A I k T R
      hstart hedge, (intrinsicConsumersNative_leftmost_iff W H h hpast hp A I
        longest k P T R hstart hedge).mpr hPT⟩
  · intro Q hQ
    obtain ⟨q, rfl⟩ := intrinsicConsumersNative_geodesic_surjective W H h hpast hp A I longest k Q
    obtain ⟨r, hr, hl⟩ := hQ
    rw [intrinsicConsumersNative_image_reference_unique W H h hpast hp A I k T R
      hstart hedge r hr] at hl
    have hq := (intrinsicConsumersNative_leftmost_iff W H h hpast hp A I
      longest k q T R hstart hedge).mp hl
    have he := m0CutGeodesicSlice_codePath_edge_eq_of_cutLeftmost W H h hpast
      (fun _ _ => hp _) longest k q P T U hq hleft
    apply Subtype.ext
    apply IntrinsicInfiniteDirectedPath.edge_ext
    intro n
    exact congrArg (fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)) (congrFun he n)

end Source

/-- Helper toward Proposition 3.9: on one iid conull event the constructed
intrinsic cut has unique native leftmost geodesics in both modes, together
with every coalescence, least-offset, normalized Busemann and increment
clause of the Lemma 5.4 and Lemma 5.7 consumer theorem. All representatives
and all source isomorphisms share the same witnesses. -/
theorem intrinsicConsumersNative54And57_sample_ae :
    ∀ᵐ U ∂wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U
      let W := uibotRecoveredCode z
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))
      let D := m0CutData W H h hLL
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      ∃ s : ∀ x : XDP, M0CutGeodesicSliceWitness W x,
      z = Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root) ∧
        ∀ I : D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root,
        let C := intrinsicFutureCut2Pushforward I (uibotCut2Source W H h hpast hp)
        let S := intrinsicConsumersBusemannCut C
        (∀ k, C.x k = I.vertexEquiv (D.x k)) ∧
        ∀ x : XDP,
        let longest := if x = XDP.ldp then true else false
        let X₀ := if x = XDP.ldp then identifiedLDPBusemann W
          else identifiedSDPBusemann W
        let P : ∀ k : ℤ, IntrinsicInfiniteXDPGeodesic A S (C.x k) longest :=
          fun k => intrinsicConsumersGeodesicOfCode W H h hpast hp A I ((s x).P k)
        (if x = XDP.ldp then IsIntrinsicBusemannLDP A S C.x X₀
          else IsIntrinsicBusemannSDP A S C.x X₀) ∧
        (∀ X : ℤ → ℤ,
          (if x = XDP.ldp then IsIntrinsicBusemannLDP A S C.x X
            else IsIntrinsicBusemannSDP A S C.x X) → X = X₀) ∧
        (∀ k k' : ℤ, ∃ a b : ℕ,
          IntrinsicEdgeTailsCoalesce (P k).val (P k').val a b) ∧
        (∀ k : ℤ, ∃! q : ℕ × ℕ,
          IntrinsicLeastEdgeCoalescence (P k).val (P (k - 1)).val q.1 q.2) ∧
        (∀ k : ℤ,
          IntrinsicLeastEdgeCoalescence (P k).val (P (k - 1)).val
            ((s x).theta k) ((s x).thetaMinus k) ∧
          uibotGeomCoalescenceOffsets z x k = ((s x).thetaMinus k, (s x).theta k) ∧
          uibotCodeCoalescenceOffsets W x k = ((s x).thetaMinus k, (s x).theta k)) ∧
        (∀ X : ℤ → ℤ,
          (if x = XDP.ldp then IsIntrinsicBusemannLDP A S C.x X
            else IsIntrinsicBusemannSDP A S C.x X) →
          ∀ (k : ℤ) (theta thetaMinus : ℕ),
            IntrinsicLeastEdgeCoalescence (P k).val (P (k - 1)).val theta thetaMinus →
            X k - X (k - 1) = (theta : ℤ) - (thetaMinus : ℤ)) ∧
        ∀ k : ℤ,
          IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest (P k) ∧
          ∀ Q : IntrinsicInfiniteXDPGeodesic A S (C.x k) longest,
            IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest Q → Q = P k := by
  filter_upwards [intrinsicConsumers54And57_sample_ae] with U hU
  dsimp only at hU ⊢
  obtain ⟨H, h, hpast, hp, s, hclass, hrep⟩ := hU
  refine ⟨H, h, hpast, hp, s, hclass, ?_⟩
  intro A hA
  refine ⟨(hrep A hA).1, ?_⟩
  intro I
  refine ⟨((hrep A hA).2 I).1, ?_⟩
  intro x
  obtain ⟨hchar, huniq, hcoal, hleast, hoff, hinc⟩ := ((hrep A hA).2 I).2 x
  refine ⟨hchar, huniq, hcoal, hleast, hoff, hinc, ?_⟩
  intro k
  obtain ⟨R, hstart, _, T, hedge, _, _⟩ :=
    RightmostRay.m0Cut_rightmost_presentPath_exists _ H h (fun _ _ => hp _) k
  exact intrinsicConsumersNative_leftmost_unique _ H h hpast hp A I
    (if x = XDP.ldp then true else false) k ((s x).P k) ((s x).T k)
    T R hstart hedge ((s x).hleft k)

end DirectedDistances.PaperProofs.Section3
end
