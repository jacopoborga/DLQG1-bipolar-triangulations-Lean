/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicGeodesicIdentification















public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1
open Set
open scoped Topology

/-- Helper toward Proposition 3.9: a set touches a specified side of an
actual directed ray edge at every interior parameter. `reverse = false`
tests the left side; `reverse = true` tests the left side of the reversed
dart, hence the right side of the directed edge. Missing edges acquire no
orientation from this predicate. -/
@[expose] def intrinsicRayTouchesSide (A : D39DomainRootedMap.{0})
    (P : ℕ → A.E) (F : Set ℂ) (reverse : Bool) : Prop :=
  ∃ (n : ℕ) (d : A.E × Bool), d.1 = P n ∧
    intrinsicFutureAmbientTail A d ∧
    ∀ s, LeftAtOn F
      (intrinsicFutureDartArc A (d.1, Bool.xor d.2 reverse)) s

/-- Helper toward Proposition 3.9: the complementary components incident
only to the right of `P` and to the left of `R`, tested using winding and
the directed darts of this drawing. No coordinate or source isomorphism
occurs in the definition. -/
@[expose] def intrinsicOpenBetween (A : D39DomainRootedMap.{0})
    (P R : ℕ → A.E) : Set ℂ :=
  {z | ∃ w : ℂ, w ∉ intrinsicEdgeRayTrace A P ∪ intrinsicEdgeRayTrace A R ∧
    let C := connectedComponentIn
      (intrinsicEdgeRayTrace A P ∪ intrinsicEdgeRayTrace A R)ᶜ w
    z ∈ C ∧ intrinsicRayTouchesSide A P C true ∧
      intrinsicRayTouchesSide A R C false ∧
      ¬ intrinsicRayTouchesSide A P C false ∧
      ¬ intrinsicRayTouchesSide A R C true}

/-- Helper toward Proposition 3.9: the closure of the selected
complementary components together with both complete geometric traces.
The source `closedBetween` characterization is a separate obligation. -/
@[expose] def nativeBetween (A : D39DomainRootedMap.{0})
    (P R : ℕ → A.E) : Set ℂ :=
  closure (intrinsicOpenBetween A P R ∪
    (intrinsicEdgeRayTrace A P ∪ intrinsicEdgeRayTrace A R))

/-- Helper toward Proposition 3.9: the native component construction is
closed, including the limiting points of its selected components. -/
theorem isClosed_nativeBetween (A : D39DomainRootedMap.{0}) (P R : ℕ → A.E) :
    IsClosed (nativeBetween A P R) := isClosed_closure

/-- Helper toward Proposition 3.9: both complete ray traces, including
their vertices and individual edge interiors, belong to the native region. -/
theorem intrinsicEdgeRayTrace_union_subset_nativeBetween
    (A : D39DomainRootedMap.{0}) (P R : ℕ → A.E) :
    intrinsicEdgeRayTrace A P ∪ intrinsicEdgeRayTrace A R ⊆ nativeBetween A P R :=
  fun _ hz => subset_closure (Or.inr hz)

/-- Helper toward Proposition 3.9: coincident rays select no
complementary component; in particular, their exterior component is excluded. -/
theorem intrinsicOpenBetween_self (A : D39DomainRootedMap.{0}) (P : ℕ → A.E) :
    intrinsicOpenBetween A P P = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨w, _, _, hright, _, _, hnright⟩
  exact hnright hright

/-- Helper toward Proposition 3.9: for a closed ray trace the native
region between the ray and itself is exactly that trace. -/
theorem nativeBetween_self (A : D39DomainRootedMap.{0}) (P : ℕ → A.E)
    (hP : IsClosed (intrinsicEdgeRayTrace A P)) :
    nativeBetween A P P = intrinsicEdgeRayTrace A P := by
  rw [nativeBetween, intrinsicOpenBetween_self, Set.union_self, Set.empty_union,
    hP.closure_eq]

/-- Helper toward Proposition 3.9: the selected components form an open
set when both ray traces are closed. -/
theorem isOpen_intrinsicOpenBetween (A : D39DomainRootedMap.{0}) (P R : ℕ → A.E)
    (hP : IsClosed (intrinsicEdgeRayTrace A P))
    (hR : IsClosed (intrinsicEdgeRayTrace A R)) :
    IsOpen (intrinsicOpenBetween A P R) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨w, hw, hz, hPr, hRl, hnPl, hnRr⟩
  apply Filter.mem_of_superset (((hP.union hR).isOpen_compl.connectedComponentIn).mem_nhds hz)
  intro q hq
  exact ⟨w, hw, hq, hPr, hRl, hnPl, hnRr⟩

/-- Helper toward Proposition 3.9: the closed-trace construction is
equally the closure of its selected components together with the two traces. -/
theorem nativeBetween_eq_closure_union (A : D39DomainRootedMap.{0})
    (P R : ℕ → A.E) (hP : IsClosed (intrinsicEdgeRayTrace A P))
    (hR : IsClosed (intrinsicEdgeRayTrace A R)) :
    nativeBetween A P R = closure (intrinsicOpenBetween A P R) ∪
      (intrinsicEdgeRayTrace A P ∪ intrinsicEdgeRayTrace A R) := by
  rw [nativeBetween, closure_union, (hP.union hR).closure_eq]

/-- Helper toward Proposition 3.9: an oriented tail in a specified cut
retains its geometric edge and loses its orientation whenever either the
ambient map or the cut marks it missing. -/
@[expose] def intrinsicBetweenCutTail (A : D39DomainRootedMap.{0})
    (S : IntrinsicBusemannCut A) (d : A.E × Bool) : Prop :=
  d.1 ∈ S.edges ∧ ¬ S.missing d.1 ∧ intrinsicFutureAmbientTail A d

/-- Helper toward Proposition 3.9: the cut's rightmost outgoing edge
has a nonoutgoing clockwise predecessor in the restricted geometric star.
The rotation retains geometric missing boundary incidences, which can stop
the outgoing block, while the tail predicate gives them no orientation. -/
@[expose] def intrinsicBetweenCutRightmostOutgoingAt (A : D39DomainRootedMap.{0})
    (S : IntrinsicBusemannCut A) (v : A.V) (e : A.E) : Prop :=
  ∃ d : A.E × Bool, d.1 = e ∧ d39GeomRootVertex A.map d = v ∧
    intrinsicBetweenCutTail A S d ∧
    ∃ a : A.E × Bool, intrinsicFutureRotation A S.edges d a ∧
      ¬ intrinsicBetweenCutTail A S a

/-- Helper toward Proposition 3.9: every edge of the ray is rightmost
in the cut's own restricted rotation, rather than in the unrestricted
ambient map. This predicate asserts no existence or uniqueness. -/
@[expose] def RightmostInCut (A : D39DomainRootedMap.{0})
    (S : IntrinsicBusemannCut A) (v : A.V)
    (T : IntrinsicInfiniteDirectedPath A S v) : Prop :=
  ∀ n, intrinsicBetweenCutRightmostOutgoingAt A S (T.vertex n) (T.edge n).val

section Transport

variable {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)

/-- Helper toward Proposition 3.9: cut-tail orientation is preserved
and reflected by geometric transport, including both missing predicates. -/
theorem intrinsicBetweenCutTail_map (S : IntrinsicBusemannCut A) (d : A.E × Bool) :
    intrinsicBetweenCutTail B (intrinsicGeodesicMapCut I S)
      (intrinsicFutureDartEquiv I d) ↔ intrinsicBetweenCutTail A S d := by
  change (I.edgeEquiv d.1 ∈ I.edgeEquiv '' S.edges ∧
    ¬ S.missing (I.edgeEquiv.symm (I.edgeEquiv d.1)) ∧
    intrinsicFutureAmbientTail B (intrinsicFutureDartEquiv I d)) ↔ _
  rw [I.edgeEquiv.injective.mem_set_image, Equiv.symm_apply_apply,
    intrinsicFutureAmbientTail_map]
  rfl

/-- Helper toward Proposition 3.9: the cut's rightmost outgoing
selector transports with the cut's restricted star, in both directions. -/
theorem intrinsicBetweenCutRightmostOutgoingAt_map_iff
    (S : IntrinsicBusemannCut A) (v : A.V) (e : A.E) :
    intrinsicBetweenCutRightmostOutgoingAt B (intrinsicGeodesicMapCut I S)
      (I.vertexEquiv v) (I.edgeEquiv e) ↔
    intrinsicBetweenCutRightmostOutgoingAt A S v e := by
  constructor
  · rintro ⟨d, hd, hv, ht, a, hr, hn⟩
    obtain ⟨d, rfl⟩ := (intrinsicFutureDartEquiv I).surjective d
    obtain ⟨a, rfl⟩ := (intrinsicFutureDartEquiv I).surjective a
    refine ⟨d, I.edgeEquiv.injective hd, ?_,
      (intrinsicBetweenCutTail_map I S d).mp ht, a,
      (intrinsicFutureRotation_map_iff I S.edges d a).mp hr, ?_⟩
    · exact I.vertexEquiv.injective ((intrinsicFutureDartEquiv_vertex I d).symm.trans hv)
    · exact fun h => hn ((intrinsicBetweenCutTail_map I S a).mpr h)
  · rintro ⟨d, hd, hv, ht, a, hr, hn⟩
    refine ⟨intrinsicFutureDartEquiv I d, congrArg I.edgeEquiv hd,
      (intrinsicFutureDartEquiv_vertex I d).trans (congrArg I.vertexEquiv hv),
      (intrinsicBetweenCutTail_map I S d).mpr ht, intrinsicFutureDartEquiv I a,
      (intrinsicFutureRotation_map_iff I S.edges d a).mpr hr, ?_⟩
    exact fun h => hn ((intrinsicBetweenCutTail_map I S a).mp h)

/-- Helper toward Proposition 3.9: rightmostness of a ray transports
with its cut and its starting vertex, using the restricted rotation. -/
theorem rightmostInCut_map_iff {S : IntrinsicBusemannCut A} {v : A.V}
    (T : IntrinsicInfiniteDirectedPath A S v) :
    RightmostInCut B (intrinsicGeodesicMapCut I S) (I.vertexEquiv v)
      (intrinsicInfiniteDirectedPathMap I T) ↔ RightmostInCut A S v T := by
  unfold RightmostInCut
  apply forall_congr'
  intro n
  rw [intrinsicInfiniteDirectedPathMap_vertex]
  exact intrinsicBetweenCutRightmostOutgoingAt_map_iff I S (T.vertex n) (T.edge n).val

private theorem intrinsicBetween_dart_xor (d : A.E × Bool) (reverse : Bool) :
    intrinsicFutureDartEquiv I (d.1, Bool.xor d.2 reverse) =
      ((intrinsicFutureDartEquiv I d).1,
        Bool.xor (intrinsicFutureDartEquiv I d).2 reverse) := by
  cases reverse
  · simp only [Bool.xor_false, Prod.mk.eta]
  · simpa only [Bool.xor_true] using intrinsicFutureDartEquiv_flip I d

/-- Helper toward Proposition 3.9: winding-side incidence of ray edges
is preserved and reflected, including endpoint-storage reversals. -/
theorem intrinsicRayTouchesSide_map (P : ℕ → A.E) (F : Set ℂ) (reverse : Bool) :
    intrinsicRayTouchesSide B (fun n => I.edgeEquiv (P n)) (I.h '' F) reverse ↔
      intrinsicRayTouchesSide A P F reverse := by
  have hside (d : A.E × Bool) :
      (∀ s, LeftAtOn F (intrinsicFutureDartArc A
        (d.1, Bool.xor d.2 reverse)) s) ↔
      ∀ s, LeftAtOn (I.h '' F) (intrinsicFutureDartArc B
        ((intrinsicFutureDartEquiv I d).1,
          Bool.xor (intrinsicFutureDartEquiv I d).2 reverse)) s := by
    rw [← intrinsicBetween_dart_xor I]
    exact intrinsicFuture_leftAtOn_map I F _
  constructor
  · rintro ⟨n, d, hd, ht, hs⟩
    obtain ⟨d, rfl⟩ := (intrinsicFutureDartEquiv I).surjective d
    exact ⟨n, d, I.edgeEquiv.injective hd,
      (intrinsicFutureAmbientTail_map I d).mp ht, (hside d).mpr hs⟩
  · rintro ⟨n, d, hd, ht, hs⟩
    exact ⟨n, intrinsicFutureDartEquiv I d, congrArg I.edgeEquiv hd,
      (intrinsicFutureAmbientTail_map I d).mpr ht, (hside d).mp hs⟩

/-- Helper toward Proposition 3.9: the union of both ray traces is
transported by the same plane homeomorphism as the drawing. -/
theorem intrinsicBetween_trace_union_map (P R : ℕ → A.E) :
    intrinsicEdgeRayTrace B (fun n => I.edgeEquiv (P n)) ∪
      intrinsicEdgeRayTrace B (fun n => I.edgeEquiv (R n)) =
        I.h '' (intrinsicEdgeRayTrace A P ∪ intrinsicEdgeRayTrace A R) := by
  rw [intrinsicEdgeRayTrace_map, intrinsicEdgeRayTrace_map, Set.image_union]

/-- Helper toward Proposition 3.9: the selected complementary components
transport as sets, with no horizontal-section assumption on the homeomorphism. -/
theorem intrinsicOpenBetween_map (P R : ℕ → A.E) :
    intrinsicOpenBetween B (fun n => I.edgeEquiv (P n))
      (fun n => I.edgeEquiv (R n)) = I.h '' intrinsicOpenBetween A P R := by
  let T := intrinsicEdgeRayTrace A P ∪ intrinsicEdgeRayTrace A R
  let T' := intrinsicEdgeRayTrace B (fun n => I.edgeEquiv (P n)) ∪
    intrinsicEdgeRayTrace B (fun n => I.edgeEquiv (R n))
  have hT : T' = I.h '' T := intrinsicBetween_trace_union_map I P R
  have hcomp (w : ℂ) (hw : w ∉ T) :
      I.h '' connectedComponentIn Tᶜ w = connectedComponentIn T'ᶜ (I.h w) := by
    rw [I.h.image_connectedComponentIn hw, I.h.image_compl, ← hT]
  ext z
  obtain ⟨z, rfl⟩ := I.h.surjective z
  rw [I.h.injective.mem_set_image]
  constructor
  · rintro ⟨w, hw, hz, hPr, hRl, hnPl, hnRr⟩
    obtain ⟨w, rfl⟩ := I.h.surjective w
    have hw' : w ∉ T := by
      change I.h w ∉ T' at hw
      rwa [hT, I.h.injective.mem_set_image] at hw
    change I.h z ∈ connectedComponentIn T'ᶜ (I.h w) at hz
    rw [← hcomp w hw'] at hz hPr hRl hnPl hnRr
    exact ⟨w, hw', I.h.injective.mem_set_image.mp hz,
      (intrinsicRayTouchesSide_map I P _ true).mp hPr,
      (intrinsicRayTouchesSide_map I R _ false).mp hRl,
      fun h => hnPl ((intrinsicRayTouchesSide_map I P _ false).mpr h),
      fun h => hnRr ((intrinsicRayTouchesSide_map I R _ true).mpr h)⟩
  · rintro ⟨w, hw, hz, hPr, hRl, hnPl, hnRr⟩
    refine ⟨I.h w, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change I.h w ∉ T'
      rwa [hT, I.h.injective.mem_set_image]
    · change I.h z ∈ connectedComponentIn T'ᶜ (I.h w)
      rw [← hcomp w hw]
      exact ⟨z, hz, rfl⟩
    · rw [← hcomp w hw]
      exact (intrinsicRayTouchesSide_map I P _ true).mpr hPr
    · rw [← hcomp w hw]
      exact (intrinsicRayTouchesSide_map I R _ false).mpr hRl
    · rw [← hcomp w hw]
      exact fun h => hnPl ((intrinsicRayTouchesSide_map I P _ false).mp h)
    · rw [← hcomp w hw]
      exact fun h => hnRr ((intrinsicRayTouchesSide_map I R _ true).mp h)

/-- Helper toward Proposition 3.9: orientation-preserving geometric
isomorphisms carry the entire native region onto the native image-ray region. -/
theorem nativeBetween_map (P R : ℕ → A.E) :
    I.h '' nativeBetween A P R =
      nativeBetween B (fun n => I.edgeEquiv (P n))
        (fun n => I.edgeEquiv (R n)) := by
  rw [nativeBetween, nativeBetween, I.h.image_closure, Set.image_union,
    intrinsicOpenBetween_map, intrinsicBetween_trace_union_map]

end Transport

/-- Helper toward Proposition 3.9: literal universal leftmostness in
the native region, relative to a reference ray from the same cut vertex.
Attributing that reference as the cut's rightmost ray is a separate task. -/
@[expose] def IntrinsicLeftmostInRegion (A : D39DomainRootedMap.{0})
    (S : IntrinsicBusemannCut A) (v : A.V) (longest : Bool)
    (P : IntrinsicInfiniteXDPGeodesic A S v longest)
    (R : IntrinsicInfiniteDirectedPath A S v) : Prop :=
  ∀ Q : IntrinsicInfiniteXDPGeodesic A S v longest,
    intrinsicEdgeRayTrace A (fun n => (Q.val.edge n).val) ⊆
      nativeBetween A (fun n => (P.val.edge n).val) (fun n => (R.edge n).val)

/-- Helper toward Proposition 3.9: universal native-region leftmostness
transports with the cut, its reference ray, and every competing geodesic. -/
theorem intrinsicLeftmostInRegion_map_iff {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)
    (S : IntrinsicBusemannCut A) (v : A.V) (longest : Bool)
    (P : IntrinsicInfiniteXDPGeodesic A S v longest)
    (R : IntrinsicInfiniteDirectedPath A S v) :
    IntrinsicLeftmostInRegion B (intrinsicGeodesicMapCut I S) (I.vertexEquiv v)
      longest (intrinsicInfiniteXDPGeodesicEquiv I S v longest P)
      (intrinsicInfiniteDirectedPathMap I R) ↔
    IntrinsicLeftmostInRegion A S v longest P R := by
  let E := intrinsicInfiniteXDPGeodesicEquiv I S v longest
  have htest (Q : IntrinsicInfiniteXDPGeodesic A S v longest) :
      intrinsicEdgeRayTrace B (fun n => ((E Q).val.edge n).val) ⊆
        nativeBetween B (fun n => ((E P).val.edge n).val)
          (fun n => ((intrinsicInfiniteDirectedPathMap I R).edge n).val) ↔
      intrinsicEdgeRayTrace A (fun n => (Q.val.edge n).val) ⊆
        nativeBetween A (fun n => (P.val.edge n).val) (fun n => (R.edge n).val) := by
    change intrinsicEdgeRayTrace B (fun n => I.edgeEquiv (Q.val.edge n).val) ⊆
      nativeBetween B (fun n => I.edgeEquiv (P.val.edge n).val)
        (fun n => I.edgeEquiv (R.edge n).val) ↔ _
    rw [← nativeBetween_map I]
    exact intrinsicEdgeRayTrace_subset_image_iff I _ _
  constructor
  · intro h Q
    exact (htest Q).mp (h (E Q))
  · intro h Q
    obtain ⟨Q, rfl⟩ := E.surjective Q
    exact (htest Q).mpr (h Q)

/-- Helper toward Proposition 3.9: intrinsic leftmostness requires a
cut-rightmost reference ray and containment of every intrinsic XDP competitor
in the native region. This is a predicate, without a choice of reference ray
or an existence or uniqueness assertion. -/
@[expose] def IsIntrinsicLeftmostXDPGeodesic (A : D39DomainRootedMap.{0})
    (S : IntrinsicBusemannCut A) (v : A.V) (longest : Bool)
    (P : IntrinsicInfiniteXDPGeodesic A S v longest) : Prop :=
  ∃ R : IntrinsicInfiniteDirectedPath A S v,
    RightmostInCut A S v R ∧ IntrinsicLeftmostInRegion A S v longest P R

/-- Helper toward Proposition 3.9: literal intrinsic leftmostness is
preserved and reflected, transporting both its rightmost reference and all
its geodesic competitors. -/
theorem isIntrinsicLeftmostXDPGeodesic_map_iff {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)
    (S : IntrinsicBusemannCut A) (v : A.V) (longest : Bool)
    (P : IntrinsicInfiniteXDPGeodesic A S v longest) :
    IsIntrinsicLeftmostXDPGeodesic B (intrinsicGeodesicMapCut I S) (I.vertexEquiv v)
      longest (intrinsicInfiniteXDPGeodesicEquiv I S v longest P) ↔
    IsIntrinsicLeftmostXDPGeodesic A S v longest P := by
  constructor
  · rintro ⟨R, hr, hl⟩
    obtain ⟨R, rfl⟩ := (intrinsicInfiniteDirectedPathEquiv I S v).surjective R
    exact ⟨R, (rightmostInCut_map_iff I R).mp hr,
      (intrinsicLeftmostInRegion_map_iff I S v longest P R).mp hl⟩
  · rintro ⟨R, hr, hl⟩
    exact ⟨intrinsicInfiniteDirectedPathMap I R, (rightmostInCut_map_iff I R).mpr hr,
      (intrinsicLeftmostInRegion_map_iff I S v longest P R).mpr hl⟩

/- REMAINING FULL-BINDER SPECIFICATIONS. These are comments, not declarations,
assumptions, or discharged results. The new geometric definitions require

All three formulas were successfully elaborated in a temporary statement
probe, subsequently removed. Their notation also uses the following opens:
DirectedDistances.PaperProofs.Section5, DirectedDistances.PaperProofs.Section7,
DirectedDistances.Paper.Section4, DirectedDistances.RandomWalk, MeasureTheory,
and Filter, with the Classical scope.

(1) Native-region characterization, with exactly the source binders:

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
  (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h (k - 1))))
let D := m0CutData W H h hLL
let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
∀ (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root)
  (longest : Bool) (k : ℤ)
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (T : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
  (_ : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
  (_ : T.edge = R.edge),
nativeBetween A
  (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n)))
  (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (T.edge n))) =
  I.h '' closedBetween
    (pathTrace G (fun n => wholePlaneDartι W 0 (P.codePath.edge n, false)))
    (pathTrace G (fun n => wholePlaneDartι W 0 (T.edge n, false))).

The unresolved deterministic step is to classify complementary components
of the two source ray traces by the four winding-incidence tests in
intrinsicOpenBetween, then identify their closure and boundary traces with
the vertical fibers in mem_closedBetween_iff. The known source traces and
the homeomorphism transport theorem alone do not prove that step.

(2) Cut-rightmost attribution of the code reference, not ambient rightmostness:

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
  (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h (k - 1))))
let D := m0CutData W H h hLL
let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
∀ (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root)
  (k : ℤ)
  (T : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
  (_ : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
  (_ : T.edge = R.edge),
RightmostInCut A (intrinsicBusemannImageCut W H G hp D A I)
  (I.vertexEquiv (D.x k))
  (intrinsicImageInfinitePathEquiv W H G hp D A I (D.x k)
    (m0CutPathOfPresentPath W H h hLL k T)).

The missing proof compares the run selector's inverse-rotation scan with
the geometric star restricted to D.edges, retaining the geometric edges
tagged D.missing as nonoriented stopping incidences. The ambient selector
transport theorem does not establish this restricted-star attribution.

(3) Common-event intrinsic leftmost uniqueness, in both modes, sharing

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
    ∀ x : XDP,
    (if x = XDP.ldp then
      IsIntrinsicBusemannLDP A (intrinsicBusemannImageCut W H G hp D A I)
        (fun k => I.vertexEquiv (D.x k)) (identifiedLDPBusemann W)
    else IsIntrinsicBusemannSDP A (intrinsicBusemannImageCut W H G hp D A I)
        (fun k => I.vertexEquiv (D.x k)) (identifiedSDPBusemann W)) ∧
    let P := fun j => intrinsicGeodesicOfCode W H h hLL G hp A I ((s x).P j)
    (∀ k k' : ℤ, ∃ a b : ℕ, IntrinsicEdgeTailsCoalesce (P k).val (P k').val a b) ∧
    (∀ k : ℤ,
      let X := if x = XDP.ldp then identifiedLDPBusemann W else identifiedSDPBusemann W
      IntrinsicLeastEdgeCoalescence (P (k - 1)).val (P k).val
        ((s x).thetaMinus k) ((s x).theta k) ∧
      uibotGeomCoalescenceOffsets z x k = ((s x).thetaMinus k, (s x).theta k) ∧
      uibotCodeCoalescenceOffsets W x k = ((s x).thetaMinus k, (s x).theta k) ∧
      (uibotGeomSideSliceObservables z x k).2 =
        some (geometricSideClass (m0CutGeodesicSlice (hp := (s x).hp) (s x).P k
          ((s x).thetaMinus k) ((s x).theta k) ((s x).least k))) ∧
      X k - X (k - 1) = (((s x).theta k : ℕ) : ℤ) -
        (((s x).thetaMinus k : ℕ) : ℤ)) ∧
    ∀ k : ℤ,
      let S := intrinsicBusemannImageCut W H G hp D A I
      let v := I.vertexEquiv (D.x k)
      let longest := if x = XDP.ldp then true else false
      ∃ T : IntrinsicInfiniteDirectedPath A S v,
        RightmostInCut A S v T ∧
        ∀ Q : IntrinsicInfiniteXDPGeodesic A S v longest,
          IntrinsicLeftmostInRegion A S v longest Q T ↔ Q = P k.

Neither (1), (2), nor (3) is assumed by any declaration in this file.
No numbered paper result or qualifier removal is claimed. -/

end DirectedDistances.PaperProofs.Section3
end
