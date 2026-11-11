/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicGeodesicIdentification
public import DirectedDistances.PaperProofs.Section5.GeoSliceBetweenFidelity
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ForgetMarks
import all DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ClassValued

/-! # Geometric sides and finite enclosures on representatives

Helpers toward Proposition 3.9, using Lemmas 5.5 and 5.6
specified explicitly; identifying an image cut with Definition 1.3 remains
separate. No intrinsic-object qualification is removed here. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4 DirectedDistances.RandomWalk MeasureTheory Filter
open scoped Topology Classical

/-- Helper toward Proposition 3.9: the component of a slit cut region -/
@[expose] def intrinsicGeodesicLeftOpen (A : D39DomainRootedMap.{0})
    (R : Set ℂ) (previous : A.V) (e : ℕ → A.E) : Set ℂ :=
  connectedComponentIn (R \ intrinsicEdgeRayTrace A e) (A.map.pos previous)

/-- Helper toward Proposition 3.9: closed sides relative to the cut,
including the whole geometric ray on either side in the source setting. -/
@[expose] def intrinsicGeodesicSideRegion (A : D39DomainRootedMap.{0})
    (R : Set ℂ) (previous : A.V) (e : ℕ → A.E) (s : ThinMapSide) : Set ℂ :=
  match s with
  | .left => closure (intrinsicGeodesicLeftOpen A R previous e) ∩ R
  | .right => R \ intrinsicGeodesicLeftOpen A R previous e

/-- Helper toward Proposition 3.9: open face sides relative to the cut;
the right face region excludes the closure of the left component. -/
@[expose] def intrinsicGeodesicSideOpenRegion (A : D39DomainRootedMap.{0})
    (R : Set ℂ) (previous : A.V) (e : ℕ → A.E) (s : ThinMapSide) : Set ℂ :=
  match s with
  | .left => intrinsicGeodesicLeftOpen A R previous e
  | .right => R \ closure (intrinsicGeodesicLeftOpen A R previous e)

/-- Helper toward Proposition 3.9: actual vertex, edge and face carriers
in the representative. Missing status is independent of geometric retention. -/
structure IntrinsicGeometricSubmap (A : D39DomainRootedMap.{0}) where
  /-- Helper toward Proposition 3.9: retained vertices. -/
  vertices : Set A.V
  /-- Helper toward Proposition 3.9: retained individual geometric edges. -/
  edges : Set A.E
  /-- Helper toward Proposition 3.9: retained ambient open faces. -/
  faces : Set A.map.toPlaneGraphDrawing.Face
  /-- Helper toward Proposition 3.9: additional cut missing tags. -/
  missing : A.E → Prop

/-- Helper toward Proposition 3.9: geometric side submap, restricted to
the specified cut carriers, with faces tested on their entire open regions. -/
@[expose] def intrinsicGeodesicSide (A : D39DomainRootedMap.{0})
    (S : IntrinsicBusemannCut A) (R : Set ℂ) (previous : A.V)
    (e : ℕ → A.E) (s : ThinMapSide) : IntrinsicGeometricSubmap A where
  vertices := {v | v ∈ S.vertices ∧
    A.map.pos v ∈ intrinsicGeodesicSideRegion A R previous e s}
  edges := {f | f ∈ S.edges ∧
    Set.range (A.map.arc f) ⊆ intrinsicGeodesicSideRegion A R previous e s}
  faces := {F | F.val ⊆ intrinsicGeodesicSideOpenRegion A R previous e s}
  missing := S.missing

/-- Helper toward Proposition 3.9: finite ray segment, including the
initial vertex even when its length is zero. -/
@[expose] def intrinsicGeodesicSegmentTrace (A : D39DomainRootedMap.{0})
    (v : A.V) (e : ℕ → A.E) (n : ℕ) : Set ℂ :=
  {A.map.pos v} ∪ ⋃ i : Fin n, Set.range (A.map.arc (e i.val))

/-- Helper toward Proposition 3.9: finite enclosing trace with the
geometric boundary edge, even if that edge is missing in the directed cut. -/
@[expose] def intrinsicGeodesicSliceBoundary (A : D39DomainRootedMap.{0})
    (v w : A.V) (p q : ℕ → A.E) (a b : ℕ) (boundary : A.E) : Set ℂ :=
  (intrinsicGeodesicSegmentTrace A v p a ∪
    intrinsicGeodesicSegmentTrace A w q b) ∪ Set.range (A.map.arc boundary)

/-- Helper toward Proposition 3.9: literal finite-segment face enclosure.
The face lies in the cut and in a bounded complementary component of the
finite enclosing trace. No stored face-successor relation enters this test. -/
@[expose] def intrinsicFaceBetweenSegments (A : D39DomainRootedMap.{0})
    (R B : Set ℂ) (F : A.map.toPlaneGraphDrawing.Face) : Prop :=
  F.val ⊆ R ∧ ∃ z ∈ F.val,
    F.val ⊆ connectedComponentIn Bᶜ z ∧
      Bornology.IsBounded (connectedComponentIn Bᶜ z)

/-- Helper toward Proposition 3.9: a finite slice in the representative.
The vertex and edge streams are the actual geodesic streams. The strict
tails are removed only from the geometric vertex and edge overlap; faces
are specified independently by finite enclosure. The boundary edge is used
geometrically even when the cut has deleted its orientation. -/
@[expose] def intrinsicGeodesicSlice (A : D39DomainRootedMap.{0})
    (S : IntrinsicBusemannCut A) (R : Set ℂ) (x : ℤ → A.V)
    (v : ℤ → ℕ → A.V) (p : ℤ → ℕ → A.E)
    (k : ℤ) (a b : ℕ) (boundary : A.E) : IntrinsicGeometricSubmap A where
  vertices :=
    ((intrinsicGeodesicSide A S R (x (k - 1 - 1)) (p (k - 1)) .right).vertices ∩
      (intrinsicGeodesicSide A S R (x (k - 1)) (p k) .left).vertices) \
      ({w | ∃ n, a < n ∧ w = v (k - 1) n} ∪ {w | ∃ n, b < n ∧ w = v k n})
  edges :=
    ((intrinsicGeodesicSide A S R (x (k - 1 - 1)) (p (k - 1)) .right).edges ∩
      (intrinsicGeodesicSide A S R (x (k - 1)) (p k) .left).edges) \
      (Set.range (fun n => p (k - 1) (a + n)) ∪ Set.range (fun n => p k (b + n)))
  faces := {F | intrinsicFaceBetweenSegments A R
    (intrinsicGeodesicSliceBoundary A (v (k - 1) 0) (v k 0)
      (p (k - 1)) (p k) a b boundary) F}
  missing := S.missing

/-- Helper toward Proposition 3.9: a strict vertex tail transports
without losing its endpoint convention. -/
theorem intrinsicSide_image_strictTail {α β : Type*}
    (f : α → β) (v : ℕ → α) (a : ℕ) :
    f '' {w | ∃ n, a < n ∧ w = v n} = {w | ∃ n, a < n ∧ w = f (v n)} := by
  ext w
  constructor
  · rintro ⟨u, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨v n, ⟨n, hn, rfl⟩, rfl⟩

section Transport
variable {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)

/-- Helper toward Proposition 3.9: relative components transport even
when their basepoint is outside the specified region. -/
theorem intrinsicSide_component_map (C : Set ℂ) (z : ℂ) :
    connectedComponentIn (I.h '' C) (I.h z) =
      I.h '' connectedComponentIn C z := by
  by_cases hz : z ∈ C
  · exact (I.h.image_connectedComponentIn hz).symm
  · have hz' : I.h z ∉ I.h '' C := by
      rwa [I.h.injective.mem_set_image]
    rw [connectedComponentIn_eq_empty hz, connectedComponentIn_eq_empty hz',
      Set.image_empty]

/-- Helper toward Proposition 3.9: slit-component transport in the
representative drawing, with its own ray and preceding boundary vertex. -/
theorem intrinsicGeodesicLeftOpen_map (R : Set ℂ) (v : A.V) (e : ℕ → A.E) :
    intrinsicGeodesicLeftOpen B (I.h '' R) (I.vertexEquiv v)
      (fun n => I.edgeEquiv (e n)) = I.h '' intrinsicGeodesicLeftOpen A R v e := by
  unfold intrinsicGeodesicLeftOpen
  rw [intrinsicEdgeRayTrace_map, ← I.pos_map,
    ← Set.image_sdiff I.h.injective, intrinsicSide_component_map]

/-- Helper toward Proposition 3.9: both closed side regions transport,
including closures and their restriction to the ambient cut region. -/
theorem intrinsicGeodesicSideRegion_map
    (R : Set ℂ) (v : A.V) (e : ℕ → A.E) (s : ThinMapSide) :
    intrinsicGeodesicSideRegion B (I.h '' R) (I.vertexEquiv v)
      (fun n => I.edgeEquiv (e n)) s =
        I.h '' intrinsicGeodesicSideRegion A R v e s := by
  cases s with
  | left =>
    simp only [intrinsicGeodesicSideRegion, intrinsicGeodesicLeftOpen_map,
      I.h.image_closure, Set.image_inter I.h.injective]
  | right =>
    simp only [intrinsicGeodesicSideRegion, intrinsicGeodesicLeftOpen_map,
      Set.image_sdiff I.h.injective]

/-- Helper toward Proposition 3.9: both face-side regions transport. -/
theorem intrinsicGeodesicSideOpenRegion_map
    (R : Set ℂ) (v : A.V) (e : ℕ → A.E) (s : ThinMapSide) :
    intrinsicGeodesicSideOpenRegion B (I.h '' R) (I.vertexEquiv v)
      (fun n => I.edgeEquiv (e n)) s =
        I.h '' intrinsicGeodesicSideOpenRegion A R v e s := by
  cases s with
  | left => exact intrinsicGeodesicLeftOpen_map I R v e
  | right =>
    simp only [intrinsicGeodesicSideOpenRegion, intrinsicGeodesicLeftOpen_map,
      I.h.image_closure, Set.image_sdiff I.h.injective]

/-- Helper toward Proposition 3.9: all three side carriers are carried
onto the target's independently specified geometric carriers. -/
theorem intrinsicGeodesicSide_map (S : IntrinsicBusemannCut A)
    (R : Set ℂ) (v : A.V) (e : ℕ → A.E) (s : ThinMapSide) :
    let L := intrinsicGeodesicSide A S R v e s
    let L' := intrinsicGeodesicSide B (intrinsicGeodesicMapCut I S)
      (I.h '' R) (I.vertexEquiv v) (fun n => I.edgeEquiv (e n)) s
    I.vertexEquiv '' L.vertices = L'.vertices ∧
    I.edgeEquiv '' L.edges = L'.edges ∧
    I.faceEquiv '' L.faces = L'.faces := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · ext w
    obtain ⟨w, rfl⟩ := I.vertexEquiv.surjective w
    simp only [I.vertexEquiv.injective.mem_set_image, intrinsicGeodesicSide,
      intrinsicGeodesicMapCut, Set.mem_ofPred_eq, intrinsicGeodesicSideRegion_map,
      ← I.pos_map, I.h.injective.mem_set_image]
  · ext f
    obtain ⟨f, rfl⟩ := I.edgeEquiv.surjective f
    simp only [I.edgeEquiv.injective.mem_set_image, intrinsicGeodesicSide,
      intrinsicGeodesicMapCut, Set.mem_ofPred_eq, intrinsicGeodesicSideRegion_map,
      ← I.arc_range_map, Set.image_subset_image_iff I.h.injective]
  · ext F
    obtain ⟨F, rfl⟩ := I.faceEquiv.surjective F
    simp only [I.faceEquiv.injective.mem_set_image, intrinsicGeodesicSide,
      Set.mem_ofPred_eq, intrinsicGeodesicSideOpenRegion_map,
      I.faceEquiv_val, Set.image_subset_image_iff I.h.injective]

/-- Helper toward Proposition 3.9: finite segment traces transport with
their endpoints, including a zero-length segment. -/
theorem intrinsicGeodesicSegmentTrace_map
    (v : A.V) (e : ℕ → A.E) (n : ℕ) :
    intrinsicGeodesicSegmentTrace B (I.vertexEquiv v)
      (fun j => I.edgeEquiv (e j)) n =
        I.h '' intrinsicGeodesicSegmentTrace A v e n := by
  unfold intrinsicGeodesicSegmentTrace
  rw [Set.image_union, Set.image_singleton, Set.image_iUnion, I.pos_map]
  congr 1
  congr 1
  funext i
  exact (I.arc_range_map (e i.val)).symm

/-- Helper toward Proposition 3.9: the whole finite enclosing trace
transports, retaining the geometric exterior-boundary edge. -/
theorem intrinsicGeodesicSliceBoundary_map
    (v w : A.V) (p q : ℕ → A.E) (a b : ℕ) (boundary : A.E) :
    intrinsicGeodesicSliceBoundary B (I.vertexEquiv v) (I.vertexEquiv w)
      (fun n => I.edgeEquiv (p n)) (fun n => I.edgeEquiv (q n)) a b
      (I.edgeEquiv boundary) =
        I.h '' intrinsicGeodesicSliceBoundary A v w p q a b boundary := by
  unfold intrinsicGeodesicSliceBoundary
  rw [intrinsicGeodesicSegmentTrace_map, intrinsicGeodesicSegmentTrace_map,
    ← I.arc_range_map, Set.image_union, Set.image_union]

/-- Helper toward Proposition 3.9: boundedness of planar sets is
preserved and reflected by a plane homeomorphism, using compact closures. -/
theorem intrinsicSide_isBounded_image_iff (C : Set ℂ) :
    Bornology.IsBounded (I.h '' C) ↔ Bornology.IsBounded C := by
  constructor
  · intro hc
    have hh := (hc.isCompact_closure.image I.h.symm.continuous).isBounded
    apply hh.subset
    intro z hz
    exact ⟨I.h z, subset_closure ⟨z, hz, rfl⟩, I.h.symm_apply_apply z⟩
  · intro hc
    exact (hc.isCompact_closure.image I.h.continuous).isBounded.subset
      (Set.image_mono subset_closure)

/-- Helper toward Proposition 3.9: finite enclosure is a geometric
property of the actual transported face, preserving its entire component. -/
theorem intrinsicFaceBetweenSegments_map_iff (R C : Set ℂ)
    (F : A.map.toPlaneGraphDrawing.Face) :
    intrinsicFaceBetweenSegments B (I.h '' R) (I.h '' C) (I.faceEquiv F) ↔
      intrinsicFaceBetweenSegments A R C F := by
  unfold intrinsicFaceBetweenSegments
  rw [I.faceEquiv_val, Set.image_subset_image_iff I.h.injective]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨z, hz, hsub, hb⟩
    obtain ⟨z, hz, rfl⟩ := hz
    have he : connectedComponentIn (I.h '' C)ᶜ (I.h z) =
        I.h '' connectedComponentIn Cᶜ z := by
      rw [← I.h.image_compl, intrinsicSide_component_map]
    rw [he] at hsub hb
    exact ⟨z, hz, (Set.image_subset_image_iff I.h.injective).mp hsub,
      (intrinsicSide_isBounded_image_iff I _).mp hb⟩
  · rintro ⟨z, hz, hsub, hb⟩
    refine ⟨I.h z, ⟨z, hz, rfl⟩, ?_, ?_⟩ <;>
      rw [← I.h.image_compl, intrinsicSide_component_map]
    · exact Set.image_mono hsub
    · exact (intrinsicSide_isBounded_image_iff I _).mpr hb

end Transport

section Source
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "hLL" => (fun (k : ℤ) (_ : k ≤ 0) => hp
  (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
local notation "D" => m0CutData W H h hLL
local notation "R" => m0GeodesicAmbientRegion W H h

variable (I : D39GeomRootedMapIsoV2
  (uibotWholePlaneSourceMap W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
  (uibotWholePlaneSourceRoot W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H))
  A.map A.root)

/-- Helper toward Proposition 3.9: every actual glued face has a unique
image face in the representative; this equivalence is on ambient faces. -/
@[expose] def intrinsicSideGluedFaceEquiv : (G).Face ≃ A.map.toPlaneGraphDrawing.Face :=
  ((G).toPlaneGraphDrawingFaceEquiv.symm.trans
    (uibotWholePlaneSourceIso W H G hp).symm.faceEquiv).trans I.faceEquiv

/-- Helper toward Proposition 3.9: the face equivalence transports the
whole complementary region, rather than just a face-successor orbit. -/
theorem intrinsicSideGluedFaceEquiv_val (F : (G).Face) :
    (intrinsicSideGluedFaceEquiv W H h hpast hp A I F).val = I.h '' F.val := by
  change I.h '' (id '' F.val) = _
  rw [Set.image_id]

/-- Helper toward Proposition 3.9: a code geodesic's entire geometric
trace equals the trace of its transported individual edges. -/
theorem intrinsicSide_code_trace {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    intrinsicEdgeRayTrace A
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n))) =
        I.h '' m0GeodesicTrace hpast P := by
  exact (intrinsicEdgeRayTrace_map (A := uibotWholePlaneSourceDomain W H G hp)
    (B := A) I (fun n => wholePlaneEdgeι W 0 (P.codePath.edge n))).trans
      (congrArg (fun C : Set ℂ => I.h '' C)
        (intrinsicGeodesicSource_trace W H G hp
          (fun n => wholePlaneEdgeι W 0 (P.codePath.edge n))))

/-- Helper toward Proposition 3.9: the source left component is the
component defined directly in the image cut's drawing. -/
theorem intrinsicSide_code_leftOpen {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    intrinsicGeodesicLeftOpen A (I.h '' R) (I.vertexEquiv ((D).x (k - 1)))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n))) =
        I.h '' m0GeodesicLeftOpen hpast P := by
  unfold intrinsicGeodesicLeftOpen
  rw [intrinsicSide_code_trace, ← I.pos_map,
    ← Set.image_sdiff I.h.injective,
    intrinsicSide_component_map (A := uibotWholePlaneSourceDomain W H G hp) I]
  rfl

/-- Helper toward Proposition 3.9: code closed-side regions agree with
the intrinsic relative-component construction on the representative. -/
theorem intrinsicSide_code_region {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) :
    intrinsicGeodesicSideRegion A (I.h '' R) (I.vertexEquiv ((D).x (k - 1)))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n))) s =
        I.h '' m0GeodesicSideRegion hpast P s := by
  cases s with
  | left =>
    simp only [intrinsicGeodesicSideRegion, m0GeodesicSideRegion,
      intrinsicSide_code_leftOpen, I.h.image_closure, Set.image_inter I.h.injective]
  | right =>
    simp only [intrinsicGeodesicSideRegion, m0GeodesicSideRegion,
      intrinsicSide_code_leftOpen, Set.image_sdiff I.h.injective]

/-- Helper toward Proposition 3.9: code open face sides agree with the
representative's relative-component sides. -/
theorem intrinsicSide_code_openRegion {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) :
    intrinsicGeodesicSideOpenRegion A (I.h '' R) (I.vertexEquiv ((D).x (k - 1)))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n))) s =
        I.h '' m0GeodesicSideOpenRegion hpast P s := by
  cases s with
  | left => exact intrinsicSide_code_leftOpen W H h hpast hp A I P
  | right =>
    simp only [intrinsicGeodesicSideOpenRegion, m0GeodesicSideOpenRegion,
      intrinsicSide_code_leftOpen, I.h.image_closure, Set.image_sdiff I.h.injective]

/-- Helper toward Proposition 3.9: all code side vertices, with no
boundary deletion, are exactly the intrinsic side's vertices. -/
theorem intrinsicSide_code_vertices {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) :
    (fun v => I.vertexEquiv (wholePlaneVertexι W 0 v)) ''
      (m0GeodesicSide hpast P s).vertices =
    (intrinsicGeodesicSide A (intrinsicBusemannImageCut W H G hp D A I)
      (I.h '' R) (I.vertexEquiv ((D).x (k - 1)))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n))) s).vertices := by
  have hV := m0Cut_leftVertices_eq_runZero W H h (D).seam
    (m0Cut_seamEdge_iff W H h hLL)
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨wholePlaneVertexι W 0 u, hV ▸ ⟨u, rfl⟩, rfl⟩, ?_⟩
    rw [intrinsicSide_code_region, ← I.pos_map, I.h.injective.mem_set_image]
    exact hu
  · rintro ⟨⟨u, hu, rfl⟩, hv⟩
    rw [hV] at hu
    obtain ⟨u, rfl⟩ := hu
    refine ⟨u, ?_, rfl⟩
    rw [intrinsicSide_code_region, ← I.pos_map, I.h.injective.mem_set_image] at hv
    exact hv

/-- Helper toward Proposition 3.9: all code side geometric edges are
exactly the intrinsic side's edges, independently of their missing tags. -/
theorem intrinsicSide_code_edges {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) :
    (fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)) ''
      (m0GeodesicSide hpast P s).edges =
    (intrinsicGeodesicSide A (intrinsicBusemannImageCut W H G hp D A I)
      (I.h '' R) (I.vertexEquiv ((D).x (k - 1)))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n))) s).edges := by
  have hE := (D).edges_eq h hLL
  have hr (e : ℕ) : Set.range ((uibotWholePlaneSourceMap W H G hp).arc
      (wholePlaneEdgeι W 0 e)) =
      ((G).arc (wholePlaneDartι W 0 (e, false))).image :=
    (G).toPlaneGraphDrawing_arc_range _
  ext e
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨wholePlaneEdgeι W 0 u, hE ▸ ⟨u, rfl⟩, rfl⟩, ?_⟩
    rw [intrinsicSide_code_region, ← I.arc_range_map, hr,
      Set.image_subset_image_iff I.h.injective]
    exact hu
  · rintro ⟨⟨u, hu, rfl⟩, he⟩
    rw [hE] at hu
    obtain ⟨u, rfl⟩ := hu
    refine ⟨u, ?_, rfl⟩
    rw [intrinsicSide_code_region, ← I.arc_range_map, hr,
      Set.image_subset_image_iff I.h.injective] at he
    exact he

/-- Helper toward Proposition 3.9: the source face collection on either
open side is exactly the face collection of the intrinsic image side. -/
theorem intrinsicSide_code_faces {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) :
    intrinsicSideGluedFaceEquiv W H h hpast hp A I ''
      {F : (G).Face | F.val ⊆ m0GeodesicSideOpenRegion hpast P s} =
    (intrinsicGeodesicSide A (intrinsicBusemannImageCut W H G hp D A I)
      (I.h '' R) (I.vertexEquiv ((D).x (k - 1)))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n))) s).faces := by
  ext F
  obtain ⟨F, rfl⟩ := (intrinsicSideGluedFaceEquiv W H h hpast hp A I).surjective F
  rw [(intrinsicSideGluedFaceEquiv W H h hpast hp A I).injective.mem_set_image]
  change (F.val ⊆ _) ↔
    ((intrinsicSideGluedFaceEquiv W H h hpast hp A I F).val ⊆ _)
  rw [intrinsicSideGluedFaceEquiv_val, intrinsicSide_code_openRegion,
    Set.image_subset_image_iff I.h.injective]

/-- Helper toward Proposition 3.9: finite code segments, including
their initial vertices at zero offset, are exactly the native image segments. -/
theorem intrinsicSide_code_segment {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (n : ℕ) :
    intrinsicGeodesicSegmentTrace A
      (I.vertexEquiv (wholePlaneVertexι W 0 (P.codePath.initial 0).1.id))
      (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge j))) n =
        I.h '' m0CutGeodesicSegmentTrace hpast P n := by
  refine (intrinsicGeodesicSegmentTrace_map
    (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I
    (wholePlaneVertexι W 0 (P.codePath.initial 0).1.id)
    (fun j => wholePlaneEdgeι W 0 (P.codePath.edge j)) n).trans ?_
  apply congrArg (fun C : Set ℂ => I.h '' C)
  unfold intrinsicGeodesicSegmentTrace m0CutGeodesicSegmentTrace
  congr 1
  congr 1
  funext i
  exact (G).toPlaneGraphDrawing_arc_range _

/-- Helper toward Proposition 3.9: the native finite enclosing trace
is the source enclosing trace's image, including a missing boundary edge. -/
theorem intrinsicSide_code_boundary {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) :
    intrinsicGeodesicSliceBoundary A
      (I.vertexEquiv (wholePlaneVertexι W 0 ((P (k - 1)).codePath.initial 0).1.id))
      (I.vertexEquiv (wholePlaneVertexι W 0 ((P k).codePath.initial 0).1.id))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 ((P (k - 1)).codePath.edge n)))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 ((P k).codePath.edge n))) a b
      (I.edgeEquiv (wholePlaneEdgeι W 0
        (boundaryOuterEdge (shiftedStream W 0) h (k - 1)))) =
      I.h '' geodesicSegmentsEnclosingTrace hpast P k a b := by
  rw [geodesicSegmentsEnclosingTrace_eq_boundaryTrace]
  unfold intrinsicGeodesicSliceBoundary m0CutGeodesicSliceBoundaryTrace
  rw [intrinsicSide_code_segment, intrinsicSide_code_segment,
    ← I.arc_range_map, Set.image_union, Set.image_union]
  have hr : Set.range ((uibotWholePlaneSourceMap W H G hp).arc
      (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h (k - 1)))) =
      ((G).arc (wholePlaneDartι W 0
        (boundaryOuterEdge (shiftedStream W 0) h (k - 1), false))).image :=
    (G).toPlaneGraphDrawing_arc_range _
  rw [hr]

/-- Helper toward Proposition 3.9: the vertex stream used in the native
slice constructor is the vertex stream of the transported edge geodesic. -/
theorem intrinsicSide_code_geodesic_vertex {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (n : ℕ) :
    (intrinsicGeodesicOfCode W H h hLL G hp A I P).val.vertex n =
      I.vertexEquiv (wholePlaneVertexι W 0 (P.codePath.initial n).1.id) := by
  exact (intrinsicInfiniteDirectedPathMap_vertex
    (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I
    (intrinsicSourceInfinitePathEquiv W H G hp D ((D).x k)
      (m0CutPathOfPresentPath W H h hLL k P.codePath)) n).trans
    (congrArg I.vertexEquiv
      ((intrinsicSourceInfinitePathEquiv_vertex W H G hp D ((D).x k)
        (m0CutPathOfPresentPath W H h hLL k P.codePath) n).trans
          (m0CutPathOfPresentPath_vertex W H h hLL k P.codePath n)))

/-- Helper toward Proposition 3.9: source finite-segment enclosure
identifies the actual image face with a bounded component in A's drawing. -/
theorem intrinsicSide_code_faceBetween_iff {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (F : (G).Face) :
    intrinsicFaceBetweenSegments A (I.h '' R)
      (I.h '' geodesicSegmentsEnclosingTrace hpast P k a b)
      (intrinsicSideGluedFaceEquiv W H h hpast hp A I F) ↔
      faceLiesBetweenSegments hpast P k a b hab F := by
  unfold intrinsicFaceBetweenSegments faceLiesBetweenSegments
  rw [intrinsicSideGluedFaceEquiv_val, Set.image_subset_image_iff I.h.injective]
  apply and_congr_right
  intro _
  have hc (z : ℂ) :
      connectedComponentIn (I.h '' geodesicSegmentsEnclosingTrace hpast P k a b)ᶜ
        (I.h z) = I.h '' connectedComponentIn
          (geodesicSegmentsEnclosingTrace hpast P k a b)ᶜ z := by
    rw [← I.h.image_compl,
      intrinsicSide_component_map (A := uibotWholePlaneSourceDomain W H G hp) I]
  constructor
  · rintro ⟨z, ⟨z, hz, rfl⟩, hsub, hb⟩
    rw [hc] at hsub hb
    exact ⟨z, hz, (Set.image_subset_image_iff I.h.injective).mp hsub,
      (intrinsicSide_isBounded_image_iff
        (A := uibotWholePlaneSourceDomain W H G hp) I _).mp hb⟩
  · rintro ⟨z, hz, hsub, hb⟩
    refine ⟨I.h z, ⟨z, hz, rfl⟩, ?_, ?_⟩ <;> rw [hc]
    · exact Set.image_mono hsub
    · exact (intrinsicSide_isBounded_image_iff
        (A := uibotWholePlaneSourceDomain W H G hp) I _).mpr hb

/-- Helper toward Proposition 3.9: the stored slice face collection
equals actual finite-segment enclosure in the representative. Leftmostness
is consumed from the existing code witness, rather than assumed intrinsically. -/
theorem intrinsicSide_code_slice_faces {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hpast hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    intrinsicSideGluedFaceEquiv W H h hpast hp A I ''
      {F : (G).Face | m0CutGeodesicSliceRepresentsFace hpast P k a b hab F} =
      {F : A.map.toPlaneGraphDrawing.Face | intrinsicFaceBetweenSegments A
        (I.h '' R) (I.h '' geodesicSegmentsEnclosingTrace hpast P k a b) F} := by
  ext F
  obtain ⟨F, rfl⟩ := (intrinsicSideGluedFaceEquiv W H h hpast hp A I).surjective F
  rw [(intrinsicSideGluedFaceEquiv W H h hpast hp A I).injective.mem_set_image]
  exact (m0CutGeodesicSlice_representsFace_iff_liesBetweenSegments
    hpast P T hleft k a b hab F).trans
      (intrinsicSide_code_faceBetween_iff W H h hpast hp A I P k a b hab F).symm

/-- Helper toward Proposition 3.9: evaluate the native slice constructor
on the actual transported code geodesic vertices and individual edges. -/
@[expose] def intrinsicGeodesicSliceOfCode {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) : IntrinsicGeometricSubmap A :=
  intrinsicGeodesicSlice A (intrinsicBusemannImageCut W H G hp D A I)
    (I.h '' R) (fun j => I.vertexEquiv ((D).x j))
    (fun j n => I.vertexEquiv (wholePlaneVertexι W 0 ((P j).codePath.initial n).1.id))
    (fun j n => I.edgeEquiv (wholePlaneEdgeι W 0 ((P j).codePath.edge n))) k a b
    (I.edgeEquiv (wholePlaneEdgeι W 0
      (boundaryOuterEdge (shiftedStream W 0) h (k - 1))))

/-- Helper toward Proposition 3.9: the native slice evaluated on code
images is exactly the native constructor on the intrinsic geodesics' own
vertex and edge streams, with no separate choice of vertices. -/
theorem intrinsicGeodesicSliceOfCode_eq_intrinsic {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) :
    let Q := fun j => intrinsicGeodesicOfCode W H h hLL G hp A I (P j)
    intrinsicGeodesicSliceOfCode W H h hpast hp A I P k a b =
      intrinsicGeodesicSlice A (intrinsicBusemannImageCut W H G hp D A I)
        (I.h '' R) (fun j => I.vertexEquiv ((D).x j))
        (fun j n => (Q j).val.vertex n) (fun j n => ((Q j).val.edge n).val) k a b
        (I.edgeEquiv (wholePlaneEdgeι W 0
          (boundaryOuterEdge (shiftedStream W 0) h (k - 1)))) := by
  dsimp only
  simp only [intrinsicSide_code_geodesic_vertex, intrinsicGeodesicOfCode_edge]
  rfl

/-- Helper toward Proposition 3.9: additional cut missing tags are
preserved exactly in the native slice, without deleting geometric edges. -/
theorem intrinsicGeodesicSliceOfCode_missing_iff {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ) (e : WholePlaneEdge W) :
    (intrinsicGeodesicSliceOfCode W H h hpast hp A I P k a b).missing (I.edgeEquiv e) ↔
      (D).missing e := by
  change (D).missing (I.edgeEquiv.symm (I.edgeEquiv e)) ↔ _
  rw [Equiv.symm_apply_apply]

/-- Helper toward Proposition 3.9: the full geometric slice carriers
transport to the native finite slice, including its actual enclosed faces. -/
theorem intrinsicGeodesicSliceOfCode_carriers {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hpast hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    let C := m0CutGeodesicSlice (hp := hpast) P k a b hab
    let C' := intrinsicGeodesicSliceOfCode W H h hpast hp A I P k a b
    (fun v => I.vertexEquiv (wholePlaneVertexι W 0 v)) '' C.vertices = C'.vertices ∧
    (fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)) '' C.edges = C'.edges ∧
    intrinsicSideGluedFaceEquiv W H h hpast hp A I ''
      {F : (G).Face | m0CutGeodesicSliceRepresentsFace hpast P k a b hab F} =
        C'.faces := by
  dsimp only
  have hvi : Function.Injective (fun v => I.vertexEquiv (wholePlaneVertexι W 0 v)) :=
    I.vertexEquiv.injective.comp (wholePlaneVertexι_injective W 0)
  have hei : Function.Injective (fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)) :=
    I.edgeEquiv.injective.comp (wholePlaneEdgeι_injective W 0)
  refine ⟨?_, ?_, ?_⟩
  · change _ '' ((_ ∩ _) \ (_ ∪ _)) = _
    have hv1 := intrinsicSide_code_vertices W H h hpast hp A I (P (k - 1)) .right
    have hv2 := intrinsicSide_code_vertices W H h hpast hp A I (P k) .left
    dsimp only [m0GeodesicSide] at hv1 hv2
    rw [Set.image_sdiff hvi, Set.image_inter hvi, Set.image_union,
      intrinsicSide_image_strictTail, intrinsicSide_image_strictTail, hv1, hv2]
    rfl
  · change _ '' ((_ ∩ _) \ (_ ∪ _)) = _
    have he1 := intrinsicSide_code_edges W H h hpast hp A I (P (k - 1)) .right
    have he2 := intrinsicSide_code_edges W H h hpast hp A I (P k) .left
    dsimp only [m0GeodesicSide] at he1 he2
    rw [Set.image_sdiff hei, Set.image_inter hei, Set.image_union,
      ← Set.range_comp', ← Set.range_comp', he1, he2]
    rfl
  · rw [intrinsicSide_code_slice_faces W H h hpast hp A I P T hleft k a b hab]
    unfold intrinsicGeodesicSliceOfCode intrinsicGeodesicSlice
    rw [intrinsicSide_code_boundary]

/-- Helper toward Proposition 3.9: both finite segment vertex sets and
edge sets are retained by the native image slice, with closed endpoints and
strict edge indices exactly as in Lemma 5.6. -/
theorem intrinsicGeodesicSliceOfCode_segments_mem {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hpast hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    let C := intrinsicGeodesicSliceOfCode W H h hpast hp A I P k a b
    (∀ n ≤ a, I.vertexEquiv (wholePlaneVertexι W 0
      ((P (k - 1)).codePath.initial n).1.id) ∈ C.vertices) ∧
    (∀ i < a, I.edgeEquiv (wholePlaneEdgeι W 0
      ((P (k - 1)).codePath.edge i)) ∈ C.edges) ∧
    (∀ n ≤ b, I.vertexEquiv (wholePlaneVertexι W 0
      ((P k).codePath.initial n).1.id) ∈ C.vertices) ∧
    (∀ i < b, I.edgeEquiv (wholePlaneEdgeι W 0
      ((P k).codePath.edge i)) ∈ C.edges) := by
  have hc := intrinsicGeodesicSliceOfCode_carriers W H h hpast hp A I P T hleft k a b hab
  have hm := m0CutGeodesicSlice_boundary_segments_mem P T hleft k a b hab
  dsimp only
  rw [← hc.1, ← hc.2.1]
  exact ⟨fun n hn => ⟨_, hm.1 n hn, rfl⟩,
    fun i hi => ⟨_, hm.2.1 i hi, rfl⟩,
    fun n hn => ⟨_, hm.2.2.1 n hn, rfl⟩,
    fun i hi => ⟨_, hm.2.2.2 i hi, rfl⟩⟩

end Source

/-- Helper toward Proposition 3.9: the upper comparison supplied by
one leftmost family and the lower reference supplied by another combine.
This allows uniqueness to compare witnesses with different reference rays. -/
theorem intrinsicSide_leftmost_change_reference
    {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {hpast : BoundaryHitWitnesses (kmswPastCode W)}
    {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}
    {longest : Bool} {k : ℤ}
    (P Q : M0CutInfiniteGeodesic W H h hLL k longest)
    (T U : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hP : Xdp.CutLeftmostXdp W H h hpast hLL longest k P T)
    (hQ : Xdp.CutLeftmostXdp W H h hpast hLL longest k Q U) :
    Xdp.CutLeftmostXdp W H h hpast hLL longest k P U := by
  intro Z hZ z hz
  exact ⟨(hQ Z hZ hz).1, (hP Z hZ hz).2⟩

/-- Helper toward Proposition 3.9: the existing left and right class
readers use the same actual geodesics as any complete slice witness. The
choice of reference ray is eliminated before applying recorded uniqueness. -/
theorem intrinsicSide_classes_of_sliceWitness
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    lemma55LeftSideClassOption x k W =
        some (geometricSideClass (m0GeodesicSide s.hp (s.P k) .left)) ∧
    lemma55RightSideClassOption2 x k W =
        some (geometricSideClass (m0GeodesicSide s.hp (s.P k) .right)) := by
  have hL : Nonempty (M0LeftSideReaderWitness W (if x = XDP.ldp then true else false)) :=
    ⟨⟨s.H, s.h, s.hLL, s.hp, s.T, s.P, s.hleft, s.huniq⟩⟩
  have hR : Nonempty (M0RightSideObservableWitness W
      (if x = XDP.ldp then true else false)) :=
    ⟨⟨s.H, s.h, s.hLL, s.hp, s.T, s.P, s.hleft, s.huniq⟩⟩
  constructor
  · rw [lemma55LeftSideClassOption_eq_some_of_nonempty x k W hL]
    have he : (Classical.choice hL).P k = s.P k :=
      s.huniq k _ (intrinsicSide_leftmost_change_reference _ _ _ _
        ((Classical.choice hL).hleft k) (s.hleft k))
    rw [he]
  · rw [lemma55RightSideClassOption2_eq_some_of_nonempty x k W hR]
    have he : (Classical.choice hR).P k = s.P k :=
      s.huniq k _ (intrinsicSide_leftmost_change_reference _ _ _ _
        ((Classical.choice hR).hleft k) (s.hleft k))
    rw [he]

/-- Helper toward Proposition 3.9: on one conull event, both modes and
every index have the same side and slice carrier identifications for every
representative and every source isomorphism. The recorded mark-forgetting
reader is applied only after identifying the actual source slice witness.
This does not construct an unmarked class of the native carrier record. -/
theorem intrinsicSideSlice_sample_carriers_ae :
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
        ∀ (x : XDP) (k : ℤ),
        let V := fun v => I.vertexEquiv (wholePlaneVertexι W 0 v)
        let E := fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)
        let F := intrinsicSideGluedFaceEquiv W H h hpast hp A I
        let P := (s x).P
        let a := (s x).thetaMinus k
        let b := (s x).theta k
        let C := m0CutGeodesicSlice (hp := hpast) P k a b ((s x).least k)
        let C' := intrinsicGeodesicSliceOfCode W H h hpast hp A I P k a b
        (∀ t : ThinMapSide,
          let L := intrinsicGeodesicSide A (intrinsicBusemannImageCut W H G hp D A I)
            (I.h '' m0GeodesicAmbientRegion W H h) (I.vertexEquiv (D.x (k - 1)))
            (fun n => E ((P k).codePath.edge n)) t
          V '' (m0GeodesicSide hpast (P k) t).vertices = L.vertices ∧
          E '' (m0GeodesicSide hpast (P k) t).edges = L.edges ∧
          F '' {f : G.Face | f.val ⊆ m0GeodesicSideOpenRegion hpast (P k) t} =
            L.faces) ∧
        V '' C.vertices = C'.vertices ∧ E '' C.edges = C'.edges ∧
        F '' {f : G.Face | m0CutGeodesicSliceRepresentsFace hpast P k a b
          ((s x).least k) f} = C'.faces ∧
        IntrinsicLeastEdgeCoalescence
          (intrinsicGeodesicOfCode W H h hLL G hp A I (P (k - 1))).val
          (intrinsicGeodesicOfCode W H h hLL G hp A I (P k)).val a b ∧
        ∀ default : GeometricSideClass,
          forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.1 =
            forgetMarks (geometricSideClass (m0GeodesicSide hpast (P k) .left)) ∧
          forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.2 =
            forgetMarks (geometricSideClass (m0GeodesicSide hpast (P k) .right)) ∧
          forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).2 =
            forgetMarks (geometricSideClass C) := by
  filter_upwards [intrinsicGeodesic_sample_offsets_ae,
    uibotGeomSideSliceObservables_ae, uibotRecoveredCode_ae] with U hU hfactor hcode
  dsimp only at hU ⊢
  obtain ⟨H, h, hpast, hp, s, hclass, hall⟩ := hU
  refine ⟨H, h, hpast, hp, s, hclass, ?_⟩
  intro A hA
  refine ⟨(hall A hA).1, ?_⟩
  intro I x k
  have hc := intrinsicGeodesicSliceOfCode_carriers _ H h hpast hp A I
    (s x).P (s x).T (s x).hleft k _ _ ((s x).least k)
  refine ⟨?_, hc.1, hc.2.1, hc.2.2, ?_, ?_⟩
  · intro t
    exact ⟨intrinsicSide_code_vertices _ H h hpast hp A I ((s x).P k) t,
      intrinsicSide_code_edges _ H h hpast hp A I ((s x).P k) t,
      intrinsicSide_code_faces _ H h hpast hp A I ((s x).P k) t⟩
  · exact (intrinsicGeodesicOfCode_least_iff _ H h _ _ hp A I
      ((s x).P (k - 1)) ((s x).P k) _ _).mpr ((s x).least k)
  · intro default
    have hf := congrArg (fun f => f x k) hfactor.symm
    change uibotGeomSideSliceObservables _ x k = uibotCodeSideSliceObservables U x k at hf
    have hl := (intrinsicSide_classes_of_sliceWitness (s x) k).1
    have hr := (intrinsicSide_classes_of_sliceWitness (s x) k).2
    have hfl := (congrArg (fun q => q.1.1) hf).trans
      ((congrArg (fun W => lemma55LeftSideClassOption x k W) hcode).symm.trans hl)
    have hfr := (congrArg (fun q => q.1.2) hf).trans
      ((congrArg (fun W => lemma55RightSideClassOption2 x k W) hcode).symm.trans hr)
    have hs := (((hall A hA).2 I x).2.2 k).2.2.2.1
    rw [hfl, hfr, hs]
    simp only [forgetMarksOptionClassValue, Function.comp_apply, lemma55OptionClassValue,
      Option.getD_some, and_self]

/- REMAINING CLASS SPECIFICATION — not a declaration or an assumed premise.

The record `IntrinsicGeometricSubmap` specifies geometric carriers and missing
tags. It does not encode a root, incidence relations, induced rotation or
face succession as an object of `SideSubmapClass`. A native class constructor
must retain all those relations from A's drawing before the class-level
intrinsic qualifier can be discharged. Its intended carrier is

  nativeClass (A : D39DomainRootedMap.{0})
    (C : IntrinsicGeometricSubmap A) (root : A.V) : SideSubmapClass.

It must be defined geometrically, independently of a code or isomorphism;
defining it to equal the right-hand sides below would not solve the task.
After that construction the exact remaining comparison, with full binders, is:

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
  (longest : Bool)
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hpast hLL longest k (P k) (T k))
  (k : ℤ) (a b : ℕ)
  (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b),
  (∀ t : ThinMapSide,
    nativeClass A
      (intrinsicGeodesicSide A (intrinsicBusemannImageCut W H G hp D A I)
        (I.h '' m0GeodesicAmbientRegion W H h) (I.vertexEquiv (D.x (k - 1)))
        (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 ((P k).codePath.edge n))) t)
      (I.vertexEquiv (D.x k)) = sideSubmapClass (m0GeodesicSide hpast (P k) t)) ∧
  nativeClass A (intrinsicGeodesicSliceOfCode W H h hpast hp A I P k a b)
    (I.vertexEquiv (D.x (k - 1))) =
      sideSubmapClass (m0CutGeodesicSlice (hp := hpast) P k a b hab).

The existing common-event theorem gives the simultaneous carrier comparison
and the source class readers after mark forgetting. It does not assert the
missing native class comparison. Intrinsic future-cut characterization and
intrinsic leftmostness remain the read-only s44 file's separate obligations. -/

end DirectedDistances.PaperProofs.Section3
