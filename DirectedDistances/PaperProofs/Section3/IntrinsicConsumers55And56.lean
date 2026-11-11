/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicSideSubmapClass
public import DirectedDistances.PaperProofs.Section3.IntrinsicSideSliceIdentification
public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion4
import all DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ForgetMarks








public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section5
open scoped Classical

section Source
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "S" => uibotWholePlaneSourceDomain W H G hp
local notation "hLL" => (fun (k : ℤ) (_ : k ≤ 0) => hp
  (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
local notation "D" => m0CutData W H h hLL

variable (I : D39GeomRootedMapIsoV2
  (uibotWholePlaneSourceMap W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
  (uibotWholePlaneSourceRoot W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H))
  A.map A.root)

/-- Helper toward Proposition 3.9: the actual run-zero incidence in the
representative, including both storage-orientation changes. -/
@[expose] def intrinsicConsumersCodeDart
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H))
      A.map A.root)
    (d : ℕ × Bool) : A.E × Bool :=
  intrinsicFutureDartEquiv I
    (uibotCut2SourceDartEquiv W H h hpast hp (wholePlaneDartι W 0 d))

/-- Helper toward Proposition 3.9: distinct code incidences remain distinct,
including the two incidences of a missing geometric edge. -/
theorem intrinsicConsumersCodeDart_injective :
    Function.Injective (intrinsicConsumersCodeDart W H h hpast hp A I) := by
  intro d e he
  have he' := (uibotCut2SourceDartEquiv W H h hpast hp).injective
    ((intrinsicFutureDartEquiv I).injective he)
  exact Prod.ext (wholePlaneEdgeι_injective W 0 (congrArg Prod.fst he'))
    (congrArg (fun q : WholePlaneDart W => q.2) he')

/-- Helper toward Proposition 3.9: incidence reversal preserves edge identity. -/
theorem intrinsicConsumersCodeDart_flip (d : ℕ × Bool) :
    intrinsicConsumersCodeDart W H h hpast hp A I (d.1, !d.2) =
      ((intrinsicConsumersCodeDart W H h hpast hp A I d).1,
        !(intrinsicConsumersCodeDart W H h hpast hp A I d).2) := by
  unfold intrinsicConsumersCodeDart
  exact (congrArg (intrinsicFutureDartEquiv (A := S) (B := A) I)
    (uibotCut2SourceDartEquiv_flip W H h hpast hp (wholePlaneDartι W 0 d))).trans
      (intrinsicFutureDartEquiv_flip (A := S) (B := A) I _)

/-- Helper toward Proposition 3.9: the geometric incidence has exactly the
code endpoint, with no collapse of parallel edges. -/
theorem intrinsicConsumersCodeDart_vertex (d : ℕ × Bool) :
    d39GeomRootVertex A.map (intrinsicConsumersCodeDart W H h hpast hp A I d) =
      I.vertexEquiv (wholePlaneVertexι W 0
        (if d.2 then edgeEast (shiftedStream W 0) d.1
         else edgeWest (shiftedStream W 0) d.1)) := by
  unfold intrinsicConsumersCodeDart
  erw [intrinsicFutureDartEquiv_vertex, uibotCut2SourceDartEquiv_vertex,
    wholePlaneDartVertex_ι]
  rfl

/-- Helper toward Proposition 3.9: after the cut's missing tags, orientation
of each image incidence agrees with run-zero presence and direction. -/
theorem intrinsicConsumersCodeDart_oriented (d : ℕ × Bool) :
    (intrinsicFutureAmbientTail A (intrinsicConsumersCodeDart W H h hpast hp A I d) ∧
      ¬ (intrinsicBusemannImageCut W H G hp D A I).missing
        (intrinsicConsumersCodeDart W H h hpast hp A I d).1) ↔
      EdgePresent (shiftedStream W 0) d.1 ∧ d.2 = false := by
  unfold intrinsicConsumersCodeDart
  erw [intrinsicFutureAmbientTail_map, uibotCut2SourceDartEquiv_tail]
  change (wholePlaneDartTail W (wholePlaneDartι W 0 d) ∧
    ¬ (D).missing (I.edgeEquiv.symm (I.edgeEquiv (wholePlaneEdgeι W 0 d.1)))) ↔ _
  rw [Equiv.symm_apply_apply, (D).missing_eq h hLL]
  cases hb : d.2 <;>
    simp only [wholePlaneDartTail, wholePlaneDartι, hb, Bool.false_eq_true,
      Bool.true_eq_false, not_false_eq_true, not_true_eq_false, hp, and_true, true_and, false_and,
      and_false, not_not]

/-- Helper toward Proposition 3.9: every retained geometric incidence has
a unique code incidence once the geometric edge carrier is identified. -/
@[expose] def intrinsicConsumersCodeDarts (K : Set ℕ)
    (C : IntrinsicGeometricSubmap A)
    (he : (fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)) '' K = C.edges) :
    {d : ℕ × Bool // d.1 ∈ K} ≃ {d : A.E × Bool // d.1 ∈ C.edges} :=
  Equiv.ofBijective (fun d => ⟨intrinsicConsumersCodeDart W H h hpast hp A I d.val,
    he ▸ ⟨d.val.1, d.property, rfl⟩⟩) (by
      constructor
      · intro d e hh
        exact Subtype.ext (intrinsicConsumersCodeDart_injective W H h hpast hp A I
          (congrArg Subtype.val hh))
      · intro d
        have hd : d.val.1 ∈ (fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)) '' K :=
          he.symm ▸ d.property
        obtain ⟨e, heK, hed⟩ := hd
        let q := (uibotCut2SourceDartEquiv W H h hpast hp).symm
          ((intrinsicFutureDartEquiv I).symm d.val)
        have hq : q.1 = wholePlaneEdgeι W 0 e := by
          change I.edgeEquiv.symm d.val.1 = wholePlaneEdgeι W 0 e
          rw [← hed, Equiv.symm_apply_apply]
        have hq' : wholePlaneDartι W 0 (e, q.2) = q := Prod.ext hq.symm rfl
        refine ⟨⟨(e, q.2), heK⟩, ?_⟩
        apply Subtype.ext
        change intrinsicFutureDartEquiv I
          (uibotCut2SourceDartEquiv W H h hpast hp (wholePlaneDartι W 0 (e, q.2))) = d.val
        rw [hq', Equiv.apply_symm_apply, Equiv.apply_symm_apply])

/-- Helper toward Proposition 3.9: code cells and native cells are in
bijection after the already geometric vertex and edge identifications. -/
@[expose] def intrinsicConsumersCodeCells (M : GeometricSideSubmap)
    (C : IntrinsicGeometricSubmap A)
    (hv : (fun v => I.vertexEquiv (wholePlaneVertexι W 0 v)) '' M.vertices = C.vertices)
    (he : (fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)) '' M.edges = C.edges) :
    GeometricSideCell M ≃ IntrinsicSideCell A C :=
  Equiv.sumCongr
    (Equiv.ofBijective (fun v => ⟨I.vertexEquiv (wholePlaneVertexι W 0 v.val),
      hv ▸ ⟨v.val, v.property, rfl⟩⟩) (by
        constructor
        · intro v w hh
          exact Subtype.ext (wholePlaneVertexι_injective W 0
            (I.vertexEquiv.injective (congrArg Subtype.val hh)))
        · intro v
          have hmem : v.val ∈ (fun w => I.vertexEquiv (wholePlaneVertexι W 0 w)) ''
              M.vertices := hv.symm ▸ v.property
          obtain ⟨w, hw, heq⟩ := hmem
          exact ⟨⟨w, hw⟩, Subtype.ext heq⟩))
    (intrinsicConsumersCodeDarts W H h hpast hp A I M.edges C he)

/-- Helper toward Proposition 3.9: either geometric side of a transported
code geodesic has the independently constructed unmarked rooted class.
This does not identify the geodesic as intrinsically leftmost. -/
theorem intrinsicConsumers_side_class {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (t : ThinMapSide) :
    intrinsicSideSubmapClass A
      (intrinsicGeodesicSide A (intrinsicBusemannImageCut W H G hp D A I)
        (I.h '' m0GeodesicAmbientRegion W H h) (I.vertexEquiv ((D).x (k - 1)))
        (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n))) t)
      (I.vertexEquiv ((D).x k)) = sideSubmapClass (m0GeodesicSide hpast P t) := by
  let M := m0GeodesicSide hpast P t
  let C := intrinsicGeodesicSide A (intrinsicBusemannImageCut W H G hp D A I)
    (I.h '' m0GeodesicAmbientRegion W H h) (I.vertexEquiv ((D).x (k - 1)))
    (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n))) t
  have hv := intrinsicSide_code_vertices W H h hpast hp A I P t
  have he := intrinsicSide_code_edges W H h hpast hp A I P t
  let e := intrinsicConsumersCodeCells W H h hpast hp A I M C hv he
  let J := intrinsicConsumersCodeDart W H h hpast hp A I
  have hi := I.vertexEquiv.injective.comp (wholePlaneVertexι_injective W 0)
  have hroot (v : M.vertices) : v.val = M.root ↔
      I.vertexEquiv (wholePlaneVertexι W 0 v.val) = I.vertexEquiv ((D).x k) := by
    rw [(D).x_eq h hLL k]
    exact hi.eq_iff.symm
  have hinc (d : {d : ℕ × Bool // d.1 ∈ M.edges}) (v : M.vertices) :
      (if d.val.2 then M.east d.val.1 else M.west d.val.1) = v.val ↔
        d39GeomRootVertex A.map (J d.val) =
          I.vertexEquiv (wholePlaneVertexι W 0 v.val) := by
    rw [intrinsicConsumersCodeDart_vertex]
    exact hi.eq_iff.symm
  have hopp (d a : {d : ℕ × Bool // d.1 ∈ M.edges}) :
      (d.val.1, !d.val.2) = a.val ↔ ((J d.val).1, !(J d.val).2) = J a.val := by
    rw [← intrinsicConsumersCodeDart_flip]
    exact (intrinsicConsumersCodeDart_injective W H h hpast hp A I).eq_iff.symm
  have hor (d : {d : ℕ × Bool // d.1 ∈ M.edges}) :
      d.val.1 ∈ M.present ∧ d.val.2 = false ↔
        intrinsicFutureAmbientTail A (J d.val) ∧ ¬ C.missing (J d.val).1 :=
    (intrinsicConsumersCodeDart_oriented W H h hpast hp A I d.val).symm
  have hrot (d a : {d : ℕ × Bool // d.1 ∈ M.edges}) :
      M.rotation d.val a.val ↔ intrinsicFutureRotation A C.edges (J a.val) (J d.val) := by
    rw [← he]
    exact (intrinsicSide_code_rotation_iff W H h hpast hp A I M.edges
      d.val a.val d.property a.property).symm
  have hface (d a : {d : ℕ × Bool // d.1 ∈ M.edges}) :
      M.faceNext d.val a.val ↔ intrinsicSideFaceNext A C (J d.val) (J a.val) :=
    (intrinsicSide_code_side_faceNext W H h hpast hp A I longest k P t d.val a.val).symm
  have hrel (r : SideSubmapRelation) (u v : GeometricSideCell M) :
      sideSubmapRelation M r u v ↔
        intrinsicSideRelation A C (I.vertexEquiv ((D).x k)) r (e u) (e v) := by
    cases r <;> cases u <;> cases v <;> first
      | exact Iff.rfl
      | exact hroot _
      | exact hinc _ _
      | exact hopp _ _
      | exact hor _
      | exact hrot _ _
      | exact hface _ _
  symm
  apply (sideSubmapClass_eq_iff _ _).mpr
  refine ⟨⟨e.trans (intrinsicSideNumberCells A C (I.vertexEquiv ((D).x k))), ?_⟩⟩
  intro r u v
  exact (hrel r u v).trans
    (intrinsicSideNumberCells_relation A C (I.vertexEquiv ((D).x k)) r (e u) (e v)).symm

/-- Helper toward Proposition 3.9: the finite enclosed slice at the least
coalescence offsets has the independently constructed unmarked rooted class.
The geometric inputs are code leftmostness and least edge coalescence; no
class equality, face-containment assertion, or intrinsic uniqueness is assumed. -/
theorem intrinsicConsumers_slice_class {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hpast hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    intrinsicSideSubmapClass A (intrinsicGeodesicSliceOfCode W H h hpast hp A I P k a b)
      (I.vertexEquiv ((D).x (k - 1))) =
        sideSubmapClass (m0CutGeodesicSlice (hp := hpast) P k a b hab) := by
  let M := m0CutGeodesicSlice (hp := hpast) P k a b hab
  let C := intrinsicGeodesicSliceOfCode W H h hpast hp A I P k a b
  have hc := intrinsicGeodesicSliceOfCode_carriers W H h hpast hp A I P T hleft k a b hab
  have hv := hc.1
  have he := hc.2.1
  let e := intrinsicConsumersCodeCells W H h hpast hp A I M C hv he
  let J := intrinsicConsumersCodeDart W H h hpast hp A I
  have hi := I.vertexEquiv.injective.comp (wholePlaneVertexι_injective W 0)
  have hroot (v : M.vertices) : v.val = M.root ↔
      I.vertexEquiv (wholePlaneVertexι W 0 v.val) = I.vertexEquiv ((D).x (k - 1)) := by
    rw [(D).x_eq h hLL (k - 1)]
    exact hi.eq_iff.symm
  have hinc (d : {d : ℕ × Bool // d.1 ∈ M.edges}) (v : M.vertices) :
      (if d.val.2 then M.east d.val.1 else M.west d.val.1) = v.val ↔
        d39GeomRootVertex A.map (J d.val) =
          I.vertexEquiv (wholePlaneVertexι W 0 v.val) := by
    rw [intrinsicConsumersCodeDart_vertex]
    exact hi.eq_iff.symm
  have hopp (d a : {d : ℕ × Bool // d.1 ∈ M.edges}) :
      (d.val.1, !d.val.2) = a.val ↔ ((J d.val).1, !(J d.val).2) = J a.val := by
    rw [← intrinsicConsumersCodeDart_flip]
    exact (intrinsicConsumersCodeDart_injective W H h hpast hp A I).eq_iff.symm
  have hor (d : {d : ℕ × Bool // d.1 ∈ M.edges}) :
      d.val.1 ∈ M.present ∧ d.val.2 = false ↔
        intrinsicFutureAmbientTail A (J d.val) ∧ ¬ C.missing (J d.val).1 :=
    (intrinsicConsumersCodeDart_oriented W H h hpast hp A I d.val).symm
  have hrot (d a : {d : ℕ × Bool // d.1 ∈ M.edges}) :
      M.rotation d.val a.val ↔ intrinsicFutureRotation A C.edges (J a.val) (J d.val) := by
    rw [← he]
    exact (intrinsicSide_code_rotation_iff W H h hpast hp A I M.edges
      d.val a.val d.property a.property).symm
  have hface (d e' : {d : ℕ × Bool // d.1 ∈ M.edges}) :
      M.faceNext d.val e'.val ↔ intrinsicSideFaceNext A C (J d.val) (J e'.val) :=
    (intrinsicSide_code_slice_faceNext W H h hpast hp A I longest
      P T hleft k a b hab d.val e'.val).symm
  have hrel (r : SideSubmapRelation) (u v : GeometricSideCell M) :
      sideSubmapRelation M r u v ↔
        intrinsicSideRelation A C (I.vertexEquiv ((D).x (k - 1))) r (e u) (e v) := by
    cases r <;> cases u <;> cases v <;> first
      | exact Iff.rfl
      | exact hroot _
      | exact hinc _ _
      | exact hopp _ _
      | exact hor _
      | exact hrot _ _
      | exact hface _ _
  symm
  apply (sideSubmapClass_eq_iff _ _).mpr
  refine ⟨⟨e.trans (intrinsicSideNumberCells A C (I.vertexEquiv ((D).x (k - 1)))), ?_⟩⟩
  intro r u v
  exact (hrel r u v).trans
    (intrinsicSideNumberCells_relation A C (I.vertexEquiv ((D).x (k - 1)))
      r (e u) (e v)).symm

end Source

/-- Helper toward Proposition 3.9: all source slice witnesses select the
same geodesics and the same ordered pair of least offsets at every index.
The reference rays may differ. -/
theorem intrinsicConsumers_sliceWitness_unique {W : ℤ → Fin 3}
    {x : XDP}
    (s t : M0CutGeodesicSliceWitness W x) :
    s.P = t.P ∧ ∀ k, s.thetaMinus k = t.thetaMinus k ∧ s.theta k = t.theta k := by
  have hP : s.P = t.P := by
    funext k
    exact t.huniq k (s.P k) (intrinsicSide_leftmost_change_reference
      (s.P k) (t.P k) (s.T k) (t.T k) (s.hleft k) (t.hleft k))
  refine ⟨hP, fun k => ?_⟩
  have hs := s.least k
  rw [hP] at hs
  have ht := t.least k
  exact ⟨le_antisymm (hs.2 _ _ ht.1).1 (ht.2 _ _ hs.1).1,
    le_antisymm (hs.2 _ _ ht.1).2 (ht.2 _ _ hs.1).2⟩

/-- Helper toward Proposition 3.9: the optional slice reader agrees with
every complete source witness, including its least offsets simultaneously. -/
theorem intrinsicConsumers_slice_reader_of_witness {W : ℤ → Fin 3}
    {x : XDP}
    (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    m0CutGeodesicSliceClassOption x k W = some (geometricSideClass
      (m0CutGeodesicSlice (hp := s.hp) s.P k
        (s.thetaMinus k) (s.theta k) (s.least k))) := by
  have hs : Nonempty (M0CutGeodesicSliceWitness W x) := ⟨s⟩
  rw [m0CutGeodesicSliceClassOption, dite_eq_left hs]
  let t := Classical.choice hs
  have ht := intrinsicConsumers_sliceWitness_unique t s
  change some (geometricSideClass (m0CutGeodesicSlice (hp := t.hp) t.P k
    (t.thetaMinus k) (t.theta k) (t.least k))) = _
  simp only [ht.1, (ht.2 k).1, (ht.2 k).2]

/-- Helper toward Proposition 3.9: one source witness identifies all three
optional readers with the native geometric classes, after mark forgetting.
The same witness supplies the least intrinsic offsets. This is deterministic
and does not assert intrinsic leftmostness or a law of intrinsic objects. -/
theorem intrinsicConsumers_readers_of_witness
    (W : ℤ → Fin 3) (x : XDP)
    (s : M0CutGeodesicSliceWitness W x)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W s.H
        (WholePlanePastGlueDrawing.glueDrawing W s.h s.hp s.H) hp)
      (uibotWholePlaneSourceRoot W s.H
        (WholePlanePastGlueDrawing.glueDrawing W s.h s.hp s.H)) A.map A.root)
    (k : ℤ) :
    let D := m0CutData W s.H s.h s.hLL
    let G := WholePlanePastGlueDrawing.glueDrawing W s.h s.hp s.H
    let L := fun t => intrinsicGeodesicSide A
      (intrinsicBusemannImageCut W s.H G hp D A I)
      (I.h '' m0GeodesicAmbientRegion W s.H s.h) (I.vertexEquiv (D.x (k - 1)))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 ((s.P k).codePath.edge n))) t
    let C := intrinsicGeodesicSliceOfCode W s.H s.h s.hp hp A I s.P k
      (s.thetaMinus k) (s.theta k)
    Option.map forgetMarks (lemma55LeftSideClassOption x k W) =
        some (intrinsicSideSubmapClass A (L .left) (I.vertexEquiv (D.x k))) ∧
    Option.map forgetMarks (lemma55RightSideClassOption2 x k W) =
        some (intrinsicSideSubmapClass A (L .right) (I.vertexEquiv (D.x k))) ∧
    Option.map forgetMarks (m0CutGeodesicSliceClassOption x k W) =
        some (intrinsicSideSubmapClass A C (I.vertexEquiv (D.x (k - 1)))) ∧
    IntrinsicLeastEdgeCoalescence
      (intrinsicGeodesicOfCode W s.H s.h s.hLL G hp A I (s.P (k - 1))).val
      (intrinsicGeodesicOfCode W s.H s.h s.hLL G hp A I (s.P k)).val
      (s.thetaMinus k) (s.theta k) := by
  dsimp only
  have hside := intrinsicSide_classes_of_sliceWitness s k
  rw [hside.1, hside.2, intrinsicConsumers_slice_reader_of_witness s k]
  simp only [Option.map_some, forgetMarks_geometricSideClass]
  exact ⟨congrArg some (intrinsicConsumers_side_class W s.H s.h s.hp hp A I
      (s.P k) .left).symm,
    congrArg some (intrinsicConsumers_side_class W s.H s.h s.hp hp A I
      (s.P k) .right).symm,
    congrArg some (intrinsicConsumers_slice_class W s.H s.h s.hp hp A I
      s.P s.T s.hleft k (s.thetaMinus k) (s.theta k) (s.least k)).symm,
    (intrinsicGeodesicOfCode_least_iff W s.H s.h s.hLL _ hp A I
      (s.P (k - 1)) (s.P k) _ _).mpr (s.least k)⟩

/-- Helper toward Proposition 3.9: the common geometric witness ensures
presence of both side readers and the slice reader at every index. -/
theorem intrinsicConsumers_readers_present {W : ℤ → Fin 3} {x : XDP}
    (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    (lemma55LeftSideClassOption x k W).isSome ∧
      (lemma55RightSideClassOption2 x k W).isSome ∧
      (m0CutGeodesicSliceClassOption x k W).isSome := by
  have hside := intrinsicSide_classes_of_sliceWitness s k
  rw [hside.1, hside.2, intrinsicConsumers_slice_reader_of_witness s k]
  exact ⟨rfl, rfl, rfl⟩

/-- Helper toward Proposition 3.9: the precise defaulted mark-forgetting
convention of Lemmas 5.5 and 5.6 gives these same native classes, for every
default, using one shared geometric witness. -/
theorem intrinsicConsumers_default_readers_of_witness
    (W : ℤ → Fin 3) (x : XDP) (s : M0CutGeodesicSliceWitness W x)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W s.H
        (WholePlanePastGlueDrawing.glueDrawing W s.h s.hp s.H) hp)
      (uibotWholePlaneSourceRoot W s.H
        (WholePlanePastGlueDrawing.glueDrawing W s.h s.hp s.H)) A.map A.root)
    (k : ℤ) (default : GeometricSideClass) :
    let D := m0CutData W s.H s.h s.hLL
    let G := WholePlanePastGlueDrawing.glueDrawing W s.h s.hp s.H
    let L := fun t => intrinsicGeodesicSide A
      (intrinsicBusemannImageCut W s.H G hp D A I)
      (I.h '' m0GeodesicAmbientRegion W s.H s.h) (I.vertexEquiv (D.x (k - 1)))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 ((s.P k).codePath.edge n))) t
    let C := intrinsicGeodesicSliceOfCode W s.H s.h s.hp hp A I s.P k
      (s.thetaMinus k) (s.theta k)
    forgetMarksOptionClassValue default (lemma55LeftSideClassOption x k W) =
        intrinsicSideSubmapClass A (L .left) (I.vertexEquiv (D.x k)) ∧
    forgetMarksOptionClassValue default (lemma55RightSideClassOption2 x k W) =
        intrinsicSideSubmapClass A (L .right) (I.vertexEquiv (D.x k)) ∧
    forgetMarksOptionClassValue default (m0CutGeodesicSliceClassOption x k W) =
        intrinsicSideSubmapClass A C (I.vertexEquiv (D.x (k - 1))) := by
  dsimp only
  have hside := intrinsicSide_classes_of_sliceWitness s k
  rw [hside.1, hside.2, intrinsicConsumers_slice_reader_of_witness s k]
  simp only [forgetMarksOptionClassValue, Function.comp_apply, lemma55OptionClassValue,
    Option.getD_some, forgetMarks_geometricSideClass]
  exact ⟨(intrinsicConsumers_side_class W s.H s.h s.hp hp A I (s.P k) .left).symm,
    (intrinsicConsumers_side_class W s.H s.h s.hp hp A I (s.P k) .right).symm,
    (intrinsicConsumers_slice_class W s.H s.h s.hp hp A I s.P s.T s.hleft k
      (s.thetaMinus k) (s.theta k) (s.least k)).symm⟩

/- REMAINING NATIVE-REGION STATEMENT — full binders; not a declaration,
not an assumption, and not discharged by any class comparison above.

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
  (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h (k - 1))))
let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
∀ (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp)
    (uibotWholePlaneSourceRoot W H G) A.map A.root)
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

REMAINING INTRINSIC UNIQUENESS — full common-event binders. The existing
source witnesses in this statement are not intrinsically leftmost until the
native-region obligation is proved. In particular, code-witness uniqueness
above cannot be substituted for the following conclusion.

∀ᵐ U ∂wholePlaneIIDCodeMeasure,
  let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U
  let W := uibotRecoveredCode z
  ∃ (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
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
    ∀ (x : XDP) (k : ℤ),
    let longest := if x = XDP.ldp then true else false
    let P := intrinsicConsumersGeodesicOfCode W H h hpast hp A I ((s x).P k)
    IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest P ∧
    ∀ Q : IntrinsicInfiniteXDPGeodesic A S (C.x k) longest,
      IsIntrinsicLeftmostXDPGeodesic A S (C.x k) longest Q → Q = P.

The complete consumer target must retain this event and these SAME witnesses,
for every representative A and every produced I, together with all three
class comparisons of intrinsicConsumers_readers_of_witness at every x,k;
the geometric Borel reader is uibotGeomSideSliceObservables and its offset
reader is uibotGeomCoalescenceOffsets. The complete laws remain the optional
presence, side independence, right laws for k ≥ 0, left laws for k ≤ 0 of
GeoInftyInd.lem_geo_infty_ind, and one Borel slice family, common witnesses,
least offsets, joint independence and laws on k ≥ 1 and k ≤ 0 of
GeoSlice.lem_geo_slice. Only after the intrinsic uniqueness above is proved
may those reader laws be called laws of the sampled map's intrinsic objects.
No probability-law conclusion with a class-equality premise is introduced. -/

end DirectedDistances.PaperProofs.Section3
