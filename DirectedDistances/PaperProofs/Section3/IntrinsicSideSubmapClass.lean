/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicSideSliceIdentification
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart7
public import Mathlib.Logic.Encodable.Basic
import all DirectedDistances.PaperProofs.Section5.GeoInftyLemma55ForgetMarks
import all DirectedDistances.PaperProofs.Section5.Prop516StarRotationCommutation
import all DirectedDistances.KMSW.WholePlaneRightmostOutgoingExists

/-! # Rooted classes of intrinsic geometric submaps

Helpers toward Proposition 3.9, using the submaps of Lemmas 5.5 and 5.6
below are computed from the representative. Natural-number labels serve only
the carrier convention of `SideSubmapClass`. Indexed boundary and seam marks
are forgotten, exactly as in `GeoInftyLemma55ForgetMarks`.

An arbitrary carrier record need not be a connected submap or contain its
specified root. The construction retains its literal relations and does not
assert these additional properties. No intrinsic qualification is removed. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section5
open scoped Classical

local instance intrinsicSideSubmapClassVertexCountable (A : D39DomainRootedMap.{0}) :
    Countable A.V := A.domain.vertices_countable
local instance intrinsicSideSubmapClassEdgeCountable (A : D39DomainRootedMap.{0}) :
    Countable A.E := A.domain.edges_countable
local instance intrinsicSideSubmapClassVertexEncodable (A : D39DomainRootedMap.{0}) :
    Encodable A.V := Encodable.ofCountable A.V
local instance intrinsicSideSubmapClassEdgeEncodable (A : D39DomainRootedMap.{0}) :
    Encodable A.E := Encodable.ofCountable A.E

/-- Helper toward Proposition 3.9: geometric vertices and both incidences
of each retained edge, including every missing edge. -/
abbrev IntrinsicSideCell (A : D39DomainRootedMap.{0}) (C : IntrinsicGeometricSubmap A) :=
  Sum C.vertices {d : A.E × Bool // d.1 ∈ C.edges}

/-- Helper toward Proposition 3.9: retained ambient face succession,
using winding-left incidence and inverse rotation after edge reversal. -/
@[expose] def intrinsicSideFaceNext (A : D39DomainRootedMap.{0})
    (C : IntrinsicGeometricSubmap A) (d e : A.E × Bool) : Prop :=
  (∃ F ∈ C.faces, ∀ s, LeftAtOn F.val (intrinsicFutureDartArc A d) s) ∧
    intrinsicFutureRotation A Set.univ (d.1, !d.2) e

/-- Helper toward Proposition 3.9: rooted structural relations computed
only from the ambient drawing and retained carriers. Forward rotation is
the converse of the existing inverse-rotation predicate. -/
@[expose] def intrinsicSideRelation (A : D39DomainRootedMap.{0})
    (C : IntrinsicGeometricSubmap A) (root : A.V) :
    SideSubmapRelation → IntrinsicSideCell A C → IntrinsicSideCell A C → Prop
  | .vertex, .inl _, _ => True
  | .root, .inl v, _ => v.val = root
  | .incident, .inr d, .inl v => d39GeomRootVertex A.map d.val = v.val
  | .opposite, .inr d, .inr e => (d.val.1, !d.val.2) = e.val
  | .oriented, .inr d, _ => intrinsicFutureAmbientTail A d.val ∧ ¬ C.missing d.val.1
  | .rotation, .inr d, .inr e => intrinsicFutureRotation A C.edges e.val d.val
  | .faceNext, .inr d, .inr e => intrinsicSideFaceNext A C d.val e.val
  | _, _, _ => False

/-- Helper toward Proposition 3.9: transport all retained carriers and
additional missing tags along the actual geometric isomorphism. -/
@[expose] def intrinsicSideMapSubmap {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)
    (C : IntrinsicGeometricSubmap A) : IntrinsicGeometricSubmap B where
  vertices := I.vertexEquiv '' C.vertices
  edges := I.edgeEquiv '' C.edges
  faces := I.faceEquiv '' C.faces
  missing e := C.missing (I.edgeEquiv.symm e)

/-- Helper toward Proposition 3.9: face succession transports with the
whole retained face and the actual dart, allowing stored-endpoint flips. -/
theorem intrinsicSideFaceNext_map {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)
    (C : IntrinsicGeometricSubmap A) (d e : A.E × Bool) :
    intrinsicSideFaceNext B (intrinsicSideMapSubmap I C)
      (intrinsicFutureDartEquiv I d) (intrinsicFutureDartEquiv I e) ↔
        intrinsicSideFaceNext A C d e := by
  unfold intrinsicSideFaceNext
  apply and_congr
  · constructor
    · rintro ⟨F, ⟨F, hF, rfl⟩, hd⟩
      rw [I.faceEquiv_val] at hd
      exact ⟨F, hF, (intrinsicFuture_leftAtOn_map I F.val d).mpr hd⟩
    · rintro ⟨F, hF, hd⟩
      refine ⟨I.faceEquiv F, ⟨F, hF, rfl⟩, ?_⟩
      rw [I.faceEquiv_val]
      exact (intrinsicFuture_leftAtOn_map I F.val d).mp hd
  · rw [← intrinsicFutureDartEquiv_flip]
    have hu : I.edgeEquiv '' (Set.univ : Set A.E) = Set.univ :=
      Set.image_univ_of_surjective I.edgeEquiv.surjective
    rw [← hu]
    exact intrinsicFutureRotation_map_iff I Set.univ _ _

/-- Helper toward Proposition 3.9: choose the stored dart that follows
the ambient direction when present. Missing edges have two unoriented
incidences; their label convention uses the stored forward arc. -/
@[expose] def intrinsicSideBaseBit (A : D39DomainRootedMap.{0}) (e : A.E) : Bool :=
  if h : ¬ A.map.missing e then A.map.forward ⟨e, h⟩ else true

/-- Helper toward Proposition 3.9: relabel the two incidences so code
bit false follows the ambient direction on every present edge. -/
@[expose] def intrinsicSideDart (A : D39DomainRootedMap.{0}) (d : A.E × Bool) :
    A.E × Bool := (d.1, Bool.xor d.2 (intrinsicSideBaseBit A d.1))

/-- Helper toward Proposition 3.9: incidence relabeling is an involution. -/
theorem intrinsicSideDart_involutive (A : D39DomainRootedMap.{0}) :
    Function.Involutive (intrinsicSideDart A) := by
  intro d
  simp only [intrinsicSideDart, Bool.xor_assoc, Bool.xor_self, Bool.xor_false,
    Prod.mk.eta]

/-- Helper toward Proposition 3.9: incidence relabeling commutes with
geometric edge reversal, including missing edges. -/
theorem intrinsicSideDart_flip (A : D39DomainRootedMap.{0}) (d : A.E × Bool) :
    intrinsicSideDart A (d.1, !d.2) =
      ((intrinsicSideDart A d).1, !(intrinsicSideDart A d).2) := by
  cases hb : d.2 <;> cases hc : intrinsicSideBaseBit A d.1 <;>
    simp only [intrinsicSideDart, hb, hc] <;> rfl

/-- Helper toward Proposition 3.9: the false code incidence is oriented
exactly on ambient present edges; a missing edge has no orientation. -/
theorem intrinsicSideDart_tail_iff (A : D39DomainRootedMap.{0}) (d : A.E × Bool) :
    intrinsicFutureAmbientTail A (intrinsicSideDart A d) ↔
      ¬ A.map.missing d.1 ∧ d.2 = false := by
  unfold intrinsicFutureAmbientTail intrinsicSideDart intrinsicSideBaseBit
  by_cases h : ¬ A.map.missing d.1
  · simp only [dite_eq_left h]
    cases hb : d.2 <;> cases hf : A.map.forward ⟨d.1, h⟩ <;>
      simp [hf, h]
  · simp only [dite_eq_right h]
    exact ⟨fun ⟨he, _⟩ => (h he).elim, fun ⟨he, _⟩ => (h he).elim⟩

/-- Helper toward Proposition 3.9: decode an ambient edge label. Values
outside the encoding range never occur in the retained cell carrier. -/
@[expose] def intrinsicSideDecodeEdge (A : D39DomainRootedMap.{0}) (n : ℕ) : A.E :=
  (Encodable.decode n).getD A.root.1

/-- Helper toward Proposition 3.9: decoding preserves each actual edge identity. -/
theorem intrinsicSideDecodeEdge_encode (A : D39DomainRootedMap.{0}) (e : A.E) :
    intrinsicSideDecodeEdge A (Encodable.encode e) = e := by
  simp only [intrinsicSideDecodeEdge, Encodable.encodek, Option.getD_some]

/-- Helper toward Proposition 3.9: decode a numbered incidence into
the drawing, using the direction-normalized bit convention. -/
@[expose] def intrinsicSideDecodeDart (A : D39DomainRootedMap.{0}) (d : ℕ × Bool) :
    A.E × Bool := intrinsicSideDart A (intrinsicSideDecodeEdge A d.1, d.2)

/-- Helper toward Proposition 3.9: the numbered representative of the
geometric submap. Only the two discarded indexed marks use arbitrary values;
all retained fields are computed from A, C, and the specified root. -/
@[expose] def intrinsicSideSubmap (A : D39DomainRootedMap.{0})
    (C : IntrinsicGeometricSubmap A) (root : A.V) : GeometricSideSubmap where
  vertices := Encodable.encode '' C.vertices
  edges := Encodable.encode '' C.edges
  west n := Encodable.encode (d39GeomRootVertex A.map (intrinsicSideDecodeDart A (n, false)))
  east n := Encodable.encode (d39GeomRootVertex A.map (intrinsicSideDecodeDart A (n, true)))
  present := {n | ¬ A.map.missing (intrinsicSideDecodeEdge A n) ∧
    ¬ C.missing (intrinsicSideDecodeEdge A n)}
  rotation d e := intrinsicFutureRotation A C.edges
    (intrinsicSideDecodeDart A e) (intrinsicSideDecodeDart A d)
  faceNext d e := intrinsicSideFaceNext A C
    (intrinsicSideDecodeDart A d) (intrinsicSideDecodeDart A e)
  root := Encodable.encode root
  boundary _ := (Encodable.encode A.root.1, false)
  seam _ := (Encodable.encode A.root.1, false)

/-- Helper toward Proposition 3.9: the rooted geometric submap class,
formed independently of a KMSW code or a source isomorphism. -/
@[expose] def intrinsicSideSubmapClass (A : D39DomainRootedMap.{0})
    (C : IntrinsicGeometricSubmap A) (root : A.V) : SideSubmapClass :=
  sideSubmapClass (intrinsicSideSubmap A C root)

/-- Helper toward Proposition 3.9: the numbering is a bijection on
retained geometric incidences; both darts of every missing edge survive. -/
@[expose] def intrinsicSideNumberDarts (A : D39DomainRootedMap.{0})
    (C : IntrinsicGeometricSubmap A) :
    {d : A.E × Bool // d.1 ∈ C.edges} ≃
      {d : ℕ × Bool // d.1 ∈ Encodable.encode '' C.edges} where
  toFun d := ⟨(Encodable.encode d.val.1, (intrinsicSideDart A d.val).2),
    ⟨d.val.1, d.property, rfl⟩⟩
  invFun d := ⟨intrinsicSideDecodeDart A d.val, by
    obtain ⟨e, he, henc⟩ := d.property
    change intrinsicSideDecodeEdge A d.val.1 ∈ C.edges
    rw [← henc, intrinsicSideDecodeEdge_encode]
    exact he⟩
  left_inv := by
    intro d
    apply Subtype.ext
    simp only [intrinsicSideDecodeDart, intrinsicSideDecodeEdge_encode]
    exact intrinsicSideDart_involutive A d.val
  right_inv := by
    rintro ⟨⟨n, b⟩, hn⟩
    apply Subtype.ext
    obtain ⟨e, he, henc⟩ := hn
    change Encodable.encode e = n at henc
    change (Encodable.encode (intrinsicSideDecodeEdge A n),
      (intrinsicSideDart A (intrinsicSideDecodeDart A (n, b))).2) = (n, b)
    rw [← henc]
    simp only [intrinsicSideDecodeDart, intrinsicSideDecodeEdge_encode,
      intrinsicSideDart, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- Helper toward Proposition 3.9: the complete cell numbering preserves
vertex and edge identity, without assuming either carrier infinite. -/
@[expose] def intrinsicSideNumberCells (A : D39DomainRootedMap.{0})
    (C : IntrinsicGeometricSubmap A) (root : A.V) :
    IntrinsicSideCell A C ≃ GeometricSideCell (intrinsicSideSubmap A C root) :=
  Equiv.sumCongr (Equiv.Set.image Encodable.encode C.vertices Encodable.encode_injective)
    (intrinsicSideNumberDarts A C)

/-- Helper toward Proposition 3.9: decoding a numbered retained dart
recovers its actual geometric incidence. -/
theorem intrinsicSideNumberDarts_decode (A : D39DomainRootedMap.{0})
    (C : IntrinsicGeometricSubmap A) (d : {d : A.E × Bool // d.1 ∈ C.edges}) :
    intrinsicSideDecodeDart A (intrinsicSideNumberDarts A C d).val = d.val := by
  change intrinsicSideDart A
    (intrinsicSideDecodeEdge A (Encodable.encode d.val.1),
      (intrinsicSideDart A d.val).2) = d.val
  rw [intrinsicSideDecodeEdge_encode]
  exact intrinsicSideDart_involutive A d.val

/-- Helper toward Proposition 3.9: numbering preserves every retained
unmarked relation, including root, induced rotation and face succession. -/
theorem intrinsicSideNumberCells_relation (A : D39DomainRootedMap.{0})
    (C : IntrinsicGeometricSubmap A) (root : A.V)
    (t : SideSubmapRelation) (u v : IntrinsicSideCell A C) :
    sideSubmapRelation (intrinsicSideSubmap A C root) t
      (intrinsicSideNumberCells A C root u) (intrinsicSideNumberCells A C root v) ↔
        intrinsicSideRelation A C root t u v := by
  have hincident (d : {d : A.E × Bool // d.1 ∈ C.edges}) (v : C.vertices) :
      (if (intrinsicSideNumberDarts A C d).val.2 then
        (intrinsicSideSubmap A C root).east (intrinsicSideNumberDarts A C d).val.1
      else (intrinsicSideSubmap A C root).west (intrinsicSideNumberDarts A C d).val.1) =
        Encodable.encode v.val ↔ d39GeomRootVertex A.map d.val = v.val := by
    have hcode (q : ℕ × Bool) :
        (if q.2 then (intrinsicSideSubmap A C root).east q.1
        else (intrinsicSideSubmap A C root).west q.1) = Encodable.encode v.val ↔
          d39GeomRootVertex A.map (intrinsicSideDecodeDart A q) = v.val := by
      rcases q with ⟨n, b⟩
      cases b <;> exact Encodable.encode_injective.eq_iff
    rw [hcode, intrinsicSideNumberDarts_decode]
  have horiented (d : {d : A.E × Bool // d.1 ∈ C.edges}) :
      (intrinsicSideNumberDarts A C d).val.1 ∈ (intrinsicSideSubmap A C root).present ∧
        (intrinsicSideNumberDarts A C d).val.2 = false ↔
          intrinsicFutureAmbientTail A d.val ∧ ¬ C.missing d.val.1 := by
    change (¬ A.map.missing (intrinsicSideDecodeEdge A (Encodable.encode d.val.1)) ∧
      ¬ C.missing (intrinsicSideDecodeEdge A (Encodable.encode d.val.1))) ∧
      (intrinsicSideDart A d.val).2 = false ↔ _
    rw [intrinsicSideDecodeEdge_encode]
    have ht := intrinsicSideDart_tail_iff A (intrinsicSideDart A d.val)
    rw [intrinsicSideDart_involutive A d.val] at ht
    rw [ht]
    exact and_right_comm
  have hopposite (d e : {d : A.E × Bool // d.1 ∈ C.edges}) :
      ((intrinsicSideNumberDarts A C d).val.1, !(intrinsicSideNumberDarts A C d).val.2) =
        (intrinsicSideNumberDarts A C e).val ↔ (d.val.1, !d.val.2) = e.val := by
    change (Encodable.encode d.val.1, !(intrinsicSideDart A d.val).2) =
      (Encodable.encode e.val.1, (intrinsicSideDart A e.val).2) ↔ _
    rw [Prod.mk.injEq, Encodable.encode_injective.eq_iff, ← Prod.mk.injEq]
    change ((intrinsicSideDart A d.val).1, !(intrinsicSideDart A d.val).2) =
      intrinsicSideDart A e.val ↔ _
    rw [← intrinsicSideDart_flip]
    exact (intrinsicSideDart_involutive A).injective.eq_iff
  cases t <;> cases u <;> cases v <;> first
    | exact Iff.rfl
    | exact Encodable.encode_injective.eq_iff
    | exact hincident _ _
    | exact horiented _
    | exact hopposite _ _
    | (change intrinsicFutureRotation A C.edges
        (intrinsicSideDecodeDart A (intrinsicSideNumberDarts A C _).val)
        (intrinsicSideDecodeDart A (intrinsicSideNumberDarts A C _).val) ↔ _
       rw [intrinsicSideNumberDarts_decode, intrinsicSideNumberDarts_decode]
       rfl)
    | (change intrinsicSideFaceNext A C
        (intrinsicSideDecodeDart A (intrinsicSideNumberDarts A C _).val)
        (intrinsicSideDecodeDart A (intrinsicSideNumberDarts A C _).val) ↔ _
       rw [intrinsicSideNumberDarts_decode, intrinsicSideNumberDarts_decode]
       rfl)

/-- Helper toward Proposition 3.9: the geometric isomorphism restricts
to all retained cells, with its storage-flip bit on each dart. -/
@[expose] def intrinsicSideMapCells {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)
    (C : IntrinsicGeometricSubmap A) :
    IntrinsicSideCell A C ≃ IntrinsicSideCell B (intrinsicSideMapSubmap I C) :=
  Equiv.sumCongr (I.vertexEquiv.image C.vertices)
    ((intrinsicFutureDartEquiv I).subtypeEquiv (by
      intro d
      change d.1 ∈ C.edges ↔ I.edgeEquiv d.1 ∈ I.edgeEquiv '' C.edges
      exact I.edgeEquiv.injective.mem_set_image.symm))

/-- Helper toward Proposition 3.9: every geometric structural relation
commutes with representative transport, including the specified vertex root. -/
theorem intrinsicSideMapCells_relation {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)
    (C : IntrinsicGeometricSubmap A) (root : A.V)
    (t : SideSubmapRelation) (u v : IntrinsicSideCell A C) :
    intrinsicSideRelation B (intrinsicSideMapSubmap I C) (I.vertexEquiv root) t
      (intrinsicSideMapCells I C u) (intrinsicSideMapCells I C v) ↔
        intrinsicSideRelation A C root t u v := by
  have hincident (d : {d : A.E × Bool // d.1 ∈ C.edges}) (v : C.vertices) :
      d39GeomRootVertex B.map (intrinsicFutureDartEquiv I d.val) = I.vertexEquiv v.val ↔
        d39GeomRootVertex A.map d.val = v.val := by
    rw [intrinsicFutureDartEquiv_vertex]
    exact I.vertexEquiv.injective.eq_iff
  have hopposite (d e : {d : A.E × Bool // d.1 ∈ C.edges}) :
      ((intrinsicFutureDartEquiv I d.val).1, !(intrinsicFutureDartEquiv I d.val).2) =
        intrinsicFutureDartEquiv I e.val ↔ (d.val.1, !d.val.2) = e.val := by
    rw [← intrinsicFutureDartEquiv_flip]
    exact (intrinsicFutureDartEquiv I).injective.eq_iff
  have horiented (d : {d : A.E × Bool // d.1 ∈ C.edges}) :
      intrinsicFutureAmbientTail B (intrinsicFutureDartEquiv I d.val) ∧
        ¬ (intrinsicSideMapSubmap I C).missing (intrinsicFutureDartEquiv I d.val).1 ↔
          intrinsicFutureAmbientTail A d.val ∧ ¬ C.missing d.val.1 := by
    change intrinsicFutureAmbientTail B (intrinsicFutureDartEquiv I d.val) ∧
      ¬ C.missing (I.edgeEquiv.symm (I.edgeEquiv d.val.1)) ↔ _
    rw [intrinsicFutureAmbientTail_map, Equiv.symm_apply_apply]
  cases t <;> cases u <;> cases v <;> first
    | exact Iff.rfl
    | exact I.vertexEquiv.injective.eq_iff
    | exact hincident _ _
    | exact hopposite _ _
    | exact horiented _
    | exact intrinsicFutureRotation_map_iff I C.edges _ _
    | exact intrinsicSideFaceNext_map I C _ _

/-- Helper toward Proposition 3.9: a geometric isomorphism produces an
unmarked rooted submap isomorphism after the independent numberings. -/
@[expose] def intrinsicSideSubmapIso {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)
    (C : IntrinsicGeometricSubmap A) (root : A.V) :
    GeometricSideUnmarkedIso (intrinsicSideSubmap A C root)
      (intrinsicSideSubmap B (intrinsicSideMapSubmap I C) (I.vertexEquiv root)) where
  equiv := ((intrinsicSideNumberCells A C root).symm.trans
    (intrinsicSideMapCells I C)).trans
      (intrinsicSideNumberCells B (intrinsicSideMapSubmap I C) (I.vertexEquiv root))
  relation_iff := by
    intro t u v
    obtain ⟨u, rfl⟩ := (intrinsicSideNumberCells A C root).surjective u
    obtain ⟨v, rfl⟩ := (intrinsicSideNumberCells A C root).surjective v
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [intrinsicSideNumberCells_relation, intrinsicSideNumberCells_relation,
      intrinsicSideMapCells_relation]

/-- Helper toward Proposition 3.9: the independently constructed rooted
geometric submap class is invariant under every local topology geometric isomorphism. -/
theorem intrinsicSideSubmapClass_map {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)
    (C : IntrinsicGeometricSubmap A) (root : A.V) :
    intrinsicSideSubmapClass B (intrinsicSideMapSubmap I C) (I.vertexEquiv root) =
      intrinsicSideSubmapClass A C root := by
  symm
  exact (sideSubmapClass_eq_iff _ _).mpr ⟨intrinsicSideSubmapIso I C root⟩

/-- Helper toward Proposition 3.9: restricting a represented finite
cyclic star gives exactly first return to the retained incidences. The
representation and periodicity hypotheses concern the ambient rotation,
not the side or slice comparison. -/
theorem intrinsicSide_topological_firstReturn {D V : Type*}
    (rot : Equiv.Perm D) (vertex : D → V) (arc : D → unitInterval → ℂ)
    (hvertex : ∀ d, vertex (rot d) = vertex d)
    (hrot : ∀ d, D39TopologicalCcwSuccessor {q | vertex q = vertex d} arc d (rot d))
    (hperiod : ∀ d, ∃ n : ℕ, 0 < n ∧ (rot ^ n) d = d)
    (S : Set D) (d a : D) (hd : d ∈ S) (ha : a ∈ S) :
    D39TopologicalCcwSuccessor {q | q ∈ S ∧ vertex q = vertex d} arc d a ↔
      ∃ n : ℕ, 0 < n ∧ (rot ^ n) d = a ∧
        ∀ j : ℕ, 0 < j → j < n → (rot ^ j) d ∉ S := by
  have hreturn (a : D) (ha : a ∈ S) (n : ℕ) (hn : 0 < n)
      (hda : (rot ^ n) d = a)
      (hmin : ∀ j : ℕ, 0 < j → j < n → (rot ^ j) d ∉ S) :
      D39TopologicalCcwSuccessor {q | q ∈ S ∧ vertex q = vertex d} arc d a := by
    let star : Set D := {q | vertex q = vertex d}
    obtain ⟨H, hH, dir, hdir, harg, hsuccD, hs⟩ := hrot d
    have hsucc : ∀ q ∈ star, CcwSuccessor star dir q (rot q) := by
      intro q hq
      obtain ⟨f, hf⟩ := exists_ccw_successor star dir hsuccD.1 hq
      have htop : D39TopologicalCcwSuccessor star arc q f :=
        ⟨H, hH, dir, hdir, harg, hf, hs⟩
      have hqrot := hrot q
      have hstar : {p | vertex p = vertex q} = star := by
        ext p
        change vertex p = vertex q ↔ vertex p = vertex d
        rw [hq]
      rw [hstar] at hqrot
      exact (d39TopologicalCcwSuccessor_unique htop hqrot) ▸ hf
    have hpow : ∀ n : ℕ, (rot ^ n) d ∈ star := by
      intro n
      change vertex ((rot ^ n) d) = vertex d
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, hvertex, ih]
    have hc := ccw_successor_of_first_return rot star S dir d a
      hpow harg hsucc (hperiod d) hd n hn hda ha hmin
    exact ⟨H, hH, dir, (fun q hq => hdir q hq.2),
      (fun q hq p hp => harg q hq.2 p hp.2), hc, (fun q hq => hs q hq.2)⟩
  constructor
  · intro htop
    have hex : ∃ n : ℕ, 0 < n ∧ (rot ^ n) d ∈ S := by
      obtain ⟨n, hn, hn'⟩ := hperiod d
      exact ⟨n, hn, by rw [hn']; exact hd⟩
    let n := Nat.find hex
    have hn := Nat.find_spec hex
    have hmin : ∀ j : ℕ, 0 < j → j < n → (rot ^ j) d ∉ S := by
      intro j hj hjn hjS
      exact (not_le_of_gt hjn) (Nat.find_min' hex ⟨hj, hjS⟩)
    have ht := hreturn ((rot ^ n) d) hn.2 n hn.1 rfl hmin
    exact ⟨n, hn.1, (d39TopologicalCcwSuccessor_unique htop ht).symm, hmin⟩
  · rintro ⟨n, hn, hda, hmin⟩
    exact hreturn a ha n hn hda hmin

/-- Helper toward Proposition 3.9: the restricted intrinsic rotation on
any retained run-zero edge set is exactly its code first-return rotation.
This applies to both side and slice carriers, including missing edges. -/
theorem intrinsicSide_source_rotation_iff
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (K : Set ℕ) (d a : ℕ × Bool) (hd : d.1 ∈ K) (ha : a.1 ∈ K) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let A := uibotWholePlaneSourceDomain W H G hp
    let J := fun q => uibotCut2SourceDartEquiv W H h hpast hp (wholePlaneDartι W 0 q)
    intrinsicFutureRotation A (wholePlaneEdgeι W 0 '' K) (J a) (J d) ↔
      ∃ n : ℕ, 0 < n ∧
        (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[n] d = a ∧
          ∀ j : ℕ, 0 < j → j < n →
            ((kmswInfRot (shiftedStream W 0) (H.1 0) :
              (ℕ × Bool) → ℕ × Bool)^[j] d).1 ∉ K := by
  intro G A J
  let E := uibotCut2SourceDartEquiv W H h hpast hp
  let ι := wholePlaneDartι W 0
  let R := kmswInfRot (shiftedStream W 0) (H.1 0)
  let P := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  have hi : Function.Injective ι := by
    intro b c he
    exact Prod.ext (wholePlaneEdgeι_injective W 0 (congrArg Prod.fst he))
      (congrArg (fun q : WholePlaneDart W => q.2) he)
  have hperiod (q : ℕ × Bool) : ∃ n : ℕ, 0 < n ∧ (R ^ n) q = q :=
    (run_exists_pow (shiftedStream W 0) (H.1 0) q q rfl).2
  have hvertex (q : ℕ × Bool) :
      kmswLimitDartVertex (shiftedStream W 0) (R q) =
        kmswLimitDartVertex (shiftedStream W 0) q := kmswLimitDartVertex_rot _ _ q
  have htop (q : ℕ × Bool) :=
    plDrawing_toPath_rotation_topological_ccwSuccessor P q
  have hbuild (q : ℕ × Bool) (hq : q.1 ∈ K)
      (hc : ∃ n : ℕ, 0 < n ∧ (R ^ n) d = q ∧
        ∀ j : ℕ, 0 < j → j < n → ((R ^ j) d).1 ∉ K) :
      intrinsicFutureRotation A (wholePlaneEdgeι W 0 '' K) (J q) (J d) := by
    have ht := (intrinsicSide_topological_firstReturn R
      (kmswLimitDartVertex (shiftedStream W 0)) (fun q t => (P.arc q).toPath t)
      hvertex htop hperiod {q | q.1 ∈ K} d q hd hq).mpr hc
    have hqd : kmswLimitDartVertex (shiftedStream W 0) q =
        kmswLimitDartVertex (shiftedStream W 0) d := by
      obtain ⟨_, _, _, _, _, hccw, _⟩ := ht
      exact hccw.2.2.1.2
    have hv := uibotCut2SourceDartEquiv_vertex W H h hpast hp
    have hstar : E '' (ι '' {b | b.1 ∈ K ∧
        kmswLimitDartVertex (shiftedStream W 0) b =
          kmswLimitDartVertex (shiftedStream W 0) d}) =
        {b : A.E × Bool | b.1 ∈ wholePlaneEdgeι W 0 '' K ∧
          d39GeomRootVertex A.map b = d39GeomRootVertex A.map (J q)} := by
      ext b
      obtain ⟨b, rfl⟩ := E.surjective b
      rw [E.injective.mem_set_image]
      constructor
      · rintro ⟨c, ⟨hcK, hcv⟩, rfl⟩
        refine ⟨⟨c.1, hcK, rfl⟩, ?_⟩
        change d39GeomRootVertex A.map (E (ι c)) = d39GeomRootVertex A.map (E (ι q))
        erw [hv, hv, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι, hqd, hcv]
      · rintro ⟨hbK, hbv⟩
        change b.1 ∈ wholePlaneEdgeι W 0 '' K at hbK
        obtain ⟨e, he, heb⟩ := hbK
        have hb : b = ι (e, b.2) := Prod.ext heb.symm rfl
        rw [hb] at hbv ⊢
        refine ⟨(e, b.2), ⟨he, ?_⟩, rfl⟩
        change d39GeomRootVertex A.map (E (ι (e, b.2))) =
          d39GeomRootVertex A.map (E (ι q)) at hbv
        erw [hv, hv, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι, hqd] at hbv
        exact wholePlaneVertexι_injective W 0 hbv
    have ht' := intrinsicFutureCut2_topological_image ι hi _
      (fun q t => (P.arc q).toPath t) (fun q t => (G.arc q).toPath t)
      (fun q t => congrArg (fun p : Polyline => p.toPath t)
        (WholePlanePastGlueM0Restriction.restrict_arc W h hpast H q)) ht
    have ht'' := uibotCut2_source_topological_map W H h hpast hp _ ht'
    change D39TopologicalCcwSuccessor (E '' (ι '' {b | b.1 ∈ K ∧
      kmswLimitDartVertex (shiftedStream W 0) b = kmswLimitDartVertex (shiftedStream W 0) d}))
      (fun q t => intrinsicFutureDartArc A q t) (J d) (J q) at ht''
    rw [hstar] at ht''
    refine ⟨⟨q.1, hq, rfl⟩, ⟨d.1, hd, rfl⟩, ?_, ht''⟩
    change d39GeomRootVertex A.map (E (ι d)) = d39GeomRootVertex A.map (E (ι q))
    erw [hv, hv, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι, hqd]
  constructor
  · intro hr
    have hex : ∃ n : ℕ, 0 < n ∧ ((R ^ n) d).1 ∈ K := by
      obtain ⟨n, hn, hn'⟩ := hperiod d
      exact ⟨n, hn, by rw [hn']; exact hd⟩
    let n := Nat.find hex
    have hn := Nat.find_spec hex
    have hmin : ∀ j : ℕ, 0 < j → j < n → ((R ^ j) d).1 ∉ K := by
      intro j hj hjn hjK
      exact (not_le_of_gt hjn) (Nat.find_min' hex ⟨hj, hjK⟩)
    have hr' := hbuild ((R ^ n) d) hn.2 ⟨n, hn.1, rfl, hmin⟩
    have heq : J a = J ((R ^ n) d) := by
      have ht := hr'.2.2.2
      have hv : d39GeomRootVertex A.map (J ((R ^ n) d)) =
          d39GeomRootVertex A.map (J a) := hr'.2.2.1.symm.trans hr.2.2.1
      rw [hv] at ht
      exact d39TopologicalCcwSuccessor_unique hr.2.2.2 ht
    have heq' : (R ^ n) d = a := (hi (E.injective heq)).symm
    exact ⟨n, hn.1, heq', hmin⟩
  · rintro ⟨n, hn, hna, hmin⟩
    exact hbuild a ha ⟨n, hn, hna, hmin⟩

/-- Helper toward Proposition 3.9: retained geometric face succession
in any representative agrees with ambient chronological face succession.
This statement uses the actual face set, without a face-containment premise. -/
theorem intrinsicSide_code_faceNext_iff
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H))
      A.map A.root)
    (C : IntrinsicGeometricSubmap A) (d a : WholePlaneDart W) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let J := fun q => intrinsicFutureDartEquiv I (uibotCut2SourceDartEquiv W H h hpast hp q)
    intrinsicSideFaceNext A C (J d) (J a) ↔
      (∃ F : G.Face, intrinsicSideGluedFaceEquiv W H h hpast hp A I F ∈ C.faces ∧
        G.dartBorders d F) ∧ a = wholePlaneFaceSucc W H d := by
  intro G J
  let S := uibotWholePlaneSourceDomain W H G hp
  let E := uibotCut2SourceDartEquiv W H h hpast hp
  let F := intrinsicSideGluedFaceEquiv W H h hpast hp A I
  have hface (f : G.Face) :
      (∀ s, LeftAtOn (F f).val (intrinsicFutureDartArc A (J d)) s) ↔
        G.dartBorders d f := by
    rw [intrinsicSideGluedFaceEquiv_val]
    exact (intrinsicFuture_leftAtOn_map (A := S) I f.val (E d)).symm.trans
      (uibotCut2_source_face_side_iff W H h hpast hp d f)
  unfold intrinsicSideFaceNext
  apply and_congr
  · constructor
    · rintro ⟨f, hf, hb⟩
      obtain ⟨f, rfl⟩ := F.surjective f
      exact ⟨f, hf, (hface f).mp hb⟩
    · rintro ⟨f, hf, hb⟩
      exact ⟨F f, hf, (hface f).mpr hb⟩
  · have hflip : ((J d).1, !(J d).2) =
        intrinsicFutureDartEquiv I (E (wholePlaneDartFlip W d)) := by
      rw [uibotCut2SourceDartEquiv_flip]
      exact (intrinsicFutureDartEquiv_flip (A := S) (B := A) I (E d)).symm
    rw [hflip]
    have hu : I.edgeEquiv '' (Set.univ : Set S.E) = Set.univ :=
      Set.image_univ_of_surjective I.edgeEquiv.surjective
    rw [← hu]
    apply (intrinsicFutureRotation_map_iff (A := S) (B := A) I Set.univ
      (E (wholePlaneDartFlip W d)) (E a)).trans
    constructor
    · exact uibotCut2_source_rotation_inverse W H h hpast hp _ _
    · intro ha
      have hr := uibotCut2SourceDartEquiv_rotation W H h hpast hp a
      have he : wholePlaneRotation W H a = wholePlaneDartFlip W d := by
        rw [ha]
        exact (wholePlaneRotation W H).apply_symm_apply _
      rw [he] at hr
      exact hr

private theorem intrinsicSide_future_face_succ
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hpast H).Face)
    (hF : F.val ⊆ m0GeodesicAmbientRegion W H h) (d : ℕ × Bool)
    (hd : (WholePlanePastGlueDrawing.glueDrawing W h hpast H).dartBorders
      (wholePlaneDartι W 0 d) F) :
    wholePlaneFaceSucc W H (wholePlaneDartι W 0 d) =
      wholePlaneDartι W 0 (kmswInfFaceSucc (shiftedStream W 0) (H.1 0) d) := by
  let P := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  obtain ⟨F0, hF0, heq⟩ := m0CutFace_exists_runZero_face hpast F hF
  have hd0 : P.dartBorders d F0 :=
    (PLDrawing.dartBorders_congr P _ F0 F
      (WholePlanePastGlueM0Restriction.restrict_arc W h hpast H d) heq).mp hd
  obtain ⟨j, hj, _⟩ := boundedFace_orbit_is_triangle (shiftedStream W 0) (H.1 0) h F0 hF0
  apply m0Cut_faceSucc_runZero_of_triangle W H d
  exact ⟨j, (Set.ext_iff.mp hj d).mp hd0⟩

/-- Helper toward Proposition 3.9: on either geometric side the retained
face-successor relation is the exact run-zero relation used by Lemma 5.5. -/
theorem intrinsicSide_code_side_faceNext
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H))
      A.map A.root)
    (longest : Bool) (k : ℤ)
    (P : M0CutInfiniteGeodesic W H h (fun _ _ => hp _) k longest)
    (t : ThinMapSide) (d a : ℕ × Bool) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let D := m0CutData W H h (fun _ _ => hp _)
    let J := fun q => intrinsicFutureDartEquiv I
      (uibotCut2SourceDartEquiv W H h hpast hp (wholePlaneDartι W 0 q))
    let C := intrinsicGeodesicSide A (intrinsicBusemannImageCut W H G hp D A I)
      (I.h '' m0GeodesicAmbientRegion W H h) (I.vertexEquiv (D.x (k - 1)))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n))) t
    intrinsicSideFaceNext A C (J d) (J a) ↔
      (m0GeodesicSide hpast P t).faceNext d a := by
  intro G D J C
  let F := intrinsicSideGluedFaceEquiv W H h hpast hp A I
  have hfaces := intrinsicSide_code_faces W H h hpast hp A I P t
  have hmem (f : G.Face) : F f ∈ C.faces ↔
      f.val ⊆ m0GeodesicSideOpenRegion hpast P t := by
    change F '' {f : G.Face | f.val ⊆ m0GeodesicSideOpenRegion hpast P t} = C.faces at hfaces
    rw [← hfaces]
    exact F.injective.mem_set_image
  have hregion : m0GeodesicSideOpenRegion hpast P t ⊆ m0GeodesicAmbientRegion W H h := by
    cases t with
    | left => exact fun z hz => (m0GeodesicLeftOpen_subset hpast P hz).1
    | right => exact fun _ hz => hz.1
  have hi : Function.Injective (wholePlaneDartι W 0) := by
    intro b c he
    exact Prod.ext (wholePlaneEdgeι_injective W 0 (congrArg Prod.fst he))
      (congrArg (fun q : WholePlaneDart W => q.2) he)
  apply (intrinsicSide_code_faceNext_iff W H h hpast hp A I C
    (wholePlaneDartι W 0 d) (wholePlaneDartι W 0 a)).trans
  constructor
  · rintro ⟨⟨f, hf, hd⟩, ha⟩
    have hf' := (hmem f).mp hf
    refine ⟨⟨f, hd, hf'⟩, ?_⟩
    rw [intrinsicSide_future_face_succ W H h hpast f (hf'.trans hregion) d hd] at ha
    exact (hi ha).symm
  · rintro ⟨⟨f, hd, hf⟩, ha⟩
    refine ⟨⟨f, (hmem f).mpr hf, hd⟩, ?_⟩
    rw [intrinsicSide_future_face_succ W H h hpast f (hf.trans hregion) d hd, ha]

/-- Helper toward Proposition 3.9: on a finite geometric slice the
retained face-successor relation is exactly the relation used by Lemma 5.6,
with the source's least coalescence offsets and complete enclosure test. -/
theorem intrinsicSide_code_slice_faceNext
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H))
      A.map A.root)
    (longest : Bool)
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h (fun _ _ => hp _) k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hpast (fun _ _ => hp _) longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) (d e : ℕ × Bool) :
    let J := fun q => intrinsicFutureDartEquiv I
      (uibotCut2SourceDartEquiv W H h hpast hp (wholePlaneDartι W 0 q))
    intrinsicSideFaceNext A (intrinsicGeodesicSliceOfCode W H h hpast hp A I P k a b)
      (J d) (J e) ↔ (m0CutGeodesicSlice (hp := hpast) P k a b hab).faceNext d e := by
  intro J
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  let C := intrinsicGeodesicSliceOfCode W H h hpast hp A I P k a b
  let F := intrinsicSideGluedFaceEquiv W H h hpast hp A I
  have hfaces := (intrinsicGeodesicSliceOfCode_carriers W H h hpast hp A I
    P T hleft k a b hab).2.2
  have hmem (f : G.Face) : F f ∈ C.faces ↔ faceLiesBetweenSegments hpast P k a b hab f := by
    change F '' {f : G.Face | m0CutGeodesicSliceRepresentsFace hpast P k a b hab f} =
      C.faces at hfaces
    rw [← hfaces, F.injective.mem_set_image]
    exact m0CutGeodesicSlice_representsFace_iff_liesBetweenSegments hpast P T hleft k a b hab f
  have hi : Function.Injective (wholePlaneDartι W 0) := by
    intro b c he
    exact Prod.ext (wholePlaneEdgeι_injective W 0 (congrArg Prod.fst he))
      (congrArg (fun q : WholePlaneDart W => q.2) he)
  apply (intrinsicSide_code_faceNext_iff W H h hpast hp A I C
    (wholePlaneDartι W 0 d) (wholePlaneDartι W 0 e)).trans
  rw [m0CutGeodesicSlice_faceNext_iff_liesBetweenSegments hpast P T hleft k a b hab]
  constructor
  · rintro ⟨⟨f, hf, hd⟩, he⟩
    have hf' := (hmem f).mp hf
    refine ⟨f, hd, hf', ?_⟩
    rw [intrinsicSide_future_face_succ W H h hpast f hf'.1 d hd] at he
    exact (hi he).symm
  · rintro ⟨f, hd, hf, he⟩
    refine ⟨⟨f, (hmem f).mpr hf, hd⟩, ?_⟩
    rw [intrinsicSide_future_face_succ W H h hpast f hf.1 d hd, he]

/-- Helper toward Proposition 3.9: every geometric representative has
the code's first-return rotation on any retained run-zero edge set. -/
theorem intrinsicSide_code_rotation_iff
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H (WholePlanePastGlueDrawing.glueDrawing W h hpast H))
      A.map A.root)
    (K : Set ℕ) (d a : ℕ × Bool) (hd : d.1 ∈ K) (ha : a.1 ∈ K) :
    let J := fun q => intrinsicFutureDartEquiv I
      (uibotCut2SourceDartEquiv W H h hpast hp (wholePlaneDartι W 0 q))
    intrinsicFutureRotation A ((fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)) '' K)
      (J a) (J d) ↔
      ∃ n : ℕ, 0 < n ∧
        (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)^[n] d = a ∧
          ∀ j : ℕ, 0 < j → j < n →
            ((kmswInfRot (shiftedStream W 0) (H.1 0) :
              (ℕ × Bool) → ℕ × Bool)^[j] d).1 ∉ K := by
  intro J
  let S := uibotWholePlaneSourceDomain W H
    (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp
  have himage : (fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e)) '' K =
      I.edgeEquiv '' (wholePlaneEdgeι W 0 '' K) := (Set.image_image _ _ _).symm
  rw [himage]
  exact (intrinsicFutureRotation_map_iff (A := S) (B := A) I
    (wholePlaneEdgeι W 0 '' K) _ _).trans
      (intrinsicSide_source_rotation_iff W H h hpast hp K d a hd ha)

/- REMAINING COMPARISON — exact signatures, not declarations or premises.

The construction and its full relation-preservation and geometric transport
are proved above. The source rotation and both retained face-successor
comparisons are also proved. What remains in this unit is to assemble the
code-to-native cell bijections, incidence, present orientation and root
comparison with those relations into unmarked isomorphisms, and consume
them in the simultaneous event. No class equality below is claimed.

1. Deterministic side and slice class comparison:

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
    intrinsicSideSubmapClass A
      (intrinsicGeodesicSide A (intrinsicBusemannImageCut W H G hp D A I)
        (I.h '' m0GeodesicAmbientRegion W H h) (I.vertexEquiv (D.x (k - 1)))
        (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 ((P k).codePath.edge n))) t)
      (I.vertexEquiv (D.x k)) = sideSubmapClass (m0GeodesicSide hpast (P k) t)) ∧
  intrinsicSideSubmapClass A (intrinsicGeodesicSliceOfCode W H h hpast hp A I P k a b)
    (I.vertexEquiv (D.x (k - 1))) =
      sideSubmapClass (m0CutGeodesicSlice (hp := hpast) P k a b hab).

2. Simultaneous comparison with the recorded mark-forgetting readers:

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
    Nonempty (D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G) A.map A.root) ∧
    ∀ I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G) A.map A.root,
    ∀ (x : XDP) (k : ℤ) (default : GeometricSideClass),
    let P := (s x).P
    let L := fun t => intrinsicGeodesicSide A
      (intrinsicBusemannImageCut W H G hp D A I)
      (I.h '' m0GeodesicAmbientRegion W H h) (I.vertexEquiv (D.x (k - 1)))
      (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 ((P k).codePath.edge n))) t
    let C := intrinsicGeodesicSliceOfCode W H h hpast hp A I P k
      ((s x).thetaMinus k) ((s x).theta k)
    forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.1 =
      intrinsicSideSubmapClass A (L .left) (I.vertexEquiv (D.x k)) ∧
    forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).1.2 =
      intrinsicSideSubmapClass A (L .right) (I.vertexEquiv (D.x k)) ∧
    forgetMarksOptionClassValue default (uibotGeomSideSliceObservables z x k).2 =
      intrinsicSideSubmapClass A C (I.vertexEquiv (D.x (k - 1))).

3. The independent s57 native-region identification for distinct rays

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
    (pathTrace G (fun n => wholePlaneDartι W 0 (T.edge n, false))). -/

end DirectedDistances.PaperProofs.Section3
