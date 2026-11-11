/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole2

/-! Intrinsic vertex identifications and a natural-number presentation of the
finite-prefix/hatted-right gluing. No data are read from the geometric target. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: a block edge's endpoint in the disjoint union
of raw vertex identities. Allocation is imposed separately on the carrier. -/
@[expose] def rMinusCodeRawEndpoint (F : State) (M : GeometricSideSubmap)
    (b : Bool) : Sum {e : ℕ // e < F.nextEdge} M.edges → Sum ℕ ℕ
  | .inl e => .inl (if b then F.east e.val else F.west e.val)
  | .inr e => .inr (if b then M.east e.val else M.west e.val)

/-- Helper toward Lemma 5.5: only endpoints of the ordered shared-boundary
edge pairs generate cross-block vertex identifications. -/
@[expose] def rMinusCodeVertexGluing (F : State) (M : GeometricSideSubmap)
    (u v : Sum ℕ ℕ) : Prop :=
  ∃ a b, rMinusCodeEdgeGluing F M a b ∧ ∃ s : Bool,
    rMinusCodeRawEndpoint F M s a = u ∧ rMinusCodeRawEndpoint F M s b = v

/-- Helper toward Lemma 5.5: the intrinsic vertex equivalence closure.
Raw unallocated identities are excluded by `rMinusCodeVertexAllocated`. -/
@[expose] def rMinusCodeVertexSetoid (F : State) (M : GeometricSideSubmap) :
    Setoid (Sum ℕ ℕ) := Relation.EqvGen.setoid (rMinusCodeVertexGluing F M)

/-- Helper toward Lemma 5.5: the raw vertex quotient of the two code blocks. -/
abbrev RMinusCodeRawVertex (F : State) (M : GeometricSideSubmap) :=
  Quotient (rMinusCodeVertexSetoid F M)

/-- Helper toward Lemma 5.5: edge equivalence identifies the corresponding
endpoint classes; no geometric endpoint equality is assumed. -/
theorem rMinusCodeRawEndpoint_sound (F : State) (M : GeometricSideSubmap)
    (s : Bool) (a b : Sum {e : ℕ // e < F.nextEdge} M.edges)
    (hab : rMinusCodeEdgeSetoid F M a b) :
    (⟦rMinusCodeRawEndpoint F M s a⟧ : RMinusCodeRawVertex F M) =
      ⟦rMinusCodeRawEndpoint F M s b⟧ := by
  have hle : rMinusCodeEdgeSetoid F M ≤
      Setoid.ker (fun a => (⟦rMinusCodeRawEndpoint F M s a⟧ : RMinusCodeRawVertex F M)) := by
    apply Setoid.eqvGen_le
    intro a b hab
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨a, b, hab, s, rfl, rfl⟩)
  exact hle hab

/-- Helper toward Lemma 5.5: both endpoints descend to the intrinsic edge
quotient, using only the code-generated vertex identifications. -/
@[expose] def rMinusCodeEndpoint (F : State) (M : GeometricSideSubmap)
    (s : Bool) : RMinusCodeGluedEdge F M → RMinusCodeRawVertex F M :=
  Quotient.lift (fun a => ⟦rMinusCodeRawEndpoint F M s a⟧)
    (rMinusCodeRawEndpoint_sound F M s)

/-- Helper toward Lemma 5.5: precisely the allocated vertex classes are
retained; the auxiliary raw quotient introduces no additional vertices. -/
@[expose] def rMinusCodeVertexAllocated (F : State) (M : GeometricSideSubmap) :
    Set (RMinusCodeRawVertex F M) :=
  {v | (∃ a : Fin F.nextVertex, (⟦Sum.inl a.val⟧ : RMinusCodeRawVertex F M) = v) ∨
    ∃ a : M.vertices, (⟦Sum.inr a.val⟧ : RMinusCodeRawVertex F M) = v}

/-- Helper toward Lemma 5.5: the allocated intrinsic glued vertex carrier. -/
abbrev RMinusCodeGluedVertex (F : State) (M : GeometricSideSubmap) :=
  rMinusCodeVertexAllocated F M

/-- Helper toward Lemma 5.5: a natural-number identity for every intrinsic
raw vertex class. This choice depends on the two code blocks alone. -/
@[expose] noncomputable def rMinusCodeVertexId (F : State) (M : GeometricSideSubmap) :
    RMinusCodeRawVertex F M → ℕ :=
  @Encodable.encode _ (Encodable.ofCountable _)

/-- Helper toward Lemma 5.5: distinct intrinsic vertex classes keep
distinct natural-number identities. -/
theorem rMinusCodeVertexId_injective (F : State) (M : GeometricSideSubmap) :
    Function.Injective (rMinusCodeVertexId F M) :=
  @Encodable.encode_injective _ (Encodable.ofCountable _)

/-- Helper toward Lemma 5.5: a natural-number identity for each glued edge;
parallel edges are separated by the edge quotient, not by endpoints. -/
@[expose] noncomputable def rMinusCodeEdgeId (F : State) (M : GeometricSideSubmap) :
    RMinusCodeGluedEdge F M → ℕ :=
  @Encodable.encode _ (Encodable.ofCountable _)

/-- Helper toward Lemma 5.5: the natural-number edge encoding is injective. -/
theorem rMinusCodeEdgeId_injective (F : State) (M : GeometricSideSubmap) :
    Function.Injective (rMinusCodeEdgeId F M) :=
  @Encodable.encode_injective _ (Encodable.ofCountable _)

/-- Helper toward Lemma 5.5: the partial inverse of the glued edge encoding. -/
@[expose] noncomputable def rMinusCodeEdgeDecode (F : State) (M : GeometricSideSubmap) :
    ℕ → Option (RMinusCodeGluedEdge F M) :=
  @Encodable.decode _ (Encodable.ofCountable _)

/-- Helper toward Lemma 5.5: decoding an encoded geometric edge succeeds. -/
theorem rMinusCodeEdgeDecode_id (F : State) (M : GeometricSideSubmap)
    (e : RMinusCodeGluedEdge F M) :
    rMinusCodeEdgeDecode F M (rMinusCodeEdgeId F M e) = some e :=
  @Encodable.encodek _ (Encodable.ofCountable _) e

/-- Helper toward Lemma 5.5: dart identities retain the endpoint bit. -/
@[expose] noncomputable def rMinusCodeDartId (F : State) (M : GeometricSideSubmap)
    (d : RMinusCodeGluedDart F M) : ℕ × Bool := (rMinusCodeEdgeId F M d.1, d.2)

/-- Helper toward Lemma 5.5: the natural-number dart presentation is faithful. -/
theorem rMinusCodeDartId_injective (F : State) (M : GeometricSideSubmap) :
    Function.Injective (rMinusCodeDartId F M) := by
  intro a b hab
  exact Prod.ext (rMinusCodeEdgeId_injective F M (congrArg Prod.fst hab))
    (congrArg (fun z : ℕ × Bool => z.2) hab)

/-- Helper toward Lemma 5.5: endpoint labels on the natural-number edge
presentation. The value outside the edge carrier is unused by incidence. -/
@[expose] noncomputable def rMinusCodeEndpointId (F : State) (M : GeometricSideSubmap)
    (s : Bool) (e : ℕ) : ℕ :=
  ((rMinusCodeEdgeDecode F M e).map
    (fun e => rMinusCodeVertexId F M (rMinusCodeEndpoint F M s e))).getD 0

/-- Helper toward Lemma 5.5: the encoded endpoints are precisely the
descended intrinsic endpoints, with no finiteness or incidence premise. -/
theorem rMinusCodeEndpointId_id (F : State) (M : GeometricSideSubmap)
    (s : Bool) (e : RMinusCodeGluedEdge F M) :
    rMinusCodeEndpointId F M s (rMinusCodeEdgeId F M e) =
      rMinusCodeVertexId F M (rMinusCodeEndpoint F M s e) := by
  simp only [rMinusCodeEndpointId, rMinusCodeEdgeDecode_id, Option.map_some,
    Option.getD_some]

/-- Helper toward Lemma 5.5: presence is the union of directed edge
representatives from the two blocks, after identification. -/
@[expose] def rMinusCodeEdgePresent (F : State) (M : GeometricSideSubmap)
    (e : RMinusCodeGluedEdge F M) : Prop :=
  (∃ a : {e : ℕ // e < F.nextEdge}, F.present a.val = true ∧
    (⟦Sum.inl a⟧ : RMinusCodeGluedEdge F M) = e) ∨
  ∃ a : M.edges, a.val ∈ M.present ∧
    (⟦Sum.inr a⟧ : RMinusCodeGluedEdge F M) = e

/-- Helper toward Lemma 5.5: a presentation from the two realized code
blocks and a constructed rotation permutation alone. The guards merely
totalize marking functions on arbitrary block inputs; on KMSW/coherent
blocks they always succeed, as `rMinusDecodedSide_eq_ofBlocks` proves.
The permutation is data, not a geometric rotation-identification premise. -/
@[expose] noncomputable def rMinusDecodedSideOfBlocks (F : State)
    (M : GeometricSideSubmap) (R : Equiv.Perm (RMinusCodeGluedDart F M)) :
    GeometricSideSubmap where
  vertices := Set.range (fun v : RMinusCodeGluedVertex F M => rMinusCodeVertexId F M v.val)
  edges := Set.range (rMinusCodeEdgeId F M)
  west := rMinusCodeEndpointId F M false
  east := rMinusCodeEndpointId F M true
  present := {i | ∃ e, rMinusCodeEdgeId F M e = i ∧ rMinusCodeEdgePresent F M e}
  rotation := fun d e => ∃ a b : RMinusCodeGluedDart F M,
    rMinusCodeDartId F M a = d ∧ rMinusCodeDartId F M b = e ∧ R a = b
  faceNext := fun d e => ∃ a b : RMinusCodeGluedDart F M,
    rMinusCodeDartId F M a = d ∧ rMinusCodeDartId F M b = e ∧ rMinusCodeFaceNext F M a b
  root := rMinusCodeVertexId F M ⟦Sum.inr M.root⟧
  boundary := fun i =>
    if hi : i < (F.LL ++ F.LR).length then
      if he : (F.LL ++ F.LR)[i] < F.nextEdge then
        rMinusCodeDartId F M (rMinusCodePrefixDart F M (⟨(F.LL ++ F.LR)[i], he⟩, false))
      else (0, false)
    else
      let j := i - (F.LL ++ F.LR).length + (F.active :: F.UR).length
      if he : (M.boundary j).1 ∈ M.edges then
        rMinusCodeDartId F M (rMinusCodeHattedDart F M ⟨M.boundary j, he⟩)
      else (0, false)
  seam := fun i =>
    if he : (M.seam i).1 ∈ M.edges then
      rMinusCodeDartId F M (rMinusCodeHattedDart F M ⟨M.seam i, he⟩)
    else (0, false)

section DecodedSide

variable (w : ℕ → Fin 3) (n : ℕ) {x : XDP}
  (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)

local notation "F" => kmswStage w n
local notation "M" => geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime ThinMapSide.right q

/-- Helper toward Lemma 5.5: the exterior boundary is the finite lower
word followed by the unattached hatted boundary tail. -/
@[expose] noncomputable def rMinusDecodedBoundary (i : ℕ) : RMinusCodeGluedDart F M :=
  if hi : i < ((F).LL ++ (F).LR).length then
    rMinusCodePrefixDart F M (⟨((F).LL ++ (F).LR)[i], by
      apply (kmswStage_boundary_ids_lt_nextEdge w n).2
      have hm := List.getElem_mem hi
      simp only [List.mem_append] at hm ⊢
      tauto⟩, false)
  else
    let j := i - ((F).LL ++ (F).LR).length + ((F).active :: (F).UR).length
    rMinusCodeHattedDart F M ⟨(M).boundary j, rMinus_hatted_boundary_mem x q j⟩

/-- Helper toward Lemma 5.5: the seam is read exclusively from the hatted
right block and retains its index and endpoint bit. -/
@[expose] noncomputable def rMinusDecodedSeam (i : ℕ) : RMinusCodeGluedDart F M :=
  rMinusCodeHattedDart F M ⟨(M).seam i, by
    change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
      renewalTime_positiveSuccessTime .right q j
    rw [iUnion_geometricAncestorEdges]
    exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i⟩

/-- Helper toward Lemma 5.5: the complete code-built nonpositive right
side. The vertex/edge encodings depend only on the two blocks; rotation is
the proved adjusted splice candidate, faces are the retained block faces,
and the exterior boundary is the lower word followed by the hatted tail.
The stream is used only to evaluate the finite prefix and its rotation.
No field is defined from `m0GeodesicSide` or a geometric gluing map. -/
@[expose] noncomputable def rMinusDecodedSide : GeometricSideSubmap where
  vertices := Set.range (fun v : RMinusCodeGluedVertex F M => rMinusCodeVertexId F M v.val)
  edges := Set.range (rMinusCodeEdgeId F M)
  west := rMinusCodeEndpointId F M false
  east := rMinusCodeEndpointId F M true
  present := {i | ∃ e, rMinusCodeEdgeId F M e = i ∧ rMinusCodeEdgePresent F M e}
  rotation := fun d e => ∃ a b : RMinusCodeGluedDart F M,
    rMinusCodeDartId F M a = d ∧ rMinusCodeDartId F M b = e ∧
      rMinusCodeInitialAdjustedRotation w n q a = b
  faceNext := fun d e => ∃ a b : RMinusCodeGluedDart F M,
    rMinusCodeDartId F M a = d ∧ rMinusCodeDartId F M b = e ∧
      rMinusCodeFaceNext F M a b
  root := rMinusCodeVertexId F M ⟦Sum.inr (M).root⟧
  boundary := fun i => rMinusCodeDartId F M (rMinusDecodedBoundary w n q i)
  seam := fun i => rMinusCodeDartId F M (rMinusDecodedSeam w n q i)

/-- Helper toward Lemma 5.5: the specialized decoder depends only on the
finite state, the hatted block and the proved adjusted splice permutation.
In particular the permanent geometric evaluation maps play no role in it. -/
theorem rMinusDecodedSide_eq_ofBlocks :
    rMinusDecodedSide w n q = rMinusDecodedSideOfBlocks F M
      (rMinusCodeInitialAdjustedRotation w n q) := by
  have hb : (fun i => rMinusCodeDartId F M (rMinusDecodedBoundary w n q i)) =
      (rMinusDecodedSideOfBlocks F M (rMinusCodeInitialAdjustedRotation w n q)).boundary := by
    funext i
    by_cases hi : i < ((F).LL ++ (F).LR).length
    · have he : ((F).LL ++ (F).LR)[i] < (F).nextEdge := by
        apply (kmswStage_boundary_ids_lt_nextEdge w n).2
        have hm := List.getElem_mem hi
        simp only [List.mem_append] at hm ⊢
        tauto
      simp only [rMinusDecodedBoundary, rMinusDecodedSideOfBlocks,
        dite_eq_left hi, dite_eq_left he]
    · simp only [rMinusDecodedBoundary, rMinusDecodedSideOfBlocks, dite_eq_right hi,
        dite_eq_left (rMinus_hatted_boundary_mem x q _)]
  have hs : (fun i => rMinusCodeDartId F M (rMinusDecodedSeam w n q i)) =
      (rMinusDecodedSideOfBlocks F M (rMinusCodeInitialAdjustedRotation w n q)).seam := by
    funext i
    have he : ((M).seam i).1 ∈ (M).edges := by
      change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime renewalTime_positiveSuccessTime .right q j
      rw [iUnion_geometricAncestorEdges]
      exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i
    simp only [rMinusDecodedSeam, rMinusDecodedSideOfBlocks, dite_eq_left he]
  unfold rMinusDecodedSide rMinusDecodedSideOfBlocks
  congr 1

/-- Helper toward Lemma 5.5: every descended endpoint of a decoded edge
is an allocated vertex, including the endpoints of missing edges. -/
theorem rMinusCodeEndpoint_allocated (s : Bool) (e : RMinusCodeGluedEdge F M) :
    rMinusCodeEndpoint F M s e ∈ rMinusCodeVertexAllocated F M := by
  refine Quotient.inductionOn e ?_
  intro a
  cases a with
  | inl a =>
    have he := kmswStage_endpoints_lt_nextVertex w n a.val a.property
    cases s
    · exact Or.inl ⟨⟨(F).west a.val, he.1⟩, rfl⟩
    · exact Or.inl ⟨⟨(F).east a.val, he.2⟩, rfl⟩
  | inr a =>
    have he := geometricSideSubmap_endpoints x renewalTime
      renewalTime_positiveSuccessTime .right q a.val a.property
    cases s
    · exact Or.inr ⟨⟨(M).west a.val, he.1⟩, rfl⟩
    · exact Or.inr ⟨⟨(M).east a.val, he.2⟩, rfl⟩

/-- Helper toward Lemma 5.5: both geometric endpoints of every decoded
edge belong to the decoded vertex carrier, including missing edges. -/
theorem rMinusDecodedSide_endpoints (e : ℕ)
    (he : e ∈ (rMinusDecodedSide w n q).edges) :
    (rMinusDecodedSide w n q).west e ∈ (rMinusDecodedSide w n q).vertices ∧
      (rMinusDecodedSide w n q).east e ∈ (rMinusDecodedSide w n q).vertices := by
  obtain ⟨a, rfl⟩ := he
  constructor
  · exact ⟨⟨rMinusCodeEndpoint F M false a, rMinusCodeEndpoint_allocated w n q false a⟩,
      (rMinusCodeEndpointId_id F M false a).symm⟩
  · exact ⟨⟨rMinusCodeEndpoint F M true a, rMinusCodeEndpoint_allocated w n q true a⟩,
      (rMinusCodeEndpointId_id F M true a).symm⟩

/-- Helper toward Lemma 5.5: all indexed exterior boundary darts are
geometric decoded edges, including the finite lower-boundary segment. -/
theorem rMinusDecodedSide_boundary_mem (i : ℕ) :
    ((rMinusDecodedSide w n q).boundary i).1 ∈ (rMinusDecodedSide w n q).edges :=
  ⟨(rMinusDecodedBoundary w n q i).1, rfl⟩

/-- Helper toward Lemma 5.5: every indexed seam dart is a geometric
decoded edge, with its original hatted index. -/
theorem rMinusDecodedSide_seam_mem (i : ℕ) :
    ((rMinusDecodedSide w n q).seam i).1 ∈ (rMinusDecodedSide w n q).edges :=
  ⟨(rMinusDecodedSeam w n q i).1, rfl⟩

/-- Helper toward Lemma 5.5: directed presence never introduces an edge
outside the decoded geometric carrier. -/
theorem rMinusDecodedSide_present_subset_edges :
    (rMinusDecodedSide w n q).present ⊆ (rMinusDecodedSide w n q).edges := by
  rintro e ⟨a, ha, _⟩
  exact ⟨a, ha⟩

/-- Helper toward Lemma 5.5: the decoded root is an allocated hatted
source vertex, rather than an auxiliary unallocated quotient class. -/
theorem rMinusDecodedSide_root_mem :
    (rMinusDecodedSide w n q).root ∈ (rMinusDecodedSide w n q).vertices := by
  have hr : (M).root ∈ (M).vertices := by
    change 0 ∈ ⋃ j, geometricAncestorVertices x renewalTime
      renewalTime_positiveSuccessTime .right q j
    rw [iUnion_geometricAncestorVertices]
    exact source_mem_sideVertices _
      (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)
      (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q) .right
  exact ⟨⟨⟦Sum.inr (M).root⟧, Or.inr ⟨⟨(M).root, hr⟩, rfl⟩⟩, rfl⟩

/-- Helper toward Lemma 5.5: the natural-number vertex presentation is
equivalent to exactly the allocated intrinsic quotient. -/
@[expose] noncomputable def rMinusDecodedVertexEquiv :
    RMinusCodeGluedVertex F M ≃ (rMinusDecodedSide w n q).vertices :=
  Equiv.ofInjective (fun v : RMinusCodeGluedVertex F M => rMinusCodeVertexId F M v.val)
    (fun _ _ hab => Subtype.ext (rMinusCodeVertexId_injective F M hab))

/-- Helper toward Lemma 5.5: both darts of every encoded geometric edge
are equivalent to the intrinsic edge-class/endpoint-bit carrier. -/
@[expose] noncomputable def rMinusDecodedDartEquiv :
    RMinusCodeGluedDart F M ≃ {d : ℕ × Bool // d.1 ∈ (rMinusDecodedSide w n q).edges} :=
  Equiv.ofBijective
    (fun d => ⟨rMinusCodeDartId F M d, ⟨d.1, rfl⟩⟩)
    ⟨fun _ _ hab => rMinusCodeDartId_injective F M (congrArg Subtype.val hab), by
      intro d
      obtain ⟨e, he⟩ := d.property
      exact ⟨(e, d.val.2), Subtype.ext (Prod.ext he rfl)⟩⟩

/-- Helper toward Lemma 5.5: all decoded cells have exactly the intrinsic
allocated vertex and dart carriers. This does not assert geometric gluing. -/
@[expose] noncomputable def rMinusDecodedCellEquiv :
    Sum (RMinusCodeGluedVertex F M) (RMinusCodeGluedDart F M) ≃
      GeometricSideCell (rMinusDecodedSide w n q) :=
  Equiv.sumCongr (rMinusDecodedVertexEquiv w n q) (rMinusDecodedDartEquiv w n q)

/-- Helper toward Lemma 5.5: the vertex equivalence has the chosen code ID. -/
theorem rMinusDecodedVertexEquiv_val (v : RMinusCodeGluedVertex F M) :
    (rMinusDecodedVertexEquiv w n q v).val = rMinusCodeVertexId F M v.val := rfl

/-- Helper toward Lemma 5.5: the dart equivalence has the chosen code ID. -/
theorem rMinusDecodedDartEquiv_val (d : RMinusCodeGluedDart F M) :
    (rMinusDecodedDartEquiv w n q d).val = rMinusCodeDartId F M d := rfl

/-- Helper toward Lemma 5.5: the full marked relation on intrinsic code
cells, before their natural-number presentation. -/
@[expose] noncomputable def rMinusCodeWholeRelation : TruncationRelation →
    Sum (RMinusCodeGluedVertex F M) (RMinusCodeGluedDart F M) →
    Sum (RMinusCodeGluedVertex F M) (RMinusCodeGluedDart F M) → Prop
  | .vertex, .inl _, _ => True
  | .root, .inl v, _ => v.val = ⟦Sum.inr (M).root⟧
  | .incident, .inr d, .inl v => rMinusCodeEndpoint F M d.2 d.1 = v.val
  | .opposite, .inr d, .inr e => (d.1, !d.2) = e
  | .oriented, .inr d, _ => rMinusCodeEdgePresent F M d.1 ∧ d.2 = false
  | .rotation, .inr d, .inr e => rMinusCodeInitialAdjustedRotation w n q d = e
  | .faceNext, .inr d, .inr e => rMinusCodeFaceNext F M d e
  | .boundary i, .inr d, _ => rMinusDecodedBoundary w n q i = d
  | .seam i, .inr d, _ => rMinusDecodedSeam w n q i = d
  | _, _, _ => False

/-- Helper toward Lemma 5.5: the complete natural-number presentation
preserves and reflects every relation tag of the intrinsic code gluing. -/
theorem rMinusDecodedCellEquiv_relation_iff (t : TruncationRelation)
    (u v : Sum (RMinusCodeGluedVertex F M) (RMinusCodeGluedDart F M)) :
    rMinusCodeWholeRelation w n q t u v ↔
      geometricSideRelation (rMinusDecodedSide w n q) t
        (rMinusDecodedCellEquiv w n q u) (rMinusDecodedCellEquiv w n q v) := by
  cases t <;> cases u <;> cases v <;>
    simp only [rMinusCodeWholeRelation, geometricSideRelation, rMinusDecodedCellEquiv,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
  all_goals simp only [rMinusDecodedVertexEquiv_val, rMinusDecodedDartEquiv_val]
  all_goals try dsimp only [rMinusDecodedSide, Set.mem_ofPred_eq]
  all_goals try exact (rMinusCodeVertexId_injective F M).eq_iff.symm
  all_goals try exact (rMinusCodeDartId_injective F M).eq_iff.symm
  all_goals try simp only [(rMinusCodeDartId_injective F M).eq_iff]
  case incident.inr.inl d v =>
    cases hb : d.2 <;>
      simpa only [rMinusCodeDartId, hb, Bool.false_eq_true, ↓reduceIte,
        rMinusCodeEndpointId_id] using (rMinusCodeVertexId_injective F M).eq_iff.symm
  case oriented.inr.inl d v =>
    change (rMinusCodeEdgePresent F M d.1 ∧ d.2 = false) ↔
      (∃ e, rMinusCodeEdgeId F M e = rMinusCodeEdgeId F M d.1 ∧
        rMinusCodeEdgePresent F M e) ∧ d.2 = false
    simp only [(rMinusCodeEdgeId_injective F M).eq_iff, exists_eq_left]
  case oriented.inr.inr d e =>
    change (rMinusCodeEdgePresent F M d.1 ∧ d.2 = false) ↔
      (∃ e, rMinusCodeEdgeId F M e = rMinusCodeEdgeId F M d.1 ∧
        rMinusCodeEdgePresent F M e) ∧ d.2 = false
    simp only [(rMinusCodeEdgeId_injective F M).eq_iff, exists_eq_left]
  case rotation.inr.inr d e =>
    constructor
    · intro h; exact ⟨d, e, rfl, rfl, h⟩
    · rintro ⟨a, b, ha, hb, h⟩
      exact ha ▸ hb ▸ h
  case faceNext.inr.inr d e =>
    constructor
    · intro h; exact ⟨d, e, rfl, rfl, h⟩
    · rintro ⟨a, b, ha, hb, h⟩
      exact ha ▸ hb ▸ h

end DecodedSide

section GeometricIdentification

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "w" => shiftedStream W 0
local notation "n" => boundaryHitTime w h k
local notation "F" => kmswStage w n
local notation "q" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.right q
local notation "VH" => boundaryGluingHatVertexMap W h k hτ
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ

/-- Helper toward Lemma 5.5: geometric evaluation of raw code vertices,
used only to prove fidelity and never to define the decoded side. -/
@[expose] noncomputable def rMinusCodeRawVertexImage : Sum ℕ ℕ → ℕ :=
  Sum.elim id VH

/-- Helper toward Lemma 5.5: each block endpoint has the same evaluation
as its permanent run-zero dart endpoint. -/
theorem rMinusCodeRawEndpoint_image (s : Bool)
    (a : Sum {e : ℕ // e < (F).nextEdge} (Q).edges) :
    rMinusCodeRawVertexImage hτ (rMinusCodeRawEndpoint F Q s a) =
      kmswLimitDartVertex w
        (Sum.elim Subtype.val (fun e => EH e.val) a, s) := by
  cases a with
  | inl a =>
    have he := edge_endpoints_eq w a.property
    cases s <;> simp only [rMinusCodeRawEndpoint, rMinusCodeRawVertexImage,
      Sum.elim_inl, id_eq, Bool.false_eq_true, ↓reduceIte, kmswLimitDartVertex,
      he.1, he.2]
  | inr a =>
    have he := boundaryGluing_hat_edge_endpoints W h k hτ a.val
    change VH (if s then edgeEast
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) a.val
      else edgeWest (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) a.val) = _
    rw [boundaryGluing_decoded_stream W h k hτ]
    cases s
    · exact he.1.symm
    · exact he.2.symm

include hfin in
/-- Helper toward Lemma 5.5: every code-generated vertex identification
is a valid geometric identification. -/
theorem rMinusCodeVertexSetoid_le_ker :
    rMinusCodeVertexSetoid F Q ≤ Setoid.ker (rMinusCodeRawVertexImage hτ) := by
  apply Setoid.eqvGen_le
  rintro u v ⟨a, b, hab, s, rfl, rfl⟩
  change rMinusCodeRawVertexImage hτ (rMinusCodeRawEndpoint F Q s a) =
    rMinusCodeRawVertexImage hτ (rMinusCodeRawEndpoint F Q s b)
  rw [rMinusCodeRawEndpoint_image hτ hqMode, rMinusCodeRawEndpoint_image hτ hqMode]
  have he : rMinusBlockEdgeImage hτ hqMode a = rMinusBlockEdgeImage hτ hqMode b := by
    apply (rMinusCodeEdgeSetoid_eq_ker hτ hqMode hfin).le
    exact Relation.EqvGen.rel _ _ hab
  exact congrArg (fun e => kmswLimitDartVertex w (e, s)) he

include hfin in
/-- Helper toward Lemma 5.5: the geometric evaluation descends through
the intrinsic vertex quotient; it is a verification map, not decoder data. -/
@[expose] noncomputable def rMinusCodeVertexImage : RMinusCodeRawVertex F Q → ℕ :=
  Quotient.lift (rMinusCodeRawVertexImage hτ) (fun _ _ hab =>
    rMinusCodeVertexSetoid_le_ker hτ hqMode hfin hab)

include hfin hk in
/-- Helper toward Lemma 5.5: a shared allocated vertex is an endpoint
of the ordered attachment interface, including both terminal endpoints. -/
theorem rMinusCode_shared_vertex_interface
    (a : boundaryGluingPrefixVertices W h k) (b : (Q).vertices)
    (hab : a.val = VH b.val) :
    ∃ d : StageDart ((F).active :: (F).UR).length,
      a.val = stageEndpoint F (rMinusPrefixBoundaryDart w n d) := by
  by_contra hn
  have haway : ∀ d : StageDart ((F).active :: (F).UR).length,
      a.val ≠ stageEndpoint F (rMinusPrefixBoundaryDart w n d) := by
    intro d hd
    exact hn ⟨d, hd⟩
  obtain ⟨e, he, hw⟩ := (geometricSideSubmap_mem_vertices_iff_west
    (if longest then XDP.ldp else XDP.sdp) q .right b.val).mp b.property
  apply rMinus_off_interface_no_hatted hτ hqMode hfin hk a.val a.property haway ⟨(e, false), he⟩
  have hv := rMinusCodeRawEndpoint_image hτ hqMode false (Sum.inr ⟨e, he⟩)
  change VH ((Q).west e) = kmswLimitDartVertex w (EH e, false) at hv
  exact hv.symm.trans ((congrArg VH hw).trans hab.symm)

include hfin hk in
/-- Helper toward Lemma 5.5: all cross-block geometric vertex equalities
are generated by the code's shared-boundary endpoint identifications. -/
theorem rMinusCode_shared_vertex_eq
    (a : boundaryGluingPrefixVertices W h k) (b : (Q).vertices)
    (hab : a.val = VH b.val) :
    (⟦Sum.inl a.val⟧ : RMinusCodeRawVertex F Q) = ⟦Sum.inr b.val⟧ := by
  obtain ⟨⟨i, s⟩, hv⟩ := rMinusCode_shared_vertex_interface hτ hqMode hfin hk a b hab
  let p := rMinusPrefixBoundaryDart w n (i, s)
  let A : Sum {e : ℕ // e < (F).nextEdge} (Q).edges := .inl ⟨p.1.val, p.1.isLt⟩
  let B : Sum {e : ℕ // e < (F).nextEdge} (Q).edges :=
    .inr ⟨((Q).boundary i.val).1, rMinus_hatted_boundary_mem _ q i.val⟩
  have hAB : rMinusCodeEdgeGluing F Q A B :=
    ⟨i.val, List.getElem?_eq_getElem i.isLt, rfl⟩
  have hA : rMinusCodeRawEndpoint F Q s A = Sum.inl a.val :=
    congrArg Sum.inl hv.symm
  let c := if s then (Q).east ((Q).boundary i.val).1 else (Q).west ((Q).boundary i.val).1
  have hgen : rMinusCodeVertexSetoid F Q
      (rMinusCodeRawEndpoint F Q s A) (rMinusCodeRawEndpoint F Q s B) :=
    Relation.EqvGen.rel _ _ ⟨A, B, hAB, s, rfl, rfl⟩
  have hc : VH c = VH b.val := by
    have hh := rMinusCodeVertexSetoid_le_ker hτ hqMode hfin hgen
    change rMinusCodeRawVertexImage hτ (rMinusCodeRawEndpoint F Q s A) = VH c at hh
    rw [hA] at hh
    exact hh.symm.trans hab
  have hc' : c = b.val := boundaryGluingHatVertexMap_injective W h k hτ hc
  have hB : rMinusCodeRawEndpoint F Q s B = Sum.inr b.val := congrArg Sum.inr hc'
  rw [hA, hB] at hgen
  exact Quotient.sound hgen

/-- Helper toward Lemma 5.5: each allocated block vertex has its
intrinsic code class, without making any geometric identification. -/
@[expose] noncomputable def rMinusBlockVertexCode : RMinusBlockVertex (h := h) hqMode →
    RMinusCodeGluedVertex F Q
  | .inl a => ⟨⟦Sum.inl a.val⟧, Or.inl ⟨⟨a.val, a.property⟩, rfl⟩⟩
  | .inr b => ⟨⟦Sum.inr b.val⟧, Or.inr ⟨b, rfl⟩⟩

include hfin hk in
/-- Helper toward Lemma 5.5: geometric quotient equality is reflected
by the intrinsic allocated vertex classes, on all four block branches. -/
theorem rMinusBlockVertexCode_sound (a b : RMinusBlockVertex (h := h) hqMode)
    (hab : rMinusBlockVertexImage hτ hqMode a = rMinusBlockVertexImage hτ hqMode b) :
    rMinusBlockVertexCode hqMode a = rMinusBlockVertexCode hqMode b := by
  apply Subtype.ext
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg (fun v => (⟦Sum.inl v⟧ : RMinusCodeRawVertex F Q)) hab
    | inr b => exact rMinusCode_shared_vertex_eq hτ hqMode hfin hk a b hab
  | inr a =>
    cases b with
    | inl b => exact (rMinusCode_shared_vertex_eq hτ hqMode hfin hk b a hab.symm).symm
    | inr b =>
      exact congrArg (fun v => (⟦Sum.inr v⟧ : RMinusCodeRawVertex F Q))
        (boundaryGluingHatVertexMap_injective W h k hτ hab)

include hfin hk in
/-- Helper toward Lemma 5.5: the actual glued vertices map to exactly
the allocated code vertex classes. -/
@[expose] noncomputable def rMinusGluedToCodeVertex : RMinusGluedVertex hτ hqMode →
    RMinusCodeGluedVertex F Q :=
  Quotient.lift (rMinusBlockVertexCode hqMode)
    (rMinusBlockVertexCode_sound hτ hqMode hfin hk)

include hfin hk in
/-- Helper toward Lemma 5.5: evaluating a transported vertex class gives
its original permanent vertex identity. -/
theorem rMinusGluedToCodeVertex_image (v : RMinusGluedVertex hτ hqMode) :
    rMinusCodeVertexImage hτ hqMode hfin (rMinusGluedToCodeVertex hτ hqMode hfin hk v).val =
      Setoid.kerLift (rMinusBlockVertexImage hτ hqMode) v := by
  refine Quotient.inductionOn v ?_
  intro a
  cases a <;> rfl

include hfin hk in
/-- Helper toward Lemma 5.5: the intrinsic vertex gluing has neither
additional geometric identifications nor omitted allocated vertices. -/
theorem rMinusGluedToCodeVertex_bijective :
    Function.Bijective (rMinusGluedToCodeVertex hτ hqMode hfin hk) := by
  constructor
  · intro a b hab
    apply (Setoid.kerLift_injective (rMinusBlockVertexImage hτ hqMode))
    rw [← rMinusGluedToCodeVertex_image hτ hqMode hfin hk a,
      ← rMinusGluedToCodeVertex_image hτ hqMode hfin hk b, hab]
  · intro v
    rcases v.property with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact ⟨⟦Sum.inl ⟨a.val, a.isLt⟩⟧, Subtype.ext ha⟩
    · exact ⟨⟦Sum.inr b⟧, Subtype.ext hb⟩

include hfin hk in
/-- Helper toward Lemma 5.5: equivalence of the intrinsic and actual
glued vertex carriers, proved from their exact boundary identifications. -/
@[expose] noncomputable def rMinusCodeToGluedVertexEquiv :
    RMinusCodeGluedVertex F Q ≃ RMinusGluedVertex hτ hqMode :=
  (Equiv.ofBijective (rMinusGluedToCodeVertex hτ hqMode hfin hk)
    (rMinusGluedToCodeVertex_bijective hτ hqMode hfin hk)).symm

include hfin hk in
/-- Helper toward Lemma 5.5: the intrinsic-to-geometric vertex equivalence
commutes with the block embeddings. -/
theorem rMinusCodeToGluedVertexEquiv_block (a : RMinusBlockVertex (h := h) hqMode) :
    rMinusCodeToGluedVertexEquiv hτ hqMode hfin hk (rMinusBlockVertexCode hqMode a) = ⟦a⟧ :=
  (rMinusCodeToGluedVertexEquiv hτ hqMode hfin hk).apply_symm_apply ⟦a⟧

include hfin hk in
/-- Helper toward Lemma 5.5: the vertex equivalence preserves permanent
identities under the geometric evaluation used for verification. -/
theorem rMinusCodeToGluedVertexEquiv_image (v : RMinusCodeGluedVertex F Q) :
    Setoid.kerLift (rMinusBlockVertexImage hτ hqMode)
      (rMinusCodeToGluedVertexEquiv hτ hqMode hfin hk v) =
        rMinusCodeVertexImage hτ hqMode hfin v.val := by
  have hh := rMinusGluedToCodeVertex_image hτ hqMode hfin hk
    (rMinusCodeToGluedVertexEquiv hτ hqMode hfin hk v)
  change rMinusCodeVertexImage hτ hqMode hfin
    ((rMinusCodeToGluedVertexEquiv hτ hqMode hfin hk).symm
      (rMinusCodeToGluedVertexEquiv hτ hqMode hfin hk v)).val = _ at hh
  rw [Equiv.symm_apply_apply] at hh
  exact hh.symm

include hfin hk in
/-- Helper toward Lemma 5.5: the intrinsic vertex evaluation is injective
on its allocated carrier, as certified by the geometric quotient equivalence. -/
theorem rMinusCodeVertexImage_injective :
    Function.Injective (fun v : RMinusCodeGluedVertex F Q =>
      rMinusCodeVertexImage hτ hqMode hfin v.val) := by
  intro a b hab
  apply (rMinusCodeToGluedVertexEquiv hτ hqMode hfin hk).injective
  apply Setoid.kerLift_injective (rMinusBlockVertexImage hτ hqMode)
  rwa [rMinusCodeToGluedVertexEquiv_image, rMinusCodeToGluedVertexEquiv_image]

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the complete decoded cell carrier is
equivalent to the previously verified geometric glued cell carrier. -/
@[expose] noncomputable def rMinusDecodedToGluedCellEquiv :
    GeometricSideCell (rMinusDecodedSide w n q) ≃
      Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode) :=
  (rMinusDecodedCellEquiv w n q).symm.trans
    (Equiv.sumCongr (rMinusCodeToGluedVertexEquiv hτ hqMode hfin hk)
      (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk))

include hfin hk in
/-- Helper toward Lemma 5.5: incidence commutes with intrinsic-to-geometric
gluing on both prefix and hatted edge representatives. -/
theorem rMinusCodeToGlued_endpoint (d : RMinusCodeGluedDart F Q) :
    rMinusGluedToCodeVertex hτ hqMode hfin hk
      (rMinusGluedDartEndpoint hτ hqMode
        (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d)) =
      ⟨rMinusCodeEndpoint F Q d.2 d.1, rMinusCodeEndpoint_allocated w n q d.2 d.1⟩ := by
  rcases d with ⟨e, s⟩
  refine Quotient.inductionOn e ?_
  intro a
  cases a with
  | inl a =>
    rw [show (⟦Sum.inl a⟧, s) = rMinusCodePrefixDart F Q (⟨a.val, a.property⟩, s) from rfl,
      rMinusCodeToGluedDartEquiv_prefix]
    cases s <;> rfl
  | inr a =>
    rw [show (⟦Sum.inr a⟧, s) = rMinusCodeHattedDart F Q ⟨(a.val, s), a.property⟩ from rfl,
      rMinusCodeToGluedDartEquiv_hatted]
    cases s <;> rfl

/-- Helper toward Lemma 5.5: the intrinsic code dart of a block dart. -/
@[expose] noncomputable def rMinusBlockDartCode : RMinusBlockDart (h := h) hqMode →
    RMinusCodeGluedDart F Q
  | .inl a => rMinusCodePrefixDart F Q (⟨a.val.1, a.property⟩, a.val.2)
  | .inr a => rMinusCodeHattedDart F Q a

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: code-to-geometric dart transport commutes
with both original block embeddings. -/
theorem rMinusBlockDartCode_equiv (a : RMinusBlockDart (h := h) hqMode) :
    rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusBlockDartCode hqMode a) = ⟦a⟧ := by
  cases a with
  | inl a => exact rMinusCodeToGluedDartEquiv_prefix hτ hp P hqMode Tpath hfin hleft hk _
  | inr a => exact rMinusCodeToGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk _

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the intrinsic presence union preserves and
reflects the directed forward darts of the geometric gluing. -/
theorem rMinusCodeToGlued_oriented (d : RMinusCodeGluedDart F Q) :
    (rMinusCodeEdgePresent F Q d.1 ∧ d.2 = false) ↔
      rMinusGluedDartOriented hτ hqMode
        (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d) := by
  let E := rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  constructor
  · rintro ⟨(⟨a, ha, he⟩ | ⟨a, ha, he⟩), hs⟩
    · let b : RMinusBlockDart (h := h) hqMode := .inl ⟨(a.val, false), a.property⟩
      refine ⟨b, ?_, ha, rfl⟩
      rw [← rMinusBlockDartCode_equiv hτ hp P hqMode Tpath hfin hleft hk]
      exact congrArg E (Prod.ext he hs.symm)
    · let b : RMinusBlockDart (h := h) hqMode := .inr ⟨(a.val, false), a.property⟩
      refine ⟨b, ?_, ha, rfl⟩
      rw [← rMinusBlockDartCode_equiv hτ hp P hqMode Tpath hfin hleft hk]
      exact congrArg E (Prod.ext he hs.symm)
  · rintro ⟨a, ha, hor⟩
    have he : rMinusBlockDartCode hqMode a = d := by
      apply E.injective
      exact (rMinusBlockDartCode_equiv hτ hp P hqMode Tpath hfin hleft hk a).trans ha
    rw [← he]
    cases a with
    | inl a => exact ⟨Or.inl ⟨⟨a.val.1, a.property⟩, hor.1, rfl⟩, hor.2⟩
    | inr a => exact ⟨Or.inr ⟨⟨a.val.1, a.property⟩, hor.1, rfl⟩, hor.2⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: endpoint-bit reversal commutes with
intrinsic-to-geometric gluing, including all missing-edge darts. -/
theorem rMinusCodeToGlued_reverse (d : RMinusCodeGluedDart F Q) :
    rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk (d.1, !d.2) =
      rMinusGluedDartReverse hτ hqMode
        (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d) := by
  rcases d with ⟨e, s⟩
  refine Quotient.inductionOn e ?_
  intro a
  cases a with
  | inl a =>
    change rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusCodePrefixDart F Q (⟨a.val, a.property⟩, !s)) =
      rMinusGluedDartReverse hτ hqMode
        (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
          (rMinusCodePrefixDart F Q (⟨a.val, a.property⟩, s)))
    rw [rMinusCodeToGluedDartEquiv_prefix, rMinusCodeToGluedDartEquiv_prefix]
    rfl
  | inr a =>
    change rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusCodeHattedDart F Q ⟨(a.val, !s), a.property⟩) =
      rMinusGluedDartReverse hτ hqMode
        (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
          (rMinusCodeHattedDart F Q ⟨(a.val, s), a.property⟩))
    rw [rMinusCodeToGluedDartEquiv_hatted, rMinusCodeToGluedDartEquiv_hatted]
    rfl

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the complete decoded exterior boundary maps
to the actual boundary, including the finite-word/hatted-tail join. -/
theorem rMinusDecodedBoundary_image (i : ℕ) :
    (rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusDecodedBoundary w n q i)).val = (m0GeodesicSide hp P .right).boundary i := by
  by_cases hi : i < ((F).LL ++ (F).LR).length
  · rw [rMinusDecodedBoundary, dite_eq_left hi, rMinusCodeGluedDartEquiv_prefix]
    exact congrArg (fun e : ℕ => (e, false)) (rMinusWhole_lower_get (h := h) hk i hi)
  · rw [rMinusDecodedBoundary, dite_eq_right hi, rMinusCodeGluedDartEquiv_hatted]
    exact rMinusWhole_hatted_boundary_tail hτ hp P hqMode hk i (Nat.le_of_not_gt hi)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the decoded seam is exactly the original
glued hatted seam, with its index and both endpoint conventions unchanged. -/
theorem rMinusDecodedSeam_equiv (i : ℕ) :
    rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusDecodedSeam w n q i) = rMinusGluedSeam hτ hqMode i :=
  rMinusCodeToGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk _

include hfin hk in
/-- Helper toward Lemma 5.5: the intrinsic root is exactly the marked
root in the geometric vertex quotient. -/
theorem rMinusCodeToGlued_root (v : RMinusCodeGluedVertex F Q) :
    v.val = ⟦Sum.inr (Q).root⟧ ↔
      Setoid.kerLift (rMinusBlockVertexImage hτ hqMode)
        (rMinusCodeToGluedVertexEquiv hτ hqMode hfin hk v) = VH 0 := by
  have hzero : 0 ∈ (Q).vertices := by
    obtain ⟨a, ha, he⟩ := boundaryGluing_root_mem_hatSide_vertices hτ
      (if longest then XDP.ldp else XDP.sdp) hqMode .right
    have hz : a = 0 := boundaryGluingHatVertexMap_injective W h k hτ
      (he.trans (boundaryGluingHatVertexMap_zero hτ).symm)
    exact hz ▸ ha
  let r : RMinusCodeGluedVertex F Q := ⟨⟦Sum.inr 0⟧, Or.inr ⟨⟨0, hzero⟩, rfl⟩⟩
  rw [rMinusCodeToGluedVertexEquiv_image]
  change v.val = r.val ↔ rMinusCodeVertexImage hτ hqMode hfin v.val =
    rMinusCodeVertexImage hτ hqMode hfin r.val
  constructor
  · exact congrArg _
  · intro he
    exact congrArg Subtype.val (rMinusCodeVertexImage_injective hτ hqMode hfin hk he)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every boundary tag is preserved and reflected
on the intrinsic dart carrier, independently of the second cell. -/
theorem rMinusDecodedBoundary_glued_iff (i : ℕ) (d : RMinusCodeGluedDart F Q)
    (v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusDecodedBoundary w n q i = d ↔
      rMinusGluedBoundary hτ hqMode i
        (.inr (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d)) v := by
  rw [rMinusGluedMarkedIso_boundary_iff hτ hp P hqMode Tpath hfin hleft hk]
  change _ ↔ (m0GeodesicSide hp P .right).boundary i =
    (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d)).val
  rw [rMinusCodeToGluedDartEquiv_equiv,
    ← rMinusDecodedBoundary_image hτ hp P hqMode Tpath hfin hleft hk i]
  constructor
  · exact congrArg (fun d =>
      (rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val)
  · intro he
    exact (rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).injective
      (Subtype.ext he)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every intrinsic marked relation is preserved
and reflected by the geometric gluing equivalence. -/
theorem rMinusCodeWholeRelation_glued_iff (t : TruncationRelation)
    (u v : Sum (RMinusCodeGluedVertex F Q) (RMinusCodeGluedDart F Q)) :
    rMinusCodeWholeRelation w n q t u v ↔
      rMinusGluedWholeRelation hτ hp P hqMode Tpath hfin hleft hk t
        ((Equiv.sumCongr (rMinusCodeToGluedVertexEquiv hτ hqMode hfin hk)
          (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk)) u)
        ((Equiv.sumCongr (rMinusCodeToGluedVertexEquiv hτ hqMode hfin hk)
          (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk)) v) := by
  cases t <;> cases u <;> cases v <;>
    simp only [rMinusCodeWholeRelation, rMinusGluedWholeRelation,
      rMinusGluedIncidenceRelation, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
  all_goals try rfl
  all_goals try exact rMinusCodeToGlued_root hτ hqMode hfin hk _
  all_goals try exact rMinusCodeToGlued_oriented hτ hp P hqMode Tpath hfin hleft hk _
  all_goals try exact rMinusDecodedBoundary_glued_iff hτ hp P hqMode Tpath hfin hleft hk _ _ _
  case incident.inr.inl d v =>
    rw [← (rMinusCodeToGluedVertexEquiv hτ hqMode hfin hk).symm.injective.eq_iff,
      Equiv.symm_apply_apply]
    change _ ↔ rMinusGluedToCodeVertex hτ hqMode hfin hk _ = v
    rw [rMinusCodeToGlued_endpoint]
    constructor
    · intro he; apply Subtype.ext; exact he
    · exact congrArg Subtype.val
  case opposite.inr.inr d e =>
    rw [← rMinusCodeToGlued_reverse]
    exact (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).injective.eq_iff.symm
  case rotation.inr.inr d e =>
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply,
      (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).injective.eq_iff]
  case faceNext.inr.inr d e =>
    exact (rMinusGluedFaceNext_code_iff hτ hp P hqMode Tpath hfin hleft hk d e).symm
  case seam.inr.inl i d v =>
    rw [← rMinusDecodedSeam_equiv hτ hp P hqMode Tpath hfin hleft hk]
    exact (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).injective.eq_iff.symm
  case seam.inr.inr i d e =>
    rw [← rMinusDecodedSeam_equiv hτ hp P hqMode Tpath hfin hleft hk]
    exact (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).injective.eq_iff.symm

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the natural-number decoder and the geometric
glued cells have identical full marked relations under their cell equivalence. -/
theorem rMinusDecodedToGluedCellEquiv_relation_iff (t : TruncationRelation)
    (u v : GeometricSideCell (rMinusDecodedSide w n q)) :
    geometricSideRelation (rMinusDecodedSide w n q) t u v ↔
      rMinusGluedWholeRelation hτ hp P hqMode Tpath hfin hleft hk t
        (rMinusDecodedToGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (rMinusDecodedToGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  obtain ⟨a, rfl⟩ := (rMinusDecodedCellEquiv w n q).surjective u
  obtain ⟨b, rfl⟩ := (rMinusDecodedCellEquiv w n q).surjective v
  simp only [rMinusDecodedToGluedCellEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact (rMinusDecodedCellEquiv_relation_iff w n q t a b).symm.trans
    (rMinusCodeWholeRelation_glued_iff hτ hp P hqMode Tpath hfin hleft hk t a b)

include hτ Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: for every nonpositive boundary index, the
code-built complete right side is marked-isomorphic to the actual geometric
right side. No rotation, face, boundary or identification premise is added. -/
theorem boundaryGluing_nonpos_right_markedIso_nonempty :
    Nonempty (GeometricSideMarkedIso (rMinusDecodedSide w n q)
      (m0GeodesicSide hp P .right)) := by
  refine ⟨⟨(rMinusDecodedToGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk).trans
    (rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk), ?_⟩⟩
  intro t u v
  exact (rMinusDecodedToGluedCellEquiv_relation_iff
    hτ hp P hqMode Tpath hfin hleft hk t u v).trans
      (rMinusGluedWholeRelation_iff hτ hp P hqMode Tpath hfin hleft hk t _ _)

end GeometricIdentification













































end DirectedDistances.PaperProofs.Section5
