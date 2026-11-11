/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole4

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical
local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5: a raw endpoint of a code edge representative.
The primed side correction is read from the primed code; the hatted endpoint
is read from the hatted block. -/
@[expose] noncomputable def lMinusCodeRawEndpoint {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) (s : Bool) : Sum ℕ M.edges → Sum ℕ ℕ
  | .inl e => .inl (kmswLimitDartVertex r.code.1
      (e, s ^^ lMinusCodePrimedSideFlip r e))
  | .inr e => .inr (if s then M.east e.1 else M.west e.1)

/-- Helper toward Lemma 5.5: the intrinsic vertex identifications are
generated only by endpoints of the shared code-boundary edges. -/
@[expose] noncomputable def lMinusCodeVertexGluing {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) (u v : Sum ℕ ℕ) : Prop :=
  ∃ a b, lMinusCodeEdgeGluing r M a b ∧ ∃ s : Bool,
    lMinusCodeRawEndpoint r M s a = u ∧ lMinusCodeRawEndpoint r M s b = v

/-- Helper toward Lemma 5.5: the code-generated vertex equivalence closure. -/
@[expose] noncomputable def lMinusCodeVertexSetoid {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) : Setoid (Sum ℕ ℕ) :=
  Relation.EqvGen.setoid (lMinusCodeVertexGluing r M)

/-- Helper toward Lemma 5.5: raw vertex classes of the two code blocks. -/
abbrev LMinusCodeRawVertex {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) := Quotient (lMinusCodeVertexSetoid r M)

/-- Helper toward Lemma 5.5: edge equivalence identifies corresponding
endpoint classes by the intrinsic code-generated vertex relation. -/
theorem lMinusCodeRawEndpoint_sound {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) (s : Bool) (a b : Sum ℕ M.edges)
    (hab : lMinusCodeEdgeSetoid r M a b) :
    (⟦lMinusCodeRawEndpoint r M s a⟧ : LMinusCodeRawVertex r M) =
      ⟦lMinusCodeRawEndpoint r M s b⟧ := by
  have hle : lMinusCodeEdgeSetoid r M ≤
      Setoid.ker (fun a =>
        (⟦lMinusCodeRawEndpoint r M s a⟧ : LMinusCodeRawVertex r M)) := by
    apply Setoid.eqvGen_le
    intro a b hab
    exact Quotient.sound (Relation.EqvGen.rel _ _
      ⟨a, b, hab, s, rfl, rfl⟩)
  exact hle hab

/-- Helper toward Lemma 5.5: endpoint descent to the intrinsic edge quotient. -/
@[expose] noncomputable def lMinusCodeEndpoint {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) (s : Bool) : LMinusCodeGluedEdge r M →
      LMinusCodeRawVertex r M :=
  Quotient.lift (fun a => ⟦lMinusCodeRawEndpoint r M s a⟧)
    (lMinusCodeRawEndpoint_sound r M s)

/-- Helper toward Lemma 5.5: exactly block vertex classes are allocated. -/
@[expose] def lMinusCodeVertexAllocated {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) : Set (LMinusCodeRawVertex r M) :=
  {v | (∃ a : ℕ, (⟦Sum.inl a⟧ : LMinusCodeRawVertex r M) = v) ∨
    ∃ a : M.vertices, (⟦Sum.inr a.1⟧ : LMinusCodeRawVertex r M) = v}

/-- Helper toward Lemma 5.5: the allocated intrinsic glued vertex carrier. -/
abbrev LMinusCodeGluedVertex {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) := lMinusCodeVertexAllocated r M

/-- Helper toward Lemma 5.5: a natural-number code for intrinsic vertex
classes, independent of the whole-plane embedding. -/
@[expose] noncomputable def lMinusCodeVertexId {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (v : LMinusCodeGluedVertex r M) : ℕ :=
  @Encodable.encode _ (Encodable.ofCountable _) v.1

/-- Helper toward Lemma 5.5: the intrinsic vertex code is injective. -/
theorem lMinusCodeVertexId_injective {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) :
    Function.Injective (lMinusCodeVertexId r M) :=
  fun _ _ h => Subtype.ext (@Encodable.encode_injective _ (Encodable.ofCountable _) _ _ h)

/-- Helper toward Lemma 5.5: a natural-number code for intrinsic edge classes. -/
@[expose] noncomputable def lMinusCodeEdgeId {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (e : LMinusCodeGluedEdge r M) : ℕ :=
  @Encodable.encode _ (Encodable.ofCountable _) e

/-- Helper toward Lemma 5.5: the intrinsic edge code is injective. -/
theorem lMinusCodeEdgeId_injective {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) : Function.Injective (lMinusCodeEdgeId r M) :=
  @Encodable.encode_injective _ (Encodable.ofCountable _)

/-- Helper toward Lemma 5.5: a partial inverse to the intrinsic edge code. -/
@[expose] noncomputable def lMinusCodeEdgeDecode {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap) :
    ℕ → Option (LMinusCodeGluedEdge r M) :=
  @Encodable.decode _ (Encodable.ofCountable _)

/-- Helper toward Lemma 5.5: decoding an encoded intrinsic edge succeeds. -/
theorem lMinusCodeEdgeDecode_id {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) (e : LMinusCodeGluedEdge r M) :
    lMinusCodeEdgeDecode r M (lMinusCodeEdgeId r M e) = some e :=
  @Encodable.encodek _ (Encodable.ofCountable _) e

/-- Helper toward Lemma 5.5: the natural-number dart code retains its side bit. -/
@[expose] noncomputable def lMinusCodeDartId {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (d : LMinusCodeGluedDart r M) : ℕ × Bool := (lMinusCodeEdgeId r M d.1, d.2)

/-- Helper toward Lemma 5.5: the intrinsic dart code is faithful. -/
theorem lMinusCodeDartId_injective {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) : Function.Injective (lMinusCodeDartId r M) := by
  intro a b hab
  rcases a with ⟨a, sa⟩
  rcases b with ⟨b, sb⟩
  change (lMinusCodeEdgeId r M a, sa) = (lMinusCodeEdgeId r M b, sb) at hab
  have hedge : a = b := lMinusCodeEdgeId_injective r M (congrArg Prod.fst hab)
  have hside : sa = sb := congrArg Prod.snd hab
  subst b
  subst sb
  rfl

/-- Helper toward Lemma 5.5: the endpoint code is the descended intrinsic
endpoint on every edge class. -/
theorem lMinusCodeEndpoint_allocated (x : XDP) (r : LMinusSidePresentation x)
    (q : Coherent x) (s : Bool) (e : LMinusCodeGluedEdge r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q)) :
    lMinusCodeEndpoint r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q) s e ∈
      lMinusCodeVertexAllocated r
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q) := by
  let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q
  refine Quotient.inductionOn e ?_
  intro a
  cases a with
  | inl a =>
    exact Or.inl ⟨kmswLimitDartVertex r.code.1
      (a, s ^^ lMinusCodePrimedSideFlip r a), rfl⟩
  | inr a =>
    have he := geometricSideSubmap_endpoints x renewalTime
      renewalTime_positiveSuccessTime .left q a.val a.property
    cases s with
    | false => exact Or.inr ⟨⟨M.west a.val, he.1⟩, rfl⟩
    | true => exact Or.inr ⟨⟨M.east a.val, he.2⟩, rfl⟩

/-- Helper toward Lemma 5.5: an endpoint as an allocated intrinsic vertex. -/
@[expose] noncomputable def lMinusCodeEndpointVertex (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x) (s : Bool)
    (e : LMinusCodeGluedEdge r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q)) :
    LMinusCodeGluedVertex r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q) :=
  ⟨lMinusCodeEndpoint r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q) s e,
    lMinusCodeEndpoint_allocated x r q s e⟩

/-- Helper toward Lemma 5.5: an endpoint natural-number code. -/
@[expose] noncomputable def lMinusCodeEndpointId (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x) (s : Bool) (e : ℕ) : ℕ :=
  ((lMinusCodeEdgeDecode r
    (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q) e).map
    (fun a => lMinusCodeVertexId r _ (lMinusCodeEndpointVertex x r q s a))).getD 0

/-- Helper toward Lemma 5.5: endpoint natural-number codes agree with the
intrinsic descended endpoints. -/
theorem lMinusCodeEndpointId_id (x : XDP) (r : LMinusSidePresentation x)
    (q : Coherent x) (s : Bool) (e : LMinusCodeGluedEdge r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q)) :
    lMinusCodeEndpointId x r q s (lMinusCodeEdgeId r _ e) =
      lMinusCodeVertexId r _ (lMinusCodeEndpointVertex x r q s e) := by
  simp only [lMinusCodeEndpointId, lMinusCodeEdgeDecode_id, Option.map_some,
    Option.getD_some]

/-- Helper toward Lemma 5.5: directed presence is inherited from either code
block after its shared-edge classes are identified. -/
@[expose] def lMinusCodeEdgePresent {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (primedPresent : ℕ → Prop) (e : LMinusCodeGluedEdge r M) : Prop :=
  (∃ a : ℕ, primedPresent a ∧ (⟦Sum.inl a⟧ : LMinusCodeGluedEdge r M) = e) ∨
  ∃ a : M.edges, a.1 ∈ M.present ∧
    (⟦Sum.inr a⟧ : LMinusCodeGluedEdge r M) = e

section DecodedSide

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

local notation "X" => (ite (longest = true) XDP.ldp XDP.sdp)
local notation "U" => boundaryGluingFutureStream W h k
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode : Coherent X)
local notation "Q" => geometricSideSubmap X renewalTime renewalTime_positiveSuccessTime
  ThinMapSide.left qL
local notation "hf" => lMinus_primed_observation_finiteIncidence hτ hfin

/-- Helper toward Lemma 5.5: the complete code-built left submap. Its vertex
and edge identities, endpoint descent, directed presence, adjusted rotation,
retained block-face successors, root, boundary and seam are defined from the
two code blocks and their intrinsic boundary identification. -/
@[expose] noncomputable def lMinusDecodedSide : GeometricSideSubmap where
  vertices := Set.range (fun v : LMinusCodeGluedVertex rL Q =>
    lMinusCodeVertexId rL Q v)
  edges := Set.range (lMinusCodeEdgeId rL Q)
  west := lMinusCodeEndpointId X rL qL false
  east := lMinusCodeEndpointId X rL qL true
  present := {i | ∃ e, lMinusCodeEdgeId rL Q e = i ∧
    lMinusCodeEdgePresent rL Q (PrimedEdgePresent U hτ) e}
  rotation := fun d e => ∃ a b : LMinusCodeGluedDart rL Q,
    lMinusCodeDartId rL Q a = d ∧ lMinusCodeDartId rL Q b = e ∧
      lMinusCodeInitialAdjustedRotation rL qL hf a = b
  faceNext := fun d e => ∃ a b : LMinusCodeGluedDart rL Q,
    lMinusCodeDartId rL Q a = d ∧ lMinusCodeDartId rL Q b = e ∧
      lMinusCodeWholeFaceNext rL qL hf a b
  root := lMinusCodeVertexId rL Q
    ⟨⟦Sum.inr (Q).root⟧, Or.inr ⟨⟨(Q).root, by
      change 0 ∈ ⋃ j, geometricAncestorVertices X renewalTime
        renewalTime_positiveSuccessTime ThinMapSide.left qL j
      rw [iUnion_geometricAncestorVertices]
      exact source_mem_sideVertices _
        (sourceAncestor_finite_incidence X renewalTime renewalTime_positiveSuccessTime qL)
        (sourceAncestor_left_nonneg X renewalTime renewalTime_positiveSuccessTime qL)
        (sourceAncestor_left_transient X renewalTime renewalTime_positiveSuccessTime qL)
        (sourceAncestor_right_unbounded X renewalTime renewalTime_positiveSuccessTime qL)
        (sourceAncestorPath X renewalTime renewalTime_positiveSuccessTime qL) .left⟩, rfl⟩⟩
  boundary := fun i => lMinusCodeDartId rL Q (lMinusCodeBoundaryDart rL qL (i, false))
  seam := fun i => lMinusCodeDartId rL Q (lMinusCodeHattedDart rL Q ⟨(Q).seam i, by
    change _ ∈ ⋃ j, geometricAncestorEdges X renewalTime
      renewalTime_positiveSuccessTime ThinMapSide.left qL j
    rw [iUnion_geometricAncestorEdges]
    exact seamEdge_mem_sideEdges _ _ _ _ _ _ ThinMapSide.left i⟩)

/-- Helper toward Lemma 5.5: every decoded vertex is an allocated intrinsic
code class. -/
@[expose] noncomputable def lMinusDecodedVertexEquiv :
    LMinusCodeGluedVertex rL Q ≃ (lMinusDecodedSide hτ hqMode hfin).vertices :=
  Equiv.ofInjective (fun v : LMinusCodeGluedVertex rL Q =>
    lMinusCodeVertexId rL Q v) (fun _ _ hab =>
      lMinusCodeVertexId_injective rL Q hab)

/-- Helper toward Lemma 5.5: the decoded darts are exactly the intrinsic
edge classes with their endpoint bits. -/
@[expose] noncomputable def lMinusDecodedDartEquiv :
    LMinusCodeGluedDart rL Q ≃
      {d : ℕ × Bool // d.1 ∈ (lMinusDecodedSide hτ hqMode hfin).edges} :=
  Equiv.ofBijective
    (fun d => ⟨lMinusCodeDartId rL Q d, ⟨d.1, rfl⟩⟩)
    ⟨fun _ _ hab => lMinusCodeDartId_injective rL Q
      (congrArg Subtype.val hab), by
      intro d
      obtain ⟨e, he⟩ := d.property
      exact ⟨(e, d.val.2), Subtype.ext (Prod.ext he rfl)⟩⟩

/-- Helper toward Lemma 5.5: all decoded cells are represented by the
intrinsic allocated vertices and glued darts. -/
@[expose] noncomputable def lMinusDecodedCellEquiv :
    Sum (LMinusCodeGluedVertex rL Q) (LMinusCodeGluedDart rL Q) ≃
      GeometricSideCell (lMinusDecodedSide hτ hqMode hfin) :=
  Equiv.sumCongr (lMinusDecodedVertexEquiv hτ hqMode hfin)
    (lMinusDecodedDartEquiv hτ hqMode hfin)

/-- Helper toward Lemma 5.5: geometric evaluation of raw code vertices,
used to compare the intrinsic and inherited vertex identifications. -/
@[expose] noncomputable def lMinusCodeRawVertexImage : Sum ℕ ℕ → ℕ :=
  Sum.elim (boundaryGluingPrimedVertexMap W h k hτ)
    (boundaryGluingHatVertexMap W h k hτ)

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a code endpoint has the same run-zero vertex
as the corresponding block dart endpoint. -/
theorem lMinusCodeRawEndpoint_image (s : Bool) (a : Sum ℕ (Q).edges) :
    lMinusCodeRawVertexImage hτ (lMinusCodeRawEndpoint rL Q s a) =
      kmswLimitDartVertex (shiftedStream W 0)
        (lMinusBlockEdgeImage hτ hqMode a, s) := by
  cases a with
  | inl e =>
      change boundaryGluingPrimedVertexMap W h k hτ
          (kmswLimitDartVertex (rL).code.1
            (e, s ^^ lMinusCodePrimedSideFlip rL e)) =
        kmswLimitDartVertex (shiftedStream W 0)
          (boundaryGluingPrimedEdgeMap W h k hτ e, s)
      have hcode : (rL).code.1 =
          primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ := by
        change (leftSideObsNonpos X k W).1 =
          primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ
        exact lMinus_primed_observation_code hτ
      have hflip : lMinusCodePrimedSideFlip rL e =
          primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ e :=
        lMinusCodePrimedSideFlip_observation hτ hfin e
      rw [hcode, hflip]
      have he := lMinusPrimedDartImage_endpoint hτ
        (e, s ^^ primedLimitSideFlip (boundaryGluingFutureStream W h k) hτ e)
      simpa [lMinusPrimedDartImage, Bool.xor_assoc] using he.symm
  | inr e =>
      let d : LMinusBlockDart hqMode := .inr ⟨(e.1, s), e.2⟩
      have hd := lMinusBlockDartEndpoint_image hτ hqMode d
      change boundaryGluingHatVertexMap W h k hτ
          (if s then (Q).east e.1 else (Q).west e.1) =
        kmswLimitDartVertex (shiftedStream W 0)
          (boundaryGluingHatEdgeMap W h k hτ e.1, s)
      simpa [lMinusCodeRawVertexImage, lMinusCodeRawEndpoint, d,
        lMinusBlockDartEndpoint, lMinusBlockDartImage, lMinusBlockVertexImage] using hd

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every code-generated vertex identification is
valid under the inherited block embeddings. -/
theorem lMinusCodeVertexGluing_sound {u v : Sum ℕ ℕ}
    (huv : lMinusCodeVertexGluing rL Q u v) :
    lMinusCodeRawVertexImage hτ u = lMinusCodeRawVertexImage hτ v := by
  obtain ⟨a, b, hab, s, ha, hb⟩ := huv
  have hedge : lMinusBlockEdgeImage hτ hqMode a =
      lMinusBlockEdgeImage hτ hqMode b := by
    have heq : (⟦a⟧ : LMinusCodeGluedEdge rL Q) = ⟦b⟧ :=
      Quotient.sound (Relation.EqvGen.rel _ _ hab)
    have h := congrArg (lMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath
      hfin hleft hk) heq
    have hv := congrArg Subtype.val h
    rw [lMinusCodeGluedEdgeEquiv_val hτ hp P hqMode Tpath hfin hleft hk a,
      lMinusCodeGluedEdgeEquiv_val hτ hp P hqMode Tpath hfin hleft hk b] at hv
    exact hv
  calc
    lMinusCodeRawVertexImage hτ u =
        lMinusCodeRawVertexImage hτ (lMinusCodeRawEndpoint rL Q s a) :=
          congrArg (lMinusCodeRawVertexImage hτ) ha.symm
    _ = kmswLimitDartVertex (shiftedStream W 0)
        (lMinusBlockEdgeImage hτ hqMode a, s) :=
          lMinusCodeRawEndpoint_image hτ hp P hqMode Tpath hfin hleft hk s a
    _ = kmswLimitDartVertex (shiftedStream W 0)
        (lMinusBlockEdgeImage hτ hqMode b, s) :=
          congrArg (fun e => kmswLimitDartVertex (shiftedStream W 0) (e, s)) hedge
    _ = lMinusCodeRawVertexImage hτ (lMinusCodeRawEndpoint rL Q s b) :=
          (lMinusCodeRawEndpoint_image hτ hp P hqMode Tpath hfin hleft hk s b).symm
    _ = lMinusCodeRawVertexImage hτ v :=
          congrArg (lMinusCodeRawVertexImage hτ) hb

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: evaluation of the intrinsic vertex quotient into
run-zero vertex IDs. This proves one direction of the needed identification;
reflection of every shared vertex remains to be established. -/
@[expose] noncomputable def lMinusCodeVertexImage :
    LMinusCodeRawVertex rL Q → ℕ :=
  Quotient.lift (lMinusCodeRawVertexImage hτ) (by
    intro a b hab
    have hle : lMinusCodeVertexSetoid rL Q ≤
        Setoid.ker (lMinusCodeRawVertexImage hτ) := by
      apply Setoid.eqvGen_le
      intro u v huv
      exact lMinusCodeVertexGluing_sound hτ hp P hqMode Tpath hfin hleft hk huv
    exact hle hab)


































end DecodedSide

end DirectedDistances.PaperProofs.Section5
