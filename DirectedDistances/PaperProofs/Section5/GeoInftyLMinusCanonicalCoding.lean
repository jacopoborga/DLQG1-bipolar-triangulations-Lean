/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusClassLocality

/-! Concrete minimal raw-token coding toward Lemma 5.5
quotient as decoder 4, including its missing edges. It does not replace the
existing decoder or infer measurability from arbitrary relabeling.

The first canonical-coordinate step is the bounded candidate characterization
of the exterior dart, with the original `LMinusPreimage` binders below.
No whole-side measurability or numbered paper result is asserted. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. Fixed raw tokens distinguish block and edge
identity; the hatted subtype certificate is not part of the token. -/
@[expose] def lMinusRawEdgeToken (M : GeometricSideSubmap) : Sum ℕ M.edges → ℕ
  | .inl e => 2 * e
  | .inr e => 2 * e.val + 1

/-- Helper toward Lemma 5.5. The raw token does not collapse parallel edges. -/
theorem lMinusRawEdgeToken_injective (M : GeometricSideSubmap) :
    Function.Injective (lMinusRawEdgeToken M) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change 2 * a = 2 * b at hab
      have h : a = b := by omega
      exact congrArg Sum.inl h
    | inr b =>
      change 2 * a = 2 * b.val + 1 at hab
      omega
  | inr a =>
    cases b with
    | inl b =>
      change 2 * a.val + 1 = 2 * b at hab
      omega
    | inr b =>
      change 2 * a.val + 1 = 2 * b.val + 1 at hab
      have h : a.val = b.val := by omega
      exact congrArg Sum.inr (Subtype.ext h)

/-- Helper toward Lemma 5.5. A candidate token represents exactly the
specified intrinsic edge class. No directed-presence filter is applied. -/
@[expose] def lMinusCanonicalEdgeCandidate {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (e : LMinusCodeGluedEdge r M) (n : ℕ) : Prop :=
  ∃ a : Sum ℕ M.edges, lMinusRawEdgeToken M a = n ∧
    (⟦a⟧ : LMinusCodeGluedEdge r M) = e

/-- Helper toward Lemma 5.5. Every edge class has a raw-token candidate. -/
theorem lMinusCanonicalEdgeCandidate_exists {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (e : LMinusCodeGluedEdge r M) :
    ∃ n, lMinusCanonicalEdgeCandidate r M e n := by
  refine Quotient.inductionOn e ?_
  intro a
  exact ⟨lMinusRawEdgeToken M a, a, rfl, rfl⟩

/-- Helper toward Lemma 5.5. The least raw token of the same concrete
edge quotient used by decoder 4. This is not `Encodable.ofCountable`. -/
@[expose] noncomputable def lMinusCanonicalEdgeId {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (e : LMinusCodeGluedEdge r M) : ℕ :=
  Nat.find (lMinusCanonicalEdgeCandidate_exists r M e)

/-- Helper toward Lemma 5.5. Complete minimal-token characterization. -/
theorem lMinusCanonicalEdgeId_eq_iff {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (e : LMinusCodeGluedEdge r M) (n : ℕ) :
    lMinusCanonicalEdgeId r M e = n ↔
      lMinusCanonicalEdgeCandidate r M e n ∧
      ∀ m < n, ¬ lMinusCanonicalEdgeCandidate r M e m := by
  exact Nat.find_eq_iff (lMinusCanonicalEdgeCandidate_exists r M e)

/-- Helper toward Lemma 5.5. The selected token really represents its edge. -/
theorem lMinusCanonicalEdgeId_spec {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (e : LMinusCodeGluedEdge r M) :
    lMinusCanonicalEdgeCandidate r M e (lMinusCanonicalEdgeId r M e) :=
  Nat.find_spec (lMinusCanonicalEdgeCandidate_exists r M e)

/-- Helper toward Lemma 5.5. Canonical numbering preserves edge identity. -/
theorem lMinusCanonicalEdgeId_injective {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap) :
    Function.Injective (lMinusCanonicalEdgeId r M) := by
  intro e f hef
  obtain ⟨a, ha, he⟩ := lMinusCanonicalEdgeId_spec r M e
  obtain ⟨b, hb, hf⟩ := lMinusCanonicalEdgeId_spec r M f
  have hab := lMinusRawEdgeToken_injective M (ha.trans (hef.trans hb.symm))
  subst b
  exact he.symm.trans hf

/-- Helper toward Lemma 5.5. The least token is bounded by every raw
representative, so a known representative gives a finite search bound. -/
theorem lMinusCanonicalEdgeId_le_token {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (a : Sum ℕ M.edges) :
    lMinusCanonicalEdgeId r M (⟦a⟧) ≤ lMinusRawEdgeToken M a :=
  Nat.find_min' (lMinusCanonicalEdgeCandidate_exists r M (⟦a⟧))
    ⟨a, rfl, rfl⟩

/-- Helper toward Lemma 5.5. Candidate membership is the original gluing
setoid, rather than equality of arbitrarily chosen global IDs. -/
theorem lMinusCanonicalEdgeCandidate_mk_iff {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (a : Sum ℕ M.edges) (n : ℕ) :
    lMinusCanonicalEdgeCandidate r M (⟦a⟧) n ↔
      ∃ b : Sum ℕ M.edges, lMinusRawEdgeToken M b = n ∧
        lMinusCodeEdgeSetoid r M b a := by
  constructor
  · rintro ⟨b, hb, he⟩
    exact ⟨b, hb, Quotient.exact he⟩
  · rintro ⟨b, hb, he⟩
    exact ⟨b, hb, Quotient.sound he⟩

/-- Helper toward Lemma 5.5. On the coherent hatted carrier, the candidate
test uses the already proved normal form of this exact edge gluing. -/
theorem lMinusCanonicalEdgeCandidate_normal_iff {x : XDP}
    (r : LMinusSidePresentation x)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (a : Sum ℕ (lMinusCoherentLeftSide x q).edges) (n : ℕ) :
    lMinusCanonicalEdgeCandidate r (lMinusCoherentLeftSide x q) (⟦a⟧) n ↔
      ∃ b : Sum ℕ (lMinusCoherentLeftSide x q).edges,
        lMinusRawEdgeToken _ b = n ∧
        lMinusCodeEdgeNormalRelation r (lMinusCoherentLeftSide x q) b a := by
  rw [lMinusCanonicalEdgeCandidate_mk_iff]
  constructor
  · rintro ⟨b, hb, he⟩
    exact ⟨b, hb, (lMinusCodeEdgeSetoid_iff r q b a).mp he⟩
  · rintro ⟨b, hb, he⟩
    exact ⟨b, hb, (lMinusCodeEdgeSetoid_iff r q b a).mpr he⟩

/-- Helper toward Lemma 5.5. A primed class has only its own even token
and the odd token of a directly shared hatted edge as possible candidates.
This eliminates the equivalence closure from this concrete candidate test. -/
theorem lMinusCanonicalEdgeCandidate_primed_iff {x : XDP}
    (r : LMinusSidePresentation x)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (e n : ℕ) :
    lMinusCanonicalEdgeCandidate r (lMinusCoherentLeftSide x q) (⟦Sum.inl e⟧) n ↔
      n = 2 * e ∨ ∃ b : (lMinusCoherentLeftSide x q).edges,
        n = 2 * b.val + 1 ∧
        lMinusCodeEdgeGluing r (lMinusCoherentLeftSide x q) (.inl e) (.inr b) := by
  rw [lMinusCanonicalEdgeCandidate_normal_iff]
  constructor
  · rintro ⟨b, hb, he⟩
    cases b with
    | inl b =>
      change b = e at he
      subst b
      exact Or.inl hb.symm
    | inr b => exact Or.inr ⟨b, hb.symm, he⟩
  · rintro (hn | ⟨b, hn, he⟩)
    · exact ⟨.inl e, hn.symm, rfl⟩
    · exact ⟨.inr b, hn.symm, he⟩

/-- Helper toward Lemma 5.5. The new and existing encoded edge carriers
are explicitly equivalent through the same intrinsic quotient. -/
@[expose] noncomputable def lMinusCanonicalToOldEdgeEquiv {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap) :
    Set.range (lMinusCanonicalEdgeId r M) ≃ Set.range (lMinusCodeEdgeId r M) :=
  (Equiv.ofInjective _ (lMinusCanonicalEdgeId_injective r M)).symm.trans
    (Equiv.ofInjective _ (lMinusCodeEdgeId_injective r M))

/-- Helper toward Lemma 5.5. The carrier equivalence represents the same
edge, including an edge absent from the directed carrier. -/
theorem lMinusCanonicalToOldEdgeEquiv_apply {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (e : LMinusCodeGluedEdge r M) :
    lMinusCanonicalToOldEdgeEquiv r M ⟨lMinusCanonicalEdgeId r M e, ⟨e, rfl⟩⟩ =
      ⟨lMinusCodeEdgeId r M e, ⟨e, rfl⟩⟩ := by
  change (Equiv.ofInjective _ (lMinusCodeEdgeId_injective r M))
    ((Equiv.ofInjective _ (lMinusCanonicalEdgeId_injective r M)).symm
      ((Equiv.ofInjective _ (lMinusCanonicalEdgeId_injective r M)) e)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Helper toward Lemma 5.5. Canonical darts retain the original bit. -/
@[expose] noncomputable def lMinusCanonicalDartId {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (d : LMinusCodeGluedDart r M) : ℕ × Bool :=
  (lMinusCanonicalEdgeId r M d.1, d.2)

/-- Helper toward Lemma 5.5. Both darts of every geometric edge remain distinct. -/
theorem lMinusCanonicalDartId_injective {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap) :
    Function.Injective (lMinusCanonicalDartId r M) := by
  intro a b hab
  change (lMinusCanonicalEdgeId r M a.1, a.2) =
    (lMinusCanonicalEdgeId r M b.1, b.2) at hab
  apply Prod.ext
  · exact lMinusCanonicalEdgeId_injective r M
      (congrArg (fun p : ℕ × Bool => p.1) hab)
  · exact congrArg (fun p : ℕ × Bool => p.2) hab

/-- Helper toward Lemma 5.5. A source preimage's exterior mark in the
new coding of the same decoder-4 intrinsic dart. No realization is chosen. -/
@[expose] noncomputable def lMinusPreimageCanonicalBoundary {x : XDP}
    (q : LMinusPreimage x) (i : ℕ) : ℕ × Bool :=
  lMinusCanonicalDartId (decodeLMinus x q.k (lMinusCodeOf q))
    (lMinusCoherentLeftSide x q.hattedCoherent)
    (lMinusCodeExteriorBoundaryDart (decodeLMinus x q.k (lMinusCodeOf q))
      q.hattedCoherent i)

/-- Helper toward Lemma 5.5. The actual source-bound exterior code has
an explicit finite bound depending only on its primed raw edge label. -/
theorem lMinusPreimageCanonicalBoundary_fst_le {x : XDP}
    (q : LMinusPreimage x) (i : ℕ) :
    (lMinusPreimageCanonicalBoundary q i).1 ≤
      2 * lMinusCodeExteriorBoundaryEdge (lMinusCodeOf q).1 i := by
  exact lMinusCanonicalEdgeId_le_token
    (decodeLMinus x q.k (lMinusCodeOf q))
    (lMinusCoherentLeftSide x q.hattedCoherent) (Sum.inl _)

/-- Helper toward Lemma 5.5. The retained primed root is token zero,
including the missing-root case; its reversed dart bit is retained. -/
theorem lMinusPreimageCanonicalBoundary_zero {x : XDP}
    (q : LMinusPreimage x) : lMinusPreimageCanonicalBoundary q 0 = (0, true) := by
  apply Prod.ext
  · have h := lMinusPreimageCanonicalBoundary_fst_le q 0
    change (lMinusPreimageCanonicalBoundary q 0).1 ≤ 2 * 0 at h
    omega
  · rfl

/-- Helper toward Lemma 5.5. Exact first canonical-coordinate reduction:
only candidate ranks below a finite raw-token bound need to be tested.
Candidate measurability itself is not assumed or claimed. -/
theorem lMinusPreimageCanonicalBoundary_fst_eq_iff {x : XDP}
    (q : LMinusPreimage x) (i n : ℕ) :
    let r := decodeLMinus x q.k (lMinusCodeOf q)
    let M := lMinusCoherentLeftSide x q.hattedCoherent
    let e : LMinusCodeGluedEdge r M :=
      ⟦Sum.inl (lMinusCodeExteriorBoundaryEdge (lMinusCodeOf q).1 i)⟧
    (lMinusPreimageCanonicalBoundary q i).1 = n ↔
      n ≤ 2 * lMinusCodeExteriorBoundaryEdge (lMinusCodeOf q).1 i ∧
      lMinusCanonicalEdgeCandidate r M e n ∧
      ∀ m < n, ¬ lMinusCanonicalEdgeCandidate r M e m := by
  dsimp only
  constructor
  · intro hn
    refine ⟨hn ▸ lMinusPreimageCanonicalBoundary_fst_le q i, ?_⟩
    exact (lMinusCanonicalEdgeId_eq_iff _ _ _ n).mp hn
  · rintro ⟨_, hn⟩
    exact (lMinusCanonicalEdgeId_eq_iff _ _ _ n).mpr hn

/-- Helper toward Lemma 5.5. Fixed raw vertex tokens, before gluing. -/
@[expose] def lMinusRawVertexToken : Sum ℕ ℕ → ℕ
  | .inl v => 2 * v
  | .inr v => 2 * v + 1

/-- Helper toward Lemma 5.5. Raw vertex identity survives tokenization. -/
theorem lMinusRawVertexToken_injective : Function.Injective lMinusRawVertexToken := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change 2 * a = 2 * b at hab
      have h : a = b := by omega
      exact congrArg Sum.inl h
    | inr b =>
      change 2 * a = 2 * b + 1 at hab
      omega
  | inr a =>
    cases b with
    | inl b =>
      change 2 * a + 1 = 2 * b at hab
      omega
    | inr b =>
      change 2 * a + 1 = 2 * b + 1 at hab
      have h : a = b := by omega
      exact congrArg Sum.inr h

/-- Helper toward Lemma 5.5. Raw candidates for a vertex quotient class. -/
@[expose] def lMinusCanonicalVertexCandidate {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (v : LMinusCodeRawVertex r M) (n : ℕ) : Prop :=
  ∃ a : Sum ℕ ℕ, lMinusRawVertexToken a = n ∧
    (⟦a⟧ : LMinusCodeRawVertex r M) = v

/-- Helper toward Lemma 5.5. Every raw vertex class has a candidate. -/
theorem lMinusCanonicalVertexCandidate_exists {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (v : LMinusCodeRawVertex r M) :
    ∃ n, lMinusCanonicalVertexCandidate r M v n := by
  refine Quotient.inductionOn v ?_
  intro a
  exact ⟨lMinusRawVertexToken a, a, rfl, rfl⟩

/-- Helper toward Lemma 5.5. Least raw token of an allocated vertex class.
Allocation is the unchanged subtype of the original vertex quotient. -/
@[expose] noncomputable def lMinusCanonicalVertexId {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (v : LMinusCodeGluedVertex r M) : ℕ :=
  Nat.find (lMinusCanonicalVertexCandidate_exists r M v.val)

/-- Helper toward Lemma 5.5. Complete characterization of vertex IDs. -/
theorem lMinusCanonicalVertexId_eq_iff {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (v : LMinusCodeGluedVertex r M) (n : ℕ) :
    lMinusCanonicalVertexId r M v = n ↔
      lMinusCanonicalVertexCandidate r M v.val n ∧
      ∀ m < n, ¬ lMinusCanonicalVertexCandidate r M v.val m :=
  Nat.find_eq_iff (lMinusCanonicalVertexCandidate_exists r M v.val)

/-- Helper toward Lemma 5.5. Canonical vertex numbering is faithful. -/
theorem lMinusCanonicalVertexId_injective {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap) :
    Function.Injective (lMinusCanonicalVertexId r M) := by
  intro v w hvw
  obtain ⟨a, ha, hv⟩ := Nat.find_spec (lMinusCanonicalVertexCandidate_exists r M v.val)
  obtain ⟨b, hb, hw⟩ := Nat.find_spec (lMinusCanonicalVertexCandidate_exists r M w.val)
  have hab := lMinusRawVertexToken_injective (ha.trans (hvw.trans hb.symm))
  subst b
  exact Subtype.ext (hv.symm.trans hw)

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. A canonical endpoint reader on numeric IDs.
The value outside the edge carrier is irrelevant to the marked relations. -/
@[expose] noncomputable def lMinusCanonicalEndpointId (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x) (s : Bool) (n : ℕ) : ℕ :=
  if h : n ∈ Set.range (lMinusCanonicalEdgeId r (lMinusCoherentLeftSide x q)) then
    lMinusCanonicalVertexId r _ (lMinusCodeEndpointVertex x r q s
      ((Equiv.ofInjective _ (lMinusCanonicalEdgeId_injective r _)).symm ⟨n, h⟩))
  else 0

/-- Helper toward Lemma 5.5. The reader is exact at every allocated edge. -/
theorem lMinusCanonicalEndpointId_id (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x) (s : Bool)
    (e : LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q)) :
    lMinusCanonicalEndpointId x r q s (lMinusCanonicalEdgeId r _ e) =
      lMinusCanonicalVertexId r _ (lMinusCodeEndpointVertex x r q s e) := by
  simp only [lMinusCanonicalEndpointId, dite_eq_left (Set.mem_range_self e),
    Equiv.ofInjective_symm_apply]

/-- Helper toward Lemma 5.5. Decoder 4 with minimal raw-token vertex and
edge IDs. All geometric predicates, missing edges and marks use the same
intrinsic cells and operations; there is no new geometric hypothesis. -/
@[expose] noncomputable def lMinusCanonicalSide (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) : GeometricSideSubmap where
  vertices := Set.range (lMinusCanonicalVertexId r (lMinusCoherentLeftSide x q))
  edges := Set.range (lMinusCanonicalEdgeId r (lMinusCoherentLeftSide x q))
  west := lMinusCanonicalEndpointId x r q false
  east := lMinusCanonicalEndpointId x r q true
  present := {i | ∃ e, lMinusCanonicalEdgeId r (lMinusCoherentLeftSide x q) e = i ∧
    lMinusCodeEdgePresent r (lMinusCoherentLeftSide x q)
      (fun a => ∃ m, a < (kmswMissingRootStage r.code.1 m).nextEdge ∧
        (kmswMissingRootStage r.code.1 m).present a = true) e}
  rotation := fun d e => ∃ a b : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q),
    lMinusCanonicalDartId r _ a = d ∧ lMinusCanonicalDartId r _ b = e ∧
      lMinusCodeInitialSplicedRotation r q hf a = b
  faceNext := fun d e => ∃ a b : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q),
    lMinusCanonicalDartId r _ a = d ∧ lMinusCanonicalDartId r _ b = e ∧
      lMinusCodeWholeFaceNext r q hf a b
  root := lMinusCanonicalVertexId r (lMinusCoherentLeftSide x q)
    ⟨⟦Sum.inr (lMinusCoherentLeftSide x q).root⟧,
      Or.inr ⟨⟨_, lMinus_hatted_root_mem x q⟩, rfl⟩⟩
  boundary := fun i => lMinusCanonicalDartId r _ (lMinusCodeExteriorBoundaryDart r q i)
  seam := fun i => lMinusCanonicalDartId r _
    (lMinusCodeHattedDart r _ ⟨(lMinusCoherentLeftSide x q).seam i,
      lMinus_hatted_seam_mem x q i⟩)

/-- Helper toward Lemma 5.5. Canonical encoding of all intrinsic cells. -/
@[expose] noncomputable def lMinusCanonicalCellEquiv (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) :
    Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) ≃
      GeometricSideCell (lMinusCanonicalSide x r q hf) :=
  Equiv.sumCongr
    (Equiv.ofInjective _ (lMinusCanonicalVertexId_injective r _))
    (Equiv.ofBijective
      (fun d => ⟨lMinusCanonicalDartId r _ d, ⟨d.1, rfl⟩⟩)
      ⟨fun _ _ hab => lMinusCanonicalDartId_injective r _ (congrArg Subtype.val hab), by
        intro d
        obtain ⟨e, he⟩ := d.property
        exact ⟨(e, d.val.2), Subtype.ext (Prod.ext he rfl)⟩⟩)

/-- Helper toward Lemma 5.5. Directed presence has not changed. -/
theorem lMinusCanonicalSide_present_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1)
    (e : LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q)) :
    lMinusCanonicalEdgeId r _ e ∈ (lMinusCanonicalSide x r q hf).present ↔
      lMinusCodeEdgePresent r (lMinusCoherentLeftSide x q)
        (fun a => ∃ m, a < (kmswMissingRootStage r.code.1 m).nextEdge ∧
          (kmswMissingRootStage r.code.1 m).present a = true) e := by
  constructor
  · rintro ⟨a, ha, hp⟩
    have h := lMinusCanonicalEdgeId_injective r _ ha
    subst a
    exact hp
  · intro hp
    exact ⟨e, rfl, hp⟩

/-- Helper toward Lemma 5.5. Canonical rotation reads the same splice. -/
theorem lMinusCanonicalSide_rotation_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1)
    (a b : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    (lMinusCanonicalSide x r q hf).rotation
      (lMinusCanonicalDartId r _ a) (lMinusCanonicalDartId r _ b) ↔
      lMinusCodeInitialSplicedRotation r q hf a = b := by
  constructor
  · rintro ⟨a', b', ha, hb, hr⟩
    have ha' := lMinusCanonicalDartId_injective r _ ha
    have hb' := lMinusCanonicalDartId_injective r _ hb
    subst a'
    subst b'
    exact hr
  · intro hr
    exact ⟨a, b, rfl, rfl, hr⟩

/-- Helper toward Lemma 5.5. Canonical face succession reads the same relation. -/
theorem lMinusCanonicalSide_faceNext_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1)
    (a b : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    (lMinusCanonicalSide x r q hf).faceNext
      (lMinusCanonicalDartId r _ a) (lMinusCanonicalDartId r _ b) ↔
      lMinusCodeWholeFaceNext r q hf a b := by
  constructor
  · rintro ⟨a', b', ha, hb, hr⟩
    have ha' := lMinusCanonicalDartId_injective r _ ha
    have hb' := lMinusCanonicalDartId_injective r _ hb
    subst a'
    subst b'
    exact hr
  · intro hr
    exact ⟨a, b, rfl, rfl, hr⟩

/-- Helper toward Lemma 5.5. Every non-boundary tag has the unchanged
intrinsic interpretation, including root, missing edges, rotation and seam. -/
theorem lMinusCanonicalCellEquiv_nonboundary_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (t : TruncationRelation)
    (ht : ∀ i, t ≠ .boundary i)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    geometricSideRelation (lMinusCanonicalSide x r q hf) t
      (lMinusCanonicalCellEquiv x r q hf u) (lMinusCanonicalCellEquiv x r q hf v) ↔
      lMinusCodeRelation2 x r q hf t u v := by
  cases t with
  | vertex => cases u <;> cases v <;> rfl
  | root =>
    cases u with
    | inl a => cases v <;> exact (lMinusCanonicalVertexId_injective r _).eq_iff
    | inr a => cases v <;> rfl
  | target => cases u <;> cases v <;> rfl
  | incident =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d =>
      cases v with
      | inr e => rfl
      | inl a =>
        change (if (lMinusCanonicalDartId r _ d).2 then
            lMinusCanonicalEndpointId x r q true (lMinusCanonicalDartId r _ d).1
          else lMinusCanonicalEndpointId x r q false (lMinusCanonicalDartId r _ d).1) =
          lMinusCanonicalVertexId r _ a ↔ lMinusCodeEndpointVertex x r q d.2 d.1 = a
        rcases d with ⟨e, s⟩
        cases s <;> simp only [lMinusCanonicalDartId, Bool.false_eq_true,
          ite_eq_left, lMinusCanonicalEndpointId_id]
        all_goals exact (lMinusCanonicalVertexId_injective r _).eq_iff
  | opposite =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d =>
      cases v with
      | inl a => rfl
      | inr e =>
        change lMinusCanonicalDartId r _ (d.1, !d.2) = lMinusCanonicalDartId r _ e ↔ _
        exact (lMinusCanonicalDartId_injective r _).eq_iff
  | oriented =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d =>
      cases v <;> exact and_congr_left (fun _ => lMinusCanonicalSide_present_iff x r q hf d.1)
  | rotation =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d =>
      cases v with
      | inl a => rfl
      | inr e => exact lMinusCanonicalSide_rotation_iff x r q hf d e
  | faceNext =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d =>
      cases v with
      | inl a => rfl
      | inr e => exact lMinusCanonicalSide_faceNext_iff x r q hf d e
  | boundary i => exact (ht i rfl).elim
  | seam i =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d => cases v <;> exact (lMinusCanonicalDartId_injective r _).eq_iff

/-- Helper toward Lemma 5.5. All ten canonical marked relations agree
with decoder 4 under the explicit common-cell correspondence. -/
theorem lMinusCanonicalCellEquiv_relation_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (t : TruncationRelation)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    geometricSideRelation (lMinusCanonicalSide x r q hf) t
      (lMinusCanonicalCellEquiv x r q hf u) (lMinusCanonicalCellEquiv x r q hf v) ↔
    geometricSideRelation (lMinusCodeSide4 x r q hf) t
      (lMinusCodeSide4CellEquiv x r q hf u) (lMinusCodeSide4CellEquiv x r q hf v) := by
  by_cases hb : ∃ i, t = .boundary i
  · obtain ⟨i, rfl⟩ := hb
    rw [lMinusCodeSide4CellEquiv_boundary_iff]
    cases u with
    | inl a => cases v <;> rfl
    | inr d => cases v <;> exact (lMinusCanonicalDartId_injective r _).eq_iff
  · have ht : ∀ i, t ≠ .boundary i := fun i hi => hb ⟨i, hi⟩
    exact (lMinusCanonicalCellEquiv_nonboundary_iff x r q hf t ht u v).trans
      (lMinusCodeSide4CellEquiv_nonboundary_iff x r q hf t ht u v).symm

/-- Helper toward Lemma 5.5. A concrete class-preserving replacement for
decoder 4; no measurability or locality hypothesis enters this isomorphism. -/
@[expose] noncomputable def lMinusCanonicalSideMarkedIso (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) :
    GeometricSideMarkedIso (lMinusCanonicalSide x r q hf) (lMinusCodeSide4 x r q hf) where
  equiv := (lMinusCanonicalCellEquiv x r q hf).symm.trans
    (lMinusCodeSide4CellEquiv x r q hf)
  relation_iff := by
    intro t u v
    have hh := lMinusCanonicalCellEquiv_relation_iff x r q hf t
      ((lMinusCanonicalCellEquiv x r q hf).symm u)
      ((lMinusCanonicalCellEquiv x r q hf).symm v)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hh
    exact hh

/-- Helper toward Lemma 5.5. The minimal-token replacement is the same
marked side class, with all geometric and boundary data retained. -/
theorem lMinusCanonicalSide_class_eq (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) :
    geometricSideClass (lMinusCanonicalSide x r q hf) =
      geometricSideClass (lMinusCodeSide4 x r q hf) :=
  (geometricSideClass_eq_iff _ _).mpr ⟨lMinusCanonicalSideMarkedIso x r q hf⟩

/-- Helper toward Lemma 5.5. Class identification with the concrete
decoder under its original binders, without additional geometric premises. -/
theorem lMinusCanonicalSide_class_eq_decodedSide4
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈ Coherent (if longest then XDP.ldp else XDP.sdp))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    geometricSideClass (lMinusCanonicalSide (if longest then XDP.ldp else XDP.sdp)
      (decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
        (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W))
      ⟨boundaryFutureHattedPath k W, hqMode⟩
      (lMinus_primed_observation_finiteIncidence hτ hfin)) =
      geometricSideClass (lMinusDecodedSide4 hτ hqMode hfin) := by
  rw [lMinusDecodedSide4_eq_codeSide4]
  exact lMinusCanonicalSide_class_eq _ _ _ _


























end DirectedDistances.PaperProofs.Section5
