/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusCanonicalCoding

/-! Canonical minimal-token presentation for the nonpositive right side, -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

section CanonicalSide

variable (w : ℕ → Fin 3) (n : ℕ) {x : XDP}
  (q : Coherent x)

local notation "F" => kmswStage w n
local notation "M" => geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime
  ThinMapSide.right q

/-- Helper toward Lemma 5.5. The canonical endpoint reader uses the unique
least-token edge preimage on its carrier and the least-token endpoint ID. -/
@[expose] noncomputable def rMinusCanonicalEndpointId (s : Bool) (e : ℕ) : ℕ :=
  if h : e ∈ Set.range (rMinusCanonicalEdgeId F M) then
    rMinusCanonicalVertexId F M (rMinusCodeEndpoint F M s
      ((Equiv.ofInjective _ (rMinusCanonicalEdgeId_injective F M)).symm ⟨e, h⟩))
  else 0

/-- Helper toward Lemma 5.5. Canonical endpoints agree with intrinsic code
endpoints on every allocated glued edge. -/
theorem rMinusCanonicalEndpointId_id (s : Bool)
    (e : RMinusCodeGluedEdge F M) :
    rMinusCanonicalEndpointId w n q s (rMinusCanonicalEdgeId F M e) =
      rMinusCanonicalVertexId F M (rMinusCodeEndpoint F M s e) := by
  simp only [rMinusCanonicalEndpointId, dite_eq_left (Set.mem_range_self e),
    Equiv.ofInjective_symm_apply]

/-- Helper toward Lemma 5.5. The complete nonpositive right-side data with
least raw-token vertex and edge labels. Every field is defined from the
intrinsic code blocks, preserving edge identity and all marks. -/
@[expose] noncomputable def rMinusCanonicalSide : GeometricSideSubmap where
  vertices := Set.range (fun v : RMinusCodeGluedVertex F M =>
    rMinusCanonicalVertexId F M v.val)
  edges := Set.range (rMinusCanonicalEdgeId F M)
  west := rMinusCanonicalEndpointId w n q false
  east := rMinusCanonicalEndpointId w n q true
  present := {i | ∃ e, rMinusCanonicalEdgeId F M e = i ∧
    rMinusCodeEdgePresent F M e}
  rotation := fun d e => ∃ a b : RMinusCodeGluedDart F M,
    rMinusCanonicalDartId F M a = d ∧ rMinusCanonicalDartId F M b = e ∧
      rMinusCodeInitialAdjustedRotation w n q a = b
  faceNext := fun d e => ∃ a b : RMinusCodeGluedDart F M,
    rMinusCanonicalDartId F M a = d ∧ rMinusCanonicalDartId F M b = e ∧
      rMinusCodeFaceNext F M a b
  root := rMinusCanonicalVertexId F M
    ⟦Sum.inr (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime
      ThinMapSide.right q).root⟧
  boundary := fun i => rMinusCanonicalDartId F M (rMinusDecodedBoundary w n q i)
  seam := fun i => rMinusCanonicalDartId F M (rMinusDecodedSeam w n q i)

/-- Helper toward Lemma 5.5. Canonical vertex IDs give an equivalence with
the canonical vertex carrier. -/
@[expose] noncomputable def rMinusCanonicalVertexEquiv :
    RMinusCodeGluedVertex F M ≃ (rMinusCanonicalSide w n q).vertices :=
  Equiv.ofInjective
    (fun v : RMinusCodeGluedVertex F M =>
      rMinusCanonicalVertexId F M v.val)
    (fun _ _ h => Subtype.ext (rMinusCanonicalVertexId_injective F M h))

/-- Helper toward Lemma 5.5. Canonical dart IDs give an equivalence with
the canonical edge-dart carrier. -/
@[expose] noncomputable def rMinusCanonicalDartEquiv :
    RMinusCodeGluedDart F M ≃
      {d : ℕ × Bool // d.1 ∈ (rMinusCanonicalSide w n q).edges} :=
  Equiv.ofBijective
    (fun d => ⟨rMinusCanonicalDartId F M d, ⟨d.1, rfl⟩⟩)
    ⟨fun _ _ h => rMinusCanonicalDartId_injective F M (congrArg Subtype.val h), by
      intro d
      obtain ⟨e, he⟩ := d.property
      exact ⟨(e, d.val.2), Subtype.ext (Prod.ext he rfl)⟩⟩

/-- Helper toward Lemma 5.5. The code cells and canonical side cells have
the same explicit vertex/dart carriers. -/
@[expose] noncomputable def rMinusCanonicalCellEquiv :
    Sum (RMinusCodeGluedVertex F M) (RMinusCodeGluedDart F M) ≃
      GeometricSideCell (rMinusCanonicalSide w n q) :=
  Equiv.sumCongr (rMinusCanonicalVertexEquiv w n q)
    (rMinusCanonicalDartEquiv w n q)

/-- Helper toward Lemma 5.5. The vertex equivalence has the canonical ID. -/
theorem rMinusCanonicalVertexEquiv_val (v : RMinusCodeGluedVertex F M) :
    (rMinusCanonicalVertexEquiv w n q v).val =
      rMinusCanonicalVertexId F M v.val := rfl

/-- Helper toward Lemma 5.5. The dart equivalence has the canonical ID. -/
theorem rMinusCanonicalDartEquiv_val (d : RMinusCodeGluedDart F M) :
    (rMinusCanonicalDartEquiv w n q d).val =
      rMinusCanonicalDartId F M d := rfl

/-- Helper toward Lemma 5.5. Directed presence is unchanged by minimal-token
relabeling. -/
theorem rMinusCanonicalSide_present_iff (e : RMinusCodeGluedEdge F M) :
    rMinusCanonicalEdgeId F M e ∈ (rMinusCanonicalSide w n q).present ↔
      rMinusCodeEdgePresent F M e := by
  constructor
  · rintro ⟨a, ha, hp⟩
    have h := rMinusCanonicalEdgeId_injective F M ha
    subst a
    exact hp
  · intro hp
    exact ⟨e, rfl, hp⟩

/-- Helper toward Lemma 5.5. Canonical rotation retains the adjusted splice
permutation on intrinsic darts. -/
theorem rMinusCanonicalSide_rotation_iff
    (a b : RMinusCodeGluedDart F M) :
    (rMinusCanonicalSide w n q).rotation
      (rMinusCanonicalDartId F M a) (rMinusCanonicalDartId F M b) ↔
      rMinusCodeInitialAdjustedRotation w n q a = b := by
  constructor
  · rintro ⟨a', b', ha, hb, hr⟩
    have ha' := rMinusCanonicalDartId_injective F M ha
    have hb' := rMinusCanonicalDartId_injective F M hb
    subst a'
    subst b'
    exact hr
  · intro hr
    exact ⟨a, b, rfl, rfl, hr⟩

/-- Helper toward Lemma 5.5. Canonical face succession retains the code
face relation on intrinsic darts. -/
theorem rMinusCanonicalSide_faceNext_iff
    (a b : RMinusCodeGluedDart F M) :
    (rMinusCanonicalSide w n q).faceNext
      (rMinusCanonicalDartId F M a) (rMinusCanonicalDartId F M b) ↔
      rMinusCodeFaceNext F M a b := by
  constructor
  · rintro ⟨a', b', ha, hb, hr⟩
    have ha' := rMinusCanonicalDartId_injective F M ha
    have hb' := rMinusCanonicalDartId_injective F M hb
    subst a'
    subst b'
    exact hr
  · intro hr
    exact ⟨a, b, rfl, rfl, hr⟩

/-- Helper toward Lemma 5.5. All ten marked relations of the intrinsic code
are preserved by the least-token cell correspondence. -/
theorem rMinusCanonicalCellEquiv_relation_iff
    (t : TruncationRelation)
    (u v : Sum (RMinusCodeGluedVertex F M) (RMinusCodeGluedDart F M)) :
    rMinusCodeWholeRelation w n q t u v ↔
      geometricSideRelation (rMinusCanonicalSide w n q) t
        (rMinusCanonicalCellEquiv w n q u) (rMinusCanonicalCellEquiv w n q v) := by
  cases t <;> cases u <;> cases v <;>
    simp only [rMinusCodeWholeRelation, geometricSideRelation,
      rMinusCanonicalCellEquiv, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
  all_goals simp only [rMinusCanonicalVertexEquiv_val, rMinusCanonicalDartEquiv_val]
  all_goals try dsimp only [rMinusCanonicalSide, Set.mem_ofPred_eq]
  all_goals try exact (rMinusCanonicalVertexId_injective F M).eq_iff.symm
  all_goals try exact (rMinusCanonicalDartId_injective F M).eq_iff.symm
  all_goals try simp only [(rMinusCanonicalDartId_injective F M).eq_iff]
  case incident.inr.inl d v =>
    cases hb : d.2 <;>
      simpa only [rMinusCanonicalDartId, hb, Bool.false_eq_true, ↓reduceIte,
        rMinusCanonicalEndpointId_id] using
        (rMinusCanonicalVertexId_injective F M).eq_iff.symm
  case oriented.inr.inl d v =>
    change (rMinusCodeEdgePresent F M d.1 ∧ d.2 = false) ↔
      (∃ e, rMinusCanonicalEdgeId F M e = rMinusCanonicalEdgeId F M d.1 ∧
        rMinusCodeEdgePresent F M e) ∧ d.2 = false
    simp only [(rMinusCanonicalEdgeId_injective F M).eq_iff, exists_eq_left]
  case oriented.inr.inr d e =>
    change (rMinusCodeEdgePresent F M d.1 ∧ d.2 = false) ↔
      (∃ e, rMinusCanonicalEdgeId F M e = rMinusCanonicalEdgeId F M d.1 ∧
        rMinusCodeEdgePresent F M e) ∧ d.2 = false
    simp only [(rMinusCanonicalEdgeId_injective F M).eq_iff, exists_eq_left]
  case rotation.inr.inr d e =>
    constructor
    · intro h
      exact ⟨d, e, rfl, rfl, h⟩
    · rintro ⟨a, b, ha, hb, h⟩
      exact ha ▸ hb ▸ h
  case faceNext.inr.inr d e =>
    constructor
    · intro h
      exact ⟨d, e, rfl, rfl, h⟩
    · rintro ⟨a, b, ha, hb, h⟩
      exact ha ▸ hb ▸ h

/-- Helper toward Lemma 5.5. The canonical cell correspondence and the
decoded cell correspondence compare through the same intrinsic code cells. -/
theorem rMinusCanonicalCellEquiv_relation_iff_decoded
    (t : TruncationRelation)
    (u v : Sum (RMinusCodeGluedVertex F M) (RMinusCodeGluedDart F M)) :
    geometricSideRelation (rMinusCanonicalSide w n q) t
      (rMinusCanonicalCellEquiv w n q u) (rMinusCanonicalCellEquiv w n q v) ↔
    geometricSideRelation (rMinusDecodedSide w n q) t
      (rMinusDecodedCellEquiv w n q u) (rMinusDecodedCellEquiv w n q v) := by
  exact (rMinusCanonicalCellEquiv_relation_iff w n q t u v).symm.trans
    (rMinusDecodedCellEquiv_relation_iff w n q t u v)

/-- Helper toward Lemma 5.5. The decoded-side cell carrier is equivalent to
the canonical least-token cell carrier. -/
@[expose] noncomputable def rMinusDecodedToCanonicalCellEquiv :
    GeometricSideCell (rMinusDecodedSide w n q) ≃
      GeometricSideCell (rMinusCanonicalSide w n q) :=
  (rMinusDecodedCellEquiv w n q).symm.trans
    (rMinusCanonicalCellEquiv w n q)

/-- Helper toward Lemma 5.5. A marked isomorphism from the canonical
least-token side to the complete code-built decoded side, transporting all
ten relations. -/
@[expose] noncomputable def rMinusCanonicalSideMarkedIso :
    GeometricSideMarkedIso (rMinusCanonicalSide w n q) (rMinusDecodedSide w n q) where
  equiv := (rMinusDecodedToCanonicalCellEquiv w n q).symm
  relation_iff := by
    intro t u v
    have hh := rMinusCanonicalCellEquiv_relation_iff_decoded w n q t
      ((rMinusCanonicalCellEquiv w n q).symm u)
      ((rMinusCanonicalCellEquiv w n q).symm v)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hh
    exact hh

/-- Helper toward Lemma 5.5. The canonical least-token side has the class
of the code-built decoded side. -/
theorem rMinusCanonicalSide_class_eq_decodedSide :
    geometricSideClass (rMinusCanonicalSide w n q) =
      geometricSideClass (rMinusDecodedSide w n q) :=
  (geometricSideClass_eq_iff _ _).mpr ⟨rMinusCanonicalSideMarkedIso w n q⟩

end CanonicalSide

/-- Helper toward Lemma 5.5. When the presentation's whole realization
exists, its marked-isomorphism class is the class of the canonical side. -/
theorem rMinusCanonicalSide_class_eq_wholeRealization
    {x : XDP} (r : RMinusSidePresentation x)
    (hreal : r.wholeRealization.isSome) (hp : r.prefixValid)
    (hq : ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 = r.code.2) :
    geometricSideClass
      (rMinusCanonicalSide r.code.1 hp.choose hq.choose) =
      geometricSideClass (r.wholeRealization.get hreal) := by
  have hk : r.boundaryIndex ≤ 0 := by
    by_contra hn
    simp [RMinusSidePresentation.wholeRealization, hn] at hreal
  have hdecode := RMinusSidePresentation.wholeRealization_eq_some_rMinusDecodedSide
    r hk hp hq
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp hreal
  have hSdecode : S = rMinusDecodedSide r.code.1 hp.choose hq.choose :=
    Option.some.inj (hS.symm.trans hdecode)
  subst S
  simpa [hS] using rMinusCanonicalSide_class_eq_decodedSide r.code.1 hp.choose hq.choose

/-- Helper toward Lemma 5.5. The optional class reader is expressed through
the canonical least-token side under the existing realization guards. -/
theorem RMinusSidePresentation.classOption_eq_canonicalSide
    {x : XDP} (r : RMinusSidePresentation x) (hk : r.boundaryIndex ≤ 0)
    (hp : r.prefixValid)
    (hq : ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 = r.code.2) :
    r.classOption = some (geometricSideClass
      (rMinusCanonicalSide r.code.1 hp.choose hq.choose)) := by
  rw [RMinusSidePresentation.classOption_eq_some r hk hp hq]
  exact congrArg some
    (rMinusCanonicalSide_class_eq_decodedSide r.code.1 hp.choose hq.choose).symm

end DirectedDistances.PaperProofs.Section5
