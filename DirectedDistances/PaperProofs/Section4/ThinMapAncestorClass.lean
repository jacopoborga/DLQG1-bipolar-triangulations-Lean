module

public import DirectedDistances.PaperProofs.Section4.ThinMapArcConfinement
public import DirectedDistances.PaperProofs.Section4.ThinIndependenceFinal

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

The finite cut decoder is total and compatible with every good cut. Its extracted
class below is deliberately named `selectedCutAncestorClass`: its identification
with the geometric ancestor restriction is not proved here. `SourceAncestorCutRealization`
records that remaining obligation using the complete marked restriction relation.
No geometric `sourceAncestorClass` is defined by renaming the decoder. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter
open scoped Classical

local notation "Ω" => (ℕ → ℤ × ℤ)

section GeometricRestriction

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
  (P : InfinitePresentPath w ⟨0⟩)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Unconditional geometric vertex exhaustion after arc confinement. -/
theorem sideVertex_mem_sourceAncestorVertices_some
    (hcuts : {v : ℕ | mapCutVertex w hfin v}.Infinite) (a : ThinMapSide)
    (v : ℕ) (hv : v ∈ sideVertices w hfin hL htrans hR P a) :
    ∃ s, v ∈ sourceAncestorVertices w hfin hL htrans hR P a s :=
  sideVertex_mem_sourceAncestorVertices_some_of_interiorArcConfinement
    w hfin hL htrans hR P hcuts a
    (thinMapInteriorArcConfinement w hfin hL htrans hR P a) v hv

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Unconditional geometric edge exhaustion, retaining missing geometric edges. -/
theorem sideEdge_mem_sourceAncestorEdges_some
    (hcuts : {v : ℕ | mapCutVertex w hfin v}.Infinite) (a : ThinMapSide)
    (e : ℕ) (he : e ∈ sideEdges w hfin hL htrans hR P a) :
    ∃ s, e ∈ sourceAncestorEdges w hfin hL htrans hR P a s :=
  sideEdge_mem_sourceAncestorEdges_some_of_interiorArcConfinement
    w hfin hL htrans hR P hcuts a
    (thinMapInteriorArcConfinement w hfin hL htrans hR P a) e he

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both darts of each geometric ancestor edge, including missing edges. -/
@[expose] noncomputable def sourceAncestorDarts (a : ThinMapSide) (s : ℕ) :
    Set (ℕ × Bool) :=
  {d | d.1 ∈ sourceAncestorEdges w hfin hL htrans hR P a s}

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The geometric ancestor dart carrier is finite without assuming edge presence. -/
theorem sourceAncestorDarts_finite (a : ThinMapSide) (s : ℕ) :
    (sourceAncestorDarts w hfin hL htrans hR P a s).Finite := by
  apply ((sourceAncestorEdges_finite w hfin hL htrans hR P a s).prod
    (Set.finite_univ : (Set.univ : Set Bool).Finite)).subset
  intro d hd
  exact ⟨hd, Set.mem_univ d.2⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The geometric vertex and dart carriers of the source ancestor restriction. -/
abbrev SourceAncestorCell (a : ThinMapSide) (s : ℕ) :=
  Sum (sourceAncestorVertices w hfin hL htrans hR P a s)
    (sourceAncestorDarts w hfin hL htrans hR P a s)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The entire geometric restriction carrier is finite. -/
theorem sourceAncestorCell_finite (a : ThinMapSide) (s : ℕ) :
    Finite (SourceAncestorCell w hfin hL htrans hR P a s) := by
  let := (sourceAncestorVertices_finite w hfin hL htrans hR P a s).to_subtype
  let := (sourceAncestorDarts_finite w hfin hL htrans hR P a s).to_subtype
  infer_instance

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A retained inner triangle has all its geometric edges in the ancestor restriction.
The creation list distinguishes inner triangles from the exterior face. -/
@[expose] noncomputable def sourceAncestorRetainedFace
    (a : ThinMapSide) (s : ℕ) (d : ℕ × Bool) : Prop :=
  ∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j ∧
    ∀ e ∈ stageTriangleDartList w j,
      e ∈ sourceAncestorDarts w hfin hL htrans hR P a s

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The geometric restriction keeps permanent dart IDs, presence, induced rotation,
inner faces and every original exterior-boundary and seam index. -/
@[expose] noncomputable def sourceAncestorRelation (a : ThinMapSide) (s : ℕ) :
    TruncationRelation → SourceAncestorCell w hfin hL htrans hR P a s →
      SourceAncestorCell w hfin hL htrans hR P a s → Prop
  | .vertex, .inl _, _ => True
  | .root, .inl v, _ => v.1 = 0
  | .target, .inl v, _ => v.1 = thinMapBoundaryVertex w hfin hL htrans hR a s
  | .incident, .inr d, .inl v =>
      (if d.1.2 then edgeEast w d.1.1 else edgeWest w d.1.1) = v.1
  | .opposite, .inr d, .inr e => (d.1.1, !d.1.2) = e.1
  | .oriented, .inr d, _ => EdgePresent w d.1.1 ∧ d.1.2 = false
  | .rotation, .inr d, .inr e => ∃ k : ℕ, 0 < k ∧
      (kmswInfRot w hfin : (ℕ × Bool) → ℕ × Bool)^[k] d.1 = e.1 ∧
        ∀ j : ℕ, 0 < j → j < k →
          (kmswInfRot w hfin : (ℕ × Bool) → ℕ × Bool)^[j] d.1 ∉
            sourceAncestorDarts w hfin hL htrans hR P a s
  | .faceNext, .inr d, .inr e =>
      sourceAncestorRetainedFace w hfin hL htrans hR P a s d.1 ∧
        kmswInfFaceSucc w hfin d.1 = e.1
  | .boundary i, .inr d, _ => thinMapBoundaryDart w hfin hL htrans hR a i = d.1
  | .seam i, .inr d, _ => (P.edge i, false) = d.1
  | _, _, _ => False

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Two explicit geometric identifications give the same finite class. This algebraic
uniqueness lemma does not construct either identification. -/
theorem finiteThinMapOfAncestors_eq_of_sourceAncestor_isos
    (a : ThinMapSide) (s : ℕ) {ℓ r n ℓ' r' n' : ℕ}
    (R : KMSWMapRep ℓ r n) (S : KMSWMapRep ℓ' r' n')
    (v : MapVertex R.B.map) (v' : MapVertex S.B.map)
    (e : TruncationCell (presentation R a v) ≃
      SourceAncestorCell w hfin hL htrans hR P a s)
    (f : TruncationCell (presentation S a v') ≃
      SourceAncestorCell w hfin hL htrans hR P a s)
    (he : ∀ t x y, truncationRelation (presentation R a v) t x y ↔
      sourceAncestorRelation w hfin hL htrans hR P a s t (e x) (e y))
    (hf : ∀ t x y, truncationRelation (presentation S a v') t x y ↔
      sourceAncestorRelation w hfin hL htrans hR P a s t (f x) (f y)) :
    finiteThinMapOfAncestors R a v = finiteThinMapOfAncestors S a v' := by
  apply (finiteThinMapOfAncestors_eq_iff R S a a v v').mpr
  refine ⟨e.trans f.symm, ?_⟩
  intro t x y
  exact (he t x y).trans (by
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
      (hf t (f.symm (e x)) (f.symm (e y))).symm)

end GeometricRestriction

section CoherentDomain

variable (x : XDP) (T : ℕ → Ω → ℕ∞)
  (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Finite incidence on the coherent domain. -/
theorem sourceAncestor_finite_incidence (q : selectedCutCoherentDomain x T hT) :
    let w := boltzmannKMSWStream (pathCode q.1)
    ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite := by
  obtain ⟨_, _, _, _, _, hfin, _⟩ := selectedCutCoherentDomain_spec x T hT q
  exact hfin

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Left-coordinate transience on the coherent domain. -/
theorem sourceAncestor_left_transient (q : selectedCutCoherentDomain x T hT) :
    Tendsto (L (boltzmannKMSWStream (pathCode q.1))) atTop atTop := by
  obtain ⟨_, _, _, _, _, _, htrans, _⟩ := selectedCutCoherentDomain_spec x T hT q
  exact htrans

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The right coordinate is unbounded below on the coherent domain. -/
theorem sourceAncestor_right_unbounded (q : selectedCutCoherentDomain x T hT) :
    ∀ a : ℤ, ∃ n, R (boltzmannKMSWStream (pathCode q.1)) n ≤ a := by
  obtain ⟨_, _, _, _, _, _, _, hR, _⟩ := selectedCutCoherentDomain_spec x T hT q
  exact hR

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The left coordinate is nonnegative on the coherent domain. -/
theorem sourceAncestor_left_nonneg (q : selectedCutCoherentDomain x T hT) :
    ∀ j, 0 ≤ L (boltzmannKMSWStream (pathCode q.1)) j := by
  obtain ⟨_, _, _, _, _, _, _, _, hL, _⟩ := selectedCutCoherentDomain_spec x T hT q
  exact hL

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical infinite leftmost XDP path used in the selected-cut prefix API.
Both extremal existence witnesses are supplied by the coherent domain. -/
@[expose] noncomputable def sourceAncestorPath (q : selectedCutCoherentDomain x T hT) :
    InfinitePresentPath (boltzmannKMSWStream (pathCode q.1)) ⟨0⟩ :=
  by
    obtain ⟨hgL, hgS⟩ := selectedCutCoherentDomain_infinite_extremal x T hT q
    have hfin := sourceAncestor_finite_incidence x T hT q
    have hL := sourceAncestor_left_nonneg x T hT q
    have htrans := sourceAncestor_left_transient x T hT q
    have hR := sourceAncestor_right_unbounded x T hT q
    cases x with
    | ldp => exact kmswLeftmostLdpPath _ hfin hL htrans hR 0 hgL
    | sdp => exact kmswLeftmostSdpPath _ hfin hL htrans hR 0 hgS

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The existing finite cut class extracted from the total decoder. Geometric -/
@[expose] noncomputable def selectedCutAncestorClass
    (a : ThinMapSide) (s : ℕ) (q : selectedCutCoherentDomain x T hT) : FiniteThinMap :=
  (thinTruncationAt x T hT a s q).get (thinTruncationAt_isSome x T hT a s q)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Total decoding of the finite cut class, without a geometric identification claim. -/
theorem thinTruncationAt_eq_some_selectedCutAncestorClass
    (a : ThinMapSide) (s : ℕ) (q : selectedCutCoherentDomain x T hT) :
    thinTruncationAt x T hT a s q = some (selectedCutAncestorClass x T hT a s q) :=
  (Option.some_get (thinTruncationAt_isSome x T hT a s q)).symm




theorem halfTruncate_eq_some_selectedCutAncestorClass
    (a : ThinMapSide) (s k : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    halfTruncate a s (selectedCutSide x T a k q.1) =
      some (selectedCutAncestorClass x T hT a s q) :=
  (thinTruncationAt_decode x T hT a s k q hk).symm.trans
    (thinTruncationAt_eq_some_selectedCutAncestorClass x T hT a s q)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every good cut has a concrete finite half and an existing indexed target whose
ancestor class is the decoded class. No geometric carrier identification is claimed. -/
theorem selectedCutAncestorClass_representation
    (a : ThinMapSide) (s k : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    ∃ (ℓ r n : ℕ) (R : KMSWMapRep ℓ r n) (v : MapVertex R.B.map),
      selectedCutSide x T a k q.1 = some ⟨r, ⟨ℓ, ⟨n, KMSWMapIsoClass.mk R⟩⟩⟩ ∧
      boundaryTarget R.B a s = some v ∧
      finiteThinMapOfAncestors R a v = selectedCutAncestorClass x T hT a s q := by
  obtain ⟨ℓ, r, n, d, R, hR, _, _, hc⟩ :=
    selectedCutPastCuts_representatives x T hT q k s hk
  have hrep : ∃ (ℓ' r' n' : ℕ) (S : KMSWMapRep ℓ' r' n'),
      selectedCutSide x T a k q.1 =
        some ⟨r', ⟨ℓ', ⟨n', KMSWMapIsoClass.mk S⟩⟩⟩ := by
    cases a with
    | left =>
      refine ⟨ℓ, d, (cutLRep R hR).1, (cutLRep R hR).2, ?_⟩
      exact congrArg Prod.fst hc
    | right =>
      refine ⟨d, r, (cutRRep R hR).1, (cutRRep R hR).2, ?_⟩
      exact congrArg Prod.snd hc
  obtain ⟨ℓ', r', n', S, hS⟩ := hrep
  have heq := halfTruncate_eq_some_selectedCutAncestorClass x T hT a s k q hk
  rw [hS, halfTruncate_some_mk_boundaryTarget] at heq
  obtain ⟨v, hv, hclass⟩ := Option.map_eq_some_iff.mp heq
  exact ⟨ℓ', r', n', S, v, hS, hv, hclass⟩




theorem thinSideCode_eq_iff_selectedCutAncestorClasses_eq
    (a : ThinMapSide) (q q' : selectedCutCoherentDomain x T hT) :
    thinSideCode x T hT a q.1 = thinSideCode x T hT a q'.1 ↔
      (fun s => selectedCutAncestorClass x T hT a s q) =
        (fun s => selectedCutAncestorClass x T hT a s q') := by
  rw [thinSideCode_coe, thinSideCode_coe]
  constructor
  · intro h
    funext s
    apply Option.some.inj
    exact (thinTruncationAt_eq_some_selectedCutAncestorClass x T hT a s q).symm.trans
      ((congrFun h s).trans
        (thinTruncationAt_eq_some_selectedCutAncestorClass x T hT a s q'))
  · intro h
    funext s
    rw [thinTruncationAt_eq_some_selectedCutAncestorClass,
      thinTruncationAt_eq_some_selectedCutAncestorClass, congrFun h s]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Exact unresolved geometric realization at every good cut. The equivalence must
preserve all incidence, orientation, induced rotations, faces and indexed markings.
This proposition is isolated, not asserted or consumed as a source hypothesis. -/
@[expose] noncomputable def SourceAncestorCutRealization : Prop :=
  ∀ (a : ThinMapSide) (s k : ℕ) (q : selectedCutCoherentDomain x T hT),
    (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
    ∃ (ℓ r n : ℕ) (R : KMSWMapRep ℓ r n) (v : MapVertex R.B.map),
      selectedCutSide x T a k q.1 = some ⟨r, ⟨ℓ, ⟨n, KMSWMapIsoClass.mk R⟩⟩⟩ ∧
      boundaryTarget R.B a s = some v ∧
      ∃ e : TruncationCell (presentation R a v) ≃
          SourceAncestorCell (boltzmannKMSWStream (pathCode q.1))
            (sourceAncestor_finite_incidence x T hT q) (sourceAncestor_left_nonneg x T hT q)
            (sourceAncestor_left_transient x T hT q) (sourceAncestor_right_unbounded x T hT q)
            (sourceAncestorPath x T hT q) a s,
        ∀ t u z, truncationRelation (presentation R a v) t u z ↔
          sourceAncestorRelation (boltzmannKMSWStream (pathCode q.1))
            (sourceAncestor_finite_incidence x T hT q) (sourceAncestor_left_nonneg x T hT q)
            (sourceAncestor_left_transient x T hT q) (sourceAncestor_right_unbounded x T hT q)
            (sourceAncestorPath x T hT q) a s t (e u) (e z)

end CoherentDomain
end DirectedDistances.PaperProofs.Section4
