module

public import DirectedDistances.PlanarMap.BdyReverseLeftEndpoint
public import DirectedDistances.PlanarMap.BdyReverseBijective
public import Mathlib.Data.Fintype.Vector

/-! # Sized restricted endpoint reversal helpers

Restricted helpers for the reflection step of Proposition 5.9 / Proposition
simple-boundary carrier, not source isomorphism classes, and are not counted.
assumed. The `l = 1` map below is the identity and does not settle I3's source
proof obligation. -/

public section
namespace DirectedDistances.PlanarMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {ℓ r l s : ℕ}

open BipolarTriangulationWithBoundary

private instance instFiniteCombinatorialMap :
    Finite (CombinatorialMap D) := by
  classical
  refine Finite.of_injective
    (fun M : CombinatorialMap D => (M.edgeInv, M.rot)) ?_
  intro M N h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨he, hr⟩
  cases M with
  | mk edgeInv edgeInv_invol edgeInv_ne rot =>
    cases N with
    | mk edgeInv' edgeInv_invol' edgeInv_ne' rot' =>
      simp_all

private instance instFiniteDirectedMapWithMissing :
    Finite (DirectedMapWithMissing D) := by
  classical
  refine Finite.of_injective
    (fun M : DirectedMapWithMissing D =>
      (M.toCombinatorialMap, {d | M.missing d}, {d | M.tail d}, M.outer)) ?_
  intro M N h
  cases M with
  | mk cm missing missing_edgeInv tail tail_iff tail_missing outer missing_outer =>
    cases N with
    | mk cm' missing' missing_edgeInv' tail' tail_iff' tail_missing' outer'
        missing_outer' =>
      simp only [Prod.mk.injEq, Set.ext_iff] at h
      rcases h with ⟨hcm, hmissing, htail, houter⟩
      have hmissing' : missing = missing' := funext fun d => propext (hmissing d)
      have htail' : tail = tail' := funext fun d => propext (htail d)
      subst cm'
      subst missing'
      subst tail'
      subst outer'
      rfl

private instance instFiniteMapVertex (M : DirectedMapWithMissing D) :
    Finite (MapVertex M) :=
  Finite.of_surjective
    (fun d : D => Quotient.mk (Equiv.Perm.SameCycle.setoid M.toCombinatorialMap.rot) d)
    Quotient.mk_surjective

private theorem finite_list_length_eq {α : Type*} [Finite α] (n : ℕ) :
    Finite {xs : List α // xs.length = n} := by
  exact (inferInstance : Finite (List.Vector α n))

private instance instFiniteSimpleDirectedDartPath
    {M : DirectedMapWithMissing D} {u v : MapVertex M} {n : ℕ} :
    Finite (SimpleDirectedDartPath M u v n) := by
  classical
  have : Finite {xs : List D // xs.length = n} :=
    finite_list_length_eq (α := D) n
  have : Finite {xs : List (MapVertex M) // xs.length = n + 1} :=
    finite_list_length_eq (α := MapVertex M) (n + 1)
  let code (P : SimpleDirectedDartPath M u v n) :
      ({xs : List D // xs.length = n} ×
        {xs : List (MapVertex M) // xs.length = n + 1}) :=
    (⟨P.darts, P.darts_length⟩,
      ⟨P.vertices, P.vertices_length⟩)
  have hcode : Function.Injective code := by
    intro P Q h
    cases P with
    | mk darts vertices darts_length vertices_length vertices_nodup start_vertex
        end_vertex edge_step =>
      cases Q with
      | mk darts' vertices' darts_length' vertices_length' vertices_nodup'
          start_vertex' end_vertex' edge_step' =>
        simp only [code, Prod.mk.injEq, Subtype.mk.injEq] at h
        rcases h with ⟨hd, hv⟩
        subst darts'
        subst vertices'
        rfl
  exact Finite.of_injective code hcode

private instance instFiniteNonemptyWord : Finite (NonemptyWord D) := by
  classical
  let code (w : NonemptyWord D) :
      {xs : List D // xs.length ≤ Fintype.card D} :=
    ⟨w.letters, w.nodup.length_le_card⟩
  have hfinite : Finite {xs : List D // xs.length ≤ Fintype.card D} := by
    have hU : (⋃ k ∈ (Finset.range (Fintype.card D + 1) : Set ℕ),
        {xs : List D | xs.length = k}).Finite := by
      apply (Finset.finite_toSet (Finset.range (Fintype.card D + 1))).biUnion
      intro k hk
      exact finite_list_length_eq (α := D) k
    have hsub : {xs : List D | xs.length ≤ Fintype.card D} ⊆
        ⋃ k ∈ (Finset.range (Fintype.card D + 1) : Set ℕ),
          {xs : List D | xs.length = k} := by
      intro xs hxs
      change xs.length ≤ Fintype.card D at hxs
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨xs.length, Finset.mem_range.mpr (by omega), rfl⟩
    exact hU.subset hsub |>.to_subtype
  let : Finite {xs : List D // xs.length ≤ Fintype.card D} := hfinite
  apply Finite.of_injective code
  intro w z h
  cases w with
  | mk letters letters_nonempty letters_nodup =>
    cases z with
    | mk letters' letters_nonempty' letters_nodup' =>
      have hletters : letters = letters' := congrArg Subtype.val h
      cases hletters
      rfl

private instance instFiniteBipolarTriangulationWithBoundary
    {a b : ℕ} : Finite (BipolarTriangulationWithBoundary D a b) := by
  classical
  let Code := Σ M : DirectedMapWithMissing D,
    Σ s : MapVertex M, Σ t : MapVertex M,
      NonemptyWord D ×
        (SimpleDirectedDartPath M s t a × SimpleDirectedDartPath M s t b)
  have : Finite Code := inferInstance
  let code (B : BipolarTriangulationWithBoundary D a b) : Code :=
    ⟨B.map, ⟨B.source, ⟨B.sink, (B.outerWord, (B.leftPath, B.rightPath))⟩⟩⟩
  apply Finite.of_injective code
  intro B C h
  cases B
  cases C
  cases h
  rfl

/-- Finiteness of the labelled restricted boundary class over a finite dart -/
instance instFiniteBoundaryMbcClass {a b : ℕ} :
    Finite (BoundaryMbcClass D a b) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- The labelled restricted boundary carrier is finite when the dart type is -/
noncomputable instance instFintypeBoundaryMbcClass
    {a b : ℕ} : Fintype (BoundaryMbcClass D a b) := by
  exact Fintype.ofFinite (BoundaryMbcClass D a b)

/-- Finiteness of each inner-edge slice. Restricted helper only; not counted; -/
instance instFiniteBoundaryMbcSizedSlice {a b s : ℕ} :
    Finite {B : BoundaryMbcClass D a b // innerEdgeCount B.val = s} :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- Every fixed inner-edge slice of the labelled restricted carrier is -/
noncomputable instance instFintypeBoundaryMbcSizedSlice
    {a b s : ℕ} :
    Fintype {B : BoundaryMbcClass D a b // innerEdgeCount B.val = s} := by
  exact Fintype.ofFinite _

/-- Edge classes of a finite dart set are finite, by the quotient map from
the darts. -/
noncomputable instance instEdgeQuotientFintype
    {M : CombinatorialMap D} : Fintype (CombinatorialMap.EdgeQuotient M) := by
  classical
  exact Quotient.fintype (Equiv.Perm.SameCycle.setoid M.edgeInv)

/-- The left and right boundary-edge classes, indexed by their simple paths.
Restricted counting helper for `lem-bdy-reverse` -/
@[expose] noncomputable def boundaryEdgeInjection
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) :
    Fin B.leftPath.darts.length ⊕ Fin B.rightPath.darts.length →
      CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap :=
  Sum.elim
    (fun i => Quotient.mk _ (B.leftPath.darts.get i))
    (fun i => Quotient.mk _ (B.rightPath.darts.get i))

private theorem simplePathEdgeOrbit_injective {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    Function.Injective (fun i : Fin P.darts.length =>
      Quotient.mk (Equiv.Perm.SameCycle.setoid M.edgeInv) (P.darts.get i)) := by
  intro i j h
  have hi := P.edge_step i
  have hj := P.edge_step j
  rcases (CombinatorialMap.edgeInv_sameCycle_iff M.toCombinatorialMap _ _).mp
      (Quotient.exact h) with he | he
  · have hv := hj.2.2.1.trans ((congrArg (dartTailVertex M) he).trans hi.2.2.1.symm)
    have heq := List.nodup_iff_injective_get.mp P.vertices_nodup hv
    exact Fin.ext (congrArg Fin.val heq).symm
  · exact False.elim (((M.tail_iff _ hi.1).mp hi.2.1)
      (by rw [← he]; exact hj.2.1))

/-- The complement of a finite edge-class carrier is finite. -/
noncomputable instance instFintypeNotBoundaryEdge
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) :
    Fintype {e : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
      e ∉ Set.range (boundaryEdgeInjection B)} := by
  classical
  exact Fintype.ofFinite _

/-- The two simple boundary paths inject into geometric edge classes, with
disjoint images. Restricted counting helper for `lem-bdy-reverse` -/
theorem boundaryEdgeInjection_injective
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) :
    Function.Injective (boundaryEdgeInjection B) := by
  intro i j h
  rcases i with i | i <;> rcases j with j | j
  · exact congrArg Sum.inl (simplePathEdgeOrbit_injective B.leftPath h)
  · exact False.elim (B.paths_edge_disjoint _ (List.get_mem _ i) _
      (List.get_mem _ j) (Quotient.exact h))
  · exact False.elim (B.paths_edge_disjoint _ (List.get_mem _ j) _
      (List.get_mem _ i) (Quotient.exact h).symm)
  · exact congrArg Sum.inr (simplePathEdgeOrbit_injective B.rightPath h)

/-- `innerEdgeCount` is the cardinality of the geometric edge classes outside
the boundary-edge injection's range. This identifies subtraction with the
actual complementary classes (`lem-bdy-reverse`, -/
theorem innerEdgeCount_eq_card_not_boundary
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) :
    innerEdgeCount B = Fintype.card
      {e : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
        e ∉ Set.range (boundaryEdgeInjection B)} := by
  classical
  have hrange : Fintype.card {e : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap // e ∈ Set.range (boundaryEdgeInjection B)} = ℓ + r := by
    calc
      _ = Fintype.card
          (Fin B.leftPath.darts.length ⊕ Fin B.rightPath.darts.length) :=
        Fintype.card_congr (Equiv.ofInjective (boundaryEdgeInjection B)
          (boundaryEdgeInjection_injective B)).symm
      _ = ℓ + r := by simp [B.leftPath.darts_length, B.rightPath.darts_length]
  rw [Fintype.card_subtype_compl (p := fun e : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => e ∈ Set.range (boundaryEdgeInjection B)), hrange]
  simp only [innerEdgeCount, CombinatorialMap.numEdges]

/-- Left-prefix reversal preserves the complementary geometric edge count.
Restricted helper for `lem-bdy-reverse` -/
theorem leftPrefixReversal_innerEdgeCount
    {a b : ℕ} (B : BipolarTriangulationWithBoundary D a b) (k : ℕ)
    (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    innerEdgeCount (leftPrefixReversal B k hk hka hbc) = innerEdgeCount B := by
  unfold leftPrefixReversal
  rw [mirror_innerEdgeCount,
    rightPrefixReversal_innerEdgeCount B.mirror k hk hka
      (mirror_isBoundaryChanneled hbc), mirror_innerEdgeCount]

private theorem boundaryMbcClassEquiv_innerEdgeCount
    {a b c d : ℕ} (ha : a = c) (hb : b = d)
    (B : BoundaryMbcClass D a b) :
    innerEdgeCount (boundaryMbcClassEquiv (D := D) ha hb B).val =
      innerEdgeCount B.val := by
  cases ha
  cases hb
  rfl

private theorem leftPrefixReversalMbc_innerEdgeCount
    {a b : ℕ} (k : ℕ) (hk : 1 ≤ k) (hka : k < a)
    (B : BoundaryMbcClass D a b) :
    innerEdgeCount (leftPrefixReversalMbc (D := D) (a := a) (b := b)
      k hk hka B).val = innerEdgeCount B.val :=
  leftPrefixReversal_innerEdgeCount B.val k hk hka B.property

/-- The literal left endpoint equivalence preserves inner-edge size for -/
theorem leftEndpointReversalEquiv_innerEdgeCount {l : ℕ} (hl : 2 ≤ l)
    (B : BoundaryMbcClass D l 1) :
    innerEdgeCount (leftEndpointReversalEquiv (D := D) hl B).val =
      innerEdgeCount B.val := by
  simp only [leftEndpointReversalEquiv, Equiv.trans_apply, Equiv.ofBijective_apply]
  exact (boundaryMbcClassEquiv_innerEdgeCount (D := D) (by omega) (by omega)
      (leftPrefixReversalMbc (D := D) (a := l) (b := 1) (l - 1)
        (by omega) (by omega) B)).trans
    (leftPrefixReversalMbc_innerEdgeCount (D := D) (l - 1) (by omega)
      (by omega) B)

/-- Endpoint symmetry preserves inner-edge size when `l ≥ 2`; the identity -/
theorem endpointSymmetryEquiv_innerEdgeCount_of_two (l : ℕ) (hl : 2 ≤ l)
    (B : BoundaryMbcClass D l 1) :
    innerEdgeCount (endpointSymmetryEquiv (D := D) l (by omega) B).val =
      innerEdgeCount B.val := by
  rw [endpointSymmetryEquiv_of_two (D := D) hl]
  exact leftEndpointReversalEquiv_innerEdgeCount (D := D) hl B

/-- The exposed identity endpoint equivalence preserves inner-edge size at -/
theorem leftEndpointReversalEquiv_innerEdgeCount_one
    (B : BoundaryMbcClass D 1 1) :
    innerEdgeCount (leftEndpointReversalEquiv_one (D := D) B).val =
      innerEdgeCount B.val := rfl

/-- Endpoint symmetry preserves inner-edge size for every positive `l`,
including the identity case `l = 1`. Restricted helper for -/
theorem endpointSymmetryEquiv_innerEdgeCount (l : ℕ) (hl : 1 ≤ l)
    (B : BoundaryMbcClass D l 1) :
    innerEdgeCount (endpointSymmetryEquiv (D := D) l hl B).val =
      innerEdgeCount B.val := by
  by_cases h : l = 1
  · subst l
    rw [endpointSymmetryEquiv_one]
    exact leftEndpointReversalEquiv_innerEdgeCount_one (D := D) B
  · have hl' : 2 ≤ l := by omega
    exact endpointSymmetryEquiv_innerEdgeCount_of_two (D := D) l hl' B

/-- The inverse endpoint symmetry preserves size for every positive `l`. -/
theorem endpointSymmetryEquiv_symm_innerEdgeCount (l : ℕ) (hl : 1 ≤ l)
    (B : BoundaryMbcClass D 1 l) :
    innerEdgeCount ((endpointSymmetryEquiv (D := D) l hl).symm B).val =
      innerEdgeCount B.val := by
  have h := endpointSymmetryEquiv_innerEdgeCount (D := D) l hl
    ((endpointSymmetryEquiv (D := D) l hl).symm B)
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- The sized-slice equivalence induced by endpoint symmetry for every
positive `l`, extending the `l ≥ 2` helper to its identity endpoint case. -/
@[expose] noncomputable def endpointSymmetrySizedEquiv (l s : ℕ)
    (hl : 1 ≤ l) :
    {B : BoundaryMbcClass D l 1 // innerEdgeCount B.val = s} ≃
      {B : BoundaryMbcClass D 1 l // innerEdgeCount B.val = s} := by
  let E := endpointSymmetryEquiv (D := D) l hl
  refine E.subtypeEquiv ?_
  intro B
  have h := endpointSymmetryEquiv_innerEdgeCount (D := D) l hl B
  constructor
  · intro hs
    exact h.trans hs
  · intro hs
    exact h.symm.trans hs

/-- The inverse endpoint symmetry also preserves size for `l ≥ 2`. -/
theorem endpointSymmetryEquiv_symm_innerEdgeCount_of_two (l : ℕ) (hl : 2 ≤ l)
    (B : BoundaryMbcClass D 1 l) :
    innerEdgeCount ((endpointSymmetryEquiv (D := D) l (by omega)).symm B).val =
      innerEdgeCount B.val := by
  have h := endpointSymmetryEquiv_innerEdgeCount_of_two (D := D) l hl
    ((endpointSymmetryEquiv (D := D) l (by omega)).symm B)
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- The size-slice equivalence induced by endpoint symmetry for `l ≥ 2`.
paper-source claim. -/
@[expose] noncomputable def endpointSymmetrySizedEquiv_of_two (l s : ℕ)
    (hl : 2 ≤ l) :
    {B : BoundaryMbcClass D l 1 // innerEdgeCount B.val = s} ≃
      {B : BoundaryMbcClass D 1 l // innerEdgeCount B.val = s} := by
  have hpos : 1 ≤ l := by omega
  let E := endpointSymmetryEquiv (D := D) l hpos
  refine E.subtypeEquiv ?_
  intro B
  have h := endpointSymmetryEquiv_innerEdgeCount_of_two (D := D) l hl B
  constructor
  · intro hs
    exact h.trans hs
  · intro hs
    exact h.symm.trans hs

private theorem rightPrefixReversalMbc_innerEdgeCount
    {a b : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkb : k < b)
    (B : BoundaryMbcClass D a b) :
    innerEdgeCount (rightPrefixReversalMbc (D := D) (ℓ := a) (r := b)
      k hk hkb B).val = innerEdgeCount B.val :=
  rightPrefixReversal_innerEdgeCount B.val k hk hkb B.property

/-- The literal right endpoint reversal preserves inner-edge size for `r ≥ 2`. -/
theorem rightEndpointReversalEquiv_innerEdgeCount {r : ℕ} (hr : 2 ≤ r)
    (B : BoundaryMbcClass D 1 r) :
    innerEdgeCount (rightEndpointReversalEquiv (D := D) hr B).val =
      innerEdgeCount B.val := by
  simp only [rightEndpointReversalEquiv, Equiv.trans_apply, Equiv.ofBijective_apply]
  exact (boundaryMbcClassEquiv_innerEdgeCount (D := D) (by omega) (by omega)
      (rightPrefixReversalMbc (D := D) (ℓ := 1) (r := r) (r - 1)
        (by omega) (by omega) B)).trans
    (rightPrefixReversalMbc_innerEdgeCount (D := D) (r - 1) (by omega)
      (by omega) B)

/-- The inner-edge equality predicate is preserved by the literal endpoint -/
theorem rightEndpointReversal_size_iff (r s : ℕ) (hr : 2 ≤ r)
    (B : BoundaryMbcClass D 1 r) :
    innerEdgeCount B.val = s ↔
      innerEdgeCount (rightEndpointReversalEquiv (D := D) hr B).val = s := by
  have h := rightEndpointReversalEquiv_innerEdgeCount (D := D) hr B
  constructor
  · intro hs
    exact h.trans hs
  · intro hs
    exact h.symm.trans hs

/-- Literal right endpoint reversal on every inner-edge size slice. Restricted -/
@[expose] noncomputable def rightEndpointReversalSizedEquiv (r s : ℕ)
    (hr : 2 ≤ r) :
    {B : BoundaryMbcClass D 1 r // innerEdgeCount B.val = s} ≃
      {B : BoundaryMbcClass D r 1 // innerEdgeCount B.val = s} :=
  (rightEndpointReversalEquiv (D := D) hr).subtypeEquiv
    (rightEndpointReversal_size_iff (D := D) r s hr)

/-- Underlying class map of the right endpoint size-slice equivalence. -/
theorem rightEndpointReversalSizedEquiv_val {r s : ℕ} (hr : 2 ≤ r)
    (B : {B : BoundaryMbcClass D 1 r // innerEdgeCount B.val = s}) :
    (rightEndpointReversalSizedEquiv (D := D) r s hr B).val =
      rightEndpointReversalEquiv (D := D) hr B.val := by
  simp only [rightEndpointReversalSizedEquiv, Equiv.subtypeEquiv_apply]

/-- Transport a marked right-prefix edge together with every fixed-size
restricted class to the literal `(r,1)` carrier. The second coordinate is
reversed, and so indexes the same geometric edge. This is a labelled helper; -/
@[expose] noncomputable def endpointMissingRootSizedTransport (r s : ℕ)
    (hr : 2 ≤ r) :
    ({B : BoundaryMbcClass D 1 r // innerEdgeCount B.val = s} × Fin (r - 1)) ≃
      ({B : BoundaryMbcClass D r 1 // innerEdgeCount B.val = s} × Fin (r - 1)) where
  toFun Bi := ((rightEndpointReversalSizedEquiv (D := D) r s hr) Bi.1, Bi.2.rev)
  invFun Bi := ((rightEndpointReversalSizedEquiv (D := D) r s hr).symm Bi.1,
    Bi.2.rev)
  left_inv := by
    rintro ⟨B, i⟩
    apply Prod.ext
    · exact (rightEndpointReversalSizedEquiv (D := D) r s hr).left_inv B
    · exact Fin.rev_rev i
  right_inv := by
    rintro ⟨B, i⟩
    apply Prod.ext
    · exact (rightEndpointReversalSizedEquiv (D := D) r s hr).right_inv B
    · exact Fin.rev_rev i

@[simp] theorem endpointMissingRootSizedTransport_apply {r s : ℕ}
    (hr : 2 ≤ r)
    (B : {B : BoundaryMbcClass D 1 r // innerEdgeCount B.val = s})
    (i : Fin (r - 1)) :
    endpointMissingRootSizedTransport (D := D) r s hr (B, i) =
      (rightEndpointReversalSizedEquiv (D := D) r s hr B, i.rev) := rfl

/-- The endpoint missing-root transport pushes the counting-normalised
uniform measure on the marked `(1,r)` size slice to the uniform measure on
the marked `(r,1)` size slice. Restricted labelled-carrier helper for -/
theorem endpointMissingRootSizedTransport_uniform (r s : ℕ) (hr : 2 ≤ r) :
    let A :=
      {B : BoundaryMbcClass D 1 r // innerEdgeCount B.val = s} × Fin (r - 1)
    let C :=
      {B : BoundaryMbcClass D r 1 // innerEdgeCount B.val = s} × Fin (r - 1)
    ∀ (mA : MeasurableSpace A) (mC : MeasurableSpace C)
      [MeasurableSingletonClass A] [MeasurableSingletonClass C],
      (@uniformCountingMeasure A inferInstance mA).map
          (endpointMissingRootSizedTransport (D := D) r s hr) =
        @uniformCountingMeasure C inferInstance mC := by
  intro A C mA mC hA hC
  exact uniformCountingMeasure_map_of_bijective
    (endpointMissingRootSizedTransport (D := D) r s hr)
    (endpointMissingRootSizedTransport (D := D) r s hr).bijective

private theorem boundaryMbcClassEquiv_leftPath_darts
    {a b c d : ℕ} (ha : a = c) (hb : b = d)
    (B : BoundaryMbcClass D a b) :
    (boundaryMbcClassEquiv (D := D) ha hb B).val.leftPath.darts =
      B.val.leftPath.darts := by
  cases ha
  cases hb
  rfl

private theorem rightEndpointReversalEquiv_leftPath_darts {r : ℕ}
    (hr : 2 ≤ r) (B : BoundaryMbcClass D 1 r) :
    (rightEndpointReversalEquiv (D := D) hr B).val.leftPath.darts =
      (rightPrefixReversal B.val (r - 1) (by omega) (by omega)
        B.property).leftPath.darts := by
  simp only [rightEndpointReversalEquiv, Equiv.trans_apply]
  exact boundaryMbcClassEquiv_leftPath_darts (D := D) (by omega) (by omega)
    (rightPrefixReversalMbc (D := D) (ℓ := 1) (r := r) (r - 1)
      (by omega) (by omega) B)

private theorem endpointMissingRootSizedTransport_fst {r s : ℕ}
    (hr : 2 ≤ r) (B : {B : BoundaryMbcClass D 1 r // innerEdgeCount B.val = s})
    (i : Fin (r - 1)) :
    (endpointMissingRootSizedTransport (D := D) r s hr (B, i)).1.val =
      rightEndpointReversalEquiv (D := D) hr B.val := by
  change ((rightEndpointReversalSizedEquiv (D := D) r s hr).prodCongr
    Fin.revPerm (B, i)).1.val = _
  rw [Equiv.prodCongr_apply]
  exact rightEndpointReversalSizedEquiv_val (D := D) hr B

private theorem endpointMissingRootSizedTransport_snd {r s : ℕ}
    (hr : 2 ≤ r) (B : {B : BoundaryMbcClass D 1 r // innerEdgeCount B.val = s})
    (i : Fin (r - 1)) :
    (endpointMissingRootSizedTransport (D := D) r s hr (B, i)).2 = i.rev := by
  rfl

private theorem rightEndpointReversalSizedEquiv_leftPath_darts {r s : ℕ}
    (hr : 2 ≤ r)
    (B : {B : BoundaryMbcClass D 1 r // innerEdgeCount B.val = s}) :
    (rightEndpointReversalSizedEquiv (D := D) r s hr B).val.val.leftPath.darts =
      (rightPrefixReversal B.val.val (r - 1) (by omega) (by omega)
        B.val.property).leftPath.darts := by
  calc
    (rightEndpointReversalSizedEquiv (D := D) r s hr B).val.val.leftPath.darts =
        (rightEndpointReversalEquiv (D := D) hr B.val).val.leftPath.darts := by
      rw [rightEndpointReversalSizedEquiv_val]
    _ = (rightPrefixReversal B.val.val (r - 1) (by omega) (by omega)
          B.val.property).leftPath.darts :=
      rightEndpointReversalEquiv_leftPath_darts (D := D) hr B.val

/-- The size-preserving marked-root transport carries each marked right
prefix dart to the same geometric edge on the left boundary. Its missing-root
designation is downstream; this theorem creates no orientation on the edge. -/
theorem endpointMissingRootSizedTransport_sameEdge {r s : ℕ} (hr : 2 ≤ r)
    (B : {B : BoundaryMbcClass D 1 r // innerEdgeCount B.val = s})
    (i : Fin (r - 1)) :
    let C := endpointMissingRootSizedTransport (D := D) r s hr (B, i)
    Equiv.Perm.SameCycle B.val.val.map.edgeInv
      (B.val.val.rightPath.darts[i.val]'(by rw [B.val.val.rightPath.darts_length]; omega))
      (C.1.val.val.leftPath.darts[C.2.val]'(by
        rw [C.1.val.val.leftPath.darts_length]
        have := C.2.isLt
        omega)) := by
  simp only [endpointMissingRootSizedTransport_apply]
  simp_rw [rightEndpointReversalSizedEquiv_leftPath_darts]
  apply (CombinatorialMap.edgeInv_sameCycle_iff
    B.val.val.map.toCombinatorialMap _ _).mpr
  exact Or.inr (rightPrefixReversal_index_dart B.val.val (r - 1)
    (by omega) (by omega) B.val.property i)

end DirectedDistances.PlanarMap
