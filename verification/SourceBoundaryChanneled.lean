/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWLeftTargetSize
public import DirectedDistances.PlanarMap.KMSWMapSimpleBoundary
public import DirectedDistances.KMSW.KMSWLeftUniformLaw
public import DirectedDistances.Paper.Section3.BdyReverse
public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedAssembly5

/-!
# Current-paper boundary-channeled view

The source view retains the general channeling predicate and requires simple outer boundary,
with the single-edge map allowed separately. The general core predicates remain unchanged.
-/

public section
namespace DirectedDistances.PlanarMap

open MeasureTheory DirectedDistances.KMSW
open scoped Classical

namespace KMSWMapIsoClass

variable {ℓ r N : ℕ}

/-- The graded isomorphism class is exactly the single-edge map `m₀`. -/
@[expose] def IsSingleEdgeClass (q : KMSWMapIsoClass ℓ r N) : Prop :=
  ℓ = 1 ∧ r = 1 ∧ N = 1 ∧ HEq q (mk KMSWMapRep.singleEdge)

/-- Definition 3.17 in the current paper: primary channeling and simple boundary,
with the single-edge class allowed. -/
@[expose] def IsSourceBoundaryChanneled (q : KMSWMapIsoClass ℓ r N) : Prop :=
  q.IsChanneled ∧ (q.IsSimpleOuterBoundary ∨ q.IsSingleEdgeClass)

/-- A nonsingleton `(1,1)` representative has simple outer boundary. -/
theorem isSimpleOuterBoundary_one_one (q : KMSWMapIsoClass 1 1 N)
    (hN : 2 ≤ N) : q.IsSimpleOuterBoundary := by
  induction q using KMSWMapIsoClass.ind with
  | h R =>
    apply (isSimpleOuterBoundary_mk R).2
    exact ⟨(R.toStrongOneOne hN).paths_internally_vertex_disjoint,
      R.oneOne_paths_edge_disjoint hN⟩

/-- On every positive left length and right length one, the paper view coincides
with the original channeling predicate, including the zero-step singleton. -/
theorem isSourceBoundaryChanneled_iff_right_one (hℓ : 1 ≤ ℓ)
    (q : KMSWMapIsoClass ℓ 1 N) : q.IsSourceBoundaryChanneled ↔ q.IsChanneled := by
  refine ⟨And.left, fun hq => ⟨hq, ?_⟩⟩
  by_cases hℓ2 : 2 ≤ ℓ
  · exact Or.inl (isSimpleOuterBoundary_of_rightEndpoint hℓ2 q)
  · have hℓ1 : ℓ = 1 := by omega
    subst ℓ
    by_cases hN : 2 ≤ N
    · exact Or.inl (isSimpleOuterBoundary_one_one q hN)
    · have hs := kmswLeftClass_eq_zeroStep_of_lt_two ⟨q, hq⟩ (by omega) (by omega)
      have hN1 : N = 1 := hs.2.1
      subst N
      have hz := kmswZeroStepMapClass_unique ⟨q, hq⟩
      have hz0 := kmswZeroStepMapClass_unique
        ⟨mk KMSWMapRep.singleEdge,
          (isChanneled_mk _).2 kmswZeroStep_singleEdge_isChanneled⟩
      have heq : q = mk KMSWMapRep.singleEdge :=
        congrArg Subtype.val (hz.trans hz0.symm)
      exact Or.inr ⟨rfl, rfl, rfl, heq_of_eq heq⟩

/-- For left length at least two the singleton alternative is impossible. -/
theorem isSourceBoundaryChanneled_iff_of_two_le_left (hℓ : 2 ≤ ℓ)
    (q : KMSWMapIsoClass ℓ r N) :
    q.IsSourceBoundaryChanneled ↔ q.IsChanneled ∧ q.IsSimpleOuterBoundary := by
  constructor
  · rintro ⟨hc, hs | hz⟩
    · exact ⟨hc, hs⟩
    · have h := hz.1
      omega
  · rintro ⟨hc, hs⟩
    exact ⟨hc, Or.inl hs⟩

/-- For right length at least two the singleton alternative is impossible. -/
theorem isSourceBoundaryChanneled_iff_of_two_le_right (hr : 2 ≤ r)
    (q : KMSWMapIsoClass ℓ r N) :
    q.IsSourceBoundaryChanneled ↔ q.IsChanneled ∧ q.IsSimpleOuterBoundary := by
  constructor
  · rintro ⟨hc, hs | hz⟩
    · exact ⟨hc, hs⟩
    · have h := hz.2.1
      omega
  · rintro ⟨hc, hs⟩
    exact ⟨hc, Or.inl hs⟩

/-- Filtering any finite ensemble by the current-paper view gives exactly the original
right-boundary-one channeled ensemble. -/
theorem filter_isSourceBoundaryChanneled_right_one (hℓ : 1 ≤ ℓ)
    (s : Finset (KMSWMapIsoClass ℓ 1 N)) :
    s.filter (fun q => q.IsSourceBoundaryChanneled) = s.filter (fun q => q.IsChanneled) := by
  classical
  ext q
  simp only [Finset.mem_filter, isSourceBoundaryChanneled_iff_right_one hℓ]

/-- Every measure has the same restriction to either right-boundary-one class;
thus ensemble weights and normalizers are not changed by the source view. -/
theorem restrict_isSourceBoundaryChanneled_right_one (hℓ : 1 ≤ ℓ)
    [MeasurableSpace (KMSWMapIsoClass ℓ 1 N)]
    (μ : Measure (KMSWMapIsoClass ℓ 1 N)) :
    μ.restrict {q | q.IsSourceBoundaryChanneled} = μ.restrict {q | q.IsChanneled} := by
  have hset : {q : KMSWMapIsoClass ℓ 1 N | q.IsSourceBoundaryChanneled} =
      {q | q.IsChanneled} := by
    ext q
    exact isSourceBoundaryChanneled_iff_right_one hℓ q
  rw [hset]

/-- On the original channeled sample space every sample satisfies the paper view;
restriction introduces neither conditioning nor a new probability space. -/
theorem restrict_sourceView_eq_self_right_one (hℓ : 1 ≤ ℓ)
    [MeasurableSpace {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled}]
    (μ : Measure {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled}) :
    μ.restrict {q | q.val.IsSourceBoundaryChanneled} = μ := by
  have hset : {q : {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} |
      q.val.IsSourceBoundaryChanneled} = Set.univ := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact (isSourceBoundaryChanneled_iff_right_one hℓ q.val).2 q.property
  rw [hset, Measure.restrict_univ]


/-- The single-edge map is explicitly included in the paper view. -/
theorem isSourceBoundaryChanneled_singleEdge :
    (mk KMSWMapRep.singleEdge).IsSourceBoundaryChanneled :=
  ⟨(isChanneled_mk _).2 kmswZeroStep_singleEdge_isChanneled,
    Or.inr ⟨rfl, rfl, rfl, HEq.rfl⟩⟩

/-- Forgetting only the proof fields identifies the right-boundary-one paper and
original sample spaces. The underlying map class is unchanged. -/
@[expose] noncomputable def sourceBoundaryChanneledEquivRightOne (hℓ : 1 ≤ ℓ) :
    {q : KMSWMapIsoClass ℓ 1 N // q.IsSourceBoundaryChanneled} ≃
      {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} :=
  Equiv.subtypeEquivRight (isSourceBoundaryChanneled_iff_right_one hℓ)

/-- The identification preserves the underlying map class exactly. -/
theorem sourceBoundaryChanneledEquivRightOne_val (hℓ : 1 ≤ ℓ)
    (q : {q : KMSWMapIsoClass ℓ 1 N // q.IsSourceBoundaryChanneled}) :
    (sourceBoundaryChanneledEquivRightOne hℓ q).val = q.val := rfl

/-- Filtering any weighted finite ensemble leaves its weight sum unchanged. -/
theorem sum_filter_sourceView_right_one (hℓ : 1 ≤ ℓ)
    {A : Type*} [AddCommMonoid A] (s : Finset (KMSWMapIsoClass ℓ 1 N))
    (w : KMSWMapIsoClass ℓ 1 N → A) :
    ∑ q ∈ s.filter (fun q => q.IsSourceBoundaryChanneled), w q =
      ∑ q ∈ s.filter (fun q => q.IsChanneled), w q := by
  rw [filter_isSourceBoundaryChanneled_right_one hℓ]

/-- Uniform finite laws are preserved by the identity on underlying map classes,
including empty finite ensembles. -/
theorem uniform_sourceBoundaryChanneledEquivRightOne (hℓ : 1 ≤ ℓ)
    [Fintype {q : KMSWMapIsoClass ℓ 1 N // q.IsSourceBoundaryChanneled}]
    [Fintype {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled}] :
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 N // q.IsSourceBoundaryChanneled} := ⊤
    letI : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} := ⊤
    (uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 N // q.IsSourceBoundaryChanneled}).map
        (sourceBoundaryChanneledEquivRightOne hℓ) =
      uniformCountingMeasure {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} := by
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 N // q.IsSourceBoundaryChanneled} := ⊤
  let : MeasurableSpace {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} := ⊤
  exact uniformCountingMeasure_map_of_bijective _
    (sourceBoundaryChanneledEquivRightOne hℓ).bijective

/-- The independent mark and every geometric observable are retained when the
original right-boundary-one sampling law is filtered by the paper view. -/
theorem map_restrict_sourceView_prod_eq (hℓ : 1 ≤ ℓ)
    {Γ Y : Type*} [MeasurableSpace Γ] [MeasurableSpace Y]
    [MeasurableSpace {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled}]
    (μ : Measure {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled})
    (ν : Measure Γ)
    (f : ({q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} × Γ) → Y) :
    ((μ.prod ν).restrict {p | p.1.val.IsSourceBoundaryChanneled}).map f =
      (μ.prod ν).map f := by
  have hset : {p : {q : KMSWMapIsoClass ℓ 1 N // q.IsChanneled} × Γ |
      p.1.val.IsSourceBoundaryChanneled} = Set.univ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact (isSourceBoundaryChanneled_iff_right_one hℓ p.1.val).2 p.1.property
  rw [hset, Measure.restrict_univ]

/-- The existing positive-step KMSW bijection, procedure identification, uniqueness,
and non-boundary-edge count on the current-paper target view. -/
theorem kmsw_left_source_view (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n) :
    ∃ F : KMSWLeftWalkClass ℓ n ≃
        {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsSourceBoundaryChanneled},
      (∀ c, Nonempty (DirectedMapWithMissingIso (F c).val.out.partialMap
        (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n))) ∧
      (∀ c (q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsSourceBoundaryChanneled}),
        Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
          (kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n)) → q = F c) ∧
      (∀ q : {q : KMSWMapIsoClass ℓ 1 (n + ℓ) // q.IsSourceBoundaryChanneled},
        KMSWMapIsoClass.nonBoundaryEdgeCount q.val = n - 1) := by
  obtain ⟨F, hF, huniq, hcount⟩ := lem_kmsw_left_procedureReading_uniform ℓ n hℓ hn
  let E := sourceBoundaryChanneledEquivRightOne (N := n + ℓ) hℓ
  refine ⟨F.trans E.symm, ?_, ?_, ?_⟩
  · exact hF
  · intro c q hq
    apply E.injective
    change E q = E (E.symm (F c))
    rw [E.apply_symm_apply]
    exact huniq c (E q) hq
  · intro q
    exact hcount (E q)

/-- The separate singleton / zero-step clause on the current-paper view. -/
theorem kmsw_left_zeroStep_source_view :
    ∃ F : KMSWLeftWalkClass 1 0 ≃
        {q : KMSWMapIsoClass 1 1 1 // q.IsSourceBoundaryChanneled},
      (∀ c, Nonempty (DirectedMapWithMissingIso (F c).val.out.partialMap
        (kmswStageDirectedMap (finiteCodeExtend (n := 1) c.val) 0))) ∧
      (∀ c (q : {q : KMSWMapIsoClass 1 1 1 // q.IsSourceBoundaryChanneled}),
        Nonempty (DirectedMapWithMissingIso q.val.out.partialMap
          (kmswStageDirectedMap (finiteCodeExtend (n := 1) c.val) 0)) → q = F c) ∧
      (∀ q : {q : KMSWMapIsoClass 1 1 1 // q.IsSourceBoundaryChanneled},
        KMSWMapIsoClass.nonBoundaryEdgeCount q.val = 0) := by
  obtain ⟨F, hF, huniq, hcount⟩ := kmsw_left_zeroStep_procedureReading
  let E := sourceBoundaryChanneledEquivRightOne (ℓ := 1) (N := 1) (by omega)
  refine ⟨F.trans E.symm, ?_, ?_, ?_⟩
  · exact hF
  · intro c q hq
    apply E.injective
    change E q = E (E.symm (F c))
    rw [E.apply_symm_apply]
    exact huniq c (E q) hq
  · intro q
    exact hcount (E q)

/-- The current-paper reversal class is exactly the old simple-boundary reversal
class in the permitted parameter range, on both sides of the bijection. -/
@[expose] noncomputable def sourceBoundaryRightPrefixReversalEquiv
    (k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (hkr : k < r) :
    {q : KMSWMapIsoClass ℓ r N // q.IsSourceBoundaryChanneled} ≃
      {q : KMSWMapIsoClass (ℓ + k) (r - k) N // q.IsSourceBoundaryChanneled} :=
  (Equiv.subtypeEquivRight
      (isSourceBoundaryChanneled_iff_of_two_le_right (by omega))).trans
    ((kmswRightPrefixReversalClassEquiv k hℓ hk hkr).trans
      (Equiv.subtypeEquivRight
        (isSourceBoundaryChanneled_iff_of_two_le_left (by omega))).symm)

end KMSWMapIsoClass

namespace KMSWMapRep

variable {ℓ r N : ℕ}

/-- The current-paper class view on the same raw representatives. -/
@[expose] def IsSourceBoundaryChanneled (R : KMSWMapRep ℓ r N) : Prop :=
  (KMSWMapIsoClass.mk R).IsSourceBoundaryChanneled

/-- The raw and isomorphism-class views agree by construction. -/
theorem isSourceBoundaryChanneled_iff (R : KMSWMapRep ℓ r N) :
    R.IsSourceBoundaryChanneled ↔
      R.IsChanneled ∧ (R.IsSimpleOuterBoundary ∨
        (KMSWMapIsoClass.mk R).IsSingleEdgeClass) := by
  simp only [IsSourceBoundaryChanneled, KMSWMapIsoClass.IsSourceBoundaryChanneled,
    KMSWMapIsoClass.isChanneled_mk, KMSWMapIsoClass.isSimpleOuterBoundary_mk]

/-- Every right-boundary-one representative has the same current-paper membership
as its original primary channeling condition. -/
theorem isSourceBoundaryChanneled_iff_right_one (hℓ : 1 ≤ ℓ)
    (R : KMSWMapRep ℓ 1 N) : R.IsSourceBoundaryChanneled ↔ R.IsChanneled := by
  exact (KMSWMapIsoClass.isSourceBoundaryChanneled_iff_right_one hℓ
    (KMSWMapIsoClass.mk R)).trans (KMSWMapIsoClass.isChanneled_mk R)

end KMSWMapRep
end DirectedDistances.PlanarMap


namespace DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly5

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open MeasureTheory

/-- Proposition 5.16's actual finite geometric law is unchanged when its finite
ensemble is filtered by the current-paper class view. The map sample, independent
missing-edge mark, and geometric observable are exactly the existing ones. -/
theorem finiteGeometricLaw_sourceView_filter_eq
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    let E := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
    let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
    letI : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) E
    letI : MeasurableSpace Q := ⊤
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    (((uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))).restrict
        {p | p.1.val.IsSourceBoundaryChanneled}).map (finiteGeometricClass ell n hell) =
      (finiteGeometricLaw n ell hell hle hmod).toMeasure := by
  let E := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n) E
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  exact (KMSWMapIsoClass.map_restrict_sourceView_prod_eq (by omega : 1 ≤ ell + 1)
    (uniformCountingMeasure Q) (uniformCountingMeasure (Fin ell))
    (finiteGeometricClass ell n hell)).trans
      (finiteGeometricLaw_toMeasure n ell hell hle hmod).symm

end DirectedDistances.PaperProofs.Section5.Prop516ExteriorAssembly5
