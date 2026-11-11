module

public import DirectedDistances.PaperProofs.Section4.ThinSideCodeFidelity
import Mathlib.Topology.Compactness.Compact

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

Assembly along the permanent-ID ancestor inclusions. This module distinguishes
constructing an isomorphism from a coherent tower from producing such a tower
from unrelated nonempty finite isomorphism spaces. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter
open scoped Classical

local notation "Ω" => (ℕ → ℤ × ℤ)

variable (x : XDP) (T : ℕ → Ω → ℕ∞)
  (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The finite geometric isomorphism space is finite, including all markings. -/
theorem geometricAncestorMarkedIso_finite
    (a : ThinMapSide) (s : ℕ) (q q' : selectedCutCoherentDomain x T hT) :
    Finite (GeometricAncestorMarkedIso x T hT a s q q') := by
  let := sourceAncestorCell_finite
    (boltzmannKMSWStream (pathCode q.1))
    (sourceAncestor_finite_incidence x T hT q) (sourceAncestor_left_nonneg x T hT q)
    (sourceAncestor_left_transient x T hT q) (sourceAncestor_right_unbounded x T hT q)
    (sourceAncestorPath x T hT q) a s
  let := sourceAncestorCell_finite
    (boltzmannKMSWStream (pathCode q'.1))
    (sourceAncestor_finite_incidence x T hT q') (sourceAncestor_left_nonneg x T hT q')
    (sourceAncestor_left_transient x T hT q') (sourceAncestor_right_unbounded x T hT q')
    (sourceAncestorPath x T hT q') a s
  apply Finite.of_injective
    (fun I : GeometricAncestorMarkedIso x T hT a s q q' => I.equiv)
  intro I J h
  cases I
  cases J
  cases h
  rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A tower of marked finite isomorphisms commuting with every permanent-ID inclusion. -/
structure GeometricAncestorIsoTower
    (a : ThinMapSide) (q q' : selectedCutCoherentDomain x T hT) where
  level : ∀ s, GeometricAncestorMarkedIso x T hT a s q q'
  commutes : ∀ {s t} (hst : s ≤ t) (u : GeometricAncestorCell x T hT a s q),
    (level t).equiv (geometricAncestorInclusion x T hT a q hst u) =
      geometricAncestorInclusion x T hT a q' hst ((level s).equiv u)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The precise remaining finite compatibility obligation; no assertion of it is made. -/
@[expose] def GeometricAncestorTowerExistence : Prop :=
  ∀ (a : ThinMapSide) (q q' : selectedCutCoherentDomain x T hT),
    (∀ s, Nonempty (GeometricAncestorMarkedIso x T hT a s q q')) →
      Nonempty (GeometricAncestorIsoTower x T hT a q q')

private theorem intoSide_inclusion
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (u : GeometricAncestorCell x T hT a s q) :
    geometricAncestorIntoSide x T hT a q t
        (geometricAncestorInclusion x T hT a q hst u) =
      geometricAncestorIntoSide x T hT a q s u := by
  cases u <;> rfl

private theorem tower_overlap
    {a : ThinMapSide} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorIsoTower x T hT a q q')
    {s t : ℕ} (u : GeometricAncestorCell x T hT a s q)
    (v : GeometricAncestorCell x T hT a t q)
    (h : geometricAncestorIntoSide x T hT a q s u =
      geometricAncestorIntoSide x T hT a q t v) :
    geometricAncestorIntoSide x T hT a q' s ((I.level s).equiv u) =
      geometricAncestorIntoSide x T hT a q' t ((I.level t).equiv v) := by
  have huv : geometricAncestorInclusion x T hT a q (le_max_left s t) u =
      geometricAncestorInclusion x T hT a q (le_max_right s t) v := by
    apply geometricAncestorIntoSide_injective x T hT a q (max s t)
    simpa only [intoSide_inclusion] using h
  have hh := congrArg (I.level (max s t)).equiv huv
  rw [I.commutes, I.commutes] at hh
  have hh' := congrArg (geometricAncestorIntoSide x T hT a q' (max s t)) hh
  simpa only [intoSide_inclusion] using hh'

private noncomputable def towerUnionMap
    {a : ThinMapSide} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorIsoTower x T hT a q q')
    (z : GeometricSideCell (geometricSideSubmap x T hT a q)) :
    GeometricSideCell (geometricSideSubmap x T hT a q') :=
  let h := geometricAncestorIntoSide_exhausts x T hT a q z
  geometricAncestorIntoSide x T hT a q' h.choose
    ((I.level h.choose).equiv h.choose_spec.choose)

private theorem towerUnionMap_intoSide
    {a : ThinMapSide} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorIsoTower x T hT a q q')
    (s : ℕ) (u : GeometricAncestorCell x T hT a s q) :
    towerUnionMap x T hT I (geometricAncestorIntoSide x T hT a q s u) =
      geometricAncestorIntoSide x T hT a q' s ((I.level s).equiv u) := by
  unfold towerUnionMap
  apply tower_overlap
  exact (geometricAncestorIntoSide_exhausts x T hT a q
    (geometricAncestorIntoSide x T hT a q s u)).choose_spec.choose_spec

private theorem towerUnionMap_bijective
    {a : ThinMapSide} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorIsoTower x T hT a q q') :
    Function.Bijective (towerUnionMap x T hT I) := by
  constructor
  · intro z z' hz
    obtain ⟨s, u, rfl⟩ := geometricAncestorIntoSide_exhausts x T hT a q z
    obtain ⟨t, v, rfl⟩ := geometricAncestorIntoSide_exhausts x T hT a q z'
    rw [towerUnionMap_intoSide, towerUnionMap_intoSide] at hz
    have heq : geometricAncestorInclusion x T hT a q' (le_max_left s t)
          ((I.level s).equiv u) =
        geometricAncestorInclusion x T hT a q' (le_max_right s t)
          ((I.level t).equiv v) := by
      apply geometricAncestorIntoSide_injective x T hT a q' (max s t)
      simpa only [intoSide_inclusion] using hz
    rw [← I.commutes, ← I.commutes] at heq
    have huv := (I.level (max s t)).equiv.injective heq
    have hh := congrArg (geometricAncestorIntoSide x T hT a q (max s t)) huv
    simpa only [intoSide_inclusion] using hh
  · intro z
    obtain ⟨s, u, rfl⟩ := geometricAncestorIntoSide_exhausts x T hT a q' z
    refine ⟨geometricAncestorIntoSide x T hT a q s ((I.level s).equiv.symm u), ?_⟩
    rw [towerUnionMap_intoSide, Equiv.apply_symm_apply]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The bijection of whole-side cells induced by a coherent tower. -/
noncomputable def GeometricAncestorIsoTower.unionEquiv
    {a : ThinMapSide} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorIsoTower x T hT a q q') :
    GeometricSideCell (geometricSideSubmap x T hT a q) ≃
      GeometricSideCell (geometricSideSubmap x T hT a q') :=
  Equiv.ofBijective (towerUnionMap x T hT I) (towerUnionMap_bijective x T hT I)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The union bijection restricts to each prescribed finite isomorphism. -/
theorem GeometricAncestorIsoTower.unionEquiv_intoSide
    {a : ThinMapSide} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorIsoTower x T hT a q q')
    (s : ℕ) (u : GeometricAncestorCell x T hT a s q) :
    I.unionEquiv x T hT (geometricAncestorIntoSide x T hT a q s u) =
      geometricAncestorIntoSide x T hT a q' s ((I.level s).equiv u) :=
  towerUnionMap_intoSide x T hT I s u

private theorem constant_stable (P : Prop) (s : ℕ) :
    P ↔ ∃ t, ∃ _hst : s ≤ t, ∀ n, t ≤ n → P := by
  constructor
  · intro h
    exact ⟨s, le_rfl, fun _ _ => h⟩
  · rintro ⟨t, _, h⟩
    exact h t le_rfl

private theorem rotation_union_stable
    (f : (ℕ × Bool) → ℕ × Bool) (U : ℕ → Set ℕ) (hU : Monotone U)
    (s : ℕ) (d e : ℕ × Bool) (he : e.1 ∈ U s) :
    (∃ k : ℕ, 0 < k ∧ f^[k] d = e ∧
      ∀ j : ℕ, 0 < j → j < k → (f^[j] d).1 ∉ ⋃ n, U n) ↔
    ∃ t, ∃ _hst : s ≤ t, ∀ n, t ≤ n →
      ∃ k : ℕ, 0 < k ∧ f^[k] d = e ∧
        ∀ j : ℕ, 0 < j → j < k → (f^[j] d).1 ∉ U n := by
  constructor
  · rintro ⟨k, hk, hend, hgap⟩
    exact ⟨s, le_rfl, fun n _ => ⟨k, hk, hend,
      fun j hj hjk hmem => hgap j hj hjk (Set.mem_iUnion.mpr ⟨n, hmem⟩)⟩⟩
  · rintro ⟨t, hst, ht⟩
    obtain ⟨k, hk, hend, hgap⟩ := ht t le_rfl
    refine ⟨k, hk, hend, ?_⟩
    intro j hj hjk hmem
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨l, hl, hlend, hlgap⟩ := ht (max t r) (le_max_left t r)
    have hlk : l = k := by
      apply le_antisymm
      · by_contra h
        apply hlgap k hk (by omega)
        rw [hend]
        exact hU (hst.trans (le_max_left t r)) he
      · by_contra h
        apply hgap l hl (by omega)
        rw [hlend]
        exact hU hst he
    subst l
    exact hlgap j hj hjk (hU (le_max_right t r) hr)

private theorem face_union_stable
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    (s : ℕ) (d e : ℕ × Bool) :
    (geometricSideSubmap x T hT a q).faceNext d e ↔
      ∃ t, ∃ _hst : s ≤ t, ∀ n, t ≤ n →
        sourceAncestorRetainedFace (boltzmannKMSWStream (pathCode q.1))
          (sourceAncestor_finite_incidence x T hT q)
          (sourceAncestor_left_nonneg x T hT q)
          (sourceAncestor_left_transient x T hT q)
          (sourceAncestor_right_unbounded x T hT q)
          (sourceAncestorPath x T hT q) a n d ∧
        kmswInfFaceSucc (boltzmannKMSWStream (pathCode q.1))
          (sourceAncestor_finite_incidence x T hT q) d = e := by
  rw [geometricSideSubmap_faceNext_iff]
  constructor
  · rintro ⟨k, ⟨j, hd, hall⟩, he⟩
    refine ⟨max s k, le_max_left s k, ?_⟩
    intro n hn
    refine ⟨⟨j, hd, ?_⟩, he⟩
    intro z hz
    exact geometricAncestorEdges_mono x T hT a q
      ((le_max_right s k).trans hn) (hall z hz)
  · rintro ⟨t, _, ht⟩
    exact ⟨t, ht t le_rfl⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every permanent whole-side relation is the eventual finite-level relation.
The finite-only target marking is excluded. Rotation requires eventual stability,
whereas retained faces are exhausted by finite levels. -/
theorem geometricSideRelation_iff_stable
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    (s : ℕ) (tag : TruncationRelation) (htag : tag ≠ .target)
    (u v : GeometricAncestorCell x T hT a s q) :
    geometricSideRelation (geometricSideSubmap x T hT a q) tag
        (geometricAncestorIntoSide x T hT a q s u)
        (geometricAncestorIntoSide x T hT a q s v) ↔
      ∃ t, ∃ hst : s ≤ t, ∀ n, (htn : t ≤ n) →
        geometricAncestorRelation x T hT a n q tag
          (geometricAncestorInclusion x T hT a q (le_trans hst htn) u)
          (geometricAncestorInclusion x T hT a q (le_trans hst htn) v) := by
  cases tag <;> cases u <;> cases v
  all_goals try exact (htag rfl).elim
  all_goals try exact constant_stable _ s
  case rotation.inr.inr u v =>
    exact rotation_union_stable _ (geometricAncestorEdges x T hT a q)
      (geometricAncestorEdges_mono x T hT a q) s u.1 v.1 v.2
  case faceNext.inr.inr u v =>
    exact face_union_stable x T hT a q s u.1 v.1

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Two whole-side cells occur together in one finite ancestor restriction. -/
theorem geometricAncestorIntoSide_exhausts_pair
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    (z z' : GeometricSideCell (geometricSideSubmap x T hT a q)) :
    ∃ s u v, geometricAncestorIntoSide x T hT a q s u = z ∧
      geometricAncestorIntoSide x T hT a q s v = z' := by
  obtain ⟨s, u, rfl⟩ := geometricAncestorIntoSide_exhausts x T hT a q z
  obtain ⟨t, v, rfl⟩ := geometricAncestorIntoSide_exhausts x T hT a q z'
  exact ⟨max s t, geometricAncestorInclusion x T hT a q (le_max_left s t) u,
    geometricAncestorInclusion x T hT a q (le_max_right s t) v,
    intoSide_inclusion x T hT a q _ _, intoSide_inclusion x T hT a q _ _⟩

private theorem side_target_false (M : GeometricSideSubmap) (u v : GeometricSideCell M) :
    geometricSideRelation M .target u v ↔ False := by
  cases u <;> cases v <;> rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The union bijection preserves all geometric whole-side relations and markings. -/
theorem GeometricAncestorIsoTower.unionEquiv_relation_iff
    {a : ThinMapSide} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorIsoTower x T hT a q q')
    (tag : TruncationRelation)
    (z z' : GeometricSideCell (geometricSideSubmap x T hT a q)) :
    geometricSideRelation (geometricSideSubmap x T hT a q) tag z z' ↔
      geometricSideRelation (geometricSideSubmap x T hT a q') tag
        (I.unionEquiv x T hT z) (I.unionEquiv x T hT z') := by
  by_cases htag : tag = .target
  · subst tag
    simp only [side_target_false]
  obtain ⟨s, u, v, rfl, rfl⟩ := geometricAncestorIntoSide_exhausts_pair x T hT a q z z'
  rw [I.unionEquiv_intoSide, I.unionEquiv_intoSide,
    geometricSideRelation_iff_stable x T hT a q s tag htag,
    geometricSideRelation_iff_stable x T hT a q' s tag htag]
  constructor
  · rintro ⟨t, hst, ht⟩
    refine ⟨t, hst, ?_⟩
    intro n htn
    rw [← I.commutes, ← I.commutes]
    exact ((I.level n).relation_iff tag _ _).mp (ht n htn)
  · rintro ⟨t, hst, ht⟩
    refine ⟨t, hst, ?_⟩
    intro n htn
    apply ((I.level n).relation_iff tag _ _).mpr
    rw [I.commutes, I.commutes]
    exact ht n htn

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A coherent tower assembles to a compatible marked isomorphism of the whole sides.
This construction assumes no geometric realization or decoder identification. -/
noncomputable def GeometricAncestorIsoTower.toCompatibleIso
    {a : ThinMapSide} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorIsoTower x T hT a q q') :
    GeometricSideCompatibleIso x T hT a q q' where
  whole := ⟨I.unionEquiv x T hT, I.unionEquiv_relation_iff x T hT⟩
  level := I.level
  commutes := I.unionEquiv_intoSide x T hT

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Whole-side assembly is equivalent to the smaller finite compatibility obligation.
The union and all its marked relations are constructed above; tower existence -/
theorem geometricAncestorIsoAssembly_iff_towerExistence :
    GeometricAncestorIsoAssembly x T hT ↔ GeometricAncestorTowerExistence x T hT := by
  constructor
  · intro h a q q' hlevels
    obtain ⟨I⟩ := h a q q' hlevels
    exact ⟨⟨I.level, fun {_ _} hst u =>
      geometricSideCompatibleIso_levels_commute x T hT a q q' I hst u⟩⟩
  · intro h a q q' hlevels
    obtain ⟨I⟩ := h a q q' hlevels
    exact ⟨I.toCompatibleIso x T hT⟩

private theorem finite_inverse_system_nonempty
    (A : ℕ → Type*) [∀ n, Finite (A n)] [∀ n, Nonempty (A n)]
    (π : ∀ {s t}, s ≤ t → A t → A s)
    (htrans : ∀ {s t r} (hst : s ≤ t) (htr : t ≤ r) (a : A r),
      π hst (π htr a) = π (hst.trans htr) a) :
    ∃ f : ∀ n, A n, ∀ {s t} (hst : s ≤ t), π hst (f t) = f s := by
  classical
  let : ∀ n, TopologicalSpace (A n) := fun _ => ⊥
  let : ∀ n, DiscreteTopology (A n) := fun _ => ⟨rfl⟩
  let C (n : ℕ) : Set (∀ i, A i) :=
    {f | ∀ i j, ∀ hij : i ≤ j, j ≤ n → π hij (f j) = f i}
  have hclosed (n : ℕ) : IsClosed (C n) := by
    simp only [C, Set.ofPred_forall]
    apply isClosed_iInter fun i => ?_
    apply isClosed_iInter fun j => ?_
    apply isClosed_iInter fun hij => ?_
    apply isClosed_iInter fun _ => ?_
    exact isClosed_eq ((continuous_of_discreteTopology (f := π hij)).comp
      (continuous_apply j)) (continuous_apply i)
  have hnonempty (n : ℕ) : (C n).Nonempty := by
    let b : A n := Classical.choice (inferInstance : Nonempty (A n))
    refine ⟨fun i => if h : i ≤ n then π h b else Classical.choice inferInstance, ?_⟩
    intro i j hij hjn
    dsimp only
    rw [dite_eq_left hjn, dite_eq_left (hij.trans hjn), htrans]
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    (fun n f h i j hij hjn => h i j hij (hjn.trans (Nat.le_succ n)))
    hnonempty ((hclosed 0).isCompact) hclosed
  refine ⟨f, ?_⟩
  intro s t hst
  exact (Set.mem_iInter.mp hf t) s t hst le_rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The permanent-ID inclusions are injective. -/
theorem geometricAncestorInclusion_injective
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) :
    Function.Injective (geometricAncestorInclusion x T hT a q hst) := by
  intro u v h
  apply geometricAncestorIntoSide_injective x T hT a q s
  have hh := congrArg (geometricAncestorIntoSide x T hT a q t) h
  simpa only [intoSide_inclusion] using hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A lower-level marked isomorphism satisfying the restriction equation is unique.
This is uniqueness of a restriction, without claiming rigidity of a marked map. -/
theorem geometricAncestorMarkedIso_restriction_unique
    (a : ThinMapSide) (q q' : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (I : GeometricAncestorMarkedIso x T hT a t q q')
    (J K : GeometricAncestorMarkedIso x T hT a s q q')
    (hJ : ∀ u, I.equiv (geometricAncestorInclusion x T hT a q hst u) =
      geometricAncestorInclusion x T hT a q' hst (J.equiv u))
    (hK : ∀ u, I.equiv (geometricAncestorInclusion x T hT a q hst u) =
      geometricAncestorInclusion x T hT a q' hst (K.equiv u)) : J = K := by
  have he : J.equiv = K.equiv := by
    apply Equiv.ext
    intro u
    apply geometricAncestorInclusion_injective x T hT a q' hst
    exact (hJ u).symm.trans (hK u)
  cases J
  cases K
  cases he
  rfl

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
an earlier ancestor carrier and its full induced marked relations. Finite
compactness alone does not supply this fact. -/
@[expose] def GeometricAncestorRestrictionProperty : Prop :=
  ∀ (a : ThinMapSide) (q q' : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (I : GeometricAncestorMarkedIso x T hT a t q q'),
    ∃ J : GeometricAncestorMarkedIso x T hT a s q q',
      ∀ u, I.equiv (geometricAncestorInclusion x T hT a q hst u) =
        geometricAncestorInclusion x T hT a q' hst (J.equiv u)

private theorem inclusion_trans
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t r : ℕ} (hst : s ≤ t) (htr : t ≤ r)
    (u : GeometricAncestorCell x T hT a s q) :
    geometricAncestorInclusion x T hT a q htr
        (geometricAncestorInclusion x T hT a q hst u) =
      geometricAncestorInclusion x T hT a q (hst.trans htr) u := by
  cases u <;> rfl

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Finite compactness reduces tower existence to the local restriction property. -/
theorem geometricAncestorRestrictionProperty_implies_towerExistence :
    GeometricAncestorRestrictionProperty x T hT → GeometricAncestorTowerExistence x T hT := by
  intro hrestrict a q q' hlevels
  classical
  let A (n : ℕ) := GeometricAncestorMarkedIso x T hT a n q q'
  let : ∀ n, Finite (A n) := fun n => geometricAncestorMarkedIso_finite x T hT a n q q'
  let : ∀ n, Nonempty (A n) := hlevels
  let π {s t : ℕ} (hst : s ≤ t) (I : A t) : A s :=
    (hrestrict a q q' hst I).choose
  have hπ {s t : ℕ} (hst : s ≤ t) (I : A t) (u) :
      I.equiv (geometricAncestorInclusion x T hT a q hst u) =
        geometricAncestorInclusion x T hT a q' hst ((π hst I).equiv u) :=
    (hrestrict a q q' hst I).choose_spec u
  have htrans {s t r : ℕ} (hst : s ≤ t) (htr : t ≤ r) (I : A r) :
      π hst (π htr I) = π (hst.trans htr) I := by
    apply geometricAncestorMarkedIso_restriction_unique x T hT a q q'
      (hst.trans htr) I
    · intro u
      rw [← inclusion_trans x T hT a q hst htr, hπ htr I,
        hπ hst (π htr I), inclusion_trans]
    · exact hπ (hst.trans htr) I
  obtain ⟨f, hf⟩ := finite_inverse_system_nonempty A π htrans
  refine ⟨⟨f, ?_⟩⟩
  intro s t hst u
  have hh := hπ hst (f t) u
  rw [hf hst] at hh
  exact hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every ancestor vertex reaches the target using present edges retained at that
same finite level. This proves directed connectedness toward the marked target. -/
theorem geometricAncestorVertices_reach_target
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    (s v : ℕ) (hv : v ∈ geometricAncestorVertices x T hT a q s) :
    Relation.ReflTransGen
      (fun u z => ∃ e ∈ geometricAncestorEdges x T hT a q s,
        EdgePresent (boltzmannKMSWStream (pathCode q.1)) e ∧
        edgeWest (boltzmannKMSWStream (pathCode q.1)) e = u ∧
        edgeEast (boltzmannKMSWStream (pathCode q.1)) e = z)
      v (thinMapBoundaryVertex (boltzmannKMSWStream (pathCode q.1))
        (sourceAncestor_finite_incidence x T hT q) (sourceAncestor_left_nonneg x T hT q)
        (sourceAncestor_left_transient x T hT q) (sourceAncestor_right_unbounded x T hT q)
        a s) := by
  let w := boltzmannKMSWStream (pathCode q.1)
  let hf := sourceAncestor_finite_incidence x T hT q
  let hl := sourceAncestor_left_nonneg x T hT q
  let ht := sourceAncestor_left_transient x T hT q
  let hr := sourceAncestor_right_unbounded x T hT q
  let P := sourceAncestorPath x T hT q
  have hpath := hv.2
  clear hv
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head u z hstep hpath ih =>
    obtain ⟨e, hes, hp, hw, he⟩ := hstep
    have hu : edgeWest w e ∈ sourceAncestorVertices w hf hl ht hr P a s := by
      refine ⟨(sideEdges_endpoints w hf hl ht hr P a hes).1, ?_⟩
      exact hw.symm ▸ hpath.head ⟨e, hes, hp, hw, he⟩
    have hz : edgeEast w e ∈ sourceAncestorVertices w hf hl ht hr P a s := by
      refine ⟨(sideEdges_endpoints w hf hl ht hr P a hes).2, ?_⟩
      exact he.symm ▸ hpath
    exact ih.head ⟨e, ⟨hes, hu, hz⟩, hp, hw, he⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Earlier ancestor membership is directed reachability to the earlier boundary
target within any later finite ancestor graph. This supplies the carrier-level
characterization needed for a restriction proof; it does not prove preservation
of induced rotation or retained faces under restriction. -/
theorem geometricAncestorVertices_iff_later_reachable
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (v : ℕ) :
    v ∈ geometricAncestorVertices x T hT a q s ↔
      v ∈ geometricAncestorVertices x T hT a q t ∧
        Relation.ReflTransGen
          (fun u z => ∃ e ∈ geometricAncestorEdges x T hT a q t,
            EdgePresent (boltzmannKMSWStream (pathCode q.1)) e ∧
            edgeWest (boltzmannKMSWStream (pathCode q.1)) e = u ∧
            edgeEast (boltzmannKMSWStream (pathCode q.1)) e = z)
          v (thinMapBoundaryVertex (boltzmannKMSWStream (pathCode q.1))
            (sourceAncestor_finite_incidence x T hT q)
            (sourceAncestor_left_nonneg x T hT q)
            (sourceAncestor_left_transient x T hT q)
            (sourceAncestor_right_unbounded x T hT q) a s) := by
  constructor
  · intro hv
    refine ⟨geometricAncestorVertices_mono x T hT a q hst hv, ?_⟩
    refine Relation.ReflTransGen.mono ?_ _ _
      (geometricAncestorVertices_reach_target x T hT a q s v hv)
    intro u z hstep
    obtain ⟨e, he, hp, hw, hz⟩ := hstep
    exact ⟨e, geometricAncestorEdges_mono x T hT a q hst he, hp, hw, hz⟩
  · rintro ⟨hv, hpath⟩
    refine ⟨hv.1, ?_⟩
    refine Relation.ReflTransGen.mono ?_ _ _ hpath
    intro u z hstep
    obtain ⟨e, he, hp, hw, hz⟩ := hstep
    exact ⟨e, he.1, hp, hw, hz⟩



@[expose] def GeometricAncestorSuccessorRestriction : Prop :=
  ∀ (a : ThinMapSide) (q q' : selectedCutCoherentDomain x T hT) (s : ℕ)
    (I : GeometricAncestorMarkedIso x T hT a (s + 1) q q'),
    ∃ J : GeometricAncestorMarkedIso x T hT a s q q',
      ∀ u, I.equiv (geometricAncestorInclusion x T hT a q (Nat.le_succ s) u) =
        geometricAncestorInclusion x T hT a q' (Nat.le_succ s) (J.equiv u)

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Adjacent restriction implies restriction across any finite number of levels. -/
theorem geometricAncestorRestrictionProperty_iff_successor :
    GeometricAncestorRestrictionProperty x T hT ↔
      GeometricAncestorSuccessorRestriction x T hT := by
  constructor
  · intro h a q q' s I
    exact h a q q' (Nat.le_succ s) I
  · intro h a q q' s t hst
    induction t, hst using Nat.le_induction with
    | base =>
      intro I
      refine ⟨I, ?_⟩
      intro u
      have hrefl (r : selectedCutCoherentDomain x T hT)
          (v : GeometricAncestorCell x T hT a s r) :
          geometricAncestorInclusion x T hT a r (le_refl s) v = v := by
        cases v <;> rfl
      rw [hrefl, hrefl]
    | succ t hst ih =>
      intro I
      obtain ⟨J, hJ⟩ := h a q q' t I
      obtain ⟨K, hK⟩ := ih J
      refine ⟨K, ?_⟩
      intro u
      rw [← inclusion_trans x T hT a q hst (Nat.le_succ t), hJ, hK,
        inclusion_trans]

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Exact reduction: adjacent finite restriction suffices for compatible whole-side
assembly, by unique restrictions, finite compactness and the union construction. -/
theorem geometricAncestorSuccessorRestriction_implies_assembly :
    GeometricAncestorSuccessorRestriction x T hT → GeometricAncestorIsoAssembly x T hT := by
  intro h
  apply (geometricAncestorIsoAssembly_iff_towerExistence x T hT).mpr
  apply geometricAncestorRestrictionProperty_implies_towerExistence x T hT
  exact (geometricAncestorRestrictionProperty_iff_successor x T hT).mpr h

end DirectedDistances.PaperProofs.Section4
