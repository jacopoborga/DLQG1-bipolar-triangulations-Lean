/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceEnclosedSlice4

/-! Conditional reductions for the intrinsic enclosure and its reconstruction. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: Open A is conditional on the explicitly
 displayed off-ray exhaustion hypothesis. Ray cells are handled separately;
 exhaustion by slit chains is required only away from the ray. -/
theorem m0GeodesicLeftSide_intrinsic_right_iff_previousRight_of_exhaustion
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (hexhaust : ∀ c : GeometricSideCell (m0GeodesicSide hp (P k) .left),
      (match c with
       | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
       | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right) →
      (match c with
       | .inl v => v.val ∉ m0GeodesicVertices (P (k - 1))
       | .inr d => d.val.1 ∉ m0GeodesicEdges (P (k - 1))) →
      ∃ a, geometricSide_right_face_seed (m0GeodesicSide hp (P k) .left)
          (m0GeodesicSideAdjacentDarts hp P k hcontain) a ∧
        Relation.ReflTransGen
          (geometricSide_slit_step (m0GeodesicSide hp (P k) .left)
            (m0GeodesicSideAdjacentVertices hp P k hcontain)
            (m0GeodesicSideAdjacentDarts hp P k hcontain)) a c)
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right := by
  classical
  constructor
  · intro hc
    cases c <;> exact m0GeodesicLeftSide_intrinsic_right_sound hp P k hcontain _ hc
  · intro hc
    cases c with
    | inl v =>
      by_cases hv : v.val ∈ m0GeodesicVertices (P (k - 1))
      · exact Or.inl ((m0GeodesicLeftSide_ray_vertex_iff hp P k hcontain v).2 hv)
      · exact Or.inr (Or.inr (hexhaust (.inl v) hc hv))
    | inr d =>
      by_cases hd : d.val.1 ∈ m0GeodesicEdges (P (k - 1))
      · exact Or.inr (Or.inl
          ((m0GeodesicLeftSide_ray_dart_iff hp P k hcontain d).2 hd))
      · exact Or.inr (Or.inr (hexhaust (.inr d) hc hd))


/-- Helper toward Lemma 5.6: a retained left-side face is retained on
 the preceding right side exactly when its initial dart has the oriented
 right invariant. This includes the forward-ray exclusion. -/
theorem m0GeodesicLeftSide_previousRight_faceNext_iff_invariant
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges})
    (hde : (m0GeodesicSide hp (P k) .left).faceNext d.val e.val) :
    (m0GeodesicSide hp (P (k - 1)) .right).faceNext d.val e.val ↔
      m0GeodesicSlitRightInvariant hp (P (k - 1)) (P k) (.inr d) := by
  obtain ⟨⟨F, hb, hFL⟩, hsucc⟩ := hde
  constructor
  · rintro ⟨⟨G, hG, hGR⟩, _⟩
    exact m0Geodesic_right_face_dart_invariant hp (P (k - 1)) (P k) d G hG hGR
  · intro hd
    exact ⟨⟨F, hb, m0Geodesic_invariant_dart_face_right hp
      (P (k - 1)) (P k) d hd F
      (fun _ hz => (m0GeodesicLeftOpen_subset hp (P k) (hFL hz)).1) hb⟩, hsucc⟩

/-- Helper toward Lemma 5.6: the retained-face criterion is conditional
 on the explicitly displayed Open A hypothesis. A left-side face step is
 retained in the overlap exactly when its initial cell is in the candidate
 and is not a forward dart of the preceding ray. -/
theorem m0GeodesicLeftSide_previousRight_faceNext_iff_of_openA
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (hA : ∀ c : GeometricSideCell (m0GeodesicSide hp (P k) .left),
      geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges})
    (hde : (m0GeodesicSide hp (P k) .left).faceNext d.val e.val) :
    (m0GeodesicSide hp (P (k - 1)) .right).faceNext d.val e.val ↔
      geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) (.inr d) ∧
      ∀ n : ℕ, (.inr d : GeometricSideCell (m0GeodesicSide hp (P k) .left)) ≠
        m0GeodesicSideAdjacentDarts hp P k hcontain n := by
  rw [m0GeodesicLeftSide_previousRight_faceNext_iff_invariant hp P k d e hde]
  change (_ ∧ ∀ n, d.val ≠ _) ↔ _
  have hAd := hA (.inr d)
  dsimp only at hAd
  rw [← hAd]
  apply and_congr Iff.rfl
  exact forall_congr' fun n => not_congr ⟨
    fun he => congrArg Sum.inr (Subtype.ext he),
    fun he => congrArg Subtype.val (Sum.inr.inj he)⟩

section TwoRealizations

variable {W' : ℤ → Fin 3} {H' : WholePlaneRotationHypothesis W'}
  {h' : BoundaryHitWitnesses (shiftedStream W' 0)}
  {hLL' : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W'
    (wholePlaneEdgeι W' 0
      (kmswLLCreatedEdge (shiftedStream W' 0)
        (boundaryHitTime (shiftedStream W' 0) h' (k - 1))))}
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (hp' : BoundaryHitWitnesses (kmswPastCode W')) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (P' : ∀ k : ℤ, M0CutInfiniteGeodesic W' H' h' hLL' k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (T' : ∀ k : ℤ, InfinitePresentPath (shiftedStream W' 0)
    (boundaryPresentVertex (shiftedStream W' 0) h' k))
  (hleft : ∀ k : ℤ,
    Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hleft' : ∀ k : ℤ,
    Xdp.CutLeftmostXdp W' H' h' hp' hLL' longest k (P' k) (T' k))
  (k l : ℤ)
  (hcontain : ∀ n : ℕ,
    (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
    ((P (k - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp (P k) .left).vertices)
  (hcontain' : ∀ n : ℕ,
    (P' (l - 1)).codePath.edge n ∈ (m0GeodesicSide hp' (P' l) .left).edges ∧
    ((P' (l - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp' (P' l) .left).vertices)
  (I : GeometricSideMarkedIso (m0GeodesicSide hp (P k) .left)
    (m0GeodesicSide hp' (P' l) .left))

include hleft hleft' in
/-- Helper toward Lemma 5.6: preceding-right membership transport is
 conditional on the explicitly displayed Open A hypotheses for both
 realizations. The isomorphism is the supplied marked isomorphism. -/
theorem m0GeodesicLeftSide_markedIso_previousRight_iff_of_openA
    (hA : ∀ c : GeometricSideCell (m0GeodesicSide hp (P k) .left),
      geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
    (hA' : ∀ c : GeometricSideCell (m0GeodesicSide hp' (P' l) .left),
      geometricSide_intrinsic_right (m0GeodesicSide hp' (P' l) .left)
        (m0GeodesicSideAdjacentVertices hp' P' l hcontain')
        (m0GeodesicSideAdjacentDarts hp' P' l hcontain') c ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp' (P' (l - 1)) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp' (P' (l - 1)) .right)
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    (match c with
     | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
     | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right) ↔
    (match I.equiv c with
     | .inl v => v.val ∈ m0GeodesicSideVertices hp' (P' (l - 1)) .right
     | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp' (P' (l - 1)) .right) := by
  exact (hA c).symm.trans
    ((m0GeodesicLeftSide_markedIso_intrinsic_right_iff
      hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I c).trans (hA' (I.equiv c)))

end TwoRealizations

/-- Helper toward Lemma 5.6: the image of actual slice cells in the left
 side is exactly the cells whose underlying vertex or edge is retained. -/
theorem m0CutGeodesicSliceLeftCell_mem_range_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    c ∈ Set.range (m0CutGeodesicSliceLeftCell hp P k a b hab) ↔
      match c with
      | .inl v => v.val ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices
      | .inr d => d.val.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges := by
  cases c with
  | inl v =>
    constructor
    · rintro ⟨u, hu⟩
      cases u with
      | inl u =>
        change v.val ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices
        exact (congrArg Subtype.val (Sum.inl.inj hu)) ▸ u.property
      | inr u => exact False.elim (Sum.inr_ne_inl hu)
    · intro hv
      exact ⟨.inl ⟨v.val, hv⟩, rfl⟩
  | inr d =>
    constructor
    · rintro ⟨u, hu⟩
      cases u with
      | inl u => exact False.elim (Sum.inl_ne_inr hu)
      | inr u =>
        change d.val.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges
        exact (congrArg (fun x : ℕ × Bool => x.1)
          (congrArg Subtype.val (Sum.inr.inj hu))) ▸ u.property
    · intro hd
      exact ⟨.inr ⟨d.val, hd⟩, rfl⟩

/-- Helper toward Lemma 5.6: a bijection restricts along injective maps
 when it preserves their images, retaining its commuting equation. -/
theorem enclosedSlice_exists_equiv_restrict {A B C D : Type*}
    (f : A → C) (g : B → D) (hf : Function.Injective f)
    (hg : Function.Injective g) (I : C ≃ D)
    (hmem : ∀ c, c ∈ Set.range f ↔ I c ∈ Set.range g) :
    ∃ J : A ≃ B, ∀ a, g (J a) = I (f a) := by
  classical
  have hex (a : A) : ∃ b, g b = I (f a) :=
    (hmem (f a)).1 ⟨a, rfl⟩
  let j : A → B := fun a => (hex a).choose
  have hj (a : A) : g (j a) = I (f a) := (hex a).choose_spec
  have hinj : Function.Injective j := by
    intro a b hab
    apply hf
    apply I.injective
    exact (hj a).symm.trans ((congrArg g hab).trans (hj b))
  have hsurj : Function.Surjective j := by
    intro b
    obtain ⟨a, ha⟩ := (hmem (I.symm (g b))).2 (by
      simpa only [Equiv.apply_symm_apply] using (Set.mem_range_self b : g b ∈ Set.range g))
    refine ⟨a, hg ?_⟩
    rw [hj, ha, Equiv.apply_symm_apply]
  exact ⟨Equiv.ofBijective j ⟨hinj, hsurj⟩, hj⟩

section SliceTransport

variable {W' : ℤ → Fin 3} {H' : WholePlaneRotationHypothesis W'}
  {h' : BoundaryHitWitnesses (shiftedStream W' 0)}
  {hLL' : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W'
    (wholePlaneEdgeι W' 0
      (kmswLLCreatedEdge (shiftedStream W' 0)
        (boundaryHitTime (shiftedStream W' 0) h' (k - 1))))}
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (hp' : BoundaryHitWitnesses (kmswPastCode W')) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (P' : ∀ k : ℤ, M0CutInfiniteGeodesic W' H' h' hLL' k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (T' : ∀ k : ℤ, InfinitePresentPath (shiftedStream W' 0)
    (boundaryPresentVertex (shiftedStream W' 0) h' k))
  (hleft : ∀ k : ℤ,
    Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hleft' : ∀ k : ℤ,
    Xdp.CutLeftmostXdp W' H' h' hp' hLL' longest k (P' k) (T' k))
  (k l : ℤ)
  (hcontain : ∀ n : ℕ,
    (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
    ((P (k - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp (P k) .left).vertices)
  (hcontain' : ∀ n : ℕ,
    (P' (l - 1)).codePath.edge n ∈ (m0GeodesicSide hp' (P' l) .left).edges ∧
    ((P' (l - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp' (P' l) .left).vertices)
  (I : GeometricSideMarkedIso (m0GeodesicSide hp (P k) .left)
    (m0GeodesicSide hp' (P' l) .left))
  (hA : ∀ c : GeometricSideCell (m0GeodesicSide hp (P k) .left),
    geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
    match c with
    | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
    | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
  (hA' : ∀ c : GeometricSideCell (m0GeodesicSide hp' (P' l) .left),
    geometricSide_intrinsic_right (m0GeodesicSide hp' (P' l) .left)
      (m0GeodesicSideAdjacentVertices hp' P' l hcontain')
      (m0GeodesicSideAdjacentDarts hp' P' l hcontain') c ↔
    match c with
    | .inl v => v.val ∈ m0GeodesicSideVertices hp' (P' (l - 1)) .right
    | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp' (P' (l - 1)) .right)

include hleft hleft' hcontain hcontain' hA hA' in
/-- Helper toward Lemma 5.6: actual slice-cell membership transport is
 conditional on the displayed Open A hypotheses for both realizations.
 Both strict vertex-tail and weak edge-tail deletions are retained. -/
theorem m0GeodesicLeftSide_markedIso_slice_range_iff_of_openA
    (a b : ℕ) (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    let hab' := (m0GeodesicLeftSide_markedIso_leastCoalescence_iff
      hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I a b).1 hab
    c ∈ Set.range (m0CutGeodesicSliceLeftCell hp P k a b hab) ↔
      I.equiv c ∈ Set.range (m0CutGeodesicSliceLeftCell hp' P' l a b hab') := by
  dsimp only
  rw [m0CutGeodesicSliceLeftCell_mem_range_iff,
    m0CutGeodesicSliceLeftCell_mem_range_iff]
  refine (m0CutGeodesicSlice_mem_cell_iff_previousRight_and_not_deletedTail
    hp P k a b hab c).trans (Iff.trans ?_
      (m0CutGeodesicSlice_mem_cell_iff_previousRight_and_not_deletedTail
        hp' P' l a b _ (I.equiv c)).symm)
  exact and_congr (m0GeodesicLeftSide_markedIso_previousRight_iff_of_openA
    hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I hA hA' c)
    (not_congr (m0GeodesicLeftSide_markedIso_deletedTailCells_iff
      hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I a b c))

include hleft hleft' hcontain hcontain' hA hA' in
/-- Helper toward Lemma 5.6: restriction to an equivalence of actual slice
 cells is conditional on the displayed Open A hypotheses for both realizations.
 The equation fixes the restriction of the supplied isomorphism. Retained
 face, rotation and marking transport are separate obligations. -/
theorem m0GeodesicLeftSide_markedIso_slice_equiv_of_openA
    (a b : ℕ) (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    let hab' := (m0GeodesicLeftSide_markedIso_leastCoalescence_iff
      hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I a b).1 hab
    ∃ J : GeometricSideCell (m0CutGeodesicSlice (hp := hp) P k a b hab) ≃
        GeometricSideCell (m0CutGeodesicSlice (hp := hp') P' l a b hab'),
      ∀ c, m0CutGeodesicSliceLeftCell hp' P' l a b hab' (J c) =
        I.equiv (m0CutGeodesicSliceLeftCell hp P k a b hab c) := by
  dsimp only
  exact enclosedSlice_exists_equiv_restrict _ _
    (m0CutGeodesicSliceLeftCell_injective hp P k a b hab)
    (m0CutGeodesicSliceLeftCell_injective hp' P' l a b _)
    I.equiv (m0GeodesicLeftSide_markedIso_slice_range_iff_of_openA
      hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I hA hA' a b hab)

end SliceTransport

/-- Helper toward Lemma 5.6: a positive chain of rotation steps, skipping
 a specified retained set at every internal cell. -/
inductive EnclosedSliceRotationChain {α : Type*} (R : α → α → Prop)
    (S : Set α) : α → α → Prop
  | single {a b} (h : R a b) : EnclosedSliceRotationChain R S a b
  | cons {a b c} (h : R a b) (hb : b ∉ S)
      (tail : EnclosedSliceRotationChain R S b c) : EnclosedSliceRotationChain R S a c

/-- Helper toward Lemma 5.6: a map preserving steps and omitted cells
 transports every positive restricted rotation chain. -/
theorem enclosedSliceRotationChain_map {A B : Type*} {Q : A → A → Prop} {Q' : B → B → Prop}
      {U : Set A} {U' : Set B} (f : A → B)
      (hQ : ∀ a b, Q a b → Q' (f a) (f b))
      (hU : ∀ a, a ∉ U → f a ∉ U') {a b : A}
      (h : EnclosedSliceRotationChain Q U a b) :
      EnclosedSliceRotationChain Q' U' (f a) (f b) := by
  induction h with
  | single h => exact .single (hQ _ _ h)
  | cons h hb _ ih => exact .cons (hQ _ _ h) (hU _ hb) ih

/-- Helper toward Lemma 5.6: nested rotation chains transport under a
 bijection preserving the step relation and the retained cells. -/
theorem enclosedSliceRotationChain_map_iff {α β : Type*}
    {R : α → α → Prop} {R' : β → β → Prop} {S : Set α} {S' : Set β}
    (I : α ≃ β) (hR : ∀ a b, R a b ↔ R' (I a) (I b))
    (hS : ∀ a, a ∈ S ↔ I a ∈ S') (a b : α) :
    EnclosedSliceRotationChain R S a b ↔ EnclosedSliceRotationChain R' S' (I a) (I b) := by
  constructor
  · exact enclosedSliceRotationChain_map I (fun a b => (hR a b).1)
      (fun a => (not_congr (hS a)).1)
  · intro h
    have hh := enclosedSliceRotationChain_map I.symm (fun a b hab => (hR (I.symm a) (I.symm b)).2
      (by simpa only [Equiv.apply_symm_apply] using hab))
      (fun a ha => (not_congr (hS (I.symm a))).2
        (by simpa only [Equiv.apply_symm_apply] using ha)) h
    simpa only [Equiv.symm_apply_apply] using hh

/-- Helper toward Lemma 5.6: first return under an ambient map, retaining
 the positive time and every omitted intermediate point explicitly. -/
@[expose] def enclosedSliceFirstReturn {α : Type*} (f : α → α)
    (S : Set α) (a b : α) : Prop :=
  ∃ n : ℕ, 0 < n ∧ f^[n] a = b ∧
    ∀ j : ℕ, 0 < j → j < n → f^[j] a ∉ S

/-- Helper toward Lemma 5.6: first return to a nested retained set is a
 positive chain of first returns to the larger set, with all internal
 returns outside the smaller set. This is the relation form of nested
 first return; neither set needs to be globally finite. -/
theorem enclosedSliceFirstReturn_nested {α : Type*} (f : α → α)
    (S T : Set α) (hTS : T ⊆ S) {a b : α} (hb : b ∈ T) :
    enclosedSliceFirstReturn f T a b ↔
      EnclosedSliceRotationChain
        (fun x y => y ∈ S ∧ enclosedSliceFirstReturn f S x y) T a b := by
  classical
  constructor
  · rintro ⟨n, hn, hend, hskip⟩
    induction n using Nat.strong_induction_on generalizing a with
    | h n ih =>
      have hex : ∃ r : ℕ, 0 < r ∧ r ≤ n ∧ f^[r] a ∈ S :=
        ⟨n, hn, le_rfl, hend ▸ hTS hb⟩
      let r := Nat.find hex
      have hr : 0 < r ∧ r ≤ n ∧ f^[r] a ∈ S := Nat.find_spec hex
      have hno (j : ℕ) (hj : 0 < j) (hjr : j < r) : f^[j] a ∉ S := by
        intro hjS
        have hh : r ≤ j := Nat.find_min' hex ⟨hj, hjr.le.trans hr.2.1, hjS⟩
        omega
      by_cases he : r = n
      · exact .single ⟨hTS hb, n, hn, hend, he ▸ hno⟩
      · have hrn : r < n := lt_of_le_of_ne hr.2.1 he
        refine .cons ⟨hr.2.2, r, hr.1, rfl, hno⟩ (hskip r hr.1 hrn) ?_
        apply ih (n - r) (by omega) (by omega)
        · rw [← Function.iterate_add_apply, Nat.sub_add_cancel hr.2.1]
          exact hend
        · intro j hj hjn
          rw [← Function.iterate_add_apply]
          exact hskip (j + r) (by omega) (by omega)
  · intro h
    induction h with
    | single h =>
      obtain ⟨n, hn, he, hno⟩ := h.2
      exact ⟨n, hn, he, fun j hj hjn hm => hno j hj hjn (hTS hm)⟩
    | @cons a c b h hc htail ih =>
      obtain ⟨r, hr, her, hno⟩ := h.2
      obtain ⟨n, hn, hen, hskip⟩ := ih hb
      refine ⟨n + r, by omega, ?_, ?_⟩
      · rw [Function.iterate_add_apply, her, hen]
      · intro j hj hjnr hjT
        rcases lt_trichotomy j r with hlt | heq | hgt
        · exact hno j hj hlt (hTS hjT)
        · exact hc (by simpa only [heq, her] using hjT)
        · apply hskip (j - r) (by omega) (by omega)
          have he : f^[j - r] c = f^[j] a := by
            rw [← her, ← Function.iterate_add_apply, Nat.sub_add_cancel hgt.le]
          exact he ▸ hjT


/-- Helper toward Lemma 5.6: rotation chains lift through an injection
 when each step from its image has an endpoint in that image. -/
theorem enclosedSliceRotationChain_injective_iff {α β : Type*}
    {R : α → α → Prop} {R' : β → β → Prop} {S : Set α} {S' : Set β}
    (f : α → β) (hf : Function.Injective f)
    (hR : ∀ a b, R a b ↔ R' (f a) (f b))
    (hS : ∀ a, a ∈ S ↔ f a ∈ S')
    (hcover : ∀ a y, R' (f a) y → ∃ b, f b = y) (a b : α) :
    EnclosedSliceRotationChain R S a b ↔ EnclosedSliceRotationChain R' S' (f a) (f b) := by
  constructor
  · exact enclosedSliceRotationChain_map f (fun a b => (hR a b).1)
      (fun a => (not_congr (hS a)).1)
  · intro h
    have back {x y : β} (h : EnclosedSliceRotationChain R' S' x y) :
        ∀ a, f a = x → ∃ b, f b = y ∧ EnclosedSliceRotationChain R S a b := by
      induction h with
      | @single x y h =>
        intro a ha
        obtain ⟨b, hb⟩ := hcover a y (ha ▸ h)
        exact ⟨b, hb, .single ((hR a b).2 (by simpa only [ha, hb] using h))⟩
      | @cons x y z h hy _ ih =>
        intro a ha
        obtain ⟨b, hb⟩ := hcover a y (ha ▸ h)
        obtain ⟨c, hc, htail⟩ := ih b hb
        exact ⟨c, hc, .cons ((hR a b).2 (by simpa only [ha, hb] using h))
          ((not_congr (hS b)).2 (hb ▸ hy)) htail⟩
    obtain ⟨c, hc, hchain⟩ := back h a rfl
    exact hf hc ▸ hchain

/-- Helper toward Lemma 5.6: actual slice rotation is nested first return
 through the current left side, with its actual slice image as retained set.
 No enclosure or exhaustion hypothesis is needed for this identity. -/
theorem m0CutGeodesicSlice_rotation_iff_left_chain
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges}) :
    (m0CutGeodesicSlice (hp := hp) P k a b hab).rotation d.val e.val ↔
      EnclosedSliceRotationChain
        (geometricSideRelation (m0GeodesicSide hp (P k) .left) .rotation)
        (Set.range (m0CutGeodesicSliceLeftCell hp P k a b hab))
        (m0CutGeodesicSliceLeftCell hp P k a b hab (.inr d))
        (m0CutGeodesicSliceLeftCell hp P k a b hab (.inr e)) := by
  let M := m0GeodesicSide hp (P k) .left
  let S : Set (ℕ × Bool) := {d | d.1 ∈ M.edges}
  let T : Set (ℕ × Bool) :=
    {d | d.1 ∈ (m0CutGeodesicSlice (hp := hp) P k a b hab).edges}
  let f := (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)
  let inc : S → GeometricSideCell M := fun d => .inr d
  let dS : S := ⟨d.val, d.property.1.2⟩
  let eS : S := ⟨e.val, e.property.1.2⟩
  have hTS : T ⊆ S := fun _ hd => hd.1.2
  have hsub := enclosedSliceRotationChain_injective_iff
    (fun x : S => x.val) Subtype.val_injective
    (R := fun x y : S => enclosedSliceFirstReturn f S x.val y.val)
    (R' := fun x y => y ∈ S ∧ enclosedSliceFirstReturn f S x y)
    (S := {x : S | x.val ∈ T}) (S' := T)
    (fun x y => ⟨fun h => ⟨y.property, h⟩, fun h => h.2⟩)
    (fun _ => Iff.rfl) (fun _ y hy => ⟨⟨y, hy.1⟩, rfl⟩) dS eS
  have hcell := enclosedSliceRotationChain_injective_iff inc
    (fun _ _ hh => Sum.inr.inj hh)
    (R := fun x y : S => enclosedSliceFirstReturn f S x.val y.val)
    (R' := geometricSideRelation M .rotation)
    (S := {x : S | x.val ∈ T})
    (S' := Set.range (m0CutGeodesicSliceLeftCell hp P k a b hab))
    (fun _ _ => Iff.rfl)
    (fun x => (m0CutGeodesicSliceLeftCell_mem_range_iff hp P k a b hab (inc x)).symm)
    (by
      intro x y hxy
      cases y with
      | inl y => exact False.elim hxy
      | inr y => exact ⟨y, rfl⟩) dS eS
  exact (enclosedSliceFirstReturn_nested f S T hTS e.property).trans
    (hsub.symm.trans hcell)


/-- Helper toward Lemma 5.6: the intrinsic relation on retained cells
 between a side's seam and an internal ray. Rotation is induced by first
 return, faces use their oriented right-sector test, and the new root and
 boundary come from the internal ray. -/
@[expose] def geometricSide_enclosed_relation (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) (keep : Set (GeometricSideCell M))
    (t : TruncationRelation) (c e : GeometricSideCell M) : Prop :=
  match t with
  | .root => c = v 0
  | .boundary i => c = d i
  | .rotation => EnclosedSliceRotationChain (geometricSideRelation M .rotation) keep c e
  | .faceNext => geometricSideRelation M .faceNext c e ∧
      geometricSide_intrinsic_right M v d c ∧ ∀ n, c ≠ d n
  | _ => geometricSideRelation M t c e

/-- Helper toward Lemma 5.6: every intrinsic enclosed relation transports
 under a marked isomorphism mapping the ray and retained cells. -/
theorem geometricSide_enclosed_relation_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d : ℕ → GeometricSideCell M)
    (keep : Set (GeometricSideCell M)) (keep' : Set (GeometricSideCell N))
    (hkeep : ∀ c, c ∈ keep ↔ I.equiv c ∈ keep')
    (t : TruncationRelation) (c e : GeometricSideCell M) :
    geometricSide_enclosed_relation M v d keep t c e ↔
      geometricSide_enclosed_relation N (I.equiv ∘ v) (I.equiv ∘ d) keep' t
        (I.equiv c) (I.equiv e) := by
  cases t with
  | root =>
    change c = v 0 ↔ I.equiv c = I.equiv (v 0)
    exact ⟨congrArg I.equiv, fun hh => I.equiv.injective hh⟩
  | boundary i =>
    change c = d i ↔ I.equiv c = I.equiv (d i)
    exact ⟨congrArg I.equiv, fun hh => I.equiv.injective hh⟩
  | rotation =>
    exact enclosedSliceRotationChain_map_iff I.equiv
      (I.relation_iff .rotation) hkeep c e
  | faceNext =>
    exact and_congr (I.relation_iff .faceNext c e)
      (and_congr (geometricSide_intrinsic_right_map_iff I v d c)
        (forall_congr' fun n => not_congr ⟨congrArg I.equiv, fun hh => I.equiv.injective hh⟩))
  | vertex => exact I.relation_iff .vertex c e
  | incident => exact I.relation_iff .incident c e
  | opposite => exact I.relation_iff .opposite c e
  | oriented => exact I.relation_iff .oriented c e
  | target => exact I.relation_iff .target c e
  | seam i => exact I.relation_iff (.seam i) c e

/-- Helper toward Lemma 5.6: the actual slice's complete relation is
 conditional on the displayed Open A hypothesis. This identifies retained
 faces, nested rotation, root and both indexed markings simultaneously. -/
theorem m0CutGeodesicSlice_relation_iff_enclosed_of_openA
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (hA : ∀ c : GeometricSideCell (m0GeodesicSide hp (P k) .left),
      geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
    (a b : ℕ) (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b)
    (t : TruncationRelation)
    (c e : GeometricSideCell (m0CutGeodesicSlice (hp := hp) P k a b hab)) :
    geometricSideRelation (m0CutGeodesicSlice (hp := hp) P k a b hab) t c e ↔
      geometricSide_enclosed_relation (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain)
        (Set.range (m0CutGeodesicSliceLeftCell hp P k a b hab)) t
        (m0CutGeodesicSliceLeftCell hp P k a b hab c)
        (m0CutGeodesicSliceLeftCell hp P k a b hab e) := by
  cases t with
  | rotation =>
    cases c with
    | inl c =>
      cases e <;> refine ⟨False.elim, ?_⟩ <;> intro hh <;>
        cases hh with
        | single h => exact False.elim h
        | cons h _ _ => exact False.elim h
    | inr c =>
      cases e with
      | inl e =>
        refine ⟨False.elim, ?_⟩
        intro hh
        have hend {x y : GeometricSideCell (m0GeodesicSide hp (P k) .left)}
            (hxy : EnclosedSliceRotationChain
              (geometricSideRelation (m0GeodesicSide hp (P k) .left) .rotation)
              (Set.range (m0CutGeodesicSliceLeftCell hp P k a b hab)) x y) :
            ∃ d, y = .inr d := by
          induction hxy with
          | @single x y h => cases y with
            | inl y => exact False.elim (by cases x <;> exact h)
            | inr y => exact ⟨y, rfl⟩
          | cons _ _ _ ih => exact ih
        obtain ⟨d, hd⟩ := hend hh
        exact False.elim (Sum.inl_ne_inr hd)
      | inr e => exact m0CutGeodesicSlice_rotation_iff_left_chain hp P k a b hab c e
  | faceNext =>
    cases c with
    | inl c => cases e <;> exact ⟨False.elim, fun h => h.1.elim⟩
    | inr c =>
      cases e with
      | inl e => exact ⟨False.elim, fun h => h.1.elim⟩
      | inr e =>
        change (_ ∧ _) ↔ (_ ∧ _ ∧ _)
        constructor
        · rintro ⟨hr, hl⟩
          exact ⟨hl, (m0GeodesicLeftSide_previousRight_faceNext_iff_of_openA
            hp P k hcontain hA ⟨c.val, c.property.1.2⟩
              ⟨e.val, e.property.1.2⟩ hl).1 hr⟩
        · rintro ⟨hl, hi⟩
          exact ⟨(m0GeodesicLeftSide_previousRight_faceNext_iff_of_openA
            hp P k hcontain hA ⟨c.val, c.property.1.2⟩
              ⟨e.val, e.property.1.2⟩ hl).2 hi, hl⟩
  | root =>
    cases c with
    | inl c =>
      change c.val = boundaryVertex (shiftedStream W 0) h (k - 1) ↔
        Sum.inl (α := (m0GeodesicSide hp (P k) .left).vertices)
          (β := {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges}) _ = .inl _
      rw [Sum.inl.injEq, Subtype.ext_iff]
      change c.val = boundaryVertex (shiftedStream W 0) h (k - 1) ↔
        c.val = ((P (k - 1)).codePath.initial 0).1.id
      rw [m0Geodesic_initial_zero]
    | inr c => exact ⟨False.elim, fun hh => (Sum.inr_ne_inl hh).elim⟩
  | boundary i =>
    cases c with
    | inl c => exact ⟨False.elim, fun hh => (Sum.inl_ne_inr hh).elim⟩
    | inr c =>
      change ((P (k - 1)).codePath.edge i, false) = c.val ↔ Sum.inr _ = Sum.inr _
      rw [Sum.inr.injEq, Subtype.ext_iff]
      exact eq_comm
  | vertex => cases c <;> cases e <;> rfl
  | incident => cases c <;> cases e <;> rfl
  | opposite => cases c <;> cases e <;> rfl
  | oriented => cases c <;> cases e <;> rfl
  | target => cases c <;> cases e <;> rfl
  | seam i => cases c <;> cases e <;> rfl


section FullRestriction

variable {W' : ℤ → Fin 3} {H' : WholePlaneRotationHypothesis W'}
  {h' : BoundaryHitWitnesses (shiftedStream W' 0)}
  {hLL' : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W'
    (wholePlaneEdgeι W' 0
      (kmswLLCreatedEdge (shiftedStream W' 0)
        (boundaryHitTime (shiftedStream W' 0) h' (k - 1))))}
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (hp' : BoundaryHitWitnesses (kmswPastCode W')) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (P' : ∀ k : ℤ, M0CutInfiniteGeodesic W' H' h' hLL' k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (T' : ∀ k : ℤ, InfinitePresentPath (shiftedStream W' 0)
    (boundaryPresentVertex (shiftedStream W' 0) h' k))
  (hleft : ∀ k : ℤ,
    Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hleft' : ∀ k : ℤ,
    Xdp.CutLeftmostXdp W' H' h' hp' hLL' longest k (P' k) (T' k))
  (k l : ℤ)
  (hcontain : ∀ n : ℕ,
    (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
    ((P (k - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp (P k) .left).vertices)
  (hcontain' : ∀ n : ℕ,
    (P' (l - 1)).codePath.edge n ∈ (m0GeodesicSide hp' (P' l) .left).edges ∧
    ((P' (l - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp' (P' l) .left).vertices)
  (I : GeometricSideMarkedIso (m0GeodesicSide hp (P k) .left)
    (m0GeodesicSide hp' (P' l) .left))
  (hA : ∀ c : GeometricSideCell (m0GeodesicSide hp (P k) .left),
    geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
    match c with
    | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
    | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
  (hA' : ∀ c : GeometricSideCell (m0GeodesicSide hp' (P' l) .left),
    geometricSide_intrinsic_right (m0GeodesicSide hp' (P' l) .left)
      (m0GeodesicSideAdjacentVertices hp' P' l hcontain')
      (m0GeodesicSideAdjacentDarts hp' P' l hcontain') c ↔
    match c with
    | .inl v => v.val ∈ m0GeodesicSideVertices hp' (P' (l - 1)) .right
    | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp' (P' (l - 1)) .right)

include hleft hleft' hcontain hcontain' hA hA' in
/-- Helper toward Lemma 5.6: Open B is conditional on the displayed
 Open A hypotheses for both realizations. The supplied marked isomorphism
 restricts to the actual slices, preserving retained faces, induced rotation,
 root and all indexed marks, with the displayed commuting equation. -/
theorem m0GeodesicLeftSide_markedIso_restrict_slice_of_openA
    (a b : ℕ) (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    let hab' := (m0GeodesicLeftSide_markedIso_leastCoalescence_iff
      hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I a b).1 hab
    ∃ J : GeometricSideMarkedIso
      (m0CutGeodesicSlice (hp := hp) P k a b hab)
      (m0CutGeodesicSlice (hp := hp') P' l a b hab'),
      ∀ c, m0CutGeodesicSliceLeftCell hp' P' l a b hab' (J.equiv c) =
        I.equiv (m0CutGeodesicSliceLeftCell hp P k a b hab c) := by
  dsimp only
  obtain ⟨J, hJ⟩ := m0GeodesicLeftSide_markedIso_slice_equiv_of_openA
    hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I hA hA' a b hab
  refine ⟨⟨J, ?_⟩, hJ⟩
  intro t c e
  have hm := geometricSide_enclosed_relation_map_iff I
    (m0GeodesicSideAdjacentVertices hp P k hcontain)
    (m0GeodesicSideAdjacentDarts hp P k hcontain)
    (Set.range (m0CutGeodesicSliceLeftCell hp P k a b hab))
    (Set.range (m0CutGeodesicSliceLeftCell hp' P' l a b _))
    (m0GeodesicLeftSide_markedIso_slice_range_iff_of_openA
      hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I hA hA' a b hab)
    t (m0CutGeodesicSliceLeftCell hp P k a b hab c)
      (m0CutGeodesicSliceLeftCell hp P k a b hab e)
  obtain ⟨hv, hd⟩ := m0GeodesicLeftSide_markedIso_map_previousRay
    hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I
  rw [hv, hd, ← hJ c, ← hJ e] at hm
  exact (m0CutGeodesicSlice_relation_iff_enclosed_of_openA
    hp P k hcontain hA a b hab t c e).trans (hm.trans
      (m0CutGeodesicSlice_relation_iff_enclosed_of_openA
        hp' P' l hcontain' hA' a b _ t (J c) (J e)).symm)

end FullRestriction

/-- Helper toward Lemma 5.6: containment of the preceding ray in the
 current closed-left side implies nesting of the actual open-left regions.
 This uses their west-or-above characterization, without coalescence. -/
theorem m0GeodesicLeftOpen_previous_subset_of_ray_containment
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    m0GeodesicLeftOpen hp (P (k - 1)) ⊆ m0GeodesicLeftOpen hp (P k) := by
  have htrace : m0GeodesicTrace hp (P (k - 1)) ⊆
      m0GeodesicSideRegion hp (P k) .left := by
    intro y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    exact (hcontain n).1 hn
  intro z hz
  obtain ⟨hzA, hw | ⟨y, hy, hre, him⟩⟩ :=
    (m0CutGeodesicLeftOpen_iff_west_or_above_trace hp (P (k - 1)) z).1 hz
  · exact (m0CutGeodesicLeftOpen_iff_west_or_above_trace hp (P k) z).2
      ⟨hzA, Or.inl (hw.trans (seamX_strictMono (shiftedStream W 0) h (H.1 0)
        (show k - 1 < k by omega)))⟩
  · apply (m0CutGeodesicLeftOpen_iff_west_or_above_trace hp (P k) z).2
    refine ⟨hzA, ?_⟩
    by_cases hyT : y ∈ m0GeodesicTrace hp (P k)
    · exact Or.inr ⟨y, hyT, hre, him⟩
    · have hyL := m0GeodesicLeftOpen_closure_inter_complement_subset hp (P k)
        ⟨(htrace hy).1, (htrace hy).2, hyT⟩
      rcases ((m0CutGeodesicLeftOpen_iff_west_or_above_trace hp (P k) y).1 hyL).2
        with hw | ⟨q, hq, hqr, hqi⟩
      · exact Or.inl (hre ▸ hw)
      · exact Or.inr ⟨q, hq, hqr.trans hre, hqi.trans him⟩

/-- Helper toward Lemma 5.6: the corresponding closed-left regions are
 nested, with no additional coalescence hypothesis. -/
theorem m0GeodesicLeftSide_previous_subset_of_ray_containment
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    m0GeodesicSideRegion hp (P (k - 1)) .left ⊆
      m0GeodesicSideRegion hp (P k) .left := by
  intro z hz
  exact ⟨closure_mono (m0GeodesicLeftOpen_previous_subset_of_ray_containment
    hp P k hcontain) hz.1, hz.2⟩

/-- Helper toward Lemma 5.6: complement-of-open-candidate reconstruction
 of the preceding left carrier is conditional on the displayed Open A
 hypothesis. Ray vertices and both darts of ray edges are retained. -/
theorem m0GeodesicLeftSide_previousLeft_mem_iff_of_openA
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (hA : ∀ c : GeometricSideCell (m0GeodesicSide hp (P k) .left),
      geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    (match c with
     | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .left
     | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .left) ↔
      ¬ geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
          (m0GeodesicSideAdjacentVertices hp P k hcontain)
          (m0GeodesicSideAdjacentDarts hp P k hcontain) c ∨
        geometricSide_ray_vertex (m0GeodesicSide hp (P k) .left)
          (m0GeodesicSideAdjacentVertices hp P k hcontain) c ∨
        geometricSide_ray_dart (m0GeodesicSide hp (P k) .left)
          (m0GeodesicSideAdjacentDarts hp P k hcontain) c := by
  classical
  rw [hA c]
  cases c with
  | inl v =>
    have hvr := m0GeodesicLeftSide_ray_vertex_iff hp P k hcontain v
    have hdn : ¬ geometricSide_ray_dart (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) (.inl v) := by
      rintro ⟨n, he | he⟩
      · exact Sum.inl_ne_inr he
      · exact he
    simp only [hdn, or_false, hvr]
    constructor
    · intro hv
      by_cases hr : v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
      · exact Or.inr ((m0GeodesicSideVertices_inter hp (P (k - 1))) ▸ ⟨hv, hr⟩)
      · exact Or.inl hr
    · rintro (hn | hr)
      · exact (m0GeodesicSideVertices_cover hp (P (k - 1)) v.val).resolve_right hn
      · rw [← m0GeodesicSideVertices_inter hp (P (k - 1))] at hr
        exact hr.1
  | inr d =>
    have hdr := m0GeodesicLeftSide_ray_dart_iff hp P k hcontain d
    have hvn : ¬ geometricSide_ray_vertex (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain) (.inr d) := by
      rintro ⟨n, he⟩
      exact Sum.inr_ne_inl he
    simp only [hvn, false_or, hdr]
    constructor
    · intro hd
      by_cases hr : d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right
      · exact Or.inr ((boundaryGluing_m0SideEdges_inter W h (k - 1) longest hp
          (P (k - 1))) ▸ ⟨hd, hr⟩)
      · exact Or.inl hr
    · rintro (hn | hr)
      · exact (m0GeodesicSideEdges_cover hp (P (k - 1)) d.val.1).resolve_right hn
      · exact (m0GeodesicEdges_subset_both hp (P (k - 1)) hr).1


/-- Helper toward Lemma 5.6: the canonical inclusion of the entire
 preceding closed-left side in the current closed-left side. -/
@[expose] def m0GeodesicPreviousLeftCell
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .left) →
      GeometricSideCell (m0GeodesicSide hp (P k) .left)
  | .inl v => .inl ⟨v.val,
      m0GeodesicLeftSide_previous_subset_of_ray_containment hp P k hcontain v.property⟩
  | .inr d => .inr ⟨d.val, fun _ hz =>
      m0GeodesicLeftSide_previous_subset_of_ray_containment hp P k hcontain (d.property hz)⟩

/-- Helper toward Lemma 5.6: the preceding-side inclusion preserves cell
 identity and is injective. -/
theorem m0GeodesicPreviousLeftCell_injective
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    Function.Injective (m0GeodesicPreviousLeftCell hp P k hcontain) := by
  intro c e hh
  cases c <;> cases e
  · dsimp only [m0GeodesicPreviousLeftCell] at hh
    have hv := congrArg Subtype.val (Sum.inl.inj hh)
    exact congrArg Sum.inl (Subtype.ext hv)
  · exact False.elim (Sum.inl_ne_inr hh)
  · exact False.elim (Sum.inr_ne_inl hh)
  · dsimp only [m0GeodesicPreviousLeftCell] at hh
    have hd := congrArg Subtype.val (Sum.inr.inj hh)
    exact congrArg Sum.inr (Subtype.ext hd)

/-- Helper toward Lemma 5.6: the preceding-side inclusion has exactly
 the preceding left-side vertex and edge carrier as its image. -/
theorem m0GeodesicPreviousLeftCell_mem_range_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    c ∈ Set.range (m0GeodesicPreviousLeftCell hp P k hcontain) ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .left
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .left := by
  cases c with
  | inl v =>
    change (∃ u, m0GeodesicPreviousLeftCell hp P k hcontain u = .inl v) ↔
      v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .left
    constructor
    · rintro ⟨u, hu⟩
      cases u with
      | inl u => exact (congrArg Subtype.val (Sum.inl.inj hu)) ▸ u.property
      | inr u => exact False.elim (Sum.inr_ne_inl hu)
    · intro hv
      exact ⟨.inl ⟨v.val, hv⟩, rfl⟩
  | inr d =>
    change (∃ u, m0GeodesicPreviousLeftCell hp P k hcontain u = .inr d) ↔
      d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .left
    constructor
    · rintro ⟨u, hu⟩
      cases u with
      | inl u => exact False.elim (Sum.inl_ne_inr hu)
      | inr u => exact (congrArg Prod.fst (congrArg Subtype.val (Sum.inr.inj hu))) ▸ u.property
    · intro hd
      exact ⟨.inr ⟨d.val, hd⟩, rfl⟩

section PreviousTransport

variable {W' : ℤ → Fin 3} {H' : WholePlaneRotationHypothesis W'}
  {h' : BoundaryHitWitnesses (shiftedStream W' 0)}
  {hLL' : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W'
    (wholePlaneEdgeι W' 0
      (kmswLLCreatedEdge (shiftedStream W' 0)
        (boundaryHitTime (shiftedStream W' 0) h' (k - 1))))}
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (hp' : BoundaryHitWitnesses (kmswPastCode W')) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (P' : ∀ k : ℤ, M0CutInfiniteGeodesic W' H' h' hLL' k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (T' : ∀ k : ℤ, InfinitePresentPath (shiftedStream W' 0)
    (boundaryPresentVertex (shiftedStream W' 0) h' k))
  (hleft : ∀ k : ℤ,
    Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hleft' : ∀ k : ℤ,
    Xdp.CutLeftmostXdp W' H' h' hp' hLL' longest k (P' k) (T' k))
  (k l : ℤ)
  (hcontain : ∀ n : ℕ,
    (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
    ((P (k - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp (P k) .left).vertices)
  (hcontain' : ∀ n : ℕ,
    (P' (l - 1)).codePath.edge n ∈ (m0GeodesicSide hp' (P' l) .left).edges ∧
    ((P' (l - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp' (P' l) .left).vertices)
  (I : GeometricSideMarkedIso (m0GeodesicSide hp (P k) .left)
    (m0GeodesicSide hp' (P' l) .left))
  (hA : ∀ c : GeometricSideCell (m0GeodesicSide hp (P k) .left),
    geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
    match c with
    | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
    | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
  (hA' : ∀ c : GeometricSideCell (m0GeodesicSide hp' (P' l) .left),
    geometricSide_intrinsic_right (m0GeodesicSide hp' (P' l) .left)
      (m0GeodesicSideAdjacentVertices hp' P' l hcontain')
      (m0GeodesicSideAdjacentDarts hp' P' l hcontain') c ↔
    match c with
    | .inl v => v.val ∈ m0GeodesicSideVertices hp' (P' (l - 1)) .right
    | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp' (P' (l - 1)) .right)

include hleft hleft' hcontain hcontain' hA hA' in
/-- Helper toward Lemma 5.6: preceding-left carrier transport is
 conditional on the displayed Open A hypotheses for both realizations.
 It is restriction to the complement of the open candidate, retaining
 the entire ray. This statement concerns cells; marked relations follow separately. -/
theorem m0GeodesicLeftSide_markedIso_previousLeft_range_iff_of_openA
    (c : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    c ∈ Set.range (m0GeodesicPreviousLeftCell hp P k hcontain) ↔
      I.equiv c ∈ Set.range (m0GeodesicPreviousLeftCell hp' P' l hcontain') := by
  rw [m0GeodesicPreviousLeftCell_mem_range_iff,
    m0GeodesicPreviousLeftCell_mem_range_iff]
  refine (m0GeodesicLeftSide_previousLeft_mem_iff_of_openA hp P k hcontain hA c).trans
    (Iff.trans ?_ (m0GeodesicLeftSide_previousLeft_mem_iff_of_openA
      hp' P' l hcontain' hA' (I.equiv c)).symm)
  obtain ⟨hv, hd⟩ := m0GeodesicLeftSide_markedIso_map_previousRay
    hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I
  have hvr := geometricSide_ray_vertex_map_iff I
    (m0GeodesicSideAdjacentVertices hp P k hcontain) c
  have hdr := geometricSide_ray_dart_map_iff I
    (m0GeodesicSideAdjacentDarts hp P k hcontain) c
  rw [hv] at hvr
  rw [hd] at hdr
  exact or_congr (not_congr (m0GeodesicLeftSide_markedIso_intrinsic_right_iff
    hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I c)) (or_congr hvr hdr)

include hleft hleft' hcontain hcontain' hA hA' in
/-- Helper toward Lemma 5.6: the supplied isomorphism restricts to the
 preceding left carriers, conditional on the displayed Open A hypotheses
 for both realizations, with its exact commuting equation. -/
theorem m0GeodesicLeftSide_markedIso_previousLeft_equiv_of_openA :
    ∃ J : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .left) ≃
        GeometricSideCell (m0GeodesicSide hp' (P' (l - 1)) .left),
      ∀ c, m0GeodesicPreviousLeftCell hp' P' l hcontain' (J c) =
        I.equiv (m0GeodesicPreviousLeftCell hp P k hcontain c) := by
  exact enclosedSlice_exists_equiv_restrict _ _
    (m0GeodesicPreviousLeftCell_injective hp P k hcontain)
    (m0GeodesicPreviousLeftCell_injective hp' P' l hcontain') I.equiv
    (m0GeodesicLeftSide_markedIso_previousLeft_range_iff_of_openA
      hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I hA hA')

end PreviousTransport

/-- Helper toward Lemma 5.6: preceding-left retained faces are precisely
 current-left retained faces which are not preceding-right retained faces. -/
theorem m0GeodesicPreviousLeft_faceNext_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P k) .left).edges}) :
    (m0GeodesicSide hp (P (k - 1)) .left).faceNext d.val e.val ↔
      (m0GeodesicSide hp (P k) .left).faceNext d.val e.val ∧
        ¬ (m0GeodesicSide hp (P (k - 1)) .right).faceNext d.val e.val := by
  constructor
  · rintro ⟨⟨F, hb, hl⟩, hsucc⟩
    refine ⟨⟨⟨F, hb, ?_⟩, hsucc⟩, ?_⟩
    · exact fun z hz => m0GeodesicLeftOpen_previous_subset_of_ray_containment
        hp P k hcontain (hl hz)
    · rintro ⟨⟨G, hG, hr⟩, _⟩
      have hi := m0Geodesic_right_face_dart_invariant hp (P (k - 1)) (P k) d G hG hr
      have hFR := m0Geodesic_invariant_dart_face_right hp (P (k - 1)) (P k) d hi F
        (fun _ hz => (m0GeodesicLeftOpen_subset hp (P (k - 1)) (hl hz)).1) hb
      obtain ⟨z, hz, hF⟩ := F.property
      have hzF := hF ▸ mem_connectedComponentIn hz
      exact Set.disjoint_left.mp (m0GeodesicSideOpenRegion_disjoint hp (P (k - 1)))
        (hl hzF) (hFR hzF)
  · rintro ⟨⟨⟨F, hb, hl⟩, hsucc⟩, hnot⟩
    have hFA : F.val ⊆ m0GeodesicAmbientRegion W H h :=
      fun _ hz => (m0GeodesicLeftOpen_subset hp (P k) (hl hz)).1
    obtain ⟨s, hs, _⟩ := m0GeodesicFace_exactly_one hp (P (k - 1)) F hFA
    cases s with
    | left => exact ⟨⟨F, hb, hs⟩, hsucc⟩
    | right => exact False.elim (hnot ⟨⟨F, hb, hs⟩, hsucc⟩)

/-- Helper toward Lemma 5.6: rotation of the preceding left side is the
 nested first return through current-left rotation. -/
theorem m0GeodesicPreviousLeft_rotation_iff_left_chain
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .left).edges}) :
    (m0GeodesicSide hp (P (k - 1)) .left).rotation d.val e.val ↔
      EnclosedSliceRotationChain
        (geometricSideRelation (m0GeodesicSide hp (P k) .left) .rotation)
        (Set.range (m0GeodesicPreviousLeftCell hp P k hcontain))
        (m0GeodesicPreviousLeftCell hp P k hcontain (.inr d))
        (m0GeodesicPreviousLeftCell hp P k hcontain (.inr e)) := by
  let M := m0GeodesicSide hp (P k) .left
  let S : Set (ℕ × Bool) := {d | d.1 ∈ M.edges}
  let T : Set (ℕ × Bool) := {d | d.1 ∈ (m0GeodesicSide hp (P (k - 1)) .left).edges}
  let f := (kmswInfRot (shiftedStream W 0) (H.1 0) : (ℕ × Bool) → ℕ × Bool)
  have hTS : T ⊆ S := fun _ hd _ hz =>
    m0GeodesicLeftSide_previous_subset_of_ray_containment hp P k hcontain (hd hz)
  let dS : S := ⟨d.val, hTS d.property⟩
  let eS : S := ⟨e.val, hTS e.property⟩
  let inc : S → GeometricSideCell M := fun d => .inr d
  have hsub := enclosedSliceRotationChain_injective_iff
    (fun x : S => x.val) Subtype.val_injective
    (R := fun x y : S => enclosedSliceFirstReturn f S x.val y.val)
    (R' := fun x y => y ∈ S ∧ enclosedSliceFirstReturn f S x y)
    (S := {x : S | x.val ∈ T}) (S' := T)
    (fun x y => ⟨fun h => ⟨y.property, h⟩, fun h => h.2⟩)
    (fun _ => Iff.rfl) (fun _ y hy => ⟨⟨y, hy.1⟩, rfl⟩) dS eS
  have hcell := enclosedSliceRotationChain_injective_iff inc
    (fun _ _ hh => Sum.inr.inj hh)
    (R := fun x y : S => enclosedSliceFirstReturn f S x.val y.val)
    (R' := geometricSideRelation M .rotation)
    (S := {x : S | x.val ∈ T})
    (S' := Set.range (m0GeodesicPreviousLeftCell hp P k hcontain))
    (fun _ _ => Iff.rfl)
    (fun x => (m0GeodesicPreviousLeftCell_mem_range_iff hp P k hcontain (inc x)).symm)
    (by
      intro x y hxy
      cases y with
      | inl y => exact False.elim hxy
      | inr y => exact ⟨y, rfl⟩) dS eS
  exact (enclosedSliceFirstReturn_nested f S T hTS e.property).trans
    (hsub.symm.trans hcell)

/-- Helper toward Lemma 5.6: intrinsic relations for the preceding
 left-side restriction, with the shifted exterior boundary and internal seam. -/
@[expose] def geometricSide_previous_left_relation (M : GeometricSideSubmap)
    (v d : ℕ → GeometricSideCell M) (keep : Set (GeometricSideCell M))
    (t : TruncationRelation) (c e : GeometricSideCell M) : Prop :=
  match t with
  | .root => c = v 0
  | .boundary i => geometricSideRelation M (.boundary (i + 1)) c e
  | .seam i => c = d i
  | .rotation => EnclosedSliceRotationChain (geometricSideRelation M .rotation) keep c e
  | .faceNext => geometricSideRelation M .faceNext c e ∧
      ¬ (geometricSide_intrinsic_right M v d c ∧ ∀ n, c ≠ d n)
  | _ => geometricSideRelation M t c e

/-- Helper toward Lemma 5.6: every intrinsic preceding-left relation
 transports under a marked isomorphism preserving the ray and retained cells. -/
theorem geometricSide_previous_left_relation_map_iff {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) (v d : ℕ → GeometricSideCell M)
    (keep : Set (GeometricSideCell M)) (keep' : Set (GeometricSideCell N))
    (hkeep : ∀ c, c ∈ keep ↔ I.equiv c ∈ keep')
    (t : TruncationRelation) (c e : GeometricSideCell M) :
    geometricSide_previous_left_relation M v d keep t c e ↔
      geometricSide_previous_left_relation N (I.equiv ∘ v) (I.equiv ∘ d) keep' t
        (I.equiv c) (I.equiv e) := by
  cases t with
  | root =>
    change c = v 0 ↔ I.equiv c = I.equiv (v 0)
    exact ⟨congrArg I.equiv, fun hh => I.equiv.injective hh⟩
  | seam i =>
    change c = d i ↔ I.equiv c = I.equiv (d i)
    exact ⟨congrArg I.equiv, fun hh => I.equiv.injective hh⟩
  | rotation =>
    exact enclosedSliceRotationChain_map_iff I.equiv (I.relation_iff .rotation) hkeep c e
  | faceNext =>
    exact and_congr (I.relation_iff .faceNext c e)
      (not_congr (and_congr (geometricSide_intrinsic_right_map_iff I v d c)
        (forall_congr' fun n => not_congr ⟨congrArg I.equiv, fun hh => I.equiv.injective hh⟩)))
  | boundary i => exact I.relation_iff (.boundary (i + 1)) c e
  | vertex => exact I.relation_iff .vertex c e
  | incident => exact I.relation_iff .incident c e
  | opposite => exact I.relation_iff .opposite c e
  | oriented => exact I.relation_iff .oriented c e
  | target => exact I.relation_iff .target c e


/-- Helper toward Lemma 5.6: a positive rotation chain has an initial step. -/
theorem enclosedSliceRotationChain_first {α : Type*} {R : α → α → Prop}
    {S : Set α} {a b : α} (h : EnclosedSliceRotationChain R S a b) : ∃ c, R a c := by
  cases h with
  | single h => exact ⟨_, h⟩
  | cons h _ _ => exact ⟨_, h⟩

/-- Helper toward Lemma 5.6: a positive rotation chain has a final step. -/
theorem enclosedSliceRotationChain_last {α : Type*} {R : α → α → Prop}
    {S : Set α} {a b : α} (h : EnclosedSliceRotationChain R S a b) : ∃ c, R c b := by
  induction h with
  | single h => exact ⟨_, h⟩
  | cons _ _ _ ih => exact ih

/-- Helper toward Lemma 5.6: all preceding-left relations, with their
 actual marks, are reconstructed conditional on the displayed Open A
 hypothesis. Rotation is induced and only actual retained faces are used. -/
theorem m0GeodesicPreviousLeft_relation_iff_of_openA
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (hA : ∀ c : GeometricSideCell (m0GeodesicSide hp (P k) .left),
      geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
      match c with
      | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
      | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
    (t : TruncationRelation)
    (c e : GeometricSideCell (m0GeodesicSide hp (P (k - 1)) .left)) :
    geometricSideRelation (m0GeodesicSide hp (P (k - 1)) .left) t c e ↔
      geometricSide_previous_left_relation (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentVertices hp P k hcontain)
        (m0GeodesicSideAdjacentDarts hp P k hcontain)
        (Set.range (m0GeodesicPreviousLeftCell hp P k hcontain)) t
        (m0GeodesicPreviousLeftCell hp P k hcontain c)
        (m0GeodesicPreviousLeftCell hp P k hcontain e) := by
  cases t with
  | rotation =>
    cases c with
    | inl c =>
      cases e <;> refine ⟨False.elim, ?_⟩ <;> intro hh <;>
        obtain ⟨z, hz⟩ := enclosedSliceRotationChain_first hh <;> cases z <;> exact hz.elim
    | inr c =>
      cases e with
      | inl e =>
        refine ⟨False.elim, ?_⟩
        intro hh
        obtain ⟨z, hz⟩ := enclosedSliceRotationChain_last hh
        cases z <;> exact hz.elim
      | inr e => exact m0GeodesicPreviousLeft_rotation_iff_left_chain hp P k hcontain c e
  | faceNext =>
    cases c with
    | inl c => cases e <;> exact ⟨False.elim, fun h => h.1.elim⟩
    | inr c =>
      cases e with
      | inl e => exact ⟨False.elim, fun h => h.1.elim⟩
      | inr e =>
        let dL := (m0GeodesicPreviousLeftCell hp P k hcontain (.inr c))
        let eL := (m0GeodesicPreviousLeftCell hp P k hcontain (.inr e))
        have hcL : c.val.1 ∈ (m0GeodesicSide hp (P k) .left).edges :=
          fun _ hz => m0GeodesicLeftSide_previous_subset_of_ray_containment hp P k hcontain (c.property hz)
        have heL : e.val.1 ∈ (m0GeodesicSide hp (P k) .left).edges :=
          fun _ hz => m0GeodesicLeftSide_previous_subset_of_ray_containment hp P k hcontain (e.property hz)
        refine (m0GeodesicPreviousLeft_faceNext_iff hp P k hcontain
          ⟨c.val, hcL⟩ ⟨e.val, heL⟩).trans ?_
        apply and_congr_right
        intro hcur
        exact not_congr (m0GeodesicLeftSide_previousRight_faceNext_iff_of_openA
          hp P k hcontain hA ⟨c.val, hcL⟩ ⟨e.val, heL⟩ hcur)
  | root =>
    cases c with
    | inl c =>
      change c.val = boundaryVertex (shiftedStream W 0) h (k - 1) ↔ Sum.inl _ = Sum.inl _
      rw [Sum.inl.injEq, Subtype.ext_iff]
      change c.val = boundaryVertex (shiftedStream W 0) h (k - 1) ↔
        c.val = ((P (k - 1)).codePath.initial 0).1.id
      rw [m0Geodesic_initial_zero]
    | inr c => exact ⟨False.elim, fun hh => (Sum.inr_ne_inl hh).elim⟩
  | seam i =>
    cases c with
    | inl c => exact ⟨False.elim, fun hh => (Sum.inl_ne_inr hh).elim⟩
    | inr c =>
      change ((P (k - 1)).codePath.edge i, false) = c.val ↔ Sum.inr _ = Sum.inr _
      rw [Sum.inr.injEq, Subtype.ext_iff]
      exact eq_comm
  | boundary i =>
    have hb : (m0GeodesicSide hp (P (k - 1)) .left).boundary i =
        (m0GeodesicSide hp (P k) .left).boundary (i + 1) := by
      change (boundaryOuterEdge (shiftedStream W 0) h ((k - 1) - 1 - (i : ℤ)), true) =
        (boundaryOuterEdge (shiftedStream W 0) h (k - 1 - ((i + 1 : ℕ) : ℤ)), true)
      congr 2
      omega
    cases c <;> cases e <;>
      simp only [geometricSide_previous_left_relation, geometricSideRelation,
        m0GeodesicPreviousLeftCell, hb]
  | vertex => cases c <;> cases e <;> rfl
  | incident => cases c <;> cases e <;> rfl
  | opposite => cases c <;> cases e <;> rfl
  | oriented => cases c <;> cases e <;> rfl
  | target => cases c <;> cases e <;> rfl


section PreviousMarkedTransport

variable {W' : ℤ → Fin 3} {H' : WholePlaneRotationHypothesis W'}
  {h' : BoundaryHitWitnesses (shiftedStream W' 0)}
  {hLL' : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W'
    (wholePlaneEdgeι W' 0
      (kmswLLCreatedEdge (shiftedStream W' 0)
        (boundaryHitTime (shiftedStream W' 0) h' (k - 1))))}
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (hp' : BoundaryHitWitnesses (kmswPastCode W')) {longest : Bool}
  (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
  (P' : ∀ k : ℤ, M0CutInfiniteGeodesic W' H' h' hLL' k longest)
  (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (T' : ∀ k : ℤ, InfinitePresentPath (shiftedStream W' 0)
    (boundaryPresentVertex (shiftedStream W' 0) h' k))
  (hleft : ∀ k : ℤ,
    Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
  (hleft' : ∀ k : ℤ,
    Xdp.CutLeftmostXdp W' H' h' hp' hLL' longest k (P' k) (T' k))
  (k l : ℤ)
  (hcontain : ∀ n : ℕ,
    (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
    ((P (k - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp (P k) .left).vertices)
  (hcontain' : ∀ n : ℕ,
    (P' (l - 1)).codePath.edge n ∈ (m0GeodesicSide hp' (P' l) .left).edges ∧
    ((P' (l - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSide hp' (P' l) .left).vertices)
  (I : GeometricSideMarkedIso (m0GeodesicSide hp (P k) .left)
    (m0GeodesicSide hp' (P' l) .left))
  (hA : ∀ c : GeometricSideCell (m0GeodesicSide hp (P k) .left),
    geometricSide_intrinsic_right (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) c ↔
    match c with
    | .inl v => v.val ∈ m0GeodesicSideVertices hp (P (k - 1)) .right
    | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp (P (k - 1)) .right)
  (hA' : ∀ c : GeometricSideCell (m0GeodesicSide hp' (P' l) .left),
    geometricSide_intrinsic_right (m0GeodesicSide hp' (P' l) .left)
      (m0GeodesicSideAdjacentVertices hp' P' l hcontain')
      (m0GeodesicSideAdjacentDarts hp' P' l hcontain') c ↔
    match c with
    | .inl v => v.val ∈ m0GeodesicSideVertices hp' (P' (l - 1)) .right
    | .inr d => d.val.1 ∈ m0GeodesicSideEdges hp' (P' (l - 1)) .right)

include hleft hleft' hcontain hcontain' hA hA' in
/-- Helper toward Lemma 5.6: restriction to the entire preceding left
 sides, with every mark, is conditional on the displayed Open A hypotheses
 for both realizations. The commuting equation fixes the restriction of
 the supplied isomorphism. -/
theorem m0GeodesicLeftSide_markedIso_restrict_previousLeft_of_openA :
    ∃ J : GeometricSideMarkedIso
      (m0GeodesicSide hp (P (k - 1)) .left)
      (m0GeodesicSide hp' (P' (l - 1)) .left),
      ∀ c, m0GeodesicPreviousLeftCell hp' P' l hcontain' (J.equiv c) =
        I.equiv (m0GeodesicPreviousLeftCell hp P k hcontain c) := by
  obtain ⟨J, hJ⟩ := m0GeodesicLeftSide_markedIso_previousLeft_equiv_of_openA
    hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I hA hA'
  refine ⟨⟨J, ?_⟩, hJ⟩
  intro t c e
  have hm := geometricSide_previous_left_relation_map_iff I
    (m0GeodesicSideAdjacentVertices hp P k hcontain)
    (m0GeodesicSideAdjacentDarts hp P k hcontain)
    (Set.range (m0GeodesicPreviousLeftCell hp P k hcontain))
    (Set.range (m0GeodesicPreviousLeftCell hp' P' l hcontain'))
    (m0GeodesicLeftSide_markedIso_previousLeft_range_iff_of_openA
      hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I hA hA')
    t (m0GeodesicPreviousLeftCell hp P k hcontain c)
      (m0GeodesicPreviousLeftCell hp P k hcontain e)
  obtain ⟨hv, hd⟩ := m0GeodesicLeftSide_markedIso_map_previousRay
    hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I
  rw [hv, hd, ← hJ c, ← hJ e] at hm
  exact (m0GeodesicPreviousLeft_relation_iff_of_openA
    hp P k hcontain hA t c e).trans (hm.trans
      (m0GeodesicPreviousLeft_relation_iff_of_openA
        hp' P' l hcontain' hA' t (J c) (J e)).symm)

include hleft hleft' hcontain hcontain' hA hA' in
include I in
/-- Helper toward Lemma 5.6: invariance of the preceding-left marked
 class is conditional on the displayed Open A hypotheses for both
 realizations. No numbered-result completion is asserted. -/
theorem m0GeodesicLeftSide_markedIso_previousLeft_class_eq_of_openA :
    geometricSideClass (m0GeodesicSide hp (P (k - 1)) .left) =
      geometricSideClass (m0GeodesicSide hp' (P' (l - 1)) .left) := by
  obtain ⟨J, _⟩ := m0GeodesicLeftSide_markedIso_restrict_previousLeft_of_openA
    hp hp' P P' T T' hleft hleft' k l hcontain hcontain' I hA hA'
  exact (geometricSideClass_eq_iff _ _).2 ⟨J⟩

end PreviousMarkedTransport
end DirectedDistances.PaperProofs.Section5











































































