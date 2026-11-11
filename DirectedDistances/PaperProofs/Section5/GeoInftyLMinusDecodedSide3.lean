/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole19

/-! This is a formalization-internal correction of the decoder's boundary-mark
No paper-completion claim is made. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: reverse each boundary mark, retaining all geometry. -/
@[expose] def _root_.DirectedDistances.PaperProofs.Section4.GeometricSideSubmap.flipBoundary (M : GeometricSideSubmap) :
    GeometricSideSubmap :=
  { M with boundary := fun i => ((M.boundary i).1, !(M.boundary i).2) }

/-- Helper toward Lemma 5.5: reversing boundary marks twice is the identity. -/
@[simp] theorem _root_.DirectedDistances.PaperProofs.Section4.GeometricSideSubmap.flipBoundary_flipBoundary (M : GeometricSideSubmap) :
    M.flipBoundary.flipBoundary = M := by
  cases M
  simp only [DirectedDistances.PaperProofs.Section4.GeometricSideSubmap.flipBoundary, Bool.not_not, Prod.eta]

/-- Helper toward Lemma 5.5: a flipped boundary mark is the opposite of an original mark. -/
theorem geometricSideRelation_flipBoundary_boundary (M : GeometricSideSubmap)
    (i : ℕ) (u v : GeometricSideCell M) :
    geometricSideRelation M.flipBoundary (.boundary i) u v ↔
      ∃ w : GeometricSideCell M,
        geometricSideRelation M (.boundary i) w v ∧
        geometricSideRelation M .opposite w u := by
  cases u with
  | inl a =>
    constructor
    · exact False.elim
    · rintro ⟨w, hb, ho⟩
      cases w <;> exact ho
  | inr d =>
    constructor
    · intro hb
      change ((M.boundary i).1, !(M.boundary i).2) = d.val at hb
      let w : {d : ℕ × Bool // d.1 ∈ M.edges} :=
        ⟨(d.val.1, !d.val.2), d.property⟩
      refine ⟨.inr w, ?_, ?_⟩
      · change M.boundary i = (d.val.1, !d.val.2)
        rw [← hb]
        simp only [Bool.not_not, Prod.eta]
      · change (d.val.1, !!d.val.2) = d.val
        simp only [Bool.not_not, Prod.eta]
    · rintro ⟨w, hb, ho⟩
      cases w with
      | inl a => exact False.elim hb
      | inr e =>
        change M.boundary i = e.val at hb
        change (e.val.1, !e.val.2) = d.val at ho
        change ((M.boundary i).1, !(M.boundary i).2) = d.val
        rw [hb]
        exact ho

/-- Helper toward Lemma 5.5: every non-boundary relation is unchanged. -/
theorem geometricSideRelation_flipBoundary_nonboundary (M : GeometricSideSubmap)
    (t : TruncationRelation) (ht : ∀ i, t ≠ .boundary i)
    (u v : GeometricSideCell M) :
    geometricSideRelation M.flipBoundary t u v ↔ geometricSideRelation M t u v := by
  cases t <;> cases u <;> cases v <;> first | rfl | exact (ht _ rfl).elim

/-- Helper toward Lemma 5.5: simultaneous reversal respects marked isomorphisms. -/
@[expose] def _root_.DirectedDistances.PaperProofs.Section4.GeometricSideMarkedIso.flipBoundary {M N : GeometricSideSubmap}
    (I : GeometricSideMarkedIso M N) :
    GeometricSideMarkedIso M.flipBoundary N.flipBoundary where
  equiv := I.equiv
  relation_iff := by
    change ∀ t (u v : GeometricSideCell M),
      geometricSideRelation M.flipBoundary t u v ↔
        geometricSideRelation N.flipBoundary t (I.equiv u) (I.equiv v)
    intro t u v
    cases t with
    | boundary i =>
      rw [geometricSideRelation_flipBoundary_boundary,
        geometricSideRelation_flipBoundary_boundary]
      constructor
      · rintro ⟨w, hb, ho⟩
        exact ⟨I.equiv w, (I.relation_iff (.boundary i) w v).mp hb,
          (I.relation_iff .opposite w u).mp ho⟩
      · rintro ⟨w, hb, ho⟩
        obtain ⟨w, rfl⟩ := I.equiv.surjective w
        exact ⟨w, (I.relation_iff (.boundary i) w v).mpr hb,
          (I.relation_iff .opposite w u).mpr ho⟩
    | vertex | root | target | incident | opposite | oriented | rotation | faceNext | seam _ =>
      rw [geometricSideRelation_flipBoundary_nonboundary M _ (by intros i he; cases he),
        geometricSideRelation_flipBoundary_nonboundary N _ (by intros i he; cases he)]
      exact I.relation_iff _ u v

/-- Helper toward Lemma 5.5: boundary reversal descends to marked classes. -/
@[expose] def GeometricSideClass.flipBoundary : GeometricSideClass → GeometricSideClass :=
  Quotient.map DirectedDistances.PaperProofs.Section4.GeometricSideSubmap.flipBoundary
    (fun _ _ h => h.elim fun I => ⟨I.flipBoundary⟩)

/-- Helper toward Lemma 5.5: boundary reversal is involutive on marked classes. -/
@[simp] theorem GeometricSideClass.flipBoundary_flipBoundary (c : GeometricSideClass) :
    c.flipBoundary.flipBoundary = c := by
  refine Quotient.inductionOn c ?_
  intro M
  change geometricSideClass M.flipBoundary.flipBoundary = geometricSideClass M
  rw [DirectedDistances.PaperProofs.Section4.GeometricSideSubmap.flipBoundary_flipBoundary]

/-- Helper toward Lemma 5.5: boundary reversal on the complete coordinate code. -/
@[expose] def geometricSideCodeFlipBoundary (c : GeometricSideCode) : GeometricSideCode :=
  (c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1,
    c.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.1,
    fun i => ((c.2.2.2.2.2.2.2.2.1 i).1, !(c.2.2.2.2.2.2.2.2.1 i).2),
    c.2.2.2.2.2.2.2.2.2)

/-- Helper toward Lemma 5.5: the coordinate reversal is measurable. -/
theorem measurable_geometricSideCodeFlipBoundary :
    Measurable geometricSideCodeFlipBoundary := by
  unfold geometricSideCodeFlipBoundary
  have hnot : Measurable Bool.not := measurable_of_countable _
  fun_prop

/-- Helper toward Lemma 5.5: boundary reversal is measurable for the
sigma-algebra generated by all geometric-side fields. -/
theorem measurable_geometricSideSubmap_flipBoundary :
    Measurable GeometricSideSubmap.flipBoundary := by
  apply measurable_comap_iff.mpr
  exact measurable_geometricSideCodeFlipBoundary.comp (comap_measurable geometricSideCode)

/-- Helper toward Lemma 5.5: boundary reversal is measurable on the quotient
sigma-algebra; no discreteness assumption is used. -/
theorem measurable_geometricSideClass_flipBoundary :
    Measurable GeometricSideClass.flipBoundary := by
  intro s hs
  change MeasurableSet (geometricSideClass ⁻¹' (GeometricSideClass.flipBoundary ⁻¹' s))
  exact (measurable_geometricSideClass.comp
    measurable_geometricSideSubmap_flipBoundary) hs

/-- Helper toward Lemma 5.5: the third decoder reverses its boundary marks only. -/
@[expose] noncomputable def lMinusDecodedSide3
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈
      selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
        renewalTime renewalTime_positiveSuccessTime)
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    GeometricSideSubmap :=
  (lMinusDecodedSide2 hτ hqMode hfin).flipBoundary

/-- Helper toward Lemma 5.5: reversing an oriented marked dart produces a
boundary dart whose opposite is oriented. -/
theorem flipBoundary_exists_boundary_opposite_oriented (M : GeometricSideSubmap)
    (i : ℕ) (u : GeometricSideCell M)
    (hb : geometricSideRelation M (.boundary i) u u)
    (ho : geometricSideRelation M .oriented u u) :
    ∃ a b : GeometricSideCell M.flipBoundary,
      geometricSideRelation M.flipBoundary (.boundary i) a a ∧
      geometricSideRelation M.flipBoundary .opposite a b ∧
      geometricSideRelation M.flipBoundary .oriented b b := by
  cases u with
  | inl u => exact False.elim hb
  | inr d =>
    let a : {d : ℕ × Bool // d.1 ∈ M.edges} :=
      ⟨(d.val.1, !d.val.2), d.property⟩
    refine ⟨.inr a, .inr d, ?_, ?_, ho⟩
    · change ((M.boundary i).1, !(M.boundary i).2) = (d.val.1, !d.val.2)
      change M.boundary i = d.val at hb
      rw [hb]
    · change (d.val.1, !!d.val.2) = d.val
      simp only [Bool.not_not, Prod.eta]

section Obstruction

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hk : k ≤ 0)

local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "D" => lMinusDecodedSide3 (W := W) (h := h) (k := k)
  (longest := longest) hτ hqMode hfin

include hk in
/-- Helper toward Lemma 5.5: neither dart of a negative exterior boundary
edge is oriented, since this edge is missing from the directed carrier. -/
theorem m0GeodesicSide_left_boundary_opposite_not_oriented
    (i : ℕ) (u v : GeometricSideCell S)
    (hb : geometricSideRelation S (.boundary i) u u)
    (ho : geometricSideRelation S .opposite u v) :
    ¬ geometricSideRelation S .oriented v v := by
  cases u with
  | inl a => exact False.elim hb
  | inr d =>
    cases v with
    | inl a => exact False.elim ho
    | inr e =>
      intro he
      have hb' : (boundaryOuterEdge (shiftedStream W 0) h (k - 1 - (i : ℤ)), true) =
          d.val := hb
      have ho' : (d.val.1, !d.val.2) = e.val := ho
      have he' : EdgePresent (shiftedStream W 0) e.val.1 ∧ e.val.2 = false := he
      have heid := congrArg Prod.fst ho'
      have hid : boundaryOuterEdge (shiftedStream W 0) h (k - 1 - (i : ℤ)) =
          e.val.1 := (congrArg Prod.fst hb').trans heid
      exact (boundaryOuterEdge_endpoints (shiftedStream W 0) h
        (k - 1 - (i : ℤ))).2.2.2 (by omega) (hid ▸ he'.1)

include hk in
/-- Helper toward Lemma 5.5: boundary reversal leaves the hatted interface
edge directed, unlike the actual missing exterior boundary edge. -/
theorem boundaryGluing_nonpos_left_not_markedIso_lMinusDecodedSide3 :
    ¬ Nonempty (GeometricSideMarkedIso S D) := by
  rintro ⟨phi⟩
  have hex : ∃ a b : GeometricSideCell D,
      geometricSideRelation D (.boundary 0) a a ∧
      geometricSideRelation D .opposite a b ∧
      geometricSideRelation D .oriented b b := by
    unfold lMinusDecodedSide3
    rw [lMinusDecodedSide2_eq_codeSide2]
    obtain ⟨u, hb, ho⟩ := lMinusCodeSide2_boundary_oriented hτ hqMode hfin 0
    exact flipBoundary_exists_boundary_opposite_oriented _ 0 u hb ho
  obtain ⟨a, b, hb, hop, hor⟩ := hex
  obtain ⟨a, rfl⟩ := phi.equiv.surjective a
  obtain ⟨b, rfl⟩ := phi.equiv.surjective b
  exact m0GeodesicSide_left_boundary_opposite_not_oriented hp P hk 0 a b
    ((phi.relation_iff (.boundary 0) a a).mpr hb)
    ((phi.relation_iff .opposite a b).mpr hop)
    ((phi.relation_iff .oriented b b).mpr hor)

end Obstruction

















































end DirectedDistances.PaperProofs.Section5

