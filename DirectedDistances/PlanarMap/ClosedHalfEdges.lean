/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfMap
public import DirectedDistances.PlanarMap.PlanarPathCutHalves

public section
namespace DirectedDistances.PlanarMap

/-- Edge orbits of a closed half are exactly the original edge orbits whose
darts all lie in the carrier. Helper toward `lem-lr-ind` -/
private noncomputable def closedHalfEdgeQuotientEquiv {D : Type*} [Fintype D]
    [DecidableEq D] (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S) :
    CombinatorialMap.EdgeQuotient (closedHalfCombinatorialMap B S hclosed) ≃
      {q : CombinatorialMap.EdgeQuotient B.toCombinatorialMap //
        ∀ d : D, edgeClass B.toCombinatorialMap d = q → d ∈ S} := by
  classical
  let M := B.toCombinatorialMap
  let H := closedHalfCombinatorialMap B S hclosed
  have hHval (x : {d : D // d ∈ S}) : (H.edgeInv x).1 = M.edgeInv x.1 := by
    rfl
  let f : CombinatorialMap.EdgeQuotient H →
      {q : CombinatorialMap.EdgeQuotient M //
        ∀ d : D, edgeClass M d = q → d ∈ S} :=
    Quotient.lift
      (fun x : {d : D // d ∈ S} =>
        ⟨edgeClass M x.1, by
          intro d hd
          have hrel : M.edgeInv.SameCycle x.1 d := Quotient.exact hd.symm
          rcases (CombinatorialMap.edgeInv_sameCycle_iff M x.1 d).mp hrel with hxd | hxd
          · simp [hxd]
          · simpa [hxd] using hclosed x.1 x.2⟩)
      (by
        intro x y hxy
        rcases (CombinatorialMap.edgeInv_sameCycle_iff H x y).mp hxy with hxy | hxy
        · subst y
          rfl
        · subst y
          apply Subtype.ext
          change edgeClass M x.1 = edgeClass M (H.edgeInv x).1
          rw [hHval]
          apply Quotient.sound
          exact ⟨1, rfl⟩)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro q r h
    revert h
    refine Quotient.inductionOn₂ q r ?_
    intro x y hxy
    apply Quotient.sound
    have hbase : edgeClass M x.1 = edgeClass M y.1 := congrArg Subtype.val hxy
    have hrel : M.edgeInv.SameCycle x.1 y.1 := Quotient.exact hbase
    rcases (CombinatorialMap.edgeInv_sameCycle_iff M x.1 y.1).mp hrel with hxy | hxy
    · have hsub : x = y := Subtype.ext hxy.symm
      subst y
      exact Equiv.Perm.SameCycle.rfl
    · have hy : y = H.edgeInv x := Subtype.ext (hxy.trans (hHval x).symm)
      rw [hy]
      exact ⟨1, rfl⟩
  · intro q
    rcases q with ⟨q, hq⟩
    obtain ⟨d, rfl⟩ := Quotient.exists_rep q
    refine ⟨Quotient.mk _ ⟨d, hq d rfl⟩, ?_⟩
    apply Subtype.ext
    rfl

private theorem finset_univ_filter_card_eq {α : Type*} (p : α → Prop)
    (F₁ F₂ : Fintype α) (d₁ d₂ : DecidablePred p) :
    (@Finset.filter α p d₁ (@Finset.univ α F₁)).card =
      (@Finset.filter α p d₂ (@Finset.univ α F₂)).card := by
  congr 1
  ext x
  simp

/-- The number of edges of a closed half is the number of original edge
orbits all of whose darts lie in its carrier. Helper toward `lem-lr-ind` -/
theorem closedHalf_numEdges_eq_card_closedEdges {D : Type*} [Fintype D]
    [DecidableEq D] (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S)
    [DecidableRel (Equiv.Perm.SameCycle B.toCombinatorialMap.edgeInv)]
    [Fintype (CombinatorialMap.EdgeQuotient B.toCombinatorialMap)]
    [DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.toCombinatorialMap => ∀ d : D,
        edgeClass B.toCombinatorialMap d = q → d ∈ S)] :
    (closedHalfCombinatorialMap B S hclosed).numEdges =
      Fintype.card {q : CombinatorialMap.EdgeQuotient B.toCombinatorialMap //
        ∀ d : D, edgeClass B.toCombinatorialMap d = q → d ∈ S} := by
  classical
  exact Fintype.card_congr (closedHalfEdgeQuotientEquiv B S hclosed)

/-- An edge-invariant dart carrier has one edge for every pair of its darts.
paper result. -/
theorem closedHalf_numEdges_eq_card_div_two {D : Type*} [Fintype D]
    [DecidableEq D] (B : DirectedMapWithMissing D) (S : Set D)
    [DecidablePred (fun d : D => d ∈ S)]
    (hclosed : ∀ d : D, d ∈ S → B.edgeInv d ∈ S) :
    (closedHalfCombinatorialMap B S hclosed).numEdges =
      Fintype.card {d : D // d ∈ S} / 2 := by
  have h := CombinatorialMap.two_mul_numEdges
    (closedHalfCombinatorialMap B S hclosed)
  omega

/-- Membership in the left half's edge set is equivalent to every dart in
that original edge orbit lying in the left half. Helper toward `lem-lr-ind` -/
theorem pathCutLeftHalfEdges_allDarts_iff {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) :
    q ∈ pathCutLeftHalfEdges B P ↔
      ∀ d : D, edgeClass B.map.toCombinatorialMap d = q →
        d ∈ pathCutLeftHalfDarts B P := by
  classical
  constructor
  · rintro ⟨e, he, hEq⟩ d hd
    have hrel : B.map.toCombinatorialMap.edgeInv.SameCycle e d :=
      Quotient.exact (hEq.trans hd.symm)
    rcases (CombinatorialMap.edgeInv_sameCycle_iff
      B.map.toCombinatorialMap e d).mp hrel with hde | hde
    · simpa [hde] using he
    · simpa [hde] using pathCutLeftHalf_edgeInv_mem B P he
  · intro hall
    refine ⟨Quotient.out q, hall _ (Quotient.out_eq' q), Quotient.out_eq' q⟩

/-- The left half-map edge count is the cardinality of the original edge
orbits represented by the closed left half (helper toward `lem-lr-ind`, -/
theorem pathCutLeftHalfMap_numEdges_eq_card_edges {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [leftHalfDartsDecidable :
      DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [edgeInvSameCycleDecidable :
      DecidableRel (Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv)]
    [edgeQuotientFintype :
      Fintype (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap)]
    [leftAllDartsDecidable : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => ∀ d : D,
        edgeClass B.map.toCombinatorialMap d = q →
          d ∈ pathCutLeftHalfDarts B P)]
    [leftHalfEdgesDecidable : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => q ∈ pathCutLeftHalfEdges B P)] :
    (pathCutLeftHalfMap B P).numEdges =
      Fintype.card {q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
        q ∈ pathCutLeftHalfEdges B P} := by
  have hclosed : ∀ d : D, d ∈ pathCutLeftHalfDarts B P →
      B.map.toCombinatorialMap.edgeInv d ∈ pathCutLeftHalfDarts B P :=
    fun d hd => pathCutLeftHalf_edgeInv_mem B P hd
  have hgeneric := closedHalf_numEdges_eq_card_closedEdges
    B.map (pathCutLeftHalfDarts B P) hclosed
  let e : {q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
      q ∈ pathCutLeftHalfEdges B P} ≃
    {q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
      ∀ d : D, edgeClass B.map.toCombinatorialMap d = q →
        d ∈ pathCutLeftHalfDarts B P} := {
    toFun := fun q => ⟨q.1,
      (pathCutLeftHalfEdges_allDarts_iff B P q.1).mp q.2⟩
    invFun := fun q => ⟨q.1,
      (pathCutLeftHalfEdges_allDarts_iff B P q.1).mpr q.2⟩
    left_inv := by intro q; cases q; rfl
    right_inv := by intro q; cases q; rfl }
  calc
    (pathCutLeftHalfMap B P).numEdges =
        Fintype.card {q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
          ∀ d : D, edgeClass B.map.toCombinatorialMap d = q →
            d ∈ pathCutLeftHalfDarts B P} := by
      simpa [pathCutLeftHalfMap] using hgeneric
    _ = Fintype.card {q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
        q ∈ pathCutLeftHalfEdges B P} := (Fintype.card_congr e).symm

/-- Membership in the right half's edge set is equivalent to every dart in
that original edge orbit lying in the right half. Helper toward `lem-lr-ind` -/
theorem pathCutRightHalfEdges_allDarts_iff {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) :
    q ∈ pathCutRightHalfEdges B P ↔
      ∀ d : D, edgeClass B.map.toCombinatorialMap d = q →
        d ∈ pathCutRightHalfDarts B P := by
  classical
  constructor
  · rintro ⟨e, he, hEq⟩ d hd
    have hrel : B.map.toCombinatorialMap.edgeInv.SameCycle e d :=
      Quotient.exact (hEq.trans hd.symm)
    rcases (CombinatorialMap.edgeInv_sameCycle_iff
      B.map.toCombinatorialMap e d).mp hrel with hde | hde
    · simpa [hde] using he
    · simpa [hde] using pathCutRightHalf_edgeInv_mem B P he
  · intro hall
    refine ⟨Quotient.out q, hall _ (Quotient.out_eq' q), Quotient.out_eq' q⟩

/-- The right half-map edge count is the cardinality of the original edge
orbits represented by the closed right half (helper toward `lem-lr-ind`, -/
theorem pathCutRightHalfMap_numEdges_eq_card_edges {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [rightHalfDartsDecidable :
      DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [edgeInvSameCycleDecidable :
      DecidableRel (Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv)]
    [edgeQuotientFintype :
      Fintype (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap)]
    [rightAllDartsDecidable : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => ∀ d : D,
        edgeClass B.map.toCombinatorialMap d = q →
          d ∈ pathCutRightHalfDarts B P)]
    [rightHalfEdgesDecidable : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => q ∈ pathCutRightHalfEdges B P)] :
    (pathCutRightHalfMap B P).numEdges =
      Fintype.card {q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
        q ∈ pathCutRightHalfEdges B P} := by
  have hclosed : ∀ d : D, d ∈ pathCutRightHalfDarts B P →
      B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightHalfDarts B P :=
    fun d hd => pathCutRightHalf_edgeInv_mem B P hd
  have hgeneric := closedHalf_numEdges_eq_card_closedEdges
    B.map (pathCutRightHalfDarts B P) hclosed
  let e : {q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
      q ∈ pathCutRightHalfEdges B P} ≃
    {q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
      ∀ d : D, edgeClass B.map.toCombinatorialMap d = q →
        d ∈ pathCutRightHalfDarts B P} := {
    toFun := fun q => ⟨q.1,
      (pathCutRightHalfEdges_allDarts_iff B P q.1).mp q.2⟩
    invFun := fun q => ⟨q.1,
      (pathCutRightHalfEdges_allDarts_iff B P q.1).mpr q.2⟩
    left_inv := by intro q; cases q; rfl
    right_inv := by intro q; cases q; rfl }
  calc
    (pathCutRightHalfMap B P).numEdges =
        Fintype.card {q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
          ∀ d : D, edgeClass B.map.toCombinatorialMap d = q →
            d ∈ pathCutRightHalfDarts B P} := by
      simpa [pathCutRightHalfMap] using hgeneric
    _ = Fintype.card {q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
        q ∈ pathCutRightHalfEdges B P} := (Fintype.card_congr e).symm

/-- The two closed half-map edge counts sum to the original map's edge count
plus the path length. Helper toward `lem-lr-ind` -/
theorem pathCutHalfMaps_numEdges_sum {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [leftHalfDartsDecidable :
      DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    [rightHalfDartsDecidable :
      DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    [edgeInvSameCycleDecidable :
      DecidableRel (Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv)]
    [edgeQuotientFintype :
      Fintype (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap)]
    [leftAllDartsDecidable : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => ∀ d : D,
        edgeClass B.map.toCombinatorialMap d = q →
          d ∈ pathCutLeftHalfDarts B P)]
    [rightAllDartsDecidable : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => ∀ d : D,
        edgeClass B.map.toCombinatorialMap d = q →
          d ∈ pathCutRightHalfDarts B P)]
    [leftHalfEdgesDecidable : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => q ∈ pathCutLeftHalfEdges B P)]
    [rightHalfEdgesDecidable : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => q ∈ pathCutRightHalfEdges B P)] :
    (pathCutLeftHalfMap B P).numEdges + (pathCutRightHalfMap B P).numEdges =
      B.map.toCombinatorialMap.numEdges + n := by
  have hleft := pathCutLeftHalfMap_numEdges_eq_card_edges B P
  have hright := pathCutRightHalfMap_numEdges_eq_card_edges B P
  let Q := CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap
  let leftPred : Q → Prop := fun q => q ∈ pathCutLeftHalfEdges B P
  let rightPred : Q → Prop := fun q => q ∈ pathCutRightHalfEdges B P
  have hleftFilter := finset_univ_filter_card_eq leftPred
    (inferInstance : Fintype Q)
    (by
      letI : DecidableRel
          (Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv) := Classical.decRel _
      exact Quotient.fintype _)
    (inferInstance : DecidablePred leftPred) (Classical.decPred _)
  have hrightFilter := finset_univ_filter_card_eq rightPred
    (inferInstance : Fintype Q)
    (by
      letI : DecidableRel
          (Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv) := Classical.decRel _
      exact Quotient.fintype _)
    (inferInstance : DecidablePred rightPred) (Classical.decPred _)
  have hsum := pathCutHalves_edge_card_sum B P
  calc
    (pathCutLeftHalfMap B P).numEdges + (pathCutRightHalfMap B P).numEdges =
        Fintype.card {q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
            q ∈ pathCutLeftHalfEdges B P} +
          Fintype.card {q : CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap //
            q ∈ pathCutRightHalfEdges B P} := by
      exact congrArg₂ Nat.add hleft hright
    _ = (Finset.univ.filter (fun q : CombinatorialMap.EdgeQuotient
          B.map.toCombinatorialMap => q ∈ pathCutLeftHalfEdges B P)).card +
        (Finset.univ.filter (fun q : CombinatorialMap.EdgeQuotient
          B.map.toCombinatorialMap => q ∈ pathCutRightHalfEdges B P)).card := by
      rw [Fintype.card_subtype, Fintype.card_subtype]
    _ = (@Finset.filter Q leftPred (Classical.decPred _)
          (@Finset.univ Q (by
            letI : DecidableRel
                (Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv) := Classical.decRel _
            exact Quotient.fintype _))).card +
        (@Finset.filter Q rightPred (Classical.decPred _)
          (@Finset.univ Q (by
            letI : DecidableRel
                (Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv) := Classical.decRel _
            exact Quotient.fintype _))).card := by
      exact congrArg₂ Nat.add
        (by simp [Q, leftPred] at hleftFilter ⊢; exact hleftFilter)
        (by simp [Q, rightPred] at hrightFilter ⊢; exact hrightFilter)
    _ = B.map.toCombinatorialMap.numEdges + n := hsum

/-- The edge-sum helper specializes to classical instances. Helper toward -/
theorem pathCutHalfMaps_numEdges_sum_classical {D : Type*} [Fintype D]
    [DecidableEq D] {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    letI : DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P) :=
      Classical.decPred _
    letI : DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P) :=
      Classical.decPred _
    letI : DecidableRel (Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv) :=
      Classical.decRel _
    letI : Fintype (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) :=
      Quotient.fintype _
    letI : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => ∀ d : D,
        edgeClass B.map.toCombinatorialMap d = q →
          d ∈ pathCutLeftHalfDarts B P) := Classical.decPred _
    letI : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => ∀ d : D,
        edgeClass B.map.toCombinatorialMap d = q →
          d ∈ pathCutRightHalfDarts B P) := Classical.decPred _
    letI : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => q ∈ pathCutLeftHalfEdges B P) := Classical.decPred _
    letI : DecidablePred (fun q : CombinatorialMap.EdgeQuotient
      B.map.toCombinatorialMap => q ∈ pathCutRightHalfEdges B P) := Classical.decPred _
    (pathCutLeftHalfMap B P).numEdges + (pathCutRightHalfMap B P).numEdges =
      B.map.toCombinatorialMap.numEdges + n := by
  classical
  exact pathCutHalfMaps_numEdges_sum B P

end DirectedDistances.PlanarMap
