/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusSideMeasurable5

/-! # Boundary compatibility for quotient transport

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The induced hatted dart map preserves the
complete indexed boundary dart, including its endpoint bit. -/
theorem rMinus_rightSideMarkedIso_dartMap_boundary
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q')) (i : ℕ) :
    (rMinus_rightSideMarkedIso_dartMap phi
      ⟨(rMinusCoherentRightSide x q).boundary i,
        rMinus_hatted_boundary_mem x q i⟩).val =
      (rMinusCoherentRightSide x q').boundary i := by
  have hcell := rMinus_rightSideMarkedIso_dartMap_cell phi
    ⟨(rMinusCoherentRightSide x q).boundary i,
      rMinus_hatted_boundary_mem x q i⟩
  rw [rMinus_rightSideMarkedIso_boundary_transport] at hcell
  have hsub := Sum.inr.inj hcell
  exact (congrArg
    (fun d : {z : ℕ × Bool // z.1 ∈ (rMinusCoherentRightSide x q').edges} => d.val)
    hsub).symm

/-- Helper toward Lemma 5.5. The induced hatted dart map preserves the
complete indexed seam dart, including its endpoint bit. -/
theorem rMinus_rightSideMarkedIso_dartMap_seam
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q')) (i : ℕ) :
    (rMinus_rightSideMarkedIso_dartMap phi
      ⟨(rMinusCoherentRightSide x q).seam i, by
        change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
          renewalTime_positiveSuccessTime .right q j
        rw [iUnion_geometricAncestorEdges]
        exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i⟩).val =
      (rMinusCoherentRightSide x q').seam i := by
  have hcell := rMinus_rightSideMarkedIso_dartMap_cell phi
    ⟨(rMinusCoherentRightSide x q).seam i, by
      change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
        renewalTime_positiveSuccessTime .right q j
      rw [iUnion_geometricAncestorEdges]
      exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i⟩
  rw [rMinus_rightSideMarkedIso_seam_transport] at hcell
  have hsub := Sum.inr.inj hcell
  exact (congrArg
    (fun d : {z : ℕ × Bool // z.1 ∈ (rMinusCoherentRightSide x q').edges} => d.val)
    hsub).symm

/-- Helper toward Lemma 5.5. The induced dart map sends darts with a common
geometric edge identity to darts with a common edge identity. -/
theorem rMinus_rightSideMarkedIso_dartMap_edge_eq
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (d e : {z : ℕ × Bool // z.1 ∈ M.edges}) (hde : d.val.1 = e.val.1) :
    (rMinus_rightSideMarkedIso_dartMap phi d).val.1 =
      (rMinus_rightSideMarkedIso_dartMap phi e).val.1 := by
  by_cases hbit : d.val.2 = e.val.2
  · have h : d = e := Subtype.ext (Prod.ext hde hbit)
    rw [h]
  · have hflip : d.val.2 = !e.val.2 := by
      cases hd : d.val.2 <;> cases he : e.val.2 <;> simp_all
    have hrel : geometricSideRelation M .opposite (.inr d) (.inr e) := by
      simp [geometricSideRelation, hde, hflip]
    have hrel' := (phi.relation_iff .opposite (.inr d) (.inr e)).mp hrel
    rw [rMinus_rightSideMarkedIso_dartMap_cell,
      rMinus_rightSideMarkedIso_dartMap_cell] at hrel'
    have hpair :
        ((rMinus_rightSideMarkedIso_dartMap phi d).val.1,
          !(rMinus_rightSideMarkedIso_dartMap phi d).val.2) =
        (rMinus_rightSideMarkedIso_dartMap phi e).val := by
      simpa only [geometricSideRelation] using hrel'
    change ((rMinus_rightSideMarkedIso_dartMap phi d).val.1,
        !(rMinus_rightSideMarkedIso_dartMap phi d).val.2) =
      ((rMinus_rightSideMarkedIso_dartMap phi e).val.1,
        (rMinus_rightSideMarkedIso_dartMap phi e).val.2) at hpair
    exact (Prod.mk.inj hpair).1

/-- Helper toward Lemma 5.5. The induced dart maps of a marked isomorphism
and its inverse compose to the identity. -/
theorem rMinus_rightSideMarkedIso_dartMap_symm_apply
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (d : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    rMinus_rightSideMarkedIso_dartMap (GeometricSideMarkedIso.symm phi)
      (rMinus_rightSideMarkedIso_dartMap phi d) = d := by
  have h := congrArg (GeometricSideMarkedIso.symm phi).equiv
    (rMinus_rightSideMarkedIso_dartMap_cell phi d)
  change phi.equiv.symm (phi.equiv (.inr d)) =
    phi.equiv.symm (.inr (rMinus_rightSideMarkedIso_dartMap phi d)) at h
  rw [phi.equiv.symm_apply_apply] at h
  change Sum.inr d = (GeometricSideMarkedIso.symm phi).equiv
    (.inr (rMinus_rightSideMarkedIso_dartMap phi d)) at h
  rw [rMinus_rightSideMarkedIso_dartMap_cell (GeometricSideMarkedIso.symm phi)] at h
  exact (Sum.inr.inj h).symm

/-- Helper toward Lemma 5.5. The induced hatted edge map forgets only the
endpoint bit of the image of the false dart. -/
noncomputable def rMinus_rightSideMarkedIso_edgeMap
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (e : M.edges) : N.edges :=
  let d : {z : ℕ × Bool // z.1 ∈ M.edges} := ⟨(e.val, false), e.property⟩
  ⟨(rMinus_rightSideMarkedIso_dartMap phi d).val.1,
    (rMinus_rightSideMarkedIso_dartMap phi d).property⟩

/-- Helper toward Lemma 5.5. The induced edge maps of a marked isomorphism
and its inverse compose to the identity on geometric edge identities. -/
theorem rMinus_rightSideMarkedIso_edgeMap_symm_apply
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (e : M.edges) :
    rMinus_rightSideMarkedIso_edgeMap (GeometricSideMarkedIso.symm phi)
      (rMinus_rightSideMarkedIso_edgeMap phi e) = e := by
  apply Subtype.ext
  let d : {z : ℕ × Bool // z.1 ∈ M.edges} := ⟨(e.val, false), e.property⟩
  let d' := rMinus_rightSideMarkedIso_dartMap phi d
  change (rMinus_rightSideMarkedIso_dartMap (GeometricSideMarkedIso.symm phi)
      ⟨(d'.val.1, false), d'.property⟩).val.1 = e.val
  have h := rMinus_rightSideMarkedIso_dartMap_edge_eq (GeometricSideMarkedIso.symm phi) d'
    ⟨(d'.val.1, false), d'.property⟩ rfl
  rw [rMinus_rightSideMarkedIso_dartMap_symm_apply] at h
  exact h.symm

/-- Helper toward Lemma 5.5. The hatted edge map is a bijection, with the
inverse induced by the inverse marked isomorphism. -/
noncomputable def rMinus_rightSideMarkedIso_edgeEquiv
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N) :
    M.edges ≃ N.edges where
  toFun := rMinus_rightSideMarkedIso_edgeMap phi
  invFun := rMinus_rightSideMarkedIso_edgeMap (GeometricSideMarkedIso.symm phi)
  left_inv := rMinus_rightSideMarkedIso_edgeMap_symm_apply phi
  right_inv := rMinus_rightSideMarkedIso_edgeMap_symm_apply
    (GeometricSideMarkedIso.symm phi)

/-- Helper toward Lemma 5.5. The induced hatted edge map preserves each
indexed boundary edge. -/
theorem rMinus_rightSideMarkedIso_edgeMap_boundary
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q')) (i : ℕ) :
    rMinus_rightSideMarkedIso_edgeMap phi
      ⟨((rMinusCoherentRightSide x q).boundary i).1,
        rMinus_hatted_boundary_mem x q i⟩ =
      ⟨((rMinusCoherentRightSide x q').boundary i).1,
        rMinus_hatted_boundary_mem x q' i⟩ := by
  apply Subtype.ext
  have h := rMinus_rightSideMarkedIso_dartMap_edge_eq phi
    ⟨(rMinusCoherentRightSide x q).boundary i,
      rMinus_hatted_boundary_mem x q i⟩
    ⟨(((rMinusCoherentRightSide x q).boundary i).1, false),
      rMinus_hatted_boundary_mem x q i⟩ rfl
  rw [rMinus_rightSideMarkedIso_dartMap_boundary] at h
  exact h.symm

/-- Helper toward Lemma 5.5. The induced hatted edge map preserves each
indexed seam edge. -/
theorem rMinus_rightSideMarkedIso_edgeMap_seam
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q')) (i : ℕ) :
    rMinus_rightSideMarkedIso_edgeMap phi
      ⟨((rMinusCoherentRightSide x q).seam i).1, by
        change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
          renewalTime_positiveSuccessTime .right q j
        rw [iUnion_geometricAncestorEdges]
        exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i⟩ =
      ⟨((rMinusCoherentRightSide x q').seam i).1, by
        change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
          renewalTime_positiveSuccessTime .right q' j
        rw [iUnion_geometricAncestorEdges]
        exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i⟩ := by
  apply Subtype.ext
  have h := rMinus_rightSideMarkedIso_dartMap_edge_eq phi
    ⟨(rMinusCoherentRightSide x q).seam i, by
      change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
        renewalTime_positiveSuccessTime .right q j
      rw [iUnion_geometricAncestorEdges]
      exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i⟩
    ⟨(((rMinusCoherentRightSide x q).seam i).1, false), by
      change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
        renewalTime_positiveSuccessTime .right q j
      rw [iUnion_geometricAncestorEdges]
      exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i⟩ rfl
  rw [rMinus_rightSideMarkedIso_dartMap_seam] at h
  exact h.symm

/-- Helper toward Lemma 5.5. Extend the induced hatted edge map by the
identity on finite-prefix edge representatives. -/
noncomputable def rMinus_rightSideMarkedIso_edgeRepMap
    (F : State) {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) :
    Sum {e : ℕ // e < F.nextEdge} M.edges →
      Sum {e : ℕ // e < F.nextEdge} N.edges
  | .inl e => .inl e
  | .inr e => .inr (rMinus_rightSideMarkedIso_edgeMap phi e)

/-- Helper toward Lemma 5.5. The representative map is bijective, fixing
the finite-prefix block and using the hatted edge equivalence. -/
noncomputable def rMinus_rightSideMarkedIso_edgeRepEquiv
    (F : State) {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) :
    Sum {e : ℕ // e < F.nextEdge} M.edges ≃
      Sum {e : ℕ // e < F.nextEdge} N.edges :=
  Equiv.sumCongr (Equiv.refl _) (rMinus_rightSideMarkedIso_edgeEquiv phi)

/-- Helper toward Lemma 5.5. The induced hatted edge map sends each shared
prefix/boundary generator to the same indexed generator. -/
theorem rMinus_rightSideMarkedIso_edgeGluing
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (a b : Sum {e : ℕ // e < F.nextEdge}
      (rMinusCoherentRightSide x q).edges)
    (hab : rMinusCodeEdgeGluing F (rMinusCoherentRightSide x q) a b) :
    rMinusCodeEdgeGluing F (rMinusCoherentRightSide x q')
      (rMinus_rightSideMarkedIso_edgeRepMap F phi a)
      (rMinus_rightSideMarkedIso_edgeRepMap F phi b) := by
  cases a with
  | inl a =>
    cases b with
    | inl b => simp [rMinusCodeEdgeGluing] at hab
    | inr b =>
      rcases hab with ⟨i, hi, hb⟩
      refine ⟨i, hi, ?_⟩
      have hsub : b = ⟨((rMinusCoherentRightSide x q).boundary i).1,
          rMinus_hatted_boundary_mem x q i⟩ := Subtype.ext hb.symm
      rw [hsub, rMinus_rightSideMarkedIso_edgeMap_boundary]
  | inr a =>
    cases b <;>
      simp [rMinusCodeEdgeGluing] at hab

/-- Helper toward Lemma 5.5. The induced representative map respects the
entire generated edge equivalence, not only its named generators. -/
theorem rMinus_rightSideMarkedIso_edgeSetoid
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (a b : Sum {e : ℕ // e < F.nextEdge}
      (rMinusCoherentRightSide x q).edges)
    (hab : rMinusCodeEdgeSetoid F (rMinusCoherentRightSide x q) a b) :
    rMinusCodeEdgeSetoid F (rMinusCoherentRightSide x q')
      (rMinus_rightSideMarkedIso_edgeRepMap F phi a)
      (rMinus_rightSideMarkedIso_edgeRepMap F phi b) := by
  change Relation.EqvGen
    (rMinusCodeEdgeGluing F (rMinusCoherentRightSide x q)) a b at hab
  change Relation.EqvGen
    (rMinusCodeEdgeGluing F (rMinusCoherentRightSide x q'))
      (rMinus_rightSideMarkedIso_edgeRepMap F phi a)
      (rMinus_rightSideMarkedIso_edgeRepMap F phi b)
  induction hab with
  | rel a b hab =>
      exact Relation.EqvGen.rel _ _
        (rMinus_rightSideMarkedIso_edgeGluing x q q' phi F a b hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab₁ hab₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Helper toward Lemma 5.5. The induced map on edge representatives
descends to the intrinsic glued-edge quotients. -/
noncomputable def rMinus_rightSideMarkedIso_codeEdgeQuotMap
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) :
    RMinusCodeGluedEdge F (rMinusCoherentRightSide x q) →
      RMinusCodeGluedEdge F (rMinusCoherentRightSide x q') :=
  Quotient.map (rMinus_rightSideMarkedIso_edgeRepMap F phi)
    (fun _ _ hab => rMinus_rightSideMarkedIso_edgeSetoid x q q' phi F _ _ hab)

/-- Helper toward Lemma 5.5. The inverse hatted edge action inverts the
induced map on the glued-edge quotient. -/
theorem rMinus_rightSideMarkedIso_codeEdgeQuotMap_symm
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (e : RMinusCodeGluedEdge F (rMinusCoherentRightSide x q)) :
    rMinus_rightSideMarkedIso_codeEdgeQuotMap x q' q
      (GeometricSideMarkedIso.symm phi) F
      (rMinus_rightSideMarkedIso_codeEdgeQuotMap x q q' phi F e) = e := by
  refine Quotient.inductionOn e ?_
  intro a
  cases a with
  | inl a => rfl
  | inr a =>
      change (⟦Sum.inr (rMinus_rightSideMarkedIso_edgeMap
        (GeometricSideMarkedIso.symm phi)
        (rMinus_rightSideMarkedIso_edgeMap phi a))⟧ :
          RMinusCodeGluedEdge F (rMinusCoherentRightSide x q)) = ⟦Sum.inr a⟧
      rw [rMinus_rightSideMarkedIso_edgeMap_symm_apply]

/-- Helper toward Lemma 5.5. The marked hatted isomorphism induces an
equivalence of the two finite-prefix/hatted edge quotients. -/
noncomputable def rMinus_rightSideMarkedIso_codeEdgeQuotEquiv
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) :
    RMinusCodeGluedEdge F (rMinusCoherentRightSide x q) ≃
      RMinusCodeGluedEdge F (rMinusCoherentRightSide x q') where
  toFun := rMinus_rightSideMarkedIso_codeEdgeQuotMap x q q' phi F
  invFun := rMinus_rightSideMarkedIso_codeEdgeQuotMap x q' q
    (GeometricSideMarkedIso.symm phi) F
  left_inv := rMinus_rightSideMarkedIso_codeEdgeQuotMap_symm x q q' phi F
  right_inv := rMinus_rightSideMarkedIso_codeEdgeQuotMap_symm x q' q
    (GeometricSideMarkedIso.symm phi) F

























end DirectedDistances.PaperProofs.Section5
