/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusSideMeasurable4

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The hatted left block at the common mode. -/
noncomputable abbrev lMinusCoherentLeftSide (x : XDP) (q : Coherent x) :=
  geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q

/-- Helper toward Lemma 5.5. Choose the already proved hatted isomorphism;
no isomorphism is an additional premise on the preimages. -/
@[expose] noncomputable def lMinusPreimageHattedIso {x : XDP}
    (q q' : LMinusPreimage x) (hc : lMinusCodeOf q = lMinusCodeOf q') :
    GeometricSideMarkedIso (lMinusCoherentLeftSide x q.hattedCoherent)
      (lMinusCoherentLeftSide x q'.hattedCoherent) :=
  (lMinusPreimage_hatted_markedIso_of_code_eq q q' hc).some

/-- Helper toward Lemma 5.5. Restrict a marked isomorphism to vertices. -/
theorem lMinus_markedIso_vertex_exists {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (v : M.vertices) :
    ∃ w : N.vertices, phi.equiv (.inl v) = .inl w := by
  cases h : phi.equiv (.inl v) with
  | inl w => exact ⟨w, rfl⟩
  | inr d =>
    have hv := (phi.relation_iff .vertex (.inl v) (.inl v)).mp (by
      simp only [geometricSideRelation])
    simp only [h, geometricSideRelation] at hv

/-- Helper toward Lemma 5.5. The vertex action of a marked isomorphism. -/
@[expose] noncomputable def lMinusMarkedVertexMap {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (v : M.vertices) : N.vertices :=
  (lMinus_markedIso_vertex_exists phi v).choose

/-- Helper toward Lemma 5.5. The vertex action agrees with the cell action. -/
theorem lMinusMarkedVertexMap_cell {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (v : M.vertices) :
    phi.equiv (.inl v) = .inl (lMinusMarkedVertexMap phi v) :=
  (lMinus_markedIso_vertex_exists phi v).choose_spec

/-- Helper toward Lemma 5.5. Restrict a marked isomorphism to darts. -/
theorem lMinus_markedIso_dart_exists {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (d : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    ∃ e : {z : ℕ × Bool // z.1 ∈ N.edges}, phi.equiv (.inr d) = .inr e := by
  cases h : phi.equiv (.inr d) with
  | inl v =>
    have hd := (phi.relation_iff .vertex (.inr d) (.inr d)).mpr (by
      simp only [h, geometricSideRelation])
    simp only [geometricSideRelation] at hd
  | inr e => exact ⟨e, rfl⟩

/-- Helper toward Lemma 5.5. The dart action of a marked isomorphism. -/
@[expose] noncomputable def lMinusMarkedDartMap {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (d : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    {z : ℕ × Bool // z.1 ∈ N.edges} :=
  (lMinus_markedIso_dart_exists phi d).choose

/-- Helper toward Lemma 5.5. The dart action agrees with the cell action. -/
theorem lMinusMarkedDartMap_cell {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (d : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    phi.equiv (.inr d) = .inr (lMinusMarkedDartMap phi d) :=
  (lMinus_markedIso_dart_exists phi d).choose_spec

/-- Helper toward Lemma 5.5. The induced vertex action has the inverse action. -/
theorem lMinusMarkedVertexMap_symm {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (v : M.vertices) :
    lMinusMarkedVertexMap (GeometricSideMarkedIso.symm phi) (lMinusMarkedVertexMap phi v) = v := by
  apply Sum.inl_injective
  rw [← lMinusMarkedVertexMap_cell, ← lMinusMarkedVertexMap_cell]
  exact phi.equiv.symm_apply_apply (.inl v)

/-- Helper toward Lemma 5.5. The induced dart action has the inverse action. -/
theorem lMinusMarkedDartMap_symm {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (d : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    lMinusMarkedDartMap (GeometricSideMarkedIso.symm phi) (lMinusMarkedDartMap phi d) = d := by
  apply Sum.inr_injective
  rw [← lMinusMarkedDartMap_cell, ← lMinusMarkedDartMap_cell]
  exact phi.equiv.symm_apply_apply (.inr d)

/-- Helper toward Lemma 5.5. The induced vertex bijection. -/
@[expose] noncomputable def lMinusMarkedVertexEquiv {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) : M.vertices ≃ N.vertices where
  toFun := lMinusMarkedVertexMap phi
  invFun := lMinusMarkedVertexMap (GeometricSideMarkedIso.symm phi)
  left_inv := lMinusMarkedVertexMap_symm phi
  right_inv := lMinusMarkedVertexMap_symm (GeometricSideMarkedIso.symm phi)

/-- Helper toward Lemma 5.5. The induced dart bijection, retaining opposite darts. -/
@[expose] noncomputable def lMinusMarkedDartEquiv {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) :
    {z : ℕ × Bool // z.1 ∈ M.edges} ≃ {z : ℕ × Bool // z.1 ∈ N.edges} where
  toFun := lMinusMarkedDartMap phi
  invFun := lMinusMarkedDartMap (GeometricSideMarkedIso.symm phi)
  left_inv := lMinusMarkedDartMap_symm phi
  right_inv := lMinusMarkedDartMap_symm (GeometricSideMarkedIso.symm phi)

/-- Helper toward Lemma 5.5. Indexed boundary darts are preserved. -/
theorem lMinus_markedIso_boundary (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (i : ℕ) :
    lMinusMarkedDartMap phi ⟨(lMinusCoherentLeftSide x q).boundary i,
      lMinus_hatted_boundary_mem x q i⟩ =
    ⟨(lMinusCoherentLeftSide x q').boundary i,
      lMinus_hatted_boundary_mem x q' i⟩ := by
  have h := (phi.relation_iff (.boundary i)
    (.inr ⟨_, lMinus_hatted_boundary_mem x q i⟩)
    (.inr ⟨_, lMinus_hatted_boundary_mem x q i⟩)).mp
      (show geometricSideRelation _ (.boundary i) _ _ from rfl)
  rw [lMinusMarkedDartMap_cell] at h
  exact Subtype.ext h.symm

/-- Helper toward Lemma 5.5. Indexed seam darts belong to the left block. -/
theorem lMinus_hatted_seam_mem (x : XDP) (q : Coherent x) (i : ℕ) :
    ((lMinusCoherentLeftSide x q).seam i).1 ∈ (lMinusCoherentLeftSide x q).edges := by
  change _ ∈ ⋃ j, geometricAncestorEdges x renewalTime
    renewalTime_positiveSuccessTime .left q j
  rw [iUnion_geometricAncestorEdges]
  exact seamEdge_mem_sideEdges _ _ _ _ _ _ .left i

/-- Helper toward Lemma 5.5. Indexed seam darts are preserved. -/
theorem lMinus_markedIso_seam (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (i : ℕ) :
    lMinusMarkedDartMap phi ⟨(lMinusCoherentLeftSide x q).seam i,
      lMinus_hatted_seam_mem x q i⟩ =
    ⟨(lMinusCoherentLeftSide x q').seam i,
      lMinus_hatted_seam_mem x q' i⟩ := by
  have h := (phi.relation_iff (.seam i)
    (.inr ⟨_, lMinus_hatted_seam_mem x q i⟩)
    (.inr ⟨_, lMinus_hatted_seam_mem x q i⟩)).mp
      (show geometricSideRelation _ (.seam i) _ _ from rfl)
  rw [lMinusMarkedDartMap_cell] at h
  exact Subtype.ext h.symm

/-- Helper toward Lemma 5.5. Opposite darts are transported as opposite darts. -/
theorem lMinusMarkedDartMap_opposite {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (d : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    (lMinusMarkedDartMap phi ⟨(d.val.1, !d.val.2), d.property⟩).val =
      ((lMinusMarkedDartMap phi d).val.1, !(lMinusMarkedDartMap phi d).val.2) := by
  have h := (phi.relation_iff .opposite (.inr d)
    (.inr ⟨(d.val.1, !d.val.2), d.property⟩)).mp
      (show geometricSideRelation _ .opposite _ _ from rfl)
  simp only [lMinusMarkedDartMap_cell, geometricSideRelation] at h
  exact h.symm

/-- Helper toward Lemma 5.5. Both endpoint bits of an indexed boundary edge
are preserved, including the bit not selected by the boundary tag. -/
theorem lMinus_markedIso_boundary_bit (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (i : ℕ) (s : Bool) :
    lMinusMarkedDartMap phi ⟨(((lMinusCoherentLeftSide x q).boundary i).1, s),
      lMinus_hatted_boundary_mem x q i⟩ =
    ⟨(((lMinusCoherentLeftSide x q').boundary i).1, s),
      lMinus_hatted_boundary_mem x q' i⟩ := by
  have hb := lMinus_markedIso_boundary x q q' phi i
  have hfalse : lMinusMarkedDartMap phi
      ⟨(((lMinusCoherentLeftSide x q).boundary i).1, false),
        lMinus_hatted_boundary_mem x q i⟩ =
      ⟨(((lMinusCoherentLeftSide x q').boundary i).1, false),
        lMinus_hatted_boundary_mem x q' i⟩ := hb
  cases s with
  | false => exact hfalse
  | true =>
    apply Subtype.ext
    have ho := lMinusMarkedDartMap_opposite phi
      ⟨(((lMinusCoherentLeftSide x q).boundary i).1, false),
        lMinus_hatted_boundary_mem x q i⟩
    rw [hfalse] at ho
    exact ho

/-- Helper toward Lemma 5.5. Extend the vertex action by the identity on
labels outside the geometric vertex carrier; only allocated labels are used
by the glued vertex carrier. -/
@[expose] noncomputable def lMinusMarkedVertexLabelMap {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (v : ℕ) : ℕ :=
  if hv : v ∈ M.vertices then (lMinusMarkedVertexMap phi ⟨v, hv⟩).val else v

/-- Helper toward Lemma 5.5. On allocated labels the extension is the vertex action. -/
theorem lMinusMarkedVertexLabelMap_mem {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (v : M.vertices) :
    lMinusMarkedVertexLabelMap phi v.val = (lMinusMarkedVertexMap phi v).val := by
  simp only [lMinusMarkedVertexLabelMap, dite_eq_left v.property]

/-- Helper toward Lemma 5.5. The hatted vertex map preserves both endpoints
of each shared boundary edge. -/
theorem lMinus_markedIso_boundary_endpoint (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (i : ℕ) (s : Bool) :
    lMinusMarkedVertexLabelMap phi
      (if s then (lMinusCoherentLeftSide x q).east
        ((lMinusCoherentLeftSide x q).boundary i).1
       else (lMinusCoherentLeftSide x q).west
        ((lMinusCoherentLeftSide x q).boundary i).1) =
      (if s then (lMinusCoherentLeftSide x q').east
        ((lMinusCoherentLeftSide x q').boundary i).1
       else (lMinusCoherentLeftSide x q').west
        ((lMinusCoherentLeftSide x q').boundary i).1) := by
  let M := lMinusCoherentLeftSide x q
  let N := lMinusCoherentLeftSide x q'
  have he := geometricSideSubmap_endpoints x renewalTime
    renewalTime_positiveSuccessTime .left q _ (lMinus_hatted_boundary_mem x q i)
  have hv : (if s then M.east (M.boundary i).1 else M.west (M.boundary i).1) ∈
      M.vertices := by cases s with
    | false => exact he.1
    | true => exact he.2
  let v : M.vertices := ⟨_, hv⟩
  let d : {z : ℕ × Bool // z.1 ∈ M.edges} :=
    ⟨((M.boundary i).1, s), lMinus_hatted_boundary_mem x q i⟩
  have h := (phi.relation_iff .incident (.inr d) (.inl v)).mp
    (show geometricSideRelation _ .incident _ _ from rfl)
  rw [lMinusMarkedDartMap_cell, lMinusMarkedVertexMap_cell] at h
  change (if (lMinusMarkedDartMap phi d).val.2 then
    N.east (lMinusMarkedDartMap phi d).val.1 else
    N.west (lMinusMarkedDartMap phi d).val.1) =
      (lMinusMarkedVertexMap phi v).val at h
  have hd := lMinus_markedIso_boundary_bit x q q' phi i s
  change lMinusMarkedDartMap phi d = _ at hd
  rw [hd] at h
  exact (lMinusMarkedVertexLabelMap_mem phi v).trans h.symm

/-- Helper toward Lemma 5.5. The primed representative is fixed and the
hatted representative is mapped by the hatted vertex action. -/
@[expose] noncomputable def lMinusCodeVertexRepMap {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) : Sum ℕ ℕ → Sum ℕ ℕ :=
  Sum.map id (lMinusMarkedVertexLabelMap phi)

/-- Helper toward Lemma 5.5. Boundary endpoint gluing generators are
preserved, with the same primed presentation on both sides. -/
theorem lMinusCodeVertexRepMap_gluing (x : XDP) (r : LMinusSidePresentation x)
    (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (u v : Sum ℕ ℕ)
    (huv : lMinusCodeVertexGluing r (lMinusCoherentLeftSide x q) u v) :
    lMinusCodeVertexGluing r (lMinusCoherentLeftSide x q')
      (lMinusCodeVertexRepMap phi u) (lMinusCodeVertexRepMap phi v) := by
  obtain ⟨a, b, hab, s, rfl, rfl⟩ := huv
  cases a with
  | inr a => simp only [lMinusCodeEdgeGluing] at hab
  | inl a =>
    cases b with
    | inl b => simp only [lMinusCodeEdgeGluing] at hab
    | inr b =>
      obtain ⟨i, hi, hb⟩ := hab
      have hb' : b = ⟨((lMinusCoherentLeftSide x q).boundary i).1,
          lMinus_hatted_boundary_mem x q i⟩ := Subtype.ext hb.symm
      subst b
      refine ⟨.inl a, .inr ⟨((lMinusCoherentLeftSide x q').boundary i).1,
        lMinus_hatted_boundary_mem x q' i⟩, ⟨i, hi, rfl⟩, s, rfl, ?_⟩
      change Sum.inr _ = Sum.inr (lMinusMarkedVertexLabelMap phi _)
      exact congrArg Sum.inr (lMinus_markedIso_boundary_endpoint x q q' phi i s).symm

/-- Helper toward Lemma 5.5. The representative map descends through the
entire equivalence closure of boundary endpoint identifications. -/
@[expose] noncomputable def lMinusCodeRawVertexMap (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) :
    LMinusCodeRawVertex r (lMinusCoherentLeftSide x q) →
      LMinusCodeRawVertex r (lMinusCoherentLeftSide x q') :=
  Quotient.lift (fun a => ⟦lMinusCodeVertexRepMap phi a⟧) (by
    have hle : lMinusCodeVertexSetoid r (lMinusCoherentLeftSide x q) ≤
        Setoid.ker (fun a =>
          (⟦lMinusCodeVertexRepMap phi a⟧ :
            LMinusCodeRawVertex r (lMinusCoherentLeftSide x q'))) := by
      apply Setoid.eqvGen_le
      intro u v huv
      exact Quotient.sound (Relation.EqvGen.rel _ _
        (lMinusCodeVertexRepMap_gluing x r q q' phi u v huv))
    exact fun _ _ hab => hle hab)

/-- Helper toward Lemma 5.5. The quotient map preserves allocated vertices. -/
theorem lMinusCodeRawVertexMap_allocated (x : XDP) (r : LMinusSidePresentation x)
    (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (v : LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q)) :
    lMinusCodeRawVertexMap x r q q' phi v.val ∈
      lMinusCodeVertexAllocated r (lMinusCoherentLeftSide x q') := by
  rcases v.property with ⟨a, ha⟩ | ⟨b, hb⟩
  · rw [← ha]
    exact Or.inl ⟨a, rfl⟩
  · rw [← hb]
    refine Or.inr ⟨lMinusMarkedVertexMap phi b, ?_⟩
    change (⟦Sum.inr (lMinusMarkedVertexMap phi b).val⟧ :
      LMinusCodeRawVertex r _) = ⟦Sum.inr (lMinusMarkedVertexLabelMap phi b.val)⟧
    rw [lMinusMarkedVertexLabelMap_mem]

/-- Helper toward Lemma 5.5. The induced map of allocated vertex quotients. -/
@[expose] noncomputable def lMinusCodeGluedVertexMap (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) :
    LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q) →
      LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q') :=
  fun v => ⟨lMinusCodeRawVertexMap x r q q' phi v.val,
    lMinusCodeRawVertexMap_allocated x r q q' phi v⟩

/-- Helper toward Lemma 5.5. The inverse hatted action inverts the glued
vertex action on every allocated class. -/
theorem lMinusCodeGluedVertexMap_symm (x : XDP) (r : LMinusSidePresentation x)
    (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (v : LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q)) :
    lMinusCodeGluedVertexMap x r q' q (GeometricSideMarkedIso.symm phi)
      (lMinusCodeGluedVertexMap x r q q' phi v) = v := by
  apply Subtype.ext
  rcases v.property with ⟨a, ha⟩ | ⟨b, hb⟩
  · change lMinusCodeRawVertexMap x r q' q _
      (lMinusCodeRawVertexMap x r q q' phi v.val) = v.val
    rw [← ha]
    rfl
  · change lMinusCodeRawVertexMap x r q' q _
      (lMinusCodeRawVertexMap x r q q' phi v.val) = v.val
    rw [← hb]
    change (⟦Sum.inr (lMinusMarkedVertexLabelMap (GeometricSideMarkedIso.symm phi)
      (lMinusMarkedVertexLabelMap phi b.val))⟧ : LMinusCodeRawVertex r _) =
        ⟦Sum.inr b.val⟧
    rw [lMinusMarkedVertexLabelMap_mem phi b,
      lMinusMarkedVertexLabelMap_mem _ (lMinusMarkedVertexMap phi b),
      lMinusMarkedVertexMap_symm]

/-- Helper toward Lemma 5.5. The glued vertex quotient bijection fixes the
primed block and uses the marked isomorphism on the hatted block. -/
@[expose] noncomputable def lMinusCodeGluedVertexEquiv (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) :
    LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q) ≃
      LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q') where
  toFun := lMinusCodeGluedVertexMap x r q q' phi
  invFun := lMinusCodeGluedVertexMap x r q' q (GeometricSideMarkedIso.symm phi)
  left_inv := lMinusCodeGluedVertexMap_symm x r q q' phi
  right_inv := lMinusCodeGluedVertexMap_symm x r q' q (GeometricSideMarkedIso.symm phi)

/-- Helper toward Lemma 5.5. Equal-code preimages have bijective allocated
vertex quotients over their common presentation, without an isomorphism premise. -/
@[expose] noncomputable def lMinusPreimageGluedVertexEquiv {x : XDP}
    (q q' : LMinusPreimage x) (hc : lMinusCodeOf q = lMinusCodeOf q') :
    LMinusCodeGluedVertex (decodeLMinus x q.k (lMinusCodeOf q))
      (lMinusCoherentLeftSide x q.hattedCoherent) ≃
    LMinusCodeGluedVertex (decodeLMinus x q'.k (lMinusCodeOf q'))
      (lMinusCoherentLeftSide x q'.hattedCoherent) := by
  change LMinusCodeGluedVertex (decodeLMinus x q.k (lMinusCodeOf q)) _ ≃
    LMinusCodeGluedVertex (decodeLMinus x q.k (lMinusCodeOf q')) _
  rw [← hc]
  exact lMinusCodeGluedVertexEquiv x _ _ _ (lMinusPreimageHattedIso q q' hc)

/-- Helper toward Lemma 5.5. The hatted edge action retains edge identity
by taking the edge of the image dart, including missing geometric edges. -/
@[expose] noncomputable def lMinusMarkedEdgeMap {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (e : M.edges) : N.edges :=
  ⟨(lMinusMarkedDartMap phi ⟨(e.val, false), e.property⟩).val.1,
    (lMinusMarkedDartMap phi ⟨(e.val, false), e.property⟩).property⟩

/-- Helper toward Lemma 5.5. The edge action is independent of which dart
of the geometric edge is used. -/
theorem lMinusMarkedEdgeMap_dart {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (d : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    (lMinusMarkedDartMap phi d).val.1 =
      (lMinusMarkedEdgeMap phi ⟨d.val.1, d.property⟩).val := by
  rcases d with ⟨⟨e, s⟩, he⟩
  cases s with
  | false => rfl
  | true =>
    have h := lMinusMarkedDartMap_opposite phi ⟨(e, false), he⟩
    have hfst := congrArg (fun z : ℕ × Bool => z.1) h
    exact hfst

/-- Helper toward Lemma 5.5. The inverse marked action inverts the edge action. -/
theorem lMinusMarkedEdgeMap_symm {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (e : M.edges) :
    lMinusMarkedEdgeMap (GeometricSideMarkedIso.symm phi)
      (lMinusMarkedEdgeMap phi e) = e := by
  apply Subtype.ext
  have h := congrArg (fun d : {z : ℕ × Bool // z.1 ∈ M.edges} => d.val.1)
    (lMinusMarkedDartMap_symm phi ⟨(e.val, false), e.property⟩)
  rw [lMinusMarkedEdgeMap_dart] at h
  exact h

/-- Helper toward Lemma 5.5. The induced hatted edge bijection. -/
@[expose] noncomputable def lMinusMarkedEdgeEquiv {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) : M.edges ≃ N.edges where
  toFun := lMinusMarkedEdgeMap phi
  invFun := lMinusMarkedEdgeMap (GeometricSideMarkedIso.symm phi)
  left_inv := lMinusMarkedEdgeMap_symm phi
  right_inv := lMinusMarkedEdgeMap_symm (GeometricSideMarkedIso.symm phi)

/-- Helper toward Lemma 5.5. The hatted edge action preserves every shared
boundary edge index. -/
theorem lMinusMarkedEdgeMap_boundary (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (i : ℕ) :
    lMinusMarkedEdgeMap phi ⟨((lMinusCoherentLeftSide x q).boundary i).1,
      lMinus_hatted_boundary_mem x q i⟩ =
    ⟨((lMinusCoherentLeftSide x q').boundary i).1,
      lMinus_hatted_boundary_mem x q' i⟩ := by
  apply Subtype.ext
  exact congrArg (fun d => d.val.1) (lMinus_markedIso_boundary_bit x q q' phi i false)

/-- Helper toward Lemma 5.5. Edge representatives are mapped by the identity
on the primed block and the marked edge action on the hatted block. -/
@[expose] noncomputable def lMinusCodeEdgeRepEquiv {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) : Sum ℕ M.edges ≃ Sum ℕ N.edges :=
  Equiv.sumCongr (Equiv.refl _) (lMinusMarkedEdgeEquiv phi)

/-- Helper toward Lemma 5.5. The edge representative action preserves the
shared-edge gluing generators. -/
theorem lMinusCodeEdgeRepEquiv_gluing (x : XDP) (r : LMinusSidePresentation x)
    (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (a b : Sum ℕ (lMinusCoherentLeftSide x q).edges)
    (hab : lMinusCodeEdgeGluing r (lMinusCoherentLeftSide x q) a b) :
    lMinusCodeEdgeGluing r (lMinusCoherentLeftSide x q')
      (lMinusCodeEdgeRepEquiv phi a) (lMinusCodeEdgeRepEquiv phi b) := by
  cases a with
  | inr a => simp only [lMinusCodeEdgeGluing] at hab
  | inl a =>
    cases b with
    | inl b => simp only [lMinusCodeEdgeGluing] at hab
    | inr b =>
      obtain ⟨i, hi, hb⟩ := hab
      have hb' : b = ⟨((lMinusCoherentLeftSide x q).boundary i).1,
          lMinus_hatted_boundary_mem x q i⟩ := Subtype.ext hb.symm
      subst b
      refine ⟨i, hi, ?_⟩
      exact (congrArg Subtype.val (lMinusMarkedEdgeMap_boundary x q q' phi i)).symm

/-- Helper toward Lemma 5.5. The edge action descends through the generated
shared-edge equivalence relation. -/
@[expose] noncomputable def lMinusCodeGluedEdgeMap (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) :
    LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q) →
      LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q') :=
  Quotient.lift (fun a => ⟦lMinusCodeEdgeRepEquiv phi a⟧) (by
    have hle : lMinusCodeEdgeSetoid r (lMinusCoherentLeftSide x q) ≤
        Setoid.ker (fun a =>
          (⟦lMinusCodeEdgeRepEquiv phi a⟧ :
            LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q'))) := by
      apply Setoid.eqvGen_le
      intro a b hab
      exact Quotient.sound (Relation.EqvGen.rel _ _
        (lMinusCodeEdgeRepEquiv_gluing x r q q' phi a b hab))
    exact fun _ _ hab => hle hab)

/-- Helper toward Lemma 5.5. The inverse hatted edge action inverts the
glued edge action on every class. -/
theorem lMinusCodeGluedEdgeMap_symm (x : XDP) (r : LMinusSidePresentation x)
    (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (e : LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q)) :
    lMinusCodeGluedEdgeMap x r q' q (GeometricSideMarkedIso.symm phi)
      (lMinusCodeGluedEdgeMap x r q q' phi e) = e := by
  refine Quotient.inductionOn e ?_
  intro a
  cases a with
  | inl a => rfl
  | inr a =>
    change (⟦Sum.inr (lMinusMarkedEdgeMap (GeometricSideMarkedIso.symm phi)
      (lMinusMarkedEdgeMap phi a))⟧ : LMinusCodeGluedEdge r _) = ⟦Sum.inr a⟧
    rw [lMinusMarkedEdgeMap_symm]

/-- Helper toward Lemma 5.5. The glued edge quotient bijection. -/
@[expose] noncomputable def lMinusCodeGluedEdgeTransportEquiv (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) :
    LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q) ≃
      LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q') where
  toFun := lMinusCodeGluedEdgeMap x r q q' phi
  invFun := lMinusCodeGluedEdgeMap x r q' q (GeometricSideMarkedIso.symm phi)
  left_inv := lMinusCodeGluedEdgeMap_symm x r q q' phi
  right_inv := lMinusCodeGluedEdgeMap_symm x r q' q (GeometricSideMarkedIso.symm phi)

/-- Helper toward Lemma 5.5. Equal-code preimages have bijective edge
quotients over their common presentation, without an isomorphism premise. -/
@[expose] noncomputable def lMinusPreimageGluedEdgeEquiv {x : XDP}
    (q q' : LMinusPreimage x) (hc : lMinusCodeOf q = lMinusCodeOf q') :
    LMinusCodeGluedEdge (decodeLMinus x q.k (lMinusCodeOf q))
      (lMinusCoherentLeftSide x q.hattedCoherent) ≃
    LMinusCodeGluedEdge (decodeLMinus x q'.k (lMinusCodeOf q'))
      (lMinusCoherentLeftSide x q'.hattedCoherent) := by
  change LMinusCodeGluedEdge (decodeLMinus x q.k (lMinusCodeOf q)) _ ≃
    LMinusCodeGluedEdge (decodeLMinus x q.k (lMinusCodeOf q')) _
  rw [← hc]
  exact lMinusCodeGluedEdgeTransportEquiv x _ _ _ (lMinusPreimageHattedIso q q' hc)

/-- Helper toward Lemma 5.5. The coherent UIQBOT block has all geometric
edges present; this fact is not imposed on the primed block. -/
theorem lMinus_hatted_present (x : XDP) (q : Coherent x) (e : ℕ) :
    e ∈ (lMinusCoherentLeftSide x q).present :=
  edgePresent_of_nonneg_of_unbounded _
    (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q) e

/-- Helper toward Lemma 5.5. The hatted marked action preserves every
endpoint bit, using directed presence in the coherent block. -/
theorem lMinus_markedIso_dart_bit (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (d : {z : ℕ × Bool // z.1 ∈ (lMinusCoherentLeftSide x q).edges}) :
    (lMinusMarkedDartMap phi d).val.2 = d.val.2 := by
  have hf (e : (lMinusCoherentLeftSide x q).edges) :
      (lMinusMarkedDartMap phi ⟨(e.val, false), e.property⟩).val.2 = false := by
    have h := (phi.relation_iff .oriented
      (.inr ⟨(e.val, false), e.property⟩)
      (.inr ⟨(e.val, false), e.property⟩)).mp
        (show geometricSideRelation _ .oriented _ _ from
          ⟨lMinus_hatted_present x q e.val, rfl⟩)
    simp only [lMinusMarkedDartMap_cell, geometricSideRelation] at h
    exact h.2
  rcases d with ⟨⟨e, s⟩, he⟩
  cases s with
  | false => exact hf ⟨e, he⟩
  | true =>
    have h := congrArg (fun z : ℕ × Bool => z.2)
      (lMinusMarkedDartMap_opposite phi ⟨(e, false), he⟩)
    rw [hf ⟨e, he⟩] at h
    exact h

/-- Helper toward Lemma 5.5. The glued dart bijection uses the proved edge
quotient bijection and preserves its endpoint bit. -/
@[expose] noncomputable def lMinusCodeGluedDartTransportEquiv (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) :
    LMinusCodeGluedDart r (lMinusCoherentLeftSide x q) ≃
      LMinusCodeGluedDart r (lMinusCoherentLeftSide x q') :=
  Equiv.prodCongr (lMinusCodeGluedEdgeTransportEquiv x r q q' phi) (Equiv.refl _)

/-- Helper toward Lemma 5.5. The glued dart action fixes primed darts. -/
theorem lMinusCodeGluedDartTransportEquiv_primed (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (d : ℕ × Bool) :
    lMinusCodeGluedDartTransportEquiv x r q q' phi
      (lMinusCodePrimedDart r (lMinusCoherentLeftSide x q) d) =
    lMinusCodePrimedDart r (lMinusCoherentLeftSide x q') d := rfl

/-- Helper toward Lemma 5.5. On hatted darts the glued action agrees with
the given hatted marked action. -/
theorem lMinusCodeGluedDartTransportEquiv_hatted (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (d : {z : ℕ × Bool // z.1 ∈ (lMinusCoherentLeftSide x q).edges}) :
    lMinusCodeGluedDartTransportEquiv x r q q' phi
      (lMinusCodeHattedDart r (lMinusCoherentLeftSide x q) d) =
    lMinusCodeHattedDart r (lMinusCoherentLeftSide x q') (lMinusMarkedDartMap phi d) := by
  apply Prod.ext
  · change (⟦Sum.inr (lMinusMarkedEdgeMap phi ⟨d.val.1, d.property⟩)⟧ :
      LMinusCodeGluedEdge r _) =
        ⟦Sum.inr ⟨(lMinusMarkedDartMap phi d).val.1,
          (lMinusMarkedDartMap phi d).property⟩⟧
    have h := lMinusMarkedEdgeMap_dart phi d
    have he : lMinusMarkedEdgeMap phi ⟨d.val.1, d.property⟩ =
        ⟨(lMinusMarkedDartMap phi d).val.1,
          (lMinusMarkedDartMap phi d).property⟩ := Subtype.ext h.symm
    rw [he]
  · exact (lMinus_markedIso_dart_bit x q q' phi d).symm

/-- Helper toward Lemma 5.5. Equal-code preimages have bijective glued dart
carriers, without an isomorphism premise. -/
@[expose] noncomputable def lMinusPreimageGluedDartEquiv {x : XDP}
    (q q' : LMinusPreimage x) (hc : lMinusCodeOf q = lMinusCodeOf q') :
    LMinusCodeGluedDart (decodeLMinus x q.k (lMinusCodeOf q))
      (lMinusCoherentLeftSide x q.hattedCoherent) ≃
    LMinusCodeGluedDart (decodeLMinus x q'.k (lMinusCodeOf q'))
      (lMinusCoherentLeftSide x q'.hattedCoherent) := by
  change LMinusCodeGluedDart (decodeLMinus x q.k (lMinusCodeOf q)) _ ≃
    LMinusCodeGluedDart (decodeLMinus x q.k (lMinusCodeOf q')) _
  rw [← hc]
  exact lMinusCodeGluedDartTransportEquiv x _ _ _ (lMinusPreimageHattedIso q q' hc)

/-- Helper toward Lemma 5.5. Indexed boundary darts commute with the glued
transport, with both endpoint bits retained. -/
theorem lMinusCodeGluedDartTransportEquiv_boundary (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (d : ℕ × Bool) :
    lMinusCodeGluedDartTransportEquiv x r q q' phi (lMinusCodeBoundaryDart r q d) =
      lMinusCodeBoundaryDart r q' d := by
  unfold lMinusCodeBoundaryDart
  rw [lMinusCodeGluedDartTransportEquiv_hatted,
    lMinus_markedIso_boundary_bit]

/-- Helper toward Lemma 5.5. Indexed seam darts commute with glued transport. -/
theorem lMinusCodeGluedDartTransportEquiv_seam (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (i : ℕ) :
    lMinusCodeGluedDartTransportEquiv x r q q' phi
      (lMinusCodeHattedDart r _ ⟨(lMinusCoherentLeftSide x q).seam i,
        lMinus_hatted_seam_mem x q i⟩) =
    lMinusCodeHattedDart r _ ⟨(lMinusCoherentLeftSide x q').seam i,
      lMinus_hatted_seam_mem x q' i⟩ := by
  rw [lMinusCodeGluedDartTransportEquiv_hatted, lMinus_markedIso_seam]

/-- Helper toward Lemma 5.5. Hatted face succession is preserved by the
induced dart action. -/
theorem lMinusMarkedDartMap_faceNext (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (d e : {z : ℕ × Bool // z.1 ∈ (lMinusCoherentLeftSide x q).edges}) :
    (lMinusCoherentLeftSide x q).faceNext d.val e.val ↔
      (lMinusCoherentLeftSide x q').faceNext
        (lMinusMarkedDartMap phi d).val (lMinusMarkedDartMap phi e).val := by
  have h := phi.relation_iff .faceNext (.inr d) (.inr e)
  simpa only [lMinusMarkedDartMap_cell, geometricSideRelation] using h

/-- Helper toward Lemma 5.5. Each retained block face successor transports
to a retained block face successor over the same primed code. -/
theorem lMinusCodeWholeFaceNext_transport (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (d e : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))
    (h : lMinusCodeWholeFaceNext r q hf d e) :
    lMinusCodeWholeFaceNext r q' hf
      (lMinusCodeGluedDartTransportEquiv x r q q' phi d)
      (lMinusCodeGluedDartTransportEquiv x r q q' phi e) := by
  rcases h with ⟨a, b, rfl, rfl, hab⟩ | ⟨a, b, rfl, rfl, hab⟩
  · exact Or.inl ⟨a, b,
      (lMinusCodeGluedDartTransportEquiv_primed x r q q' phi a).symm,
      (lMinusCodeGluedDartTransportEquiv_primed x r q q' phi b).symm, hab⟩
  · exact Or.inr ⟨lMinusMarkedDartMap phi a, lMinusMarkedDartMap phi b,
      (lMinusCodeGluedDartTransportEquiv_hatted x r q q' phi a).symm,
      (lMinusCodeGluedDartTransportEquiv_hatted x r q q' phi b).symm,
      (lMinusMarkedDartMap_faceNext x q q' phi a b).mp hab⟩

/-- Helper toward Lemma 5.5. The inverse glued dart action is inverse on
all edge classes and bits. -/
theorem lMinusCodeGluedDartTransportEquiv_symm_apply (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (d : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeGluedDartTransportEquiv x r q' q (GeometricSideMarkedIso.symm phi)
      (lMinusCodeGluedDartTransportEquiv x r q q' phi d) = d := by
  exact Prod.ext (lMinusCodeGluedEdgeMap_symm x r q q' phi d.1) rfl

/-- Helper toward Lemma 5.5. The entire retained-face relation is invariant
under the glued dart bijection. -/
theorem lMinusCodeWholeFaceNext_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (d e : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeWholeFaceNext r q hf d e ↔
    lMinusCodeWholeFaceNext r q' hf
      (lMinusCodeGluedDartTransportEquiv x r q q' phi d)
      (lMinusCodeGluedDartTransportEquiv x r q q' phi e) := by
  constructor
  · exact lMinusCodeWholeFaceNext_transport x r q q' phi hf d e
  · intro h
    have hi := lMinusCodeWholeFaceNext_transport x r q' q
      (GeometricSideMarkedIso.symm phi) hf _ _ h
    simpa only [lMinusCodeGluedDartTransportEquiv_symm_apply] using hi

/-- Helper toward Lemma 5.5. Directed presence on a glued edge is preserved
for any fixed primed predicate, including the code-determined missing-root one. -/
theorem lMinusCodeEdgePresent_transport (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (p : ℕ → Prop)
    (e : LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q))
    (he : lMinusCodeEdgePresent r (lMinusCoherentLeftSide x q) p e) :
    lMinusCodeEdgePresent r (lMinusCoherentLeftSide x q') p
      (lMinusCodeGluedEdgeMap x r q q' phi e) := by
  rcases he with ⟨a, ha, rfl⟩ | ⟨a, _, rfl⟩
  · exact Or.inl ⟨a, ha, rfl⟩
  · exact Or.inr ⟨lMinusMarkedEdgeMap phi a,
      lMinus_hatted_present x q' _, rfl⟩

/-- Helper toward Lemma 5.5. Glued directed presence is invariant, retaining
the distinction between geometric edges and the primed directed predicate. -/
theorem lMinusCodeEdgePresent_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (p : ℕ → Prop)
    (e : LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q)) :
    lMinusCodeEdgePresent r (lMinusCoherentLeftSide x q) p e ↔
    lMinusCodeEdgePresent r (lMinusCoherentLeftSide x q') p
      (lMinusCodeGluedEdgeMap x r q q' phi e) := by
  constructor
  · exact lMinusCodeEdgePresent_transport x r q q' phi p e
  · intro h
    have hi := lMinusCodeEdgePresent_transport x r q' q
      (GeometricSideMarkedIso.symm phi) p _ h
    simpa only [lMinusCodeGluedEdgeMap_symm] using hi

/-- Helper toward Lemma 5.5. The hatted first-return permutation is
conjugated by the marked dart bijection. -/
theorem lMinusMarkedDartMap_rotation (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (d : {z : ℕ × Bool // z.1 ∈ (lMinusCoherentLeftSide x q).edges}) :
    lMinusMarkedDartMap phi (lMinusHattedRotation x q d) =
      lMinusHattedRotation x q' (lMinusMarkedDartMap phi d) := by
  have h := (phi.relation_iff .rotation (.inr d)
    (.inr (lMinusHattedRotation x q d))).mp
      ((lMinusHattedRotation_iff x q d _).mpr rfl)
  simp only [lMinusMarkedDartMap_cell, geometricSideRelation] at h
  exact ((lMinusHattedRotation_iff x q' _ _).mp h).symm

/-- Helper toward Lemma 5.5. Extending the hatted rotation by the identity
outside its block commutes with the glued dart transport. -/
theorem lMinusCodeGluedDartTransportEquiv_hatted_extend (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (d : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeGluedDartTransportEquiv x r q q' phi
      ((lMinusHattedRotation x q).extendDomain
        (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q)) d) =
    (lMinusHattedRotation x q').extendDomain
      (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q'))
      (lMinusCodeGluedDartTransportEquiv x r q q' phi d) := by
  let T := lMinusCodeGluedDartTransportEquiv x r q q' phi
  let f := lMinusCodeHattedDart r (lMinusCoherentLeftSide x q)
  let g := lMinusCodeHattedDart r (lMinusCoherentLeftSide x q')
  by_cases hd : d ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hd
    have hs := Equiv.Perm.extendDomain_apply_image (lMinusHattedRotation x q)
      (Equiv.ofInjective f (lMinusCodeHattedDart_injective r q)) a
    change (lMinusHattedRotation x q).extendDomain
      (Equiv.ofInjective f (lMinusCodeHattedDart_injective r q)) (f a) =
      f (lMinusHattedRotation x q a) at hs
    rw [hs]
    change T (f (lMinusHattedRotation x q a)) = _
    rw [lMinusCodeGluedDartTransportEquiv_hatted,
      lMinusCodeGluedDartTransportEquiv_hatted]
    rw [lMinusMarkedDartMap_rotation]
    exact (Equiv.Perm.extendDomain_apply_image (lMinusHattedRotation x q')
      (Equiv.ofInjective g (lMinusCodeHattedDart_injective r q'))
      (lMinusMarkedDartMap phi a)).symm
  · have ht : T d ∉ Set.range g := by
      rintro ⟨b, hb⟩
      obtain ⟨a, ha⟩ := (lMinusMarkedDartEquiv phi).surjective b
      apply hd
      refine ⟨a, T.injective ?_⟩
      rw [lMinusCodeGluedDartTransportEquiv_hatted]
      change g (lMinusMarkedDartMap phi a) = T d
      rw [show lMinusMarkedDartMap phi a = b from ha]
      exact hb
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hd,
      Equiv.Perm.extendDomain_apply_not_subtype _ _ ht]

/-- Helper toward Lemma 5.5. The primed rotation, extended by the identity
outside its block, commutes with glued dart transport. -/
theorem lMinusCodeGluedDartTransportEquiv_primed_extend (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (d : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeGluedDartTransportEquiv x r q q' phi
      ((kmswInfRot r.code.1 hf).extendDomain
        (Equiv.ofInjective _ (lMinusCodePrimedDart_injective r q)) d) =
    (kmswInfRot r.code.1 hf).extendDomain
      (Equiv.ofInjective _ (lMinusCodePrimedDart_injective r q'))
      (lMinusCodeGluedDartTransportEquiv x r q q' phi d) := by
  let T := lMinusCodeGluedDartTransportEquiv x r q q' phi
  let f := lMinusCodePrimedDart r (lMinusCoherentLeftSide x q)
  let g := lMinusCodePrimedDart r (lMinusCoherentLeftSide x q')
  by_cases hd : d ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hd
    have hs := Equiv.Perm.extendDomain_apply_image (kmswInfRot r.code.1 hf)
      (Equiv.ofInjective f (lMinusCodePrimedDart_injective r q)) a
    change (kmswInfRot r.code.1 hf).extendDomain
      (Equiv.ofInjective f (lMinusCodePrimedDart_injective r q)) (f a) =
      f (kmswInfRot r.code.1 hf a) at hs
    rw [hs]
    change T (f (kmswInfRot r.code.1 hf a)) = _
    rw [lMinusCodeGluedDartTransportEquiv_primed,
      lMinusCodeGluedDartTransportEquiv_primed]
    exact (Equiv.Perm.extendDomain_apply_image (kmswInfRot r.code.1 hf)
      (Equiv.ofInjective g (lMinusCodePrimedDart_injective r q')) a).symm
  · have ht : T d ∉ Set.range g := by
      rintro ⟨a, ha⟩
      apply hd
      refine ⟨a, T.injective ?_⟩
      rw [lMinusCodeGluedDartTransportEquiv_primed]
      exact ha
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hd,
      Equiv.Perm.extendDomain_apply_not_subtype _ _ ht]

/-- Helper toward Lemma 5.5. The extended indexed boundary correction
commutes with glued dart transport. -/
theorem lMinusCodeGluedDartTransportEquiv_boundary_extend (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (d : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeGluedDartTransportEquiv x r q q' phi
      (lMinusBoundaryCornerPerm.extendDomain
        (Equiv.ofInjective _ (lMinusCodeBoundaryDart_injective r q)) d) =
    lMinusBoundaryCornerPerm.extendDomain
      (Equiv.ofInjective _ (lMinusCodeBoundaryDart_injective r q'))
      (lMinusCodeGluedDartTransportEquiv x r q q' phi d) := by
  let T := lMinusCodeGluedDartTransportEquiv x r q q' phi
  let f := lMinusCodeBoundaryDart r q
  let g := lMinusCodeBoundaryDart r q'
  by_cases hd : d ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hd
    have hs := Equiv.Perm.extendDomain_apply_image lMinusBoundaryCornerPerm
      (Equiv.ofInjective f (lMinusCodeBoundaryDart_injective r q)) a
    change lMinusBoundaryCornerPerm.extendDomain
      (Equiv.ofInjective f (lMinusCodeBoundaryDart_injective r q)) (f a) =
      f (lMinusBoundaryCornerPerm a) at hs
    rw [hs]
    change T (f (lMinusBoundaryCornerPerm a)) = _
    rw [lMinusCodeGluedDartTransportEquiv_boundary,
      lMinusCodeGluedDartTransportEquiv_boundary]
    exact (Equiv.Perm.extendDomain_apply_image lMinusBoundaryCornerPerm
      (Equiv.ofInjective g (lMinusCodeBoundaryDart_injective r q')) a).symm
  · have ht : T d ∉ Set.range g := by
      rintro ⟨a, ha⟩
      apply hd
      refine ⟨a, T.injective ?_⟩
      rw [lMinusCodeGluedDartTransportEquiv_boundary]
      exact ha
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hd,
      Equiv.Perm.extendDomain_apply_not_subtype _ _ ht]

/-- Helper toward Lemma 5.5. The three-factor code splice is conjugated by
the glued dart transport. This concerns the code-built permutation. -/
theorem lMinusCodeGluedDartTransportEquiv_splice (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (d : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeGluedDartTransportEquiv x r q q' phi
      (lMinusCodeSpliceRotation r q hf d) =
    lMinusCodeSpliceRotation r q' hf
      (lMinusCodeGluedDartTransportEquiv x r q q' phi d) := by
  simp only [lMinusCodeSpliceRotation, Equiv.Perm.mul_apply]
  rw [lMinusCodeGluedDartTransportEquiv_primed_extend,
    lMinusCodeGluedDartTransportEquiv_boundary_extend,
    lMinusCodeGluedDartTransportEquiv_hatted_extend]

/-- Helper toward Lemma 5.5. The initial swap adjustment is natural under
transport, so the complete code-built adjusted rotations are conjugate. -/
theorem lMinusCodeGluedDartTransportEquiv_adjustedRotation (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (d : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeGluedDartTransportEquiv x r q q' phi
      (lMinusCodeInitialAdjustedRotation r q hf d) =
    lMinusCodeInitialAdjustedRotation r q' hf
      (lMinusCodeGluedDartTransportEquiv x r q q' phi d) := by
  let T := lMinusCodeGluedDartTransportEquiv x r q q' phi
  let H := (lMinusHattedRotation x q).extendDomain
    (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q))
  let H' := (lMinusHattedRotation x q').extendDomain
    (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q'))
  let c := lMinusCodeBoundaryDart r q (0, false)
  let c' := lMinusCodeBoundaryDart r q' (0, false)
  have hc : T c = c' := lMinusCodeGluedDartTransportEquiv_boundary x r q q' phi _
  have hh : T (H.symm c) = H'.symm c' := by
    apply H'.injective
    rw [Equiv.apply_symm_apply]
    have ht := lMinusCodeGluedDartTransportEquiv_hatted_extend x r q q' phi (H.symm c)
    change T (H (H.symm c)) = H' (T (H.symm c)) at ht
    rw [Equiv.apply_symm_apply, hc] at ht
    exact ht.symm
  have hs : T (Equiv.swap c (H.symm c) d) =
      Equiv.swap c' (H'.symm c') (T d) := by
    rw [T.injective.map_swap, hc, hh]
  change T (lMinusCodeSpliceRotation r q hf (Equiv.swap c (H.symm c) d)) =
    lMinusCodeSpliceRotation r q' hf (Equiv.swap c' (H'.symm c') (T d))
  rw [lMinusCodeGluedDartTransportEquiv_splice]
  exact congrArg (lMinusCodeSpliceRotation r q' hf) hs

/-- Helper toward Lemma 5.5. Both endpoint maps of every hatted edge are
transported by the hatted vertex action. -/
theorem lMinusMarkedVertexLabelMap_endpoint (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (e : (lMinusCoherentLeftSide x q).edges) (s : Bool) :
    lMinusMarkedVertexLabelMap phi
      (if s then (lMinusCoherentLeftSide x q).east e.val
       else (lMinusCoherentLeftSide x q).west e.val) =
      (if s then (lMinusCoherentLeftSide x q').east (lMinusMarkedEdgeMap phi e).val
       else (lMinusCoherentLeftSide x q').west (lMinusMarkedEdgeMap phi e).val) := by
  let M := lMinusCoherentLeftSide x q
  let N := lMinusCoherentLeftSide x q'
  have he := geometricSideSubmap_endpoints x renewalTime
    renewalTime_positiveSuccessTime .left q e.val e.property
  have hv : (if s then M.east e.val else M.west e.val) ∈ M.vertices := by
    cases s with
    | false => exact he.1
    | true => exact he.2
  let v : M.vertices := ⟨_, hv⟩
  let d : {z : ℕ × Bool // z.1 ∈ M.edges} := ⟨(e.val, s), e.property⟩
  have h := (phi.relation_iff .incident (.inr d) (.inl v)).mp
    (show geometricSideRelation _ .incident _ _ from rfl)
  simp only [lMinusMarkedDartMap_cell, lMinusMarkedVertexMap_cell,
    geometricSideRelation] at h
  rw [lMinus_markedIso_dart_bit x q q' phi d, lMinusMarkedEdgeMap_dart phi d] at h
  exact (lMinusMarkedVertexLabelMap_mem phi v).trans h.symm

/-- Helper toward Lemma 5.5. Raw endpoints commute with the representative
maps on both blocks. -/
theorem lMinusCodeVertexRepMap_endpoint (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (s : Bool)
    (a : Sum ℕ (lMinusCoherentLeftSide x q).edges) :
    lMinusCodeVertexRepMap phi
      (lMinusCodeRawEndpoint r (lMinusCoherentLeftSide x q) s a) =
    lMinusCodeRawEndpoint r (lMinusCoherentLeftSide x q') s
      (lMinusCodeEdgeRepEquiv phi a) := by
  cases a with
  | inl a => rfl
  | inr a =>
    exact congrArg Sum.inr (lMinusMarkedVertexLabelMap_endpoint x q q' phi a s)

/-- Helper toward Lemma 5.5. The descended intrinsic endpoints commute
with the glued vertex and edge maps. -/
theorem lMinusCodeRawVertexMap_endpoint (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (s : Bool)
    (e : LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q)) :
    lMinusCodeRawVertexMap x r q q' phi
      (lMinusCodeEndpoint r (lMinusCoherentLeftSide x q) s e) =
    lMinusCodeEndpoint r (lMinusCoherentLeftSide x q') s
      (lMinusCodeGluedEdgeMap x r q q' phi e) := by
  refine Quotient.inductionOn e ?_
  intro a
  change (⟦lMinusCodeVertexRepMap phi
    (lMinusCodeRawEndpoint r (lMinusCoherentLeftSide x q) s a)⟧ :
      LMinusCodeRawVertex r _) =
    ⟦lMinusCodeRawEndpoint r (lMinusCoherentLeftSide x q') s
      (lMinusCodeEdgeRepEquiv phi a)⟧
  rw [lMinusCodeVertexRepMap_endpoint]

/-- Helper toward Lemma 5.5. Allocated endpoint vertices commute with the
actual glued carrier bijections. -/
theorem lMinusCodeGluedVertexMap_endpoint (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (s : Bool)
    (e : LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q)) :
    lMinusCodeGluedVertexMap x r q q' phi (lMinusCodeEndpointVertex x r q s e) =
      lMinusCodeEndpointVertex x r q' s (lMinusCodeGluedEdgeMap x r q q' phi e) :=
  Subtype.ext (lMinusCodeRawVertexMap_endpoint x r q q' phi s e)

/-- Helper toward Lemma 5.5. The coherent hatted root is an allocated vertex. -/
theorem lMinus_hatted_root_mem (x : XDP) (q : Coherent x) :
    (lMinusCoherentLeftSide x q).root ∈ (lMinusCoherentLeftSide x q).vertices := by
  change 0 ∈ ⋃ j, geometricAncestorVertices x renewalTime
    renewalTime_positiveSuccessTime .left q j
  rw [iUnion_geometricAncestorVertices]
  exact source_mem_sideVertices _
    (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q) .left

/-- Helper toward Lemma 5.5. The hatted root label is transported to the
hatted root label. -/
theorem lMinusMarkedVertexLabelMap_root (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) :
    lMinusMarkedVertexLabelMap phi (lMinusCoherentLeftSide x q).root =
      (lMinusCoherentLeftSide x q').root := by
  let v : (lMinusCoherentLeftSide x q).vertices :=
    ⟨_, lMinus_hatted_root_mem x q⟩
  have h := (phi.relation_iff .root (.inl v) (.inl v)).mp
    (show geometricSideRelation _ .root _ _ from rfl)
  simp only [lMinusMarkedVertexMap_cell, geometricSideRelation] at h
  exact (lMinusMarkedVertexLabelMap_mem phi v).trans h

/-- Helper toward Lemma 5.5. The actual decoded cell carrier is equivalent
to its intrinsic common-mode carrier, with no extra coherence premise. -/
@[expose] noncomputable def LMinusPreimage.decodedCellToCommon {x : XDP}
    (q : LMinusPreimage x) :
    GeometricSideCell (lMinusDecodedSide (W := q.W) (h := q.h) (k := q.k)
      (longest := q.longest) q.hτ q.hqMode q.hfin) ≃
    Sum (LMinusCodeGluedVertex (decodeLMinus x q.k (lMinusCodeOf q))
      (lMinusCoherentLeftSide x q.hattedCoherent))
      (LMinusCodeGluedDart (decodeLMinus x q.k (lMinusCodeOf q))
        (lMinusCoherentLeftSide x q.hattedCoherent)) := by
  rcases q with ⟨W, h, H, hLL, longest, mode_eq, k, hk, hp, hτ, hqMode,
    hfin, P, Tpath, hleft⟩
  subst x
  exact (lMinusDecodedCellEquiv hτ hqMode hfin).symm

/-- Helper toward Lemma 5.5. The complete decoded cell carriers of equal-code
preimages are bijective. Its marked-relation verification is recorded below
as a separate remaining obligation. -/
@[expose] noncomputable def lMinusPreimageDecodedCellEquiv {x : XDP}
    (q q' : LMinusPreimage x) (hc : lMinusCodeOf q = lMinusCodeOf q') :
    GeometricSideCell (lMinusDecodedSide (W := q.W) (h := q.h) (k := q.k)
      (longest := q.longest) q.hτ q.hqMode q.hfin) ≃
    GeometricSideCell (lMinusDecodedSide (W := q'.W) (h := q'.h) (k := q'.k)
      (longest := q'.longest) q'.hτ q'.hqMode q'.hfin) :=
  q.decodedCellToCommon.trans
    ((Equiv.sumCongr (lMinusPreimageGluedVertexEquiv q q' hc)
      (lMinusPreimageGluedDartEquiv q q' hc)).trans q'.decodedCellToCommon.symm)

/-- Helper toward Lemma 5.5. The allocated hatted root class is preserved
by the glued vertex action. -/
theorem lMinusCodeGluedVertexMap_root (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) :
    lMinusCodeGluedVertexMap x r q q' phi
      ⟨⟦Sum.inr (lMinusCoherentLeftSide x q).root⟧,
        Or.inr ⟨⟨_, lMinus_hatted_root_mem x q⟩, rfl⟩⟩ =
      ⟨⟦Sum.inr (lMinusCoherentLeftSide x q').root⟧,
        Or.inr ⟨⟨_, lMinus_hatted_root_mem x q'⟩, rfl⟩⟩ := by
  apply Subtype.ext
  change (⟦Sum.inr (lMinusMarkedVertexLabelMap phi
    (lMinusCoherentLeftSide x q).root)⟧ : LMinusCodeRawVertex r _) =
      ⟦Sum.inr (lMinusCoherentLeftSide x q').root⟧
  rw [lMinusMarkedVertexLabelMap_root]






































end DirectedDistances.PaperProofs.Section5

