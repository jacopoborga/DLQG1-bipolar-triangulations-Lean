/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusSideMeasurable6

/-! # Vertex transport for the nonpositive right-side code

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The marked isomorphism induces the unique
vertex action on the hatted geometric-side carrier. -/
noncomputable def rMinus_rightSideMarkedIso_vertexMap
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N) :
    M.vertices → N.vertices := fun v =>
      Classical.choose (rMinus_rightSideMarkedIso_vertex phi v)

/-- Helper toward Lemma 5.5. The induced vertex action is the marked
isomorphism's action on vertex cells. -/
theorem rMinus_rightSideMarkedIso_vertexMap_cell
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (v : M.vertices) :
    phi.equiv (.inl v) = .inl (rMinus_rightSideMarkedIso_vertexMap phi v) :=
  Classical.choose_spec (rMinus_rightSideMarkedIso_vertex phi v)

/-- Helper toward Lemma 5.5. Extend the marked vertex action to all natural
IDs, fixing IDs outside the hatted vertex carrier. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_vertexIdMap
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N) :
    ℕ → ℕ := fun v => if hv : v ∈ M.vertices then
      (rMinus_rightSideMarkedIso_vertexMap phi ⟨v, hv⟩).val else v

/-- Helper toward Lemma 5.5. On a hatted vertex, the total ID map is the
marked vertex action. -/
theorem rMinus_rightSideMarkedIso_vertexIdMap_of_mem
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (v : ℕ) (hv : v ∈ M.vertices) :
    rMinus_rightSideMarkedIso_vertexIdMap phi v =
      (rMinus_rightSideMarkedIso_vertexMap phi ⟨v, hv⟩).val := by
  simp [rMinus_rightSideMarkedIso_vertexIdMap, hv]

/-- Helper toward Lemma 5.5. The marked isomorphism preserves both endpoint
darts of each indexed boundary edge. -/
theorem rMinus_rightSideMarkedIso_boundaryDart_bit
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (i : ℕ) (s : Bool) :
    phi.equiv (.inr ⟨(((rMinusCoherentRightSide x q).boundary i).1, s), by
      exact (rMinus_hatted_boundary_mem x q i)⟩) =
    .inr ⟨(((rMinusCoherentRightSide x q').boundary i).1, s), by
      exact (rMinus_hatted_boundary_mem x q' i)⟩ := by
  let M := rMinusCoherentRightSide x q
  let N := rMinusCoherentRightSide x q'
  let dM : {z : ℕ × Bool // z.1 ∈ M.edges} := ⟨M.boundary i,
    rMinus_hatted_boundary_mem x q i⟩
  let dN : {z : ℕ × Bool // z.1 ∈ N.edges} := ⟨N.boundary i,
    rMinus_hatted_boundary_mem x q' i⟩
  let dMs : {z : ℕ × Bool // z.1 ∈ M.edges} := ⟨((M.boundary i).1, s),
    rMinus_hatted_boundary_mem x q i⟩
  let dNs : {z : ℕ × Bool // z.1 ∈ N.edges} := ⟨((N.boundary i).1, s),
    rMinus_hatted_boundary_mem x q' i⟩
  change phi.equiv (.inr dMs) = .inr dNs
  have hbase : phi.equiv (.inr dM) = .inr dN := by
    exact rMinus_rightSideMarkedIso_boundary x q q' phi i
  by_cases hs : s = (M.boundary i).2
  · subst s
    exact hbase
  · have hflip : s = !(M.boundary i).2 := by
      cases hbit : (M.boundary i).2 <;> cases s <;> simp_all
    have hrel : geometricSideRelation M .opposite (.inr dM) (.inr dMs) := by
      simp [geometricSideRelation, dM, dMs, M, hflip]
    have hrel' := (phi.relation_iff .opposite (.inr dM) (.inr dMs)).mp hrel
    rw [hbase] at hrel'
    cases hd : phi.equiv (.inr dMs) with
    | inl v => simp [geometricSideRelation, hd] at hrel'
    | inr d =>
      have hval : d.val = dNs.val := by
        have hp : ((N.boundary i).1, !(N.boundary i).2) = d.val := by
          simpa [geometricSideRelation, hd, dN, M, N] using hrel'
        have hbit' : s = !(N.boundary i).2 := by
          have hbitM : (M.boundary i).2 = false := by
            simp [M, geometricSideSubmap, thinMapBoundaryDart]
          have hbitN : (N.boundary i).2 = false := by
            simp [N, geometricSideSubmap, thinMapBoundaryDart]
          have htrue : s = true := by simpa [hbitM] using hflip
          simp [htrue, hbitN]
        simp [dNs, hbit', hp]
      exact congrArg Sum.inr (Subtype.ext hval)

/-- Helper toward Lemma 5.5. The induced hatted vertex action preserves west
and east endpoints of each indexed boundary edge. -/
theorem rMinus_rightSideMarkedIso_boundaryEndpoint
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (i : ℕ) (s : Bool) :
    rMinus_rightSideMarkedIso_vertexIdMap phi
        (if s then (rMinusCoherentRightSide x q).east
          ((rMinusCoherentRightSide x q).boundary i).1
         else (rMinusCoherentRightSide x q).west
          ((rMinusCoherentRightSide x q).boundary i).1) =
      if s then (rMinusCoherentRightSide x q').east
          ((rMinusCoherentRightSide x q').boundary i).1
        else (rMinusCoherentRightSide x q').west
          ((rMinusCoherentRightSide x q').boundary i).1 := by
  let M := rMinusCoherentRightSide x q
  let N := rMinusCoherentRightSide x q'
  have hm : (M.boundary i).1 ∈ M.edges := rMinus_hatted_boundary_mem x q i
  have hn : (N.boundary i).1 ∈ N.edges := rMinus_hatted_boundary_mem x q' i
  have hme := geometricSideSubmap_endpoints x renewalTime
    renewalTime_positiveSuccessTime .right q (M.boundary i).1 hm
  have hne := geometricSideSubmap_endpoints x renewalTime
    renewalTime_positiveSuccessTime .right q' (N.boundary i).1 hn
  let vm : M.vertices := ⟨if s then M.east (M.boundary i).1
    else M.west (M.boundary i).1, by
      cases s
      · exact hme.1
      · exact hme.2⟩
  let vn : N.vertices := ⟨if s then N.east (N.boundary i).1
    else N.west (N.boundary i).1, by
      cases s
      · exact hne.1
      · exact hne.2⟩
  let dm : {z : ℕ × Bool // z.1 ∈ M.edges} :=
    ⟨((M.boundary i).1, s), hm⟩
  let dn : {z : ℕ × Bool // z.1 ∈ N.edges} :=
    ⟨((N.boundary i).1, s), hn⟩
  have hd := rMinus_rightSideMarkedIso_boundaryDart_bit x q q' phi i s
  have hv := rMinus_rightSideMarkedIso_vertexMap_cell phi vm
  have hinc : geometricSideRelation M .incident (.inr dm) (.inl vm) := by
    simp [geometricSideRelation, dm, vm]
  have hinc' := (phi.relation_iff .incident (.inr dm) (.inl vm)).mp hinc
  rw [hd, hv] at hinc'
  have hend :
      (if s then N.east (N.boundary i).1 else N.west (N.boundary i).1) =
        (rMinus_rightSideMarkedIso_vertexMap phi vm).val := by
    simpa [geometricSideRelation, dn] using hinc'
  rw [rMinus_rightSideMarkedIso_vertexIdMap_of_mem phi _ vm.property]
  simpa [vm, M, N] using hend.symm

/-- Helper toward Lemma 5.5. Extend the hatted vertex action by the identity
on finite-prefix vertex IDs. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_vertexRepMap
    (_F : State) {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) : Sum ℕ ℕ → Sum ℕ ℕ
  | .inl v => .inl v
  | .inr v => .inr (rMinus_rightSideMarkedIso_vertexIdMap phi v)

/-- Helper toward Lemma 5.5. Extend the hatted edge action by the identity
on finite-prefix edge representatives. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_edgeRepMap7
    (F : State) {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) :
    Sum {e : ℕ // e < F.nextEdge} M.edges →
      Sum {e : ℕ // e < F.nextEdge} N.edges
  | .inl e => .inl e
  | .inr e => .inr (rMinus_rightSideMarkedIso_edgeMap phi e)

/-- Helper toward Lemma 5.5. The raw vertex action preserves each endpoint
of an indexed hatted boundary edge. -/
theorem rMinus_rightSideMarkedIso_rawEndpoint_boundary
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (i : ℕ) (s : Bool) :
    rMinus_rightSideMarkedIso_vertexRepMap F phi
      (rMinusCodeRawEndpoint F (rMinusCoherentRightSide x q) s
        (.inr ⟨((rMinusCoherentRightSide x q).boundary i).1,
          rMinus_hatted_boundary_mem x q i⟩)) =
    rMinusCodeRawEndpoint F (rMinusCoherentRightSide x q') s
      (.inr ⟨((rMinusCoherentRightSide x q').boundary i).1,
        rMinus_hatted_boundary_mem x q' i⟩) := by
  let M := rMinusCoherentRightSide x q
  let N := rMinusCoherentRightSide x q'
  change Sum.inr (rMinus_rightSideMarkedIso_vertexIdMap phi
      (if s then M.east (M.boundary i).1 else M.west (M.boundary i).1)) =
    Sum.inr (if s then N.east (N.boundary i).1 else N.west (N.boundary i).1)
  exact congrArg Sum.inr (rMinus_rightSideMarkedIso_boundaryEndpoint x q q' phi i s)

/-- Helper toward Lemma 5.5. The raw vertex action sends each endpoint of a
shared-prefix/boundary edge generator to the corresponding target endpoint. -/
theorem rMinus_rightSideMarkedIso_rawEndpoint_edgeGluing
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (s : Bool)
    (a b : Sum {e : ℕ // e < F.nextEdge}
      (rMinusCoherentRightSide x q).edges)
    (hab : rMinusCodeEdgeGluing F (rMinusCoherentRightSide x q) a b) :
    (rMinus_rightSideMarkedIso_vertexRepMap F phi
      (rMinusCodeRawEndpoint F (rMinusCoherentRightSide x q) s a) =
      rMinusCodeRawEndpoint F (rMinusCoherentRightSide x q') s
        (rMinus_rightSideMarkedIso_edgeRepMap7 F phi a)) ∧
    (rMinus_rightSideMarkedIso_vertexRepMap F phi
      (rMinusCodeRawEndpoint F (rMinusCoherentRightSide x q) s b) =
      rMinusCodeRawEndpoint F (rMinusCoherentRightSide x q') s
        (rMinus_rightSideMarkedIso_edgeRepMap7 F phi b)) := by
  cases a with
  | inl a =>
    cases b with
    | inl b => simp [rMinusCodeEdgeGluing] at hab
    | inr b =>
      rcases hab with ⟨i, hi, hb⟩
      have hbe : b = ⟨((rMinusCoherentRightSide x q).boundary i).1,
          rMinus_hatted_boundary_mem x q i⟩ := Subtype.ext hb.symm
      subst b
      refine ⟨by rfl, ?_⟩
      change Sum.inr (rMinus_rightSideMarkedIso_vertexIdMap phi
          (if s then (rMinusCoherentRightSide x q).east
            ((rMinusCoherentRightSide x q).boundary i).1
           else (rMinusCoherentRightSide x q).west
            ((rMinusCoherentRightSide x q).boundary i).1)) =
        Sum.inr (if s then (rMinusCoherentRightSide x q').east
        (rMinus_rightSideMarkedIso_edgeMap phi
              ⟨((rMinusCoherentRightSide x q).boundary i).1,
                rMinus_hatted_boundary_mem x q i⟩).val
           else (rMinusCoherentRightSide x q').west
            (rMinus_rightSideMarkedIso_edgeMap phi
              ⟨((rMinusCoherentRightSide x q).boundary i).1,
                rMinus_hatted_boundary_mem x q i⟩).val)
      rw [rMinus_rightSideMarkedIso_edgeMap_boundary]
      exact congrArg Sum.inr
        (rMinus_rightSideMarkedIso_boundaryEndpoint x q q' phi i s)
  | inr a => cases b <;> simp [rMinusCodeEdgeGluing] at hab

/-- Helper toward Lemma 5.5. The exposed representative map sends each
shared-prefix/boundary edge generator to a target generator. -/
theorem rMinus_rightSideMarkedIso_edgeGluing7
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (a b : Sum {e : ℕ // e < F.nextEdge}
      (rMinusCoherentRightSide x q).edges)
    (hab : rMinusCodeEdgeGluing F (rMinusCoherentRightSide x q) a b) :
    rMinusCodeEdgeGluing F (rMinusCoherentRightSide x q')
      (rMinus_rightSideMarkedIso_edgeRepMap7 F phi a)
      (rMinus_rightSideMarkedIso_edgeRepMap7 F phi b) := by
  cases a with
  | inl a =>
    cases b with
    | inl b => simp [rMinusCodeEdgeGluing] at hab
    | inr b =>
      rcases hab with ⟨i, hi, hb⟩
      have hbe : b = ⟨((rMinusCoherentRightSide x q).boundary i).1,
          rMinus_hatted_boundary_mem x q i⟩ := Subtype.ext hb.symm
      subst b
      refine ⟨i, hi, ?_⟩
      exact (congrArg Subtype.val
        (rMinus_rightSideMarkedIso_edgeMap_boundary x q q' phi i)).symm
  | inr a => cases b <;> simp [rMinusCodeEdgeGluing] at hab

/-- Helper toward Lemma 5.5. The raw vertex action sends every endpoint
gluing generator to a generator for the transported two-block code. -/
theorem rMinus_rightSideMarkedIso_vertexGluing
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (u v : Sum ℕ ℕ)
    (huv : rMinusCodeVertexGluing F (rMinusCoherentRightSide x q) u v) :
    rMinusCodeVertexGluing F (rMinusCoherentRightSide x q')
      (rMinus_rightSideMarkedIso_vertexRepMap F phi u)
      (rMinus_rightSideMarkedIso_vertexRepMap F phi v) := by
  rcases huv with ⟨a, b, hab, s, hu, hv⟩
  have hEdge := rMinus_rightSideMarkedIso_edgeGluing7 x q q' phi F a b hab
  have hEndpoint := rMinus_rightSideMarkedIso_rawEndpoint_edgeGluing
    x q q' phi F s a b hab
  refine ⟨rMinus_rightSideMarkedIso_edgeRepMap7 F phi a,
    rMinus_rightSideMarkedIso_edgeRepMap7 F phi b, hEdge, s, ?_, ?_⟩
  · exact hEndpoint.1.symm.trans
      (congrArg (rMinus_rightSideMarkedIso_vertexRepMap F phi) hu)
  · exact hEndpoint.2.symm.trans
      (congrArg (rMinus_rightSideMarkedIso_vertexRepMap F phi) hv)

end DirectedDistances.PaperProofs.Section5

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The raw vertex action respects the complete
generated endpoint-gluing equivalence. -/
theorem rMinus_rightSideMarkedIso_vertexSetoid7
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (a b : Sum ℕ ℕ)
    (hab : rMinusCodeVertexSetoid F (rMinusCoherentRightSide x q) a b) :
    rMinusCodeVertexSetoid F (rMinusCoherentRightSide x q')
      (rMinus_rightSideMarkedIso_vertexRepMap F phi a)
      (rMinus_rightSideMarkedIso_vertexRepMap F phi b) := by
  change Relation.EqvGen
    (rMinusCodeVertexGluing F (rMinusCoherentRightSide x q)) a b at hab
  change Relation.EqvGen
    (rMinusCodeVertexGluing F (rMinusCoherentRightSide x q'))
      (rMinus_rightSideMarkedIso_vertexRepMap F phi a)
      (rMinus_rightSideMarkedIso_vertexRepMap F phi b)
  induction hab with
  | rel a b hab =>
      exact Relation.EqvGen.rel _ _
        (rMinus_rightSideMarkedIso_vertexGluing x q q' phi F a b hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab₁ hab₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Helper toward Lemma 5.5. The raw vertex action descends to the intrinsic
quotient of vertex representatives. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_rawVertexQuotMap7
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) :
    RMinusCodeRawVertex F (rMinusCoherentRightSide x q) →
      RMinusCodeRawVertex F (rMinusCoherentRightSide x q') :=
  Quotient.map (rMinus_rightSideMarkedIso_vertexRepMap F phi)
    (fun _ _ hab => rMinus_rightSideMarkedIso_vertexSetoid7 x q q' phi F _ _ hab)

/-- Helper toward Lemma 5.5. The raw quotient map fixes finite-prefix
vertex representatives. -/
theorem rMinus_rightSideMarkedIso_rawVertexQuotMap7_inl
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (v : ℕ) :
    rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F
      (⟦Sum.inl v⟧ : RMinusCodeRawVertex F (rMinusCoherentRightSide x q)) =
    (⟦Sum.inl v⟧ : RMinusCodeRawVertex F (rMinusCoherentRightSide x q')) := rfl

/-- Helper toward Lemma 5.5. The raw quotient map applies the marked vertex
action to hatted representatives. -/
theorem rMinus_rightSideMarkedIso_rawVertexQuotMap7_inr
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (v : ℕ) :
    rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F
      (⟦Sum.inr v⟧ : RMinusCodeRawVertex F (rMinusCoherentRightSide x q)) =
    (⟦Sum.inr (rMinus_rightSideMarkedIso_vertexIdMap phi v)⟧ :
      RMinusCodeRawVertex F (rMinusCoherentRightSide x q')) := rfl

/-- Helper toward Lemma 5.5. The marked vertex maps induced by an
isomorphism and its inverse compose to the identity on actual vertices. -/
theorem rMinus_rightSideMarkedIso_vertexMap_symm_apply
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (v : M.vertices) :
    rMinus_rightSideMarkedIso_vertexMap (GeometricSideMarkedIso.symm phi)
      (rMinus_rightSideMarkedIso_vertexMap phi v) = v := by
  apply Subtype.ext
  have h₁ := rMinus_rightSideMarkedIso_vertexMap_cell phi v
  have h₂ := rMinus_rightSideMarkedIso_vertexMap_cell
    (GeometricSideMarkedIso.symm phi) (rMinus_rightSideMarkedIso_vertexMap phi v)
  have h₃ := congrArg phi.equiv.symm h₁
  rw [phi.equiv.symm_apply_apply] at h₃
  have h₄ : Sum.inl v =
      Sum.inl (rMinus_rightSideMarkedIso_vertexMap
        (GeometricSideMarkedIso.symm phi)
        (rMinus_rightSideMarkedIso_vertexMap phi v)) := h₃.trans h₂
  exact (congrArg Subtype.val (Sum.inl.inj h₄)).symm

/-- Helper toward Lemma 5.5. The total vertex-ID maps induced by inverse
marked isomorphisms compose on the hatted vertex carrier. -/
theorem rMinus_rightSideMarkedIso_vertexIdMap_symm_apply
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (v : ℕ) (hv : v ∈ M.vertices) :
    rMinus_rightSideMarkedIso_vertexIdMap (GeometricSideMarkedIso.symm phi)
      (rMinus_rightSideMarkedIso_vertexIdMap phi v) = v := by
  rw [rMinus_rightSideMarkedIso_vertexIdMap_of_mem phi v hv]
  rw [rMinus_rightSideMarkedIso_vertexIdMap_of_mem
    (GeometricSideMarkedIso.symm phi) _
    (rMinus_rightSideMarkedIso_vertexMap phi ⟨v, hv⟩).property]
  exact congrArg Subtype.val (rMinus_rightSideMarkedIso_vertexMap_symm_apply phi ⟨v, hv⟩)

end DirectedDistances.PaperProofs.Section5

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The raw quotient action restricts to the
allocated finite-prefix/hatted vertex carrier. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_gluedVertexMap7
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) :
    RMinusCodeGluedVertex F (rMinusCoherentRightSide x q) →
      RMinusCodeGluedVertex F (rMinusCoherentRightSide x q') := fun v =>
  ⟨rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F v.val, by
    rcases v.property with hprefix | hhatted
    · obtain ⟨a, ha⟩ := hprefix
      apply Or.inl
      refine ⟨a, ?_⟩
      calc
        (⟦Sum.inl a.val⟧ : RMinusCodeRawVertex F
            (rMinusCoherentRightSide x q')) =
            rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F
              (⟦Sum.inl a.val⟧ : RMinusCodeRawVertex F
                (rMinusCoherentRightSide x q)) :=
          (rMinus_rightSideMarkedIso_rawVertexQuotMap7_inl x q q' phi F a.val).symm
        _ = rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F v.val :=
          congrArg (rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F) ha
    · obtain ⟨b, hb⟩ := hhatted
      apply Or.inr
      refine ⟨rMinus_rightSideMarkedIso_vertexMap phi b, ?_⟩
      have hmap := congrArg
        (rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F) hb
      rw [rMinus_rightSideMarkedIso_rawVertexQuotMap7_inr] at hmap
      rw [rMinus_rightSideMarkedIso_vertexIdMap_of_mem phi b.val b.property] at hmap
      exact hmap⟩

/-- Helper toward Lemma 5.5. On a finite-prefix allocated vertex, the
induced maps of a marked isomorphism and its inverse compose identically. -/
theorem rMinus_rightSideMarkedIso_rawVertexQuotMap7_symm_inl
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (v : ℕ) :
    rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q' q
      (GeometricSideMarkedIso.symm phi) F
      (rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F
        (⟦Sum.inl v⟧ : RMinusCodeRawVertex F (rMinusCoherentRightSide x q))) =
      (⟦Sum.inl v⟧ : RMinusCodeRawVertex F (rMinusCoherentRightSide x q)) := rfl

/-- Helper toward Lemma 5.5. On an allocated hatted vertex, the induced maps
of a marked isomorphism and its inverse compose identically. -/
theorem rMinus_rightSideMarkedIso_rawVertexQuotMap7_symm_inr
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (v : (rMinusCoherentRightSide x q).vertices) :
    rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q' q
      (GeometricSideMarkedIso.symm phi) F
      (rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F
        (⟦Sum.inr v.val⟧ : RMinusCodeRawVertex F (rMinusCoherentRightSide x q))) =
      (⟦Sum.inr v.val⟧ : RMinusCodeRawVertex F (rMinusCoherentRightSide x q)) := by
  simp only [rMinus_rightSideMarkedIso_rawVertexQuotMap7_inr]
  rw [rMinus_rightSideMarkedIso_vertexIdMap_symm_apply phi v.val v.property]

/-- Helper toward Lemma 5.5. The restricted raw quotient maps induced by a
marked isomorphism and its inverse compose on allocated vertices. -/
theorem rMinus_rightSideMarkedIso_gluedVertexMap7_symm_apply
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (v : RMinusCodeGluedVertex F (rMinusCoherentRightSide x q)) :
    rMinus_rightSideMarkedIso_gluedVertexMap7 x q' q
      (GeometricSideMarkedIso.symm phi) F
      (rMinus_rightSideMarkedIso_gluedVertexMap7 x q q' phi F v) = v := by
  apply Subtype.ext
  rcases v.property with hprefix | hhatted
  · obtain ⟨a, ha⟩ := hprefix
    calc
      rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q' q
          (GeometricSideMarkedIso.symm phi) F
          (rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F v.val) =
        rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q' q
          (GeometricSideMarkedIso.symm phi) F
          (rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F
            (⟦Sum.inl a.val⟧ : RMinusCodeRawVertex F
              (rMinusCoherentRightSide x q))) :=
          congrArg
            (rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q' q
              (GeometricSideMarkedIso.symm phi) F)
            (congrArg
              (rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F) ha.symm)
      _ = (⟦Sum.inl a.val⟧ : RMinusCodeRawVertex F
          (rMinusCoherentRightSide x q)) :=
        rMinus_rightSideMarkedIso_rawVertexQuotMap7_symm_inl x q q' phi F a.val
      _ = v.val := ha
  · obtain ⟨b, hb⟩ := hhatted
    calc
      rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q' q
          (GeometricSideMarkedIso.symm phi) F
          (rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F v.val) =
        rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q' q
          (GeometricSideMarkedIso.symm phi) F
          (rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F
            (⟦Sum.inr b.val⟧ : RMinusCodeRawVertex F
              (rMinusCoherentRightSide x q))) :=
          congrArg
            (rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q' q
              (GeometricSideMarkedIso.symm phi) F)
            (congrArg
              (rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F) hb.symm)
      _ = (⟦Sum.inr b.val⟧ : RMinusCodeRawVertex F
          (rMinusCoherentRightSide x q)) :=
        rMinus_rightSideMarkedIso_rawVertexQuotMap7_symm_inr x q q' phi F b
      _ = v.val := hb

/-- Helper toward Lemma 5.5. The allocated vertex quotients are equivalent
under a hatted marked isomorphism. -/
noncomputable def rMinus_rightSideMarkedIso_gluedVertexEquiv7
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) :
    RMinusCodeGluedVertex F (rMinusCoherentRightSide x q) ≃
      RMinusCodeGluedVertex F (rMinusCoherentRightSide x q') where
  toFun := rMinus_rightSideMarkedIso_gluedVertexMap7 x q q' phi F
  invFun := rMinus_rightSideMarkedIso_gluedVertexMap7 x q' q
    (GeometricSideMarkedIso.symm phi) F
  left_inv := rMinus_rightSideMarkedIso_gluedVertexMap7_symm_apply x q q' phi F
  right_inv := rMinus_rightSideMarkedIso_gluedVertexMap7_symm_apply x q' q
    (GeometricSideMarkedIso.symm phi) F

end DirectedDistances.PaperProofs.Section5


namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The exposed edge-representative map respects
the full generated edge-gluing equivalence. -/
theorem rMinus_rightSideMarkedIso_edgeSetoid7
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State)
    (a b : Sum {e : ℕ // e < F.nextEdge}
      (rMinusCoherentRightSide x q).edges)
    (hab : rMinusCodeEdgeSetoid F (rMinusCoherentRightSide x q) a b) :
    rMinusCodeEdgeSetoid F (rMinusCoherentRightSide x q')
      (rMinus_rightSideMarkedIso_edgeRepMap7 F phi a)
      (rMinus_rightSideMarkedIso_edgeRepMap7 F phi b) := by
  change Relation.EqvGen
    (rMinusCodeEdgeGluing F (rMinusCoherentRightSide x q)) a b at hab
  change Relation.EqvGen
    (rMinusCodeEdgeGluing F (rMinusCoherentRightSide x q'))
      (rMinus_rightSideMarkedIso_edgeRepMap7 F phi a)
      (rMinus_rightSideMarkedIso_edgeRepMap7 F phi b)
  induction hab with
  | rel a b hab =>
      exact Relation.EqvGen.rel _ _
        (rMinus_rightSideMarkedIso_edgeGluing7 x q q' phi F a b hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab₁ hab₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Helper toward Lemma 5.5. The exposed edge-representative map descends to
the complete glued-edge quotient. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_rawEdgeQuotMap7
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) :
    RMinusCodeGluedEdge F (rMinusCoherentRightSide x q) →
      RMinusCodeGluedEdge F (rMinusCoherentRightSide x q') :=
  Quotient.map (rMinus_rightSideMarkedIso_edgeRepMap7 F phi)
    (fun _ _ hab => rMinus_rightSideMarkedIso_edgeSetoid7 x q q' phi F _ _ hab)

/-- Helper toward Lemma 5.5. The edge quotient action fixes finite-prefix
edge representatives. -/
theorem rMinus_rightSideMarkedIso_rawEdgeQuotMap7_inl
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (e : {e : ℕ // e < F.nextEdge}) :
    rMinus_rightSideMarkedIso_rawEdgeQuotMap7 x q q' phi F
      (⟦Sum.inl e⟧ : RMinusCodeGluedEdge F (rMinusCoherentRightSide x q)) =
    (⟦Sum.inl e⟧ : RMinusCodeGluedEdge F (rMinusCoherentRightSide x q')) := rfl

/-- Helper toward Lemma 5.5. The edge quotient action uses the marked edge
map on hatted representatives. -/
theorem rMinus_rightSideMarkedIso_rawEdgeQuotMap7_inr
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (e : (rMinusCoherentRightSide x q).edges) :
    rMinus_rightSideMarkedIso_rawEdgeQuotMap7 x q q' phi F
      (⟦Sum.inr e⟧ : RMinusCodeGluedEdge F (rMinusCoherentRightSide x q)) =
    (⟦Sum.inr (rMinus_rightSideMarkedIso_edgeMap phi e)⟧ :
      RMinusCodeGluedEdge F (rMinusCoherentRightSide x q')) := rfl

/-- Helper toward Lemma 5.5. The edge quotient action induced by a marked
isomorphism and its inverse composes to the identity. -/
theorem rMinus_rightSideMarkedIso_rawEdgeQuotMap7_symm_apply
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (e : RMinusCodeGluedEdge F (rMinusCoherentRightSide x q)) :
    rMinus_rightSideMarkedIso_rawEdgeQuotMap7 x q' q
      (GeometricSideMarkedIso.symm phi) F
      (rMinus_rightSideMarkedIso_rawEdgeQuotMap7 x q q' phi F e) = e := by
  refine Quotient.inductionOn e ?_
  intro a
  cases a with
  | inl a => rfl
  | inr a =>
      simp only [rMinus_rightSideMarkedIso_rawEdgeQuotMap7_inr]
      rw [rMinus_rightSideMarkedIso_edgeMap_symm_apply]

/-- Helper toward Lemma 5.5. The complete glued-edge quotients are
 equivalent under the hatted marked isomorphism. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_gluedEdgeEquiv7
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) :
    RMinusCodeGluedEdge F (rMinusCoherentRightSide x q) ≃
      RMinusCodeGluedEdge F (rMinusCoherentRightSide x q') where
  toFun := rMinus_rightSideMarkedIso_rawEdgeQuotMap7 x q q' phi F
  invFun := rMinus_rightSideMarkedIso_rawEdgeQuotMap7 x q' q
    (GeometricSideMarkedIso.symm phi) F
  left_inv := rMinus_rightSideMarkedIso_rawEdgeQuotMap7_symm_apply x q q' phi F
  right_inv := rMinus_rightSideMarkedIso_rawEdgeQuotMap7_symm_apply x q' q
    (GeometricSideMarkedIso.symm phi) F

end DirectedDistances.PaperProofs.Section5

namespace DirectedDistances.PaperProofs.Section5


























end DirectedDistances.PaperProofs.Section5

