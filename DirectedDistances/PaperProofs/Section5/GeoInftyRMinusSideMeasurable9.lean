/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusSideMeasurable8

/-! # Decoded right-side marked isomorphism

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The source root belongs to the hatted right
side's vertex carrier. -/
theorem rMinus_rightSide_root_mem9 (x : XDP) (q : Coherent x) :
    (rMinusCoherentRightSide x q).root ∈ (rMinusCoherentRightSide x q).vertices := by
  change 0 ∈ ⋃ j, geometricAncestorVertices x renewalTime
    renewalTime_positiveSuccessTime .right q j
  rw [iUnion_geometricAncestorVertices]
  exact source_mem_sideVertices _
    (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q) .right

/-- Helper toward Lemma 5.5. The quotient vertex representing the hatted
root is carried to the target quotient's hatted root. -/
theorem rMinus_rightSideMarkedIso_codeRoot9
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) :
    rMinus_rightSideMarkedIso_gluedVertexMap7 x q q' phi F
      ⟨(⟦Sum.inr (rMinusCoherentRightSide x q).root⟧ :
          RMinusCodeRawVertex F (rMinusCoherentRightSide x q)),
        Or.inr ⟨⟨(rMinusCoherentRightSide x q).root,
          rMinus_rightSide_root_mem9 x q⟩, rfl⟩⟩ =
    ⟨(⟦Sum.inr (rMinusCoherentRightSide x q').root⟧ :
        RMinusCodeRawVertex F (rMinusCoherentRightSide x q')),
      Or.inr ⟨⟨(rMinusCoherentRightSide x q').root,
        rMinus_rightSide_root_mem9 x q'⟩, rfl⟩⟩ := by
  apply Subtype.ext
  change rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F
      (⟦Sum.inr (rMinusCoherentRightSide x q).root⟧) = _
  rw [rMinus_rightSideMarkedIso_rawVertexQuotMap7_inr]
  rw [rMinus_rightSideMarkedIso_vertexIdMap_of_mem phi _
    (rMinus_rightSide_root_mem9 x q)]
  have hr := rMinus_rightSideMarkedIso_vertexMap_root8 phi
    ⟨(rMinusCoherentRightSide x q).root,
      rMinus_rightSide_root_mem9 x q⟩ rfl
  rw [hr]

end DirectedDistances.PaperProofs.Section5

namespace DirectedDistances.PaperProofs.Section5
open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical
local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime


/-- Helper toward Lemma 5.5. The allocated vertex equivalence is induced
by the hatted marked isomorphism and the identity on the prefix. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_gluedVertexEquiv9
    (x : XDP) (q q' : Coherent x)
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

/-- Helper toward Lemma 5.5. The intrinsic decoded cells are equivalent
under the induced vertex and endpoint-aware dart maps. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_codeCellEquiv9
    (x : XDP) (w : ℕ → Fin 3) (n : ℕ)
    (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q')) :
    Sum (RMinusCodeGluedVertex (kmswStage w n) (rMinusCoherentRightSide x q))
        (RMinusCodeGluedDart (kmswStage w n) (rMinusCoherentRightSide x q)) ≃
      Sum (RMinusCodeGluedVertex (kmswStage w n) (rMinusCoherentRightSide x q'))
        (RMinusCodeGluedDart (kmswStage w n) (rMinusCoherentRightSide x q')) :=
  Equiv.sumCongr
    (rMinus_rightSideMarkedIso_gluedVertexEquiv9 x q q' phi (kmswStage w n))
    (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n))

/-- Helper toward Lemma 5.5. The root predicate is preserved and reflected
by the intrinsic cell equivalence. -/
theorem rMinus_rightSideMarkedIso_codeRootRelation9
    (x : XDP) (w : ℕ → Fin 3) (n : ℕ) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (v : RMinusCodeGluedVertex (kmswStage w n) (rMinusCoherentRightSide x q)) :
    v.val = (⟦Sum.inr (rMinusCoherentRightSide x q).root⟧ :
        RMinusCodeRawVertex (kmswStage w n) (rMinusCoherentRightSide x q)) ↔
      (rMinus_rightSideMarkedIso_gluedVertexEquiv9 x q q' phi (kmswStage w n) v).val =
        (⟦Sum.inr (rMinusCoherentRightSide x q').root⟧ :
          RMinusCodeRawVertex (kmswStage w n) (rMinusCoherentRightSide x q')) := by
  let F := kmswStage w n
  let M := rMinusCoherentRightSide x q
  let N := rMinusCoherentRightSide x q'
  let V := rMinus_rightSideMarkedIso_gluedVertexEquiv9 x q q' phi F
  let rM : RMinusCodeGluedVertex F M :=
    ⟨⟦Sum.inr M.root⟧, Or.inr ⟨⟨M.root, rMinus_rightSide_root_mem9 x q⟩, rfl⟩⟩
  let rN : RMinusCodeGluedVertex F N :=
    ⟨⟦Sum.inr N.root⟧, Or.inr ⟨⟨N.root, rMinus_rightSide_root_mem9 x q'⟩, rfl⟩⟩
  have hr : V rM = rN := by
    change rMinus_rightSideMarkedIso_gluedVertexMap7 x q q' phi F rM = rN
    exact rMinus_rightSideMarkedIso_codeRoot9 x q q' phi F
  constructor
  · intro hv
    have he : v = rM := Subtype.ext hv
    have hm := congrArg V he
    simpa [hr, rN, N] using congrArg Subtype.val hm
  · intro hv
    have he : V v = V rM := by
      apply Subtype.ext
      simpa [hr, rN, N] using hv
    exact congrArg Subtype.val (V.injective he)

end DirectedDistances.PaperProofs.Section5

namespace DirectedDistances.PaperProofs.Section5
open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical
local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. A present glued edge has its false dart sent
to a false target dart. -/
theorem rMinus_rightSideMarkedIso_presentFalse9
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (e : RMinusCodeGluedEdge F (rMinusCoherentRightSide x q))
    (he : rMinusCodeEdgePresent F (rMinusCoherentRightSide x q) e) :
    (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F (e, false)).2 = false := by
  let T := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F
  revert he
  refine Quotient.inductionOn e ?_
  intro a he
  rcases he with ⟨p, hp, hclass⟩ | ⟨b, hb, hclass⟩
  · let d : StageDart F.nextEdge := (⟨p.val, p.property⟩, false)
    have hrep : rMinusCodePrefixDart F (rMinusCoherentRightSide x q) d = (⟦Sum.inl p⟧, false) := rfl
    have hmap := congrArg T (congrArg (fun z => (z, false)) hclass)
    rw [← hrep, rMinus_rightSideMarkedIso_gluedDartEquiv8_prefixOfBlocks] at hmap
    exact (congrArg Prod.snd hmap).symm
  · let d : {z : ℕ × Bool // z.1 ∈ (rMinusCoherentRightSide x q).edges} :=
      ⟨(b.val, false), b.property⟩
    have ho := (rMinus_rightSideMarkedIso_oriented phi d).mp ⟨hb, rfl⟩
    have hrep : rMinusCodeHattedDart F (rMinusCoherentRightSide x q) d =
        (⟦Sum.inr b⟧, false) := rfl
    have hmap := congrArg T (congrArg (fun z => (z, false)) hclass)
    rw [← hrep, rMinus_rightSideMarkedIso_gluedDartEquiv8_hattedOfBlocks] at hmap
    have hbit := congrArg Prod.snd hmap
    simpa only [rMinusCodeHattedDart] using hbit.symm.trans ho.2

/-- Helper toward Lemma 5.5. The oriented-dart relation is preserved by the
endpoint-aware glued dart map. -/
theorem rMinus_rightSideMarkedIso_orientedForward9
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (d : RMinusCodeGluedDart F (rMinusCoherentRightSide x q))
    (hd : rMinusCodeEdgePresent F (rMinusCoherentRightSide x q) d.1 ∧ d.2 = false) :
    rMinusCodeEdgePresent F (rMinusCoherentRightSide x q')
        (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F d).1 ∧
      (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F d).2 = false := by
  rcases d with ⟨e, s⟩
  have hs : s = false := hd.2
  subst s
  exact ⟨rMinus_rightSideMarkedIso_codeEdgePresent8 x q q' phi F e hd.1,
    rMinus_rightSideMarkedIso_presentFalse9 x q q' phi F e hd.1⟩

/-- Helper toward Lemma 5.5. The oriented-dart relation is preserved and
reflected by the endpoint-aware glued dart equivalence. -/
theorem rMinus_rightSideMarkedIso_oriented9
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (d : RMinusCodeGluedDart F (rMinusCoherentRightSide x q)) :
    (rMinusCodeEdgePresent F (rMinusCoherentRightSide x q) d.1 ∧ d.2 = false) ↔
      (rMinusCodeEdgePresent F (rMinusCoherentRightSide x q')
        (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F d).1 ∧
       (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F d).2 = false) := by
  constructor
  · exact rMinus_rightSideMarkedIso_orientedForward9 x q q' phi F d
  · intro hd
    let T := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F
    have hi := rMinus_rightSideMarkedIso_orientedForward9 x q' q
      (GeometricSideMarkedIso.symm phi) F (T d) hd
    change (rMinusCodeEdgePresent F (rMinusCoherentRightSide x q) (T.invFun (T d)).1 ∧
      (T.invFun (T d)).2 = false) at hi
    rw [show T.invFun (T d) = d from T.left_inv d] at hi
    exact hi


/-- Helper toward Lemma 5.5. Every intrinsic code relation is preserved and
reflected by the vertex/dart equivalence. -/
theorem rMinus_rightSideMarkedIso_codeWholeRelation_iff9
    (x : XDP) (w : ℕ → Fin 3) (n : ℕ) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (t : TruncationRelation)
    (u v : Sum (RMinusCodeGluedVertex (kmswStage w n) (rMinusCoherentRightSide x q))
      (RMinusCodeGluedDart (kmswStage w n) (rMinusCoherentRightSide x q))) :
    rMinusCodeWholeRelation w n q t u v ↔
      rMinusCodeWholeRelation w n q' t
        (rMinus_rightSideMarkedIso_codeCellEquiv9 x w n q q' phi u)
        (rMinus_rightSideMarkedIso_codeCellEquiv9 x w n q q' phi v) := by
  cases t <;> cases u <;> cases v <;>
    simp only [rMinusCodeWholeRelation, rMinus_rightSideMarkedIso_codeCellEquiv9,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]

  case root.inl.inl a b =>
    exact rMinus_rightSideMarkedIso_codeRootRelation9 x w n q q' phi a
  case root.inl.inr a b =>
    exact rMinus_rightSideMarkedIso_codeRootRelation9 x w n q q' phi a
  case incident.inr.inl d v =>
    let F := kmswStage w n
    let M := rMinusCoherentRightSide x q
    let N := rMinusCoherentRightSide x q'
    let V := rMinus_rightSideMarkedIso_gluedVertexEquiv9 x q q' phi F
    let D := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F
    let ep : RMinusCodeGluedVertex F M :=
      ⟨rMinusCodeEndpoint F M d.2 d.1,
        rMinusCodeEndpoint_allocated w n q d.2 d.1⟩
    have he : (V ep).val = rMinusCodeEndpoint F N (D d).2 (D d).1 := by
      change rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F ep.val = _
      exact rMinus_rightSideMarkedIso_codeEndpoint8 x q q' phi F d
    constructor
    · intro h
      have hp : ep = v := Subtype.ext h
      have hv := congrArg (fun z => z.val) (congrArg V hp)
      rw [he] at hv
      exact hv
    · intro h
      have hv : (V ep).val = (V v).val := he.trans h
      exact congrArg Subtype.val (V.injective (Subtype.ext hv))
  case opposite.inr.inr d e =>
    let D := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
    constructor
    · intro h
      have hd := congrArg D h
      rw [rMinus_rightSideMarkedIso_gluedDartEquiv8_reverse] at hd
      exact hd
    · intro h
      apply D.injective
      rw [rMinus_rightSideMarkedIso_gluedDartEquiv8_reverse]
      exact h
  case oriented.inr.inl d v =>
    exact rMinus_rightSideMarkedIso_oriented9 x q q' phi (kmswStage w n) d
  case oriented.inr.inr d e =>
    exact rMinus_rightSideMarkedIso_oriented9 x q q' phi (kmswStage w n) d
  case rotation.inr.inr d e =>
    let D := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
    have hr := rMinus_rightSideMarkedIso_gluedDartEquiv8_adjustedRotation
      x q q' phi w n d
    constructor
    · intro h
      exact hr.symm.trans (congrArg D h)
    · intro h
      apply D.injective
      exact hr.trans h
  case faceNext.inr.inr d e =>
    exact rMinus_rightSideMarkedIso_gluedDartEquiv8_faceNext
      x q q' phi (kmswStage w n) d e
  case boundary.inr.inl i d v =>
    let D := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
    have hb := rMinus_rightSideMarkedIso_decodedBoundary8 x q q' phi w n i
    constructor
    · intro h
      exact hb.symm.trans (congrArg D h)
    · intro h
      apply D.injective
      exact hb.trans h
  case boundary.inr.inr i d e =>
    let D := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
    have hb := rMinus_rightSideMarkedIso_decodedBoundary8 x q q' phi w n i
    constructor
    · intro h
      exact hb.symm.trans (congrArg D h)
    · intro h
      apply D.injective
      exact hb.trans h
  case seam.inr.inl i d v =>
    let D := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
    have hs := rMinus_rightSideMarkedIso_decodedSeam8 x q q' phi w n i
    constructor
    · intro h
      exact hs.symm.trans (congrArg D h)
    · intro h
      apply D.injective
      exact hs.trans h
  case seam.inr.inr i d e =>
    let D := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
    have hs := rMinus_rightSideMarkedIso_decodedSeam8 x q q' phi w n i
    constructor
    · intro h
      exact hs.symm.trans (congrArg D h)
    · intro h
      apply D.injective
      exact hs.trans h

/-- Helper toward Lemma 5.5. Equal coherent right-side codes induce a
marked isomorphism of the complete decoded finite-prefix/hatted sides. -/
theorem rMinusDecodedSideOfBlocks_markedIso_of_eq
    (x : XDP) (w : ℕ → Fin 3) (n : ℕ)
    (q q' : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (hc : thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q'.1) :
    Nonempty (GeometricSideMarkedIso
      (rMinusDecodedSideOfBlocks (kmswStage w n)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
        (rMinusCodeInitialAdjustedRotation w n q))
      (rMinusDecodedSideOfBlocks (kmswStage w n)
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q')
        (rMinusCodeInitialAdjustedRotation w n q'))) := by
  rw [← rMinusDecodedSide_eq_ofBlocks w n q,
    ← rMinusDecodedSide_eq_ofBlocks w n q']
  obtain ⟨phi⟩ := rMinus_rightSideCode_markedIso_of_eq x q q' hc
  let C := (rMinusDecodedCellEquiv w n q).symm.trans
    ((rMinus_rightSideMarkedIso_codeCellEquiv9 x w n q q' phi).trans
      (rMinusDecodedCellEquiv w n q'))
  refine ⟨{ equiv := C, relation_iff := ?_ }⟩
  intro t u v
  obtain ⟨a, rfl⟩ := (rMinusDecodedCellEquiv w n q).surjective u
  obtain ⟨b, rfl⟩ := (rMinusDecodedCellEquiv w n q).surjective v
  simp only [C, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact (rMinusDecodedCellEquiv_relation_iff w n q t a b).symm.trans
    ((rMinus_rightSideMarkedIso_codeWholeRelation_iff9 x w n q q' phi t a b).trans
      (rMinusDecodedCellEquiv_relation_iff w n q' t
        (rMinus_rightSideMarkedIso_codeCellEquiv9 x w n q q' phi a)
        (rMinus_rightSideMarkedIso_codeCellEquiv9 x w n q q' phi b)))

end DirectedDistances.PaperProofs.Section5
