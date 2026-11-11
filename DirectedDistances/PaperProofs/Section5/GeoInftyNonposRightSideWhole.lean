/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideMarkedIso

/-! Code-side retained faces for the nonpositive right-side gluing. Face data are
read from the stored finite triangles and the hatted block, before transport
to the geometric side. Geometric face exhaustion is a separate obligation. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: the oriented cycle of a stored prefix triangle,
using only the decoded state's endpoint data. The endpoint test distinguishes
left and up creation, as in `triangleOrientedDarts`. -/
@[expose] def rMinusPrefixTriangleCycle (F : State) (t : ℕ × ℕ × ℕ) :
    (ℕ × Bool) × (ℕ × Bool) × (ℕ × Bool) :=
  if F.east t.1 = F.east t.2.1 then
    ((t.1, false), (t.2.1, true), (t.2.2, false))
  else ((t.1, false), (t.2.2, true), (t.2.1, true))

/-- Helper toward Lemma 5.5: cyclic adjacency in an oriented triangle.
All three edges, including missing geometric edges, keep their identities. -/
@[expose] def rMinusTriangleStep
    (c : (ℕ × Bool) × (ℕ × Bool) × (ℕ × Bool))
    (d e : ℕ × Bool) : Prop :=
  (d = c.1 ∧ e = c.2.1) ∨ (d = c.2.1 ∧ e = c.2.2) ∨
    (d = c.2.2 ∧ e = c.1)

/-- Helper toward Lemma 5.5: retained finite-prefix face succession.
Only recorded triangles contribute; the finite exterior face does not. -/
@[expose] def rMinusPrefixFaceNext (F : State) (d e : ℕ × Bool) : Prop :=
  ∃ t ∈ F.triangles, rMinusTriangleStep (rMinusPrefixTriangleCycle F t) d e

/-- Helper toward Lemma 5.5: the decoded endpoint test gives exactly the
canonical finite-stage triangle cycle, with the same dart values. -/
theorem rMinusPrefixTriangleCycle_eq (w : ℕ → Fin 3) (n : ℕ)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ (kmswStage w n).triangles) :
    rMinusPrefixTriangleCycle (kmswStage w n) t =
      let c := triangleDartCycle w n t ht
      ((c.1.1.val, c.1.2), (c.2.1.1.val, c.2.1.2), (c.2.2.1.val, c.2.2.2)) := by
  have hb := triBound_stage w n t ht
  have ha := (edge_endpoints_eq w hb.1).2
  have he := (edge_endpoints_eq w hb.2.1).2
  simp only [rMinusPrefixTriangleCycle, triangleDartCycle, ha, he]
  split <;> rfl

private theorem rMinus_stageDart_val_injective (N : ℕ) :
    Function.Injective (fun d : StageDart N => (d.1.val, d.2)) := by
  intro a b hab
  exact Prod.ext (Fin.ext (congrArg Prod.fst hab)) (congrArg (fun z : ℕ × Bool => z.2) hab)

/-- Helper toward Lemma 5.5: a decoded prefix face step is the actual
finite-stage face successor, rather than an exterior rotation shortcut. -/
theorem rMinusPrefixFaceNext_faceSucc (w : ℕ → Fin 3) (n : ℕ)
    (d e : StageDart (kmswStage w n).nextEdge)
    (hde : rMinusPrefixFaceNext (kmswStage w n) (d.1.val, d.2) (e.1.val, e.2)) :
    (kmswMap w n).faceSucc d = e := by
  obtain ⟨t, ht, hs⟩ := hde
  rw [rMinusPrefixTriangleCycle_eq w n t ht] at hs
  have hc := triangleDartCycle_isFace w n t ht
  rcases hs with ⟨hd, he⟩ | ⟨hd, he⟩ | ⟨hd, he⟩
  · have hd' := rMinus_stageDart_val_injective _ hd
    have he' := rMinus_stageDart_val_injective _ he
    rw [hd', he']
    exact hc.1
  · have hd' := rMinus_stageDart_val_injective _ hd
    have he' := rMinus_stageDart_val_injective _ he
    rw [hd', he']
    exact hc.2.1
  · have hd' := rMinus_stageDart_val_injective _ hd
    have he' := rMinus_stageDart_val_injective _ he
    rw [hd', he']
    exact hc.2.2.1

/-- Helper toward Lemma 5.5: the intrinsic decoded retained-face relation.
Each witness is a whole face in one block, carried along that block's gluing
map. No face relation is defined by pulling back the geometric target. -/
@[expose] def rMinusCodeFaceNext (F : State) (M : GeometricSideSubmap)
    (d e : RMinusCodeGluedDart F M) : Prop :=
  (∃ a b : StageDart F.nextEdge,
    rMinusPrefixFaceNext F (a.1.val, a.2) (b.1.val, b.2) ∧
      rMinusCodePrefixDart F M a = d ∧ rMinusCodePrefixDart F M b = e) ∨
  (∃ a b : {z : ℕ × Bool // z.1 ∈ M.edges},
    M.faceNext a.val b.val ∧
      rMinusCodeHattedDart F M a = d ∧ rMinusCodeHattedDart F M b = e)

/-- Helper toward Lemma 5.5: every finite-prefix retained face step occurs
in the intrinsic decoded face relation. -/
theorem rMinusCodeFaceNext_prefix (F : State) (M : GeometricSideSubmap)
    (a b : StageDart F.nextEdge)
    (hab : rMinusPrefixFaceNext F (a.1.val, a.2) (b.1.val, b.2)) :
    rMinusCodeFaceNext F M (rMinusCodePrefixDart F M a)
      (rMinusCodePrefixDart F M b) := Or.inl ⟨a, b, hab, rfl, rfl⟩

/-- Helper toward Lemma 5.5: every hatted retained face step occurs in the
intrinsic decoded face relation, with both dart identities preserved. -/
theorem rMinusCodeFaceNext_hatted (F : State) (M : GeometricSideSubmap)
    (a b : {z : ℕ × Bool // z.1 ∈ M.edges}) (hab : M.faceNext a.val b.val) :
    rMinusCodeFaceNext F M (rMinusCodeHattedDart F M a)
      (rMinusCodeHattedDart F M b) := Or.inr ⟨a, b, hab, rfl, rfl⟩

/-- Helper toward Lemma 5.5: enlarging a KMSW prefix preserves each of its
recorded face steps, including the orientation determined by its endpoints. -/
theorem rMinusPrefixFaceNext_mono (w : ℕ → Fin 3) {n m : ℕ} (hnm : n ≤ m)
    {d e : ℕ × Bool} (hde : rMinusPrefixFaceNext (kmswStage w n) d e) :
    rMinusPrefixFaceNext (kmswStage w m) d e := by
  obtain ⟨t, ht, hs⟩ := hde
  have htm := triangles_sub_stage w hnm t ht
  refine ⟨t, htm, ?_⟩
  have hn := triBound_stage w n t ht
  have hm := triBound_stage w m t htm
  have heq : rMinusPrefixTriangleCycle (kmswStage w n) t =
      rMinusPrefixTriangleCycle (kmswStage w m) t := by
    simp only [rMinusPrefixTriangleCycle, (edge_endpoints_eq w hn.1).2,
      (edge_endpoints_eq w hn.2.1).2, (edge_endpoints_eq w hm.1).2,
      (edge_endpoints_eq w hm.2.1).2]
  exact heq ▸ hs

/-- Helper toward Lemma 5.5: a recorded prefix face step keeps its original
successor in the infinite map. Finite incidence is the existing requirement
for the infinite face permutation, not a face-identification premise. -/
theorem rMinusPrefixFaceNext_infFaceSucc (w : ℕ → Fin 3)
    (hf : KMSWFiniteIncidence w) (n : ℕ)
    (d e : StageDart (kmswStage w n).nextEdge)
    (hde : rMinusPrefixFaceNext (kmswStage w n) (d.1.val, d.2) (e.1.val, e.2)) :
    kmswInfFaceSucc w hf (d.1.val, d.2) = (e.1.val, e.2) := by
  obtain ⟨N, hN⟩ := kmswInfFaceSucc_eventually_eq_stage w hf (d.1.val, d.2)
  obtain ⟨hd, hsucc⟩ := hN (max n N) (le_max_right _ _)
  let d' : StageDart (kmswStage w (max n N)).nextEdge := (⟨d.1.val, hd⟩, d.2)
  let e' : StageDart (kmswStage w (max n N)).nextEdge :=
    (⟨e.1.val, e.1.isLt.trans_le (kmswStage_nextEdge_mono w (le_max_left _ _))⟩, e.2)
  have he := rMinusPrefixFaceNext_faceSucc w (max n N) d' e'
    (rMinusPrefixFaceNext_mono w (le_max_left _ _) hde)
  exact hsucc.trans (congrArg (fun z => (z.1.val, z.2)) he)

section GluedFaces

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "F" => kmswStage (shiftedStream W 0)
  (boundaryHitTime (shiftedStream W 0) h k)
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.right
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)

/-- Helper toward Lemma 5.5: the prefix dart gluing map, retaining its
allocated edge ID and its endpoint bit. -/
@[expose] noncomputable def rMinusGluedPrefixDart (d : StageDart (F).nextEdge) :
    RMinusGluedDart hτ hqMode :=
  ⟦Sum.inl ⟨(d.1.val, d.2), d.1.isLt⟩⟧

/-- Helper toward Lemma 5.5: the hatted dart gluing map. -/
@[expose] noncomputable def rMinusGluedHattedDart (d : {z : ℕ × Bool // z.1 ∈ (Q).edges}) :
    RMinusGluedDart hτ hqMode := ⟦Sum.inr d⟧

/-- Helper toward Lemma 5.5: the code-built face relation on the existing
glued cells. Its witnesses are retained prefix or hatted faces carried along
the gluing maps. In particular, the definition does not consult the geometric
side or its face relation. Whether these exhaust its retained faces is proved
only by the separate transport obligation below. -/
@[expose] noncomputable def rMinusGluedFaceNext :
    Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode) →
      Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode) → Prop
  | .inr d, .inr e =>
    (∃ a b : StageDart (F).nextEdge,
      rMinusPrefixFaceNext F (a.1.val, a.2) (b.1.val, b.2) ∧
        rMinusGluedPrefixDart hτ hqMode a = d ∧ rMinusGluedPrefixDart hτ hqMode b = e) ∨
    (∃ a b : {z : ℕ × Bool // z.1 ∈ (Q).edges},
      (Q).faceNext a.val b.val ∧
        rMinusGluedHattedDart hτ hqMode a = d ∧ rMinusGluedHattedDart hτ hqMode b = e)
  | _, _ => False

/-- Helper toward Lemma 5.5: prefix gluing commutes with the proved
intrinsic-code to geometric-quotient change of dart carrier. -/
theorem rMinusCodeToGluedDartEquiv_prefix (a : StageDart (F).nextEdge) :
    rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusCodePrefixDart F Q a) = rMinusGluedPrefixDart hτ hqMode a := by
  apply (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).injective
  apply Subtype.ext
  rw [rMinusCodeToGluedDartEquiv_equiv, rMinusCodeGluedDartEquiv_prefix]
  rfl

/-- Helper toward Lemma 5.5: hatted gluing commutes with the proved
intrinsic-code to geometric-quotient change of dart carrier. -/
theorem rMinusCodeToGluedDartEquiv_hatted (a : {z : ℕ × Bool // z.1 ∈ (Q).edges}) :
    rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusCodeHattedDart F Q a) = rMinusGluedHattedDart hτ hqMode a := by
  apply (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).injective
  apply Subtype.ext
  rw [rMinusCodeToGluedDartEquiv_equiv, rMinusCodeGluedDartEquiv_hatted]
  rfl

/-- Helper toward Lemma 5.5: the glued-cell face relation is exactly the
intrinsic two-block code relation after changing the dart carrier. -/
theorem rMinusGluedFaceNext_code_iff (d e : RMinusCodeGluedDart F Q) :
    rMinusGluedFaceNext hτ hqMode
      (.inr (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d))
      (.inr (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk e)) ↔
        rMinusCodeFaceNext F Q d e := by
  let E := rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
  have hP := rMinusCodeToGluedDartEquiv_prefix hτ hp P hqMode Tpath hfin hleft hk
  have hQ := rMinusCodeToGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk
  change
    ((∃ a b, rMinusPrefixFaceNext F (a.1.val, a.2) (b.1.val, b.2) ∧
      rMinusGluedPrefixDart hτ hqMode a = E d ∧ rMinusGluedPrefixDart hτ hqMode b = E e) ∨
    (∃ a b, (Q).faceNext a.val b.val ∧
      rMinusGluedHattedDart hτ hqMode a = E d ∧ rMinusGluedHattedDart hτ hqMode b = E e)) ↔ _
  dsimp only [E]
  simp only [← hP, ← hQ,
    (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).injective.eq_iff,
    rMinusCodeFaceNext]







































end GluedFaces

end DirectedDistances.PaperProofs.Section5

