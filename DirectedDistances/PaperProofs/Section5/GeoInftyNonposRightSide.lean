/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftySideVertices
public import DirectedDistances.PaperProofs.Section5.GeoInftyIndCodeLevel
import DirectedDistances.PaperProofs.Section5.GeoInftyHattedSideIso
import Mathlib.Order.Setoid.Basic
















public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.Probability
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Code" => (ℕ → Fin 3) × (ℕ → Option FiniteThinMap)
local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5: the two generating codes and their boundary index. -/
structure RMinusSidePresentation (x : XDP) where
  boundaryIndex : ℤ
  code : Code

/-- Helper toward Lemma 5.5: the explicit cylinder sigma algebra, including
all coordinates of both codes and the boundary index. -/
noncomputable instance (x : XDP) : MeasurableSpace (RMinusSidePresentation x) :=
  MeasurableSpace.comap (fun r => (r.boundaryIndex, r.code)) inferInstance

/-- Helper toward Lemma 5.5: retain both blocks with their actual index. -/
@[expose] def decodeRMinus (x : XDP) (k : ℤ) (c : Code) :
    RMinusSidePresentation x := ⟨k, c⟩

/-- Helper toward Lemma 5.5: measurability for the specified cylinder algebra. -/
theorem measurable_decodeRMinus (x : XDP) (k : ℤ) :
    Measurable (decodeRMinus x k) :=
  measurable_comap_iff.mpr (measurable_const.prodMk measurable_id)

/-- Helper toward Lemma 5.5: neither code block loses any coordinate. -/
theorem decodeRMinus_code (x : XDP) (k : ℤ) (c : Code) :
    (decodeRMinus x k c).code = c := rfl

/-- Helper toward Lemma 5.5: the boundary index is retained exactly. -/
theorem decodeRMinus_boundaryIndex (x : XDP) (k : ℤ) (c : Code) :
    (decodeRMinus x k c).boundaryIndex = k := rfl

/-- Helper toward Lemma 5.5: reading both codes and the index is measurable. -/
theorem measurable_rMinusSidePresentation_coordinates (x : XDP) :
    Measurable (fun r : RMinusSidePresentation x => (r.boundaryIndex, r.code)) :=
  comap_measurable _

/-- Helper toward Lemma 5.5: decoding recovers every presentation. -/
theorem RMinusSidePresentation.decode_code {x : XDP}
    (r : RMinusSidePresentation x) :
    decodeRMinus x r.boundaryIndex r.code = r := rfl

/-- Helper toward Lemma 5.5: the observed two-block reader is a.e. measurable. -/
theorem aemeasurable_decodeRMinus_rightSideObsNonpos (x : XDP) (k : ℤ) :
    AEMeasurable (fun W => decodeRMinus x k (rightSideObsNonpos x k W))
      wholePlaneIIDCodeMeasure :=
  (measurable_decodeRMinus x k).comp_aemeasurable
    ((aemeasurable_boundaryFourObservations x k 0).prodMk
      (aemeasurable_boundaryFourObservations x k 2))

/-- Helper toward Lemma 5.5: coherent equal right codes give a complete
marked isomorphism of the hatted block, before attaching the finite prefix. -/
theorem rMinus_rightSideCode_markedIso_of_eq (x : XDP) (q q' : Coherent x)
    (hc : thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q'.1) :
    Nonempty (GeometricSideMarkedIso
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q')) := by
  obtain ⟨I⟩ :=
    ((DirectedDistances.PaperProofs.SourceResults.thin_ind x).2.1 .right q q').mp hc
  exact ⟨I.whole⟩

/-- Helper toward Lemma 5.5: partial realization of the hatted right block.
Invalid hatted codes have no realization. This does not realize the glued side. -/
@[expose] noncomputable def RMinusSidePresentation.hattedRealization {x : XDP}
    (r : RMinusSidePresentation x) : Option GeometricSideSubmap :=
  if h : ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 = r.code.2
  then some (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime
    .right h.choose)
  else none

/-- Helper toward Lemma 5.5: invalid hatted codes return no submap. -/
theorem RMinusSidePresentation.hattedRealization_eq_none_iff {x : XDP}
    (r : RMinusSidePresentation x) :
    r.hattedRealization = none ↔ ¬ ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 = r.code.2 := by
  unfold RMinusSidePresentation.hattedRealization
  split <;> simp only [Option.some_ne_none, not_true_eq_false, not_false_eq_true, *]

/-- Helper toward Lemma 5.5: every returned hatted block has exactly its code. -/
theorem RMinusSidePresentation.hattedRealization_eq_some_spec {x : XDP}
    (r : RMinusSidePresentation x) (M : GeometricSideSubmap)
    (hM : r.hattedRealization = some M) :
    ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 = r.code.2 ∧
      geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q = M := by
  unfold RMinusSidePresentation.hattedRealization at hM
  split at hM
  · rename_i h
    exact ⟨h.choose, h.choose_spec, Option.some.inj hM⟩
  · cases hM

/-- Helper toward Lemma 5.5: the observed hatted block exists on its source domain. -/
theorem decodeRMinus_rightSideObsNonpos_hattedRealization_isSome (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) (hq : boundaryFutureHattedPath k W ∈ Coherent x) :
    (decodeRMinus x k (rightSideObsNonpos x k W)).hattedRealization.isSome := by
  unfold RMinusSidePresentation.hattedRealization
  rw [dite_eq_left ⟨⟨boundaryFutureHattedPath k W, hq⟩, rfl⟩]
  rfl

/-- Helper toward Lemma 5.5: the observed hatted block exists almost surely. -/
theorem ae_decodeRMinus_rightSideObsNonpos_hattedRealization_isSome (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (decodeRMinus x k (rightSideObsNonpos x k W)).hattedRealization.isSome := by
  filter_upwards [(boundaryFutureThinSides_package x k).2.2.2.2.2] with W hq
  exact decodeRMinus_rightSideObsNonpos_hattedRealization_isSome x k W hq

/-- Helper toward Lemma 5.5: the partial hatted realization is marked-isomorphic
to the actual coherent hatted right block. -/
theorem boundaryFutureHattedRight_markedIso_decodeRMinus (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) (hq : boundaryFutureHattedPath k W ∈ Coherent x) :
    Nonempty (GeometricSideMarkedIso
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right
        ⟨boundaryFutureHattedPath k W, hq⟩)
      ((decodeRMinus x k (rightSideObsNonpos x k W)).hattedRealization.get
        (decodeRMinus_rightSideObsNonpos_hattedRealization_isSome x k W hq))) := by
  let r := decodeRMinus x k (rightSideObsNonpos x k W)
  have hs := decodeRMinus_rightSideObsNonpos_hattedRealization_isSome x k W hq
  obtain ⟨q', hcode, hside⟩ := r.hattedRealization_eq_some_spec
    (r.hattedRealization.get hs) (Option.some_get hs).symm
  rw [← hside]
  exact rMinus_rightSideCode_markedIso_of_eq x ⟨boundaryFutureHattedPath k W, hq⟩ q' hcode.symm

/-- Helper toward Lemma 5.5: restore the dummy coordinate used by code walks. -/
@[expose] def rMinusPrefixPath (p : ℕ → Fin 3) : ℕ → Fin 3 :=
  fun i => if i = 0 then 0 else p (i - 1)

/-- Helper toward Lemma 5.5: a finite stopping event depends only on the
codes before its frontier. This uses the proved stopping-time sigma algebra. -/
theorem rMinus_boundaryCodeStoppingTime_eq_of_prefix (n : ℕ)
    (j : ℤ) (ω ω' : ℕ → Fin 3)
    (hω : boundaryCodeStoppingTime j ω = n)
    (hp : ∀ i < n, ω (i + 1) = ω' (i + 1)) :
    boundaryCodeStoppingTime j ω' = n := by
  obtain ⟨A, _, hA⟩ := measurableSet_codePast_boundaryCodeStoppingTime_eq j n
  have he : (fun i : Fin n => ω (i.val + 1)) =
      (fun i : Fin n => ω' (i.val + 1)) := funext fun i => hp i.val i.isLt
  have hmem : ω ∈ {w | boundaryCodeStoppingTime j w = n} := hω
  change ω' ∈ {w | boundaryCodeStoppingTime j w = n}
  rw [← hA] at hmem ⊢
  change (fun i : Fin n => ω (i.val + 1)) ∈ A at hmem
  change (fun i : Fin n => ω' (i.val + 1)) ∈ A
  rwa [he] at hmem

/-- Helper toward Lemma 5.5: a valid prefix is exactly a finite stopped
code with the specified zero padding. No infinite stopping frontier is coerced
to a finite prefix. -/
@[expose] def RMinusSidePresentation.prefixValid {x : XDP}
    (r : RMinusSidePresentation x) : Prop :=
  ∃ n : ℕ, boundaryCodeStoppingTime r.boundaryIndex (rMinusPrefixPath r.code.1) = n ∧
    ∀ i, n ≤ i → r.code.1 i = 0

/-- Helper toward Lemma 5.5: the stopping frontier is unique. -/
theorem rMinus_prefix_frontier_unique (k : ℤ) (p : ℕ → Fin 3) (m n : ℕ)
    (hm : boundaryCodeStoppingTime k (rMinusPrefixPath p) = m)
    (hn : boundaryCodeStoppingTime k (rMinusPrefixPath p) = n) : m = n := by
  exact_mod_cast hm.symm.trans hn

/-- Helper toward Lemma 5.5: realize a valid finite prefix by its KMSW
stage. Invalid prefixes have no realization. -/
@[expose] noncomputable def RMinusSidePresentation.prefixRealization {x : XDP}
    (r : RMinusSidePresentation x) : Option State :=
  if h : r.prefixValid then some (kmswStage r.code.1 h.choose) else none

/-- Helper toward Lemma 5.5: precisely invalid prefix codes return `none`. -/
theorem RMinusSidePresentation.prefixRealization_eq_none_iff {x : XDP}
    (r : RMinusSidePresentation x) :
    r.prefixRealization = none ↔ ¬ r.prefixValid := by
  unfold RMinusSidePresentation.prefixRealization
  split <;> simp only [Option.some_ne_none, not_true_eq_false, not_false_eq_true, *]

/-- Helper toward Lemma 5.5: every returned finite prefix realizes its
entire stopped code, with a finite frontier and exactly the specified padding. -/
theorem RMinusSidePresentation.prefixRealization_eq_some_spec {x : XDP}
    (r : RMinusSidePresentation x) (F : State)
    (hF : r.prefixRealization = some F) :
    ∃ n : ℕ, boundaryCodeStoppingTime r.boundaryIndex (rMinusPrefixPath r.code.1) = n ∧
      (∀ i, n ≤ i → r.code.1 i = 0) ∧ kmswStage r.code.1 n = F := by
  unfold RMinusSidePresentation.prefixRealization at hF
  split at hF
  · rename_i h
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, Option.some.inj hF⟩
  · cases hF

/-- Helper toward Lemma 5.5: stopped codes recover their finite KMSW
stage exactly, independently of the codes after the stopping frontier. -/
theorem rMinus_stopped_prefix_stage (x : XDP) (k : ℤ) (ω : ℕ → Fin 3) (n : ℕ)
    (hω : boundaryCodeStoppingTime k ω = n) (c : ℕ → Option FiniteThinMap) :
    (decodeRMinus x k (codePastVector (boundaryCodeStoppingTime k) ω, c)).prefixRealization =
      some (kmswStage (fun i => ω (i + 1)) n) := by
  let p := codePastVector (boundaryCodeStoppingTime k) ω
  have hp (i : ℕ) (hi : i < n) : p i = ω (i + 1) := by
    simp only [p, codePastVector, hω, ENat.natCast_lt_natCast, ite_eq_left hi]
  have hpad (i : ℕ) (hi : n ≤ i) : p i = 0 := by
    simp only [p, codePastVector, hω, ENat.natCast_lt_natCast, not_lt.mpr hi, ↓reduceIte]
  have hstop : boundaryCodeStoppingTime k (rMinusPrefixPath p) = n := by
    apply rMinus_boundaryCodeStoppingTime_eq_of_prefix n k ω _ hω
    intro i hi
    simpa only [rMinusPrefixPath, Nat.add_one_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel] using (hp i hi).symm
  have hv : (decodeRMinus x k (p, c)).prefixValid := ⟨n, hstop, hpad⟩
  unfold RMinusSidePresentation.prefixRealization
  rw [dite_eq_left hv]
  congr 1
  have hn : hv.choose = n :=
    rMinus_prefix_frontier_unique k p hv.choose n hv.choose_spec.1 hstop
  rw [hn]
  exact kmswStage_congr hp

/-- Helper toward Lemma 5.5: source boundary-hit witnesses give a finite
extended stopping frontier, including the root index zero. -/
theorem rMinus_boundaryCodeStoppingTime_eq_boundaryHitTime (k : ℤ)
    (ω : ℕ → Fin 3) (h : BoundaryHitWitnesses (fun i => ω (i + 1))) :
    boundaryCodeStoppingTime k ω =
      (boundaryHitTime (fun i => ω (i + 1)) h k : ℕ∞) := by
  by_cases hk0 : k = 0
  · subst k
    simp only [boundaryCodeStoppingTime, boundaryHitTime_zero]
    rfl
  · by_cases hk : 0 < k
    · simp only [boundaryCodeStoppingTime, ite_eq_right hk0, ite_eq_left hk]
      exact codeSndFirstHit_eq_boundaryHitTime ω h (by omega)
    · simp only [boundaryCodeStoppingTime, ite_eq_right hk0, ite_eq_right hk]
      exact codeFstFirstHit_eq_boundaryHitTime ω h (by omega)

/-- Helper toward Lemma 5.5: intrinsic shared-boundary gluing of a finite
prefix and a hatted right block. Ordered boundary edge IDs, including the
active prefix edge at index zero, determine every generating identification. -/
@[expose] def rMinusCodeEdgeGluing (F : State) (M : GeometricSideSubmap) :
    Sum {e : ℕ // e < F.nextEdge} M.edges →
      Sum {e : ℕ // e < F.nextEdge} M.edges → Prop
  | .inl a, .inr b => ∃ i, (F.active :: F.UR)[i]? = some a.val ∧
      (M.boundary i).1 = b.val
  | _, _ => False

/-- Helper toward Lemma 5.5: the equivalence closure identifies exactly
the named boundary edge pairs, independently of any whole-plane embedding. -/
@[expose] def rMinusCodeEdgeSetoid (F : State) (M : GeometricSideSubmap) :
    Setoid (Sum {e : ℕ // e < F.nextEdge} M.edges) :=
  Relation.EqvGen.setoid (rMinusCodeEdgeGluing F M)

/-- Helper toward Lemma 5.5: the intrinsic two-block glued edge carrier. -/
abbrev RMinusCodeGluedEdge (F : State) (M : GeometricSideSubmap) :=
  Quotient (rMinusCodeEdgeSetoid F M)

/-- Helper toward Lemma 5.5: the realized blocks of the intrinsic edge
gluing. The remaining vertex, rotation and face assembly is not a field or
an assumption of this structure. -/
structure RMinusRealizedBlocks where
  finitePrefix : State
  hatted : GeometricSideSubmap

/-- Helper toward Lemma 5.5: the edge carrier is the actual boundary-ID
quotient of the two realized blocks. -/
abbrev RMinusRealizedBlocks.edges (b : RMinusRealizedBlocks) :=
  RMinusCodeGluedEdge b.finitePrefix b.hatted

/-- Helper toward Lemma 5.5: realize both code blocks only when both
individual realizations exist. Invalid codes never receive default blocks. -/
@[expose] noncomputable def RMinusSidePresentation.blocksRealization {x : XDP}
    (r : RMinusSidePresentation x) : Option RMinusRealizedBlocks :=
  r.prefixRealization.bind fun F => r.hattedRealization.map fun M => ⟨F, M⟩

/-- Helper toward Lemma 5.5: exact specification of the two returned blocks. -/
theorem RMinusSidePresentation.blocksRealization_eq_some_iff {x : XDP}
    (r : RMinusSidePresentation x) (F : State) (M : GeometricSideSubmap) :
    r.blocksRealization = some ⟨F, M⟩ ↔
      r.prefixRealization = some F ∧ r.hattedRealization = some M := by
  unfold RMinusSidePresentation.blocksRealization
  cases hp : r.prefixRealization with
  | none => simp only [Option.bind_none, reduceCtorEq, false_and]
  | some G =>
    cases hq : r.hattedRealization with
    | none => simp only [Option.bind_some, Option.map_none, reduceCtorEq, and_false]
    | some N =>
      simp only [Option.bind_some, Option.map_some, Option.some.injEq,
        RMinusRealizedBlocks.mk.injEq]

/-- Helper toward Lemma 5.5: precisely the invalid code blocks have no
two-block realization; neither branch assigns an arbitrary geometric map. -/
theorem RMinusSidePresentation.blocksRealization_eq_none_iff {x : XDP}
    (r : RMinusSidePresentation x) :
    r.blocksRealization = none ↔ ¬ r.prefixValid ∨ ¬ ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.1 = r.code.2 := by
  rw [← r.prefixRealization_eq_none_iff, ← r.hattedRealization_eq_none_iff]
  unfold RMinusSidePresentation.blocksRealization
  cases r.prefixRealization <;> cases r.hattedRealization <;> simp only
    [Option.bind_none, Option.bind_some, Option.map_none, Option.map_some,
      Option.some_ne_none, true_or, false_or]

section GeometricGluing

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ Coherent
    (if longest then XDP.ldp else XDP.sdp))
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "S" => m0GeodesicSide hp P ThinMapSide.right
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.right
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "U" => boundaryGluingFutureStream W h k
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "VH" => boundaryGluingHatVertexMap W h k hτ
local notation "F" => kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)

/-- Helper toward Lemma 5.5: the observed prefix decoder returns exactly
the actual stopped KMSW stage, rather than any default stage. -/
theorem decodeRMinus_rightSideObsNonpos_prefixRealization (x : XDP) :
    (decodeRMinus x k (rightSideObsNonpos x k W)).prefixRealization = some F := by
  have hω : BoundaryHitWitnesses (fun i => shiftedCodePath W 0 (i + 1)) := by
    simpa only [shiftedCodePath, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] using h
  have ht := rMinus_boundaryCodeStoppingTime_eq_boundaryHitTime k (shiftedCodePath W 0) hω
  have ht' : boundaryCodeStoppingTime k (shiftedCodePath W 0) =
      (boundaryHitTime (shiftedStream W 0) h k : ℕ∞) := by
    simpa only [shiftedCodePath, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] using ht
  exact rMinus_stopped_prefix_stage x k (shiftedCodePath W 0) _ ht'
    (rightSideObsNonpos x k W).2

include h in
/-- Helper toward Lemma 5.5: the observed two-block realization exists
on exactly the existing boundary-hit and coherent-hatted source domain. -/
theorem decodeRMinus_rightSideObsNonpos_blocksRealization_isSome (x : XDP)
    (hq : boundaryFutureHattedPath k W ∈ Coherent x) :
    (decodeRMinus x k (rightSideObsNonpos x k W)).blocksRealization.isSome := by
  have hs := decodeRMinus_rightSideObsNonpos_hattedRealization_isSome x k W hq
  unfold RMinusSidePresentation.blocksRealization
  rw [decodeRMinus_rightSideObsNonpos_prefixRealization (h := h) x, Option.bind_some]
  cases hh : (decodeRMinus x k (rightSideObsNonpos x k W)).hattedRealization with
  | none => rw [hh] at hs; cases hs
  | some M => rfl

/-- Helper toward Lemma 5.5: the two edge-ID blocks before gluing. -/
abbrev RMinusBlockEdge := Sum (boundaryGluingPrefixEdges W h k) (Q).edges

/-- Helper toward Lemma 5.5: finite prefix edge IDs are already run-zero
IDs; the hatted block uses the proved hat-then-future edge embedding. -/
@[expose] noncomputable def rMinusBlockEdgeImage :
    RMinusBlockEdge (h := h) hqMode → ℕ := Sum.elim Subtype.val (fun e => EH e.val)

/-- Helper toward Lemma 5.5: geometric gluing identifies edge IDs exactly
when the two block embeddings agree. Multiedges remain distinct. -/
abbrev RMinusGluedEdge := Quotient (Setoid.ker (rMinusBlockEdgeImage hτ hqMode))

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the two-block edge image is exactly the actual
nonpositive right-side geometric edge carrier. -/
theorem rMinusBlockEdgeImage_range :
    Set.range (rMinusBlockEdgeImage hτ hqMode) = (S).edges := by
  rw [(boundaryGluing_nonpos_side_identities W h k hτ longest hp P
    hqMode Tpath hfin hleft hk).2]
  ext e
  constructor
  · rintro ⟨a | b, rfl⟩
    · exact Or.inl a.property
    · exact Or.inr ⟨b.val, b.property, rfl⟩
  · rintro (ha | ⟨b, hb, rfl⟩)
    · exact ⟨Sum.inl ⟨e, ha⟩, rfl⟩
    · exact ⟨Sum.inr ⟨b, hb⟩, rfl⟩

/-- Helper toward Lemma 5.5: the glued edge quotient bijects with the
actual right-side edges, retaining absent geometric edges. -/
@[expose] noncomputable def rMinusGluedEdgeEquiv :
    RMinusGluedEdge hτ hqMode ≃ (S).edges :=
  (Setoid.quotientKerEquivRange (rMinusBlockEdgeImage hτ hqMode)).trans
    (Set.equivOfEq (rMinusBlockEdgeImage_range hτ hp P hqMode Tpath hfin hleft hk))

/-- Helper toward Lemma 5.5: distinct prefix edge IDs cannot collapse. -/
theorem rMinusGluedEdge_prefix_injective :
    Function.Injective (fun a : boundaryGluingPrefixEdges W h k =>
      (⟦Sum.inl a⟧ : RMinusGluedEdge hτ hqMode)) := by
  intro a b hab
  exact Subtype.ext (Quotient.exact hab)

/-- Helper toward Lemma 5.5: distinct hatted edge IDs cannot collapse. -/
theorem rMinusGluedEdge_hatted_injective :
    Function.Injective (fun a : (Q).edges =>
      (⟦Sum.inr a⟧ : RMinusGluedEdge hτ hqMode)) := by
  intro a b hab
  exact Subtype.ext (boundaryGluingHatEdgeMap_injective W h k hτ (Quotient.exact hab))

/-- Helper toward Lemma 5.5: cross-block equality is equality of geometric
edge IDs through the hat-then-future embedding, not equality of endpoints. -/
theorem rMinusGluedEdge_cross_eq_iff
    (a : boundaryGluingPrefixEdges W h k) (b : (Q).edges) :
    (⟦Sum.inl a⟧ : RMinusGluedEdge hτ hqMode) = ⟦Sum.inr b⟧ ↔ a.val = EH b.val := by
  rw [Quotient.eq]
  rfl

include hfin in
/-- Helper toward Lemma 5.5: the shared geometric edge IDs are precisely
the stopped upper-right boundary, including its active edge at index zero. -/
theorem rMinus_shared_edges :
    boundaryGluingPrefixEdges W h k ∩ EH '' (Q).edges =
      boundaryGluingUpperRightEdges W h k :=
  boundaryGluingPrefixEdges_inter_rightHatEdges_eq_upperRight W h k hτ
    (if longest then XDP.ldp else XDP.sdp) hqMode hfin

/-- Helper toward Lemma 5.5: the two vertex blocks before geometric gluing. -/
abbrev RMinusBlockVertex := Sum (boundaryGluingPrefixVertices W h k) (Q).vertices

/-- Helper toward Lemma 5.5: the actual vertex image of each block. -/
@[expose] noncomputable def rMinusBlockVertexImage :
    RMinusBlockVertex (h := h) hqMode → ℕ := Sum.elim Subtype.val (fun v => VH v.val)

/-- Helper toward Lemma 5.5: the geometric vertex quotient is separate
from the edge quotient and retains all shared-boundary vertices. -/
abbrev RMinusGluedVertex := Quotient (Setoid.ker (rMinusBlockVertexImage hτ hqMode))

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the geometric vertex image is the complete
right-side carrier, including the root and geodesic seam. -/
theorem rMinusBlockVertexImage_range :
    Set.range (rMinusBlockVertexImage hτ hqMode) = (S).vertices := by
  rw [boundaryGluing_nonpos_right_vertices hτ hp P hqMode Tpath hfin hleft hk]
  ext v
  constructor
  · rintro ⟨a | b, rfl⟩
    · exact Or.inl ⟨a.val, a.property, rfl⟩
    · exact Or.inr ⟨b.val, b.property, rfl⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact ⟨Sum.inl ⟨a, ha⟩, rfl⟩
    · exact ⟨Sum.inr ⟨b, hb⟩, rfl⟩

/-- Helper toward Lemma 5.5: the glued vertices biject with actual side vertices. -/
@[expose] noncomputable def rMinusGluedVertexEquiv :
    RMinusGluedVertex hτ hqMode ≃ (S).vertices :=
  (Setoid.quotientKerEquivRange (rMinusBlockVertexImage hτ hqMode)).trans
    (Set.equivOfEq (rMinusBlockVertexImage_range hτ hp P hqMode Tpath hfin hleft hk))

/-- Helper toward Lemma 5.5: both darts of every retained geometric edge. -/
abbrev RMinusBlockDart := Sum
  {d : ℕ × Bool // d.1 ∈ boundaryGluingPrefixEdges W h k}
  {d : ℕ × Bool // d.1 ∈ (Q).edges}

/-- Helper toward Lemma 5.5: the embeddings preserve the ordered endpoints
of both finite-prefix and hatted darts. No primed side correction is needed. -/
@[expose] noncomputable def rMinusBlockDartImage :
    RMinusBlockDart (h := h) hqMode → ℕ × Bool :=
  Sum.elim Subtype.val (fun d => (EH d.val.1, d.val.2))

/-- Helper toward Lemma 5.5: the geometric dart quotient retains edge IDs
and side bits, also on missing geometric edges. -/
abbrev RMinusGluedDart := Quotient (Setoid.ker (rMinusBlockDartImage hτ hqMode))

/-- Helper toward Lemma 5.5: local incidence before quotienting. -/
@[expose] noncomputable def rMinusBlockDartEndpoint :
    RMinusBlockDart (h := h) hqMode → RMinusBlockVertex (h := h) hqMode
  | .inl d => .inl ⟨if d.val.2 then (F).east d.val.1 else (F).west d.val.1, by
      have he := kmswStage_endpoints_lt_nextVertex (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k) d.val.1 d.property
      cases hb : d.val.2
      · simpa only [hb, Bool.false_eq_true, ↓reduceIte,
          boundaryGluingPrefixVertices, Set.mem_ofPred_eq] using he.1
      · simpa only [hb, ↓reduceIte, boundaryGluingPrefixVertices,
          Set.mem_ofPred_eq] using he.2⟩
  | .inr d => .inr ⟨if d.val.2 then (Q).east d.val.1 else (Q).west d.val.1, by
      have he := geometricSideSubmap_endpoints
        (if longest then XDP.ldp else XDP.sdp) renewalTime
        renewalTime_positiveSuccessTime .right
        ⟨boundaryFutureHattedPath k W, hqMode⟩ d.val.1 d.property
      cases hb : d.val.2
      · simpa only [hb, Bool.false_eq_true, ↓reduceIte] using he.1
      · simpa only [hb, ↓reduceIte] using he.2⟩

/-- Helper toward Lemma 5.5: the local block endpoint maps agree with
run-zero incidence for every geometric edge, not just directed edges. -/
theorem rMinusBlockDartEndpoint_image (d : RMinusBlockDart (h := h) hqMode) :
    rMinusBlockVertexImage hτ hqMode (rMinusBlockDartEndpoint (h := h) hqMode d) =
      kmswLimitDartVertex (shiftedStream W 0) (rMinusBlockDartImage hτ hqMode d) := by
  cases d with
  | inl d =>
    have he := edge_endpoints_eq (shiftedStream W 0) d.property
    change (if d.val.2 then (F).east d.val.1 else (F).west d.val.1) =
      if d.val.2 then edgeEast (shiftedStream W 0) d.val.1
        else edgeWest (shiftedStream W 0) d.val.1
    split
    · exact he.2
    · exact he.1
  | inr d =>
    have he := boundaryGluing_hat_edge_endpoints W h k hτ d.val.1
    change VH (if d.val.2 then edgeEast
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) d.val.1
      else edgeWest (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) d.val.1) =
        if d.val.2 then edgeEast (shiftedStream W 0) (EH d.val.1)
          else edgeWest (shiftedStream W 0) (EH d.val.1)
    rw [boundaryGluing_decoded_stream W h k hτ]
    split
    · exact he.2.symm
    · exact he.1.symm

/-- Helper toward Lemma 5.5: incidence descends to the glued geometric cells. -/
@[expose] noncomputable def rMinusGluedDartEndpoint :
    RMinusGluedDart hτ hqMode → RMinusGluedVertex hτ hqMode :=
  Quotient.lift (fun d => ⟦rMinusBlockDartEndpoint (h := h) hqMode d⟧) (by
    intro a b hab
    apply Quotient.sound
    change rMinusBlockVertexImage hτ hqMode (rMinusBlockDartEndpoint (h := h) hqMode a) =
      rMinusBlockVertexImage hτ hqMode (rMinusBlockDartEndpoint (h := h) hqMode b)
    rw [rMinusBlockDartEndpoint_image hτ hqMode a,
      rMinusBlockDartEndpoint_image hτ hqMode b]
    exact congrArg (kmswLimitDartVertex (shiftedStream W 0)) hab)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the dart image is the full actual side dart carrier. -/
theorem rMinusBlockDartImage_range :
    Set.range (rMinusBlockDartImage hτ hqMode) =
      {d : ℕ × Bool | d.1 ∈ (S).edges} := by
  ext d
  constructor
  · rintro ⟨a | b, rfl⟩
    · have he : a.val.1 ∈ Set.range (rMinusBlockEdgeImage hτ hqMode) :=
        ⟨Sum.inl ⟨a.val.1, a.property⟩, rfl⟩
      rwa [rMinusBlockEdgeImage_range hτ hp P hqMode Tpath hfin hleft hk] at he
    · have he : EH b.val.1 ∈ Set.range (rMinusBlockEdgeImage hτ hqMode) :=
        ⟨Sum.inr ⟨b.val.1, b.property⟩, rfl⟩
      rwa [rMinusBlockEdgeImage_range hτ hp P hqMode Tpath hfin hleft hk] at he
  · intro hd
    have he : d.1 ∈ Set.range (rMinusBlockEdgeImage hτ hqMode) := by
      rw [rMinusBlockEdgeImage_range hτ hp P hqMode Tpath hfin hleft hk]
      exact hd
    obtain ⟨a | b, ha⟩ := he
    · exact ⟨Sum.inl ⟨(a.val, d.2), a.property⟩, Prod.ext ha rfl⟩
    · exact ⟨Sum.inr ⟨(b.val, d.2), b.property⟩, Prod.ext ha rfl⟩

/-- Helper toward Lemma 5.5: the dart quotient bijects with actual side darts. -/
@[expose] noncomputable def rMinusGluedDartEquiv :
    RMinusGluedDart hτ hqMode ≃ {d : ℕ × Bool // d.1 ∈ (S).edges} :=
  (Setoid.quotientKerEquivRange (rMinusBlockDartImage hτ hqMode)).trans
    (Set.equivOfEq (rMinusBlockDartImage_range hτ hp P hqMode Tpath hfin hleft hk))

/-- Helper toward Lemma 5.5: equivalence of the geometric incidence cells.
This alone makes no assertion about rotation, faces or boundary marks. -/
@[expose] noncomputable def rMinusGluedCellEquiv :
    Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode) ≃
      GeometricSideCell S :=
  Equiv.sumCongr (rMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk)
    (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk)

/-- Helper toward Lemma 5.5: evaluate the vertex equivalence by its block image. -/
theorem rMinusGluedVertexEquiv_val (v : RMinusGluedVertex hτ hqMode) :
    (rMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk v).val =
      Setoid.kerLift (rMinusBlockVertexImage hτ hqMode) v := rfl

/-- Helper toward Lemma 5.5: evaluate the dart equivalence by its block image. -/
theorem rMinusGluedDartEquiv_val (d : RMinusGluedDart hτ hqMode) :
    (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val =
      Setoid.kerLift (rMinusBlockDartImage hτ hqMode) d := rfl

/-- Helper toward Lemma 5.5: the descended endpoint is actual incidence. -/
theorem rMinusGluedDartEndpoint_equiv (d : RMinusGluedDart hτ hqMode) :
    (rMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusGluedDartEndpoint hτ hqMode d)).val =
      kmswLimitDartVertex (shiftedStream W 0)
        (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val := by
  refine Quotient.inductionOn d ?_
  intro a
  exact rMinusBlockDartEndpoint_image hτ hqMode a

/-- Helper toward Lemma 5.5: local geometric dart reversal. -/
@[expose] def rMinusBlockDartReverse : RMinusBlockDart (h := h) hqMode → RMinusBlockDart (h := h) hqMode
  | .inl d => .inl ⟨(d.val.1, !d.val.2), d.property⟩
  | .inr d => .inr ⟨(d.val.1, !d.val.2), d.property⟩

/-- Helper toward Lemma 5.5: reversal commutes with both edge-ID embeddings. -/
theorem rMinusBlockDartReverse_image (d : RMinusBlockDart (h := h) hqMode) :
    rMinusBlockDartImage hτ hqMode (rMinusBlockDartReverse (h := h) hqMode d) =
      ((rMinusBlockDartImage hτ hqMode d).1, !(rMinusBlockDartImage hτ hqMode d).2) := by
  cases d <;> rfl

/-- Helper toward Lemma 5.5: opposition descends to glued darts. -/
@[expose] noncomputable def rMinusGluedDartReverse :
    RMinusGluedDart hτ hqMode → RMinusGluedDart hτ hqMode :=
  Quotient.lift (fun d => ⟦rMinusBlockDartReverse (h := h) hqMode d⟧) (by
    intro a b hab
    apply Quotient.sound
    change rMinusBlockDartImage hτ hqMode (rMinusBlockDartReverse (h := h) hqMode a) =
      rMinusBlockDartImage hτ hqMode (rMinusBlockDartReverse (h := h) hqMode b)
    rw [rMinusBlockDartReverse_image hτ hqMode a,
      rMinusBlockDartReverse_image hτ hqMode b]
    exact congrArg (fun d : ℕ × Bool => (d.1, !d.2)) hab)

/-- Helper toward Lemma 5.5: descended opposition is actual dart reversal. -/
theorem rMinusGluedDartReverse_equiv (d : RMinusGluedDart hτ hqMode) :
    (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusGluedDartReverse hτ hqMode d)).val =
      ((rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val.1,
        !(rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val.2) := by
  refine Quotient.inductionOn d ?_
  intro a
  exact rMinusBlockDartReverse_image hτ hqMode a

include hτ hk in
/-- Helper toward Lemma 5.5: at a nonpositive hit, future-edge presence
agrees with run-zero presence. The empty upper-left attachment is proved
internally, so no missing-boundary status is added as a premise. -/
theorem rMinus_future_present_iff (e : ℕ) :
    EdgePresent U e ↔ EdgePresent (shiftedStream W 0) (boundaryGluingEdgeMap W h k e) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  have hA : (kmswStage w t).UL.dropLast = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have hm : a ∈ boundaryGluingUpperLeftEdges W h k := ha
    rw [boundaryGluingUpperLeftEdges_of_nonpos W h k hk] at hm
    exact hm
  constructor
  · rintro ⟨n, he, hp⟩
    rw [boundaryGluingEdgeMap, kmswWindowEdgeMapInf_eq_stage w t n e he]
    exact ⟨t + n, (kmswWindowPatchData_rel w t n).edge_bound e he,
      (kmswWindowPatchData_rel w t n).present e he hp⟩
  · intro hp
    by_contra hn
    obtain ⟨N, hN⟩ := (m0Cut_not_present_iff_eventually_LL U
      (hatBoundaryHitWitnesses U hτ) e).mp hn
    apply ((m0Cut_not_present_iff_eventually_LL w h
      (boundaryGluingEdgeMap W h k e)).mpr ?_) hp
    refine ⟨t + N, fun n hn => ?_⟩
    let m := n - t
    have hm : N ≤ m := by dsimp [m]; omega
    have ht : t + m = n := by dsimp [m]; omega
    let D := kmswWindowPatchData w t m
    have hr := kmswWindowPatchData_rel w t m
    change KMSWWindowPatchRel (kmswStage w t) (kmswStage w (t + m))
      (kmswStage U m) D.φ D.A D.B D.YL D.YR D.XL D.XR at hr
    have hy : D.YL = [] := by
      have heq := hr.left_residual.symm.trans hA
      exact List.map_eq_nil_iff.mp (List.append_eq_nil_iff.mp heq).2
    have he : e ∈ D.XL := by
      have he := hN m hm
      rw [hr.ll_split, hy, List.append_nil] at he
      exact he
    have healloc : e < (kmswStage U m).nextEdge :=
      (kmswStage_boundary_ids_lt_nextEdge U m).2 e (by
        simp only [List.mem_append]
        exact Or.inl (Or.inr (hN m hm)))
    rw [← ht, boundaryGluingEdgeMap, kmswWindowEdgeMapInf_eq_stage w t m e healloc, hr.ll]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩)

/-- Helper toward Lemma 5.5: a lower-left geometric edge stays missing
in the infinite one-sided run. -/
theorem rMinus_LL_not_present (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).LL) : ¬ EdgePresent w e := by
  have hmono {m : ℕ} (hnm : n ≤ m) : e ∈ (kmswStage w m).LL := by
    induction m, hnm using Nat.le_induction with
    | base => exact he
    | succ m _ ih =>
      change e ∈ (kmswStep (kmswStage w m) (w m)).LL
      unfold kmswStep
      cases hc : kmswCodeStep (w m) with
      | up => exact ih
      | down => cases hs : (kmswStage w m).UR <;>
          simpa only [kmswStepOfStep, hs, State.addEdge] using ih
      | left =>
        cases hs : (kmswStage w m).UL.dropLast.reverse with
        | nil =>
          simpa only [kmswStepOfStep, hs, State.addEdge] using
            List.mem_cons_of_mem ((kmswStage w m).nextEdge + 1) ih
        | cons f fs => simpa only [kmswStepOfStep, hs, State.addEdge] using ih
  intro hpresent
  obtain ⟨m, hm⟩ := hpresent.eventually_present
  have hm' := hm (max m n) (Nat.le_max_left _ _)
  have hmissing := ((kmswStage_status w (max m n)).1 e hm'.1).mpr
    (Or.inr (hmono (Nat.le_max_right _ _)))
  rw [hm'.2] at hmissing
  cases hmissing

/-- Helper toward Lemma 5.5: directed tails are read from the finite stage
and the hatted side separately. A missing prefix edge is never oriented locally. -/
@[expose] noncomputable def rMinusBlockDartOriented :
    RMinusBlockDart (h := h) hqMode → Prop
  | .inl d => (F).present d.val.1 = true ∧ d.val.2 = false
  | .inr d => d.val.1 ∈ (Q).present ∧ d.val.2 = false

/-- Helper toward Lemma 5.5: a glued dart is directed precisely when it
has a directed representative in one of its two blocks. -/
@[expose] noncomputable def rMinusGluedDartOriented
    (d : RMinusGluedDart hτ hqMode) : Prop :=
  ∃ a : RMinusBlockDart (h := h) hqMode, ⟦a⟧ = d ∧
    rMinusBlockDartOriented (h := h) hqMode a

include hk in
/-- Helper toward Lemma 5.5: directed local representatives have directed
run-zero images, with their forward side unchanged. -/
theorem rMinusBlockDartOriented_image (d : RMinusBlockDart (h := h) hqMode)
    (hd : rMinusBlockDartOriented (h := h) hqMode d) :
    EdgePresent (shiftedStream W 0) (rMinusBlockDartImage hτ hqMode d).1 ∧
      (rMinusBlockDartImage hτ hqMode d).2 = false := by
  cases d with
  | inl d => exact ⟨⟨_, d.property, hd.1⟩, hd.2⟩
  | inr d =>
    have hpresent := hatCodes_edge_present U hτ d.val.1
    exact ⟨(rMinus_future_present_iff hτ hk _).mp
      (hatLimit_edge_incidence (hatLimitExplicitInput U hτ) hpresent).1, hd.2⟩

include hfin in
/-- Helper toward Lemma 5.5: every directed image has a directed local
representative. A missing upper-right prefix edge uses its identified hatted
representative; a lower-left edge cannot have a directed image. -/
theorem rMinusBlockDartOriented_preimage (d : RMinusBlockDart (h := h) hqMode)
    (hpresent : EdgePresent (shiftedStream W 0) (rMinusBlockDartImage hτ hqMode d).1)
    (hforward : (rMinusBlockDartImage hτ hqMode d).2 = false) :
    rMinusGluedDartOriented hτ hqMode ⟦d⟧ := by
  cases d with
  | inr d =>
    refine ⟨Sum.inr d, rfl, ?_, hforward⟩
    change EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) d.val.1
    rw [boundaryGluing_decoded_stream W h k hτ]
    exact hatCodes_edge_present U hτ d.val.1
  | inl d =>
    by_cases hpref : (F).present d.val.1 = true
    · exact ⟨Sum.inl d, rfl, hpref, hforward⟩
    · have hfalse : (F).present d.val.1 = false := Bool.eq_false_iff.mpr hpref
      rcases ((kmswStage_status (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k)).1 d.val.1 d.property).mp hfalse with
        hUR | hLL'
      · obtain ⟨b, hb, hab⟩ := boundaryGluingUpperRightEdges_subset_rightHatEdges W h k hτ
          (if longest then XDP.ldp else XDP.sdp) hqMode hfin (Or.inr hUR)
        refine ⟨Sum.inr ⟨(b, false), hb⟩, ?_, ?_, rfl⟩
        · apply Quotient.sound
          exact Prod.ext hab hforward.symm
        · change EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) b
          rw [boundaryGluing_decoded_stream W h k hτ]
          exact hatCodes_edge_present U hτ b
      · exact (rMinus_LL_not_present (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h k) d.val.1 hLL' hpresent).elim

/-- Helper toward Lemma 5.5: the hatted seam is retained in the right block. -/
theorem rMinus_hatted_seam_mem (i : ℕ) : ((Q).seam i).1 ∈ (Q).edges := by
  change _ ∈ ⋃ j, geometricAncestorEdges (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime .right
    ⟨boundaryFutureHattedPath k W, hqMode⟩ j
  rw [iUnion_geometricAncestorEdges]
  exact seamEdge_mem_sideEdges _ _ _ _ _ _ .right i

/-- Helper toward Lemma 5.5: the intrinsic hatted seam dart in the glued
geometric dart carrier, with its original index and edge ID. -/
@[expose] noncomputable def rMinusGluedSeam (i : ℕ) : RMinusGluedDart hτ hqMode :=
  ⟦Sum.inr ⟨(Q).seam i, rMinus_hatted_seam_mem hqMode i⟩⟧

/-- Helper toward Lemma 5.5: the proved incidence skeleton of the geometric
gluing, including its indexed seam. Rotation, face succession and the exterior
boundary are not yet specified by this partial relation. -/
@[expose] noncomputable def rMinusGluedIncidenceRelation :
    TruncationRelation →
      Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode) →
      Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode) → Prop
  | .vertex, .inl _, _ => True
  | .root, .inl v, _ => Setoid.kerLift (rMinusBlockVertexImage hτ hqMode) v = VH 0
  | .incident, .inr d, .inl v => rMinusGluedDartEndpoint hτ hqMode d = v
  | .opposite, .inr d, .inr e => rMinusGluedDartReverse hτ hqMode d = e
  | .oriented, .inr d, _ => rMinusGluedDartOriented hτ hqMode d
  | .seam i, .inr d, _ => rMinusGluedSeam hτ hqMode i = d
  | _, _, _ => False

local notation "Φ" => rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the geometric cell equivalence preserves the vertex tag. -/
theorem rMinusGluedCellEquiv_vertex_iff
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusGluedIncidenceRelation hτ hqMode .vertex u v ↔
      geometricSideRelation S .vertex (Φ u) (Φ v) := by
  cases u <;> cases v <;> rfl

/-- Helper toward Lemma 5.5: the hatted source gives the correct root of
the nonpositive right side. -/
theorem rMinusGluedCellEquiv_root_iff
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusGluedIncidenceRelation hτ hqMode .root u v ↔
      geometricSideRelation S .root (Φ u) (Φ v) := by
  cases u with
  | inl a =>
    change Setoid.kerLift (rMinusBlockVertexImage hτ hqMode) a = VH 0 ↔
      (rMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk a).val =
        boundaryVertex (shiftedStream W 0) h k
    rw [rMinusGluedVertexEquiv_val hτ hp P hqMode Tpath hfin hleft hk,
      boundaryGluingHatVertexMap_zero hτ]
  | inr d => cases v <;> rfl

/-- Helper toward Lemma 5.5: directed presence and forward orientation of
the glued darts agree with those of the actual nonpositive right side. -/
theorem rMinusGluedCellEquiv_oriented_iff
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusGluedIncidenceRelation hτ hqMode .oriented u v ↔
      geometricSideRelation S .oriented (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    change rMinusGluedDartOriented hτ hqMode d ↔
      EdgePresent (shiftedStream W 0)
        (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val.1 ∧
        (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val.2 = false
    constructor
    · rintro ⟨a, ha, hor⟩
      subst d
      exact rMinusBlockDartOriented_image hτ hqMode hk a hor
    · refine Quotient.inductionOn d ?_
      intro a ha
      exact rMinusBlockDartOriented_preimage hτ hqMode hfin a ha.1 ha.2

/-- Helper toward Lemma 5.5: the glued cell equivalence preserves the complete
incidence tag, using the proved local block endpoint identities. -/
theorem rMinusGluedCellEquiv_incident_iff
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusGluedIncidenceRelation hτ hqMode .incident u v ↔
      geometricSideRelation S .incident (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    cases v with
    | inr e => rfl
    | inl a =>
      change rMinusGluedDartEndpoint hτ hqMode d = a ↔
        kmswLimitDartVertex (shiftedStream W 0)
          (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val =
            (rMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk a).val
      rw [← rMinusGluedDartEndpoint_equiv hτ hp P hqMode Tpath hfin hleft hk d]
      constructor
      · intro he
        rw [he]
      · intro he
        apply (rMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk).injective
        exact Subtype.ext he

/-- Helper toward Lemma 5.5: the glued cell equivalence preserves opposite
darts, using edge IDs and their preserved side bits. -/
theorem rMinusGluedCellEquiv_opposite_iff
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusGluedIncidenceRelation hτ hqMode .opposite u v ↔
      geometricSideRelation S .opposite (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    cases v with
    | inl a => rfl
    | inr e =>
      change rMinusGluedDartReverse hτ hqMode d = e ↔
        ((rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val.1,
          !(rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val.2) =
            (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk e).val
      rw [← rMinusGluedDartReverse_equiv hτ hp P hqMode Tpath hfin hleft hk d]
      constructor
      · intro he
        rw [he]
      · intro he
        apply (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).injective
        exact Subtype.ext he

/-- Helper toward Lemma 5.5: the finite-only target tag is empty on both
the glued incidence skeleton and the actual whole side. -/
theorem rMinusGluedCellEquiv_target_iff
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusGluedIncidenceRelation hτ hqMode .target u v ↔
      geometricSideRelation S .target (Φ u) (Φ v) := by
  cases u <;> cases v <;> rfl

include Tpath hfin hleft in
/-- Helper toward Lemma 5.5: the indexed hatted geodesic seam maps to the
actual right-side seam with the same geometric edge ID and forward side. -/
theorem rMinus_hatted_seam_image (i : ℕ) :
    (EH ((Q).seam i).1, ((Q).seam i).2) = (S).seam i := by
  exact congrArg (fun e : ℕ => (e, false))
    ((boundaryGluing_geodesicIdentification W h k hτ longest hqMode
      hp Tpath P hfin hleft i).symm)

/-- Helper toward Lemma 5.5: every indexed glued seam tag agrees with
the actual nonpositive right-side seam tag. -/
theorem rMinusGluedCellEquiv_seam_iff (i : ℕ)
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusGluedIncidenceRelation hτ hqMode (.seam i) u v ↔
      geometricSideRelation S (.seam i) (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    change rMinusGluedSeam hτ hqMode i = d ↔
      (S).seam i = (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val
    have hs : (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
        (rMinusGluedSeam hτ hqMode i)).val = (S).seam i :=
      rMinus_hatted_seam_image hτ hp P hqMode Tpath hfin hleft i
    rw [← hs]
    constructor
    · intro he
      rw [he]
    · intro he
      apply (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).injective
      exact Subtype.ext he


include hτ in
/-- Helper toward Lemma 5.5: every finite-prefix upper-right edge is the
image of the raw future boundary edge with exactly the same list index.
This is an edge-ID statement, including the active edge at index zero. -/
theorem rMinus_future_upperRight_index (i a : ℕ)
    (ha : ((F).active :: (F).UR)[i]? = some a) :
    boundaryGluingEdgeMap W h k (kmswRightBoundaryEdge U i) = a := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  have hR : ∀ b : ℤ, ∃ n, R U n ≤ b := by
    intro b
    obtain ⟨n, hn⟩ := (hatBoundaryHitWitnesses U hτ).rightHit (max (-b) 1) (le_max_right _ _)
    exact ⟨n, by have hm := le_max_left (-b) 1; omega⟩
  obtain ⟨N, hN⟩ := kmswStage_LR_getElem?_eventually U hR i
  let e := kmswRightBoundaryEdge U i
  let m := max N e
  let D := kmswWindowPatchData w t m
  have hr := kmswWindowPatchData_rel w t m
  change KMSWWindowPatchRel (kmswStage w t) (kmswStage w (t + m))
    (kmswStage U m) D.φ D.A D.B D.YL D.YR D.XL D.XR at hr
  have hget : (kmswStage U m).LR[i]? = some e := hN m (le_max_left _ _)
  have hi : i < (0 :: D.YR).length := by
    by_cases hB : D.B = []
    · have hlen := congrArg List.length hr.right_residual
      have hai := (List.getElem?_eq_some_iff.mp ha).1
      simp only [hB, List.append_nil, List.length_map] at hlen
      change (F).UR.length = D.YR.length at hlen
      simp only [List.length_cons] at hai ⊢
      rw [hlen] at hai
      omega
    · have hXR := hr.xr_nil hB
      have hli := (List.getElem?_eq_some_iff.mp hget).1
      rw [hr.lr_split, hXR, List.append_nil] at hli
      exact hli
  have hget' : (0 :: D.YR)[i]? = some e := by
    rw [hr.lr_split, List.singleton_append, List.getElem?_append_left hi] at hget
    exact hget
  have hlist : (F).active :: (F).UR = (0 :: D.YR).map D.φ ++ D.B := by
    rw [hr.right_residual, List.map_cons, hr.root, List.cons_append]
  have hmap : ((F).active :: (F).UR)[i]? = some (D.φ e) := by
    rw [hlist, List.getElem?_append_left (by simpa only [List.length_map] using hi),
      List.getElem?_map, hget']
    rfl
  have he : e < (kmswStage U m).nextEdge :=
    (kmsw_edge_allocated_by_self U e).trans_le
      (kmswStage_nextEdge_mono U (le_max_right _ _))
  change kmswWindowEdgeMapInf w t e = a
  rw [kmswWindowEdgeMapInf_eq_stage w t m e he]
  exact Option.some.inj (hmap.symm.trans ha)

include hτ in
/-- Helper toward Lemma 5.5: the hatted right-boundary marks have their
literal KMSW boundary edge IDs. -/
theorem rMinus_hatted_boundary (i : ℕ) :
    ((Q).boundary i).1 = kmswRightBoundaryEdge (hatCodes U hτ) i := by
  rw [boundaryGluing_nonneg_right_boundary_index hqMode i]
  change kmswRightBoundaryEdge
    (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) i = _
  rw [boundaryGluing_decoded_stream W h k hτ]

include hτ in
/-- Helper toward Lemma 5.5: each intrinsic code gluing pair has the same
actual geometric edge ID in both blocks. -/
theorem rMinus_code_boundary_gluing (i a : ℕ)
    (ha : ((F).active :: (F).UR)[i]? = some a) :
    EH (((Q).boundary i).1) = a := by
  rw [rMinus_hatted_boundary hτ hqMode i]
  change boundaryGluingEdgeMap W h k
    (hatLimitEdgeMap U hτ (kmswRightBoundaryEdge (hatCodes U hτ) i)) = a
  rw [hattedSide_hatLimitEdgeMap_rightBoundaryEdge]
  exact rMinus_future_upperRight_index hτ i a ha

include hfin in
/-- Helper toward Lemma 5.5: cross-block equality holds exactly at a
shared upper-right boundary index. Equality of endpoints is never used. -/
theorem rMinus_cross_edge_eq_iff
    (a : boundaryGluingPrefixEdges W h k) (b : (Q).edges) :
    a.val = EH b.val ↔ ∃ i, ((F).active :: (F).UR)[i]? = some a.val ∧
      ((Q).boundary i).1 = b.val := by
  constructor
  · intro hab
    have hm : a.val ∈ boundaryGluingPrefixEdges W h k ∩ EH '' (Q).edges :=
      ⟨a.property, b.val, b.property, hab.symm⟩
    rw [rMinus_shared_edges hτ hqMode hfin] at hm
    have hmem : a.val ∈ (F).active :: (F).UR := by
      rcases hm with he | he
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons.mpr (Or.inr he)
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
    refine ⟨i, hi, ?_⟩
    apply boundaryGluingHatEdgeMap_injective W h k hτ
    exact (rMinus_code_boundary_gluing hτ hqMode i a.val hi).trans hab
  · rintro ⟨i, hi, hb⟩
    rw [← hb]
    exact (rMinus_code_boundary_gluing hτ hqMode i a.val hi).symm

include hfin in
/-- Helper toward Lemma 5.5: intrinsic boundary edge gluing is exactly
geometric edge-ID equality. There are no extra identifications of multiedges. -/
theorem rMinusCodeEdgeSetoid_eq_ker :
    rMinusCodeEdgeSetoid F Q = Setoid.ker (rMinusBlockEdgeImage hτ hqMode) := by
  apply le_antisymm
  · apply Setoid.eqvGen_le
    intro a b hab
    cases a with
    | inr a => cases b <;> exact hab.elim
    | inl a =>
      cases b with
      | inl b => exact hab.elim
      | inr b =>
        exact (rMinus_cross_edge_eq_iff hτ hqMode hfin a b).mpr hab
  · intro a b hab
    have hcross (a : boundaryGluingPrefixEdges W h k) (b : (Q).edges)
        (he : a.val = EH b.val) :
        rMinusCodeEdgeSetoid F Q (Sum.inl a) (Sum.inr b) :=
      Relation.EqvGen.rel _ _ ((rMinus_cross_edge_eq_iff hτ hqMode hfin a b).mp he)
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have he : a = b := Subtype.ext hab
        subst b
        exact Relation.EqvGen.refl _
      | inr b => exact hcross a b hab
    | inr a =>
      cases b with
      | inl b => exact Relation.EqvGen.symm _ _ (hcross b a hab.symm)
      | inr b =>
        have he : a = b := Subtype.ext
          (boundaryGluingHatEdgeMap_injective W h k hτ hab)
        subst b
        exact Relation.EqvGen.refl _

/-- Helper toward Lemma 5.5: the intrinsic finite-prefix/hatted edge
quotient bijects with the actual nonpositive right-side edge carrier. -/
@[expose] noncomputable def rMinusCodeGluedEdgeEquiv :
    RMinusCodeGluedEdge F Q ≃ (S).edges :=
  (Equiv.cast (congrArg Quotient (rMinusCodeEdgeSetoid_eq_ker hτ hqMode hfin))).trans
    (rMinusGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk)

end GeometricGluing

/-- Helper toward Lemma 5.5: both observed code blocks have realizations
almost surely. This asserts existence of the two blocks and their edge gluing,
not a marked isomorphism of the complete glued map. -/
theorem ae_decodeRMinus_rightSideObsNonpos_blocksRealization_isSome (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (decodeRMinus x k (rightSideObsNonpos x k W)).blocksRealization.isSome := by
  have hfin : ∀ᵐ ω ∂wholePlaneIIDCodeMeasure.map (fun W => shiftedCodePath W 0),
      boundaryCodeStoppingTime k ω < ⊤ := by
    rw [wholePlaneIIDCodeMeasure_map_shiftedPath]
    exact ae_boundaryCodeStoppingTime_lt_top k
  have hfin' := (Measure.tendsto_ae_map
    (measurable_shiftedCodePath 0).aemeasurable).eventually hfin
  filter_upwards [hfin', (boundaryFutureThinSides_package x k).2.2.2.2.2] with W hf hq
  have ht : boundaryCodeStoppingTime k (shiftedCodePath W 0) =
      ((boundaryCodeStoppingTime k (shiftedCodePath W 0)).toNat : ℕ∞) :=
    (ENat.natCast_toNat hf.ne).symm
  have hpref := rMinus_stopped_prefix_stage x k (shiftedCodePath W 0) _ ht
    (rightSideObsNonpos x k W).2
  have hhat := decodeRMinus_rightSideObsNonpos_hattedRealization_isSome x k W hq
  unfold RMinusSidePresentation.blocksRealization
  change ((decodeRMinus x k
    (codePastVector (boundaryCodeStoppingTime k) (shiftedCodePath W 0),
      (rightSideObsNonpos x k W).2)).prefixRealization.bind _).isSome = true
  rw [hpref, Option.bind_some]
  cases hh : (decodeRMinus x k (rightSideObsNonpos x k W)).hattedRealization with
  | none => rw [hh] at hhat; cases hhat
  | some M => rfl

/-- Helper toward Lemma 5.5: a single full-measure event gives two-block
realizations for both modes and every nonpositive index, including zero.
Full marked-map identification remains a separate obligation. -/
theorem ae_all_decodeRMinus_rightSideObsNonpos_blocksRealization_isSome :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ longest : Bool, ∀ k : ℤ, k ≤ 0 →
      (decodeRMinus (if longest then XDP.ldp else XDP.sdp) k
        (rightSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)).blocksRealization.isSome := by
  apply ae_all_iff.mpr
  intro longest
  apply ae_all_iff.mpr
  intro k
  filter_upwards [ae_decodeRMinus_rightSideObsNonpos_blocksRealization_isSome
    (if longest then XDP.ldp else XDP.sdp) k] with W hW
  intro _
  exact hW

/-- Helper toward Lemma 5.5: every indexed hatted boundary edge belongs to
the coherent block's geometric carrier. -/
theorem rMinus_hatted_boundary_mem (x : XDP) (q : Coherent x) (i : ℕ) :
    ((geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).boundary i).1 ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges := by
  apply Set.mem_iUnion.mpr
  refine ⟨i + 1, ?_⟩
  exact thinMapBoundaryDart_mem_sourceAncestorEdges _
    (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q) .right i

/-- Helper toward Lemma 5.5: the coherent hatted right rotation, as a genuine
first-return permutation on its geometric dart carrier. -/
@[expose] noncomputable def rMinusHattedRotation (x : XDP) (q : Coherent x) :
    Equiv.Perm {d : ℕ × Bool // d.1 ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges} :=
  drawingFirstReturnPerm
    (monotoneFamilyDrawing (boltzmannKMSWStream (pathCode q.val))
      (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
      (monotone_family_all _))
    {d | d.1 ∈ (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges}

/-- Helper toward Lemma 5.5: the hatted permutation has exactly the
first-return relation recorded by its coherent geometric block. -/
theorem rMinusHattedRotation_iff (x : XDP) (q : Coherent x)
    (d e : {d : ℕ × Bool // d.1 ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges}) :
    (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).rotation
      d.val e.val ↔ rMinusHattedRotation x q d = e := by
  let w := boltzmannKMSWStream (pathCode q.val)
  let hf := sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q
  let G := monotoneFamilyDrawing w hf (monotone_family_all w)
  let A : Set (ℕ × Bool) := {a | a.1 ∈
    (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges}
  let σ := kmswInfRot w hf
  let t := subsetFirstReturnTime σ A (drawingPositiveReturn G A) d
  have ht := subsetFirstReturnTime_spec σ A (drawingPositiveReturn G A) d
  change (∃ n : ℕ, 0 < n ∧ (σ : _ → _)^[n] d.val = e.val ∧
    ∀ j : ℕ, 0 < j → j < n → (σ : _ → _)^[j] d.val ∉ A) ↔ _
  constructor
  · rintro ⟨n, hn, he, hg⟩
    have htn : t ≤ n := Nat.find_min' (drawingPositiveReturn G A d)
      ⟨hn, he ▸ e.property⟩
    have hnt : n ≤ t := by
      by_contra hnot
      exact hg t ht.1 (by omega) ht.2.1
    have hteq : t = n := Nat.le_antisymm htn hnt
    apply Subtype.ext
    change (σ : _ → _)^[t] d.val = e.val
    rw [hteq]
    exact he
  · intro he
    exact ⟨t, ht.1, congrArg Subtype.val he, ht.2.2⟩


section RotationHelpers

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ Coherent
    (if longest then XDP.ldp else XDP.sdp))
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "S" => m0GeodesicSide hp P ThinMapSide.right
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.right
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "U" => boundaryGluingFutureStream W h k
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "VH" => boundaryGluingHatVertexMap W h k hτ
local notation "F" => kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)


local notation "qR" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode)

/-- Helper toward Lemma 5.5: the future embedding is a first-return
embedding for the run-zero rotation, retaining both sides of missing edges. -/
theorem rMinus_future_firstReturn (d : ℕ × Bool) :
    let J : (ℕ × Bool) → ℕ × Bool :=
      fun a => (boundaryGluingEdgeMap W h k a.1, a.2)
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n] (J d) =
        J (kmswInfRot U hfin d) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j] (J d) ∉ Set.range J := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let J : (ℕ × Bool) → ℕ × Bool :=
    fun a => (boundaryGluingEdgeMap W h k a.1, a.2)
  have hJ : J = fun a : ℕ × Bool => (kmswShiftEdgeMapAll w t a.1 a.1, a.2) := by
    funext a
    exact Prod.ext (boundaryGluingEdgeMap_eq_shift W h k a.1) rfl
  change ∃ n : ℕ, 0 < n ∧
    (kmswInfRot w (H.1 0) : _ → _)^[n] (J d) = J (kmswInfRot U hfin d) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot w (H.1 0) : _ → _)^[j] (J d) ∉ Set.range J
  rw [hJ]
  exact shiftInfRot_firstReturn w t hfin (H.1 0) d

/-- Helper toward Lemma 5.5: the full hatted embedding is first return
in run zero, before restricting to the hatted right side. -/
theorem rMinus_hatted_ambient_firstReturn (d : ℕ × Bool) :
    let D : (ℕ × Bool) → ℕ × Bool := fun a => (EH a.1, a.2)
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n] (D d) =
        D (kmswInfRot (hatCodes U hτ) (hatCodes_inducedFiniteIncidence U hτ hfin) d) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j] (D d) ∉ Set.range D := by
  let I : (ℕ × Bool) → ℕ × Bool := fun a => (hatLimitEdgeMap U hτ a.1, a.2)
  let J : (ℕ × Bool) → ℕ × Bool :=
    fun a => (boundaryGluingEdgeMap W h k a.1, a.2)
  have hJ : Function.Injective J := by
    intro a b hab
    have hb := congrArg (fun z : ℕ × Bool => z.2) hab
    exact Prod.ext (boundaryGluingEdgeMap_injective W h k (congrArg Prod.fst hab))
      hb
  exact hatExit_induced_rotation_comp
    (kmswInfRot (hatCodes U hτ) (hatCodes_inducedFiniteIncidence U hτ hfin))
    (kmswInfRot U hfin) (kmswInfRot (shiftedStream W 0) (H.1 0)) I J hJ
    (hatInfRot_firstReturn U hτ hfin) (rMinus_future_firstReturn (H := H) hfin) d

include hfin in
/-- Helper toward Lemma 5.5: first return to precisely the retained
hatted right darts gives the hatted right block's own rotation permutation.
This does not identify first return to the union with the prefix block. -/
theorem rMinusHattedDartImage_firstReturn
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges}) :
    let D : {a : ℕ × Bool // a.1 ∈ (Q).edges} → ℕ × Bool :=
      fun a => (EH a.val.1, a.val.2)
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n] (D d) =
        D (rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qR d) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j] (D d) ∉ Set.range D := by
  let z := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  let hf := sourceAncestor_finite_incidence
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime qR
  let G := monotoneFamilyDrawing z hf (monotone_family_all z)
  let A : Set (ℕ × Bool) := {a | a.1 ∈ (Q).edges}
  let I : A → ℕ × Bool := Subtype.val
  let J : (ℕ × Bool) → ℕ × Bool := fun a => (EH a.1, a.2)
  have hJ : Function.Injective J := by
    intro a b hab
    have hb := congrArg (fun z : ℕ × Bool => z.2) hab
    exact Prod.ext (boundaryGluingHatEdgeMap_injective W h k hτ
      (congrArg Prod.fst hab)) hb
  have hI (a : A) : ∃ n : ℕ, 0 < n ∧
      (kmswInfRot z hf : _ → _)^[n] (I a) =
        I (rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qR a) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot z hf : _ → _)^[j] (I a) ∉ Set.range I := by
    have ht := subsetFirstReturnTime_spec (kmswInfRot z hf) A
      (drawingPositiveReturn G A) a
    refine ⟨subsetFirstReturnTime (kmswInfRot z hf) A
      (drawingPositiveReturn G A) a, ht.1, rfl, ?_⟩
    intro j hj hjn hmem
    obtain ⟨b, hb⟩ := hmem
    exact ht.2.2 j hj hjn (hb ▸ b.property)
  have hretJ (a : ℕ × Bool) : ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n] (J a) =
        J (kmswInfRot z hf a) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j] (J a) ∉ Set.range J := by
    have hrot : kmswInfRot z hf =
        kmswInfRot (hatCodes U hτ) (hatCodes_inducedFiniteIncidence U hτ hfin) := by
      congr 1
      exact boundaryGluing_decoded_stream W h k hτ
    rw [hrot]
    exact rMinus_hatted_ambient_firstReturn (H := H) hτ hfin a
  exact hatExit_induced_rotation_comp
    (rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qR)
    (kmswInfRot z hf) (kmswInfRot (shiftedStream W 0) (H.1 0)) I J hJ hI hretJ d


/-- Helper toward Lemma 5.5: the finite prefix dart embedding retains both
endpoint bits of every allocated geometric edge, including missing edges. -/
@[expose] def rMinusPrefixDartImage (d : StageDart (F).nextEdge) : ℕ × Bool :=
  (d.1.val, d.2)

/-- Helper toward Lemma 5.5: the stopped prefix rotation is the first return
of the ambient rotation to its geometric darts. The prefix replaces the primed
block in the nonpositive right gluing. -/
theorem rMinusPrefixDartImage_firstReturn (d : StageDart (F).nextEdge) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n]
          (rMinusPrefixDartImage (h := h) d) =
        rMinusPrefixDartImage (h := h)
          (stageRot (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k) d) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
          (rMinusPrefixDartImage (h := h) d) ∉
            Set.range (rMinusPrefixDartImage (h := h) (k := k)) := by
  obtain ⟨n, hn, he, hg⟩ := kmswInfRot_firstReturn_stage
    (shiftedStream W 0) (H.1 0) (boundaryHitTime (shiftedStream W 0) h k) d
  refine ⟨n, hn, ?_, ?_⟩
  · simpa only [Equiv.Perm.coe_pow, rMinusPrefixDartImage] using he
  · intro j hj hjn hmem
    obtain ⟨a, ha⟩ := hmem
    have hge := hg j hj hjn
    rw [Equiv.Perm.coe_pow] at hge
    change (a.1.val, a.2) =
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j] (d.1.val, d.2) at ha
    rw [← ha] at hge
    exact Nat.not_lt_of_ge hge a.1.isLt

include hτ in
/-- Helper toward Lemma 5.5: an indexed shared prefix dart and its hatted
boundary dart have identical geometric edge IDs and identical endpoint bits. -/
theorem rMinusPrefixDartImage_boundary (i a : ℕ)
    (ha : ((F).active :: (F).UR)[i]? = some a) (b : Bool) :
    (a, b) = (EH (((Q).boundary i).1), b) :=
  Prod.ext (rMinus_code_boundary_gluing hτ hqMode i a ha).symm rfl

/-- Helper toward Lemma 5.5: the hatted right block closes its exterior
corner from the preceding reverse dart to the next forward dart. -/
theorem rMinusHattedRotation_boundary_corner (i : ℕ) :
    rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qR
        ⟨(((Q).boundary i).1, true), rMinus_hatted_boundary_mem _ qR i⟩ =
      ⟨(((Q).boundary (i + 1)).1, false), rMinus_hatted_boundary_mem _ qR (i + 1)⟩ := by
  let z := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  let hf := sourceAncestor_finite_incidence
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime qR
  apply (rMinusHattedRotation_iff _ qR _ _).mp
  refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
  · have he := kmswInfFaceSucc_right z hf (stageOuterWord_faceSucc z)
      (sourceAncestor_left_nonneg _ renewalTime renewalTime_positiveSuccessTime qR)
      (sourceAncestor_right_unbounded _ renewalTime renewalTime_positiveSuccessTime qR) i
    change (kmswInfRot z hf).symm (kmswRightBoundaryEdge z (i + 1), false) =
      (kmswRightBoundaryEdge z i, true) at he
    have hr := congrArg (kmswInfRot z hf) he
    rw [Equiv.apply_symm_apply] at hr
    change kmswInfRot z hf (((Q).boundary i).1, true) =
      (((Q).boundary (i + 1)).1, false)
    rw [boundaryGluing_nonneg_right_boundary_index hqMode i,
      boundaryGluing_nonneg_right_boundary_index hqMode (i + 1)]
    exact hr.symm
  · intro j hj hj1
    omega

/-- Helper toward Lemma 5.5: each indexed prefix interface edge is allocated. -/
theorem rMinus_prefix_boundary_lt (i a : ℕ)
    (ha : ((F).active :: (F).UR)[i]? = some a) : a < (F).nextEdge := by
  have hm := List.mem_iff_getElem?.mpr ⟨i, ha⟩
  rcases List.mem_cons.mp hm with he | he
  · subst a
    exact act_lt_nextEdge (shiftedStream W 0) (le_refl _)
  · exact (kmswStage_boundary_ids_lt_nextEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k)).2 a (by
        simp only [List.mem_append]
        tauto)

/-- Helper toward Lemma 5.5: consecutive prefix upper-boundary edge IDs
bound the exterior corner, from the next forward dart to the preceding reverse
dart. The two list-index equations specify the actual geometric ports. -/
theorem rMinusPrefixRotation_boundary_corner (i a b : ℕ)
    (ha : ((F).active :: (F).UR)[i]? = some a)
    (hb : ((F).active :: (F).UR)[i + 1]? = some b) :
    stageRot (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)
        (⟨b, rMinus_prefix_boundary_lt i.succ b hb⟩, false) =
      (⟨a, rMinus_prefix_boundary_lt i a ha⟩, true) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w t
  have hw : stageOuterWordVal w t =
      xs.map (fun e => (e, false)) ++
        (((F).active :: (F).UR).map (fun e => (e, false)) ++
          ((F).LR.reverse.map (fun e => (e, true)) ++
            (F).LL.reverse.map (fun e => (e, true)))) := by
    rw [stageOuterWordVal_eq_runs, hxs]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.singleton_append]
    rfl
  have hword (j c : ℕ) (hc : ((F).active :: (F).UR)[j]? = some c) :
      (stageOuterWordVal w t)[xs.length + j]? = some (c, false) := by
    have hj := (List.getElem?_eq_some_iff.mp hc).1
    rw [hw, List.getElem?_append_right (by simp), List.length_map,
      Nat.add_sub_cancel_left, List.getElem?_append_left (by simpa only [List.length_map] using hj),
      List.getElem?_map, hc]
    rfl
  have va := hword i a ha
  have vb := hword (i + 1) b hb
  obtain ⟨d, e, hd, he, hface⟩ := outer_faceSucc_exists w t
    (stageOuterWord_faceSucc w t) _ (List.getElem?_eq_some_iff.mp va).1
  rw [Nat.mod_eq_of_lt (by
    have ht := (List.getElem?_eq_some_iff.mp vb).1
    omega)] at he
  have hdv := Option.some.inj (hd.symm.trans va)
  have hev : (e.1.val, e.2) = (b, false) := by
    apply Option.some.inj
    exact he.symm.trans (by simpa only [Nat.add_assoc] using vb)
  have hd' : d = (⟨a, rMinus_prefix_boundary_lt i a ha⟩, false) :=
    Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) hdv))
      (congrArg (fun z : ℕ × Bool => z.2) hdv)
  have he' : e = (⟨b, rMinus_prefix_boundary_lt (i + 1) b hb⟩, false) :=
    Prod.ext (Fin.ext (congrArg (fun z : ℕ × Bool => z.1) hev))
      (congrArg (fun z : ℕ × Bool => z.2) hev)
  rw [hd', he'] at hface
  change (stageRot w t).symm (⟨a, rMinus_prefix_boundary_lt i a ha⟩, true) =
    (⟨b, rMinus_prefix_boundary_lt (i + 1) b hb⟩, false) at hface
  have hr := congrArg (stageRot w t) hface
  rw [Equiv.apply_symm_apply] at hr
  exact hr.symm

include hτ in
/-- Helper toward Lemma 5.5: the prefix exterior arc excludes all prefix
darts in its open part, at every pair of consecutive shared ports. -/
theorem rMinus_prefix_boundary_gap (i a b : ℕ)
    (ha : ((F).active :: (F).UR)[i]? = some a)
    (hb : ((F).active :: (F).UR)[i + 1]? = some b) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n]
          (EH (((Q).boundary (i + 1)).1), false) =
        (EH (((Q).boundary i).1), true) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
          (EH (((Q).boundary (i + 1)).1), false) ∉
            Set.range (rMinusPrefixDartImage (h := h) (k := k)) := by
  have hr := rMinusPrefixDartImage_firstReturn (H := H)
    (⟨b, rMinus_prefix_boundary_lt (i + 1) b hb⟩, false)
  rw [rMinusPrefixRotation_boundary_corner i a b ha hb] at hr
  simpa only [rMinusPrefixDartImage,
    rMinus_code_boundary_gluing hτ hqMode i a ha,
    rMinus_code_boundary_gluing hτ hqMode (i + 1) b hb] using hr

include hfin in
/-- Helper toward Lemma 5.5: the hatted right exterior arc runs from the
incoming to the outgoing port and excludes the hatted right block in its open part. -/
theorem rMinus_hatted_boundary_gap (i : ℕ) :
    let D : {a : ℕ × Bool // a.1 ∈ (Q).edges} → ℕ × Bool :=
      fun a => (EH a.val.1, a.val.2)
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n]
          (EH (((Q).boundary i).1), true) =
        (EH (((Q).boundary (i + 1)).1), false) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
          (EH (((Q).boundary i).1), true) ∉ Set.range D := by
  have hr := rMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin
    ⟨(((Q).boundary i).1, true), rMinus_hatted_boundary_mem _ qR i⟩
  dsimp only at hr
  rw [rMinusHattedRotation_boundary_corner hqMode i] at hr
  exact hr

include hfin in
/-- Helper toward Lemma 5.5: at every interior vertex of the finite shared
segment, the two exterior arcs form one minimal ambient cycle. Each arc excludes
its own block, with the right-side corner directions. -/
theorem rMinus_positive_boundary_rotation_separation (i a₀ b₀ : ℕ)
    (ha₀ : ((F).active :: (F).UR)[i]? = some a₀)
    (hb₀ : ((F).active :: (F).UR)[i + 1]? = some b₀) :
    let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
    let a : ℕ × Bool := (EH (((Q).boundary i).1), true)
    let b : ℕ × Bool := (EH (((Q).boundary (i + 1)).1), false)
    let D : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
      fun d => (EH d.val.1, d.val.2)
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
      (σ : _ → _)^[n] a = b ∧ (σ : _ → _)^[m] b = a ∧
      (∀ j : ℕ, 0 < j → j < n → (σ : _ → _)^[j] a ∉ Set.range D) ∧
      (∀ j : ℕ, 0 < j → j < m → (σ : _ → _)^[j] b ∉
        Set.range (rMinusPrefixDartImage (h := h) (k := k))) ∧
      (σ : _ → _)^[n + m] a = a ∧
      ∀ j : ℕ, 0 < j → j < n + m → (σ : _ → _)^[j] a ≠ a := by
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  let a : ℕ × Bool := (EH (((Q).boundary i).1), true)
  let b : ℕ × Bool := (EH (((Q).boundary (i + 1)).1), false)
  let D : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  obtain ⟨n, hn, hna, hgapH⟩ := rMinus_hatted_boundary_gap (H := H) hτ hqMode hfin i
  obtain ⟨m, hm, hmb, hgapP⟩ := rMinus_prefix_boundary_gap
    (H := H) hτ hqMode i a₀ b₀ ha₀ hb₀
  change (σ : _ → _)^[n] a = b at hna
  change (σ : _ → _)^[m] b = a at hmb
  have haH : a ∈ Set.range D :=
    ⟨⟨(((Q).boundary i).1, true), rMinus_hatted_boundary_mem _ qR i⟩, rfl⟩
  have haP : a ∈ Set.range (rMinusPrefixDartImage (h := h) (k := k)) := by
    refine ⟨(⟨a₀, rMinus_prefix_boundary_lt i a₀ ha₀⟩, true), ?_⟩
    exact rMinusPrefixDartImage_boundary hτ hqMode i a₀ ha₀ true
  have hab : b ≠ a := by
    intro he
    exact Bool.false_ne_true (congrArg (fun z : ℕ × Bool => z.2) he)
  refine ⟨n, m, hn, hm, hna, hmb, hgapH, hgapP, ?_, ?_⟩
  · rw [Nat.add_comm n m, Function.iterate_add_apply, hna, hmb]
  · intro j hj hjnm he
    by_cases hjn : j < n
    · exact hgapH j hj hjn (he.symm ▸ haH)
    · have hstep : (σ : _ → _)^[j] a = (σ : _ → _)^[j - n] b := by
        rw [← hna, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
      by_cases hjeq : j = n
      · subst j
        exact hab (hna.symm.trans he)
      · apply hgapP (j - n) (by omega) (by omega)
        exact (hstep.symm.trans he).symm ▸ haP

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the retained right-side darts are exactly the
union of the prefix and hatted images, including both darts of missing edges. -/
theorem rMinus_side_darts_union :
    {d : ℕ × Bool | d.1 ∈ (S).edges} =
      Set.range (rMinusPrefixDartImage (h := h) (k := k)) ∪
        Set.range (fun d : {d : ℕ × Bool // d.1 ∈ (Q).edges} => (EH d.val.1, d.val.2)) := by
  rw [← rMinusBlockDartImage_range hτ hp P hqMode Tpath hfin hleft hk]
  ext d
  constructor
  · rintro ⟨a | b, he⟩
    · exact Or.inl ⟨(⟨a.val.1, a.property⟩, a.val.2), he⟩
    · exact Or.inr ⟨b, he⟩
  · rintro (⟨a, he⟩ | ⟨b, he⟩)
    · exact ⟨Sum.inl ⟨(a.1.val, a.2), a.1.isLt⟩, he⟩
    · exact ⟨Sum.inr b, he⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: in each open exterior arc of a shared interior
vertex, retained right-side darts belong exactly to the opposite block. -/
theorem rMinus_positive_boundary_side_separation (i a₀ b₀ : ℕ)
    (ha₀ : ((F).active :: (F).UR)[i]? = some a₀)
    (hb₀ : ((F).active :: (F).UR)[i + 1]? = some b₀) :
    let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
    let a : ℕ × Bool := (EH (((Q).boundary i).1), true)
    let b : ℕ × Bool := (EH (((Q).boundary (i + 1)).1), false)
    let D : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
      fun d => (EH d.val.1, d.val.2)
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
      (σ : _ → _)^[n] a = b ∧ (σ : _ → _)^[m] b = a ∧
      (σ : _ → _)^[n + m] a = a ∧
      (∀ j : ℕ, 0 < j → j < n + m → (σ : _ → _)^[j] a ≠ a) ∧
      (∀ j : ℕ, 0 < j → j < n →
        (((σ : _ → _)^[j] a).1 ∈ (S).edges ↔ (σ : _ → _)^[j] a ∈
          Set.range (rMinusPrefixDartImage (h := h) (k := k)))) ∧
      ∀ j : ℕ, 0 < j → j < m →
        (((σ : _ → _)^[j] b).1 ∈ (S).edges ↔ (σ : _ → _)^[j] b ∈ Set.range D) := by
  obtain ⟨n, m, hn, hm, hna, hmb, hgapH, hgapP, hperiod, hminimal⟩ :=
    rMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i a₀ b₀ ha₀ hb₀
  have hset := rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk
  have hmem (d : ℕ × Bool) : d.1 ∈ (S).edges ↔
      d ∈ Set.range (rMinusPrefixDartImage (h := h) (k := k)) ∨
        d ∈ Set.range (fun a : {a : ℕ × Bool // a.1 ∈ (Q).edges} => (EH a.val.1, a.val.2)) :=
    Set.ext_iff.mp hset d
  refine ⟨n, m, hn, hm, hna, hmb, hperiod, hminimal, ?_, ?_⟩
  · intro j hj hjn
    rw [hmem, or_iff_left (hgapH j hj hjn)]
  · intro j hj hjm
    rw [hmem, or_iff_right (hgapP j hj hjm)]

end RotationHelpers

/-- Helper toward Lemma 5.5: the hatted right exterior boundary has its
literal lower-right KMSW edge IDs, for any coherent code. -/
theorem rMinus_hatted_boundary_index (x : XDP) (q : Coherent x) (i : ℕ) :
    ((geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).boundary i).1 =
      kmswRightBoundaryEdge (boltzmannKMSWStream (pathCode q.val)) i := by
  let z := boltzmannKMSWStream (pathCode q.val)
  let hf := sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q
  let hL := sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q
  let ht := sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q
  let hR := sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q
  change (kmswRightmostPath z hf hL ht hR 0).edge i = _
  induction i with
  | zero => exact kmswRightmostOutgoingEdge_source z hf hL ht hR _
  | succ i ih =>
    have hv : kmswRightmostOrbit z hf hL ht hR 0 (i + 1) =
        edgeWest z (kmswRightBoundaryEdge z (i + 1)) := by
      rw [← (kmswRightmostPath_edge_spec z hf hL ht hR 0 i).2.2, ih]
      exact (kmswRightBoundary_infinite_path z hL hR).2.1 i
    change kmswRightmostOutgoingEdge z hf hL ht hR _
      (kmswRightmostOrbit z hf hL ht hR 0 (i + 1)) = _
    rw [hv]
    exact kmswRightBoundaryEdge_is_rightmost z hf hL ht hR (by omega)

/-- Helper toward Lemma 5.5: hatted right boundary edge IDs are injective. -/
theorem rMinus_hatted_boundary_edge_injective (x : XDP) (q : Coherent x) :
    Function.Injective (fun i =>
      ((geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).boundary i).1) := by
  intro i j hij
  dsimp only at hij
  rw [rMinus_hatted_boundary_index, rMinus_hatted_boundary_index] at hij
  exact (kmswRightBoundary_infinite_path _
    (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)).1 hij

/-- Helper toward Lemma 5.5: the finite shared interface has no repeated edge IDs. -/
theorem rMinus_prefix_boundary_nodup (w : ℕ → Fin 3) (n : ℕ) :
    ((kmswStage w n).active :: (kmswStage w n).UR).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨?_, (kmswStage_status w n).2.2.2.1⟩
  intro hm
  obtain ⟨xs, hxs⟩ := kmswStage_UL_last w n
  have hUL : (kmswStage w n).active ∈ (kmswStage w n).UL := by
    rw [hxs]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hp := (kmswStage_status w n).2.1 _ hUL
  have hn := ((kmswStage_status w n).1 _ (act_lt_nextEdge w (le_refl n))).mpr (Or.inl hm)
  change (kmswStage w n).present (kmswStage w n).active = false at hn
  rw [hp] at hn
  cases hn

/-- Helper toward Lemma 5.5: normal form of intrinsic edge gluing. -/
@[expose] def rMinusCodeEdgeNormalRelation (F : State) (M : GeometricSideSubmap) :
    Sum {e : ℕ // e < F.nextEdge} M.edges →
      Sum {e : ℕ // e < F.nextEdge} M.edges → Prop
  | .inl a, .inl b => a = b
  | .inr a, .inr b => a = b
  | .inl a, .inr b => rMinusCodeEdgeGluing F M (.inl a) (.inr b)
  | .inr a, .inl b => rMinusCodeEdgeGluing F M (.inl b) (.inr a)

/-- Helper toward Lemma 5.5: equivalence closure adds no unintended edge
identifications; the finite prefix and coherent hatted block both embed. -/
theorem rMinusCodeEdgeSetoid_iff (w : ℕ → Fin 3) (n : ℕ)
    {x : XDP} (q : Coherent x)
    (a b : Sum {e : ℕ // e < (kmswStage w n).nextEdge}
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges) :
    rMinusCodeEdgeSetoid (kmswStage w n) _ a b ↔
      rMinusCodeEdgeNormalRelation (kmswStage w n) _ a b := by
  let F := kmswStage w n
  let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
  have hl (a c : {e : ℕ // e < F.nextEdge}) (b : M.edges)
      (hab : rMinusCodeEdgeGluing F M (.inl a) (.inr b))
      (hcb : rMinusCodeEdgeGluing F M (.inl c) (.inr b)) : a = c := by
    obtain ⟨i, hi, hib⟩ := hab
    obtain ⟨j, hj, hjb⟩ := hcb
    have hij := rMinus_hatted_boundary_edge_injective x q (hib.trans hjb.symm)
    subst j
    exact Subtype.ext (Option.some.inj (hi.symm.trans hj))
  have hr (a : {e : ℕ // e < F.nextEdge}) (b c : M.edges)
      (hab : rMinusCodeEdgeGluing F M (.inl a) (.inr b))
      (hac : rMinusCodeEdgeGluing F M (.inl a) (.inr c)) : b = c := by
    obtain ⟨i, hi, hib⟩ := hab
    obtain ⟨j, hj, hjc⟩ := hac
    have hij := (rMinus_prefix_boundary_nodup w n).eq_of_getElem?_eq
      (List.getElem?_eq_some_iff.mp hi).1 (hi.trans hj.symm)
    subst j
    exact Subtype.ext (hib.symm.trans hjc)
  let R := rMinusCodeEdgeNormalRelation F M
  have hrefl : ∀ a, R a a := by intro a; cases a <;> exact rfl
  have hsymm : ∀ {a b}, R a b → R b a := by
    intro a b hab
    cases a <;> cases b
    · exact hab.symm
    · exact hab
    · exact hab
    · exact hab.symm
  have htrans : ∀ {a b c}, R a b → R b c → R a c := by
    intro a b c hab hbc
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        cases c with
        | inl c => exact hab.trans hbc
        | inr c => change a = b at hab; subst b; exact hbc
      | inr b =>
        cases c with
        | inl c => exact hl a c b hab hbc
        | inr c => change b = c at hbc; subst c; exact hab
    | inr a =>
      cases b with
      | inl b =>
        cases c with
        | inl c => change b = c at hbc; subst c; exact hab
        | inr c => exact hr b a c hab hbc
      | inr b =>
        cases c with
        | inl c => change a = b at hab; subst b; exact hbc
        | inr c => exact hab.trans hbc
  constructor
  · exact (show rMinusCodeEdgeSetoid F M ≤
        (⟨R, hrefl, hsymm, htrans⟩ : Setoid _) from by
      apply Setoid.eqvGen_le
      intro a b hab
      cases a <;> cases b <;> first | exact hab | exact hab.elim) (x := a) (y := b)
  · intro hab
    cases a <;> cases b
    · change _ = _ at hab
      subst_vars
      exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ hab
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hab)
    · change _ = _ at hab
      subst_vars
      exact Relation.EqvGen.refl _

/-- Helper toward Lemma 5.5: intrinsic code darts retain the glued edge ID
and a separate endpoint bit. No side correction is needed for the prefix. -/
abbrev RMinusCodeGluedDart (F : State) (M : GeometricSideSubmap) :=
  RMinusCodeGluedEdge F M × Bool

/-- Helper toward Lemma 5.5: the intrinsic prefix dart embedding. -/
@[expose] def rMinusCodePrefixDart (F : State) (M : GeometricSideSubmap)
    (d : StageDart F.nextEdge) : RMinusCodeGluedDart F M :=
  (⟦Sum.inl ⟨d.1.val, d.1.isLt⟩⟧, d.2)

/-- Helper toward Lemma 5.5: the intrinsic hatted dart embedding. -/
@[expose] def rMinusCodeHattedDart (F : State) (M : GeometricSideSubmap)
    (d : {d : ℕ × Bool // d.1 ∈ M.edges}) : RMinusCodeGluedDart F M :=
  (⟦Sum.inr ⟨d.val.1, d.property⟩⟧, d.val.2)

/-- Helper toward Lemma 5.5: prefix intrinsic darts are injective. -/
theorem rMinusCodePrefixDart_injective (w : ℕ → Fin 3) (n : ℕ)
    {x : XDP} (q : Coherent x) :
    Function.Injective (rMinusCodePrefixDart (kmswStage w n)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) := by
  intro a b hab
  have he := (rMinusCodeEdgeSetoid_iff w n q _ _).mp (Quotient.exact (congrArg Prod.fst hab))
  change (⟨a.1.val, a.1.isLt⟩ : {e : ℕ // e < (kmswStage w n).nextEdge}) =
    ⟨b.1.val, b.1.isLt⟩ at he
  exact Prod.ext (Fin.ext (congrArg Subtype.val he))
    (congrArg (fun d : RMinusCodeGluedDart (kmswStage w n) _ => d.2) hab)

/-- Helper toward Lemma 5.5: hatted intrinsic darts are injective. -/
theorem rMinusCodeHattedDart_injective (w : ℕ → Fin 3) (n : ℕ)
    {x : XDP} (q : Coherent x) :
    Function.Injective (rMinusCodeHattedDart (kmswStage w n)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) := by
  intro a b hab
  have he := (rMinusCodeEdgeSetoid_iff w n q _ _).mp (Quotient.exact (congrArg Prod.fst hab))
  change (⟨a.val.1, a.property⟩ :
    (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q).edges) =
      ⟨b.val.1, b.property⟩ at he
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val he)
    (congrArg (fun d : RMinusCodeGluedDart (kmswStage w n) _ => d.2) hab)

/-- Helper toward Lemma 5.5: the finite boundary correction swaps the two
ports at each interior shared vertex and fixes both endpoint ports. -/
@[expose] def rMinusBoundaryCorner (N : ℕ) (d : StageDart N) : StageDart N :=
  if d.2 then
    if hi : d.1.val + 1 < N then (⟨d.1.val + 1, hi⟩, false) else d
  else if hi : 0 < d.1.val then
    (⟨d.1.val - 1, by have := d.1.isLt; omega⟩, true) else d

/-- Helper toward Lemma 5.5: the finite interface correction is involutive. -/
theorem rMinusBoundaryCorner_involutive (N : ℕ) :
    Function.Involutive (rMinusBoundaryCorner N) := by
  rintro ⟨⟨i, hi⟩, b⟩
  cases b with
  | false =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [rMinusBoundaryCorner, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte,
        Nat.zero_lt_succ, Nat.add_sub_cancel, hi]
  | true =>
    by_cases hn : i + 1 < N
    · simp only [rMinusBoundaryCorner, ↓reduceIte, ↓reduceDIte, hn, Bool.false_eq_true,
        Nat.zero_lt_succ, Nat.add_sub_cancel]
    · simp only [rMinusBoundaryCorner, ↓reduceIte, ↓reduceDIte, hn]

/-- Helper toward Lemma 5.5: the finite boundary correction as a permutation. -/
@[expose] def rMinusBoundaryCornerPerm (N : ℕ) : Equiv.Perm (StageDart N) :=
  ⟨rMinusBoundaryCorner N, rMinusBoundaryCorner N,
    rMinusBoundaryCorner_involutive N, rMinusBoundaryCorner_involutive N⟩

/-- Helper toward Lemma 5.5: each finite interface port retains its prefix
edge ID and endpoint bit in the intrinsic dart carrier. -/
@[expose] def rMinusCodeBoundaryDart (w : ℕ → Fin 3) (n : ℕ)
    (M : GeometricSideSubmap)
    (d : StageDart ((kmswStage w n).active :: (kmswStage w n).UR).length) :
    RMinusCodeGluedDart (kmswStage w n) M :=
  rMinusCodePrefixDart _ M
    (⟨((kmswStage w n).active :: (kmswStage w n).UR)[d.1.val], by
      have hm := List.getElem_mem d.1.isLt
      rcases List.mem_cons.mp hm with he | he
      · rw [he]
        exact act_lt_nextEdge w (le_refl n)
      · exact (kmswStage_boundary_ids_lt_nextEdge w n).2 _ (by
          simp only [List.mem_append]
          tauto)⟩, d.2)

/-- Helper toward Lemma 5.5: intrinsic interface ports are injective. -/
theorem rMinusCodeBoundaryDart_injective (w : ℕ → Fin 3) (n : ℕ)
    {x : XDP} (q : Coherent x) :
    Function.Injective (rMinusCodeBoundaryDart w n
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) := by
  intro a b hab
  have hd := rMinusCodePrefixDart_injective w n q hab
  have he := congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.1.val) hd
  apply Prod.ext
  · apply Fin.ext
    exact (rMinus_prefix_boundary_nodup w n).getElem_inj_iff.mp he
  · exact congrArg (fun d : StageDart (kmswStage w n).nextEdge => d.2) hd

/-- Helper toward Lemma 5.5: the right-side splice candidate multiplies
the extended hatted rotation, finite interface correction, and prefix rotation.
Its geometric rotation transport remains a separate obligation. -/
@[expose] noncomputable def rMinusCodeSpliceRotation (w : ℕ → Fin 3) (n : ℕ)
    {x : XDP} (q : Coherent x) :
    Equiv.Perm (RMinusCodeGluedDart (kmswStage w n)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) :=
  (rMinusHattedRotation x q).extendDomain
      (Equiv.ofInjective _ (rMinusCodeHattedDart_injective w n q)) *
    (rMinusBoundaryCornerPerm ((kmswStage w n).active :: (kmswStage w n).UR).length).extendDomain
      (Equiv.ofInjective _ (rMinusCodeBoundaryDart_injective w n q)) *
    (stageRot w n).extendDomain
      (Equiv.ofInjective _ (rMinusCodePrefixDart_injective w n q))

/-- Helper toward Lemma 5.5: the intrinsic splice candidate is bijective. -/
theorem rMinusCodeSpliceRotation_bijective (w : ℕ → Fin 3) (n : ℕ)
    {x : XDP} (q : Coherent x) :
    Function.Bijective (rMinusCodeSpliceRotation w n q) :=
  (rMinusCodeSpliceRotation w n q).bijective

/-- Helper toward Lemma 5.5: select a rotation candidate from exactly the
two valid decoded blocks. Invalid prefixes and hatted codes return `none`. -/
@[expose] noncomputable def RMinusSidePresentation.rotationAssembly {x : XDP}
    (r : RMinusSidePresentation x) :
    Option (Σ F : State, Σ M : GeometricSideSubmap, Equiv.Perm (RMinusCodeGluedDart F M)) :=
  if hp : r.prefixValid then
    if hq : ∃ q : Coherent x,
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.val = r.code.2
    then some ⟨kmswStage r.code.1 hp.choose,
      geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right hq.choose,
      rMinusCodeSpliceRotation r.code.1 hp.choose hq.choose⟩
    else none
  else none

/-- Helper toward Lemma 5.5: exact existence criterion for the code-only
candidate, without a rotation or gluing premise. -/
theorem RMinusSidePresentation.rotationAssembly_isSome_iff {x : XDP}
    (r : RMinusSidePresentation x) :
    r.rotationAssembly.isSome ↔ r.prefixValid ∧
      ∃ q : Coherent x,
        thinSideCode x renewalTime renewalTime_positiveSuccessTime .right q.val = r.code.2 := by
  unfold RMinusSidePresentation.rotationAssembly
  split
  · rename_i hp
    split <;> simp_all only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
      and_self, and_false]
  · simp_all only [Option.isSome_none, Bool.false_eq_true, false_and]


/-- Helper toward Lemma 5.5: the allocated prefix dart at an indexed
interface port, retaining its geometric edge ID. -/
@[expose] def rMinusPrefixBoundaryDart (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart ((kmswStage w n).active :: (kmswStage w n).UR).length) :
    StageDart (kmswStage w n).nextEdge :=
  (⟨((kmswStage w n).active :: (kmswStage w n).UR)[d.1.val], by
    have hm := List.getElem_mem d.1.isLt
    rcases List.mem_cons.mp hm with he | he
    · rw [he]
      exact act_lt_nextEdge w (le_refl n)
    · exact (kmswStage_boundary_ids_lt_nextEdge w n).2 _ (by
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inr he)))⟩, d.2)

/-- Helper toward Lemma 5.5: an intrinsic interface dart is its literal
allocated prefix representative. -/
theorem rMinusCodeBoundaryDart_eq_prefix (w : ℕ → Fin 3) (n : ℕ)
    (M : GeometricSideSubmap)
    (d : StageDart ((kmswStage w n).active :: (kmswStage w n).UR).length) :
    rMinusCodeBoundaryDart w n M d =
      rMinusCodePrefixDart (kmswStage w n) M (rMinusPrefixBoundaryDart w n d) := rfl

/-- Helper toward Lemma 5.5: a one-edge interface has no interior
corner exchanges, so both of its endpoint ports are fixed. -/
theorem rMinusBoundaryCornerPerm_one : rMinusBoundaryCornerPerm 1 = 1 := by
  apply Equiv.ext
  rintro ⟨⟨i, hi⟩, b⟩
  have hi0 : i = 0 := by omega
  subst i
  cases b <;> rfl

/-- Helper toward Lemma 5.5: at stage zero the finite prefix and corner
factors are identities; the splice is the extended hatted permutation. -/
theorem rMinusCodeSpliceRotation_zero (w : ℕ → Fin 3)
    {x : XDP} (q : Coherent x) :
    rMinusCodeSpliceRotation w 0 q =
      (rMinusHattedRotation x q).extendDomain
        (Equiv.ofInjective _ (rMinusCodeHattedDart_injective w 0 q)) := by
  have hc : rMinusBoundaryCornerPerm
      ((kmswStage w 0).active :: (kmswStage w 0).UR).length = 1 :=
    rMinusBoundaryCornerPerm_one
  unfold rMinusCodeSpliceRotation
  rw [hc, stageRot_zero]
  have hidentity {α β : Type} {p : β → Prop} [DecidablePred p]
      (f : α ≃ Subtype p) : (1 : Equiv.Perm α).extendDomain f = 1 :=
    Equiv.Perm.extendDomain_refl f
  rw [hidentity, hidentity, mul_one, mul_one]

section CodeRotationTransport

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ Coherent
    (if longest then XDP.ldp else XDP.sdp))
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "S" => m0GeodesicSide hp P ThinMapSide.right
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.right
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "U" => boundaryGluingFutureStream W h k
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "VH" => boundaryGluingHatVertexMap W h k hτ
local notation "F" => kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)


local notation "qR" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode)

/-- Helper toward Lemma 5.5: changing the proved setoid presentation
does not change a representative's edge ID. -/
private theorem rMinus_quotient_cast_mk {α : Type*} {s t : Setoid α}
    (hst : s = t) (a : α) :
    Equiv.cast (congrArg Quotient hst) (Quotient.mk s a) = Quotient.mk t a := by
  subst t
  rfl

include h hqMode in
/-- Helper toward Lemma 5.5: the observed stopped prefix and coherent
hatted code give an intrinsic rotation candidate, without any rotation premise. -/
theorem decodeRMinus_rightSideObsNonpos_rotationAssembly_isSome :
    (decodeRMinus (if longest then XDP.ldp else XDP.sdp) k
      (rightSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)).rotationAssembly.isSome := by
  apply (RMinusSidePresentation.rotationAssembly_isSome_iff _).mpr
  refine ⟨?_, qR, rfl⟩
  obtain ⟨n, hn, hpad, _⟩ := RMinusSidePresentation.prefixRealization_eq_some_spec _ _
    (decodeRMinus_rightSideObsNonpos_prefixRealization (h := h)
      (if longest then XDP.ldp else XDP.sdp))
  exact ⟨n, hn, hpad⟩

/-- Helper toward Lemma 5.5: the intrinsic edge equivalence evaluates
each block representative at its existing geometric edge embedding. -/
theorem rMinusCodeGluedEdgeEquiv_val (a : RMinusBlockEdge hqMode) :
    (rMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk
      (Quotient.mk _ a)).val = rMinusBlockEdgeImage hτ hqMode a := by
  change (rMinusGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk
    (Equiv.cast (congrArg Quotient (rMinusCodeEdgeSetoid_eq_ker hτ hqMode hfin))
      (Quotient.mk _ a))).val = _
  exact congrArg (fun z : RMinusGluedEdge hτ hqMode =>
    (rMinusGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk z).val)
    (rMinus_quotient_cast_mk (rMinusCodeEdgeSetoid_eq_ker hτ hqMode hfin) a)

/-- Helper toward Lemma 5.5: the code-only edge gluing, with a separate
endpoint bit, bijects with all geometric darts of the actual right side. -/
@[expose] noncomputable def rMinusCodeGluedDartEquiv :
    RMinusCodeGluedDart F Q ≃ {d : ℕ × Bool // d.1 ∈ (S).edges} where
  toFun d := ⟨((rMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk d.1).val,
    d.2), (rMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk d.1).property⟩
  invFun d := ((rMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk).symm
    ⟨d.val.1, d.property⟩, d.val.2)
  left_inv d := by
    obtain ⟨e, b⟩ := d
    change ((rMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk).symm
      (rMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk e), b) = (e, b)
    rw [Equiv.symm_apply_apply]
  right_inv d := by
    apply Subtype.ext
    change ((rMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk
      ((rMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk).symm
        ⟨d.val.1, d.property⟩)).val, d.val.2) = d.val
    rw [Equiv.apply_symm_apply]


/-- Helper toward Lemma 5.5: both endpoint bits of intrinsic hatted darts
map to their actual geometric edge IDs. -/
theorem rMinusCodeGluedDartEquiv_hatted (d : {d : ℕ × Bool // d.1 ∈ (Q).edges}) :
    (rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusCodeHattedDart F Q d)).val = (EH d.val.1, d.val.2) :=
  Prod.ext (rMinusCodeGluedEdgeEquiv_val hτ hp P hqMode Tpath hfin hleft hk
    (.inr ⟨d.val.1, d.property⟩)) rfl

/-- Helper toward Lemma 5.5: intrinsic prefix darts preserve both the
allocated geometric edge ID and the endpoint bit. -/
theorem rMinusCodeGluedDartEquiv_prefix (d : StageDart (F).nextEdge) :
    (rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusCodePrefixDart F Q d)).val = (d.1.val, d.2) :=
  Prod.ext (rMinusCodeGluedEdgeEquiv_val hτ hp P hqMode Tpath hfin hleft hk
    (.inl ⟨d.1.val, d.1.isLt⟩)) rfl

/-- Helper toward Lemma 5.5: intrinsic code darts and the geometric dart
quotient have the same complete edge-ID carrier and endpoint bits. -/
@[expose] noncomputable def rMinusCodeToGluedDartEquiv :
    RMinusCodeGluedDart F Q ≃ RMinusGluedDart hτ hqMode :=
  (rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).trans
    (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm

/-- Helper toward Lemma 5.5: changing dart presentation commutes with the
actual geometric embedding. -/
theorem rMinusCodeToGluedDartEquiv_equiv (d : RMinusCodeGluedDart F Q) :
    rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d) =
        rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d :=
  (rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).apply_symm_apply _

/-- Helper toward Lemma 5.5: transport the intrinsic splice candidate
to the existing geometric dart quotient, using only the proved carrier equivalence. -/
@[expose] noncomputable def rMinusGluedSpliceRotation :
    Equiv.Perm (RMinusGluedDart hτ hqMode) :=
  Equiv.permCongr (rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk)
    (rMinusCodeSpliceRotation (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k) qR)



@[expose] noncomputable def rMinusSpliceRotationRelation :
    Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode) →
      Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode) → Prop
  | .inr d, .inr e => rMinusGluedSpliceRotation hτ hp P hqMode Tpath hfin hleft hk d = e
  | _, _ => False

/-- Helper toward Lemma 5.5: a return before the end of another block's
open gap is first return to the union of the two blocks. -/
private theorem rMinus_firstReturn_union_of_gap {α : Type*} (σ : α → α)
    (A B : Set α) (x z : α) (n t : ℕ)
    (ht : 0 < t) (hz : σ^[t] x = z) (hzB : z ∈ B)
    (hB : ∀ j : ℕ, 0 < j → j < t → σ^[j] x ∉ B)
    (hn : 0 < n) (hnB : σ^[n] x ∈ B)
    (hA : ∀ j : ℕ, 0 < j → j < n → σ^[j] x ∉ A) :
    0 < t ∧ σ^[t] x = z ∧ z ∈ A ∪ B ∧
      ∀ j : ℕ, 0 < j → j < t → σ^[j] x ∉ A ∪ B := by
  have htn : t ≤ n := by
    by_contra hnot
    exact hB n hn (by omega) hnB
  refine ⟨ht, hz, Or.inr hzB, ?_⟩
  intro j hj hjt hmem
  rcases hmem with ha | hb
  · exact hA j hj (lt_of_lt_of_le hjt htn) ha
  · exact hB j hj hjt hb

/-- Helper toward Lemma 5.5: minimal positive returns to a retained dart
set have a unique endpoint, with the entire dart identity retained. -/
private theorem rMinus_firstReturn_endpoint_unique {α : Type*} (σ : α → α)
    (A : Set α) {x y z : α} (hy : y ∈ A) (hz : z ∈ A)
    (hyret : ∃ n : ℕ, 0 < n ∧ σ^[n] x = y ∧
      ∀ j : ℕ, 0 < j → j < n → σ^[j] x ∉ A)
    (hzret : ∃ n : ℕ, 0 < n ∧ σ^[n] x = z ∧
      ∀ j : ℕ, 0 < j → j < n → σ^[j] x ∉ A) : y = z := by
  obtain ⟨n, hn, hny, hngap⟩ := hyret
  obtain ⟨m, hm, hmz, hmgap⟩ := hzret
  have hnm : n = m := by
    apply Nat.le_antisymm
    · by_contra hnot
      exact hngap m hm (by omega) (hmz.symm ▸ hz)
    · by_contra hnot
      exact hmgap n hn (by omega) (hny.symm ▸ hy)
  exact hny.symm.trans (hnm ▸ hmz)

local notation "wR" => shiftedStream W 0
local notation "tR" => boundaryHitTime (shiftedStream W 0) h k
local notation "N" => List.length (State.active (kmswStage (shiftedStream W 0)
  (boundaryHitTime (shiftedStream W 0) h k)) ::
  State.UR (kmswStage (shiftedStream W 0) (boundaryHitTime (shiftedStream W 0) h k)))
local notation "D" => rMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "E" => rMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "G" => rMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "Φ" => rMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a finite interface port is exactly the
hatted port with the same edge identity and endpoint bit. -/
theorem rMinusCodeBoundaryDart_eq_hatted (i : Fin N) (b : Bool) :
    rMinusCodeBoundaryDart wR tR Q (i, b) =
      rMinusCodeHattedDart F Q
        ⟨(((Q).boundary i.val).1, b), rMinus_hatted_boundary_mem _ qR i.val⟩ := by
  apply (D).injective
  apply Subtype.ext
  rw [rMinusCodeGluedDartEquiv_hatted]
  change (D (rMinusCodePrefixDart F Q _)).val = _
  rw [rMinusCodeGluedDartEquiv_prefix]
  exact rMinusPrefixDartImage_boundary hτ hqMode i.val _
    (List.getElem?_eq_getElem i.isLt) b

include hτ hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at an interior incoming port the whole-side
successor is the prefix first return, since the hatted gap excludes all
other hatted darts before the outgoing port. -/
theorem rMinus_positive_incoming_side_rotation (i a b : ℕ)
    (ha : ((F).active :: (F).UR)[i]? = some a)
    (hb : ((F).active :: (F).UR)[i + 1]? = some b) :
    let d : StageDart (F).nextEdge :=
      (⟨a, rMinus_prefix_boundary_lt i a ha⟩, true)
    (S).rotation (a, true)
      (rMinusPrefixDartImage (h := h) (stageRot wR tR d)) := by
  let σ := kmswInfRot wR (H.1 0)
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let d : StageDart (F).nextEdge :=
    (⟨a, rMinus_prefix_boundary_lt i a ha⟩, true)
  obtain ⟨n, hn, hne, hgap⟩ := rMinus_hatted_boundary_gap (H := H) hτ hqMode hfin i
  have ha' := rMinusPrefixDartImage_boundary hτ hqMode i a ha true
  have hb' := rMinusPrefixDartImage_boundary hτ hqMode (i + 1) b hb false
  rw [← ha'] at hne hgap
  rw [← hb'] at hne
  obtain ⟨t, ht, hte, htgap⟩ := rMinusPrefixDartImage_firstReturn (H := H) d
  have hnP : (σ : _ → _)^[n] (a, true) ∈
      Set.range (rMinusPrefixDartImage (h := h) (k := k)) := by
    rw [hne]
    exact ⟨(⟨b, rMinus_prefix_boundary_lt (i + 1) b hb⟩, false), rfl⟩
  have hret := rMinus_firstReturn_union_of_gap (σ : _ → _) (Set.range J)
    (Set.range (rMinusPrefixDartImage (h := h) (k := k))) (a, true) _ n t
    ht hte ⟨_, rfl⟩ htgap hn hnP hgap
  refine ⟨t, hret.1, hret.2.1, ?_⟩
  intro j hj hjt hmem
  apply hret.2.2.2 j hj hjt
  rw [Set.union_comm, ← rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk]
  exact hmem

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at an interior outgoing port the whole-side
successor is the hatted first return, using the proved prefix exterior gap. -/
theorem rMinus_positive_outgoing_side_rotation (i a b : ℕ)
    (ha : ((F).active :: (F).UR)[i]? = some a)
    (hb : ((F).active :: (F).UR)[i + 1]? = some b) :
    let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
      ⟨(((Q).boundary (i + 1)).1, false), rMinus_hatted_boundary_mem _ qR (i + 1)⟩
    let e := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qR d
    (S).rotation (EH d.val.1, d.val.2) (EH e.val.1, e.val.2) := by
  let σ := kmswInfRot wR (H.1 0)
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let d : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary (i + 1)).1, false), rMinus_hatted_boundary_mem _ qR (i + 1)⟩
  obtain ⟨n, hn, hne, hgap⟩ := rMinus_prefix_boundary_gap (H := H) hτ hqMode i a b ha hb
  obtain ⟨t, ht, hte, htgap⟩ := rMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin d
  have hnJ : (σ : _ → _)^[n] (J d) ∈ Set.range J := by
    rw [hne]
    exact ⟨⟨(((Q).boundary i).1, true), rMinus_hatted_boundary_mem _ qR i⟩, rfl⟩
  have hret := rMinus_firstReturn_union_of_gap (σ : _ → _)
    (Set.range (rMinusPrefixDartImage (h := h) (k := k))) (Set.range J) (J d) _ n t
    ht hte ⟨_, rfl⟩ htgap hn hnJ hgap
  refine ⟨t, hret.1, hret.2.1, ?_⟩
  intro j hj hjt hmem
  apply hret.2.2.2 j hj hjt
  rw [← rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk]
  exact hmem

/-- Helper toward Lemma 5.5: the prefix exterior corner exchanges the
two indexed interior ports before the splice correction. -/
theorem rMinusPrefixRotation_boundary_indexed (i : Fin N) (hi : i.val + 1 < N) :
    stageRot wR tR (rMinusPrefixBoundaryDart wR tR (⟨i.val + 1, hi⟩, false)) =
      rMinusPrefixBoundaryDart wR tR (i, true) :=
  rMinusPrefixRotation_boundary_corner i.val _ _
    (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at an outgoing interior port the prefix
exterior corner and the finite correction cancel exactly. -/
theorem rMinusCodeSpliceRotation_outgoing (i : Fin N) (hi : i.val + 1 < N) :
    rMinusCodeSpliceRotation wR tR qR
        (rMinusCodeBoundaryDart wR tR Q (⟨i.val + 1, hi⟩, false)) =
      rMinusCodeHattedDart F Q
        (rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qR
          ⟨(((Q).boundary (i.val + 1)).1, false),
            rMinus_hatted_boundary_mem _ qR (i.val + 1)⟩) := by
  let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qR
  let Hemb := Equiv.ofInjective (rMinusCodeHattedDart F Q)
    (rMinusCodeHattedDart_injective wR tR qR)
  let Cemb := Equiv.ofInjective (rMinusCodeBoundaryDart wR tR Q)
    (rMinusCodeBoundaryDart_injective wR tR qR)
  let Prot := stageRot wR tR
  let Pemb := Equiv.ofInjective (rMinusCodePrefixDart F Q)
    (rMinusCodePrefixDart_injective wR tR qR)
  have hP : Prot.extendDomain Pemb
      (rMinusCodeBoundaryDart wR tR Q (⟨i.val + 1, hi⟩, false)) =
        rMinusCodeBoundaryDart wR tR Q (i, true) := by
    rw [rMinusCodeBoundaryDart_eq_prefix]
    have he := Prot.extendDomain_apply_image Pemb
      (rMinusPrefixBoundaryDart wR tR (⟨i.val + 1, hi⟩, false))
    change Prot.extendDomain Pemb (rMinusCodePrefixDart F Q
      (rMinusPrefixBoundaryDart wR tR (⟨i.val + 1, hi⟩, false))) =
        rMinusCodePrefixDart F Q
          (Prot (rMinusPrefixBoundaryDart wR tR (⟨i.val + 1, hi⟩, false))) at he
    change Prot.extendDomain Pemb (rMinusCodePrefixDart F Q _) = _
    rw [he, show Prot = stageRot wR tR from rfl,
      rMinusPrefixRotation_boundary_indexed i hi]
    rfl
  have hC : (rMinusBoundaryCornerPerm N).extendDomain Cemb
      (rMinusCodeBoundaryDart wR tR Q (i, true)) =
        rMinusCodeBoundaryDart wR tR Q (⟨i.val + 1, hi⟩, false) := by
    have he := (rMinusBoundaryCornerPerm N).extendDomain_apply_image Cemb (i, true)
    change (rMinusBoundaryCornerPerm N).extendDomain Cemb
      (rMinusCodeBoundaryDart wR tR Q (i, true)) =
        rMinusCodeBoundaryDart wR tR Q (rMinusBoundaryCorner N (i, true)) at he
    simpa only [rMinusBoundaryCornerPerm, rMinusBoundaryCorner, hi, ↓reduceIte,
      ↓reduceDIte] using he
  change Hrot.extendDomain Hemb ((rMinusBoundaryCornerPerm N).extendDomain Cemb
    (Prot.extendDomain Pemb (rMinusCodeBoundaryDart wR tR Q (⟨i.val + 1, hi⟩, false)))) = _
  rw [hP, hC, rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk]
  exact Hrot.extendDomain_apply_image Hemb _

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a prefix successor of an incoming interior
port can be hatted only when it is the next outgoing shared port. -/
theorem rMinusPrefixRotation_incoming_mem_hatted_iff (i : Fin N)
    (hi : i.val + 1 < N) :
    let y := rMinusCodePrefixDart F Q
      (stageRot wR tR (rMinusPrefixBoundaryDart wR tR (i, true)))
    y ∈ Set.range (rMinusCodeHattedDart F Q) ↔
      y = rMinusCodeBoundaryDart wR tR Q (⟨i.val + 1, hi⟩, false) := by
  let σ := kmswInfRot wR (H.1 0)
  let J : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  let d := rMinusPrefixBoundaryDart wR tR (i, true)
  let y := rMinusCodePrefixDart F Q (stageRot wR tR d)
  obtain ⟨n, hn, hne, hgap⟩ := rMinus_hatted_boundary_gap (H := H) hτ hqMode hfin i.val
  have ha := rMinusPrefixDartImage_boundary hτ hqMode i.val _
    (List.getElem?_eq_getElem i.isLt) true
  have hb := rMinusPrefixDartImage_boundary hτ hqMode (i.val + 1) _
    (List.getElem?_eq_getElem hi) false
  rw [← ha] at hne hgap
  rw [← hb] at hne
  change (σ : _ → _)^[n] (rMinusPrefixDartImage (h := h) d) =
    rMinusPrefixDartImage (h := h)
      (rMinusPrefixBoundaryDart wR tR (⟨i.val + 1, hi⟩, false)) at hne
  change ∀ j : ℕ, 0 < j → j < n →
    (σ : _ → _)^[j] (rMinusPrefixDartImage (h := h) d) ∉ Set.range J at hgap
  obtain ⟨t, ht, hte, htgap⟩ := rMinusPrefixDartImage_firstReturn (H := H) d
  have hnP : (σ : _ → _)^[n] (rMinusPrefixDartImage (h := h) d) ∈
      Set.range (rMinusPrefixDartImage (h := h) (k := k)) := by
    rw [hne]
    exact ⟨rMinusPrefixBoundaryDart wR tR (⟨i.val + 1, hi⟩, false), rfl⟩
  have htn : t ≤ n := by
    by_contra hnot
    exact htgap n hn (by omega) hnP
  constructor
  · rintro ⟨e, he⟩
    have hym : rMinusPrefixDartImage (h := h) (stageRot wR tR d) ∈ Set.range J := by
      refine ⟨e, ?_⟩
      have hv := congrArg (fun z => (D z).val) he
      rw [rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_prefix] at hv
      exact hv
    have hnt : n ≤ t := by
      by_contra hnot
      exact hgap t ht (by omega) (hte.symm ▸ hym)
    have hteq : t = n := Nat.le_antisymm htn hnt
    apply (D).injective
    apply Subtype.ext
    rw [rMinusCodeBoundaryDart_eq_prefix,
      rMinusCodeGluedDartEquiv_prefix, rMinusCodeGluedDartEquiv_prefix]
    exact hte.symm.trans (hteq ▸ hne)
  · intro he
    rw [he, rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk]
    exact ⟨_, rfl⟩

include hτ hp P Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at an incoming interior port the splice
is precisely the prefix successor, using the proved block separation. -/
theorem rMinusCodeSpliceRotation_incoming (i : Fin N) (hi : i.val + 1 < N) :
    rMinusCodeSpliceRotation wR tR qR (rMinusCodeBoundaryDart wR tR Q (i, true)) =
      rMinusCodePrefixDart F Q
        (stageRot wR tR (rMinusPrefixBoundaryDart wR tR (i, true))) := by
  let Hrot := rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qR
  let Hemb := Equiv.ofInjective (rMinusCodeHattedDart F Q)
    (rMinusCodeHattedDart_injective wR tR qR)
  let Cemb := Equiv.ofInjective (rMinusCodeBoundaryDart wR tR Q)
    (rMinusCodeBoundaryDart_injective wR tR qR)
  let Prot := stageRot wR tR
  let Pemb := Equiv.ofInjective (rMinusCodePrefixDart F Q)
    (rMinusCodePrefixDart_injective wR tR qR)
  let y := rMinusCodePrefixDart F Q
    (stageRot wR tR (rMinusPrefixBoundaryDart wR tR (i, true)))
  have hP : Prot.extendDomain Pemb (rMinusCodeBoundaryDart wR tR Q (i, true)) = y :=
    Prot.extendDomain_apply_image Pemb (rMinusPrefixBoundaryDart wR tR (i, true))
  change Hrot.extendDomain Hemb ((rMinusBoundaryCornerPerm N).extendDomain Cemb
    (Prot.extendDomain Pemb (rMinusCodeBoundaryDart wR tR Q (i, true)))) = y
  rw [hP]
  by_cases hy : y ∈ Set.range (rMinusCodeHattedDart F Q)
  · have he := (rMinusPrefixRotation_incoming_mem_hatted_iff
      hτ hp P hqMode Tpath hfin hleft hk i hi).mp hy
    change y = rMinusCodeBoundaryDart wR tR Q (⟨i.val + 1, hi⟩, false) at he
    rw [he]
    have hC : (rMinusBoundaryCornerPerm N).extendDomain Cemb
        (rMinusCodeBoundaryDart wR tR Q (⟨i.val + 1, hi⟩, false)) =
          rMinusCodeBoundaryDart wR tR Q (i, true) := by
      have hh := (rMinusBoundaryCornerPerm N).extendDomain_apply_image Cemb
        (⟨i.val + 1, hi⟩, false)
      change (rMinusBoundaryCornerPerm N).extendDomain Cemb
        (rMinusCodeBoundaryDart wR tR Q (⟨i.val + 1, hi⟩, false)) =
          rMinusCodeBoundaryDart wR tR Q
            (rMinusBoundaryCorner N (⟨i.val + 1, hi⟩, false)) at hh
      simpa only [rMinusBoundaryCornerPerm, rMinusBoundaryCorner, Bool.false_eq_true,
        ↓reduceIte, ↓reduceDIte, Nat.zero_lt_succ, Nat.add_sub_cancel] using hh
    rw [hC, rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk]
    have hh := Hrot.extendDomain_apply_image Hemb
      ⟨(((Q).boundary i.val).1, true), rMinus_hatted_boundary_mem _ qR i.val⟩
    change Hrot.extendDomain Hemb
      (rMinusCodeHattedDart F Q
        ⟨(((Q).boundary i.val).1, true), rMinus_hatted_boundary_mem _ qR i.val⟩) =
      rMinusCodeHattedDart F Q
        (Hrot ⟨(((Q).boundary i.val).1, true),
          rMinus_hatted_boundary_mem _ qR i.val⟩) at hh
    change Hrot.extendDomain Hemb (rMinusCodeHattedDart F Q _) = _
    rw [hh, show Hrot = rMinusHattedRotation _ qR from rfl,
      rMinusHattedRotation_boundary_corner hqMode i.val]
    exact (rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk
      ⟨i.val + 1, hi⟩ false).symm
  · have hC : y ∉ Set.range (rMinusCodeBoundaryDart wR tR Q) := by
      rintro ⟨⟨j, b⟩, he⟩
      apply hy
      rw [← he, rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk]
      exact ⟨_, rfl⟩
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ Cemb hC,
      Equiv.Perm.extendDomain_apply_not_subtype _ Hemb hy]

/-- Helper toward Lemma 5.5: the splice successor at each incoming
interior port is the actual whole-side first return. -/
theorem rMinusCodeSpliceRotation_incoming_side_rotation (i : Fin N)
    (hi : i.val + 1 < N) :
    (S).rotation (D (rMinusCodeBoundaryDart wR tR Q (i, true))).val
      (D (rMinusCodeSpliceRotation wR tR qR
        (rMinusCodeBoundaryDart wR tR Q (i, true)))).val := by
  rw [rMinusCodeSpliceRotation_incoming hτ hp P hqMode Tpath hfin hleft hk i hi,
    rMinusCodeBoundaryDart_eq_prefix,
    rMinusCodeGluedDartEquiv_prefix, rMinusCodeGluedDartEquiv_prefix]
  exact rMinus_positive_incoming_side_rotation hτ hp P hqMode Tpath hfin hleft hk
    i.val _ _ (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)

/-- Helper toward Lemma 5.5: the splice successor at each outgoing
interior port is the actual whole-side first return. -/
theorem rMinusCodeSpliceRotation_outgoing_side_rotation (i : Fin N)
    (hi : i.val + 1 < N) :
    (S).rotation
      (D (rMinusCodeBoundaryDart wR tR Q (⟨i.val + 1, hi⟩, false))).val
      (D (rMinusCodeSpliceRotation wR tR qR
        (rMinusCodeBoundaryDart wR tR Q (⟨i.val + 1, hi⟩, false)))).val := by
  rw [rMinusCodeSpliceRotation_outgoing hτ hp P hqMode Tpath hfin hleft hk i hi,
    rMinusCodeBoundaryDart_eq_hatted hτ hp P hqMode Tpath hfin hleft hk,
    rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_hatted]
  exact rMinus_positive_outgoing_side_rotation hτ hp P hqMode Tpath hfin hleft hk
    i.val _ _ (List.getElem?_eq_getElem i.isLt) (List.getElem?_eq_getElem hi)

/-- Helper toward Lemma 5.5: conjugation of the splice evaluates on
each intrinsic code dart by the proved change of carrier. -/
theorem rMinusGluedSpliceRotation_apply_code (d : RMinusCodeGluedDart F Q) :
    rMinusGluedSpliceRotation hτ hp P hqMode Tpath hfin hleft hk (E d) =
      E (rMinusCodeSpliceRotation wR tR qR d) := by
  unfold rMinusGluedSpliceRotation
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- Helper toward Lemma 5.5: every incoming interior shared dart has
rotation-relation transport to every vertex or dart target cell. -/
theorem rMinusGluedCellEquiv_rotation_incoming_iff (i : Fin N)
    (hi : i.val + 1 < N)
    (v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    let u := Sum.inr (E (rMinusCodeBoundaryDart wR tR Q (i, true)))
    rMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
      geometricSideRelation S .rotation (Φ u) (Φ v) := by
  let d := rMinusCodeBoundaryDart wR tR Q (i, true)
  let R := rMinusCodeSpliceRotation wR tR qR
  have hr := rMinusCodeSpliceRotation_incoming_side_rotation
    hτ hp P hqMode Tpath hfin hleft hk i hi
  cases v with
  | inl v => rfl
  | inr e =>
    change rMinusGluedSpliceRotation hτ hp P hqMode Tpath hfin hleft hk (E d) = e ↔
      (S).rotation (G (E d)).val (G e).val
    rw [rMinusGluedSpliceRotation_apply_code, rMinusCodeToGluedDartEquiv_equiv]
    constructor
    · intro he
      rw [← he, rMinusCodeToGluedDartEquiv_equiv]
      exact hr
    · intro he
      apply (G).injective
      rw [rMinusCodeToGluedDartEquiv_equiv]
      apply Subtype.ext
      exact rMinus_firstReturn_endpoint_unique
        (kmswInfRot wR (H.1 0) : _ → _) {a : ℕ × Bool | a.1 ∈ (S).edges}
        (D (R d)).property (G e).property hr he

/-- Helper toward Lemma 5.5: every outgoing interior shared dart has
rotation-relation transport to every vertex or dart target cell. -/
theorem rMinusGluedCellEquiv_rotation_outgoing_iff (i : Fin N)
    (hi : i.val + 1 < N)
    (v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    let u := Sum.inr (E (rMinusCodeBoundaryDart wR tR Q (⟨i.val + 1, hi⟩, false)))
    rMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
      geometricSideRelation S .rotation (Φ u) (Φ v) := by
  let d := rMinusCodeBoundaryDart wR tR Q (⟨i.val + 1, hi⟩, false)
  let R := rMinusCodeSpliceRotation wR tR qR
  have hr := rMinusCodeSpliceRotation_outgoing_side_rotation
    hτ hp P hqMode Tpath hfin hleft hk i hi
  cases v with
  | inl v => rfl
  | inr e =>
    change rMinusGluedSpliceRotation hτ hp P hqMode Tpath hfin hleft hk (E d) = e ↔
      (S).rotation (G (E d)).val (G e).val
    rw [rMinusGluedSpliceRotation_apply_code, rMinusCodeToGluedDartEquiv_equiv]
    constructor
    · intro he
      rw [← he, rMinusCodeToGluedDartEquiv_equiv]
      exact hr
    · intro he
      apply (G).injective
      rw [rMinusCodeToGluedDartEquiv_equiv]
      apply Subtype.ext
      exact rMinus_firstReturn_endpoint_unique
        (kmswInfRot wR (H.1 0) : _ → _) {a : ℕ × Bool | a.1 ∈ (S).edges}
        (D (R d)).property (G e).property hr he

/-- Helper toward Lemma 5.5: both rotation relations have empty branches
on source vertex cells. -/
theorem rMinusGluedCellEquiv_rotation_vertex_iff
    (u : RMinusGluedVertex hτ hqMode)
    (v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk (.inl u) v ↔
      geometricSideRelation S .rotation (Φ (.inl u)) (Φ v) := by
  cases v <;> rfl

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at boundary index zero the allocated
prefix darts already lie in the hatted block, including both endpoint bits. -/
theorem rMinus_side_darts_eq_hatted_of_zero (hk0 : k = 0) :
    {d : ℕ × Bool | d.1 ∈ (S).edges} =
      Set.range (fun d : {d : ℕ × Bool // d.1 ∈ (Q).edges} => (EH d.val.1, d.val.2)) := by
  have ht : boundaryHitTime wR h k = 0 := by rw [hk0, boundaryHitTime_zero]
  rw [rMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk]
  apply Set.union_eq_right.mpr
  rintro z ⟨d, rfl⟩
  have he : d.1.val = 0 := by
    have hi := d.1.isLt
    have hbnd : (F).nextEdge = 1 := by rw [ht]; rfl
    omega
  refine ⟨⟨(((Q).boundary 0).1, d.2), rMinus_hatted_boundary_mem _ qR 0⟩, ?_⟩
  change (EH ((Q).boundary 0).1, d.2) = (d.1.val, d.2)
  rw [he]
  exact (rMinusPrefixDartImage_boundary hτ hqMode 0 0 (by
    rw [ht]
    rfl) d.2).symm

/-- Helper toward Lemma 5.5: at index zero the original splice gives
the actual successor of every hatted dart, hence also both endpoints of
the one-edge shared segment. -/
theorem rMinusCodeSpliceRotation_zero_side_rotation (hk0 : k = 0)
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges}) :
    (S).rotation (D (rMinusCodeHattedDart F Q d)).val
      (D (rMinusCodeSpliceRotation wR tR qR (rMinusCodeHattedDart F Q d))).val := by
  have ht : boundaryHitTime wR h k = 0 := by rw [hk0, boundaryHitTime_zero]
  have he : rMinusCodeSpliceRotation wR tR qR
      (rMinusCodeHattedDart F Q d) =
      rMinusCodeHattedDart F Q
        (rMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qR d) := by
    rw [ht, rMinusCodeSpliceRotation_zero]
    exact Equiv.Perm.extendDomain_apply_image _
      (Equiv.ofInjective _ (rMinusCodeHattedDart_injective wR 0 qR)) d
  rw [he, rMinusCodeGluedDartEquiv_hatted, rMinusCodeGluedDartEquiv_hatted]
  obtain ⟨n, hn, hne, hgap⟩ := rMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin d
  refine ⟨n, hn, hne, ?_⟩
  intro j hj hjn hmem
  apply hgap j hj hjn
  rw [← rMinus_side_darts_eq_hatted_of_zero hτ hp P hqMode Tpath hfin hleft hk hk0]
  exact hmem

/-- Helper toward Lemma 5.5: every intrinsic code dart has the actual
splice successor at boundary index zero, since the prefix is already hatted. -/
theorem rMinusCodeSpliceRotation_zero_code_side_rotation (hk0 : k = 0)
    (d : RMinusCodeGluedDart F Q) :
    (S).rotation (D d).val (D (rMinusCodeSpliceRotation wR tR qR d)).val := by
  have hm : (D d).val ∈ Set.range
      (fun e : {e : ℕ × Bool // e.1 ∈ (Q).edges} => (EH e.val.1, e.val.2)) := by
    rw [← rMinus_side_darts_eq_hatted_of_zero hτ hp P hqMode Tpath hfin hleft hk hk0]
    exact (D d).property
  obtain ⟨e, he⟩ := hm
  have hecode : rMinusCodeHattedDart F Q e = d := by
    apply (D).injective
    apply Subtype.ext
    rw [rMinusCodeGluedDartEquiv_hatted]
    exact he
  rw [← hecode]
  exact rMinusCodeSpliceRotation_zero_side_rotation hτ hp P hqMode Tpath hfin hleft hk hk0 e

/-- Helper toward Lemma 5.5: the original splice is certified for all
rotation cells at boundary index zero. This includes both endpoint stars
and every interior dart; no claim for negative indices is implied. -/
theorem rMinusGluedCellEquiv_rotation_zero_iff (hk0 : k = 0)
    (u v : Sum (RMinusGluedVertex hτ hqMode) (RMinusGluedDart hτ hqMode)) :
    rMinusSpliceRotationRelation hτ hp P hqMode Tpath hfin hleft hk u v ↔
      geometricSideRelation S .rotation (Φ u) (Φ v) := by
  cases u with
  | inl u =>
    exact rMinusGluedCellEquiv_rotation_vertex_iff hτ hp P hqMode Tpath hfin hleft hk u v
  | inr u =>
    obtain ⟨d, rfl⟩ := (E).surjective u
    let R := rMinusCodeSpliceRotation wR tR qR
    have hr := rMinusCodeSpliceRotation_zero_code_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk hk0 d
    cases v with
    | inl v => rfl
    | inr e =>
      change rMinusGluedSpliceRotation hτ hp P hqMode Tpath hfin hleft hk (E d) = e ↔
        (S).rotation (G (E d)).val (G e).val
      rw [rMinusGluedSpliceRotation_apply_code, rMinusCodeToGluedDartEquiv_equiv]
      constructor
      · intro he
        rw [← he, rMinusCodeToGluedDartEquiv_equiv]
        exact hr
      · intro he
        apply (G).injective
        rw [rMinusCodeToGluedDartEquiv_equiv]
        apply Subtype.ext
        exact rMinus_firstReturn_endpoint_unique
          (kmswInfRot wR (H.1 0) : _ → _) {a : ℕ × Bool | a.1 ∈ (S).edges}
          (D (R d)).property (G e).property hr he

end CodeRotationTransport





































































end DirectedDistances.PaperProofs.Section5


