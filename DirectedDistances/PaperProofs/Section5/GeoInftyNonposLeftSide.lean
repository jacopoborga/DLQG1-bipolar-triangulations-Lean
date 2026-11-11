/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftySideVertices
public import DirectedDistances.PaperProofs.Section5.GeoInftyIndCodeLevel
import DirectedDistances.KMSW.PrimedRotInducedOriented
import Mathlib.Order.Setoid.Basic



















public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Code" => (ℕ → Fin 3) × (ℕ → Option FiniteThinMap)
local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5: the complete two-block code observation. -/
structure LMinusSidePresentation (x : XDP) where
  code : Code

/-- Helper toward Lemma 5.5: the cylinder sigma algebra of both blocks. -/
noncomputable instance (x : XDP) : MeasurableSpace (LMinusSidePresentation x) :=
  MeasurableSpace.comap LMinusSidePresentation.code inferInstance

/-- Helper toward Lemma 5.5: retain both generating codes without a default
geometric submap. Whole glued realization is a separate obligation. -/
@[expose] def decodeLMinus (x : XDP) (_k : ℤ) (c : Code) :
    LMinusSidePresentation x := ⟨c⟩

/-- Helper toward Lemma 5.5: measurability for the specified cylinder algebra. -/
theorem measurable_decodeLMinus (x : XDP) (k : ℤ) :
    Measurable (decodeLMinus x k) :=
  measurable_comap_iff.mpr measurable_id

/-- Helper toward Lemma 5.5: neither block loses any code coordinate. -/
theorem decodeLMinus_code (x : XDP) (k : ℤ) (c : Code) :
    (decodeLMinus x k c).code = c := rfl

/-- Helper toward Lemma 5.5: the code projection is measurable. -/
theorem measurable_lMinusSidePresentation_code (x : XDP) :
    Measurable (LMinusSidePresentation.code (x := x)) := comap_measurable _

/-- Helper toward Lemma 5.5: decoding is inverse to reading the two codes. -/
theorem LMinusSidePresentation.decode_code {x : XDP}
    (r : LMinusSidePresentation x) (k : ℤ) :
    decodeLMinus x k r.code = r := rfl

/-- Helper toward Lemma 5.5: measurability of the observed two-block reader. -/
theorem aemeasurable_decodeLMinus_leftSideObsNonpos (x : XDP) (k : ℤ) :
    AEMeasurable (fun W => decodeLMinus x k (leftSideObsNonpos x k W))
      wholePlaneIIDCodeMeasure :=
  (measurable_decodeLMinus x k).comp_aemeasurable
    ((aemeasurable_boundaryFourObservations x k 3).prodMk
      (aemeasurable_boundaryFourObservations x k 1))

/-- Helper toward Lemma 5.5: equal coherent left codes determine the entire
hatted left block, including its boundary and seam, up to marked isomorphism. -/
theorem leftSideCode_markedIso_of_eq (x : XDP) (q q' : Coherent x)
    (hc : thinSideCode x renewalTime renewalTime_positiveSuccessTime .left q.1 =
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .left q'.1) :
    Nonempty (GeometricSideMarkedIso
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q')) := by
  obtain ⟨I⟩ :=
    ((DirectedDistances.PaperProofs.SourceResults.thin_ind x).2.1 .left q q').mp hc
  exact ⟨I.whole⟩

/-- Helper toward Lemma 5.5: partial realization of the hatted block only.
Its code fidelity precedes this choice; absent coherent codes return `none`.
This is not a realization of the glued side. -/
@[expose] noncomputable def LMinusSidePresentation.hattedRealization {x : XDP}
    (r : LMinusSidePresentation x) : Option GeometricSideSubmap :=
  if h : ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .left q.1 = r.code.2
  then some (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime
    .left h.choose)
  else none

/-- Helper toward Lemma 5.5: invalid hatted codes have no hatted realization. -/
theorem LMinusSidePresentation.hattedRealization_eq_none_iff {x : XDP}
    (r : LMinusSidePresentation x) :
    r.hattedRealization = none ↔ ¬ ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .left q.1 = r.code.2 := by
  unfold LMinusSidePresentation.hattedRealization
  split <;> simp only [Option.some_ne_none, not_true_eq_false, not_false_eq_true, *]

/-- Helper toward Lemma 5.5: each returned hatted block has exactly its code. -/
theorem LMinusSidePresentation.hattedRealization_eq_some_spec {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (hM : r.hattedRealization = some M) :
    ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .left q.1 = r.code.2 ∧
      geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q = M := by
  unfold LMinusSidePresentation.hattedRealization at hM
  split at hM
  · rename_i h
    exact ⟨h.choose, h.choose_spec, Option.some.inj hM⟩
  · cases hM

/-- Helper toward Lemma 5.5: existence of the observed hatted block. -/
theorem decodeLMinus_leftSideObsNonpos_hattedRealization_isSome (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) (hq : boundaryFutureHattedPath k W ∈ Coherent x) :
    (decodeLMinus x k (leftSideObsNonpos x k W)).hattedRealization.isSome := by
  unfold LMinusSidePresentation.hattedRealization
  rw [dite_eq_left ⟨⟨boundaryFutureHattedPath k W, hq⟩, rfl⟩]
  rfl

/-- Helper toward Lemma 5.5: the observed hatted block has a realization a.s. -/
theorem ae_decodeLMinus_leftSideObsNonpos_hattedRealization_isSome (x : XDP) (k : ℤ) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (decodeLMinus x k (leftSideObsNonpos x k W)).hattedRealization.isSome := by
  filter_upwards [(boundaryFutureThinSides_package x k).2.2.2.2.2] with W hq
  exact decodeLMinus_leftSideObsNonpos_hattedRealization_isSome x k W hq

/-- Helper toward Lemma 5.5: the partial hatted realization of the observed
pair is marked-isomorphic to the actual coherent hatted left block. -/
theorem boundaryFutureHattedLeft_markedIso_decodeLMinus (x : XDP) (k : ℤ)
    (W : ℤ → Fin 3) (hq : boundaryFutureHattedPath k W ∈ Coherent x) :
    Nonempty (GeometricSideMarkedIso
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left
        ⟨boundaryFutureHattedPath k W, hq⟩)
      ((decodeLMinus x k (leftSideObsNonpos x k W)).hattedRealization.get
        (decodeLMinus_leftSideObsNonpos_hattedRealization_isSome x k W hq))) := by
  let r := decodeLMinus x k (leftSideObsNonpos x k W)
  have hs := decodeLMinus_leftSideObsNonpos_hattedRealization_isSome x k W hq
  obtain ⟨q', hcode, hside⟩ := r.hattedRealization_eq_some_spec
    (r.hattedRealization.get hs) (Option.some_get hs).symm
  rw [← hside]
  exact leftSideCode_markedIso_of_eq x ⟨boundaryFutureHattedPath k W, hq⟩ q' hcode.symm

/-- Helper toward Lemma 5.5: the measurable two-code presentations have
the same law at every nonpositive index, including zero. This is a law of
presentations; a whole geometric-side law still requires the glued decoder. -/
theorem decodeLMinus_leftSideObsNonpos_law_eq_zero (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    wholePlaneIIDCodeMeasure.map (fun W => decodeLMinus x k (leftSideObsNonpos x k W)) =
      wholePlaneIIDCodeMeasure.map (fun W => decodeLMinus x 0 (leftSideObsNonpos x 0 W)) := by
  have hm (j : ℤ) : AEMeasurable (leftSideObsNonpos x j) wholePlaneIIDCodeMeasure :=
    (aemeasurable_boundaryFourObservations x j 3).prodMk
      (aemeasurable_boundaryFourObservations x j 1)
  change wholePlaneIIDCodeMeasure.map (decodeLMinus x k ∘ leftSideObsNonpos x k) =
    wholePlaneIIDCodeMeasure.map (decodeLMinus x k ∘ leftSideObsNonpos x 0)
  rw [← AEMeasurable.map_map_of_aemeasurable
    (measurable_decodeLMinus x k).aemeasurable (hm k),
    ← AEMeasurable.map_map_of_aemeasurable
      (measurable_decodeLMinus x k).aemeasurable (hm 0),
    leftSideObsNonpos_law_eq_zero x k hk]

/-- Helper toward Lemma 5.5: the permanent upper-right boundary is read
from the primed code itself, by eventual stabilization of its reversed stack. -/
@[expose] def lMinusPrimedBoundaryEdge (p : ℕ → Fin 3) (i e : ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → (kmswStage p n).UR.reverse[i]? = some e

/-- Helper toward Lemma 5.5: a permanent boundary index has at most one edge ID. -/
theorem lMinusPrimedBoundaryEdge_unique (p : ℕ → Fin 3) (i e f : ℕ)
    (he : lMinusPrimedBoundaryEdge p i e) (hf : lMinusPrimedBoundaryEdge p i f) : e = f := by
  obtain ⟨N, hN⟩ := he
  obtain ⟨M, hM⟩ := hf
  exact Option.some.inj ((hN (max N M) (le_max_left _ _)).symm.trans
    (hM (max N M) (le_max_right _ _)))

/-- Helper toward Lemma 5.5: the shared-edge gluing is read from the primed
permanent upper-right stack and the marked boundary of the hatted left block.
Only edge IDs enter this relation. -/
@[expose] def lMinusCodeEdgeGluing {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) : Sum ℕ M.edges → Sum ℕ M.edges → Prop
  | .inl a, .inr b => ∃ i, lMinusPrimedBoundaryEdge r.code.1 i a ∧
      (M.boundary i).1 = b.val
  | _, _ => False

/-- Helper toward Lemma 5.5: equivalence closure glues the two edge-ID blocks
along exactly the code-specified shared boundary. -/
@[expose] def lMinusCodeEdgeSetoid {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) : Setoid (Sum ℕ M.edges) :=
  Relation.EqvGen.setoid (lMinusCodeEdgeGluing r M)

/-- Helper toward Lemma 5.5: the edge carrier of the code-based gluing.
This carrier is defined independently of a whole-plane embedding. -/
abbrev LMinusCodeGluedEdge {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) := Quotient (lMinusCodeEdgeSetoid r M)

/-- Helper toward Lemma 5.5: a permanent primed edge has a unique boundary
index. The proof uses stack edge IDs and nodup, including parallel edges. -/
theorem lMinusPrimedBoundaryEdge_index_unique (p : ℕ → Fin 3) (i j e : ℕ)
    (hi : lMinusPrimedBoundaryEdge p i e) (hj : lMinusPrimedBoundaryEdge p j e) :
    i = j := by
  obtain ⟨N, hN⟩ := hi
  obtain ⟨M, hM⟩ := hj
  have hi' := hN (max N M) (le_max_left _ _)
  have hj' := hM (max N M) (le_max_right _ _)
  have hn : (kmswStage p (max N M)).UR.reverse.Nodup :=
    List.nodup_reverse.mpr (kmswStage_status p (max N M)).2.2.2.1
  exact hn.eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp hi').1
    (hi'.trans hj'.symm)

/-- Helper toward Lemma 5.5: the code gluing has only identity and one
shared-boundary identification; this relation is used to check its closure. -/
@[expose] def lMinusCodeEdgeNormalRelation {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap) :
    Sum ℕ M.edges → Sum ℕ M.edges → Prop
  | .inl a, .inl b => a = b
  | .inr a, .inr b => a = b
  | .inl a, .inr b => lMinusCodeEdgeGluing r M (.inl a) (.inr b)
  | .inr a, .inl b => lMinusCodeEdgeGluing r M (.inl b) (.inr a)

/-- Helper toward Lemma 5.5: a coherent hatted left block has injective
boundary edge IDs, independently of any whole-plane embedding. -/
theorem lMinus_hatted_boundary_edge_injective (x : XDP) (q : Coherent x) :
    Function.Injective (fun i =>
      ((geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).boundary i).1) :=
  (kmswLeftBoundary_infinite_present_path _
    (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)).1

/-- Helper toward Lemma 5.5: equivalence closure adds no additional edge
identifications. Both code blocks embed injectively in their intrinsic gluing. -/
theorem lMinusCodeEdgeSetoid_iff {x : XDP} (r : LMinusSidePresentation x)
    (q : Coherent x)
    (a b : Sum ℕ (geometricSideSubmap x renewalTime
      renewalTime_positiveSuccessTime .left q).edges) :
    lMinusCodeEdgeSetoid r _ a b ↔ lMinusCodeEdgeNormalRelation r _ a b := by
  let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q
  have hl (a c : ℕ) (b : M.edges)
      (hab : lMinusCodeEdgeGluing r M (.inl a) (.inr b))
      (hcb : lMinusCodeEdgeGluing r M (.inl c) (.inr b)) : a = c := by
    obtain ⟨i, hi, hib⟩ := hab
    obtain ⟨j, hj, hjb⟩ := hcb
    have hij := lMinus_hatted_boundary_edge_injective x q (hib.trans hjb.symm)
    subst j
    exact lMinusPrimedBoundaryEdge_unique r.code.1 i a c hi hj
  have hr (a : ℕ) (b c : M.edges)
      (hab : lMinusCodeEdgeGluing r M (.inl a) (.inr b))
      (hac : lMinusCodeEdgeGluing r M (.inl a) (.inr c)) : b = c := by
    obtain ⟨i, hi, hib⟩ := hab
    obtain ⟨j, hj, hjc⟩ := hac
    have hij := lMinusPrimedBoundaryEdge_index_unique r.code.1 i j a hi hj
    subst j
    exact Subtype.ext (hib.symm.trans hjc)
  let R := lMinusCodeEdgeNormalRelation r M
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
  · exact (show lMinusCodeEdgeSetoid r M ≤
        (⟨R, hrefl, hsymm, htrans⟩ : Setoid (Sum ℕ M.edges)) from by
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

/-- Helper toward Lemma 5.5: the intrinsic primed edge injection. -/
theorem lMinusCodeGluedEdge_primed_injective {x : XDP} (r : LMinusSidePresentation x)
    (q : Coherent x) : Function.Injective (fun e : ℕ =>
      (⟦Sum.inl e⟧ : LMinusCodeGluedEdge r
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q))) := by
  intro a b hab
  exact (lMinusCodeEdgeSetoid_iff r q _ _).mp (Quotient.exact hab)

/-- Helper toward Lemma 5.5: the intrinsic hatted edge injection. -/
theorem lMinusCodeGluedEdge_hatted_injective {x : XDP} (r : LMinusSidePresentation x)
    (q : Coherent x) : Function.Injective (fun e =>
      (⟦Sum.inr e⟧ : LMinusCodeGluedEdge r
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q))) := by
  intro a b hab
  exact (lMinusCodeEdgeSetoid_iff r q _ _).mp (Quotient.exact hab)

/-- Helper toward Lemma 5.5: intrinsic darts retain the glued edge ID and
a separate endpoint bit, including both darts of every missing edge. -/
abbrev LMinusCodeGluedDart {x : XDP} (r : LMinusSidePresentation x)
    (M : GeometricSideSubmap) := LMinusCodeGluedEdge r M × Bool

/-- Helper toward Lemma 5.5: the primed endpoint correction is read from
the permanent upper-right stack, without a whole-plane vertex embedding. -/
@[expose] noncomputable def lMinusCodePrimedSideFlip {x : XDP}
    (r : LMinusSidePresentation x) (e : ℕ) : Bool :=
  decide (∃ i, lMinusPrimedBoundaryEdge r.code.1 i e)

/-- Helper toward Lemma 5.5: the primed block embeds in intrinsic darts. -/
@[expose] noncomputable def lMinusCodePrimedDart {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap) (d : ℕ × Bool) :
    LMinusCodeGluedDart r M :=
  (⟦Sum.inl d.1⟧, d.2 ^^ lMinusCodePrimedSideFlip r d.1)

/-- Helper toward Lemma 5.5: the hatted block embeds in intrinsic darts. -/
@[expose] def lMinusCodeHattedDart {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap)
    (d : {d : ℕ × Bool // d.1 ∈ M.edges}) : LMinusCodeGluedDart r M :=
  (⟦Sum.inr ⟨d.val.1, d.property⟩⟧, d.val.2)

/-- Helper toward Lemma 5.5: primed intrinsic dart IDs are injective. -/
theorem lMinusCodePrimedDart_injective {x : XDP} (r : LMinusSidePresentation x)
    (q : Coherent x) : Function.Injective (lMinusCodePrimedDart r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q)) := by
  intro a b hab
  have he := lMinusCodeGluedEdge_primed_injective r q (congrArg Prod.fst hab)
  obtain ⟨a, c⟩ := a
  obtain ⟨b, d⟩ := b
  dsimp at he
  subst b
  have hb := congrArg Prod.snd hab
  change (c ^^ lMinusCodePrimedSideFlip r a) =
    (d ^^ lMinusCodePrimedSideFlip r a) at hb
  refine Prod.ext rfl ?_
  exact Bool.xor_left_inj.mp hb

/-- Helper toward Lemma 5.5: hatted intrinsic dart IDs are injective. -/
theorem lMinusCodeHattedDart_injective {x : XDP} (r : LMinusSidePresentation x)
    (q : Coherent x) : Function.Injective (lMinusCodeHattedDart r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q)) := by
  intro a b hab
  have he := lMinusCodeGluedEdge_hatted_injective r q (congrArg Prod.fst hab)
  have hb : a.val.2 = b.val.2 := congrArg
    (fun z : LMinusCodeGluedDart r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q) => z.2) hab
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val he) hb

/-- Helper toward Lemma 5.5: every indexed hatted boundary edge belongs to
the coherent block's geometric carrier. -/
theorem lMinus_hatted_boundary_mem (x : XDP) (q : Coherent x) (i : ℕ) :
    ((geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).boundary i).1 ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).edges := by
  apply Set.mem_iUnion.mpr
  refine ⟨i + 1, ?_⟩
  exact thinMapBoundaryDart_mem_sourceAncestorEdges _
    (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q) .left i

/-- Helper toward Lemma 5.5: indexed darts of the interface, in intrinsic
glued IDs. No endpoint-based edge identification is used. -/
@[expose] noncomputable def lMinusCodeBoundaryDart {x : XDP}
    (r : LMinusSidePresentation x) (q : Coherent x) (d : ℕ × Bool) :
    LMinusCodeGluedDart r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q) :=
  lMinusCodeHattedDart r _ ⟨(((geometricSideSubmap x renewalTime
    renewalTime_positiveSuccessTime .left q).boundary d.1).1, d.2),
      lMinus_hatted_boundary_mem x q d.1⟩

/-- Helper toward Lemma 5.5: the interface dart enumeration is injective. -/
theorem lMinusCodeBoundaryDart_injective {x : XDP}
    (r : LMinusSidePresentation x) (q : Coherent x) :
    Function.Injective (lMinusCodeBoundaryDart r q) := by
  intro a b hab
  have hd := lMinusCodeHattedDart_injective r q hab
  have he := congrArg (fun d => d.val.1) hd
  exact Prod.ext (lMinus_hatted_boundary_edge_injective x q he)
    (congrArg (fun d => d.val.2) hd)

/-- Helper toward Lemma 5.5: the boundary-chain correction swaps the two
interface darts at each positive boundary vertex and fixes the initial dart. -/
@[expose] def lMinusBoundaryCorner (d : ℕ × Bool) : ℕ × Bool :=
  match d with
  | (i, true) => (i + 1, false)
  | (0, false) => (0, false)
  | (i + 1, false) => (i, true)

/-- Helper toward Lemma 5.5: the boundary correction is an involution. -/
theorem lMinusBoundaryCorner_involutive : Function.Involutive lMinusBoundaryCorner := by
  rintro ⟨i, b⟩
  cases b
  · cases i <;> rfl
  · rfl

/-- Helper toward Lemma 5.5: the boundary correction is a permutation,
constructed from the indexed interface alone. -/
@[expose] def lMinusBoundaryCornerPerm : Equiv.Perm (ℕ × Bool) :=
  ⟨lMinusBoundaryCorner, lMinusBoundaryCorner,
    lMinusBoundaryCorner_involutive, lMinusBoundaryCorner_involutive⟩

/-- Helper toward Lemma 5.5: the coherent hatted left rotation, as a genuine
first-return permutation on its geometric dart carrier. -/
@[expose] noncomputable def lMinusHattedRotation (x : XDP) (q : Coherent x) :
    Equiv.Perm {d : ℕ × Bool // d.1 ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).edges} :=
  drawingFirstReturnPerm
    (monotoneFamilyDrawing (boltzmannKMSWStream (pathCode q.val))
      (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
      (monotone_family_all _))
    {d | d.1 ∈ (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).edges}

/- Helper toward Lemma 5.5: the intrinsic splice candidate is the product
of the two extended block rotations and the interface correction. Its -/
@[expose] noncomputable def lMinusCodeSpliceRotation {x : XDP}
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) :
    Equiv.Perm (LMinusCodeGluedDart r
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q)) :=
  (kmswInfRot r.code.1 hf).extendDomain
      (Equiv.ofInjective _ (lMinusCodePrimedDart_injective r q)) *
    lMinusBoundaryCornerPerm.extendDomain
      (Equiv.ofInjective _ (lMinusCodeBoundaryDart_injective r q)) *
    (lMinusHattedRotation x q).extendDomain
      (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q))

/-- Helper toward Lemma 5.5: splice assembly is bijective without any
geometric rotation or layout premise. This alone is not rotation transport. -/
theorem lMinusCodeSpliceRotation_bijective {x : XDP}
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) :
    Function.Bijective (lMinusCodeSpliceRotation r q hf) :=
  (lMinusCodeSpliceRotation r q hf).bijective

/-- Helper toward Lemma 5.5: the hatted permutation has exactly the
first-return relation recorded by its coherent geometric block. -/
theorem lMinusHattedRotation_iff (x : XDP) (q : Coherent x)
    (d e : {d : ℕ × Bool // d.1 ∈
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).edges}) :
    (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).rotation
      d.val e.val ↔ lMinusHattedRotation x q d = e := by
  let w := boltzmannKMSWStream (pathCode q.val)
  let hf := sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q
  let G := monotoneFamilyDrawing w hf (monotone_family_all w)
  let A : Set (ℕ × Bool) := {a | a.1 ∈
    (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q).edges}
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

/-- Helper toward Lemma 5.5: the hatted left block closes its exterior
corner from the next forward boundary dart to the preceding reverse dart. -/
theorem lMinusHattedRotation_boundary_corner (x : XDP) (q : Coherent x) (i : ℕ) :
    let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .left q
    lMinusHattedRotation x q
        ⟨((M.boundary (i + 1)).1, false), lMinus_hatted_boundary_mem x q (i + 1)⟩ =
      ⟨((M.boundary i).1, true), lMinus_hatted_boundary_mem x q i⟩ := by
  let w := boltzmannKMSWStream (pathCode q.val)
  let hf := sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q
  apply (lMinusHattedRotation_iff x q _ _).mp
  refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
  · have he := kmswInfFaceSucc_left w hf (stageOuterWord_faceSucc w)
      (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q) i
    change (kmswInfRot w hf).symm (kmswLeftBoundaryEdge w i, true) =
      (kmswLeftBoundaryEdge w (i + 1), false) at he
    have hr := congrArg (kmswInfRot w hf) he
    rw [Equiv.apply_symm_apply] at hr
    exact hr.symm
  · intro j hj hj1
    omega

/-- Helper toward Lemma 5.5: a rotation assembly selected only from the
two codes. Invalid hatted codes or non-locally-finite primed codes return
`none`. This is a rotation candidate, not a whole marked-side realization. -/
@[expose] noncomputable def LMinusSidePresentation.rotationAssembly {x : XDP}
    (r : LMinusSidePresentation x) :
    Option (Σ M : GeometricSideSubmap, Equiv.Perm (LMinusCodeGluedDart r M)) :=
  if hq : ∃ q : Coherent x,
      thinSideCode x renewalTime renewalTime_positiveSuccessTime .left q.val = r.code.2
  then if hf : KMSWFiniteIncidence r.code.1
    then some ⟨geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime
      .left hq.choose, lMinusCodeSpliceRotation r hq.choose hf⟩
    else none
  else none

/-- Helper toward Lemma 5.5: exact existence criterion for the code-only
rotation candidate. It asserts no geometric-side identification. -/
theorem LMinusSidePresentation.rotationAssembly_isSome_iff {x : XDP}
    (r : LMinusSidePresentation x) :
    r.rotationAssembly.isSome ↔
      (∃ q : Coherent x, thinSideCode x renewalTime renewalTime_positiveSuccessTime
        .left q.val = r.code.2) ∧ KMSWFiniteIncidence r.code.1 := by
  unfold LMinusSidePresentation.rotationAssembly
  split
  · rename_i hq
    split <;> simp_all only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
      true_and, and_self]
  · rename_i hq
    simp only [Option.isSome_none, Bool.false_eq_true, hq, false_and]

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

local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.left
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "U" => boundaryGluingFutureStream W h k
local notation "EP" => boundaryGluingPrimedEdgeMap W h k hτ
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "VP" => boundaryGluingPrimedVertexMap W h k hτ
local notation "VH" => boundaryGluingHatVertexMap W h k hτ
local notation "B" => primedBeta0EdgeIndex U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin
local notation "rL" => decodeLMinus (ite (longest = true) XDP.ldp XDP.sdp) k
  (leftSideObsNonpos (ite (longest = true) XDP.ldp XDP.sdp) k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  Coherent (ite (longest = true) XDP.ldp XDP.sdp))

/-- Helper toward Lemma 5.5: every shared primed upper-right edge reverses
its local side bit. This follows from its C13 creation, including index zero;
the retained missing primed root is a different edge. -/
theorem lMinusPrimedLimitSideFlip_beta (i : ℕ) :
    primedLimitSideFlip U hτ (B i) = true := by
  let p := primedCode (primedSimInput U) hτ
  let m := primedIntervalBase (primedSimInput U) hτ i
  have hc : p m = 1 := by
    cases i with
    | zero =>
      change primedCode (primedSimInput U) hτ
        (primedIntervalBase (primedSimInput U) hτ 0) = 1
      rw [primedIntervalBase_zero]
      exact primedCode_zero _ hτ
    | succ i => exact (primedCrossing_codes U hτ i).1
  have he : (B i) = (kmswMissingRootStage p m).nextEdge + 1 :=
    primedBeta0EdgeIndex_eq_creation U hτ hfin (hatBoundaryHitWitnesses U hτ) hfin i
  have hb : (B i) < (kmswMissingRootStage p (m + 1)).nextEdge := by
    rw [he]
    simp [kmswMissingRootStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep,
      State.addEdge]
  rw [primedLimitSideFlip_eq_stage U hτ (m + 1) ⟨B i, hb⟩]
  exact (primedSideFlip_eq_true_iff U hτ (m + 1) ⟨B i, hb⟩).mpr
    ⟨i, by dsimp [m]; omega, he⟩

/-- Helper toward Lemma 5.5: the observed first block is exactly the primed
stream used by the geometric boundary gluing. -/
theorem lMinus_primed_observation_code :
    (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W).1 =
      primedCode (primedSimInput U) hτ := by
  change hatLawPrimedCodes (boundaryFutureCode k W) = _
  have hs : HasFlowLineHits (fun j => boundaryFutureCode k W (j + 1)) := by
    rw [boundaryFutureCode_tail W h k]
    exact hτ
  simp only [hatLawPrimedCodes, dite_eq_left hs]
  congr 1
  exact congrArg primedSimInput (boundaryFutureCode_tail W h k)

include hτ hfin in
/-- Helper toward Lemma 5.5: local finiteness of the observed primed code
is inherited from the standing future finite-incidence hypothesis. -/
theorem lMinus_primed_observation_finiteIncidence :
    KMSWFiniteIncidence
      (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W).1 := by
  rw [lMinus_primed_observation_code hτ]
  exact primedCode_finiteIncidence U hτ hfin

include hτ hfin hqMode in
/-- Helper toward Lemma 5.5: both observed blocks admit the code-only
rotation assembly. This is not an assertion of geometric rotation transport. -/
theorem decodeLMinus_leftSideObsNonpos_rotationAssembly_isSome :
    (decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
      (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)).rotationAssembly.isSome := by
  apply (LMinusSidePresentation.rotationAssembly_isSome_iff _).mpr
  exact ⟨⟨⟨boundaryFutureHattedPath k W, hqMode⟩, rfl⟩,
    lMinus_primed_observation_finiteIncidence hτ hfin⟩

/-- Helper toward Lemma 5.5: the actual observed primed code reads exactly
the permanent upper-right boundary edge used by the geometric gluing. -/
theorem lMinusPrimedBoundaryEdge_observation (i : ℕ) :
    lMinusPrimedBoundaryEdge (leftSideObsNonpos
      (if longest then XDP.ldp else XDP.sdp) k W).1 i (B i) := by
  change lMinusPrimedBoundaryEdge (hatLawPrimedCodes (boundaryFutureCode k W)) i (B i)
  have hc : hatLawPrimedCodes (boundaryFutureCode k W) =
      primedCode (primedSimInput U) hτ := by
    have hs : HasFlowLineHits (fun j => boundaryFutureCode k W (j + 1)) := by
      rw [boundaryFutureCode_tail W h k]
      exact hτ
    simp only [hatLawPrimedCodes, dite_eq_left hs]
    congr 1
    exact congrArg primedSimInput (boundaryFutureCode_tail W h k)
  rw [hc]
  exact ⟨primedIntervalBase (primedSimInput U) hτ i + 1,
    fun n hn => primedBeta0EdgeIndex_UR_reverse_order U hτ hfin
      (hatBoundaryHitWitnesses U hτ) hfin i n hn⟩

include hfin in
/-- Helper toward Lemma 5.5: the code-only endpoint correction agrees with
the geometric primed correction on every edge, not just shared endpoints. -/
theorem lMinusCodePrimedSideFlip_observation (e : ℕ) :
    lMinusCodePrimedSideFlip
      (decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
        (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)) e =
      primedLimitSideFlip U hτ e := by
  apply Bool.eq_iff_iff.mpr
  change decide (∃ i, lMinusPrimedBoundaryEdge
    (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W).1 i e) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    have he := lMinusPrimedBoundaryEdge_unique _ i e (B i) hi
      (lMinusPrimedBoundaryEdge_observation hτ hfin i)
    rw [he]
    exact lMinusPrimedLimitSideFlip_beta hτ hfin i
  · intro he
    let p := primedCode (primedSimInput U) hτ
    have hb : e < (kmswMissingRootStage p e).nextEdge := by
      rw [(kmswMissingRootStage_agree p e).2.1]
      exact kmsw_edge_allocated_by_self p e
    have hs : primedSideFlip U hτ e ⟨e, hb⟩ = true :=
      (primedLimitSideFlip_eq_stage U hτ e ⟨e, hb⟩).symm.trans he
    obtain ⟨i, _, hi⟩ := (primedSideFlip_eq_true_iff U hτ e ⟨e, hb⟩).mp hs
    have heB : e = B i := hi.trans
      (primedBeta0EdgeIndex_eq_creation U hτ hfin
        (hatBoundaryHitWitnesses U hτ) hfin i).symm
    refine ⟨i, ?_⟩
    rw [heB]
    exact lMinusPrimedBoundaryEdge_observation hτ hfin i

/-- Helper toward Lemma 5.5: cross-block equality is exactly shared-boundary
equality at one beta index. This uses edge IDs, not endpoint coincidence. -/
theorem lMinus_cross_edge_eq_iff (a b : ℕ) :
    EP a = EH b ↔ ∃ i, a = B i ∧
      b = kmswLeftBoundaryEdge (hatCodes U hτ) i := by
  constructor
  · intro hab
    have hm : EH b ∈ boundaryGluingPrimedEdges W h k hτ ∩ Set.range EH :=
      ⟨⟨a, hab⟩, ⟨b, rfl⟩⟩
    rw [boundaryGluingPrimedEdges_inter_hatRange W h k hτ hfin] at hm
    obtain ⟨i, hi⟩ := hm
    refine ⟨i, ?_, (boundaryGluingHatEdgeMap_injective W h k hτ hi).symm⟩
    apply boundaryGluingPrimedEdgeMap_injective W h k hτ
    exact hab.trans (hi.symm.trans (boundaryGluingBeta_edge_primed W h k hτ hfin i).1)
  · rintro ⟨i, rfl, rfl⟩
    exact (boundaryGluingBeta_edge_primed W h k hτ hfin i).1.symm

include hfin in
/-- Helper toward Lemma 5.5: the code-read primed boundary identifies the
same geometric edge with the hatted block; invalid boundary IDs cannot glue. -/
theorem lMinus_code_boundary_gluing (i a : ℕ)
    (ha : lMinusPrimedBoundaryEdge (leftSideObsNonpos
      (if longest then XDP.ldp else XDP.sdp) k W).1 i a) :
    EP a = EH (kmswLeftBoundaryEdge (hatCodes U hτ) i) := by
  have he := lMinusPrimedBoundaryEdge_unique _ i a (B i) ha
    (lMinusPrimedBoundaryEdge_observation hτ hfin i)
  rw [he]
  exact (boundaryGluingBeta_edge_primed W h k hτ hfin i).1.symm

/-- Helper toward Lemma 5.5: the two geometric edge-ID blocks before gluing. -/
abbrev LMinusBlockEdge := Sum ℕ (Q).edges

/-- Helper toward Lemma 5.5: the edge image of each block, preserving IDs. -/
@[expose] noncomputable def lMinusBlockEdgeImage :
    LMinusBlockEdge hqMode → ℕ := Sum.elim EP (fun e => EH e.val)

/-- Helper toward Lemma 5.5: geometric gluing identifies edge IDs precisely
when their existing embeddings agree, including missing and parallel edges. -/
abbrev LMinusGluedEdge := Quotient (Setoid.ker (lMinusBlockEdgeImage hτ hqMode))

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the glued edge image is exactly the actual
nonpositive left-side geometric edge carrier. -/
theorem lMinusBlockEdgeImage_range :
    Set.range (lMinusBlockEdgeImage hτ hqMode) = (S).edges := by
  rw [(boundaryGluing_nonpos_side_identities W h k hτ longest hp P
    hqMode Tpath hfin hleft hk).1]
  ext e
  constructor
  · rintro ⟨a | b, rfl⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨b.val, b.property, rfl⟩
  · rintro (⟨a, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact ⟨Sum.inl a, rfl⟩
    · exact ⟨Sum.inr ⟨b, hb⟩, rfl⟩

/-- Helper toward Lemma 5.5: the quotient retains every actual left-side
edge exactly once. Only proved edge identities enter its construction. -/
@[expose] noncomputable def lMinusGluedEdgeEquiv :
    LMinusGluedEdge hτ hqMode ≃ (S).edges :=
  (Setoid.quotientKerEquivRange (lMinusBlockEdgeImage hτ hqMode)).trans
    (Set.equivOfEq (lMinusBlockEdgeImage_range hτ hp P hqMode Tpath hfin hleft hk))

/-- Helper toward Lemma 5.5: primed edge IDs remain distinct after gluing. -/
theorem lMinusGluedEdge_primed_injective :
    Function.Injective (fun a : ℕ =>
      (⟦Sum.inl a⟧ : LMinusGluedEdge hτ hqMode)) := by
  intro a b hab
  exact boundaryGluingPrimedEdgeMap_injective W h k hτ (Quotient.exact hab)

/-- Helper toward Lemma 5.5: hatted edge IDs remain distinct after gluing. -/
theorem lMinusGluedEdge_hatted_injective :
    Function.Injective (fun a : (Q).edges =>
      (⟦Sum.inr a⟧ : LMinusGluedEdge hτ hqMode)) := by
  intro a b hab
  exact Subtype.ext (boundaryGluingHatEdgeMap_injective W h k hτ (Quotient.exact hab))

/-- Helper toward Lemma 5.5: the quotient glues precisely the shared
boundary edge pair at each index; endpoint equality is never used. -/
theorem lMinusGluedEdge_cross_eq_iff (a : ℕ) (b : (Q).edges) :
    (⟦Sum.inl a⟧ : LMinusGluedEdge hτ hqMode) = ⟦Sum.inr b⟧ ↔
      ∃ i, a = B i ∧ b.val = kmswLeftBoundaryEdge (hatCodes U hτ) i := by
  rw [Quotient.eq]
  exact lMinus_cross_edge_eq_iff hτ hfin a b.val

include hτ in
/-- Helper toward Lemma 5.5: the hatted block's boundary marking reads the
same left-boundary edge IDs used in the shared-boundary identification. -/
theorem lMinus_hatted_boundary (i : ℕ) :
    ((Q).boundary i).1 = kmswLeftBoundaryEdge (hatCodes U hτ) i := by
  change kmswLeftBoundaryEdge
    (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) i = _
  rw [boundaryGluing_decoded_stream W h k hτ]

include hfin in
/-- Helper toward Lemma 5.5: the equivalence closure of code-read boundary
edge pairs is exactly equality of embedded geometric edge IDs. Thus the
code-based gluing identifies neither parallel edges nor extra interior edges. -/
theorem lMinusCodeEdgeSetoid_eq_ker :
    lMinusCodeEdgeSetoid
      (decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
        (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)) Q =
      Setoid.ker (lMinusBlockEdgeImage hτ hqMode) := by
  apply le_antisymm
  · apply Setoid.eqvGen_le
    intro a b hab
    cases a with
    | inr a => cases b <;> exact hab.elim
    | inl a =>
      cases b with
      | inl b => exact hab.elim
      | inr b =>
        obtain ⟨i, hi, hb⟩ := hab
        change EP a = EH b.val
        have he := lMinus_code_boundary_gluing hτ hfin i a hi
        rw [← lMinus_hatted_boundary hτ hqMode i, hb] at he
        exact he
  · intro a b hab
    have hcross (a : ℕ) (b : (Q).edges) (he : EP a = EH b.val) :
        lMinusCodeEdgeSetoid
          (decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
            (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)) Q
          (Sum.inl a) (Sum.inr b) := by
      obtain ⟨i, ha, hb⟩ := (lMinus_cross_edge_eq_iff hτ hfin a b.val).mp he
      apply Relation.EqvGen.rel
      refine ⟨i, ?_, ?_⟩
      · rw [ha]
        exact lMinusPrimedBoundaryEdge_observation hτ hfin i
      · exact (lMinus_hatted_boundary hτ hqMode i).trans hb.symm
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have he := boundaryGluingPrimedEdgeMap_injective W h k hτ hab
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

/-- Helper toward Lemma 5.5: the explicitly code-glued edge carrier is
equivalent to the actual nonpositive left geometric edge carrier. -/
@[expose] noncomputable def lMinusCodeGluedEdgeEquiv :
    LMinusCodeGluedEdge
      (decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
        (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W)) Q ≃ (S).edges :=
  (Equiv.cast (congrArg Quotient (lMinusCodeEdgeSetoid_eq_ker hτ hqMode hfin))).trans
    (lMinusGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk)

/-- Helper toward Lemma 5.5: changing the proved setoid presentation
does not change a representative's edge ID. -/
private theorem lMinus_quotient_cast_mk {α : Type*} {s t : Setoid α}
    (hst : s = t) (a : α) :
    Equiv.cast (congrArg Quotient hst) (Quotient.mk s a) = Quotient.mk t a := by
  subst t
  rfl

/-- Helper toward Lemma 5.5: the intrinsic edge equivalence evaluates
each block representative at its existing geometric edge embedding. -/
theorem lMinusCodeGluedEdgeEquiv_val (a : LMinusBlockEdge hqMode) :
    (lMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk
      (Quotient.mk _ a)).val = lMinusBlockEdgeImage hτ hqMode a := by
  change (lMinusGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk
    (Equiv.cast (congrArg Quotient (lMinusCodeEdgeSetoid_eq_ker hτ hqMode hfin))
      (Quotient.mk _ a))).val = _
  rw [lMinus_quotient_cast_mk (lMinusCodeEdgeSetoid_eq_ker hτ hqMode hfin)]
  rfl

/-- Helper toward Lemma 5.5: the code-only edge gluing, with a separate
endpoint bit, bijects with all geometric darts of the actual left side. -/
@[expose] noncomputable def lMinusCodeGluedDartEquiv :
    LMinusCodeGluedDart rL Q ≃ {d : ℕ × Bool // d.1 ∈ (S).edges} where
  toFun d := ⟨((lMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk d.1).val,
    d.2), (lMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk d.1).property⟩
  invFun d := ((lMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk).symm
    ⟨d.val.1, d.property⟩, d.val.2)
  left_inv d := by
    obtain ⟨e, b⟩ := d
    change ((lMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk).symm
      (lMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk e), b) = (e, b)
    rw [Equiv.symm_apply_apply]
  right_inv d := by
    apply Subtype.ext
    change ((lMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk
      ((lMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk).symm
        ⟨d.val.1, d.property⟩)).val, d.val.2) = d.val
    rw [Equiv.apply_symm_apply]

/-- Helper toward Lemma 5.5: both endpoint bits of an intrinsic hatted
dart map to the correct geometric dart, with the original edge ID. -/
theorem lMinusCodeGluedDartEquiv_hatted (d : {d : ℕ × Bool // d.1 ∈ (Q).edges}) :
    (lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (lMinusCodeHattedDart rL Q d)).val = (EH d.val.1, d.val.2) :=
  Prod.ext (lMinusCodeGluedEdgeEquiv_val hτ hp P hqMode Tpath hfin hleft hk
    (.inr ⟨d.val.1, d.property⟩)) rfl

/-- Helper toward Lemma 5.5: both endpoint bits of an intrinsic primed
dart map correctly, using only the proved code-derived side correction. -/
theorem lMinusCodeGluedDartEquiv_primed (d : ℕ × Bool) :
    (lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (lMinusCodePrimedDart rL Q d)).val =
      (EP d.1, d.2 ^^ primedLimitSideFlip U hτ d.1) := by
  refine Prod.ext
    (lMinusCodeGluedEdgeEquiv_val hτ hp P hqMode Tpath hfin hleft hk (.inl d.1)) ?_
  change (d.2 ^^ lMinusCodePrimedSideFlip rL d.1) = _
  rw [lMinusCodePrimedSideFlip_observation hτ hfin]

/-- Helper toward Lemma 5.5: the two vertex blocks before geometric gluing. -/
abbrev LMinusBlockVertex := Sum ℕ (Q).vertices

/-- Helper toward Lemma 5.5: the vertex image of each block. -/
@[expose] noncomputable def lMinusBlockVertexImage :
    LMinusBlockVertex hqMode → ℕ := Sum.elim VP (fun v => VH v.val)

/-- Helper toward Lemma 5.5: shared vertices are identified by the actual
geometric embeddings, separately from the edge-ID gluing. -/
abbrev LMinusGluedVertex := Quotient (Setoid.ker (lMinusBlockVertexImage hτ hqMode))

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the glued vertex image equals the actual
nonpositive left vertex carrier, including root and seam vertices. -/
theorem lMinusBlockVertexImage_range :
    Set.range (lMinusBlockVertexImage hτ hqMode) = (S).vertices := by
  rw [boundaryGluing_nonpos_left_vertices hτ hp P hqMode Tpath hfin hleft hk]
  ext v
  constructor
  · rintro ⟨a | b, rfl⟩
    · exact Or.inl ⟨a, Set.mem_univ a, rfl⟩
    · exact Or.inr ⟨b.val, b.property, rfl⟩
  · rintro (⟨a, _, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact ⟨Sum.inl a, rfl⟩
    · exact ⟨Sum.inr ⟨b, hb⟩, rfl⟩

/-- Helper toward Lemma 5.5: the glued vertex quotient bijects with the
actual vertex carrier, with no extra geometric-layout hypothesis. -/
@[expose] noncomputable def lMinusGluedVertexEquiv :
    LMinusGluedVertex hτ hqMode ≃ (S).vertices :=
  (Setoid.quotientKerEquivRange (lMinusBlockVertexImage hτ hqMode)).trans
    (Set.equivOfEq (lMinusBlockVertexImage_range hτ hp P hqMode Tpath hfin hleft hk))

/-- Helper toward Lemma 5.5: both darts of every geometric edge in each block. -/
abbrev LMinusBlockDart := Sum (ℕ × Bool) {d : ℕ × Bool // d.1 ∈ (Q).edges}

/-- Helper toward Lemma 5.5: the primed dart embedding corrects endpoint
order even on missing edges; its edge coordinate is the primed edge-ID map. -/
@[expose] noncomputable def lMinusPrimedDartImage (d : ℕ × Bool) : ℕ × Bool :=
  (EP d.1, d.2 ^^ primedLimitSideFlip U hτ d.1)

/-- Helper toward Lemma 5.5: the future embedding is a first-return
embedding for the run-zero rotation, retaining both sides of missing edges. -/
theorem lMinus_future_firstReturn (d : ℕ × Bool) :
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

/-- Helper toward Lemma 5.5: the endpoint-corrected primed rotation is
first return in the future map. The primed missing root is included. -/
theorem lMinus_primed_future_firstReturn (d : ℕ × Bool) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot U hfin : _ → _)^[n] (primedLimitDartMap U hτ d) =
        primedLimitDartMap U hτ
          (kmswInfRot (primedCode (primedSimInput U) hτ)
            (primedCode_finiteIncidence U hτ hfin) d) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot U hfin : _ → _)^[j] (primedLimitDartMap U hτ d) ∉
          Set.range (primedLimitDartMap U hτ) := by
  let hb := hatBoundaryHitWitnesses U hτ
  let A := primeDartSet U hfin hb
  let G := monotoneFamilyDrawing U hfin (monotone_family_all U)
  let E := primedGeometricDartEquiv U hτ hfin hb
  let ρ := kmswInfRot U hfin
  let n := subsetFirstReturnTime ρ A (drawingPositiveReturn G A) (E d)
  have hn := subsetFirstReturnTime_spec ρ A (drawingPositiveReturn G A) (E d)
  have he := congrArg Subtype.val
    (primedGeometricDartEquiv_rotation U hτ hfin hb d).symm
  refine ⟨n, hn.1, he, ?_⟩
  intro j hj hjn hmem
  obtain ⟨a, ha⟩ := hmem
  apply hn.2.2 j hj hjn
  exact ha ▸ (E a).property

/-- Helper toward Lemma 5.5: successive permanent primed upper-right
edges bound an exterior corner. This uses their stabilized stack positions,
not coincidence of endpoints, so parallel edges remain distinct. -/
theorem lMinusPrimedRotation_boundary_corner (i : ℕ) :
    kmswInfRot (primedCode (primedSimInput U) hτ)
        (primedCode_finiteIncidence U hτ hfin) (B i, false) = (B (i + 1), true) := by
  let p := primedCode (primedSimInput U) hτ
  let hf := primedCode_finiteIncidence U hτ hfin
  have hword (n j e : ℕ) (he : (kmswStage p n).UR.reverse[j]? = some e) :
      (stageOuterWordVal p n)[(kmswStage p n).UL.length +
        ((kmswStage p n).UR.length - 1 - j)]? = some (e, false) := by
    have hj : j < (kmswStage p n).UR.length := by
      simpa only [List.length_reverse] using (List.getElem?_eq_some_iff.mp he).1
    have he' : (kmswStage p n).UR[(kmswStage p n).UR.length - 1 - j]? = some e := by
      rw [List.getElem?_reverse hj] at he
      exact he
    have h1 : (kmswStage p n).UL.length + ((kmswStage p n).UR.length - 1 - j) <
        (((kmswStage p n).UL.map fun e => (e, false)) ++
          ((kmswStage p n).UR.map fun e => (e, false))).length := by simp; omega
    have h2 : (kmswStage p n).UL.length + ((kmswStage p n).UR.length - 1 - j) <
        ((((kmswStage p n).UL.map fun e => (e, false)) ++
          ((kmswStage p n).UR.map fun e => (e, false))) ++
            ((kmswStage p n).LR.reverse.map fun e => (e, true))).length := by
      simp; omega
    rw [stageOuterWordVal_eq_runs, List.getElem?_append_left h2,
      List.getElem?_append_left h1, List.getElem?_append_right (by simp), List.length_map]
    have hidx : (kmswStage p n).UL.length + ((kmswStage p n).UR.length - 1 - j) -
        (kmswStage p n).UL.length = (kmswStage p n).UR.length - 1 - j := by omega
    rw [hidx, List.getElem?_map, he']
    rfl
  have hface : kmswInfFaceSucc p hf (B (i + 1), false) = (B i, false) := by
    apply kmswInfFaceSucc_eq_of_stages
    refine ⟨max (primedIntervalBase (primedSimInput U) hτ i + 1)
      (primedIntervalBase (primedSimInput U) hτ (i + 1) + 1), ?_⟩
    intro n hn
    have hi := primedBeta0EdgeIndex_UR_reverse_order U hτ hfin
      (hatBoundaryHitWitnesses U hτ) hfin i n
      ((Nat.le_max_left _ _).trans hn)
    have hj := primedBeta0EdgeIndex_UR_reverse_order U hτ hfin
      (hatBoundaryHitWitnesses U hτ) hfin (i + 1) n
      ((Nat.le_max_right _ _).trans hn)
    have v1 := hword n (i + 1) (B (i + 1)) hj
    have v2 := hword n i (B i) hi
    have hjlen : i + 1 < (kmswStage p n).UR.length := by
      simpa only [List.length_reverse] using (List.getElem?_eq_some_iff.mp hj).1
    have hidx : (kmswStage p n).UL.length + ((kmswStage p n).UR.length - 1 - (i + 1)) + 1 =
        (kmswStage p n).UL.length + ((kmswStage p n).UR.length - 1 - i) := by omega
    have hk := (List.getElem?_eq_some_iff.mp v1).1
    have hk' := (List.getElem?_eq_some_iff.mp v2).1
    obtain ⟨d, e, hd, he, hde⟩ :=
      outer_faceSucc_exists p n (stageOuterWord_faceSucc p n) _ hk
    rw [Nat.mod_eq_of_lt (by omega), hidx] at he
    exact ⟨d, e, Option.some.inj (hd.symm.trans v1),
      Option.some.inj (he.symm.trans v2), hde⟩
  change (kmswInfRot p hf).symm (B (i + 1), true) = (B i, false) at hface
  have hr := congrArg (kmswInfRot p hf) hface
  rw [Equiv.apply_symm_apply] at hr
  exact hr.symm

/-- Helper toward Lemma 5.5: the corrected primed block embedding is
first return for the run-zero rotation, with edge IDs and side bits intact. -/
theorem lMinusPrimedDartImage_firstReturn (d : ℕ × Bool) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n]
          (lMinusPrimedDartImage hτ d) =
        lMinusPrimedDartImage hτ
          (kmswInfRot (primedCode (primedSimInput U) hτ)
            (primedCode_finiteIncidence U hτ hfin) d) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
          (lMinusPrimedDartImage hτ d) ∉ Set.range (lMinusPrimedDartImage hτ) := by
  let J : (ℕ × Bool) → ℕ × Bool :=
    fun a => (boundaryGluingEdgeMap W h k a.1, a.2)
  have hJ : Function.Injective J := by
    intro a b hab
    have hb := congrArg (fun z : ℕ × Bool => z.2) hab
    exact Prod.ext (boundaryGluingEdgeMap_injective W h k (congrArg Prod.fst hab))
      hb
  exact hatExit_induced_rotation_comp
    (kmswInfRot (primedCode (primedSimInput U) hτ)
      (primedCode_finiteIncidence U hτ hfin))
    (kmswInfRot U hfin) (kmswInfRot (shiftedStream W 0) (H.1 0))
    (primedLimitDartMap U hτ) J hJ
    (lMinus_primed_future_firstReturn hτ hfin)
    (lMinus_future_firstReturn (H := H) hfin) d

/-- Helper toward Lemma 5.5: the primed boundary ports have the hatted
boundary edge IDs and the opposite endpoint bits. -/
theorem lMinusPrimedDartImage_boundary (i : ℕ) (b : Bool) :
    lMinusPrimedDartImage hτ (B i, b) =
      (EH (kmswLeftBoundaryEdge (hatCodes U hτ) i), !b) := by
  apply Prod.ext
  · exact (boundaryGluingBeta_edge_primed W h k hτ hfin i).1.symm
  · change (b ^^ primedLimitSideFlip U hτ (B i)) = !b
    rw [lMinusPrimedLimitSideFlip_beta hτ hfin i, Bool.xor_true]

include hfin in
/-- Helper toward Lemma 5.5: the positive shared vertex has an ambient
arc from its incoming interface dart to its outgoing interface dart with no
primed dart in the open arc. The arc is obtained from actual first return. -/
theorem lMinus_primed_boundary_gap (i : ℕ) :
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n]
          (EH (kmswLeftBoundaryEdge (hatCodes U hτ) i), true) =
        (EH (kmswLeftBoundaryEdge (hatCodes U hτ) (i + 1)), false) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
          (EH (kmswLeftBoundaryEdge (hatCodes U hτ) i), true) ∉
            Set.range (lMinusPrimedDartImage hτ) := by
  have hr := lMinusPrimedDartImage_firstReturn (H := H) hτ hfin (B i, false)
  rw [lMinusPrimedRotation_boundary_corner hτ hfin i,
    lMinusPrimedDartImage_boundary hτ hfin i false,
    lMinusPrimedDartImage_boundary hτ hfin (i + 1) true] at hr
  exact hr

/-- Helper toward Lemma 5.5: the full hatted embedding is first return
in run zero, before restricting to the hatted left side. -/
theorem lMinus_hatted_ambient_firstReturn (d : ℕ × Bool) :
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
    (hatInfRot_firstReturn U hτ hfin) (lMinus_future_firstReturn (H := H) hfin) d

include hfin in
/-- Helper toward Lemma 5.5: first return to precisely the retained
hatted left darts gives the hatted left block's own rotation permutation.
This does not identify first return to the union with the primed block. -/
theorem lMinusHattedDartImage_firstReturn
    (d : {d : ℕ × Bool // d.1 ∈ (Q).edges}) :
    let D : {a : ℕ × Bool // a.1 ∈ (Q).edges} → ℕ × Bool :=
      fun a => (EH a.val.1, a.val.2)
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n] (D d) =
        D (lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL d) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j] (D d) ∉ Set.range D := by
  let z := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  let hf := sourceAncestor_finite_incidence
    (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime qL
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
        I (lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL a) ∧
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
    exact lMinus_hatted_ambient_firstReturn (H := H) hτ hfin a
  exact hatExit_induced_rotation_comp
    (lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL)
    (kmswInfRot z hf) (kmswInfRot (shiftedStream W 0) (H.1 0)) I J hJ hI hretJ d

include hfin in
/-- Helper toward Lemma 5.5: the other exterior arc at a positive shared
vertex runs from the outgoing to the incoming interface dart and contains
no hatted-left dart in its open part. -/
theorem lMinus_hatted_boundary_gap (i : ℕ) :
    let D : {a : ℕ × Bool // a.1 ∈ (Q).edges} → ℕ × Bool :=
      fun a => (EH a.val.1, a.val.2)
    ∃ n : ℕ, 0 < n ∧
      (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[n]
          (EH ((Q).boundary (i + 1)).1, false) =
        (EH ((Q).boundary i).1, true) ∧
      ∀ j : ℕ, 0 < j → j < n →
        (kmswInfRot (shiftedStream W 0) (H.1 0) : _ → _)^[j]
          (EH ((Q).boundary (i + 1)).1, false) ∉ Set.range D := by
  have hr := lMinusHattedDartImage_firstReturn (H := H) hτ hqMode hfin
    ⟨(((Q).boundary (i + 1)).1, false), lMinus_hatted_boundary_mem _ qL (i + 1)⟩
  dsimp only at hr
  rw [lMinusHattedRotation_boundary_corner _ qL i] at hr
  exact hr

include hfin in
/-- Helper toward Lemma 5.5: the two positive-interface arcs form one
complete ambient rotation cycle. Their open parts exclude respectively the
primed and hatted-left blocks. This records the cyclic separation with
geometric dart IDs, including the endpoints of parallel edges. -/
theorem lMinus_positive_boundary_rotation_separation (i : ℕ) :
    let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
    let a : ℕ × Bool := (EH ((Q).boundary i).1, true)
    let b : ℕ × Bool := (EH ((Q).boundary (i + 1)).1, false)
    let D : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
      fun d => (EH d.val.1, d.val.2)
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
      (σ : _ → _)^[n] a = b ∧ (σ : _ → _)^[m] b = a ∧
      (∀ j : ℕ, 0 < j → j < n →
        (σ : _ → _)^[j] a ∉ Set.range (lMinusPrimedDartImage hτ)) ∧
      (∀ j : ℕ, 0 < j → j < m → (σ : _ → _)^[j] b ∉ Set.range D) ∧
      (σ : _ → _)^[n + m] a = a ∧
      ∀ j : ℕ, 0 < j → j < n + m → (σ : _ → _)^[j] a ≠ a := by
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  let a : ℕ × Bool := (EH ((Q).boundary i).1, true)
  let b : ℕ × Bool := (EH ((Q).boundary (i + 1)).1, false)
  let D : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
    fun d => (EH d.val.1, d.val.2)
  have hboundary (j : ℕ) : ((Q).boundary j).1 =
      kmswLeftBoundaryEdge (hatCodes U hτ) j := by
    change kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) j = _
    rw [boundaryGluing_decoded_stream W h k hτ]
  have hp := lMinus_primed_boundary_gap (H := H) hτ hfin i
  rw [← hboundary i, ← hboundary (i + 1)] at hp
  obtain ⟨n, hn, hna, hgapP⟩ := hp
  obtain ⟨m, hm, hmb, hgapH⟩ := lMinus_hatted_boundary_gap (H := H) hτ hqMode hfin i
  change (σ : _ → _)^[n] a = b at hna
  change (σ : _ → _)^[m] b = a at hmb
  have haP : a ∈ Set.range (lMinusPrimedDartImage hτ) := by
    refine ⟨(B i, false), ?_⟩
    rw [lMinusPrimedDartImage_boundary hτ hfin i false, ← hboundary i]
    rfl
  have haH : a ∈ Set.range D :=
    ⟨⟨(((Q).boundary i).1, true), lMinus_hatted_boundary_mem _ qL i⟩, rfl⟩
  have hab : b ≠ a := by
    intro he
    have hh : false = true := congrArg Prod.snd he
    exact Bool.false_ne_true hh
  refine ⟨n, m, hn, hm, hna, hmb, hgapP, hgapH, ?_, ?_⟩
  · rw [Nat.add_comm n m, Function.iterate_add_apply, hna, hmb]
  · intro j hj hjnm he
    by_cases hjn : j < n
    · exact hgapP j hj hjn (he.symm ▸ haP)
    · have hstep : (σ : _ → _)^[j] a = (σ : _ → _)^[j - n] b := by
        rw [← hna, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
      by_cases hjeq : j = n
      · subst j
        exact hab (hna.symm.trans he)
      · apply hgapH (j - n) (by omega) (by omega)
        exact (hstep.symm.trans he).symm ▸ haH

/-- Helper toward Lemma 5.5: the corrected dart image of both blocks. -/
@[expose] noncomputable def lMinusBlockDartImage :
    LMinusBlockDart hqMode → ℕ × Bool :=
  Sum.elim (lMinusPrimedDartImage hτ) (fun d => (EH d.val.1, d.val.2))

/-- Helper toward Lemma 5.5: geometric dart gluing, retaining the side bit. -/
abbrev LMinusGluedDart := Quotient (Setoid.ker (lMinusBlockDartImage hτ hqMode))

/-- Helper toward Lemma 5.5: ordered primed dart incidence is preserved,
including missing geometric edges that require the endpoint-order correction. -/
theorem lMinusPrimedDartImage_endpoint (d : ℕ × Bool) :
    kmswLimitDartVertex (shiftedStream W 0) (lMinusPrimedDartImage hτ d) =
      VP (kmswLimitDartVertex (primedCode (primedSimInput U) hτ) d) := by
  obtain ⟨e, b⟩ := d
  have hg := boundaryGluing_future_edge_endpoints W h k (primedLimitEdgeMap U hτ e)
  rcases primedLimitEdgeMap_endpoint_sideflip U hτ e with
    ⟨hf, hw, he⟩ | ⟨hf, hw, he⟩
  · cases b <;>
      simp only [lMinusPrimedDartImage, hf, Bool.xor_false, kmswLimitDartVertex,
        Bool.false_eq_true, ↓reduceIte]
    · exact hg.1.trans (congrArg (boundaryGluingFutureVertexMap W h k) hw)
    · exact hg.2.trans (congrArg (boundaryGluingFutureVertexMap W h k) he)
  · cases b <;>
      simp only [lMinusPrimedDartImage, hf, Bool.false_xor, Bool.true_xor,
        Bool.not_true, kmswLimitDartVertex, Bool.false_eq_true, ↓reduceIte]
    · exact hg.2.trans (congrArg (boundaryGluingFutureVertexMap W h k) he)
    · exact hg.1.trans (congrArg (boundaryGluingFutureVertexMap W h k) hw)

/-- Helper toward Lemma 5.5: the endpoint of each block dart, expressed in
its own block's vertex carrier before gluing. -/
@[expose] noncomputable def lMinusBlockDartEndpoint :
    LMinusBlockDart hqMode → LMinusBlockVertex hqMode
  | .inl d => .inl (kmswLimitDartVertex (primedCode (primedSimInput U) hτ) d)
  | .inr d => .inr ⟨if d.val.2 then (Q).east d.val.1 else (Q).west d.val.1, by
      have he := geometricSideSubmap_endpoints
        (if longest then XDP.ldp else XDP.sdp) renewalTime
        renewalTime_positiveSuccessTime .left
        ⟨boundaryFutureHattedPath k W, hqMode⟩ d.val.1 d.property
      cases hb : d.val.2
      · simpa only [hb, Bool.false_eq_true, ↓reduceIte] using he.1
      · simpa only [hb, ↓reduceIte] using he.2⟩

/-- Helper toward Lemma 5.5: the local block incidences agree after geometric
embedding. Both primed endpoint correction and hatted edge IDs are used. -/
theorem lMinusBlockDartEndpoint_image (d : LMinusBlockDart hqMode) :
    lMinusBlockVertexImage hτ hqMode (lMinusBlockDartEndpoint hτ hqMode d) =
      kmswLimitDartVertex (shiftedStream W 0) (lMinusBlockDartImage hτ hqMode d) := by
  cases d with
  | inl d => exact (lMinusPrimedDartImage_endpoint hτ d).symm
  | inr d =>
    have he := boundaryGluing_hat_edge_endpoints W h k hτ d.val.1
    have hc := boundaryGluing_decoded_stream W h k hτ
    change VH (if d.val.2 then edgeEast
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) d.val.1
      else edgeWest (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) d.val.1) =
        if d.val.2 then edgeEast (shiftedStream W 0) (EH d.val.1)
          else edgeWest (shiftedStream W 0) (EH d.val.1)
    rw [hc]
    split
    · exact he.2.symm
    · exact he.1.symm

/-- Helper toward Lemma 5.5: incidence descends from the two local block
incidences to the glued dart and vertex quotients. -/
@[expose] noncomputable def lMinusGluedDartEndpoint :
    LMinusGluedDart hτ hqMode → LMinusGluedVertex hτ hqMode :=
  Quotient.lift (fun d => ⟦lMinusBlockDartEndpoint hτ hqMode d⟧) (by
    intro a b hab
    apply Quotient.sound
    change lMinusBlockVertexImage hτ hqMode (lMinusBlockDartEndpoint hτ hqMode a) =
      lMinusBlockVertexImage hτ hqMode (lMinusBlockDartEndpoint hτ hqMode b)
    rw [lMinusBlockDartEndpoint_image hτ hqMode a,
      lMinusBlockDartEndpoint_image hτ hqMode b]
    exact congrArg (kmswLimitDartVertex (shiftedStream W 0)) hab)

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the glued dart image is the complete actual
left-side dart carrier, including both darts of every missing edge. -/
theorem lMinusBlockDartImage_range :
    Set.range (lMinusBlockDartImage hτ hqMode) =
      {d : ℕ × Bool | d.1 ∈ (S).edges} := by
  ext d
  constructor
  · rintro ⟨a | b, rfl⟩
    · have he : EP a.1 ∈ Set.range (lMinusBlockEdgeImage hτ hqMode) :=
        ⟨Sum.inl a.1, rfl⟩
      rwa [lMinusBlockEdgeImage_range hτ hp P hqMode Tpath hfin hleft hk] at he
    · have he : EH b.val.1 ∈ Set.range (lMinusBlockEdgeImage hτ hqMode) :=
        ⟨Sum.inr ⟨b.val.1, b.property⟩, rfl⟩
      rwa [lMinusBlockEdgeImage_range hτ hp P hqMode Tpath hfin hleft hk] at he
  · intro hd
    have he : d.1 ∈ Set.range (lMinusBlockEdgeImage hτ hqMode) := by
      rw [lMinusBlockEdgeImage_range hτ hp P hqMode Tpath hfin hleft hk]
      exact hd
    obtain ⟨a | b, ha⟩ := he
    · refine ⟨Sum.inl (a, d.2 ^^ primedLimitSideFlip U hτ a), ?_⟩
      apply Prod.ext ha
      change ((d.2 ^^ primedLimitSideFlip U hτ a) ^^ primedLimitSideFlip U hτ a) = d.2
      cases d.2 <;> cases primedLimitSideFlip U hτ a <;> rfl
    · exact ⟨Sum.inr ⟨(b.val, d.2), b.property⟩, Prod.ext ha rfl⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the retained run-zero darts are the union
of the two actual block images. This is equality of geometric dart sets,
with the primed endpoint correction and both sides of every edge retained. -/
theorem lMinus_side_darts_union :
    {d : ℕ × Bool | d.1 ∈ (S).edges} =
      Set.range (lMinusPrimedDartImage hτ) ∪
        Set.range (fun d : {d : ℕ × Bool // d.1 ∈ (Q).edges} => (EH d.val.1, d.val.2)) := by
  rw [← lMinusBlockDartImage_range hτ hp P hqMode Tpath hfin hleft hk]
  ext d
  constructor
  · rintro ⟨a | b, he⟩
    · exact Or.inl ⟨a, he⟩
    · exact Or.inr ⟨b, he⟩
  · rintro (⟨a, he⟩ | ⟨b, he⟩)
    · exact ⟨Sum.inl a, he⟩
    · exact ⟨Sum.inr b, he⟩

include Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: at a positive interface vertex, retained
side darts in each open rotation interval belong exactly to the other
block. The two intervals traverse a full ambient cycle without repetition. -/
theorem lMinus_positive_boundary_side_separation (i : ℕ) :
    let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
    let a : ℕ × Bool := (EH ((Q).boundary i).1, true)
    let b : ℕ × Bool := (EH ((Q).boundary (i + 1)).1, false)
    let D : {d : ℕ × Bool // d.1 ∈ (Q).edges} → ℕ × Bool :=
      fun d => (EH d.val.1, d.val.2)
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
      (σ : _ → _)^[n] a = b ∧ (σ : _ → _)^[m] b = a ∧
      (σ : _ → _)^[n + m] a = a ∧
      (∀ j : ℕ, 0 < j → j < n + m → (σ : _ → _)^[j] a ≠ a) ∧
      (∀ j : ℕ, 0 < j → j < n →
        (((σ : _ → _)^[j] a).1 ∈ (S).edges ↔ (σ : _ → _)^[j] a ∈ Set.range D)) ∧
      ∀ j : ℕ, 0 < j → j < m →
        (((σ : _ → _)^[j] b).1 ∈ (S).edges ↔
          (σ : _ → _)^[j] b ∈ Set.range (lMinusPrimedDartImage hτ)) := by
  obtain ⟨n, m, hn, hm, hna, hmb, hgapP, hgapH, hperiod, hminimal⟩ :=
    lMinus_positive_boundary_rotation_separation (H := H) hτ hqMode hfin i
  have hset := lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk
  have hmem (d : ℕ × Bool) : d.1 ∈ (S).edges ↔
      d ∈ Set.range (lMinusPrimedDartImage hτ) ∨
        d ∈ Set.range (fun a : {a : ℕ × Bool // a.1 ∈ (Q).edges} => (EH a.val.1, a.val.2)) := by
    exact Set.ext_iff.mp hset d
  refine ⟨n, m, hn, hm, hna, hmb, hperiod, hminimal, ?_, ?_⟩
  · intro j hj hjn
    rw [hmem, or_iff_right (hgapP j hj hjn)]
  · intro j hj hjm
    rw [hmem, or_iff_left (hgapH j hj hjm)]

/-- Helper toward Lemma 5.5: the glued dart quotient is equivalent to all
actual left-side darts, without collapsing edge IDs. -/
@[expose] noncomputable def lMinusGluedDartEquiv :
    LMinusGluedDart hτ hqMode ≃ {d : ℕ × Bool // d.1 ∈ (S).edges} :=
  (Setoid.quotientKerEquivRange (lMinusBlockDartImage hτ hqMode)).trans
    (Set.equivOfEq (lMinusBlockDartImage_range hτ hp P hqMode Tpath hfin hleft hk))

/-- Helper toward Lemma 5.5: intrinsic code darts and the earlier geometric
dart quotient have the same complete edge-ID carrier and endpoint bits. -/
@[expose] noncomputable def lMinusCodeToGluedDartEquiv :
    LMinusCodeGluedDart rL Q ≃ LMinusGluedDart hτ hqMode :=
  (lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).trans
    (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm

/-- Helper toward Lemma 5.5: changing the dart presentation commutes with
its actual geometric embedding. -/
theorem lMinusCodeToGluedDartEquiv_equiv (d : LMinusCodeGluedDart rL Q) :
    lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d) =
        lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d :=
  (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).apply_symm_apply _

/-- Helper toward Lemma 5.5: the code splice candidate on the previous
dart presentation. No rotation of the actual whole side enters this definition;
only the proved carrier equivalence transports the intrinsic permutation. -/
@[expose] noncomputable def lMinusGluedSpliceRotation :
    Equiv.Perm (LMinusGluedDart hτ hqMode) :=
  Equiv.permCongr (lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk)
    (lMinusCodeSpliceRotation rL qL (lMinus_primed_observation_finiteIncidence hτ hfin))

/- Helper toward Lemma 5.5: the candidate rotation branch, separately from
the old incidence skeleton's false rotation branch. Geometric transport of this -/
@[expose] noncomputable def lMinusSpliceRotationRelation :
    Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode) →
      Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode) → Prop
  | .inr d, .inr e => lMinusGluedSpliceRotation hτ hp P hqMode Tpath hfin hleft hk d = e
  | _, _ => False

/-- Helper toward Lemma 5.5: the glued incidence cells biject with all cells
of the actual nonpositive left side. Full rotation and marking fidelity are
separate from this carrier equivalence. -/
@[expose] noncomputable def lMinusGluedCellEquiv :
    Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode) ≃
      GeometricSideCell S :=
  Equiv.sumCongr (lMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk)
    (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk)

/-- Helper toward Lemma 5.5: the vertex equivalence evaluates by the geometric
block image, independently of representatives of the quotient. -/
theorem lMinusGluedVertexEquiv_val (v : LMinusGluedVertex hτ hqMode) :
    (lMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk v).val =
      Setoid.kerLift (lMinusBlockVertexImage hτ hqMode) v := rfl

/-- Helper toward Lemma 5.5: the dart equivalence evaluates by the corrected
geometric block image. -/
theorem lMinusGluedDartEquiv_val (d : LMinusGluedDart hτ hqMode) :
    (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val =
      Setoid.kerLift (lMinusBlockDartImage hτ hqMode) d := rfl

/-- Helper toward Lemma 5.5: the glued endpoint function is the actual
geometric incidence function under the vertex and dart equivalences. -/
theorem lMinusGluedDartEndpoint_equiv (d : LMinusGluedDart hτ hqMode) :
    (lMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk
      (lMinusGluedDartEndpoint hτ hqMode d)).val =
      kmswLimitDartVertex (shiftedStream W 0)
        (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val := by
  refine Quotient.inductionOn d ?_
  intro a
  exact lMinusBlockDartEndpoint_image hτ hqMode a

/-- Helper toward Lemma 5.5: reversal of each local geometric dart. -/
@[expose] def lMinusBlockDartReverse : LMinusBlockDart hqMode → LMinusBlockDart hqMode
  | .inl d => .inl (d.1, !d.2)
  | .inr d => .inr ⟨(d.val.1, !d.val.2), d.property⟩

/-- Helper toward Lemma 5.5: reversal commutes with the corrected block map,
including missing edges whose primed side bit was corrected. -/
theorem lMinusBlockDartReverse_image (d : LMinusBlockDart hqMode) :
    lMinusBlockDartImage hτ hqMode (lMinusBlockDartReverse hqMode d) =
      ((lMinusBlockDartImage hτ hqMode d).1, !(lMinusBlockDartImage hτ hqMode d).2) := by
  cases d with
  | inl d => exact Prod.ext rfl (Bool.not_xor _ _)
  | inr d => rfl

/-- Helper toward Lemma 5.5: geometric opposition descends to the glued darts. -/
@[expose] noncomputable def lMinusGluedDartReverse :
    LMinusGluedDart hτ hqMode → LMinusGluedDart hτ hqMode :=
  Quotient.lift (fun d => ⟦lMinusBlockDartReverse hqMode d⟧) (by
    intro a b hab
    apply Quotient.sound
    change lMinusBlockDartImage hτ hqMode (lMinusBlockDartReverse hqMode a) =
      lMinusBlockDartImage hτ hqMode (lMinusBlockDartReverse hqMode b)
    rw [lMinusBlockDartReverse_image hτ hqMode a,
      lMinusBlockDartReverse_image hτ hqMode b]
    exact congrArg (fun d : ℕ × Bool => (d.1, !d.2)) hab)

/-- Helper toward Lemma 5.5: the glued reversal is actual geometric dart
opposition under the dart equivalence. -/
theorem lMinusGluedDartReverse_equiv (d : LMinusGluedDart hτ hqMode) :
    (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
      (lMinusGluedDartReverse hτ hqMode d)).val =
      ((lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val.1,
        !(lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val.2) := by
  refine Quotient.inductionOn d ?_
  intro a
  exact lMinusBlockDartReverse_image hτ hqMode a

include hτ hk in
/-- Helper toward Lemma 5.5: at a nonpositive hit, future-edge presence
agrees with run-zero presence. The empty upper-left attachment is proved
internally, so no missing-boundary status is added as a premise. -/
theorem lMinus_future_present_iff (e : ℕ) :
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

/-- Helper toward Lemma 5.5: every shared-boundary edge is retained in the
hatted left block, as a geometric edge ID. -/
theorem lMinus_shared_edge_mem (i : ℕ) :
    kmswLeftBoundaryEdge (hatCodes U hτ) i ∈ (Q).edges := by
  have hm := boundaryGluingBetaEdges_subset_leftHatEdges W h k hτ
    (if longest then XDP.ldp else XDP.sdp) hqMode ⟨i, rfl⟩
  obtain ⟨a, ha, hea⟩ := hm
  have he := boundaryGluingHatEdgeMap_injective W h k hτ hea
  exact he ▸ ha

/-- Helper toward Lemma 5.5: directed tail data in the separate blocks.
The primed missing root and missing shared-boundary edges are not oriented. -/
@[expose] noncomputable def lMinusBlockDartOriented : LMinusBlockDart hqMode → Prop
  | .inl d => PrimedEdgePresent U hτ d.1 ∧ d.2 = false
  | .inr d => d.val.1 ∈ (Q).present ∧ d.val.2 = false

/-- Helper toward Lemma 5.5: a glued dart is directed when one of its block
representatives is directed. The shared edge may be missing in the primed
block and present in the hatted block. -/
@[expose] noncomputable def lMinusGluedDartOriented
    (d : LMinusGluedDart hτ hqMode) : Prop :=
  ∃ a : LMinusBlockDart hqMode, ⟦a⟧ = d ∧ lMinusBlockDartOriented hτ hqMode a

include hk in
/-- Helper toward Lemma 5.5: a directed representative maps to a directed
run-zero dart, with its forward side preserved. -/
theorem lMinusBlockDartOriented_image (d : LMinusBlockDart hqMode)
    (hd : lMinusBlockDartOriented hτ hqMode d) :
    EdgePresent (shiftedStream W 0) (lMinusBlockDartImage hτ hqMode d).1 ∧
      (lMinusBlockDartImage hτ hqMode d).2 = false := by
  cases d with
  | inl d =>
    have hp := (primedLimitEdgeMap_present_iff U hτ d.1).mp hd.1
    refine ⟨(lMinus_future_present_iff hτ hk _).mp hp.1, ?_⟩
    change (d.2 ^^ primedLimitSideFlip U hτ d.1) = false
    rw [hd.2, primedLimitSideFlip_of_present U hτ hd.1]
    rfl
  | inr d =>
    have hp := hatCodes_edge_present U hτ d.val.1
    exact ⟨(lMinus_future_present_iff hτ hk _).mp
      (hatLimit_edge_incidence (hatLimitExplicitInput U hτ) hp).1, hd.2⟩

include hk hfin in
/-- Helper toward Lemma 5.5: every directed image dart has a directed block
representative. A missing primed boundary representative is replaced by its
identified hatted representative, rather than incorrectly oriented in place. -/
theorem lMinusBlockDartOriented_preimage (d : LMinusBlockDart hqMode)
    (hpresent : EdgePresent (shiftedStream W 0) (lMinusBlockDartImage hτ hqMode d).1)
    (hforward : (lMinusBlockDartImage hτ hqMode d).2 = false) :
    lMinusGluedDartOriented hτ hqMode ⟦d⟧ := by
  cases d with
  | inr d =>
    refine ⟨Sum.inr d, rfl, ?_, hforward⟩
    change EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) d.val.1
    rw [boundaryGluing_decoded_stream W h k hτ]
    exact hatCodes_edge_present U hτ d.val.1
  | inl d =>
    by_cases hp : PrimedEdgePresent U hτ d.1
    · refine ⟨Sum.inl d, rfl, hp, ?_⟩
      change (d.2 ^^ primedLimitSideFlip U hτ d.1) = false at hforward
      rwa [primedLimitSideFlip_of_present U hτ hp, Bool.xor_false] at hforward
    · have hraw : EdgePresent U (primedLimitEdgeMap U hτ d.1) :=
        (lMinus_future_present_iff hτ hk _).mpr hpresent
      have hh : MhatGeometricEdge U (primedLimitEdgeMap U hτ d.1) := by
        by_contra hn
        exact hp ((primedLimitEdgeMap_present_iff U hτ d.1).mpr ⟨hraw, hn⟩)
      obtain ⟨a, ha⟩ := (hatLimitEdgeMap_geometric_range_iff U hτ _).mpr hh
      have hcross : EP d.1 = EH a :=
        congrArg (boundaryGluingEdgeMap W h k) ha.symm
      obtain ⟨i, he, hi⟩ := (lMinus_cross_edge_eq_iff hτ hfin d.1 a).mp hcross
      let b := kmswLeftBoundaryEdge (hatCodes U hτ) i
      have hb : b ∈ (Q).edges := lMinus_shared_edge_mem hτ hqMode i
      refine ⟨Sum.inr ⟨(b, false), hb⟩, ?_, ?_, rfl⟩
      · apply Quotient.sound
        apply Prod.ext
        · change EH b = EP d.1
          exact (congrArg EH hi).symm.trans hcross.symm
        · exact hforward.symm
      · change EdgePresent (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) b
        rw [boundaryGluing_decoded_stream W h k hτ]
        exact hatCodes_edge_present U hτ b

/-- Helper toward Lemma 5.5: the proved incidence skeleton of the glued
blocks, including their actual directed tails. Rotation, face succession and
boundary/seam marks are not supplied by this partial relation. -/
@[expose] noncomputable def lMinusGluedIncidenceRelation :
    TruncationRelation →
      Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode) →
      Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode) → Prop
  | .vertex, .inl _, _ => True
  | .root, .inl v, _ => Setoid.kerLift (lMinusBlockVertexImage hτ hqMode) v = VH 0
  | .incident, .inr d, .inl v => lMinusGluedDartEndpoint hτ hqMode d = v
  | .opposite, .inr d, .inr e => lMinusGluedDartReverse hτ hqMode d = e
  | .oriented, .inr d, _ => lMinusGluedDartOriented hτ hqMode d
  | _, _, _ => False

local notation "Φ" => lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the glued cell equivalence preserves the vertex tag. -/
theorem lMinusGluedCellEquiv_vertex_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusGluedIncidenceRelation hτ hqMode .vertex u v ↔
      geometricSideRelation S .vertex (Φ u) (Φ v) := by
  cases u <;> cases v <;> rfl

/-- Helper toward Lemma 5.5: the hatted source supplies the correct root of
the glued nonpositive left side. -/
theorem lMinusGluedCellEquiv_root_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusGluedIncidenceRelation hτ hqMode .root u v ↔
      geometricSideRelation S .root (Φ u) (Φ v) := by
  cases u with
  | inl a =>
    change Setoid.kerLift (lMinusBlockVertexImage hτ hqMode) a = VH 0 ↔
      (lMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk a).val =
        boundaryVertex (shiftedStream W 0) h k
    rw [lMinusGluedVertexEquiv_val hτ hp P hqMode Tpath hfin hleft hk,
      boundaryGluingHatVertexMap_zero hτ]
  | inr d => cases v <;> rfl

/-- Helper toward Lemma 5.5: directed presence and forward orientation of
the glued darts agree with those of the actual nonpositive left side. -/
theorem lMinusGluedCellEquiv_oriented_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusGluedIncidenceRelation hτ hqMode .oriented u v ↔
      geometricSideRelation S .oriented (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    change lMinusGluedDartOriented hτ hqMode d ↔
      EdgePresent (shiftedStream W 0)
        (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val.1 ∧
        (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val.2 = false
    constructor
    · rintro ⟨a, ha, hor⟩
      subst d
      exact lMinusBlockDartOriented_image hτ hqMode hk a hor
    · refine Quotient.inductionOn d ?_
      intro a ha
      exact lMinusBlockDartOriented_preimage hτ hqMode hfin hk a ha.1 ha.2

/-- Helper toward Lemma 5.5: the glued cell equivalence preserves the complete
incidence tag, using the proved local block endpoint identities. -/
theorem lMinusGluedCellEquiv_incident_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusGluedIncidenceRelation hτ hqMode .incident u v ↔
      geometricSideRelation S .incident (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    cases v with
    | inr e => rfl
    | inl a =>
      change lMinusGluedDartEndpoint hτ hqMode d = a ↔
        kmswLimitDartVertex (shiftedStream W 0)
          (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val =
            (lMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk a).val
      rw [← lMinusGluedDartEndpoint_equiv hτ hp P hqMode Tpath hfin hleft hk d]
      constructor
      · intro he
        rw [he]
      · intro he
        apply (lMinusGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk).injective
        exact Subtype.ext he

/-- Helper toward Lemma 5.5: the glued cell equivalence preserves opposite
darts, using edge IDs and the corrected primed side bits. -/
theorem lMinusGluedCellEquiv_opposite_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusGluedIncidenceRelation hτ hqMode .opposite u v ↔
      geometricSideRelation S .opposite (Φ u) (Φ v) := by
  cases u with
  | inl a => cases v <;> rfl
  | inr d =>
    cases v with
    | inl a => rfl
    | inr e =>
      change lMinusGluedDartReverse hτ hqMode d = e ↔
        ((lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val.1,
          !(lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val.2) =
            (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk e).val
      rw [← lMinusGluedDartReverse_equiv hτ hp P hqMode Tpath hfin hleft hk d]
      constructor
      · intro he
        rw [he]
      · intro he
        apply (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).injective
        exact Subtype.ext he

/-- Helper toward Lemma 5.5: the finite-only target tag is empty on both
the glued incidence skeleton and the actual whole side. -/
theorem lMinusGluedCellEquiv_target_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusGluedIncidenceRelation hτ hqMode .target u v ↔
      geometricSideRelation S .target (Φ u) (Φ v) := by
  cases u <;> cases v <;> rfl

include Tpath hfin hleft in
/-- Helper toward Lemma 5.5: the indexed hatted geodesic seam maps to the
actual left-side seam with the same geometric edge ID and forward side. -/
theorem lMinus_hatted_seam_image (i : ℕ) :
    (EH ((Q).seam i).1, ((Q).seam i).2) = (S).seam i := by
  exact congrArg (fun e : ℕ => (e, false))
    ((boundaryGluing_geodesicIdentification W h k hτ longest hqMode
      hp Tpath P hfin hleft i).symm)
































end GeometricGluing

end DirectedDistances.PaperProofs.Section5
