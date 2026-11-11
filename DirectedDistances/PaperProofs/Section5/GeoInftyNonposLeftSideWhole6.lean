/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole5

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section DecodedVertexIdentification

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

local notation "X" => (ite (longest = true) XDP.ldp XDP.sdp)
local notation "U" => boundaryGluingFutureStream W h k
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain X renewalTime renewalTime_positiveSuccessTime)
local notation "Q" => geometricSideSubmap X renewalTime
  renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "VP" => boundaryGluingPrimedVertexMap W h k hτ
local notation "VH" => boundaryGluingHatVertexMap W h k hτ
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "EP" => boundaryGluingPrimedEdgeMap W h k hτ
local notation "B" => primedBeta0EdgeIndex U hτ hfin
  (hatBoundaryHitWitnesses U hτ) hfin
local notation "w0" => shiftedStream W 0
local notation "z" => boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
local notation "hf" => lMinus_primed_observation_finiteIncidence hτ hfin

include hτ in
/-- Helper toward Lemma 5.5: the inherited primed vertex identities remain
distinct under their permanent embedding into the run-zero map. -/
theorem lMinusPrimedVertexMap_injective : Function.Injective VP := by
  intro a b hab
  change boundaryGluingFutureVertexMap W h k
      (primedLimitVertexMap U hτ a) =
    boundaryGluingFutureVertexMap W h k
      (primedLimitVertexMap U hτ b) at hab
  have hfuture := boundaryGluingFutureVertexMap_injective W h k hab
  have halloc (v : ℕ) : ∃ m, v <
      (kmswMissingRootStage (primedCode (primedSimInput U) hτ) m).nextVertex :=
    (primedLocalIds_eventually_allocated U hτ).2 v
  exact (primedLimit_maps_injective_on_allocated U hτ).2
    ⟨(halloc a).choose, (halloc a).choose_spec⟩
    ⟨(halloc b).choose, (halloc b).choose_spec⟩ hfuture

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every shared block vertex is an endpoint of
an indexed gluing edge. The incident darts are selected from finite incidence
on the primed block and the endpoint characterization of the hatted carrier;
the initial root is included as boundary index zero. -/
theorem lMinus_shared_vertex_endpoint_interface
    (a : ℕ) (b : (Q).vertices)
    (hab : VP a = VH b.val) :
    ∃ i : ℕ, ∃ s : Bool,
      VP a = kmswLimitDartVertex w0 (EH ((Q).boundary i).1, s) ∧
      VH b.val = kmswLimitDartVertex w0 (EH ((Q).boundary i).1, s) := by
  have hcode : (rL).code.1 =
      primedCode (primedSimInput U) hτ := by
    exact lMinus_primed_observation_code hτ
  obtain ⟨N, hN⟩ := kmsw_vertex_allocated_of_finite_incidence
    (rL).code.1 hf a
  obtain ⟨d, hd⟩ := stageEndpoint_exists (rL).code.1 N a hN
  let p : ℕ × Bool := (d.1.val, d.2)
  have hpv : kmswLimitDartVertex (rL).code.1 p = a := by
    dsimp only [p, kmswLimitDartVertex]
    cases hb : d.2
    · change edgeWest (rL).code.1 d.1.val = a
      exact (edge_endpoints_eq (rL).code.1 d.1.isLt).1.symm.trans
        (by simpa [stageEndpoint, hb] using hd)
    · change edgeEast (rL).code.1 d.1.val = a
      exact (edge_endpoints_eq (rL).code.1 d.1.isLt).2.symm.trans
        (by simpa [stageEndpoint, hb] using hd)
  obtain ⟨e, he, hwest⟩ :=
    (geometricSideSubmap_mem_vertices_iff_west X qL ThinMapSide.left b.val).mp b.property
  have hhatEndpoint := lMinusCodeRawEndpoint_image hτ hp P hqMode Tpath
    hfin hleft hk false (.inr ⟨e, he⟩)
  change VH ((Q).west e) = kmswLimitDartVertex w0 (EH e, false) at hhatEndpoint
  rw [hwest] at hhatEndpoint
  have hprimEndpoint : kmswLimitDartVertex w0 (lMinusPrimedDartImage hτ p) = VP a := by
    rw [lMinusPrimedDartImage_endpoint hτ p, ← hcode, hpv]
  have hv : kmswLimitDartVertex w0 (lMinusPrimedDartImage hτ p) =
      kmswLimitDartVertex w0 (EH e, false) :=
    hprimEndpoint.trans (hab.trans hhatEndpoint)
  rcases lMinus_shared_dart_endpoint_interface hτ hfin p (e, false) hv with
    hroot | ⟨i, hport⟩
  · have hsource : kmswLimitDartVertex z (((Q).boundary 0).1, false) = 0 :=
      (lMinus_hatted_boundary_source_iff hqMode 0 false).mpr ⟨rfl, rfl⟩
    have hedge := boundaryGluing_hat_edge_endpoints W h k hτ ((Q).boundary 0).1
    have hwest0 : edgeWest z ((Q).boundary 0).1 = 0 := by
      simpa only [kmswLimitDartVertex, Bool.false_eq_true, ite_false] using hsource
    have hrootPort : VH 0 = kmswLimitDartVertex w0
        (EH ((Q).boundary 0).1, false) := by
      have hedgeW : VH (edgeWest z ((Q).boundary 0).1) =
          edgeWest w0 (EH ((Q).boundary 0).1) := by
        rw [boundaryGluing_decoded_stream W h k hτ]
        exact hedge.1.symm
      rw [hwest0] at hedgeW
      simpa only [kmswLimitDartVertex, Bool.false_eq_true, ite_false] using hedgeW
    refine ⟨0, false, ?_, ?_⟩
    · exact hprimEndpoint.symm.trans (hroot.trans hrootPort)
    · exact (hab.symm.trans hprimEndpoint.symm).trans (hroot.trans hrootPort)
  · refine ⟨i, true, ?_, ?_⟩
    · have hbdy := lMinus_hatted_boundary hτ hqMode i
      rw [← hbdy] at hport
      exact hprimEndpoint.symm.trans hport
    · have hbdy := lMinus_hatted_boundary hτ hqMode i
      rw [← hbdy] at hport
      exact (hab.symm.trans hprimEndpoint.symm).trans hport

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: equality of inherited vertices across the two
blocks is generated by the shared-edge endpoint relation. -/
theorem lMinusCode_shared_vertex_eq
    (a : ℕ) (b : (Q).vertices)
    (hab : VP a = VH b.val) :
    (⟦Sum.inl a⟧ : LMinusCodeRawVertex rL Q) = ⟦Sum.inr b.val⟧ := by
  obtain ⟨i, s, hAimage, hBimage⟩ :=
    lMinus_shared_vertex_endpoint_interface hτ hp P hqMode Tpath hfin hleft hk a b hab
  let A : Sum ℕ (Q).edges := .inl (B i)
  let Bedge : (Q).edges := ⟨((Q).boundary i).1, lMinus_hatted_boundary_mem X qL i⟩
  let C : Sum ℕ (Q).edges := .inr Bedge
  have hglue : lMinusCodeEdgeGluing rL Q A C := by
    refine ⟨i, ?_, rfl⟩
    exact lMinusPrimedBoundaryEdge_observation hτ hfin i
  have hside : lMinusPrimedDartImage hτ (B i, !s) =
      (EH ((Q).boundary i).1, s) := by
    rw [lMinusPrimedDartImage_boundary hτ hfin i (!s), lMinus_hatted_boundary hτ hqMode i]
    simp only [Bool.not_not]
  have hAendpoint := lMinusCodeRawEndpoint_image hτ hp P hqMode Tpath
    hfin hleft hk s A
  change VP (kmswLimitDartVertex (rL).code.1
      (B i, s ^^ lMinusCodePrimedSideFlip rL (B i))) =
    kmswLimitDartVertex w0 (EP (B i), s) at hAendpoint
  have hEPside : kmswLimitDartVertex w0 (EP (B i), s) =
      kmswLimitDartVertex w0 (EH ((Q).boundary i).1, s) := by
    have hEP : (lMinusPrimedDartImage hτ (B i, !s)).1 = EH ((Q).boundary i).1 :=
      congrArg Prod.fst hside
    exact congrArg (fun e => kmswLimitDartVertex w0 (e, s)) hEP
  have hAvertex : kmswLimitDartVertex (rL).code.1
      (B i, s ^^ lMinusCodePrimedSideFlip rL (B i)) = a := by
    have hA' : VP (kmswLimitDartVertex (rL).code.1
        (B i, s ^^ lMinusCodePrimedSideFlip rL (B i))) = VP a :=
      hAendpoint.trans (hEPside.trans hAimage.symm)
    exact lMinusPrimedVertexMap_injective hτ hA'
  have hBendpoint := lMinusCodeRawEndpoint_image hτ hp P hqMode Tpath
    hfin hleft hk s C
  change VH (if s then (Q).east ((Q).boundary i).1
      else (Q).west ((Q).boundary i).1) =
    kmswLimitDartVertex w0 (EH ((Q).boundary i).1, s) at hBendpoint
  have hendpoint : (if s then (Q).east ((Q).boundary i).1
      else (Q).west ((Q).boundary i).1) = b.val := by
    apply boundaryGluingHatVertexMap_injective W h k hτ
    exact hBendpoint.trans hBimage.symm
  have hrawA : lMinusCodeRawEndpoint rL Q s A = Sum.inl a := by
    change Sum.inl (kmswLimitDartVertex (rL).code.1
      (B i, s ^^ lMinusCodePrimedSideFlip rL (B i))) = Sum.inl a
    exact congrArg Sum.inl hAvertex
  have hrawB : lMinusCodeRawEndpoint rL Q s C = Sum.inr b.val := by
    change Sum.inr (if s then (Q).east ((Q).boundary i).1
      else (Q).west ((Q).boundary i).1) = Sum.inr b.val
    exact congrArg Sum.inr hendpoint
  have hgen : lMinusCodeVertexGluing rL Q
      (lMinusCodeRawEndpoint rL Q s A) (lMinusCodeRawEndpoint rL Q s C) :=
    ⟨A, C, hglue, s, rfl, rfl⟩
  have hq : (⟦lMinusCodeRawEndpoint rL Q s A⟧ : LMinusCodeRawVertex rL Q) =
      ⟦lMinusCodeRawEndpoint rL Q s C⟧ :=
    Quotient.sound (Relation.EqvGen.rel _ _ hgen)
  rw [hrawA, hrawB] at hq
  exact hq

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: each inherited block vertex has its intrinsic
code class, with no geometric identification built into the code. -/
@[expose] noncomputable def lMinusBlockVertexCode : LMinusBlockVertex hqMode →
    LMinusCodeGluedVertex rL Q
  | .inl a => ⟨⟦Sum.inl a⟧, Or.inl ⟨a, rfl⟩⟩
  | .inr b => ⟨⟦Sum.inr b.val⟧, Or.inr ⟨b, rfl⟩⟩

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: inherited vertex equality is reflected by the
intrinsic code classes on all four block branches. -/
theorem lMinusBlockVertexCode_sound
    (a b : LMinusBlockVertex hqMode)
    (hab : lMinusBlockVertexImage hτ hqMode a = lMinusBlockVertexImage hτ hqMode b) :
    lMinusBlockVertexCode hqMode a = lMinusBlockVertexCode hqMode b := by
  apply Subtype.ext
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      exact congrArg (fun v => (⟦Sum.inl v⟧ : LMinusCodeRawVertex rL Q))
        (lMinusPrimedVertexMap_injective hτ hab)
    | inr b => exact lMinusCode_shared_vertex_eq hτ hp P hqMode Tpath hfin hleft hk a b hab
  | inr a =>
    cases b with
    | inl b =>
      exact (lMinusCode_shared_vertex_eq hτ hp P hqMode Tpath hfin hleft hk b a hab.symm).symm
    | inr b =>
      exact congrArg (fun v => (⟦Sum.inr v⟧ : LMinusCodeRawVertex rL Q))
        (boundaryGluingHatVertexMap_injective W h k hτ hab)

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: geometric vertex classes map to precisely the
allocated intrinsic code classes. -/
@[expose] noncomputable def lMinusGluedToCodeVertex :
    LMinusGluedVertex hτ hqMode → LMinusCodeGluedVertex rL Q :=
  Quotient.lift (lMinusBlockVertexCode hqMode)
    (lMinusBlockVertexCode_sound hτ hp P hqMode Tpath hfin hleft hk)

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: evaluating a transported vertex class gives its
original run-zero vertex identity. -/
theorem lMinusGluedToCodeVertex_image (v : LMinusGluedVertex hτ hqMode) :
    lMinusCodeVertexImage hτ hp P hqMode Tpath hfin hleft hk
        (lMinusGluedToCodeVertex hτ hp P hqMode Tpath hfin hleft hk v).val =
      Setoid.kerLift (lMinusBlockVertexImage hτ hqMode) v := by
  refine Quotient.inductionOn v ?_
  intro a
  cases a <;> rfl

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the intrinsic and inherited vertex quotients
are bijective, with every allocated code class represented by a block. -/
theorem lMinusGluedToCodeVertex_bijective :
    Function.Bijective (lMinusGluedToCodeVertex hτ hp P hqMode Tpath hfin hleft hk) := by
  constructor
  · intro a b hab
    apply (Setoid.kerLift_injective (lMinusBlockVertexImage hτ hqMode))
    rw [← lMinusGluedToCodeVertex_image hτ hp P hqMode Tpath hfin hleft hk a,
      ← lMinusGluedToCodeVertex_image hτ hp P hqMode Tpath hfin hleft hk b, hab]
  · intro v
    rcases v.property with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact ⟨⟦Sum.inl a⟧, Subtype.ext ha⟩
    · exact ⟨⟦Sum.inr b⟧, Subtype.ext hb⟩

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the code-only and inherited vertex quotients
are equivalent. -/
@[expose] noncomputable def lMinusCodeToGluedVertexEquiv :
    LMinusCodeGluedVertex rL Q ≃ LMinusGluedVertex hτ hqMode :=
  (Equiv.ofBijective (lMinusGluedToCodeVertex hτ hp P hqMode Tpath hfin hleft hk)
    (lMinusGluedToCodeVertex_bijective hτ hp P hqMode Tpath hfin hleft hk)).symm

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the decoded cell carrier is equivalent to the
inherited glued carrier, using the proved vertex and dart identifications. -/
@[expose] noncomputable def lMinusDecodedToGluedCellEquiv :
    GeometricSideCell (lMinusDecodedSide hτ hqMode hfin) ≃
      Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode) :=
  (lMinusDecodedCellEquiv hτ hqMode hfin).symm.trans
    (Equiv.sumCongr
      (lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk)
      (lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk))

end DecodedVertexIdentification

end DirectedDistances.PaperProofs.Section5
