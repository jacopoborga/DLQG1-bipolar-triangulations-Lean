/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole11
public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusSideMeasurable5
public import DirectedDistances.RandomWalk.ConstructedLawInstances







public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

section DecodedSide

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {longest : Bool}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hqMode : boundaryFutureHattedPath k W ∈ Coherent (if longest then XDP.ldp else XDP.sdp))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))

local notation "X" => (ite (longest = true) XDP.ldp XDP.sdp)
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode : Coherent X)
local notation "Q" => geometricSideSubmap X renewalTime renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "hf" => lMinus_primed_observation_finiteIncidence hτ hfin

/-- Helper toward Lemma 5.5: the complete decoded side with the reconnected
initial rotation. All nine other fields are inherited literally. -/
@[expose] noncomputable def lMinusDecodedSide2 : GeometricSideSubmap :=
  { lMinusDecodedSide hτ hqMode hfin with
    rotation := fun d e => ∃ a b : LMinusCodeGluedDart rL Q,
      lMinusCodeDartId rL Q a = d ∧ lMinusCodeDartId rL Q b = e ∧
        lMinusCodeInitialSplicedRotation rL qL hf a = b }

/-- Helper toward Lemma 5.5: exact agreement of every non-rotation field,
including missing-edge presence, both endpoints, face succession and markings. -/
theorem lMinusDecodedSide2_nonrotation_fields :
    let A := lMinusDecodedSide2 hτ hqMode hfin
    let B := lMinusDecodedSide hτ hqMode hfin
    A.vertices = B.vertices ∧ A.edges = B.edges ∧ A.west = B.west ∧
      A.east = B.east ∧ A.present = B.present ∧ A.faceNext = B.faceNext ∧
      A.root = B.root ∧ A.boundary = B.boundary ∧ A.seam = B.seam :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Helper toward Lemma 5.5: the corrected decoded cells have precisely the
same intrinsic vertex and dart representatives as the original decoder. -/
@[expose] noncomputable def lMinusDecodedSide2CellEquiv :
    Sum (LMinusCodeGluedVertex rL Q) (LMinusCodeGluedDart rL Q) ≃
      GeometricSideCell (lMinusDecodedSide2 hτ hqMode hfin) :=
  lMinusDecodedCellEquiv hτ hqMode hfin

/-- Helper toward Lemma 5.5: every non-rotation relation can reuse its
original decoded-side proof on the identical cell carrier. -/
theorem lMinusDecodedSide2_relation_iff_of_ne_rotation
    (t : TruncationRelation) (ht : t ≠ .rotation)
    (u v : GeometricSideCell (lMinusDecodedSide2 hτ hqMode hfin)) :
    geometricSideRelation (lMinusDecodedSide2 hτ hqMode hfin) t u v ↔
      geometricSideRelation (lMinusDecodedSide hτ hqMode hfin) t u v := by
  cases t <;> cases u <;> cases v <;> first | exact (ht rfl).elim | rfl

/-- Helper toward Lemma 5.5: on intrinsic darts the corrected decoded
rotation is exactly the spliced permutation, with no extra geometric premise. -/
theorem lMinusDecodedSide2_rotation_code_iff (a b : LMinusCodeGluedDart rL Q) :
    (lMinusDecodedSide2 hτ hqMode hfin).rotation
        (lMinusCodeDartId rL Q a) (lMinusCodeDartId rL Q b) ↔
      lMinusCodeInitialSplicedRotation rL qL hf a = b := by
  constructor
  · rintro ⟨a', b', ha, hb, hr⟩
    have ha' := lMinusCodeDartId_injective rL Q ha
    have hb' := lMinusCodeDartId_injective rL Q hb
    subst a'
    subst b'
    exact hr
  · intro hr
    exact ⟨a, b, rfl, rfl, hr⟩

end DecodedSide

section GeometricGluing

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ Coherent (if longest then XDP.ldp else XDP.sdp))
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "X" => (ite (longest = true) XDP.ldp XDP.sdp)
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode : Coherent X)
local notation "Q" => geometricSideSubmap X renewalTime renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "E" => lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "Φ" => lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the corrected decoded carrier uses the existing
intrinsic-to-glued and glued-to-geometric cell equivalences. -/
@[expose] noncomputable def lMinusDecodedSide2ToGeometricCellEquiv :
    GeometricSideCell (lMinusDecodedSide2 hτ hqMode hfin) ≃ GeometricSideCell S :=
  (lMinusDecodedToGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk).trans Φ

/-- Helper toward Lemma 5.5: the corrected decoder's rotation iff on its
entire cell carrier, obtained from Whole11's reconnected rotation transport. -/
theorem lMinusDecodedSide2_rotation_iff
    (u v : GeometricSideCell (lMinusDecodedSide2 hτ hqMode hfin)) :
    geometricSideRelation (lMinusDecodedSide2 hτ hqMode hfin) .rotation u v ↔
      geometricSideRelation S .rotation
        (lMinusDecodedSide2ToGeometricCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (lMinusDecodedSide2ToGeometricCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  obtain ⟨a, rfl⟩ := (lMinusDecodedSide2CellEquiv hτ hqMode hfin).surjective u
  obtain ⟨b, rfl⟩ := (lMinusDecodedSide2CellEquiv hτ hqMode hfin).surjective v
  change geometricSideRelation (lMinusDecodedSide2 hτ hqMode hfin) .rotation
      ((lMinusDecodedCellEquiv hτ hqMode hfin) a)
      ((lMinusDecodedCellEquiv hτ hqMode hfin) b) ↔
    geometricSideRelation S .rotation
      (Φ ((Equiv.sumCongr
        (lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk) E)
        ((lMinusDecodedCellEquiv hτ hqMode hfin).symm
          ((lMinusDecodedCellEquiv hτ hqMode hfin) a))))
      (Φ ((Equiv.sumCongr
        (lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk) E)
        ((lMinusDecodedCellEquiv hτ hqMode hfin).symm
          ((lMinusDecodedCellEquiv hτ hqMode hfin) b))))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have ht := lMinusInitialSplicedRotationRelation_rotation_iff
    hτ hp P hqMode Tpath hfin hleft hk
  cases a with
  | inl a =>
    cases b with
    | inl b => exact ht (.inl (lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk a)) (.inl (lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk b))
    | inr b => exact ht (.inl (lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk a)) (.inr (E b))
  | inr a =>
    cases b with
    | inl b => exact (ht (.inr (E a)) (.inl (lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk b)))
    | inr b =>
      change (lMinusDecodedSide2 hτ hqMode hfin).rotation
        (lMinusCodeDartId rL Q a) (lMinusCodeDartId rL Q b) ↔ _
      rw [lMinusDecodedSide2_rotation_code_iff]
      have hE : E (lMinusCodeInitialSplicedRotation rL qL
          (lMinus_primed_observation_finiteIncidence hτ hfin) a) = E b ↔
          lMinusCodeInitialSplicedRotation rL qL
            (lMinus_primed_observation_finiteIncidence hτ hfin) a = b :=
        ⟨fun he => (E).injective he, congrArg E⟩
      have ht' := ht (.inr (E a)) (.inr (E b))
      change E (lMinusCodeInitialSplicedRotation rL qL
          (lMinus_primed_observation_finiteIncidence hτ hfin) ((E).symm (E a))) = E b ↔ _ at ht'
      rw [Equiv.symm_apply_apply] at ht'
      exact hE.symm.trans ht'

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the adjusted decoder has the reconnected
permutation exactly when the initial retained hatted source star is a
singleton. No fixed-point assertion is introduced as a premise. -/
theorem lMinusCodeInitialSplicedRotation_eq_adjusted_iff_singleton :
    lMinusCodeInitialSplicedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin) =
      lMinusCodeInitialAdjustedRotation rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin) ↔
      {e : ℕ × Bool | e.1 ∈ (Q).edges ∧
        kmswLimitDartVertex
          (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) e = 0} =
        {(((Q).boundary 0).1, false)} := by
  let c : {d : ℕ × Bool // d.1 ∈ (Q).edges} :=
    ⟨(((Q).boundary 0).1, false), lMinus_hatted_boundary_mem _ qL 0⟩
  let Hrot := lMinusHattedRotation (if longest then XDP.ldp else XDP.sdp) qL
  refine (show _ ↔ Hrot c = c from ?_).trans
    (lMinusHattedRotation_initial_eq_self_iff_singleton hqMode)
  constructor
  · intro he
    have hr := lMinusCodeInitialSplicedRotation_predecessor_side_rotation
      hτ hp P hqMode Tpath hfin hleft hk
    dsimp only at hr
    rw [he] at hr
    exact (lMinusCodeInitialAdjustedRotation_predecessor_side_rotation_iff
      hτ hp P hqMode Tpath hfin hleft hk).mp hr
  · intro hfix
    exact lMinusCodeInitialSplicedRotation_eq_adjusted_of_fixed
      hτ hqMode hfin hfix

end GeometricGluing

/-- Helper toward Lemma 5.5: the reconnection is natural under exactly the
same intrinsic dart transport used in `GeoInftyLMinusSideMeasurable5`.
The hatted isomorphism is a map being transported, not an assumption about
the actual glued side or its rotation. -/
theorem lMinusCodeGluedDartTransportEquiv_splicedRotation (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (d : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeGluedDartTransportEquiv x r q q' phi
      (lMinusCodeInitialSplicedRotation r q hf d) =
    lMinusCodeInitialSplicedRotation r q' hf
      (lMinusCodeGluedDartTransportEquiv x r q q' phi d) := by
  let T := lMinusCodeGluedDartTransportEquiv x r q q' phi
  let H := (lMinusHattedRotation x q).extendDomain
    (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q))
  let H' := (lMinusHattedRotation x q').extendDomain
    (Equiv.ofInjective _ (lMinusCodeHattedDart_injective r q'))
  let c := lMinusCodeBoundaryDart r q (0, false)
  let c' := lMinusCodeBoundaryDart r q' (0, false)
  let a := H.symm c
  let a' := H'.symm c'
  let A := lMinusCodeInitialAdjustedRotation r q hf
  let A' := lMinusCodeInitialAdjustedRotation r q' hf
  have hc : T c = c' := lMinusCodeGluedDartTransportEquiv_boundary x r q q' phi _
  have ha : T a = a' := by
    apply H'.injective
    change H' (T (H.symm c)) = H' (H'.symm c')
    rw [Equiv.apply_symm_apply]
    have ht := lMinusCodeGluedDartTransportEquiv_hatted_extend x r q q' phi (H.symm c)
    change T (H (H.symm c)) = H' (T (H.symm c)) at ht
    rw [Equiv.apply_symm_apply, hc] at ht
    exact ht.symm
  have hfix : a = c ↔ a' = c' := by
    constructor
    · intro h
      exact ha.symm.trans ((congrArg T h).trans hc)
    · intro h
      apply T.injective
      exact ha.trans (h.trans hc.symm)
  have hA (e) : T (A e) = A' (T e) :=
    lMinusCodeGluedDartTransportEquiv_adjustedRotation x r q q' phi hf e
  change T ((if a = c then A else Equiv.swap (A a) c * A) d) =
    (if a' = c' then A' else Equiv.swap (A' a') c' * A') (T d)
  by_cases h : a = c
  · rw [ite_eq_left h, ite_eq_left (hfix.mp h)]
    exact hA d
  · rw [ite_eq_right h, ite_eq_right (fun he => h (hfix.mpr he)), Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, T.injective.map_swap, hc, hA a, hA d, ha]

/-- Helper toward Lemma 5.5: exact rotation-iff replacement for the
adjusted-rotation transport lemma in the presentation measurability chain.
The same quotient carriers and hatted marked action are reused. -/
theorem lMinusCodeInitialSplicedRotation_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (a b : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeInitialSplicedRotation r q hf a = b ↔
      lMinusCodeInitialSplicedRotation r q' hf
        (lMinusCodeGluedDartTransportEquiv x r q q' phi a) =
        lMinusCodeGluedDartTransportEquiv x r q q' phi b := by
  rw [← lMinusCodeGluedDartTransportEquiv_splicedRotation]
  exact ⟨congrArg _, fun h => (lMinusCodeGluedDartTransportEquiv x r q q' phi).injective h⟩

/-- Helper toward Lemma 5.5: a formula for the corrected decoder using only
the presentation, its coherent hatted block and primed finite incidence.
Primed directed presence is read from missing-root stages of the first code. -/
@[expose] noncomputable def lMinusCodeSide2 (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) : GeometricSideSubmap where
  vertices := Set.range (lMinusCodeVertexId r (lMinusCoherentLeftSide x q))
  edges := Set.range (lMinusCodeEdgeId r (lMinusCoherentLeftSide x q))
  west := lMinusCodeEndpointId x r q false
  east := lMinusCodeEndpointId x r q true
  present := {i | ∃ e, lMinusCodeEdgeId r (lMinusCoherentLeftSide x q) e = i ∧
    lMinusCodeEdgePresent r (lMinusCoherentLeftSide x q)
      (fun a => ∃ m, a < (kmswMissingRootStage r.code.1 m).nextEdge ∧
        (kmswMissingRootStage r.code.1 m).present a = true) e}
  rotation := fun d e => ∃ a b : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q),
    lMinusCodeDartId r _ a = d ∧ lMinusCodeDartId r _ b = e ∧
      lMinusCodeInitialSplicedRotation r q hf a = b
  faceNext := fun d e => ∃ a b : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q),
    lMinusCodeDartId r _ a = d ∧ lMinusCodeDartId r _ b = e ∧
      lMinusCodeWholeFaceNext r q hf a b
  root := lMinusCodeVertexId r (lMinusCoherentLeftSide x q)
    ⟨⟦Sum.inr (lMinusCoherentLeftSide x q).root⟧,
      Or.inr ⟨⟨_, lMinus_hatted_root_mem x q⟩, rfl⟩⟩
  boundary := fun i => lMinusCodeDartId r _ (lMinusCodeBoundaryDart r q (i, false))
  seam := fun i => lMinusCodeDartId r _
    (lMinusCodeHattedDart r _ ⟨(lMinusCoherentLeftSide x q).seam i,
      lMinus_hatted_seam_mem x q i⟩)

/-- Helper toward Lemma 5.5: the contextual corrected decoder is the
code-only formula. No additional whole-plane data enter its rotation. -/
theorem lMinusDecodedSide2_eq_codeSide2
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈ Coherent (if longest then XDP.ldp else XDP.sdp))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    lMinusDecodedSide2 hτ hqMode hfin =
      lMinusCodeSide2 (if longest then XDP.ldp else XDP.sdp)
        (decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
          (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W))
        ⟨boundaryFutureHattedPath k W, hqMode⟩
        (lMinus_primed_observation_finiteIncidence hτ hfin) := by
  have hp := lMinusDecodedSide_present_eq_code hτ hqMode hfin
  unfold lMinusDecodedSide2 lMinusCodeSide2 lMinusDecodedSide
  dsimp only
  congr 1

/-- Helper toward Lemma 5.5: the code-only corrected vertex and dart
encodings give the same intrinsic carriers used by the old decoder. -/
@[expose] noncomputable def lMinusCodeSide2CellEquiv (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) :
    Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) ≃
    GeometricSideCell (lMinusCodeSide2 x r q hf) :=
  Equiv.sumCongr
    (Equiv.ofInjective _ (lMinusCodeVertexId_injective r _))
    (Equiv.ofBijective
      (fun d => ⟨lMinusCodeDartId r _ d, ⟨d.1, rfl⟩⟩)
      ⟨fun _ _ hab => lMinusCodeDartId_injective r _ (congrArg Subtype.val hab), by
        intro d
        obtain ⟨e, he⟩ := d.property
        exact ⟨(e, d.val.2), Subtype.ext (Prod.ext he rfl)⟩⟩)

/-- Helper toward Lemma 5.5: the code-only rotation relation reduces to its
intrinsic permutation without losing the dart identifiers. -/
theorem lMinusCodeSide2_rotation_iff (x : XDP) (r : LMinusSidePresentation x)
    (q : Coherent x) (hf : KMSWFiniteIncidence r.code.1)
    (a b : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    (lMinusCodeSide2 x r q hf).rotation
        (lMinusCodeDartId r _ a) (lMinusCodeDartId r _ b) ↔
      lMinusCodeInitialSplicedRotation r q hf a = b := by
  constructor
  · rintro ⟨a', b', ha, hb, hr⟩
    have ha' := lMinusCodeDartId_injective r _ ha
    have hb' := lMinusCodeDartId_injective r _ hb
    subst a'
    subst b'
    exact hr
  · intro hr
    exact ⟨a, b, rfl, rfl, hr⟩

/-- Helper toward Lemma 5.5: the retained face relation of the code-only
side reduces to the unchanged intrinsic retained-face relation. -/
theorem lMinusCodeSide2_faceNext_iff (x : XDP) (r : LMinusSidePresentation x)
    (q : Coherent x) (hf : KMSWFiniteIncidence r.code.1)
    (a b : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    (lMinusCodeSide2 x r q hf).faceNext
        (lMinusCodeDartId r _ a) (lMinusCodeDartId r _ b) ↔
      lMinusCodeWholeFaceNext r q hf a b := by
  constructor
  · rintro ⟨a', b', ha, hb, hr⟩
    have ha' := lMinusCodeDartId_injective r _ ha
    have hb' := lMinusCodeDartId_injective r _ hb
    subst a'
    subst b'
    exact hr
  · intro hr
    exact ⟨a, b, rfl, rfl, hr⟩

/-- Helper toward Lemma 5.5: the code-only directed-presence test is exactly
the unchanged intrinsic geometric-edge presence test. -/
theorem lMinusCodeSide2_present_iff (x : XDP) (r : LMinusSidePresentation x)
    (q : Coherent x) (hf : KMSWFiniteIncidence r.code.1)
    (a : LMinusCodeGluedEdge r (lMinusCoherentLeftSide x q)) :
    lMinusCodeEdgeId r _ a ∈ (lMinusCodeSide2 x r q hf).present ↔
      lMinusCodeEdgePresent r (lMinusCoherentLeftSide x q)
        (fun e => ∃ m, e < (kmswMissingRootStage r.code.1 m).nextEdge ∧
          (kmswMissingRootStage r.code.1 m).present e = true) a := by
  constructor
  · rintro ⟨b, hb, hp⟩
    have hab := lMinusCodeEdgeId_injective r _ hb
    subst b
    exact hp
  · intro hp
    exact ⟨a, rfl, hp⟩

/-- Helper toward Lemma 5.5: the code-side intrinsic cell equivalence
reuses the existing vertex and dart transport maps unchanged. -/
@[expose] noncomputable def lMinusCodeSide2TransportEquiv (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) :
    Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) ≃
    Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q'))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q')) :=
  Equiv.sumCongr (lMinusCodeGluedVertexEquiv x r q q' phi)
    (lMinusCodeGluedDartTransportEquiv x r q q' phi)

/-- Helper toward Lemma 5.5: the marked relations on intrinsic code cells,
prior to their natural-number encoding. This is the literal decoded-side
relation, with the reconnected rotation in place of the adjusted one. -/
@[expose] noncomputable def lMinusCodeRelation2 (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) :
    TruncationRelation →
      Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
        (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) →
      Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
        (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) → Prop
  | .vertex => fun u _ => match u with
      | .inl _ => True
      | .inr _ => False
  | .root => fun u _ => match u with
      | .inl v => v = ⟨⟦Sum.inr (lMinusCoherentLeftSide x q).root⟧,
          Or.inr ⟨⟨_, lMinus_hatted_root_mem x q⟩, rfl⟩⟩
      | .inr _ => False
  | .target => fun _ _ => False
  | .incident => fun u v => match u, v with
      | .inr d, .inl a => lMinusCodeEndpointVertex x r q d.2 d.1 = a
      | _, _ => False
  | .opposite => fun u v => match u, v with
      | .inr d, .inr e => (d.1, !d.2) = e
      | _, _ => False
  | .oriented => fun u _ => match u with
      | .inr d => lMinusCodeEdgePresent r (lMinusCoherentLeftSide x q)
          (fun a => ∃ m, a < (kmswMissingRootStage r.code.1 m).nextEdge ∧
            (kmswMissingRootStage r.code.1 m).present a = true) d.1 ∧ d.2 = false
      | .inl _ => False
  | .rotation => fun u v => match u, v with
      | .inr d, .inr e => lMinusCodeInitialSplicedRotation r q hf d = e
      | _, _ => False
  | .faceNext => fun u v => match u, v with
      | .inr d, .inr e => lMinusCodeWholeFaceNext r q hf d e
      | _, _ => False
  | .boundary i => fun u _ => match u with
      | .inr d => lMinusCodeBoundaryDart r q (i, false) = d
      | .inl _ => False
  | .seam i => fun u _ => match u with
      | .inr d => lMinusCodeHattedDart r _
          ⟨(lMinusCoherentLeftSide x q).seam i, lMinus_hatted_seam_mem x q i⟩ = d
      | .inl _ => False

/-- Helper toward Lemma 5.5: natural-number encoding preserves and reflects
every intrinsic marked relation, including the corrected rotation. -/
theorem lMinusCodeSide2CellEquiv_relation_iff (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (t : TruncationRelation)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    geometricSideRelation (lMinusCodeSide2 x r q hf) t
        (lMinusCodeSide2CellEquiv x r q hf u) (lMinusCodeSide2CellEquiv x r q hf v) ↔
      lMinusCodeRelation2 x r q hf t u v := by
  cases t with
  | vertex => cases u <;> cases v <;> rfl
  | root =>
    cases u with
    | inl a =>
      cases v <;>
        exact (lMinusCodeVertexId_injective r (lMinusCoherentLeftSide x q)).eq_iff
    | inr a => cases v <;> rfl
  | target => cases u <;> cases v <;> rfl
  | incident =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d =>
      cases v with
      | inr e => rfl
      | inl a =>
        change (if (lMinusCodeDartId r _ d).2 then
            lMinusCodeEndpointId x r q true (lMinusCodeDartId r _ d).1
          else lMinusCodeEndpointId x r q false (lMinusCodeDartId r _ d).1) =
          lMinusCodeVertexId r _ a ↔ lMinusCodeEndpointVertex x r q d.2 d.1 = a
        rcases d with ⟨e, s⟩
        cases s <;> simp only [lMinusCodeDartId, Bool.false_eq_true,
          ite_eq_left, lMinusCodeEndpointId_id]
        all_goals exact (lMinusCodeVertexId_injective r _).eq_iff
  | opposite =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d =>
      cases v with
      | inl a => rfl
      | inr e =>
        change lMinusCodeDartId r _ (d.1, !d.2) = lMinusCodeDartId r _ e ↔ _
        exact (lMinusCodeDartId_injective r _).eq_iff
  | oriented =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d =>
      cases v <;> exact and_congr_left (fun _ => lMinusCodeSide2_present_iff x r q hf d.1)
  | rotation =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d =>
      cases v with
      | inl a => rfl
      | inr e => exact lMinusCodeSide2_rotation_iff x r q hf d e
  | faceNext =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d =>
      cases v with
      | inl a => rfl
      | inr e => exact lMinusCodeSide2_faceNext_iff x r q hf d e
  | boundary i =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d => cases v <;> exact (lMinusCodeDartId_injective r _).eq_iff
  | seam i =>
    cases u with
    | inl a => cases v <;> rfl
    | inr d => cases v <;> exact (lMinusCodeDartId_injective r _).eq_iff

/-- Helper toward Lemma 5.5: expose the sum action once, so relation
transport reuses the named vertex and dart maps without unfolding them. -/
theorem lMinusCodeSide2TransportEquiv_apply (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (u : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    lMinusCodeSide2TransportEquiv x r q q' phi u =
      Sum.map (lMinusCodeGluedVertexEquiv x r q q' phi)
        (lMinusCodeGluedDartTransportEquiv x r q q' phi) u := by
  cases u <;> rfl

/-- Helper toward Lemma 5.5: all intrinsic marked relations transport under
the same code and hatted marked action. Rotation uses the new splice lemma;
the other fields use the unchanged transport lemmas from Measurable5. -/
theorem lMinusCodeRelation2_vertex_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    lMinusCodeRelation2 x r q hf .vertex u v ↔
      lMinusCodeRelation2 x r q' hf .vertex
        (lMinusCodeSide2TransportEquiv x r q q' phi u)
        (lMinusCodeSide2TransportEquiv x r q q' phi v) := by
  cases u <;> rfl

/-- Helper toward Lemma 5.5: all intrinsic marked relations transport under
the same code and hatted marked action. Rotation uses the new splice lemma;
the other fields use the unchanged transport lemmas from Measurable5. -/
theorem lMinusCodeRelation2_root_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    lMinusCodeRelation2 x r q hf .root u v ↔
      lMinusCodeRelation2 x r q' hf .root
        (lMinusCodeSide2TransportEquiv x r q q' phi u)
        (lMinusCodeSide2TransportEquiv x r q q' phi v) := by
  let V := lMinusCodeGluedVertexEquiv x r q q' phi
  cases u with
  | inr d => rfl
  | inl a =>
    have hr := lMinusCodeGluedVertexMap_root x r q q' phi
    change a = _ ↔ V a = _
    exact ⟨fun he => (congrArg V he).trans hr,
        fun he => V.injective (he.trans hr.symm)⟩

/-- Helper toward Lemma 5.5: all intrinsic marked relations transport under
the same code and hatted marked action. Rotation uses the new splice lemma;
the other fields use the unchanged transport lemmas from Measurable5. -/
theorem lMinusCodeRelation2_target_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (hf : KMSWFiniteIncidence r.code.1)
    (u v : Sum (LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q))
      (LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))) :
    lMinusCodeRelation2 x r q hf .target u v ↔
      lMinusCodeRelation2 x r q' hf .target
        (lMinusCodeSide2TransportEquiv x r q q' phi u)
        (lMinusCodeSide2TransportEquiv x r q q' phi v) := by
  rfl

/-- Helper toward Lemma 5.5: expose the vertex action without unfolding
the allocated quotient equivalence during relation transport. -/
theorem lMinusCodeSide2TransportEquiv_inl (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (a : LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q)) :
    lMinusCodeSide2TransportEquiv x r q q' phi (.inl a) =
      .inl (lMinusCodeGluedVertexMap x r q q' phi a) := rfl

/-- Helper toward Lemma 5.5: expose the dart action without unfolding the
quotient edge equivalence during relation transport. -/
theorem lMinusCodeSide2TransportEquiv_inr (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (d : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q)) :
    lMinusCodeSide2TransportEquiv x r q q' phi (.inr d) =
      .inr (lMinusCodeGluedEdgeMap x r q q' phi d.1, d.2) := rfl

/-- Helper toward Lemma 5.5: endpoint equality is preserved and reflected
by the allocated vertex and geometric edge actions. -/
theorem lMinusCodeEndpointVertex_transport_iff (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q'))
    (d : LMinusCodeGluedDart r (lMinusCoherentLeftSide x q))
    (a : LMinusCodeGluedVertex r (lMinusCoherentLeftSide x q)) :
    lMinusCodeEndpointVertex x r q d.2 d.1 = a ↔
      lMinusCodeEndpointVertex x r q' d.2
        (lMinusCodeGluedEdgeMap x r q q' phi d.1) =
      lMinusCodeGluedVertexMap x r q q' phi a := by
  have hend := lMinusCodeGluedVertexMap_endpoint x r q q' phi d.2 d.1
  constructor
  · intro he
    exact hend.symm.trans (congrArg (lMinusCodeGluedVertexMap x r q q' phi) he)
  · intro he
    exact (lMinusCodeGluedVertexEquiv x r q q' phi).injective (hend.trans he)





















































































































/-- Helper toward Lemma 5.5: the three-step up/down/down word for a local
shortest-geodesic test at the initial hatted source. -/
@[expose] def lMinusSdpInitialWord (i : Fin 3) : Fin 3 :=
  if i = 0 then 1 else 2

/-- Helper toward Lemma 5.5: a concrete finite-prefix and future-barrier
event, without any rotation or fixed-point requirement in its definition. -/
@[expose] def lMinusSdpInitialSeed : Set (ℕ → ℤ × ℤ) :=
  {p | (fun j : Fin 4 => p j.val) = lazyTwoDimensionalPrefix 0 0 lMinusSdpInitialWord ∧
    ∀ j, (2 : ℤ) ≤ (p (3 + j)).1}

/-- Helper toward Lemma 5.5: the concrete initial seed has positive
conditioned-walk probability, using the proved joint prefix/barrier law. -/
theorem lMinusSdpInitialSeed_measure_pos :
    0 < conditionedVectorPathLaw 0 0 lMinusSdpInitialSeed := by
  have hw : ∀ j, 0 ≤ (lazyTwoDimensionalPrefix 0 0 lMinusSdpInitialWord j).1 := by
    decide
  have hX : (lazyTwoDimensionalPrefix 0 0 lMinusSdpInitialWord (Fin.last 3)).1 =
      ((2 : ℕ) : ℤ) := by decide
  have hCpos := (conditionedSource_prefix_atom_pos_iff 0 0
    (conditionedVectorPathLaw 0 0) (conditionedVectorPathLaw_map_prefix 0 0)
    3 lMinusSdpInitialWord).mpr hw
  have hp := conditionedVectorPathLaw_prefix_inter_future_barrier 0 0
    3 2 2 lMinusSdpInitialWord hw le_rfl hX
  change (conditionedVectorPathLaw 0 0).real lMinusSdpInitialSeed = _ at hp
  simp only [Nat.sub_self, Nat.cast_zero, zero_add, mul_one] at hp
  have hpos : 0 < (conditionedVectorPathLaw 0 0).real lMinusSdpInitialSeed := by
    rw [hp]
    exact div_pos (ENNReal.toReal_pos hCpos.ne' (MeasureTheory.measure_ne_top _ _))
      (by norm_num)
  apply bot_lt_iff_ne_bot.mpr
  intro hz
  rw [MeasureTheory.Measure.real, hz] at hpos
  change 0 < (0 : ℝ) at hpos
  exact (lt_irrefl 0) hpos


























































end DirectedDistances.PaperProofs.Section5

