/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusActualSideIso6




public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
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
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain X renewalTime renewalTime_positiveSuccessTime)
local notation "Q" => geometricSideSubmap X renewalTime
  renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "z" => hatCodes (boundaryGluingFutureStream W h k) hτ
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "D" => lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

include Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: for nonpositive k, an embedded hatted edge
is in the actual left side exactly when it is in the hatted left side.
The primed overlap adds only beta edges, all already in the hatted left side. -/
theorem lMinusHattedEdge_mem_actual_iff (e : ℕ) :
    EH e ∈ (S).edges ↔ e ∈ (Q).edges := by
  rw [(boundaryGluing_nonpos_side_identities W h k hτ longest hp P
    hqMode Tpath hfin hleft hk).1]
  have reflect (he : EH e ∈ boundaryGluingLeftHatEdges W h k hτ X hqMode) :
      e ∈ (Q).edges := by
    obtain ⟨a, ha, hae⟩ := he
    exact boundaryGluingHatEdgeMap_injective W h k hτ hae ▸ ha
  constructor
  · rintro (hp' | hh)
    · have hb : EH e ∈ boundaryGluingBetaEdges W h k hτ := by
        rw [← boundaryGluingPrimedEdges_inter_hatRange W h k hτ hfin]
        exact ⟨hp', e, rfl⟩
      exact reflect (boundaryGluingBetaEdges_subset_leftHatEdges
        W h k hτ X hqMode hb)
    · exact reflect hh
  · intro he
    exact Or.inr ⟨e, he, rfl⟩

/-- Helper toward Lemma 5.5: if a dart of any hatted creation triangle
borders a retained actual face, every edge of that hatted triangle is retained.
No retention or face correspondence for the other two darts is assumed. -/
theorem lMinusHattedTriangle_retained_of_actual_faceNext
    (j : TriangleCreationTime z) (a e : ℕ × Bool)
    (ha : a ∈ stageTriangleDartList z j)
    (hde : (S).faceNext (EH a.1, a.2) e) :
    ∀ c ∈ stageTriangleDartList z j, c.1 ∈ (Q).edges := by
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index z j
  let T : HatLocalTri (boundaryGluingFutureStream W h k) hτ :=
    ⟨stageTriangleRecord z j, j.val + 1, hi ▸ List.get_mem _ i⟩
  obtain ⟨F, hFR, hb⟩ :=
    boundaryGluing_hatTriangle_gluedFace W h k hτ H hp hfin T
  have border (c : ℕ × Bool) (hc : c ∈ stageTriangleDartList z j) :
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (EH c.1, c.2)) F :=
    hb c ((rMinusWhole_creation_oriented_mem z j c).mpr hc)
  obtain ⟨⟨G, haG, hG⟩, _⟩ := hde
  have hFG : F = G := by
    obtain ⟨δ₁, hδ₁, hw₁⟩ := border a ha
    obtain ⟨δ₂, hδ₂, hw₂⟩ := haG
    let t := min δ₁ δ₂ / 2
    have ht : 0 < t := half_pos (lt_min hδ₁ hδ₂)
    have ht₁ : t < δ₁ :=
      (half_lt_self (lt_min hδ₁ hδ₂)).trans_le (min_le_left _ _)
    have ht₂ : t < δ₂ :=
      (half_lt_self (lt_min hδ₁ hδ₂)).trans_le (min_le_right _ _)
    exact (WholePlanePastGlueDrawing.glueDrawing W h hp H).faces_eq_of_mem
      (hw₁ t t ht ht₁ ht ht₁) (hw₂ t t ht ht₂ ht ht₂)
  have hF : F.val ⊆ m0GeodesicSideOpenRegion hp P .left := by
    rw [hFG]
    exact hG
  intro c hc
  apply (lMinusHattedEdge_mem_actual_iff hτ hp P hqMode Tpath hfin hleft hk c.1).mp
  by_cases hs : EH c.1 ∈ m0GeodesicEdges P
  · exact (m0GeodesicEdges_subset_both hp P hs).1
  · exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P hs
      c.2 F hFR (border c hc) .left).mpr hF

/-- Helper toward Lemma 5.5: reverse transport needs only a hatted
creation-triangle representative of the first dart; retention of that triangle
is a consequence, including when the dart is on beta. -/
theorem lMinusCodeWholeFaceNext_actual_reverse_of_hatted_creation
    (d e : LMinusCodeGluedDart rL Q)
    (hde : (S).faceNext (D d).val (D e).val)
    (a : {a : ℕ × Bool // a.1 ∈ (Q).edges})
    (j : TriangleCreationTime z)
    (hd : d = lMinusCodeHattedDart rL Q a)
    (ha : a.val ∈ stageTriangleDartList z j) :
    lMinusCodeWholeFaceNext rL qL
      (lMinus_primed_observation_finiteIncidence hτ hfin) d e := by
  have hactual : (S).faceNext (EH a.val.1, a.val.2) (D e).val := by
    rw [hd, lMinusCodeGluedDartEquiv_hatted
      hτ hp P hqMode Tpath hfin hleft hk a] at hde
    exact hde
  have hall := lMinusHattedTriangle_retained_of_actual_faceNext
    hτ hp P hqMode Tpath hfin hleft hk j a.val (D e).val ha hactual
  exact lMinusCodeWholeFaceNext_actual_reverse_of_hatted_triangle
    hτ hp P hqMode Tpath hfin hleft hk d e hde a j hd ha hall

/-- Helper toward Lemma 5.5: an arbitrary actual retained face step lifts
to the code relation if its first raw dart is the image of a hatted creation
dart. Both concrete dart correspondences and triangle retention are proved. -/
theorem lMinusActualFaceNext_hatted_creation_lift
    (j : TriangleCreationTime z) (a e : ℕ × Bool)
    (ha : a ∈ stageTriangleDartList z j)
    (hde : (S).faceNext (EH a.1, a.2) e) :
    ∃ d' e' : LMinusCodeGluedDart rL Q,
      (D d').val = (EH a.1, a.2) ∧ (D e').val = e ∧
      lMinusCodeWholeFaceNext rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin) d' e' := by
  have hall := lMinusHattedTriangle_retained_of_actual_faceNext
    hτ hp P hqMode Tpath hfin hleft hk j a e ha hde
  let aQ : {a : ℕ × Bool // a.1 ∈ (Q).edges} := ⟨a, hall a ha⟩
  let d' := lMinusCodeHattedDart rL Q aQ
  have hd' : (D d').val = (EH a.1, a.2) :=
    lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk aQ
  obtain ⟨J, hdJ, hJ⟩ := lMinusActualFaceNext_triangle hp P _ e hde
  have heJ := rMinusWhole_triangle_succ_mem (shiftedStream W 0) (H.1 0) J _ hdJ
  rw [hde.2] at heJ
  let eS : {a : ℕ × Bool // a.1 ∈ (S).edges} := ⟨e, hJ e heJ⟩
  let e' := (D).symm eS
  have he' : (D e').val = e := congrArg Subtype.val ((D).apply_symm_apply eS)
  refine ⟨d', e', hd', he', ?_⟩
  apply lMinusCodeWholeFaceNext_actual_reverse_of_hatted_creation
    hτ hp P hqMode Tpath hfin hleft hk d' e' _ aQ j rfl ha
  rw [hd', he']
  exact hde

/- Remaining geometric obligation, under the standing binders above:
for every raw actual retained face step `S.faceNext d e`, prove

  (∃ a : ℕ × Bool, ∃ j : TriangleCreationTime
      (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ),
    lMinusPrimedDartImage hτ a = d ∧
      a ∈ stageTriangleDartList
        (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ) j) ∨
  (∃ a : ℕ × Bool, ∃ j : TriangleCreationTime z,
    (EH a.1, a.2) = d ∧ a ∈ stageTriangleDartList z j).

The second disjunct needs no retained-triangle premise: the helpers above
derive it and construct both exact code dart preimages. The first disjunct
is handled by the existing primed triangle reverse helper after taking dart
preimages through D. Edge-image membership alone does not prove either
oriented creation-dart membership. This obligation is not assumed here. -/

end
end DirectedDistances.PaperProofs.Section5
