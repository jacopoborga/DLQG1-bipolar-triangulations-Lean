/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusActualSideIso
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole2

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section ActualFaceTransport

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

local notation "w" => shiftedStream W 0
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "U" => boundaryGluingFutureStream W h k
local notation "X" => (ite (longest = true) XDP.ldp XDP.sdp)
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain X renewalTime renewalTime_positiveSuccessTime)
local notation "Q" => geometricSideSubmap X renewalTime
  renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "p" => primedCode (primedSimInput U) hτ
local notation "hf" => primedCode_finiteIncidence U hτ hfin
local notation "z" => hatCodes U hτ
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ

/-- Helper toward Lemma 5.5: a run-zero creation triangle with all edges in
the actual left side has its whole glued face retained there. -/
theorem lMinusRunZeroCreationTriangle_retained
    (j : TriangleCreationTime w)
    (hall : ∀ d ∈ stageTriangleDartList w j, d.1 ∈ (S).edges) :
    ∃ G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      G.val ⊆ m0GeodesicSideOpenRegion hp P .left ∧
      ∀ d ∈ stageTriangleDartList w j,
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 d) G := by
  obtain ⟨G, hGR, hb⟩ := rMinusWhole_creation_gluedFace hp (H := H) j
  obtain ⟨d, hd, hoff⟩ := rMinusWhole_triangle_off_path w (H.1 0) P.codePath j
  exact ⟨G, (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P hoff
    d.2 G hGR (hb d hd) .left).mp (hall d hd), hb⟩

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: a primed code face step is retained in the
actual left side with its original infinite successor. -/
theorem lMinusPrimedCodeFaceNext_actual
    (j : TriangleCreationTime
      (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ))
    (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList
      (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ) j) :
    (S).faceNext (lMinusPrimedDartImage hτ d)
      (lMinusPrimedDartImage hτ
        (kmswInfFaceSucc
          (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ)
          (primedCode_finiteIncidence (boundaryGluingFutureStream W h k) hτ hfin)
          d)) := by
  obtain ⟨J, hmap, hall, hsucc⟩ :=
    lMinusPrimedCreationTriangle_retained hτ hp P hqMode Tpath hfin hleft hk j
  obtain ⟨G, hG, hb⟩ := lMinusRunZeroCreationTriangle_retained hp P J hall
  exact ⟨⟨G, hb _ (hmap d hd), hG⟩, (hsucc d hd).symm⟩

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: either retained code-block face step maps to a
retained face step of the actual left side. -/
theorem lMinusCodeWholeFaceNext_actual_forward
    (d e : LMinusCodeGluedDart rL Q)
    (hde : lMinusCodeWholeFaceNext rL qL
      (lMinus_primed_observation_finiteIncidence hτ hfin) d e) :
    (S).faceNext
      (lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val
      (lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk e).val := by
  rcases hde with ⟨a, b, hda, heb, ⟨j, ha, hsucc⟩⟩ |
    ⟨a, b, hda, heb, hsucc⟩
  · subst d
    subst e
    rw [lMinusCodeGluedDartEquiv_primed hτ hp P hqMode Tpath hfin hleft hk a,
      lMinusCodeGluedDartEquiv_primed hτ hp P hqMode Tpath hfin hleft hk b]
    have hcode : (rL).code.1 = p := by
      change (leftSideObsNonpos X k W).1 = p
      exact lMinus_primed_observation_code (longest := longest) hτ
    let j' : TriangleCreationTime p := ⟨j.val, by rw [← hcode]; exact j.property⟩
    have hlist : stageTriangleDartList (rL).code.1 j =
        stageTriangleDartList p j' := by
      simp only [stageTriangleDartList, stageTriangleDartTriple, j', hcode]
    have ha' : a ∈ stageTriangleDartList p j' := hlist ▸ ha
    have hcongr : ∀ (c d : ℕ → Fin 3) (hc : KMSWFiniteIncidence c)
        (hd : KMSWFiniteIncidence d), c = d → kmswInfFaceSucc c hc =
          kmswInfFaceSucc d hd := by
      intro c d hc hd hcd
      subst d
      rfl
    have hsuccEq := hcongr _ _
      (lMinus_primed_observation_finiteIncidence hτ hfin)
      (primedCode_finiteIncidence U hτ hfin) hcode
    have hsucc' : kmswInfFaceSucc p (primedCode_finiteIncidence U hτ hfin) a = b :=
      (congrArg (fun f : Equiv.Perm (ℕ × Bool) => f a) hsuccEq).symm.trans hsucc
    have hactual := lMinusPrimedCodeFaceNext_actual hτ hp P hqMode Tpath
      hfin hleft hk j' a ha'
    rw [hsucc'] at hactual
    exact hactual
  · subst d
    subst e
    rw [lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk a,
      lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk b]
    obtain ⟨⟨j, hd, hall⟩, hsucc⟩ := hsucc
    have hc := boundaryGluing_decoded_stream W h k hτ
    let j' : TriangleCreationTime z := ⟨j.val, by rw [← hc]; exact j.property⟩
    have hlist : stageTriangleDartList
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) j =
          stageTriangleDartList z j' := by
      simp only [stageTriangleDartList, stageTriangleDartTriple, j', hc]
    have hd' : a.val ∈ stageTriangleDartList z j' := hlist ▸ hd
    have hall' : ∀ d ∈ stageTriangleDartList z j', d.1 ∈ (Q).edges := by
      intro d hd
      exact hall d (hlist.symm ▸ hd)
    obtain ⟨G, hG, hb⟩ := lMinusHattedCreationTriangle_retained
      hτ hp P hqMode Tpath hfin hleft hk j' hall'
    have hsucc' : kmswInfFaceSucc z
        (hatCodes_inducedFiniteIncidence U hτ hfin) a.val = b.val := by
      have hcongr : ∀ (c d : ℕ → Fin 3) (hc : KMSWFiniteIncidence c)
          (hd : KMSWFiniteIncidence d), c = d → kmswInfFaceSucc c hc =
            kmswInfFaceSucc d hd := by
        intro c d hc hd hcd
        subst d
        rfl
      have hsuccEq := hcongr _ _
        (sourceAncestor_finite_incidence X renewalTime
          renewalTime_positiveSuccessTime qL)
        (hatCodes_inducedFiniteIncidence U hτ hfin) hc
      exact (congrArg (fun f : Equiv.Perm (ℕ × Bool) => f a.val) hsuccEq).symm.trans hsucc
    refine ⟨⟨G, hb a.val hd', hG⟩, ?_⟩
    have hmap := rMinusWhole_hatted_infFaceSucc hτ (H := H) hfin j' a.val hd'
    rw [hsucc'] at hmap
    exact hmap

include hτ hqMode hfin in
/-- Helper toward Lemma 5.5: a primed and hatted triangle dart with the
same glued edge ID lies on their shared beta boundary. -/
theorem lMinusPrimedHattedDart_shared_edge_mem_beta
    (jP : TriangleCreationTime p)
    (jH : TriangleCreationTime z)
    (hRetH : ∀ d ∈ stageTriangleDartList z jH, d.1 ∈ (Q).edges)
    (dP : ℕ × Bool) (_hdP : dP ∈ stageTriangleDartList p jP)
    (dH : ℕ × Bool) (hdH : dH ∈ stageTriangleDartList z jH)
    (heq : lMinusPrimedDartImage hτ dP = (EH dH.1, dH.2)) :
    (lMinusPrimedDartImage hτ dP).1 ∈ boundaryGluingBetaEdges W h k hτ := by
  have hP : (lMinusPrimedDartImage hτ dP).1 ∈
      boundaryGluingPrimedEdges W h k hτ := ⟨dP.1, rfl⟩
  have hH : (lMinusPrimedDartImage hτ dP).1 ∈
      boundaryGluingLeftHatEdges W h k hτ X hqMode := by
    rw [heq]
    exact ⟨dH.1, hRetH dH hdH, rfl⟩
  have hboth : (lMinusPrimedDartImage hτ dP).1 ∈
      boundaryGluingPrimedEdges W h k hτ ∩
        boundaryGluingLeftHatEdges W h k hτ X hqMode := ⟨hP, hH⟩
  exact (Set.ext_iff.mp
    (boundaryGluingPrimedEdges_inter_leftHatEdges W h k hτ X hqMode hfin)
    (lMinusPrimedDartImage hτ dP).1).mp hboth

include hτ hqMode hfin in
/-- Helper toward Lemma 5.5: primed and retained hatted creation triangles
can share a mapped dart only along their common beta boundary. -/
theorem lMinusPrimedHattedTriangle_intersection_only_boundary
    (jP : TriangleCreationTime p) (jH : TriangleCreationTime z)
    (hRetH : ∀ d ∈ stageTriangleDartList z jH, d.1 ∈ (Q).edges)
    (dP dH : ℕ × Bool)
    (hdP : dP ∈ stageTriangleDartList p jP)
    (hdH : dH ∈ stageTriangleDartList z jH)
    (heq : lMinusPrimedDartImage hτ dP = (EH dH.1, dH.2)) :
    (lMinusPrimedDartImage hτ dP).1 ∈ boundaryGluingBetaEdges W h k hτ :=
  lMinusPrimedHattedDart_shared_edge_mem_beta hτ hqMode hfin
    jP jH hRetH dP hdP dH hdH heq

include hp P in
/-- Helper toward Lemma 5.5: every retained face step of the actual left
side comes from one run-zero KMSW creation triangle, with all its edges kept. -/
theorem lMinusActualFaceNext_triangle
    (d e : ℕ × Bool) (hde : (S).faceNext d e) :
    ∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j ∧
      ∀ a ∈ stageTriangleDartList w j, a.1 ∈ (S).edges := by
  obtain ⟨⟨G, hdG, hG⟩, _⟩ := hde
  let A := monotoneFamilyDrawing w (H.1 0) (monotone_family_all w)
  have hGR : G.val ⊆ m0GeodesicAmbientRegion W H h := fun a ha =>
    (m0GeodesicLeftOpen_subset hp P (hG ha)).1
  have hupper : G.val ⊆ {a : ℂ | seamFun w h (H.1 0) a.re < a.im} := by
    rcases WholePlaneM0Drawing.face_side W h hp H G with hu | hl
    · exact hu
    · obtain ⟨a, ha, hface⟩ := G.property
      have ham : a ∈ G.val := hface ▸ mem_connectedComponentIn ha
      have hle : seamFun w h (H.1 0) a.re ≤ a.im := hGR ham
      have hlt : a.im < seamFun w h (H.1 0) a.re := hl ham
      exact False.elim (not_lt_of_ge hle hlt)
  obtain ⟨G₀, hG₀, hval⟩ := (WholePlaneM0Drawing.m0_face_iff W h hp H G).mp hupper
  have hb (r : ℕ × Bool) : A.dartBorders r G₀ ↔
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 r) G :=
    (PLDrawing.dartBorders_congr A _ G₀ G
      (WholePlanePastGlueM0Restriction.restrict_arc W h hp H r) hval).symm
  obtain ⟨j, hlist, _, _⟩ := boundedFace_orbit_is_triangle w (H.1 0) h G₀ hG₀
  have hj (a : ℕ × Bool) : A.dartBorders a G₀ ↔ a ∈ stageTriangleDartList w j :=
    Set.ext_iff.mp hlist a
  refine ⟨j, (hj d).mp ((hb d).mpr hdG), ?_⟩
  intro a ha
  by_cases hs : a.1 ∈ m0GeodesicEdges P
  · exact (m0GeodesicEdges_subset_both hp P hs).1
  · exact (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P hs
      a.2 G hGR ((hb a).mp ((hj a).mpr ha)) .left).mpr hG

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: the first dart of an actual retained face step
has a representative in one of the two glued code blocks. -/
theorem lMinusActualFaceNext_firstDart_in_block
    (d e : ℕ × Bool) (hde : (S).faceNext d e) :
    d ∈ Set.range (lMinusPrimedDartImage hτ) ∨
      d ∈ Set.range (fun a : {a : ℕ × Bool // a.1 ∈ (Q).edges} =>
        (EH a.val.1, a.val.2)) := by
  obtain ⟨j, hd, hall⟩ := lMinusActualFaceNext_triangle hp P d e hde
  have hside : d.1 ∈ (S).edges := hall d hd
  have hset := lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk
  exact (Set.ext_iff.mp hset d).mp hside

end ActualFaceTransport

end DirectedDistances.PaperProofs.Section5
