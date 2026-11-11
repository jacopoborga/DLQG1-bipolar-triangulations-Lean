/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposLeftSideWhole3

 

public section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

private theorem lMinusCreation_record_east_eq_iff (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) :
    edgeEast w (stageTriangleRecord w j).1 =
      edgeEast w (stageTriangleRecord w j).2.1 ↔ w j.val = 0 := by
  have hjmem : stageTriangleRecord w j ∈ (kmswStage w (j.val + 1)).triangles := by
    rw [← stageTriangleTimes_records]
    exact List.mem_map.mpr ⟨j, (mem_stageTriangleTimes w _ j).mpr (Nat.lt_succ_self _), rfl⟩
  have hb := triBound_stage w (j.val + 1) _ hjmem
  rw [← (edge_endpoints_eq w hb.1).2, ← (edge_endpoints_eq w hb.2.1).2]
  have ha := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
  have hne : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge := ne_of_lt ha
  have hne' : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge + 1 := by omega
  have hv := (kmswStage_endpoints_lt_nextVertex w j.val _ ha).2
  rcases j.property with h0 | h1
  · cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, h0, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
        hp, State.addEdge, hne, hne']
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    simp [stageTriangleRecord, h1, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
      State.addEdge, hne, hne', ne_of_lt hv]

private theorem lMinusCreation_oriented_mem (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (d : ℕ × Bool) :
    d ∈ triangleOrientedDarts w (stageTriangleRecord w j) ↔
      d ∈ stageTriangleDartList w j := by
  unfold triangleOrientedDarts
  rcases j.property with h0 | h1
  · rw [ite_eq_left ((lMinusCreation_record_east_eq_iff w j).mpr h0)]
    cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple,
        h0, hp, or_comm, or_left_comm, or_assoc]
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    rw [ite_eq_right (fun he => h0 ((lMinusCreation_record_east_eq_iff w j).mp he))]
    simp only [stageTriangleRecord, stageTriangleDartList, stageTriangleDartTriple,
      h0, ↓reduceIte]

private theorem lMinusCreation_triangle_off_path (w : ℕ → Fin 3)
    (hf : KMSWFiniteIncidence w) {v : ℕ} (R : InfinitePresentPath w ⟨v⟩)
    (j : TriangleCreationTime w) :
    ∃ d ∈ stageTriangleDartList w j, d.1 ∉ Set.range R.edge := by
  classical
  have hW := infinitePresentPath_west_injective hf
    (fun n => ⟨_, (monotone_family_all w n).choose_spec⟩) R
  have hE : Function.Injective (fun i => edgeEast w (R.edge i)) := by
    intro a b hab
    change edgeEast w (R.edge a) = edgeEast w (R.edge b) at hab
    have he (i : ℕ) : edgeEast w (R.edge i) = edgeWest w (R.edge (i + 1)) :=
      (R.edge_incoming_at_succ w i).2.trans (R.edge_outgoing_at_initial w (i + 1)).2.symm
    rw [he, he] at hab
    have := hW hab
    omega
  let t := stageTriangleRecord w j
  have hne : t.1 ≠ t.2.1 := by
    have ha := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
    rcases j.property with h0 | h1
    · cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
        simpa only [t, stageTriangleRecord, h0, ↓reduceIte, hp] using ne_of_lt ha
    · have h0 : w j.val ≠ 0 := by rw [h1]; decide
      simpa only [t, stageTriangleRecord, h0, ↓reduceIte] using ne_of_lt ha
  have hold : (t.1, false) ∈ stageTriangleDartList w j := by
    apply (lMinusCreation_oriented_mem w j _).mp
    unfold triangleOrientedDarts
    split <;> exact List.mem_cons_self
  have hnew : (t.2.1, true) ∈ stageTriangleDartList w j := by
    apply (lMinusCreation_oriented_mem w j _).mp
    unfold triangleOrientedDarts
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false, t, Prod.mk.injEq,
      and_true, true_or, or_true]
  by_contra hn
  have hall : ∀ d ∈ stageTriangleDartList w j, d.1 ∈ Set.range R.edge := by
    intro d hd
    by_contra hnot
    exact hn ⟨d, hd, hnot⟩
  obtain ⟨a, ha⟩ := hall _ hold
  obtain ⟨b, hb⟩ := hall _ hnew
  apply hne
  have heq : a = b := by
    by_cases h0 : w j.val = 0
    · apply hE
      change edgeEast w (R.edge a) = edgeEast w (R.edge b)
      rw [ha, hb]
      exact (lMinusCreation_record_east_eq_iff w j).mpr h0
    · apply hW
      change edgeWest w (R.edge a) = edgeWest w (R.edge b)
      rw [ha, hb]
      have h1 : w j.val = 1 := j.property.resolve_left h0
      obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
      have hbounds := triBound_stage w (j.val + 1) _ (hi ▸ List.get_mem _ i)
      rw [← (edge_endpoints_eq w hbounds.1).1, ← (edge_endpoints_eq w hbounds.2.1).1]
      have hact := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
      have hne' : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge + 1 := by omega
      simp [stageTriangleRecord, h1, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep,
        State.addEdge, ne_of_lt hact, hne']
  exact ha.symm.trans (heq ▸ hb)

section HattedRetention

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
local notation "U" => boundaryGluingFutureStream W h k
local notation "Q" => geometricSideSubmap (ite (longest = true) XDP.ldp XDP.sdp)
  renewalTime renewalTime_positiveSuccessTime ThinMapSide.left
  (Subtype.mk (boundaryFutureHattedPath k W) hqMode)
local notation "z" => hatCodes U hτ
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: every retained hatted triangle maps to one
retained geometric triangle on the left, with all bordering darts preserved. -/
theorem lMinusHattedCreationTriangle_retained (j : TriangleCreationTime z)
    (hall : ∀ d ∈ stageTriangleDartList z j, d.1 ∈ (Q).edges) :
    ∃ G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face,
      G.val ⊆ m0GeodesicSideOpenRegion hp P .left ∧
      ∀ d ∈ stageTriangleDartList z j,
        (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
          (wholePlaneDartι W 0 (EH d.1, d.2)) G := by
  have hc := boundaryGluing_decoded_stream W h k hτ
  let j' : TriangleCreationTime
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))) :=
    ⟨j.val, by rw [hc]; exact j.property⟩
  let R := sourceAncestorPath (if longest then XDP.ldp else XDP.sdp)
    renewalTime renewalTime_positiveSuccessTime ⟨boundaryFutureHattedPath k W, hqMode⟩
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index z j
  let T : HatLocalTri U hτ :=
    ⟨stageTriangleRecord z j, j.val + 1, hi ▸ List.get_mem _ i⟩
  obtain ⟨G, hGR, hborder⟩ := boundaryGluing_hatTriangle_gluedFace W h k hτ H hp hfin T
  have hb (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList z j) :
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (EH d.1, d.2)) G :=
    hborder d ((lMinusCreation_oriented_mem z j d).mpr hd)
  obtain ⟨d, hd, hoff⟩ := lMinusCreation_triangle_off_path _
    (sourceAncestor_finite_incidence (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime
      ⟨boundaryFutureHattedPath k W, hqMode⟩) R j'
  have hdz : d ∈ stageTriangleDartList z j := by
    simpa only [stageTriangleDartList, stageTriangleDartTriple, j', hc] using hd
  have hid := boundaryGluing_geodesicIdentification W h k hτ longest hqMode
    hp Tpath P hfin hleft
  have hoff' : EH d.1 ∉ m0GeodesicEdges P := by
    rintro ⟨a, ha⟩
    apply hoff
    exact ⟨a, boundaryGluingHatEdgeMap_injective W h k hτ ((hid a).symm.trans ha)⟩
  have heL : EH d.1 ∈ (m0GeodesicSide hp P .left).edges :=
    boundaryGluingLeftHatEdges_subset_left W h k hτ longest hp P hqMode
      Tpath hfin hleft ⟨d.1, hall d hdz, rfl⟩
  exact ⟨G, (boundaryGluing_sideEdges_iff_borderingFace W h k longest hp P hoff'
    d.2 G hGR (hb d hdz) .left).mp heL, hb⟩












































end HattedRetention

end DirectedDistances.PaperProofs.Section5
