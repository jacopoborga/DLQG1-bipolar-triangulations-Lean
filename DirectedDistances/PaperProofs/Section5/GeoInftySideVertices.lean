module

public import DirectedDistances.PaperProofs.Section5.BoundaryGeodesicSideGluing

/-! vertex carriers of the geometric sides, with their original geometric definitions. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

/-- Helper toward Lemma 5.5: every run-zero vertex is a geometric endpoint,
including endpoints of missing edges. -/
theorem geoInfty_vertex_endpoint (w : ℕ → Fin 3) (v : ℕ) :
    ∃ e, edgeWest w e = v ∨ edgeEast w e = v := by
  obtain ⟨n, hn⟩ := kmswVertexAllocated_all w ⟨v⟩
  obtain ⟨⟨e, b⟩, he⟩ := stageEndpoint_exists w n v hn
  have hs := edge_endpoints_eq w e.isLt
  cases b with
  | false => exact ⟨e, Or.inl (hs.1.symm.trans he)⟩
  | true => exact ⟨e, Or.inr (hs.2.symm.trans he)⟩

/-- Helper toward Lemma 5.5: the geometric vertex carrier has no isolated
vertices; every retained vertex is an endpoint of a retained edge. -/
theorem m0GeodesicSide_mem_vertices_iff_endpoint
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) (v : ℕ) :
    v ∈ (m0GeodesicSide hp P s).vertices ↔
      ∃ e ∈ (m0GeodesicSide hp P s).edges,
        edgeWest (shiftedStream W 0) e = v ∨ edgeEast (shiftedStream W 0) e = v := by
  constructor
  · intro hv
    by_cases hseam : v ∈ m0GeodesicVertices P
    · obtain ⟨i, rfl⟩ := hseam
      refine ⟨P.codePath.edge i, ?_, Or.inl (P.codePath.edge_outgoing_at_initial _ i).2⟩
      have he := m0GeodesicEdges_subset_both hp P ⟨i, rfl⟩
      cases s with
      | left => exact he.1
      | right => exact he.2
    · obtain ⟨e, he⟩ := geoInfty_vertex_endpoint (shiftedStream W 0) v
      have hend (t : ThinMapSide) (ht : e ∈ (m0GeodesicSide hp P t).edges) :
          v ∈ (m0GeodesicSide hp P t).vertices := by
        have hvv := m0GeodesicSide_endpoints hp P t e ht
        rcases he with hw | ht
        · exact hw ▸ hvv.1
        · exact ht ▸ hvv.2
      rcases m0GeodesicSideEdges_cover hp P e with hl | hr
      · cases s with
        | left => exact ⟨e, hl, he⟩
        | right => exact False.elim (hseam (m0GeodesicSideVertices_inter hp P ▸ ⟨hend .left hl, hv⟩))
      · cases s with
        | left => exact False.elim (hseam (m0GeodesicSideVertices_inter hp P ▸ ⟨hv, hend .right hr⟩))
        | right => exact ⟨e, hr, he⟩
  · rintro ⟨e, he, hw | ht⟩
    · exact hw ▸ (m0GeodesicSide_endpoints hp P s e he).1
    · exact ht ▸ (m0GeodesicSide_endpoints hp P s e he).2

/-- Helper toward Lemma 5.5: every vertex of a coherent hatted side is
incident to a retained outgoing edge, including its source and boundary vertices. -/
theorem geometricSideSubmap_mem_vertices_iff_west
    (x : XDP) (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (s : ThinMapSide) (v : ℕ) :
    v ∈ (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime s q).vertices ↔
      ∃ e ∈ (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime s q).edges,
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime s q).west e = v := by
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    let w := boltzmannKMSWStream (pathCode q.val)
    let hf := sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q
    let hL := sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q
    let ht := sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q
    let hR := sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q
    let Q := sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q
    have hreach : Relation.ReflTransGen (sideDirectedStep w hf hL ht hR Q s) v
        (thinMapBoundaryVertex w hf hL ht hR s i) := hi.2
    obtain ⟨e, he, hw⟩ : ∃ e ∈ sideEdges w hf hL ht hR Q s, edgeWest w e = v := by
      rcases hreach.cases_head with hEq | ⟨b, hb, _⟩
      · obtain ⟨e, he, _, hw, _⟩ := thinMapBoundaryVertex_step w hf hL ht hR Q s i
        exact ⟨e, he, hw.trans hEq.symm⟩
      · obtain ⟨e, he, _, hw, _⟩ := hb
        exact ⟨e, he, hw⟩
    refine ⟨e, ?_, hw⟩
    change e ∈ ⋃ j, geometricAncestorEdges x renewalTime renewalTime_positiveSuccessTime s q j
    rw [iUnion_geometricAncestorEdges]
    exact he
  · rintro ⟨e, he, hw⟩
    exact hw ▸ (geometricSideSubmap_endpoints x renewalTime renewalTime_positiveSuccessTime s q e he).1




theorem boundaryGluing_nonneg_right_vertices
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k) :
    (m0GeodesicSide hp P .right).vertices =
      boundaryGluingHatVertexMap W h k hτ ''
        (geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
          renewalTime renewalTime_positiveSuccessTime .right
          ⟨boundaryFutureHattedPath k W, hqMode⟩).vertices := by
  let x := if longest then XDP.ldp else XDP.sdp
  let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k W, hqMode⟩
  let S := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
  have hedge := (boundaryGluing_nonneg_side_identities W h k hτ longest hp P
    hqMode Tpath hfin hleft hk).1
  have hend (e : ℕ) :
      edgeWest (shiftedStream W 0) (boundaryGluingHatEdgeMap W h k hτ e) =
          boundaryGluingHatVertexMap W h k hτ (S.west e) ∧
      edgeEast (shiftedStream W 0) (boundaryGluingHatEdgeMap W h k hτ e) =
          boundaryGluingHatVertexMap W h k hτ (S.east e) := by
    dsimp only [S, geometricSideSubmap, q]
    rw [boundaryGluing_decoded_stream W h k hτ]
    exact boundaryGluing_hat_edge_endpoints W h k hτ e
  apply Set.Subset.antisymm
  · intro v hv
    obtain ⟨e, he, hw | ht⟩ :=
      (m0GeodesicSide_mem_vertices_iff_endpoint hp P .right v).mp hv
    · rw [hedge] at he
      obtain ⟨a, ha, rfl⟩ := he
      exact ⟨S.west a, (geometricSideSubmap_endpoints x renewalTime
        renewalTime_positiveSuccessTime .right q a ha).1, (hend a).1.symm.trans hw⟩
    · rw [hedge] at he
      obtain ⟨a, ha, rfl⟩ := he
      exact ⟨S.east a, (geometricSideSubmap_endpoints x renewalTime
        renewalTime_positiveSuccessTime .right q a ha).2, (hend a).2.symm.trans ht⟩
  · rintro v ⟨a, ha, rfl⟩
    obtain ⟨e, he, hw⟩ :=
      (geometricSideSubmap_mem_vertices_iff_west x q .right a).mp ha
    have heM : boundaryGluingHatEdgeMap W h k hτ e ∈
        (m0GeodesicSide hp P .right).edges := by
      rw [hedge]
      exact ⟨e, he, rfl⟩
    exact ((hend e).1.trans (congrArg (boundaryGluingHatVertexMap W h k hτ) hw)) ▸
      (m0GeodesicSide_endpoints hp P .right _ heM).1

/-- Helper toward Lemma 5.5: endpoints of a geometric edge carrier. -/
@[expose] def geoInftyEdgeVertices (w : ℕ → Fin 3) (E : Set ℕ) : Set ℕ :=
  {v | ∃ e ∈ E, edgeWest w e = v ∨ edgeEast w e = v}

/-- Helper toward Lemma 5.5: endpoint carriers commute with block unions. -/
theorem geoInftyEdgeVertices_union (w : ℕ → Fin 3) (E F : Set ℕ) :
    geoInftyEdgeVertices w (E ∪ F) =
      geoInftyEdgeVertices w E ∪ geoInftyEdgeVertices w F := by
  ext v
  constructor
  · rintro ⟨e, he | he, hv⟩
    · exact Or.inl ⟨e, he, hv⟩
    · exact Or.inr ⟨e, he, hv⟩
  · rintro (⟨e, he, hv⟩ | ⟨e, he, hv⟩)
    · exact ⟨e, Or.inl he, hv⟩
    · exact ⟨e, Or.inr he, hv⟩

/-- Helper toward Lemma 5.5: the actual positional vertex carrier is exactly
the endpoint carrier; this includes the source and every seam vertex. -/
theorem m0GeodesicSide_vertices_eq_endpoints
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide) :
    (m0GeodesicSide hp P s).vertices =
      geoInftyEdgeVertices (shiftedStream W 0) (m0GeodesicSide hp P s).edges := by
  ext v
  exact m0GeodesicSide_mem_vertices_iff_endpoint hp P s v

/-- Helper toward Lemma 5.5: endpoint transport for either hatted side,
using its original increasing union of geometric ancestor vertex carriers. -/
theorem boundaryGluingHatSideEdges_vertices
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (x : XDP) (hq : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      x renewalTime renewalTime_positiveSuccessTime) (s : ThinMapSide) :
    geoInftyEdgeVertices (shiftedStream W 0)
        (boundaryGluingHatSideEdges W h k hτ x hq s) =
      boundaryGluingHatVertexMap W h k hτ ''
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime s
          ⟨boundaryFutureHattedPath k W, hq⟩).vertices := by
  let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k W, hq⟩
  let S := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime s q
  have hend (e : ℕ) :
      edgeWest (shiftedStream W 0) (boundaryGluingHatEdgeMap W h k hτ e) =
          boundaryGluingHatVertexMap W h k hτ (S.west e) ∧
      edgeEast (shiftedStream W 0) (boundaryGluingHatEdgeMap W h k hτ e) =
          boundaryGluingHatVertexMap W h k hτ (S.east e) := by
    dsimp only [S, geometricSideSubmap, q]
    rw [boundaryGluing_decoded_stream W h k hτ]
    exact boundaryGluing_hat_edge_endpoints W h k hτ e
  apply Set.Subset.antisymm
  · rintro v ⟨e, ⟨a, ha, rfl⟩, hw | ht⟩
    · exact ⟨S.west a, (geometricSideSubmap_endpoints x renewalTime
        renewalTime_positiveSuccessTime s q a ha).1, (hend a).1.symm.trans hw⟩
    · exact ⟨S.east a, (geometricSideSubmap_endpoints x renewalTime
        renewalTime_positiveSuccessTime s q a ha).2, (hend a).2.symm.trans ht⟩
  · rintro v ⟨a, ha, rfl⟩
    obtain ⟨e, he, hw⟩ :=
      (geometricSideSubmap_mem_vertices_iff_west x q s a).mp ha
    exact ⟨boundaryGluingHatEdgeMap W h k hτ e, ⟨e, he, rfl⟩,
      Or.inl ((hend e).1.trans (congrArg (boundaryGluingHatVertexMap W h k hτ) hw))⟩

/-- Helper toward Lemma 5.5: the stopped prefix's allocated vertex carrier. -/
@[expose] noncomputable def boundaryGluingPrefixVertices
    (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) : Set ℕ :=
  {v | v < (kmswStage (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k)).nextVertex}

/-- Helper toward Lemma 5.5: the edge-deleted prefix retains its attachment
root even at zero, where its edge carrier is empty. All other retained vertices
are endpoints of the remaining geometric edges. -/
@[expose] noncomputable def boundaryGluingPrefixMinusVertices
    (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) : Set ℕ :=
  geoInftyEdgeVertices (shiftedStream W 0) (boundaryGluingPrefixMinusEdges W h k) ∪
    {boundaryVertex (shiftedStream W 0) h k}

/-- Helper toward Lemma 5.5: at zero the deleted prefix retains exactly its
isolated attachment vertex, rather than either endpoint of the deleted edge. -/
theorem boundaryGluingPrefixMinusVertices_zero :
    boundaryGluingPrefixMinusVertices W h 0 = {0} := by
  simp only [boundaryGluingPrefixMinusVertices, boundaryGluingPrefixMinusEdges_zero,
    geoInftyEdgeVertices, Set.mem_empty_iff_false, false_and, exists_false,
    Set.ofPred_false, Set.empty_union, boundaryVertex_zero]

/-- Helper toward Lemma 5.5: every allocated prefix vertex is an endpoint of
its geometric edge carrier, including missing boundary edges. -/
theorem boundaryGluingPrefixEdges_vertices :
    geoInftyEdgeVertices (shiftedStream W 0) (boundaryGluingPrefixEdges W h k) =
      boundaryGluingPrefixVertices W h k := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  ext v
  constructor
  · rintro ⟨e, he, hw | ht⟩
    · have hb := (kmswStage_endpoints_lt_nextVertex w t e he).1
      rw [(edge_endpoints_eq w he).1, hw] at hb
      exact hb
    · have hb := (kmswStage_endpoints_lt_nextVertex w t e he).2
      rw [(edge_endpoints_eq w he).2, ht] at hb
      exact hb
  · intro hv
    obtain ⟨⟨e, b⟩, he⟩ := stageEndpoint_exists w t v hv
    have hs := edge_endpoints_eq w e.isLt
    cases b with
    | false => exact ⟨e, e.isLt, Or.inl (hs.1.symm.trans he)⟩
    | true => exact ⟨e, e.isLt, Or.inr (hs.2.symm.trans he)⟩

/-- Helper toward Lemma 5.5: the primed vertex embedding is the primed
limit embedding followed by the existing future embedding into run zero. -/
@[expose] noncomputable def boundaryGluingPrimedVertexMap
    (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) : ℕ → ℕ :=
  boundaryGluingFutureVertexMap W h k ∘
    primedLimitVertexMap (boundaryGluingFutureStream W h k) hτ





theorem boundaryGluingPrefixMinusVertices_of_pos (hk : 0 < k) :
    boundaryGluingPrefixMinusVertices W h k =
      {v | v < (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k - 1)).nextVertex} := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  have hk1 : 1 ≤ k := by omega
  have hfind : t = Nat.find (h.rightHit k hk1) := by
    dsimp only [t]
    unfold boundaryHitTime
    simp only [dite_eq_right (ne_of_gt hk), dite_eq_left hk]
  have hspec : R w t = -k := boundaryHitTime_right_spec w h hk1
  have htpos : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := by omega
    rw [ht0] at hspec
    change 0 = -k at hspec
    omega
  have hmin : R w t = minR w t :=
    (kmswStage_UR_eq_nil_iff_record w t).mp (boundaryHit_right_UR_empty w h hk1)
  have hrec : ∀ j < t, R w t ≤ R w j - 1 := by
    intro j hj
    have hm := runningMin_le (R w) t j hj.le
    change minR w t ≤ R w j at hm
    rw [← hmin] at hm
    have hn := Nat.find_min (h.rightHit k hk1) (show j < Nat.find (h.rightHit k hk1) by
      rw [← hfind]; exact hj)
    change R w j ≠ -k at hn
    omega
  have hd := record_stage_before_empty_UR_public w t hrec htpos
  have hprev : t - 1 + 1 = t := by omega
  have hcount : (kmswStage w t).nextEdge = (kmswStage w (t - 1)).nextEdge + 1 := by
    conv_lhs => rw [← hprev]
    simp only [kmswStage, kmswStep, kmswCodeStep, hd.1,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      ↓reduceIte, kmswStepOfStep, hd.2, State.addEdge]
  have hact : act w t = (kmswStage w (t - 1)).nextEdge := by
    change (kmswStage w t).active = _
    conv_lhs => rw [← hprev]
    simp only [kmswStage, kmswStep, kmswCodeStep, hd.1,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      ↓reduceIte, kmswStepOfStep, hd.2, State.addEdge]
  have hedges (e : ℕ) : e ∈ boundaryGluingPrefixMinusEdges W h k ↔
      e < (kmswStage w (t - 1)).nextEdge := by
    change (e < (kmswStage w t).nextEdge ∧ e ≠ act w t) ↔ _
    rw [hcount, hact]
    omega
  have hr : boundaryVertex w h k < (kmswStage w (t - 1)).nextVertex := by
    have hroot : boundaryVertex w h k = (kmswStage w (t - 1)).east (act w (t - 1)) := by
      rw [boundaryVertex_eq_edgeWest_hit w h k,
        ← (edge_endpoints_eq w (act_lt_nextEdge w (le_refl t))).1]
      change (kmswStage w t).west (kmswStage w t).active = _
      conv_lhs => rw [← hprev]
      simp only [kmswStage, kmswStep, kmswCodeStep, hd.1,
        show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
        ↓reduceIte, kmswStepOfStep, hd.2, State.addEdge, ↓reduceIte]
      rfl
    rw [hroot]
    exact (kmswStage_endpoints_lt_nextVertex w (t - 1) _
      (act_lt_nextEdge w (le_refl (t - 1)))).2
  ext v
  constructor
  · rintro (⟨e, he, hw | ht⟩ | hv)
    · have hb := (kmswStage_endpoints_lt_nextVertex w (t - 1) e ((hedges e).mp he)).1
      rw [(edge_endpoints_eq w ((hedges e).mp he)).1, hw] at hb
      exact hb
    · have hb := (kmswStage_endpoints_lt_nextVertex w (t - 1) e ((hedges e).mp he)).2
      rw [(edge_endpoints_eq w ((hedges e).mp he)).2, ht] at hb
      exact hb
    · exact (Set.mem_singleton_iff.mp hv) ▸ hr
  · intro hv
    obtain ⟨⟨e, b⟩, he⟩ := stageEndpoint_exists w (t - 1) v hv
    have hs := edge_endpoints_eq w e.isLt
    apply Or.inl
    cases b with
    | false => exact ⟨e, (hedges e).mpr e.isLt, Or.inl (hs.1.symm.trans he)⟩
    | true => exact ⟨e, (hedges e).mpr e.isLt, Or.inr (hs.2.symm.trans he)⟩

/-- Helper toward Lemma 5.5: the primed embedding preserves unordered
endpoints, including missing edges whose dart orientations can reverse. -/
theorem boundaryGluing_primed_edge_endpoints
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) (e : ℕ) :
    let u := primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ
    let E := boundaryGluingPrimedEdgeMap W h k hτ e
    let a := boundaryGluingPrimedVertexMap W h k hτ (edgeWest u e)
    let b := boundaryGluingPrimedVertexMap W h k hτ (edgeEast u e)
    (edgeWest (shiftedStream W 0) E = a ∧ edgeEast (shiftedStream W 0) E = b) ∨
      (edgeWest (shiftedStream W 0) E = b ∧ edgeEast (shiftedStream W 0) E = a) := by
  have hf := boundaryGluing_future_edge_endpoints W h k
    (primedLimitEdgeMap (boundaryGluingFutureStream W h k) hτ e)
  have hp := primedLimitEdgeMap_endpoint_orders (boundaryGluingFutureStream W h k) hτ e
  dsimp only at hp ⊢
  rcases hp with hp | hp
  · exact Or.inl ⟨hf.1.trans (congrArg (boundaryGluingFutureVertexMap W h k) hp.1),
      hf.2.trans (congrArg (boundaryGluingFutureVertexMap W h k) hp.2)⟩
  · exact Or.inr ⟨hf.1.trans (congrArg (boundaryGluingFutureVertexMap W h k) hp.1),
      hf.2.trans (congrArg (boundaryGluingFutureVertexMap W h k) hp.2)⟩

/-- Helper toward Lemma 5.5: all primed vertices, including both endpoints
of the missing root, are exactly the endpoints of its embedded edge carrier. -/
theorem boundaryGluingPrimedEdges_vertices
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :
    geoInftyEdgeVertices (shiftedStream W 0) (boundaryGluingPrimedEdges W h k hτ) =
      boundaryGluingPrimedVertexMap W h k hτ '' Set.univ := by
  let u := primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ
  apply Set.Subset.antisymm
  · rintro v ⟨E, ⟨e, rfl⟩, hw | ht⟩
    · rcases boundaryGluing_primed_edge_endpoints hτ e with he | he
      · exact ⟨edgeWest u e, Set.mem_univ _, he.1.symm.trans hw⟩
      · exact ⟨edgeEast u e, Set.mem_univ _, he.1.symm.trans hw⟩
    · rcases boundaryGluing_primed_edge_endpoints hτ e with he | he
      · exact ⟨edgeEast u e, Set.mem_univ _, he.2.symm.trans ht⟩
      · exact ⟨edgeWest u e, Set.mem_univ _, he.2.symm.trans ht⟩
  · rintro v ⟨a, _, rfl⟩
    obtain ⟨e, hw | ht⟩ := geoInfty_vertex_endpoint u a
    · refine ⟨boundaryGluingPrimedEdgeMap W h k hτ e, ⟨e, rfl⟩, ?_⟩
      rcases boundaryGluing_primed_edge_endpoints hτ e with he | he
      · exact Or.inl (he.1.trans (congrArg (boundaryGluingPrimedVertexMap W h k hτ) hw))
      · exact Or.inr (he.2.trans (congrArg (boundaryGluingPrimedVertexMap W h k hτ) hw))
    · refine ⟨boundaryGluingPrimedEdgeMap W h k hτ e, ⟨e, rfl⟩, ?_⟩
      rcases boundaryGluing_primed_edge_endpoints hτ e with he | he
      · exact Or.inr (he.2.trans (congrArg (boundaryGluingPrimedVertexMap W h k hτ) ht))
      · exact Or.inl (he.1.trans (congrArg (boundaryGluingPrimedVertexMap W h k hτ) ht))

/-- Helper toward Lemma 5.5: the hatted vertex root maps to x_k. -/
theorem boundaryGluingHatVertexMap_zero
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :
    boundaryGluingHatVertexMap W h k hτ 0 = boundaryVertex (shiftedStream W 0) h k := by
  change boundaryGluingFutureVertexMap W h k
    (hatLimitVertexMap (boundaryGluingFutureStream W h k) hτ 0) = _
  rw [(hatLimitExplicitInput (boundaryGluingFutureStream W h k) hτ).root]
  exact boundaryGluingFutureVertexMap_zero W h k

/-- Helper toward Lemma 5.5: the shared attachment root belongs to both
hatted vertex images, independently of the sign of k. -/
theorem boundaryGluing_root_mem_hatSide_vertices
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (x : XDP) (hq : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      x renewalTime renewalTime_positiveSuccessTime) (s : ThinMapSide) :
    boundaryVertex (shiftedStream W 0) h k ∈
      boundaryGluingHatVertexMap W h k hτ ''
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime s
          ⟨boundaryFutureHattedPath k W, hq⟩).vertices := by
  let q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime :=
    ⟨boundaryFutureHattedPath k W, hq⟩
  refine ⟨0, ?_, boundaryGluingHatVertexMap_zero hτ⟩
  change 0 ∈ ⋃ i, geometricAncestorVertices x renewalTime renewalTime_positiveSuccessTime s q i
  rw [iUnion_geometricAncestorVertices]
  exact source_mem_sideVertices _
    (sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_nonneg x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_left_transient x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestor_right_unbounded x renewalTime renewalTime_positiveSuccessTime q)
    (sourceAncestorPath x renewalTime renewalTime_positiveSuccessTime q) s




theorem boundaryGluing_nonneg_left_vertices
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : 0 ≤ k) :
    (m0GeodesicSide hp P .left).vertices =
      id '' boundaryGluingPrefixMinusVertices W h k ∪
        boundaryGluingHatVertexMap W h k hτ ''
          (geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
            renewalTime renewalTime_positiveSuccessTime .left
            ⟨boundaryFutureHattedPath k W, hqMode⟩).vertices ∪
        boundaryGluingPrimedVertexMap W h k hτ '' Set.univ := by
  rw [m0GeodesicSide_vertices_eq_endpoints hp P .left,
    (boundaryGluing_nonneg_side_identities W h k hτ longest hp P
      hqMode Tpath hfin hleft hk).2,
    geoInftyEdgeVertices_union, geoInftyEdgeVertices_union]
  change _ ∪ geoInftyEdgeVertices _ (boundaryGluingHatSideEdges W h k hτ _ hqMode .left) ∪ _ = _
  rw [boundaryGluingHatSideEdges_vertices hτ, boundaryGluingPrimedEdges_vertices hτ]
  simp only [Set.image_id, boundaryGluingPrefixMinusVertices]
  have hr := boundaryGluing_root_mem_hatSide_vertices hτ
    (if longest then XDP.ldp else XDP.sdp) hqMode .left
  apply Set.Subset.antisymm
  · rintro v ((he | hh) | hp)
    · exact Or.inl (Or.inl (Or.inl he))
    · exact Or.inl (Or.inr hh)
    · exact Or.inr hp
  · rintro v (((he | hr') | hh) | hp)
    · exact Or.inl (Or.inl he)
    · exact Or.inl (Or.inr ((Set.mem_singleton_iff.mp hr') ▸ hr))
    · exact Or.inl (Or.inr hh)
    · exact Or.inr hp



theorem boundaryGluing_nonpos_left_vertices
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : k ≤ 0) :
    (m0GeodesicSide hp P .left).vertices =
      boundaryGluingPrimedVertexMap W h k hτ '' Set.univ ∪
        boundaryGluingHatVertexMap W h k hτ ''
          (geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
            renewalTime renewalTime_positiveSuccessTime .left
            ⟨boundaryFutureHattedPath k W, hqMode⟩).vertices := by
  rw [m0GeodesicSide_vertices_eq_endpoints hp P .left,
    (boundaryGluing_nonpos_side_identities W h k hτ longest hp P
      hqMode Tpath hfin hleft hk).1,
    geoInftyEdgeVertices_union, boundaryGluingPrimedEdges_vertices hτ]
  exact congrArg (fun V => boundaryGluingPrimedVertexMap W h k hτ '' Set.univ ∪ V)
    (boundaryGluingHatSideEdges_vertices hτ _ hqMode .left)



theorem boundaryGluing_nonpos_right_vertices
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (hqMode : boundaryFutureHattedPath k W ∈ selectedCutCoherentDomain
      (if longest then XDP.ldp else XDP.sdp) renewalTime renewalTime_positiveSuccessTime)
    (Tpath : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
    (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
    (hk : k ≤ 0) :
    (m0GeodesicSide hp P .right).vertices =
      id '' boundaryGluingPrefixVertices W h k ∪
        boundaryGluingHatVertexMap W h k hτ ''
          (geometricSideSubmap (if longest then XDP.ldp else XDP.sdp)
            renewalTime renewalTime_positiveSuccessTime .right
            ⟨boundaryFutureHattedPath k W, hqMode⟩).vertices := by
  rw [m0GeodesicSide_vertices_eq_endpoints hp P .right,
    (boundaryGluing_nonpos_side_identities W h k hτ longest hp P
      hqMode Tpath hfin hleft hk).2,
    geoInftyEdgeVertices_union, boundaryGluingPrefixEdges_vertices, Set.image_id]
  exact congrArg (fun V => boundaryGluingPrefixVertices W h k ∪ V)
    (boundaryGluingHatSideEdges_vertices hτ _ hqMode .right)

end DirectedDistances.PaperProofs.Section5

