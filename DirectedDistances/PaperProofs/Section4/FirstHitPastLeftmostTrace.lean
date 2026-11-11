module

public import DirectedDistances.KMSW.PastLeftmostPathInduction
public import DirectedDistances.KMSW.StageInfiniteOutgoingOrderSource
public import DirectedDistances.PaperProofs.Section4.FirstHitGeodesicPiece
public import DirectedDistances.PaperProofs.Section4.FirstHitXDPIdentification

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory Quiver

section CutRecord

variable (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ)
    (hcut : mapCutVertex w hfin (recordVertex w t).id)

include hcut

/-- at a cut record vertex (and a.s. at the first hit τ_r on the barrier event) the
past-stage leftmost XDP trace equals the prefix of the infinite leftmost geodesic,
whose length is the past-map XDP length; the renewal-time selection T_{m_k} is not
treated; not the paper result. -/
theorem past_ldp_trace_eq_prefix
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments) :
    let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hg
    ∃ i, (P.initial i).1 = recordVertex w t ∧
      (∀ k < i, (P.initial k).1 ≠ recordVertex w t) ∧
      ∀ j ≤ i, ∃ ds : List (StageDart (kmswStage w (t - 1)).nextEdge),
        pastStageLeftmostXDPTrace w t .ldp j = some ((P.initial j).1.id, ds) ∧
          ds.map (fun d => d.1.val) = pathEdgeList (P.initial j).2 ∧
          (j = i → pastStageLeftmostXDPTrace w t .ldp (j + 1) = none) := by
  dsimp only
  let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hg
  obtain ⟨i, hi, hfirst, htrace⟩ :=
    past_ldp_firstVisit_trace_eq_prefix w hfin hL htrans hR t hcut hg
  refine ⟨i, hi, hfirst, ?_⟩
  intro j hj
  exact htrace j hj (stageOutgoingEdgeOrder_hord w hfin hL htrans hR t P j)

/-- at a cut record vertex (and a.s. at the first hit τ_r on the barrier event) the
past-stage leftmost XDP trace equals the prefix of the infinite leftmost geodesic,
whose length is the past-map XDP length; the renewal-time selection T_{m_k} is not
treated; not the paper result. -/
theorem past_sdp_trace_eq_prefix
    (hg : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) :
    let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hg
    ∃ i, (P.initial i).1 = recordVertex w t ∧
      (∀ k < i, (P.initial k).1 ≠ recordVertex w t) ∧
      ∀ j ≤ i, ∃ ds : List (StageDart (kmswStage w (t - 1)).nextEdge),
        pastStageLeftmostXDPTrace w t .sdp j = some ((P.initial j).1.id, ds) ∧
          ds.map (fun d => d.1.val) = pathEdgeList (P.initial j).2 ∧
          (j = i → pastStageLeftmostXDPTrace w t .sdp (j + 1) = none) := by
  dsimp only
  let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hg
  obtain ⟨i, hi, hfirst, htrace⟩ :=
    past_sdp_firstVisit_trace_eq_prefix w hfin hL htrans hR t hcut hg
  refine ⟨i, hi, hfirst, ?_⟩
  intro j hj
  exact htrace j hj (stageOutgoingEdgeOrder_hord w hfin hL htrans hR t P j)

end CutRecord

/-- at a cut record vertex (and a.s. at the first hit τ_r on the barrier event) the
past-stage leftmost XDP trace equals the prefix of the infinite leftmost geodesic,
whose length is the past-map XDP length; the renewal-time selection T_{m_k} is not
treated; not the paper result. -/
theorem firstHit_past_leftmost_trace_ae (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      let t := (conditionedSecondCoordinateFirstHit r p).toNat
      let w := boltzmannKMSWStream (pathCode p)
      ∃ (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
        (hL : ∀ j, 0 ≤ L w j)
        (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
        (hgL : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments)
        (hgS : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments),
        (∀ j ≥ t, (p t).1 ≤ (p j).1) →
        mapCutVertex w hfin (recordVertex w t).id ∧
        (let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hgL
         ∃ (i : ℕ) (ds : List (StageDart (kmswStage w (t - 1)).nextEdge)),
           (P.initial i).1 = recordVertex w t ∧
           (∀ j < i, (P.initial j).1 ≠ recordVertex w t) ∧
           IsLongest (P.initial i).2 ∧
           (∀ e ∈ pathEdgeList (P.initial i).2, ∃ k < t, e = act w k) ∧
           pastStageLeftmostXDPTrace w t .ldp i = some ((recordVertex w t).id, ds) ∧
           ds.map (fun d => d.1.val) = pathEdgeList (P.initial i).2 ∧
           (P.initial i).2.length =
             firstHitPastXdpLength .ldp r (stoppedMap r hr (pathCode p)) ∧
           ds.length = firstHitPastXdpLength .ldp r (stoppedMap r hr (pathCode p)) ∧
           pastStageLeftmostXDPTrace w t .ldp (i + 1) = none) ∧
        (let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hgS
         ∃ (i : ℕ) (ds : List (StageDart (kmswStage w (t - 1)).nextEdge)),
           (P.initial i).1 = recordVertex w t ∧
           (∀ j < i, (P.initial j).1 ≠ recordVertex w t) ∧
           IsShortest (P.initial i).2 ∧
           (∀ e ∈ pathEdgeList (P.initial i).2, ∃ k < t, e = act w k) ∧
           pastStageLeftmostXDPTrace w t .sdp i = some ((recordVertex w t).id, ds) ∧
           ds.map (fun d => d.1.val) = pathEdgeList (P.initial i).2 ∧
           (P.initial i).2.length =
             firstHitPastXdpLength .sdp r (stoppedMap r hr (pathCode p)) ∧
           ds.length = firstHitPastXdpLength .sdp r (stoppedMap r hr (pathCode p)) ∧
           pastStageLeftmostXDPTrace w t .sdp (i + 1) = none) := by
  filter_upwards [firstHit_leftmost_prefix_ae r hr] with p hp
  dsimp only at hp ⊢
  let t := (conditionedSecondCoordinateFirstHit r p).toNat
  let w := boltzmannKMSWStream (pathCode p)
  obtain ⟨hfin, hL, htrans, hR, hgL, hgS, hp⟩ := hp
  refine ⟨hfin, hL, htrans, hR, hgL, hgS, ?_⟩
  intro hbar
  obtain ⟨hcut, hpL, hpS⟩ := hp hbar
  refine ⟨hcut, ?_, ?_⟩
  · let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hgL
    obtain ⟨i, hi, hfirst, hgeo, hedges, hlen⟩ := hpL
    obtain ⟨k, hk, hkfirst, htrace⟩ :=
      past_ldp_trace_eq_prefix w hfin hL htrans hR t hcut hgL
    have hik : i = k := by
      apply le_antisymm
      · by_contra h
        exact hfirst k (by omega) hk
      · by_contra h
        exact hkfirst i (by omega) hi
    subst k
    obtain ⟨ds, htrace, hids, hstop⟩ := htrace i (le_refl i)
    have hlenNat : (P.initial i).2.length =
        firstHitPastXdpLength .ldp r (stoppedMap r hr (pathCode p)) :=
      ENat.natCast_inj.mp (WithBot.coe_inj.mp hlen)
    have hdsLen : ds.length =
        firstHitPastXdpLength .ldp r (stoppedMap r hr (pathCode p)) := by
      calc
        ds.length = (pathEdgeList (P.initial i).2).length := by
          rw [← hids, List.length_map]
        _ = _ := (pathEdgeList_length _).trans hlenNat
    refine ⟨i, ds, hi, hfirst, hgeo, hedges, ?_, hids, hlenNat, hdsLen, hstop rfl⟩
    change (P.initial i).1 = recordVertex w t at hi
    change pastStageLeftmostXDPTrace w t .ldp i = some ((P.initial i).1.id, ds) at htrace
    rw [hi] at htrace
    exact htrace
  · let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hgS
    obtain ⟨i, hi, hfirst, hgeo, hedges, hlen⟩ := hpS
    obtain ⟨k, hk, hkfirst, htrace⟩ :=
      past_sdp_trace_eq_prefix w hfin hL htrans hR t hcut hgS
    have hik : i = k := by
      apply le_antisymm
      · by_contra h
        exact hfirst k (by omega) hk
      · by_contra h
        exact hkfirst i (by omega) hi
    subst k
    obtain ⟨ds, htrace, hids, hstop⟩ := htrace i (le_refl i)
    have hlenNat : (P.initial i).2.length =
        firstHitPastXdpLength .sdp r (stoppedMap r hr (pathCode p)) :=
      ENat.natCast_inj.mp hlen
    have hdsLen : ds.length =
        firstHitPastXdpLength .sdp r (stoppedMap r hr (pathCode p)) := by
      calc
        ds.length = (pathEdgeList (P.initial i).2).length := by
          rw [← hids, List.length_map]
        _ = _ := (pathEdgeList_length _).trans hlenNat
    refine ⟨i, ds, hi, hfirst, hgeo, hedges, ?_, hids, hlenNat, hdsLen, hstop rfl⟩
    change (P.initial i).1 = recordVertex w t at hi
    change pastStageLeftmostXDPTrace w t .sdp i = some ((P.initial i).1.id, ds) at htrace
    rw [hi] at htrace
    exact htrace

end DirectedDistances.PaperProofs.Section4
