module

public import DirectedDistances.PaperProofs.Section4.FirstHitXDPIdentification
public import DirectedDistances.KMSW.LeftmostGeodesicCutPrefix
import DirectedDistances.KMSW.PathSpaceTransfer
import DirectedDistances.KMSW.InfiniteGeodesicAE

/-! First-hit code-graph helpers toward `lem-finite-ind`,
Leftmost paths below use the providers' first-divergence ordering.
The finite leftmost identification is separate and is not imported here. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section3
open MeasureTheory Quiver

/-- at the first hit τ_r on the barrier event, the leftmost infinite XDP geodesic visits
the cut vertex and its past piece has the past-map XDP length; the renewal-time
selection T_{m_k} and the finite leftmost identification are not treated;
not the paper result. -/
private theorem edges_before_of_endpoint_eq {w : ℕ → Fin 3} {t : ℕ}
    {b : PresentVertex w} (q : Path (⟨0⟩ : PresentVertex w) b)
    (hb : b = recordVertex w t) :
    ∀ e ∈ pathEdgeList q, ∃ k < t, e = act w k := by
  subst b
  exact (presentPath_to_record_edges_before q).2

/-- at the first hit τ_r on the barrier event, the leftmost infinite XDP geodesic visits
the cut vertex and its past piece has the past-map XDP length; the renewal-time
selection T_{m_k} and the finite leftmost identification are not treated;
not the paper result. -/
theorem record_mapCutVertex_of_barrier (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ)
    (hrec : ∀ j < t, R w t ≤ R w j - 1)
    (hbar : ∀ j ≥ t, L w t ≤ L w j) :
    mapCutVertex w hfin (recordVertex w t).id := by
  have hcut := ((mapCutVertex_first_visit_iff w hfin htrans hR hL t).2
    ⟨hrec, hbar⟩).1
  have hid : (recordVertex w t).id = activeInitial w t :=
    (CutConverse.activeInitial_eq w t).symm
  rwa [hid]

/-- at the first hit τ_r on the barrier event, the leftmost infinite XDP geodesic visits
the cut vertex and its past piece has the past-map XDP length; the renewal-time
selection T_{m_k} and the finite leftmost identification are not treated;
not the paper result. -/
theorem firstVisit_record_prefix_isLongest (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ)
    (hrec : ∀ j < t, R w t ≤ R w j - 1)
    (hbar : ∀ j ≥ t, L w t ≤ L w j)
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasLongestSegments) :
    ∃ i, (P.initial i).1 = recordVertex w t ∧
      (∀ j < i, (P.initial j).1 ≠ recordVertex w t) ∧
      IsLongest (P.initial i).2 ∧
      (∀ e ∈ pathEdgeList (P.initial i).2, ∃ k < t, e = act w k) ∧
      presentLdp (⟨0⟩ : PresentVertex w) (recordVertex w t) =
        (((P.initial i).2.length : ℕ∞) : WithBot ℕ∞) := by
  have hcut := record_mapCutVertex_of_barrier w hfin hL htrans hR t hrec hbar
  obtain ⟨i, hi, hfirst, hgeo, hlen⟩ :=
    P.firstVisit_mapCutVertex_prefix_isLongest w hfin htrans hR hL hcut hP
  exact ⟨i, hi, hfirst, hgeo, edges_before_of_endpoint_eq _ hi, hlen⟩

/-- at the first hit τ_r on the barrier event, the leftmost infinite XDP geodesic visits
the cut vertex and its past piece has the past-map XDP length; the renewal-time
selection T_{m_k} and the finite leftmost identification are not treated;
not the paper result. -/
theorem firstVisit_record_prefix_isShortest (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (hL : ∀ j, 0 ≤ L w j)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (t : ℕ)
    (hrec : ∀ j < t, R w t ≤ R w j - 1)
    (hbar : ∀ j ≥ t, L w t ≤ L w j)
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasShortestSegments) :
    ∃ i, (P.initial i).1 = recordVertex w t ∧
      (∀ j < i, (P.initial j).1 ≠ recordVertex w t) ∧
      IsShortest (P.initial i).2 ∧
      (∀ e ∈ pathEdgeList (P.initial i).2, ∃ k < t, e = act w k) ∧
      sdp (⟨0⟩ : PresentVertex w) (recordVertex w t) =
        ((P.initial i).2.length : ℕ∞) := by
  have hcut := record_mapCutVertex_of_barrier w hfin hL htrans hR t hrec hbar
  obtain ⟨i, hi, hfirst, hgeo, hlen⟩ :=
    P.firstVisit_mapCutVertex_prefix_isShortest w hfin htrans hR hL hcut hP
  exact ⟨i, hi, hfirst, hgeo, edges_before_of_endpoint_eq _ hi, hlen⟩

/-- at the first hit τ_r on the barrier event, the leftmost infinite XDP geodesic visits
the cut vertex and its past piece has the past-map XDP length; the renewal-time
selection T_{m_k} and the finite leftmost identification are not treated;
not the paper result. -/
theorem firstHit_leftmost_prefix_ae (r : ℕ) (hr : 1 ≤ r) :
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
         ∃ i, (P.initial i).1 = recordVertex w t ∧
           (∀ j < i, (P.initial j).1 ≠ recordVertex w t) ∧
           IsLongest (P.initial i).2 ∧
           (∀ e ∈ pathEdgeList (P.initial i).2, ∃ k < t, e = act w k) ∧
           (((P.initial i).2.length : ℕ∞) : WithBot ℕ∞) =
             ((firstHitPastXdpLength .ldp r (stoppedMap r hr (pathCode p)) : ℕ∞) :
               WithBot ℕ∞)) ∧
        (let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hgS
         ∃ i, (P.initial i).1 = recordVertex w t ∧
           (∀ j < i, (P.initial j).1 ≠ recordVertex w t) ∧
           IsShortest (P.initial i).2 ∧
           (∀ e ∈ pathEdgeList (P.initial i).2, ∃ k < t, e = act w k) ∧
           ((P.initial i).2.length : ℕ∞) =
             (firstHitPastXdpLength .sdp r (stoppedMap r hr (pathCode p)) : ℕ∞)) := by
  classical
  filter_upwards [conditionedVectorPathLaw_ae_legal, firstHitPastMap_finite_hit_ae r hr,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit,
    conditionedVectorPathLaw_ae_infinite_success] with p hp hhit hex hsuccess
  let t := (conditionedSecondCoordinateFirstHit r p).toNat
  let w := boltzmannKMSWStream (pathCode p)
  have hconv := firstHit_stoppedCode_conventions r p hp.1 hp.2 hhit
  have hwp : integrateCodes w = p := hconv.2.1
  obtain ⟨u, hup, hfin, htrans, hR, hL, _, _⟩ := hex
  have huw : u = w := integrateCodes_injective (hup.trans hwp.symm)
  subst u
  have hS : {n : ℕ | (∀ j < n, R w n ≤ R w j - 1) ∧
      ∀ j, n ≤ j → L w n ≤ L w j}.Infinite := by
    have himage := hsuccess.image (fun a _ b _ hab => Nat.succ.inj hab)
    apply himage.mono
    rintro n ⟨k, hk, rfl⟩
    simpa only [Set.mem_ofPred_eq, kmsw_L_eq, kmsw_R_eq, hwp,
      Nat.succ_eq_add_one] using hk
  obtain ⟨hgL, hgS⟩ := infinite_records_exists_source_extremal w hS
    (zero_mem_records_of_L_nonneg w hL)
  refine ⟨hfin, hL, htrans, hR, hgL, hgS, ?_⟩
  intro hbar
  have hbarw : ∀ j ≥ t, L w t ≤ L w j := by
    intro j hj
    simpa only [kmsw_L_eq, hwp] using hbar j hj
  have hLp (j : ℕ) : 0 ≤ (p j).1 := by
    simpa only [kmsw_L_eq, hwp] using hL j
  have hhit' : ∃ n, (p n).2 = -(r : ℤ) := by
    by_contra hnone
    simp only [conditionedSecondCoordinateFirstHit, dite_eq_right hnone,
      lt_self_iff_false] at hhit
  have hE : pathCode p ∈ boltzmannEvent r := by
    obtain ⟨n, hn⟩ := hhit'
    have hw : codeWalk (pathCode p) = p := by
      funext n
      rw [codeWalk_pathCode p hp.2 n, hp.1]
      exact sub_zero _
    exact ⟨n, by rwa [hw], fun j _ => by rw [hw]; exact hLp j⟩
  have hrec : ∀ j < t, R w t ≤ R w j - 1 := by
    have h := (firstHitPast_sink_eq_record_and_strict r hr (pathCode p) hE).2
    rwa [hconv.2.2.1] at h
  have hd := firstHitPastXdpLength_eq_shifted_limit r hr (pathCode p) hE
  rw [hconv.2.2.1] at hd
  refine ⟨record_mapCutVertex_of_barrier w hfin hL htrans hR t hrec hbarw, ?_, ?_⟩
  · let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hgL
    obtain ⟨i, hi, hfirst, hgeo, hedges, hlen⟩ :=
      firstVisit_record_prefix_isLongest w hfin hL htrans hR t hrec hbarw P
        (kmswLeftmostLdpPath_hasLongestSegments w hfin hL htrans hR 0 hgL)
    exact ⟨i, hi, hfirst, hgeo, hedges, hlen.symm.trans hd.1.symm⟩
  · let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hgS
    obtain ⟨i, hi, hfirst, hgeo, hedges, hlen⟩ :=
      firstVisit_record_prefix_isShortest w hfin hL htrans hR t hrec hbarw P
        (kmswLeftmostSdpPath_hasShortestSegments w hfin hL htrans hR 0 hgS)
    exact ⟨i, hi, hfirst, hgeo, hedges, hlen.symm.trans hd.2.symm⟩

end DirectedDistances.PaperProofs.Section4
