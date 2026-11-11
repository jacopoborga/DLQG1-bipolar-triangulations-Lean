module

public import DirectedDistances.KMSW.LeftmostGeodesicSubmap
public import DirectedDistances.KMSW.LeftmostGeodesicSdpPlanar

/- # SDP comparison between the leftmost and rightmost paths

SDP (X = S) helpers toward `def-infinite-geo` / `lem-geo-exist`
The existing `InBetweenLeftmostRightmost` predicate compares outgoing edge IDs
at shared departures. Its equivalence with planar submap containment remains -/

public section
namespace DirectedDistances.KMSW

open Quiver Filter

variable (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
helper, not the paper result. -/
theorem kmswLeftmostSdpPath_inBetweenLeftmostRightmost (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments)
    (Q : InfinitePresentPath w ⟨v⟩) (hQ : Q.HasShortestSegments) :
    InBetweenLeftmostRightmost w hfin hL htrans hR v
      (kmswLeftmostSdpPath w hfin hL htrans hR v hg)
      (kmswRightmostPath w hfin hL htrans hR v) Q := by
  exact ⟨kmswLeftmostSdpPath_sharedDeparturesRightOf w hfin hL htrans hR v hg Q hQ,
    kmswRightmostPath_sharedDeparturesLeftOf w hfin hL htrans hR v Q⟩


/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
helper, not the paper result. -/
theorem pitmanCodes_ae_exists_unique_inBetweenLeftmostRightmostSdp :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
      ∃ (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
        (hL : ∀ j, 0 ≤ L w j) (ht : Tendsto (L w) atTop atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a),
        ∀ v, ∃! es : ℕ → ℕ,
          ∃ P : InfinitePresentPath w ⟨v⟩, P.edge = es ∧ P.HasShortestSegments ∧
            ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasShortestSegments →
              InBetweenLeftmostRightmost w hf hL ht hR v P
                (kmswRightmostPath w hf hL ht hR v) Q := by
  filter_upwards [pitmanCodes_ae_exists_unique_sharedDepartureLeftmostSdp] with ω h
  obtain ⟨hf, hL, ht, hR, hall⟩ := h
  refine ⟨hf, hL, ht, hR, fun v => ?_⟩
  obtain ⟨P, hP, hleft, huniq⟩ := hall v
  refine ⟨P.edge, ⟨P, rfl, hP, fun Q hQ => ?_⟩, ?_⟩
  · exact ⟨hleft Q hQ, kmswRightmostPath_sharedDeparturesLeftOf _ hf hL ht hR v Q⟩
  · rintro es ⟨Q, he, hQ, hbetween⟩
    exact he.symm.trans (huniq Q hQ (fun S hS => (hbetween S hS).1))

end DirectedDistances.KMSW
