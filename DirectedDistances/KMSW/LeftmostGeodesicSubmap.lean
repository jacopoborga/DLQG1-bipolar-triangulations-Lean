module

public import DirectedDistances.KMSW.LeftmostGeodesicPlanar
public import DirectedDistances.KMSW.RightmostCoalescenceM0

/-! # Between the leftmost geodesic and the rightmost directed path

Helpers for `def-infinite-geo` and `lem-geo-exist`,

The source says that every competing infinite LDP geodesic is contained in
the submap weakly right of the leftmost geodesic and weakly left of the
rightmost directed path from the same start, including their boundary edges
and vertices. Here `InBetweenLeftmostRightmost` is a combinatorial
rotation-order rendering: it compares outgoing edge IDs at every shared
departure, allowing different visit indices and equality of edges. The
planar-region formulation itself is not formalized. No equivalence between
this local predicate and containment in a planar submap is asserted.

Uniqueness is stated for edge streams, retaining parallel-edge identities;
the auxiliary finite-prefix witnesses in `InfinitePresentPath` are not part
of that uniqueness carrier. The rightmost path need not be an LDP geodesic. -/

public section
namespace DirectedDistances.KMSW

open Quiver Filter

variable (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)

/-- No edge ID occurs twice in the geometric outgoing order -/
theorem kmswOutgoingEdgesLeftToRight_nodup (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) :
    (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv).Nodup := by
  classical
  unfold kmswOutgoingEdgesLeftToRight
  split
  · rw [List.nodup_reverse]
    exact (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose_spec.1
  · rename_i h
    rw [List.nodup_reverse]
    exact (kmsw_nonzero_outgoing_enumeration w hfin hL hR v hv h).choose_spec.choose_spec.choose_spec.1

/-- Every present outgoing edge precedes the rightmost outgoing edge in the -/
theorem kmswRightmostOutgoingEdge_maximal
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v e : ℕ) (he : EdgePresent w e) (hv : edgeWest w e = v) :
    (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v (halloc v)).idxOf e ≤
      (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v (halloc v)).idxOf
        (kmswRightmostOutgoingEdge w hfin hL htrans hR halloc v) := by
  have hm := (mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v
    (halloc v) e).2 ⟨he, hv⟩
  have hlt := List.idxOf_lt_length_of_mem hm
  unfold kmswRightmostOutgoingEdge
  rw [List.getLast_eq_getElem,
    (kmswOutgoingEdgesLeftToRight_nodup w hfin hL htrans hR v (halloc v)).idxOf_getElem]
  omega

/-- `Q` departs weakly left of `P` at every shared vertex, including the
start. This reverses the two paths and departure indices in the weakly-right -/
@[expose] def GeodesicSharedDeparturesLeftOf (v : ℕ)
    (P Q : InfinitePresentPath w ⟨v⟩) : Prop :=
  ∀ m n, (P.initial m).1 = (Q.initial n).1 →
    SharedDepartureWeaklyRight w hfin hL htrans hR Q P n m

/-- Every infinite present directed path departs weakly left of the
rightmost path at each shared vertex. Longest-segment optimality is not -/
theorem kmswRightmostPath_sharedDeparturesLeftOf (v : ℕ)
    (Q : InfinitePresentPath w ⟨v⟩) :
    GeodesicSharedDeparturesLeftOf w hfin hL htrans hR v
      (kmswRightmostPath w hfin hL htrans hR v) Q := by
  intro m n hs
  refine ⟨hs.symm, ?_⟩
  have hend : geodesicPrefixEnd w v (List.ofFn (fun i : Fin n => Q.edge i.val)) =
      kmswRightmostOrbit w hfin hL htrans hR v m := by
    rw [← Q.prefix_edges, pathEdgeList_endpoint]
    exact congrArg PresentVertex.id hs.symm
  have he := Q.edge_outgoing n
  rw [hend] at he
  dsimp only [kmswPrefixOutgoingEdges]
  simp only [hend]
  exact kmswRightmostOutgoingEdge_maximal w hfin hL htrans hR
    (kmsw_vertex_allocated_of_finite_incidence w hfin) _ _ he.1 he.2

/-- `Q` is weakly right of `P` and weakly left of `R` at every shared
departure. This is the rotation-order rendering of the source's submap
wording, not a planar-region containment predicate (`def-infinite-geo`, -/
@[expose] def InBetweenLeftmostRightmost (v : ℕ)
    (P R Q : InfinitePresentPath w ⟨v⟩) : Prop :=
  GeodesicSharedDeparturesRightOf w hfin hL htrans hR v P Q ∧
    GeodesicSharedDeparturesLeftOf w hfin hL htrans hR v R Q

/-- Every infinite LDP geodesic is between the constructed leftmost
geodesic and the rightmost directed path in shared-departure rotation -/
theorem kmswLeftmostLdpPath_inBetweenLeftmostRightmost (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments)
    (Q : InfinitePresentPath w ⟨v⟩) (hQ : Q.HasLongestSegments) :
    InBetweenLeftmostRightmost w hfin hL htrans hR v
      (kmswLeftmostLdpPath w hfin hL htrans hR v hg)
      (kmswRightmostPath w hfin hL htrans hR v) Q := by
  exact ⟨kmswLeftmostLdpPath_sharedDeparturesRightOf w hfin hL htrans hR v hg Q hQ,
    kmswRightmostPath_sharedDeparturesLeftOf w hfin hL htrans hR v Q⟩

/-- Almost surely for the UIQBOT Pitman code, simultaneously at every
vertex there is a unique infinite LDP geodesic edge stream such that all
infinite LDP geodesics from that vertex are between it and the rightmost
directed path in shared-departure rotation order. Every vertex ID is
allocated under the displayed finite-incidence hypothesis. This is the
combinatorial rendering of `lem-geo-exist` and the leftmost clause of
`def-infinite-geo`, not the unformalized planar-region formulation -/
theorem pitmanCodes_ae_exists_unique_inBetweenLeftmostRightmostLdp :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
      ∃ (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
        (hL : ∀ j, 0 ≤ L w j) (ht : Tendsto (L w) atTop atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a),
        ∀ v, ∃! es : ℕ → ℕ,
          ∃ P : InfinitePresentPath w ⟨v⟩, P.edge = es ∧ P.HasLongestSegments ∧
            ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasLongestSegments →
              InBetweenLeftmostRightmost w hf hL ht hR v P
                (kmswRightmostPath w hf hL ht hR v) Q := by
  filter_upwards [pitmanCodes_ae_exists_unique_sharedDepartureLeftmostLdp] with ω h
  obtain ⟨hf, hL, ht, hR, hall⟩ := h
  refine ⟨hf, hL, ht, hR, fun v => ?_⟩
  obtain ⟨P, hP, hleft, huniq⟩ := hall v
  refine ⟨P.edge, ⟨P, rfl, hP, fun Q hQ => ?_⟩, ?_⟩
  · exact ⟨hleft Q hQ, kmswRightmostPath_sharedDeparturesLeftOf _ hf hL ht hR v Q⟩
  · rintro es ⟨Q, he, hQ, hbetween⟩
    exact he.symm.trans (huniq Q hQ (fun S hS => (hbetween S hS).1))

end DirectedDistances.KMSW
