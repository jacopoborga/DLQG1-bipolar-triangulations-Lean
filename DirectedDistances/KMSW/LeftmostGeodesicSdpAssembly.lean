module

public import DirectedDistances.KMSW.LeftmostGeodesicAssembly
import DirectedDistances.KMSW.InfiniteGeodesicAnyStart

/-! # Compatible leftmost extensions of infinite SDP geodesics

SDP (X = S) mirror toward `def-infinite-geo` / `lem-geo-exist`
leftmost, not the source submap containment. both-mode scope is not decided. This is a
helper, not the paper result. The empty-prefix / first-step tie-in is deferred. -/

public section
namespace DirectedDistances.KMSW

open Quiver Filter

variable {w : ℕ → Fin 3}

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
@[expose] def StartsInfiniteSdpGeodesicWithPrefix (w : ℕ → Fin 3)
    (v : ℕ) (pfx : List ℕ) : Prop :=
  ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments ∧
    List.ofFn (fun i : Fin pfx.length => P.edge i.val) = pfx

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem InfinitePresentPath.startsWithSdpPrefix {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasShortestSegments) (n : ℕ) :
    StartsInfiniteSdpGeodesicWithPrefix w v
      (List.ofFn (fun i : Fin n => P.edge i.val)) := by
  refine ⟨P, hP, ?_⟩
  simp only [List.length_ofFn, Fin.val_cast]

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem StartsInfiniteSdpGeodesicWithPrefix.exists_extension {v : ℕ} {pfx : List ℕ}
    (hp : StartsInfiniteSdpGeodesicWithPrefix w v pfx) :
    ∃ e, StartsInfiniteSdpGeodesicWithPrefix w v (pfx ++ [e]) := by
  obtain ⟨P, hP, he⟩ := hp
  refine ⟨P.edge pfx.length, P, hP, ?_⟩
  simp only [List.length_append, List.length_singleton, List.ofFn_succ',
    List.concat_eq_append, Fin.val_cast, Fin.val_castSucc, Fin.val_last, he]

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem StartsInfiniteSdpGeodesicWithPrefix.extension_outgoing {v e : ℕ}
    {pfx : List ℕ} (hp : StartsInfiniteSdpGeodesicWithPrefix w v (pfx ++ [e])) :
    EdgePresent w e ∧ edgeWest w e = geodesicPrefixEnd w v pfx := by
  obtain ⟨P, _, he⟩ := hp
  have heq : List.ofFn (fun i : Fin pfx.length => P.edge i.val) ++ [P.edge pfx.length] =
      pfx ++ [e] := by
    simpa only [List.length_append, List.length_singleton, List.ofFn_succ',
      List.concat_eq_append, Fin.val_cast, Fin.val_castSucc, Fin.val_last] using he
  have hx : P.edge pfx.length = e :=
    List.singleton_inj.mp (List.append_inj_right' heq rfl)
  have hpfx := List.append_inj_left' heq rfl
  simpa only [hx, hpfx] using P.edge_outgoing pfx.length

variable (w)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

include hfin in
/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem startsInfiniteSdpGeodesicWithPrefix_extensions_finite (v : ℕ) (pfx : List ℕ) :
    {e | StartsInfiniteSdpGeodesicWithPrefix w v (pfx ++ [e])}.Finite := by
  apply (hfin (geodesicPrefixEnd w v pfx)).subset
  intro e he
  have hp := he.extension_outgoing
  exact ⟨e, kmsw_edge_allocated_by_self w e, Or.inl hp.2⟩

variable (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
@[expose] noncomputable def kmswLeftmostSdpExtension (v : ℕ) (pfx : List ℕ) : Option ℕ := by
  classical
  exact (kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx).find?
    (fun e => decide (StartsInfiniteSdpGeodesicWithPrefix w v (pfx ++ [e])))

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem kmswLeftmostSdpExtension_eq_some_iff (v : ℕ) (pfx : List ℕ) (e : ℕ) :
    kmswLeftmostSdpExtension w hfin hL htrans hR v pfx = some e ↔
      StartsInfiniteSdpGeodesicWithPrefix w v (pfx ++ [e]) ∧ ∃ as bs : List ℕ,
        kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx = as ++ e :: bs ∧
        ∀ a ∈ as, ¬StartsInfiniteSdpGeodesicWithPrefix w v (pfx ++ [a]) := by
  classical
  simp only [kmswLeftmostSdpExtension, List.find?_eq_some_iff_append,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem kmswLeftmostSdpExtension_exists (v : ℕ) (pfx : List ℕ)
    (hp : StartsInfiniteSdpGeodesicWithPrefix w v pfx) :
    ∃ e, kmswLeftmostSdpExtension w hfin hL htrans hR v pfx = some e := by
  classical
  apply Option.isSome_iff_exists.mp
  change ((kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx).find?
    (fun e => decide (StartsInfiniteSdpGeodesicWithPrefix w v (pfx ++ [e])))).isSome = true
  apply List.find?_isSome.mpr
  obtain ⟨e, he⟩ := hp.exists_extension
  exact ⟨e, (mem_kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx e).2
    he.extension_outgoing, decide_eq_true he⟩

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem kmswLeftmostSdpExtension_minimal (v : ℕ) (pfx : List ℕ) (e f : ℕ)
    (he : kmswLeftmostSdpExtension w hfin hL htrans hR v pfx = some e)
    (hf : StartsInfiniteSdpGeodesicWithPrefix w v (pfx ++ [f])) :
    (kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx).idxOf e ≤
      (kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx).idxOf f := by
  obtain ⟨he, as, bs, hs, ha⟩ :=
    (kmswLeftmostSdpExtension_eq_some_iff w hfin hL htrans hR v pfx e).1 he
  have hne : e ∉ as := fun h => ha e h he
  have hnf : f ∉ as := fun h => ha f h hf
  rw [hs, List.idxOf_append_of_notMem hne, List.idxOf_append_of_notMem hnf,
    List.idxOf_cons_self, Nat.add_zero]
  exact Nat.le_add_right _ _

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
@[expose] noncomputable def kmswLeftmostSdpPrefixes (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments) :
    ℕ → {pfx : List ℕ // StartsInfiniteSdpGeodesicWithPrefix w v pfx}
  | 0 => ⟨[], by obtain ⟨P, hP⟩ := hg; exact ⟨P, hP, rfl⟩⟩
  | n + 1 =>
    let p := kmswLeftmostSdpPrefixes v hg n
    let he := kmswLeftmostSdpExtension_exists w hfin hL htrans hR v p.val p.property
    ⟨p.val ++ [he.choose],
      ((kmswLeftmostSdpExtension_eq_some_iff w hfin hL htrans hR v p.val he.choose).1
        he.choose_spec).1⟩

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
@[expose] noncomputable def kmswLeftmostSdpEdge (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments) (n : ℕ) : ℕ :=
  (kmswLeftmostSdpExtension_exists w hfin hL htrans hR v
    (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).val
    (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).property).choose

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem kmswLeftmostSdpPrefixes_succ (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments) (n : ℕ) :
    (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg (n + 1)).val =
      (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).val ++
        [kmswLeftmostSdpEdge w hfin hL htrans hR v hg n] := rfl

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem kmswLeftmostSdpPrefixes_eq_ofFn (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments) (n : ℕ) :
    (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).val =
      List.ofFn (fun i : Fin n => kmswLeftmostSdpEdge w hfin hL htrans hR v hg i.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [kmswLeftmostSdpPrefixes_succ, ih, List.ofFn_succ']
    simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem kmswLeftmostSdpPrefixes_length (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments) (n : ℕ) :
    (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).val.length = n := by
  rw [kmswLeftmostSdpPrefixes_eq_ofFn, List.length_ofFn]

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem kmswLeftmostSdpEdge_selected (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments) (n : ℕ) :
    kmswLeftmostSdpExtension w hfin hL htrans hR v
      (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).val =
        some (kmswLeftmostSdpEdge w hfin hL htrans hR v hg n) :=
  (kmswLeftmostSdpExtension_exists w hfin hL htrans hR v
    (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).val
    (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).property).choose_spec

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
@[expose] noncomputable def kmswLeftmostSdpPrefixWitness (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments) (n : ℕ) :
    InfinitePresentPath w ⟨v⟩ :=
  (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).property.choose

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem kmswLeftmostSdpPrefixWitness_hasShortestSegments (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments) (n : ℕ) :
    (kmswLeftmostSdpPrefixWitness w hfin hL htrans hR v hg n).HasShortestSegments :=
  (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).property.choose_spec.1

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem kmswLeftmostSdpPrefixWitness_edges (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments) (n : ℕ) :
    List.ofFn (fun i : Fin n =>
      (kmswLeftmostSdpPrefixWitness w hfin hL htrans hR v hg n).edge i.val) =
      List.ofFn (fun i : Fin n => kmswLeftmostSdpEdge w hfin hL htrans hR v hg i.val) := by
  have he := (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).property.choose_spec.2
  change List.ofFn (fun i : Fin (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).val.length =>
    (kmswLeftmostSdpPrefixWitness w hfin hL htrans hR v hg n).edge i.val) =
      (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).val at he
  have he' : List.ofFn (fun i : Fin n =>
      (kmswLeftmostSdpPrefixWitness w hfin hL htrans hR v hg n).edge i.val) =
        (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).val := by
    simpa only [kmswLeftmostSdpPrefixes_length, Fin.val_cast] using he
  exact he'.trans (kmswLeftmostSdpPrefixes_eq_ofFn w hfin hL htrans hR v hg n)

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
@[expose] noncomputable def kmswLeftmostSdpPath (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments) :
    InfinitePresentPath w ⟨v⟩ where
  edge := kmswLeftmostSdpEdge w hfin hL htrans hR v hg
  initial n := (kmswLeftmostSdpPrefixWitness w hfin hL htrans hR v hg n).initial n
  prefix_length n := (kmswLeftmostSdpPrefixWitness w hfin hL htrans hR v hg n).prefix_length n
  prefix_edges n := ((kmswLeftmostSdpPrefixWitness w hfin hL htrans hR v hg n).prefix_edges n).trans
    (kmswLeftmostSdpPrefixWitness_edges w hfin hL htrans hR v hg n)

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem kmswLeftmostSdpPath_hasShortestSegments (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments) :
    (kmswLeftmostSdpPath w hfin hL htrans hR v hg).HasShortestSegments := by
  intro a b ha hab
  obtain ⟨z, q, hlen, he, hq⟩ :=
    kmswLeftmostSdpPrefixWitness_hasShortestSegments w hfin hL htrans hR v hg b a b ha hab
  refine ⟨z, q, hlen, ?_, hq⟩
  exact he.trans (congrArg (fun es : List ℕ => es.drop (a - 1))
    (kmswLeftmostSdpPrefixWitness_edges w hfin hL htrans hR v hg b))

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem kmswLeftmostSdpPath_firstDivergenceRightOf (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments)
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasShortestSegments) :
    GeodesicFirstDivergenceRightOf w hfin hL htrans hR v
      (kmswLeftmostSdpPath w hfin hL htrans hR v hg) P := by
  intro n hn
  have hs : List.ofFn (fun i : Fin n => P.edge i.val) =
      (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).val := by
    rw [kmswLeftmostSdpPrefixes_eq_ofFn]
    apply congrArg List.ofFn
    funext i
    exact (hn i.val i.isLt).symm
  have hc : StartsInfiniteSdpGeodesicWithPrefix w v
      ((kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).val ++ [P.edge n]) := by
    refine ⟨P, hP, ?_⟩
    simpa only [List.length_append, List.length_singleton, kmswLeftmostSdpPrefixes_length,
      List.ofFn_succ', List.concat_eq_append, Fin.val_cast, Fin.val_castSucc, Fin.val_last]
      using congrArg (fun es : List ℕ => es ++ [P.edge n]) hs
  have hm := kmswLeftmostSdpExtension_minimal w hfin hL htrans hR v
    (kmswLeftmostSdpPrefixes w hfin hL htrans hR v hg n).val
    (kmswLeftmostSdpEdge w hfin hL htrans hR v hg n) (P.edge n)
    (kmswLeftmostSdpEdge_selected w hfin hL htrans hR v hg n) hc
  simpa only [kmswLeftmostSdpPrefixes_eq_ofFn, kmswLeftmostSdpPath] using hm

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem kmswLeftmostSdpPath_unique_edge (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments)
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasShortestSegments)
    (hleft : ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasShortestSegments →
      GeodesicFirstDivergenceRightOf w hfin hL htrans hR v P Q) :
    P.edge = (kmswLeftmostSdpPath w hfin hL htrans hR v hg).edge := by
  apply GeodesicFirstDivergenceRightOf.antisymm w hfin hL htrans hR v P
    (kmswLeftmostSdpPath w hfin hL htrans hR v hg)
  · exact hleft _ (kmswLeftmostSdpPath_hasShortestSegments w hfin hL htrans hR v hg)
  · exact kmswLeftmostSdpPath_firstDivergenceRightOf w hfin hL htrans hR v hg P hP

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem existsUnique_firstDivergenceLeftmostSdp_edge (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments) :
    ∃! edges : ℕ → ℕ, ∃ P : InfinitePresentPath w ⟨v⟩,
      P.HasShortestSegments ∧ P.edge = edges ∧
      ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasShortestSegments →
        GeodesicFirstDivergenceRightOf w hfin hL htrans hR v P Q := by
  refine ⟨(kmswLeftmostSdpPath w hfin hL htrans hR v hg).edge, ?_, ?_⟩
  · exact ⟨kmswLeftmostSdpPath w hfin hL htrans hR v hg,
      kmswLeftmostSdpPath_hasShortestSegments w hfin hL htrans hR v hg, rfl,
      kmswLeftmostSdpPath_firstDivergenceRightOf w hfin hL htrans hR v hg⟩
  · rintro edges ⟨P, hP, he, hleft⟩
    exact he.symm.trans (kmswLeftmostSdpPath_unique_edge w hfin hL htrans hR v hg P hP hleft)

/-- SDP (X = S) mirror toward def-infinite-geo / lem-geo-exist
not the source submap containment; both-mode scope is not decided; helper, not the paper result. -/
theorem pitmanCodes_ae_exists_unique_firstDivergenceLeftmostSdp :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
      ∃ (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
        (hL : ∀ j, 0 ≤ L w j) (ht : Tendsto (L w) atTop atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a),
        ∀ v, ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments ∧
          (∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasShortestSegments →
            GeodesicFirstDivergenceRightOf w hf hL ht hR v P Q) ∧
          ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasShortestSegments →
            (∀ S : InfinitePresentPath w ⟨v⟩, S.HasShortestSegments →
              GeodesicFirstDivergenceRightOf w hf hL ht hR v Q S) → Q.edge = P.edge := by
  filter_upwards [pitmanCodes_ae_infinite_mapCutVertices,
    pitmanCodes_ae_exists_allocated_infinite_extremal] with ω hmap hgeo
  obtain ⟨hf, ht, hR, hL, _⟩ := hmap
  let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
  have halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex :=
    fun v => kmsw_vertex_allocated_of_finite_incidence w hf v
  refine ⟨hf, hL, ht, hR, fun v => ?_⟩
  have hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasShortestSegments :=
    (hgeo ⟨v⟩ (halloc v)).2
  exact ⟨kmswLeftmostSdpPath w hf hL ht hR v hg,
    kmswLeftmostSdpPath_hasShortestSegments w hf hL ht hR v hg,
    kmswLeftmostSdpPath_firstDivergenceRightOf w hf hL ht hR v hg,
    fun Q hQ hleft => kmswLeftmostSdpPath_unique_edge w hf hL ht hR v hg Q hQ hleft⟩

end DirectedDistances.KMSW
