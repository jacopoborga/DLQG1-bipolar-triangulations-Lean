module

public import DirectedDistances.KMSW.LeftmostGeodesicUIQBOT

/-! # Compatible leftmost extensions of infinite LDP geodesics

Proved: an edge-stream-level, first-divergence lexicographically leftmost
infinite LDP geodesic from every vertex, unique among geodesics with the
first-divergence property. NOT proved here: comparison at later shared
departures (see LeftmostGeodesicPlanar), a rightmost directed path and the
planar submap construction, hence containment in the submap between the path
and the rightmost path; `def-infinite-geo`'s leftmost clause and `lem-geo-exist`
in full are not established here. -/

public section
namespace DirectedDistances.KMSW

open Quiver Filter

variable {w : ℕ → Fin 3}

/-- Endpoint read from an edge prefix, retaining the start for the empty prefix -/
@[expose] def geodesicPrefixEnd (w : ℕ → Fin 3) (v : ℕ) (pfx : List ℕ) : ℕ :=
  pfx.getLast?.elim v (edgeEast w)

/-- The edge list determines the terminal vertex of an actual finite path -/
theorem pathEdgeList_endpoint {x y : PresentVertex w} (p : Path x y) :
    geodesicPrefixEnd w x.id (pathEdgeList p) = y.id := by
  cases p with
  | nil => rfl
  | cons p e =>
    simpa only [geodesicPrefixEnd, pathEdgeList, List.getLast?_append,
      List.getLast?_singleton, Option.some_or, Option.elim_some] using e.property.2.2

/-- A prefix is eligible precisely when some infinite longest-segment path -/
@[expose] def StartsInfiniteLdpGeodesicWithPrefix (w : ℕ → Fin 3)
    (v : ℕ) (pfx : List ℕ) : Prop :=
  ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments ∧
    List.ofFn (fun i : Fin pfx.length => P.edge i.val) = pfx

/-- Every initial edge list of a geodesic is an eligible prefix -/
theorem InfinitePresentPath.startsWithPrefix {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasLongestSegments) (n : ℕ) :
    StartsInfiniteLdpGeodesicWithPrefix w v
      (List.ofFn (fun i : Fin n => P.edge i.val)) := by
  refine ⟨P, hP, ?_⟩
  simp only [List.length_ofFn, Fin.val_cast]

/-- The next edge of a path starts at the endpoint of its preceding prefix -/
theorem InfinitePresentPath.edge_outgoing {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (n : ℕ) :
    EdgePresent w (P.edge n) ∧ edgeWest w (P.edge n) =
      geodesicPrefixEnd w v (List.ofFn (fun i : Fin n => P.edge i.val)) := by
  have hlen := P.prefix_length (n + 1)
  have hedges := P.prefix_edges (n + 1)
  generalize hq : P.initial (n + 1) = zq at hlen hedges
  rcases zq with ⟨z, q⟩
  dsimp only at hlen hedges
  cases q with
  | nil => simp only [Path.length_nil] at hlen; omega
  | cons q e =>
    have heq : pathEdgeList q ++ [e.val] =
        List.ofFn (fun i : Fin n => P.edge i.val) ++ [P.edge n] := by
      simpa only [pathEdgeList, List.ofFn_succ', List.concat_eq_append,
        Fin.val_castSucc, Fin.val_last] using hedges
    have he : e.val = P.edge n := by
      have h := List.append_inj_right' heq rfl
      exact List.singleton_inj.mp h
    have hp := List.append_inj_left' heq rfl
    rw [← he]
    refine ⟨e.property.1, ?_⟩
    rw [← hp, pathEdgeList_endpoint]
    exact e.property.2.1

/-- Every eligible finite prefix has an eligible one-edge extension, supplied -/
theorem StartsInfiniteLdpGeodesicWithPrefix.exists_extension {v : ℕ} {pfx : List ℕ}
    (hp : StartsInfiniteLdpGeodesicWithPrefix w v pfx) :
    ∃ e, StartsInfiniteLdpGeodesicWithPrefix w v (pfx ++ [e]) := by
  obtain ⟨P, hP, he⟩ := hp
  refine ⟨P.edge pfx.length, P, hP, ?_⟩
  simp only [List.length_append, List.length_singleton, List.ofFn_succ',
    List.concat_eq_append, Fin.val_cast, Fin.val_castSucc, Fin.val_last, he]

/-- An eligible extension is an outgoing present edge at the prefix endpoint -/
theorem StartsInfiniteLdpGeodesicWithPrefix.extension_outgoing {v e : ℕ}
    {pfx : List ℕ} (hp : StartsInfiniteLdpGeodesicWithPrefix w v (pfx ++ [e])) :
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

/-- Every finite prefix of the tail is realized from the east endpoint of -/
theorem InfinitePresentPath.exists_tail_initial {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (n : ℕ) :
    ∃ q : Path (⟨edgeEast w (P.edge 0)⟩ : PresentVertex w) (P.initial (n + 1)).1,
      q.length = n ∧ pathEdgeList q = List.ofFn (fun i : Fin n => P.edge (i.val + 1)) := by
  obtain ⟨z, p, q, hpq, hp⟩ := (P.initial (n + 1)).2.exists_eq_comp_of_le_length
    (show 1 ≤ (P.initial (n + 1)).2.length by rw [P.prefix_length]; omega)
  have hlist : pathEdgeList p ++ pathEdgeList q =
      [P.edge 0] ++ List.ofFn (fun i : Fin n => P.edge (i.val + 1)) := by
    rw [← pathEdgeList_comp, ← hpq, P.prefix_edges, List.ofFn_succ]
    rfl
  have hpre : pathEdgeList p = [P.edge 0] :=
    List.append_inj_left hlist (by rw [pathEdgeList_length, hp]; rfl)
  have hsuf : pathEdgeList q = List.ofFn (fun i : Fin n => P.edge (i.val + 1)) :=
    List.append_inj_right hlist (by rw [pathEdgeList_length, hp]; rfl)
  have hz := pathEdgeList_endpoint p
  rw [hpre] at hz
  change edgeEast w (P.edge 0) = z.id at hz
  have hzz : z = (⟨edgeEast w (P.edge 0)⟩ : PresentVertex w) := by
    cases z
    congr 1
    exact hz.symm
  subst z
  refine ⟨q, ?_, hsuf⟩
  have hlen := P.prefix_length (n + 1)
  rw [hpq, Path.length_comp, hp] at hlen
  omega

/-- Remove the first edge, starting the resulting path at that edge's east -/
@[expose] noncomputable def InfinitePresentPath.tail {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) :
    InfinitePresentPath w ⟨edgeEast w (P.edge 0)⟩ where
  edge n := P.edge (n + 1)
  initial n := ⟨(P.initial (n + 1)).1, (P.exists_tail_initial n).choose⟩
  prefix_length n := (P.exists_tail_initial n).choose_spec.1
  prefix_edges n := (P.exists_tail_initial n).choose_spec.2

/-- Deleting the first edge of an infinite LDP geodesic preserves all
longest-segment conditions. No unrestricted converse is used -/
theorem InfinitePresentPath.tail_hasLongestSegments {v : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasLongestSegments) :
    P.tail.HasLongestSegments := by
  intro a b ha hab
  obtain ⟨z, q, hlen, he, hq⟩ := hP (a + 1) (b + 1) (by omega) (by omega)
  have hlen' : q.length = b + 1 - a := by
    simpa only [Nat.add_sub_add_right] using hlen
  refine ⟨z, q, hlen', ?_, hq⟩
  change pathEdgeList q = (List.ofFn (fun i : Fin b => P.edge (i.val + 1))).drop (a - 1)
  rw [List.ofFn_succ] at he
  simpa only [Nat.add_sub_cancel, Fin.val_succ,
    List.drop_cons (by omega : 0 < a)] using he

/-- Equal finite edge prefixes have equal terminal vertices, independently
of the auxiliary path witnesses (`def-infinite-geo`, -/
theorem InfinitePresentPath.initial_vertex_eq_of_prefix_eq {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) (n : ℕ)
    (he : List.ofFn (fun i : Fin n => P.edge i.val) =
      List.ofFn (fun i : Fin n => Q.edge i.val)) :
    (P.initial n).1 = (Q.initial n).1 := by
  have hp := pathEdgeList_endpoint (P.initial n).2
  have hq := pathEdgeList_endpoint (Q.initial n).2
  rw [P.prefix_edges] at hp
  rw [Q.prefix_edges] at hq
  have hi : (P.initial n).1.id = (Q.initial n).1.id :=
    hp.symm.trans ((congrArg (geodesicPrefixEnd w v) he).trans hq)
  exact congrArg (fun i : ℕ => (⟨i⟩ : PresentVertex w)) hi

/-- Longest-segment optimality depends only on the edge stream, not on
which finite path witnesses are stored in `initial` -/
theorem InfinitePresentPath.hasLongestSegments_of_edge_eq {v : ℕ}
    (P Q : InfinitePresentPath w ⟨v⟩) (he : P.edge = Q.edge)
    (hP : P.HasLongestSegments) : Q.HasLongestSegments := by
  intro a b ha hab
  have hpfx : List.ofFn (fun i : Fin b => P.edge i.val) =
      List.ofFn (fun i : Fin b => Q.edge i.val) :=
    congrArg (fun f : ℕ → ℕ => List.ofFn (fun i : Fin b => f i.val)) he
  have hv := P.initial_vertex_eq_of_prefix_eq Q b hpfx
  rw [← hv]
  obtain ⟨z, q, hlen, hq, hlongest⟩ := hP a b ha hab
  exact ⟨z, q, hlen, hq.trans (congrArg (fun es : List ℕ => es.drop (a - 1)) hpfx), hlongest⟩

/-- A geodesic whose first edge is `e` has a geodesic tail starting at
`edgeEast w e`, with the exact shifted edge IDs. In particular this applies
to a witness starting with the selected edge -/
theorem InfinitePresentPath.exists_geodesic_tail {v e : ℕ}
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasLongestSegments) (he : P.edge 0 = e) :
    ∃ Q : InfinitePresentPath w ⟨edgeEast w e⟩, Q.HasLongestSegments ∧
      ∀ n, Q.edge n = P.edge (n + 1) := by
  subst e
  exact ⟨P.tail, P.tail_hasLongestSegments hP, fun _ => rfl⟩

variable (w)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

include hfin in
/-- Eligible extensions form a finite set, since they are incident at the -/
theorem startsInfiniteLdpGeodesicWithPrefix_extensions_finite (v : ℕ) (pfx : List ℕ) :
    {e | StartsInfiniteLdpGeodesicWithPrefix w v (pfx ++ [e])}.Finite := by
  apply (hfin (geodesicPrefixEnd w v pfx)).subset
  intro e he
  have hp := he.extension_outgoing
  exact ⟨e, kmsw_edge_allocated_by_self w e, Or.inl hp.2⟩

variable (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)

/-- The boundary-anchored outgoing order at the endpoint of a finite prefix -/
@[expose] noncomputable def kmswPrefixOutgoingEdges (v : ℕ) (pfx : List ℕ) : List ℕ :=
  kmswOutgoingEdgesLeftToRight w hfin hL htrans hR (geodesicPrefixEnd w v pfx)
    (kmsw_vertex_allocated_of_finite_incidence w hfin _)

/-- Membership in the prefix endpoint's order is directed incidence -/
theorem mem_kmswPrefixOutgoingEdges (v : ℕ) (pfx : List ℕ) (e : ℕ) :
    e ∈ kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx ↔
      EdgePresent w e ∧ edgeWest w e = geodesicPrefixEnd w v pfx :=
  mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR _ _ e

/-- Select the first edge whose addition preserves realization of the entire
Toward lem-geo-exist; partial: leftmost here means
first-divergence-lexicographically leftmost, not the source's submap
containment. -/
@[expose] noncomputable def kmswLeftmostLdpExtension(v : ℕ) (pfx : List ℕ) : Option ℕ := by
  classical
  exact (kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx).find?
    (fun e => decide (StartsInfiniteLdpGeodesicWithPrefix w v (pfx ++ [e])))

/-- A successful search is eligible, with no eligible edge preceding it -/
theorem kmswLeftmostLdpExtension_eq_some_iff (v : ℕ) (pfx : List ℕ) (e : ℕ) :
    kmswLeftmostLdpExtension w hfin hL htrans hR v pfx = some e ↔
      StartsInfiniteLdpGeodesicWithPrefix w v (pfx ++ [e]) ∧ ∃ as bs : List ℕ,
        kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx = as ++ e :: bs ∧
        ∀ a ∈ as, ¬StartsInfiniteLdpGeodesicWithPrefix w v (pfx ++ [a]) := by
  classical
  simp only [kmswLeftmostLdpExtension, List.find?_eq_some_iff_append,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]

/-- Every eligible prefix has a successful leftmost extension search -/
theorem kmswLeftmostLdpExtension_exists (v : ℕ) (pfx : List ℕ)
    (hp : StartsInfiniteLdpGeodesicWithPrefix w v pfx) :
    ∃ e, kmswLeftmostLdpExtension w hfin hL htrans hR v pfx = some e := by
  classical
  apply Option.isSome_iff_exists.mp
  change ((kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx).find?
    (fun e => decide (StartsInfiniteLdpGeodesicWithPrefix w v (pfx ++ [e])))).isSome = true
  apply List.find?_isSome.mpr
  obtain ⟨e, he⟩ := hp.exists_extension
  exact ⟨e, (mem_kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx e).2
    he.extension_outgoing, decide_eq_true he⟩

/-- The selected compatible extension precedes any other eligible extension -/
theorem kmswLeftmostLdpExtension_minimal (v : ℕ) (pfx : List ℕ) (e f : ℕ)
    (he : kmswLeftmostLdpExtension w hfin hL htrans hR v pfx = some e)
    (hf : StartsInfiniteLdpGeodesicWithPrefix w v (pfx ++ [f])) :
    (kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx).idxOf e ≤
      (kmswPrefixOutgoingEdges w hfin hL htrans hR v pfx).idxOf f := by
  obtain ⟨he, as, bs, hs, ha⟩ :=
    (kmswLeftmostLdpExtension_eq_some_iff w hfin hL htrans hR v pfx e).1 he
  have hne : e ∉ as := fun h => ha e h he
  have hnf : f ∉ as := fun h => ha f h hf
  rw [hs, List.idxOf_append_of_notMem hne, List.idxOf_append_of_notMem hnf,
    List.idxOf_cons_self, Nat.add_zero]
  exact Nat.le_add_right _ _

/-- Compatible prefixes selected recursively in the geometric outgoing order.
Every state includes an actual infinite geodesic witness -/
@[expose] noncomputable def kmswLeftmostLdpPrefixes (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) :
    ℕ → {pfx : List ℕ // StartsInfiniteLdpGeodesicWithPrefix w v pfx}
  | 0 => ⟨[], by obtain ⟨P, hP⟩ := hg; exact ⟨P, hP, rfl⟩⟩
  | n + 1 =>
    let p := kmswLeftmostLdpPrefixes v hg n
    let he := kmswLeftmostLdpExtension_exists w hfin hL htrans hR v p.val p.property
    ⟨p.val ++ [he.choose],
      ((kmswLeftmostLdpExtension_eq_some_iff w hfin hL htrans hR v p.val he.choose).1
        he.choose_spec).1⟩

/-- The next edge is selected by the compatible finite search, with no -/
@[expose] noncomputable def kmswLeftmostLdpEdge (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) : ℕ :=
  (kmswLeftmostLdpExtension_exists w hfin hL htrans hR v
    (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).val
    (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).property).choose

/-- Successive selected prefixes add exactly the next selected edge -/
theorem kmswLeftmostLdpPrefixes_succ (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg (n + 1)).val =
      (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).val ++
        [kmswLeftmostLdpEdge w hfin hL htrans hR v hg n] := rfl

/-- The selected stream has precisely the recursively selected prefixes -/
theorem kmswLeftmostLdpPrefixes_eq_ofFn (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).val =
      List.ofFn (fun i : Fin n => kmswLeftmostLdpEdge w hfin hL htrans hR v hg i.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [kmswLeftmostLdpPrefixes_succ, ih, List.ofFn_succ']
    simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

/-- The selected prefix at time `n` has length `n` -/
theorem kmswLeftmostLdpPrefixes_length (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).val.length = n := by
  rw [kmswLeftmostLdpPrefixes_eq_ofFn, List.length_ofFn]

/-- Each selected edge is exactly the successful compatible extension search -/
theorem kmswLeftmostLdpEdge_selected (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    kmswLeftmostLdpExtension w hfin hL htrans hR v
      (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).val =
        some (kmswLeftmostLdpEdge w hfin hL htrans hR v hg n) :=
  (kmswLeftmostLdpExtension_exists w hfin hL htrans hR v
    (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).val
    (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).property).choose_spec

/-- An infinite geodesic realizing the selected prefix at time `n` -/
@[expose] noncomputable def kmswLeftmostLdpPrefixWitness (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    InfinitePresentPath w ⟨v⟩ :=
  (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).property.choose

/-- The prefix witness is an infinite longest-segment geodesic -/
theorem kmswLeftmostLdpPrefixWitness_hasLongestSegments (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    (kmswLeftmostLdpPrefixWitness w hfin hL htrans hR v hg n).HasLongestSegments :=
  (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).property.choose_spec.1

/-- The witness agrees with the selected stream through its specified prefix -/
theorem kmswLeftmostLdpPrefixWitness_edges (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) (n : ℕ) :
    List.ofFn (fun i : Fin n => (kmswLeftmostLdpPrefixWitness w hfin hL htrans hR v hg n).edge i.val) =
      List.ofFn (fun i : Fin n => kmswLeftmostLdpEdge w hfin hL htrans hR v hg i.val) := by
  have he := (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).property.choose_spec.2
  change List.ofFn (fun i : Fin (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).val.length =>
    (kmswLeftmostLdpPrefixWitness w hfin hL htrans hR v hg n).edge i.val) =
      (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).val at he
  have he' : List.ofFn (fun i : Fin n =>
      (kmswLeftmostLdpPrefixWitness w hfin hL htrans hR v hg n).edge i.val) =
        (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).val := by
    simpa only [kmswLeftmostLdpPrefixes_length, Fin.val_cast] using he
  exact he'.trans (kmswLeftmostLdpPrefixes_eq_ofFn w hfin hL htrans hR v hg n)

/-- The limit of compatible prefixes is a genuine present-edge path
Toward lem-geo-exist; partial: leftmost here means
first-divergence-lexicographically leftmost, not the source's submap
containment. -/
@[expose] noncomputable def kmswLeftmostLdpPath(v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) :
    InfinitePresentPath w ⟨v⟩ where
  edge := kmswLeftmostLdpEdge w hfin hL htrans hR v hg
  initial n := (kmswLeftmostLdpPrefixWitness w hfin hL htrans hR v hg n).initial n
  prefix_length n := (kmswLeftmostLdpPrefixWitness w hfin hL htrans hR v hg n).prefix_length n
  prefix_edges n := ((kmswLeftmostLdpPrefixWitness w hfin hL htrans hR v hg n).prefix_edges n).trans
    (kmswLeftmostLdpPrefixWitness_edges w hfin hL htrans hR v hg n)

/-- Every finite segment of the limit is a longest segment of a geodesic
witness for a sufficiently long prefix -/
theorem kmswLeftmostLdpPath_hasLongestSegments (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) :
    (kmswLeftmostLdpPath w hfin hL htrans hR v hg).HasLongestSegments := by
  intro a b ha hab
  obtain ⟨z, q, hlen, he, hq⟩ :=
    kmswLeftmostLdpPrefixWitness_hasLongestSegments w hfin hL htrans hR v hg b a b ha hab
  refine ⟨z, q, hlen, ?_, hq⟩
  exact he.trans (congrArg (fun es : List ℕ => es.drop (a - 1))
    (kmswLeftmostLdpPrefixWitness_edges w hfin hL htrans hR v hg b))

/-- First-divergence comparison in the boundary-anchored outgoing order.
This predicate records an edge-order comparison, not the unconstructed
submap containment of `def-infinite-geo` -/
@[expose] def GeodesicFirstDivergenceRightOf (v : ℕ)
    (L P : InfinitePresentPath w ⟨v⟩) : Prop :=
  ∀ n, (∀ i, i < n → L.edge i = P.edge i) →
    (kmswPrefixOutgoingEdges w hfin hL htrans hR v
      (List.ofFn (fun i : Fin n => L.edge i.val))).idxOf (L.edge n) ≤
    (kmswPrefixOutgoingEdges w hfin hL htrans hR v
      (List.ofFn (fun i : Fin n => L.edge i.val))).idxOf (P.edge n)

/-- Every competing infinite LDP geodesic is weakly to the right at the
No submap-containment conclusion is asserted. -/
theorem kmswLeftmostLdpPath_firstDivergenceRightOf (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments)
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasLongestSegments) :
    GeodesicFirstDivergenceRightOf w hfin hL htrans hR v
      (kmswLeftmostLdpPath w hfin hL htrans hR v hg) P := by
  intro n hn
  have hs : List.ofFn (fun i : Fin n => P.edge i.val) =
      (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).val := by
    rw [kmswLeftmostLdpPrefixes_eq_ofFn]
    apply congrArg List.ofFn
    funext i
    exact (hn i.val i.isLt).symm
  have hc : StartsInfiniteLdpGeodesicWithPrefix w v
      ((kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).val ++ [P.edge n]) := by
    refine ⟨P, hP, ?_⟩
    simpa only [List.length_append, List.length_singleton, kmswLeftmostLdpPrefixes_length,
      List.ofFn_succ', List.concat_eq_append, Fin.val_cast, Fin.val_castSucc, Fin.val_last]
      using congrArg (fun es : List ℕ => es ++ [P.edge n]) hs
  have hm := kmswLeftmostLdpExtension_minimal w hfin hL htrans hR v
    (kmswLeftmostLdpPrefixes w hfin hL htrans hR v hg n).val
    (kmswLeftmostLdpEdge w hfin hL htrans hR v hg n) (P.edge n)
    (kmswLeftmostLdpEdge_selected w hfin hL htrans hR v hg n) hc
  simpa only [kmswLeftmostLdpPrefixes_eq_ofFn, kmswLeftmostLdpPath] using hm

/-- Mutual first-divergence comparison forces equality of edge streams.
The proof retains parallel-edge identities and does not equate auxiliary -/
theorem GeodesicFirstDivergenceRightOf.antisymm (v : ℕ)
    (P Q : InfinitePresentPath w ⟨v⟩)
    (hPQ : GeodesicFirstDivergenceRightOf w hfin hL htrans hR v P Q)
    (hQP : GeodesicFirstDivergenceRightOf w hfin hL htrans hR v Q P) :
    P.edge = Q.edge := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hs : List.ofFn (fun i : Fin n => Q.edge i.val) =
        List.ofFn (fun i : Fin n => P.edge i.val) := by
      apply congrArg List.ofFn
      funext i
      exact (ih i.val i.isLt).symm
    have hpq := hPQ n ih
    have hqp := hQP n (fun i hi => (ih i hi).symm)
    rw [hs] at hqp
    have hmem := (mem_kmswPrefixOutgoingEdges w hfin hL htrans hR v
      (List.ofFn (fun i : Fin n => P.edge i.val)) (P.edge n)).2 (P.edge_outgoing n)
    exact (List.idxOf_inj hmem).1 (Nat.le_antisymm hpq hqp)

/-- The universal first-divergence property characterizes the constructed
edge stream uniquely among infinite LDP geodesics
Toward lem-geo-exist; partial: leftmost here means
first-divergence-lexicographically leftmost, not the source's submap
containment. -/
theorem kmswLeftmostLdpPath_unique_edge (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments)
    (P : InfinitePresentPath w ⟨v⟩) (hP : P.HasLongestSegments)
    (hleft : ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasLongestSegments →
      GeodesicFirstDivergenceRightOf w hfin hL htrans hR v P Q) :
    P.edge = (kmswLeftmostLdpPath w hfin hL htrans hR v hg).edge := by
  apply GeodesicFirstDivergenceRightOf.antisymm w hfin hL htrans hR v P
    (kmswLeftmostLdpPath w hfin hL htrans hR v hg)
  · exact hleft _ (kmswLeftmostLdpPath_hasLongestSegments w hfin hL htrans hR v hg)
  · exact kmswLeftmostLdpPath_firstDivergenceRightOf w hfin hL htrans hR v hg P hP

/-- There is exactly one edge stream of an infinite LDP geodesic with the
universal first-divergence property. Auxiliary finite path realizations are
not part of this uniqueness carrier
Toward lem-geo-exist; partial: leftmost here means
first-divergence-lexicographically leftmost, not the source's submap
containment. -/
theorem existsUnique_firstDivergenceLeftmostLdp_edge (v : ℕ)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) :
    ∃! edges : ℕ → ℕ, ∃ P : InfinitePresentPath w ⟨v⟩,
      P.HasLongestSegments ∧ P.edge = edges ∧
      ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasLongestSegments →
        GeodesicFirstDivergenceRightOf w hfin hL htrans hR v P Q := by
  refine ⟨(kmswLeftmostLdpPath w hfin hL htrans hR v hg).edge, ?_, ?_⟩
  · exact ⟨kmswLeftmostLdpPath w hfin hL htrans hR v hg,
      kmswLeftmostLdpPath_hasLongestSegments w hfin hL htrans hR v hg, rfl,
      kmswLeftmostLdpPath_firstDivergenceRightOf w hfin hL htrans hR v hg⟩
  · rintro edges ⟨P, hP, he, hleft⟩
    exact he.symm.trans (kmswLeftmostLdpPath_unique_edge w hfin hL htrans hR v hg P hP hleft)

/-- At an actual first difference, the competitor's outgoing edge is strictly -/
theorem GeodesicFirstDivergenceRightOf.strict_of_ne (v : ℕ)
    (P Q : InfinitePresentPath w ⟨v⟩)
    (hPQ : GeodesicFirstDivergenceRightOf w hfin hL htrans hR v P Q)
    (n : ℕ) (hn : ∀ i, i < n → P.edge i = Q.edge i) (hne : P.edge n ≠ Q.edge n) :
    (kmswPrefixOutgoingEdges w hfin hL htrans hR v
      (List.ofFn (fun i : Fin n => P.edge i.val))).idxOf (P.edge n) <
    (kmswPrefixOutgoingEdges w hfin hL htrans hR v
      (List.ofFn (fun i : Fin n => P.edge i.val))).idxOf (Q.edge n) := by
  have hmem := (mem_kmswPrefixOutgoingEdges w hfin hL htrans hR v
    (List.ofFn (fun i : Fin n => P.edge i.val)) (P.edge n)).2 (P.edge_outgoing n)
  exact lt_of_le_of_ne (hPQ n hn) (fun he => hne ((List.idxOf_inj hmem).1 he))



theorem startsInfiniteLdpGeodesicWithPrefix_singleton_iff (v e : ℕ) :
    StartsInfiniteLdpGeodesicWithPrefix w v [e] ↔ StartsInfiniteLdpGeodesic w v e := by
  constructor
  · rintro ⟨P, hP, he⟩
    refine ⟨P, hP, ?_⟩
    simpa only [List.length_singleton, List.ofFn_succ, List.ofFn_zero,
      Fin.val_zero, List.singleton_inj] using he
  · rintro ⟨P, hP, he⟩
    refine ⟨P, hP, ?_⟩
    simpa only [List.length_singleton, List.ofFn_succ, List.ofFn_zero, Fin.val_zero] using
      congrArg (fun e : ℕ => [e]) he



theorem kmswLeftmostLdpExtension_nil (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) :
    kmswLeftmostLdpExtension w hfin hL htrans hR v [] =
      kmswLeftmostLdpStep w hfin hL htrans hR v hv := by
  classical
  simp only [kmswLeftmostLdpExtension, kmswPrefixOutgoingEdges, geodesicPrefixEnd,
    List.getLast?_nil, Option.elim_none, List.nil_append,
    startsInfiniteLdpGeodesicWithPrefix_singleton_iff, kmswLeftmostLdpStep]



theorem kmswLeftmostLdpPath_first_edge (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex)
    (hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments) :
    kmswLeftmostLdpStep w hfin hL htrans hR v hv =
      some ((kmswLeftmostLdpPath w hfin hL htrans hR v hg).edge 0) := by
  rw [← kmswLeftmostLdpExtension_nil w hfin hL htrans hR v hv]
  exact kmswLeftmostLdpEdge_selected w hfin hL htrans hR v hg 0

/-- Simultaneously from every vertex, the UIQBOT realization almost surely
has a longest-segment path with the universal first-divergence comparison,
and its edge stream is unique with this property. This does not assert the
unformalized submap-containment clause of `def-infinite-geo` -/
theorem pitmanCodes_ae_exists_unique_firstDivergenceLeftmostLdp :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
      ∃ (hf : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
        (hL : ∀ j, 0 ≤ L w j) (ht : Tendsto (L w) atTop atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a),
        ∀ v, ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments ∧
          (∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasLongestSegments →
            GeodesicFirstDivergenceRightOf w hf hL ht hR v P Q) ∧
          ∀ Q : InfinitePresentPath w ⟨v⟩, Q.HasLongestSegments →
            (∀ S : InfinitePresentPath w ⟨v⟩, S.HasLongestSegments →
              GeodesicFirstDivergenceRightOf w hf hL ht hR v Q S) → Q.edge = P.edge := by
  filter_upwards [pitmanCodes_ae_leftmostLdpStep_isSome] with ω hstep
  obtain ⟨hf, hL, ht, hR, halloc, hs⟩ := hstep
  let w := RandomWalk.pitmanCode (fun i => ω (i + 1))
  refine ⟨hf, hL, ht, hR, fun v => ?_⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (hs v)
  obtain ⟨P₀, hP₀, _⟩ :=
    ((kmswLeftmostLdpStep_eq_some_iff w hf hL ht hR v (halloc v) e).1 he).1
  have hg : ∃ P : InfinitePresentPath w ⟨v⟩, P.HasLongestSegments := ⟨P₀, hP₀⟩
  exact ⟨kmswLeftmostLdpPath w hf hL ht hR v hg,
    kmswLeftmostLdpPath_hasLongestSegments w hf hL ht hR v hg,
    kmswLeftmostLdpPath_firstDivergenceRightOf w hf hL ht hR v hg,
    fun Q hQ hleft => kmswLeftmostLdpPath_unique_edge w hf hL ht hR v hg Q hQ hleft⟩

end DirectedDistances.KMSW
