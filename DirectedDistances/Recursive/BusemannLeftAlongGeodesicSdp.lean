module

public import DirectedDistances.Recursive.BusemannLeftAlongGeodesic
public import DirectedDistances.Recursive.BusemannLeftSideDecompositionSdp
public import DirectedDistances.Recursive.BusemannRightSideLocalizationSdp
public import DirectedDistances.KMSW.HatLimitDartIdentification
public import DirectedDistances.KMSW.GluingBoundaryOrder
public import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfLaunchSeed
import DirectedDistances.KMSW.UIQBOTOrientation
import DirectedDistances.KMSW.DirectedContainHat
import DirectedDistances.Recursive.OneStepTransport
import DirectedDistances.PaperProofs.Section4.ThinMapSideConfinement

/-! Supporting lemmas for paper labels `lem-geo-infty`, `lem-geo-infty-ind` (see CORRESPONDENCE.md). -/






public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap DirectedDistances.Paper.Section4
open DirectedDistances.PaperProofs.Section4 DirectedDistances.PaperProofs.Section3
open Quiver MeasureTheory Filter

local notation "SdpDomain" =>
  selectedCutCoherentDomain XDP.sdp renewalTime renewalTime_positiveSuccessTime
local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" q => sourceAncestor_finite_incidence
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "HL" q => sourceAncestor_left_nonneg
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "HT" q => sourceAncestor_left_transient
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "HR" q => sourceAncestor_right_unbounded
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "Q" q => sourceAncestorPath
  XDP.sdp renewalTime renewalTime_positiveSuccessTime q
local notation "SE" => fun (q : SdpDomain) (a : ThinMapSide) =>
  sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (Q q) a
local notation "SV" => fun (q : SdpDomain) (a : ThinMapSide) =>
  sideVertices (W q) (HF q) (HL q) (HT q) (HR q) (Q q) a

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The closed left SDP edge side keeps all geometric edges outside the hatted map and -/
@[expose] noncomputable def closedLeftSdpEdges (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain) : Set ℕ :=
  {e | ¬ MhatGeometricEdge w e} ∪ hatLimitEdgeMap w h '' SE q .left

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The closed right SDP edge side is the image of its hatted side, retaining edge IDs. -/
@[expose] noncomputable def closedRightSdpEdges (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain) : Set ℕ :=
  hatLimitEdgeMap w h '' SE q .right

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw closed left SDP vertex side includes the primed region and the hatted left side. -/
@[expose] noncomputable def closedLeftSdpVertices (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain) : Set (PresentVertex w) :=
  {v | v ∉ leftHatVertices w} ∪
    {v | ∃ a ∈ SV q .left, hatLimitVertexMap w h a = v.id}

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw closed right SDP vertex side is the image of the hatted right side. -/
@[expose] noncomputable def closedRightSdpVertices (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain) : Set (PresentVertex w) :=
  {v | ∃ a ∈ SV q .right, hatLimitVertexMap w h a = v.id}





@[expose] noncomputable def leftAlongSdpSeamEdge (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain) (i : ℕ) : ℕ :=
  hatLimitEdgeMap w h ((Q q).edge i)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Prepends a present edge to an infinite path and retains the original tail. -/
private noncomputable def sdpAlongPrepend {w : ℕ → Fin 3} {u v : PresentVertex w}
    (e : u ⟶ v) (S : InfinitePresentPath w v) : InfinitePresentPath w u where
  edge
    | 0 => e.val
    | n + 1 => S.edge n
  initial
    | 0 => ⟨u, .nil⟩
    | n + 1 => ⟨(S.initial n).1, e.toPath.comp (S.initial n).2⟩
  prefix_length n := by
    cases n with
    | zero => rfl
    | succ n => simp only [Path.length_comp, Path.length_toPath, S.prefix_length, Nat.add_comm]
  prefix_edges n := by
    cases n with
    | zero => rfl
    | succ n =>
      rw [pathEdgeList_comp, S.prefix_edges, List.ofFn_succ]
      rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A finite prefix followed by an infinite path preserves the tail edge stream. -/
private theorem sdpAlongExtend {w : ℕ → Fin 3} {u v : PresentVertex w}
    (p : Path u v) (S : InfinitePresentPath w v) :
    ∃ T : InfinitePresentPath w u, Set.range S.edge ⊆ Set.range T.edge := by
  induction p with
  | nil => exact ⟨S, Set.Subset.rfl⟩
  | @cons v z p e ih =>
    obtain ⟨T, hT⟩ := ih (sdpAlongPrepend e S)
    refine ⟨T, ?_⟩
    rintro f ⟨i, rfl⟩
    exact hT ⟨i + 1, rfl⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every present hatted edge belongs to a side of the canonical SDP seam. -/
private theorem sdpAlongSideEdgeCover (q : SdpDomain) (e : ℕ)
    (he : EdgePresent (W q) e) : e ∈ SE q .left ∪ SE q .right := by
  classical
  by_cases hs : ∃ i, e = (Q q).edge i
  · obtain ⟨i, rfl⟩ := hs
    exact Or.inl (seamEdge_mem_sideEdges
      (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left i)
  · have hoff := fun i hi => hs ⟨i, hi⟩
    obtain ⟨p⟩ := allocated_vertex_reachable_from_zero (W q) (HL q)
      (edgeWest (W q) e) (kmswVertexAllocated_all _ ⟨edgeWest (W q) e⟩)
    let a : (⟨edgeWest (W q) e⟩ : PresentVertex (W q)) ⟶
        ⟨edgeEast (W q) e⟩ := ⟨e, he, rfl, rfl⟩
    let S := sdpAlongPrepend a
      (kmswRightmostPath (W q) (HF q) (HL q) (HT q) (HR q) (edgeEast (W q) e))
    obtain ⟨T, hT⟩ := sdpAlongExtend p S
    obtain ⟨i, hi⟩ := hT (show e ∈ Set.range S.edge from ⟨0, rfl⟩)
    have hz := thinMapPathTrace_subset_sideRegions
      (W q) (HF q) (HL q) (HT q) (HR q) (Q q) T
      (Set.mem_iUnion.mpr ⟨i, hi ▸ (thinMapArcSeed_mem_interior (W q) (HF q) e).1⟩)
    rw [hi] at hz
    rcases hz with hl | hr
    · exact Or.inl ((thinMapArc_subset_sideRegion_iff_seed
        (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left e hoff).mpr hl)
    · exact Or.inr ((thinMapArc_subset_sideRegion_iff_seed
        (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .right e hoff).mpr hr)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The two raw closed edge sides cover all geometric edges, including missing edges. -/
theorem closedSdpEdges_cover (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : SdpDomain) (hw : (W q) = hatCodes w h) :
    closedLeftSdpEdges w h q ∪ closedRightSdpEdges w h q = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro e
  by_cases he : MhatGeometricEdge w e
  · obtain ⟨a, rfl⟩ := (hatLimitEdgeMap_geometric_range_iff w h e).mpr he
    have ha : EdgePresent (W q) a := hw.symm ▸ hatCodes_edge_present w h a
    rcases sdpAlongSideEdgeCover q a ha with hl | hr
    · exact Or.inl (Or.inr ⟨a, hl, rfl⟩)
    · exact Or.inr ⟨a, hr, rfl⟩
  · exact Or.inl (Or.inl he)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The edge-side intersection is exactly the image of the seam edge stream. -/
theorem closedSdpEdges_inter (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : SdpDomain) :
    closedLeftSdpEdges w h q ∩ closedRightSdpEdges w h q =
      Set.range (leftAlongSdpSeamEdge w h q) := by
  ext e
  constructor
  · rintro ⟨hl, a, ha, rfl⟩
    have hm := (hatLimitEdgeMap_geometric_range_iff w h _).mp ⟨a, rfl⟩
    rcases hl with hn | ⟨b, hb, he⟩
    · exact (hn hm).elim
    · have hba := hatLimitEdgeMap_injective w h he
      subst b
      have hs : a ∈ Set.range (Q q).edge := by
        rw [← thinMapSideEdges_inter_eq_seamEdges
          (W q) (HF q) (HL q) (HT q) (HR q) (Q q)]
        exact ⟨hb, ha⟩
      obtain ⟨i, rfl⟩ := hs
      exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Or.inr ⟨(Q q).edge i, seamEdge_mem_sideEdges
      (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left i, rfl⟩,
      ⟨(Q q).edge i, seamEdge_mem_sideEdges
        (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .right i, rfl⟩⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The hatted-to-raw incidence functor preserves paths and individual edge IDs. -/
@[expose] noncomputable def alongSdpHatFunctor (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain) (hw : (W q) = hatCodes w h) :
    Prefunctor (PresentVertex (W q)) (PresentVertex w) where
  obj a := ⟨hatLimitVertexMap w h a.id⟩
  map {a b} e := by
    have he : EdgePresent (hatCodes w h) e.val := by
      rw [← hw]
      exact e.property.1
    have hi := hatLimit_edge_incidence (hatLimitExplicitInput w h) he
    rw [← hw] at hi
    exact ⟨hatLimitEdgeMap w h e.val, hi.1,
      hi.2.1.trans (congrArg (hatLimitVertexMap w h) e.property.2.1),
      hi.2.2.trans (congrArg (hatLimitVertexMap w h) e.property.2.2)⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The hatted-to-raw incidence functor preserves finite path lengths. -/
theorem alongSdpMap_length (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : SdpDomain) (hw : (W q) = hatCodes w h)
    {a b : PresentVertex (W q)} (p : Path a b) :
    ((alongSdpHatFunctor w h q hw).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The mapped path retains the exact ordered edge-ID list through the hat map. -/
theorem alongSdpMap_edges (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : SdpDomain) (hw : (W q) = hatCodes w h)
    {a b : PresentVertex (W q)} (p : Path a b) :
    pathEdgeList ((alongSdpHatFunctor w h q hw).mapPath p) =
      (pathEdgeList p).map (hatLimitEdgeMap w h) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, pathEdgeList, ih, List.map_append,
      List.map_singleton]
    rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The mapped canonical hatted path before transporting its root equality. -/
@[expose] noncomputable def alongSdpMappedPath (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain) (hw : (W q) = hatCodes w h) :
    InfinitePresentPath w ⟨hatLimitVertexMap w h 0⟩ where
  edge := leftAlongSdpSeamEdge w h q
  initial n := ⟨(alongSdpHatFunctor w h q hw).obj ((Q q).initial n).1,
    (alongSdpHatFunctor w h q hw).mapPath ((Q q).initial n).2⟩
  prefix_length n := (alongSdpMap_length w h q hw _).trans ((Q q).prefix_length n)
  prefix_edges n := by
    change pathEdgeList ((alongSdpHatFunctor w h q hw).mapPath ((Q q).initial n).2) = _
    rw [alongSdpMap_edges, (Q q).prefix_edges]
    simp only [List.map_ofFn, Function.comp_def]
    rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Transport of the root equality preserves the exact edge stream. -/
private theorem alongSdpRootTransport_edge {w : ℕ → Fin 3} {a b : PresentVertex w}
    (hab : a = b) (P : InfinitePresentPath w a) : (hab ▸ P).edge = P.edge := by
  subst b
  rfl





@[expose] noncomputable def leftAlongRawSdpGeodesic (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain) (hw : (W q) = hatCodes w h) :
    InfinitePresentPath w ⟨0⟩ :=
  (congrArg PresentVertex.mk (hatLimitExplicitInput w h).root) ▸
    alongSdpMappedPath w h q hw

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw SDP path's edge stream is the exact image of the hatted seam stream. -/
theorem leftAlongRawSdpGeodesic_edge (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain)
    (hw : (W q) = hatCodes w h) :
    (leftAlongRawSdpGeodesic w h q hw).edge = leftAlongSdpSeamEdge w h q :=
  alongSdpRootTransport_edge _ _

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw closed edge sides intersect exactly in the raw SDP path edge stream. -/
theorem closedSdpEdges_inter_rawGeodesic (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain)
    (hw : (W q) = hatCodes w h) :
    closedLeftSdpEdges w h q ∩ closedRightSdpEdges w h q =
      Set.range (leftAlongRawSdpGeodesic w h q hw).edge := by
  rw [leftAlongRawSdpGeodesic_edge]
  exact closedSdpEdges_inter w h q


/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Transport of the initial vertex preserves every mapped prefix endpoint. -/
private theorem alongSdpRootTransport_vertex {w : ℕ → Fin 3} {a b : PresentVertex w}
    (hab : a = b) (P : InfinitePresentPath w a) (n : ℕ) :
    ((hab ▸ P).initial n).1 = (P.initial n).1 := by
  subst b
  rfl

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Each raw prefix endpoint is the H-image of the corresponding canonical SDP endpoint. -/
theorem leftAlongRawSdpGeodesic_vertex (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain)
    (hw : (W q) = hatCodes w h) (n : ℕ) :
    ((leftAlongRawSdpGeodesic w h q hw).initial n).1 =
      ⟨hatLimitVertexMap w h ((Q q).initial n).1.id⟩ :=
  alongSdpRootTransport_vertex _ _ n

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every raw prefix is a shortest path, by lifting all raw competitors to the coherent
hatted carrier without changing lengths. -/
theorem leftAlongRawSdpGeodesic_initial_isShortest (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain)
    (hw : (W q) = hatCodes w h) (n : ℕ) :
    IsShortest ((leftAlongRawSdpGeodesic w h q hw).initial n).2 := by
  have hQ : (Q q).HasShortestSegments := by
    obtain ⟨_, hgS⟩ := selectedCutCoherentDomain_infinite_extremal
      XDP.sdp renewalTime renewalTime_positiveSuccessTime q
    exact kmswLeftmostSdpPath_hasShortestSegments
      (W q) (HF q) (HL q) (HT q) (HR q) 0 hgS
  intro p
  have hv := leftAlongRawSdpGeodesic_vertex w h q hw n
  have hroot : hatLimitVertexMap w h 0 = 0 := (hatLimitExplicitInput w h).root
  have hlift : ∃ r : Path (⟨0⟩ : PresentVertex (W q)) ((Q q).initial n).1,
      r.length = p.length := by
    obtain ⟨p', hp'⟩ : ∃ p' : Path
        (⟨hatLimitVertexMap w h 0⟩ : PresentVertex w)
        ⟨hatLimitVertexMap w h ((Q q).initial n).1.id⟩,
        p'.length = p.length := by
      rw [hroot, ← hv]
      exact ⟨p, rfl⟩
    obtain ⟨r, hr⟩ := rightHat_path_lift w h ⟨0⟩
      ⟨((Q q).initial n).1.id⟩ p'
    have hr' : ∃ r : Path (⟨0⟩ : PresentVertex (hatCodes w h))
        ⟨((Q q).initial n).1.id⟩, r.length = p.length := ⟨r, hr.trans hp'⟩
    rw [← hw] at hr'
    exact hr'
  obtain ⟨r, hr⟩ := hlift
  have hn := (Q q).initial_isShortest (W q) hQ n r
  rw [hr, (Q q).prefix_length] at hn
  rw [(leftAlongRawSdpGeodesic w h q hw).prefix_length]
  exact hn

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every nonempty raw segment is shortest, with the source's literal indexing. -/
theorem leftAlongRawSdpGeodesic_hasShortestSegments (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain)
    (hw : (W q) = hatCodes w h) :
    (leftAlongRawSdpGeodesic w h q hw).HasShortestSegments := by
  let P := leftAlongRawSdpGeodesic w h q hw
  intro a b ha hab
  obtain ⟨z, p, r, hpr, hp⟩ := (P.initial b).2.exists_eq_comp_of_le_length
    (show a - 1 ≤ (P.initial b).2.length by rw [P.prefix_length]; omega)
  refine ⟨z, r, ?_, ?_, ?_⟩
  · have hlen := P.prefix_length b
    rw [hpr, Path.length_comp, hp] at hlen
    omega
  · rw [← P.prefix_edges b, hpr, pathEdgeList_comp, ← hp, ← pathEdgeList_length p]
    exact List.drop_left.symm
  · have hopt := leftAlongRawSdpGeodesic_initial_isShortest w h q hw b
    change IsShortest (P.initial b).2 at hopt
    rw [hpr] at hopt
    exact hopt.of_comp_right

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The finite raw root SDP to the seam at index t is attained and equals t, including zero. -/
theorem leftAlongRawSdpGeodesic_root_distance (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain)
    (hw : (W q) = hatCodes w h) (t : ℕ) :
    sdp (⟨0⟩ : PresentVertex w)
      ((leftAlongRawSdpGeodesic w h q hw).initial t).1 = (t : ℕ∞) := by
  exact leftSdpGeodesic_root_distance
    (leftAlongRawSdpGeodesic w h q hw)
    (leftAlongRawSdpGeodesic_hasShortestSegments w h q hw) t

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A path ending outside the hatted reachable region uses only non-hatted edges. -/
private theorem sdpAlongOutsideEdges {w : ℕ → Fin 3} {x y : PresentVertex w}
    (p : Path x y) (hy : y ∉ leftHatVertices w) :
    ∀ e ∈ pathEdgeList p, ¬ MhatGeometricEdge w e := by
  induction p with
  | nil => exact fun _ he => False.elim (List.not_mem_nil he)
  | @cons z y p e ih =>
    have hz : z ∉ leftHatVertices w := by
      intro hz
      exact hy (leftHatVertices_closed hz e.toPath)
    intro f hf
    change f ∈ pathEdgeList p ++ [e.val] at hf
    rcases List.mem_append.mp hf with hf | hf
    · exact ih hz f hf
    · have heq : f = e.val := List.mem_singleton.mp hf
      subst f
      intro hgeom
      apply hy
      have hend := hgeom.2
      rw [e.property.2.2] at hend
      exact hend

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A first-entry prefix uses only primed geometric edges, including its crossing arrow. -/
private theorem sdpAlongEntryEdges {w : ℕ → Fin 3} {x y : PresentVertex w}
    (p : Path x y)
    (hp : ∀ u ∈ p.vertices, u ≠ y → u ∉ leftHatVertices w) :
    ∀ e ∈ pathEdgeList p, ¬ MhatGeometricEdge w e := by
  cases p with
  | nil => exact fun _ he => False.elim (List.not_mem_nil he)
  | @cons z y p e =>
    have hzy : z ≠ y := by
      intro heq
      have hc : ∀ v : PresentVertex w, ∀ r : Path v v, r.length = 0 :=
        presentVertex_acyclic w
      subst y
      have hz := hc z e.toPath
      simp only [Path.length_toPath] at hz
      omega
    have hz : z ∉ leftHatVertices w := hp z
      ((Path.mem_vertices_cons p e).mpr (Or.inl p.end_mem_vertices)) hzy
    intro f hf
    change f ∈ pathEdgeList p ++ [e.val] at hf
    rcases List.mem_append.mp hf with hf | hf
    · exact sdpAlongOutsideEdges p hz f hf
    · have heq : f = e.val := List.mem_singleton.mp hf
      subst f
      intro hgeom
      apply hz
      have hstart := hgeom.1
      rw [e.property.2.1] at hstart
      exact hstart

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every first-entry split has a closed-left prefix and a wholly hatted suffix. -/
theorem leftAlongSdp_firstEntry_closedLeft (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain) {x y : PresentVertex w}
    (p : Path x y) (hx : x ∉ leftHatVertices w) (hy : y ∈ leftHatVertices w) :
    ∃ v ∈ leftHatEntryVertices w, ∃ a : Path x v, ∃ b : Path v y,
      p = a.comp b ∧ (∀ e ∈ pathEdgeList a, e ∈ closedLeftSdpEdges w h q) ∧
      ∀ u ∈ b.vertices, u ∈ leftHatVertices w := by
  obtain ⟨v, hv, a, b, hp, ha, hb⟩ := leftHat_firstEntry_split p hx hy
  exact ⟨v, hv, a, b, hp, fun e he => Or.inl (sdpAlongEntryEdges a ha e he), hb⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every entry vertex lifts into the SDP closed left side through the ordered beta boundary. -/
theorem leftAlongSdpEntryLocalization_proved (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w)
    (q : SdpDomain) (hw : (W q) = hatCodes w h) :
    ∀ v ∈ leftHatEntryVertices w,
      ∃ a ∈ SV q .left, hatLimitVertexMap w h a = v.id := by
  intro v hv
  let hb := hatBoundaryHitWitnesses w h
  obtain ⟨i, hi⟩ := leftHatEntryOnBeta_proved w hfin hb v hv
  have htail : kmswBeta0Vertices w hfin hb i =
      edgeWest w (kmswBeta0Stream w hfin hb i).1 := by
    cases i with
    | zero => exact (kmswBeta0Stream_start w hfin hb).symm
    | succ i => exact (kmswBeta0Stream_chain w hfin hb i).symm
  let a := edgeWest (W q) (kmswLeftBoundaryEdge (W q) i)
  have ha : a ∈ SV q .left := by
    have hv := thinMapBoundaryVertex_mem_sourceAncestorVertices
      (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left i
    have haw : a = thinMapBoundaryVertex (W q) (HF q) (HL q) (HT q)
        (HR q) .left i := by
      dsimp [a]
      cases i with
      | zero => exact (kmswLeftBoundary_infinite_present_path
          (W q) (HT q) (HL q) (HR q)).2.2.1
      | succ i => exact ((kmswLeftBoundary_infinite_present_path
          (W q) (HT q) (HL q) (HR q)).2.1 i).symm
    exact haw ▸ hv.1
  refine ⟨a, ha, ?_⟩
  rw [hi, htail, ← hattedLeftBoundaryBeta0EdgeCorrespondence_proved w h hfin hb i,
    (hatLimitEdgeMap_endpoint_alignment w h _).1]
  dsimp [a]
  rw [hw]


/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A vertex in both SDP side regions is on the actual canonical seam. -/
private theorem sdpSideVertexInter (q : SdpDomain) (v : PresentVertex (W q))
    (hl : v.id ∈ SV q .left) (hr : v.id ∈ SV q .right) :
    ∃ i, v = ((Q q).initial i).1 := by
  have hv : (monotoneFamilyDrawing (W q) (HF q) (monotone_family_all (W q))).pos v.id ∈
      pathTrace (monotoneFamilyDrawing (W q) (HF q) (monotone_family_all (W q)))
        (fun i => ((Q q).edge i, false)) := by
    rw [← thinMapSideRegions_inter_eq_seamTrace
      (W q) (HF q) (HL q) (HT q) (HR q) (Q q)]
    exact ⟨hl, hr⟩
  obtain ⟨i, hi⟩ := (thinMapVertex_mem_seamTrace_iff (W q) (HF q) (Q q) v.id).mp hv
  exact ⟨i, congrArg PresentVertex.mk hi⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
A path with no seam vertex remains in its initial left side and uses left-side edges. -/
private theorem sdpPath_noSeam_left (q : SdpDomain) {x y : PresentVertex (W q)}
    (p : Path x y) (hx : x.id ∈ SV q .left)
    (hno : ∀ z ∈ p.vertices, ∀ i, z ≠ ((Q q).initial i).1) :
    y.id ∈ SV q .left ∧ ∀ e ∈ pathEdgeList p, e ∈ SE q .left := by
  induction p with
  | nil =>
    exact ⟨hx, fun _ he => False.elim (List.not_mem_nil he)⟩
  | @cons z y p e ih =>
    have hnoP : ∀ u ∈ p.vertices, ∀ i, u ≠ ((Q q).initial i).1 := by
      intro u hu i
      exact hno u ((Path.mem_vertices_cons p e).mpr (Or.inl hu)) i
    obtain ⟨hzL, hpL⟩ := ih hnoP
    have hreachX := allocated_vertex_reachable_from_zero (W q) (HL q) x.id
      (kmswVertexAllocated_all _ x)
    have hreachZ : Reachable (⟨0⟩ : PresentVertex (W q)) z := hreachX.trans p.reachable
    have heL : e.val ∈ SE q .left := by
      rcases sdpAlongSideEdgeCover q e.val e.property.1 with hl | hr
      · exact hl
      · have hzR := e.property.2.1 ▸
          (sideEdges_endpoints (W q) (HF q) (HL q) (HT q) (HR q)
            (Q q) .right hr).1
        obtain ⟨i, hi⟩ := sdpSideVertexInter q z hzL hzR
        exact (hnoP z p.end_mem_vertices i hi).elim
    have hyL := e.property.2.2 ▸
      (sideEdges_endpoints (W q) (HF q) (HL q) (HT q) (HR q)
        (Q q) .left heL).2
    refine ⟨hyL, ?_⟩
    intro f hf
    change f ∈ pathEdgeList p ++ [e.val] at hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hpL f hf
    · exact List.mem_singleton.mp hf ▸ heL

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every path from a left-side vertex to a right-side vertex visits the seam. -/
private theorem sdpPath_hits_seam (q : SdpDomain) {x y : PresentVertex (W q)}
    (p : Path x y) (hx : x.id ∈ SV q .left) (hy : y.id ∈ SV q .right) :
    ∃ i, ((Q q).initial i).1 ∈ p.vertices := by
  classical
  by_contra hn
  have hno : ∀ z ∈ p.vertices, ∀ i, z ≠ ((Q q).initial i).1 := by
    intro z hz i hi
    exact hn ⟨i, hi ▸ hz⟩
  have hyL := (sdpPath_noSeam_left q p hx hno).1
  obtain ⟨i, hi⟩ := sdpSideVertexInter q y hyL hy
  exact hno y p.end_mem_vertices i hi

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Splits at the first seam visit; the prefix lies entirely in the left side. -/
private theorem sdpFirstSeamSplit (q : SdpDomain) {x y : PresentVertex (W q)}
    (p : Path x y) (hx : x.id ∈ SV q .left)
    (hHit : ∃ i, ((Q q).initial i).1 ∈ p.vertices) :
    ∃ i, ∃ a : Path x ((Q q).initial i).1, ∃ b : Path ((Q q).initial i).1 y,
      p = a.comp b ∧ ∀ e ∈ pathEdgeList a, e ∈ SE q .left := by
  induction p with
  | nil =>
    obtain ⟨i, hi⟩ := hHit
    have heq : ((Q q).initial i).1 = x := by
      simpa only [Path.vertices_nil, List.mem_singleton] using hi
    subst x
    refine ⟨i, .nil, .nil, ?_, fun _ he => False.elim (List.not_mem_nil he)⟩
    rfl
  | @cons z y p e ih =>
    by_cases hpHit : ∃ i, ((Q q).initial i).1 ∈ p.vertices
    · obtain ⟨i, a, b, hp, ha⟩ := ih hpHit
      refine ⟨i, a, b.cons e, ?_, ha⟩
      rw [hp, Path.comp_cons]
    · obtain ⟨i, hi⟩ := hHit
      have hyHit : y = ((Q q).initial i).1 := by
        rcases (Path.mem_vertices_cons p e).mp hi with hprev | hend
        · exact (hpHit ⟨i, hprev⟩).elim
        · exact hend.symm
      have hno : ∀ u ∈ p.vertices, ∀ j, u ≠ ((Q q).initial j).1 := by
        intro u hu j hEq
        exact hpHit ⟨j, hEq ▸ hu⟩
      have hzL := sdpPath_noSeam_left q p hx hno
      subst y
      have hreachX := allocated_vertex_reachable_from_zero (W q) (HL q) x.id
        (kmswVertexAllocated_all _ x)
      have hreachZ : Reachable (⟨0⟩ : PresentVertex (W q)) z := hreachX.trans p.reachable
      have heL : e.val ∈ SE q .left := by
        rcases sdpAlongSideEdgeCover q e.val e.property.1 with hl | hr
        · exact hl
        · have hzR := e.property.2.1 ▸
            (sideEdges_endpoints (W q) (HF q) (HL q) (HT q) (HR q)
              (Q q) .right hr).1
          obtain ⟨j, hj⟩ := sdpSideVertexInter q z hzL.1 hzR
          exact (hno z p.end_mem_vertices j hj).elim
      refine ⟨i, p.cons e, .nil, ?_, ?_⟩
      · exact (Path.comp_nil _).symm
      · intro f hf
        change f ∈ pathEdgeList p ++ [e.val] at hf
        rcases List.mem_append.mp hf with hf | hf
        · exact hzL.2 f hf
        · exact List.mem_singleton.mp hf ▸ heL

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The canonical shortest seam visits distinct vertices, by acyclicity and prefix lengths. -/
private theorem sdpSeamVertex_injective (q : SdpDomain) :
    Function.Injective (fun i => ((Q q).initial i).1) := by
  have hz {u v : PresentVertex (W q)} (r : Path u v) (huv : u = v) :
      r.length = 0 := by
    subst v
    exact presentVertex_acyclic (W q) _ r
  have hordered (i j : ℕ) (hij : i ≤ j)
      (heq : ((Q q).initial i).1 = ((Q q).initial j).1) : i = j := by
    have H := (Q q).exists_shift_split i (j - i)
    rw [Nat.add_sub_of_le hij] at H
    obtain ⟨_, r, _, _, hr, _⟩ := H
    have hr0 := hz r heq
    omega
  intro i j heq
  rcases le_total i j with hij | hji
  · exact hordered i j hij heq
  · exact (hordered j i hji heq.symm).symm

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The suffix after the last seam vertex contains no later seam vertex. -/
private theorem sdpLastSeamSplit (q : SdpDomain) {x y : PresentVertex (W q)}
    (p : Path x y) (hHit : ∃ i, ((Q q).initial i).1 ∈ p.vertices) :
    ∃ i, ∃ a : Path x ((Q q).initial i).1, ∃ b : Path ((Q q).initial i).1 y,
      p = a.comp b ∧
      ∀ j, ((Q q).initial j).1 ∈ b.vertices → j = i := by
  classical
  induction p with
  | nil =>
    obtain ⟨i, hi⟩ := hHit
    have heq : ((Q q).initial i).1 = x := by
      simpa only [Path.vertices_nil, List.mem_singleton] using hi
    subst x
    refine ⟨i, .nil, .nil, rfl, ?_⟩
    intro j hj
    have hEq : ((Q q).initial j).1 = ((Q q).initial i).1 := by
      simpa only [Path.vertices_nil, List.mem_singleton] using hj
    exact sdpSeamVertex_injective q hEq
  | @cons z y p e ih =>
    by_cases hend : ∃ i, y = ((Q q).initial i).1
    · obtain ⟨i, rfl⟩ := hend
      refine ⟨i, p.cons e, .nil, (Path.comp_nil _).symm, ?_⟩
      intro j hj
      have heq : ((Q q).initial j).1 = ((Q q).initial i).1 := by
        simpa only [Path.vertices_nil, List.mem_singleton] using hj
      exact sdpSeamVertex_injective q heq
    · have hHitP : ∃ i, ((Q q).initial i).1 ∈ p.vertices := by
        obtain ⟨i, hi⟩ := hHit
        rcases (Path.mem_vertices_cons p e).mp hi with hi | hi
        · exact ⟨i, hi⟩
        · exact (hend ⟨i, hi.symm⟩).elim
      obtain ⟨i, a, b, hp, hb⟩ := ih hHitP
      refine ⟨i, a, b.cons e, ?_, ?_⟩
      · rw [hp, Path.comp_cons]
      · intro j hj
        rcases (Path.mem_vertices_cons b e).mp hj with hj | hj
        · exact hb j hj
        · exact (hend ⟨j, hj.symm⟩).elim


/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The shortest-path single-seam exchange at specified closed sides and edge carriers. -/
@[expose] def LeftClosedSideSdpGeodesicExchange (w : ℕ → Fin 3)
    (P : InfinitePresentPath w ⟨0⟩)
    (closedLeftVertices closedRightVertices : Set (PresentVertex w))
    (closedLeftEdges closedRightEdges : Set ℕ) : Prop :=
  ∀ x ∈ closedLeftVertices, ∀ y ∈ closedRightVertices,
    ∀ p : Path x y, IsShortest p →
      ∃ t, ∃ a : Path x (P.initial t).1, ∃ b : Path (P.initial t).1 y,
        a.length + b.length = p.length ∧ IsShortest (a.comp b) ∧
        (∀ e ∈ pathEdgeList a, e ∈ closedLeftEdges) ∧
        (∀ e ∈ pathEdgeList b, e ∈ closedRightEdges) ∧
        ∀ s, (P.initial s).1 ∈ b.vertices → s = t

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
In the hatted SDP carrier, a shortest path between sides rearranges to one seam visit.
The left prefix includes its seam segment; the right suffix has no later seam visit. -/
private theorem leftAlongSdpHat_exchange (q : SdpDomain) :
    LeftClosedSideSdpGeodesicExchange (W q) (Q q)
      {v | v.id ∈ SV q .left} {v | v.id ∈ SV q .right}
      (SE q .left) (SE q .right) := by
  intro u hu v hv p hp
  obtain ⟨i, hi⟩ := sdpPath_hits_seam q p hu hv
  obtain ⟨i, a, b, hsplit, ha⟩ := sdpFirstSeamSplit q p hu ⟨i, hi⟩
  have hseamRight := seamVertex_mem_sideVertices
    (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .right i
  have hreachSeam := allocated_vertex_reachable_from_zero (W q) (HL q)
    ((Q q).initial i).1.id (kmswVertexAllocated_all _ ((Q q).initial i).1)
  obtain ⟨r, hrlen, hrEdges⟩ := rightSideSdp_path_dominance q b
    hreachSeam hseamRight hv
  have hpSplitLen := congrArg Path.length hsplit
  simp only [Path.length_comp] at hpSplitLen
  have hcompLen : a.length + r.length = p.length := by
    have hpLower := hp (a.comp r)
    have hpLower' : p.length ≤ a.length + r.length := by
      simpa only [Path.length_comp] using hpLower
    have hpUpper' : a.length + r.length ≤ p.length := by
      rw [hpSplitLen]
      exact Nat.add_le_add_left hrlen _
    exact Nat.le_antisymm hpUpper' hpLower'
  have hpComp : IsShortest (a.comp r) := by
    apply hp.of_length_eq
    simpa only [Path.length_comp] using hcompLen
  obtain ⟨j, c, d, hrsplit, hlast⟩ := sdpLastSeamSplit q r
    ⟨i, r.start_mem_vertices⟩
  have hpAssoc : IsShortest ((a.comp c).comp d) := by
    rw [Path.comp_assoc, ← hrsplit]
    exact hpComp
  have hQ : (Q q).HasShortestSegments := by
    obtain ⟨_, hgS⟩ := selectedCutCoherentDomain_infinite_extremal
      XDP.sdp renewalTime renewalTime_positiveSuccessTime q
    exact kmswLeftmostSdpPath_hasShortestSegments
      (W q) (HF q) (HL q) (HT q) (HR q) 0 hgS
  obtain ⟨s, _, _, hsEdges, hslen, hsShort⟩ :=
    leftSdpGeodesic_replace_excursion (Q q) hQ i j a c d hpAssoc
  have hrSplitLen := congrArg Path.length hrsplit
  simp only [Path.length_comp] at hrSplitLen
  have hlen : (a.comp s).length + d.length = p.length := by
    calc
      (a.comp s).length + d.length = a.length + s.length + d.length := by
        rw [Path.length_comp]
      _ = a.length + c.length + d.length := by rw [hslen]
      _ = a.length + r.length := by omega
      _ = p.length := hcompLen
  refine ⟨j, a.comp s, d, hlen, hsShort, ?_, ?_, hlast⟩
  · intro e he
    rw [pathEdgeList_comp] at he
    rcases List.mem_append.mp he with he | he
    · exact ha e he
    · rw [hsEdges] at he
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp he
      exact hk ▸ seamEdge_mem_sideEdges
        (W q) (HF q) (HL q) (HT q) (HR q) (Q q) .left (i + k.val)
  · intro e he
    apply hrEdges e
    rw [hrsplit, pathEdgeList_comp]
    exact List.mem_append.mpr (Or.inr he)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The raw SDP single-seam exchange, with closed sides from the actual raw geodesic. -/
@[expose] def LeftAlongSdpRawGeodesicExchange (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (q : SdpDomain)
    (hw : (W q) = hatCodes w h) : Prop :=
  LeftClosedSideSdpGeodesicExchange w (leftAlongRawSdpGeodesic w h q hw)
    (closedLeftSdpVertices w h q) (closedRightSdpVertices w h q)
    (closedLeftSdpEdges w h q) (closedRightSdpEdges w h q)
/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Mapped path vertices are precisely images of the original visited vertices. -/
private theorem sdpCloseMap_vertices {V U : Type*} [Quiver V] [Quiver U]
    (F : Prefunctor V U) {a b : V} (p : Path a b) (z : U)
    (hz : z ∈ (F.mapPath p).vertices) : ∃ v ∈ p.vertices, F.obj v = z := by
  induction p with
  | nil =>
    have he : z = F.obj a := by
      simpa only [Prefunctor.mapPath_nil, Path.vertices_nil, List.mem_singleton] using hz
    exact ⟨a, Path.start_mem_vertices _, he.symm⟩
  | @cons b c p e ih =>
    rcases (Path.mem_vertices_cons (F.mapPath p) (F.map e)).mp hz with hz | hz
    · obtain ⟨v, hv, he⟩ := ih hz
      exact ⟨v, (Path.mem_vertices_cons p e).mpr (Or.inl hv), he⟩
    · exact ⟨c, Path.end_mem_vertices _, hz.symm⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Injectivity of the hatted vertex injection on the identified coherent carrier. -/
private theorem sdpCloseVertex_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Function.Injective (hatLimitVertexMap w h) := by
  intro a b hab
  exact vertex_inj (hatLimitExplicitInput w h)
    (kmswVertexAllocated_all _ ⟨a⟩) (kmswVertexAllocated_all _ ⟨b⟩) hab

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The hatted exchange transports to raw endpoints; its suffix has no later seam visit. -/
private theorem sdpCloseHat_exchange (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (q : SdpDomain) (hw : (W q) = hatCodes w h)
    (u v : PresentVertex (W q)) (hu : u.id ∈ SV q .left)
    (hv : v.id ∈ SV q .right)
    (p : Path (⟨hatLimitVertexMap w h u.id⟩ : PresentVertex w)
      ⟨hatLimitVertexMap w h v.id⟩) (hp : IsShortest p) :
    ∃ t, ∃ a : Path (⟨hatLimitVertexMap w h u.id⟩ : PresentVertex w)
        ((leftAlongRawSdpGeodesic w h q hw).initial t).1,
      ∃ b : Path ((leftAlongRawSdpGeodesic w h q hw).initial t).1
        ⟨hatLimitVertexMap w h v.id⟩,
      a.length + b.length = p.length ∧ IsShortest (a.comp b) ∧
      (∀ e ∈ pathEdgeList a, e ∈ closedLeftSdpEdges w h q) ∧
      (∀ e ∈ pathEdgeList b, e ∈ closedRightSdpEdges w h q) ∧
      ∀ s, ((leftAlongRawSdpGeodesic w h q hw).initial s).1 ∈ b.vertices → s = t := by
  have hlift : ∃ r : Path u v, r.length = p.length := by
    have hh := rightHat_path_lift w h ⟨u.id⟩ ⟨v.id⟩ p
    erw [← hw] at hh
    exact hh
  obtain ⟨r, hr⟩ := hlift
  have hrl : IsShortest r := by
    intro s
    have hs := hp ((alongSdpHatFunctor w h q hw).mapPath s)
    erw [alongSdpMap_length w h q hw s, ← hr] at hs
    exact hs
  obtain ⟨t, a, b, hlen, _, ha, hb, ht⟩ :=
    leftAlongSdpHat_exchange q u hu v hv r hrl
  have hvertex := leftAlongRawSdpGeodesic_vertex w h q hw t
  refine ⟨t, ?_⟩
  erw [hvertex]
  let F := alongSdpHatFunctor w h q hw
  refine ⟨F.mapPath a, F.mapPath b, ?_, ?_, ?_, ?_, ?_⟩
  · erw [alongSdpMap_length w h q hw a, alongSdpMap_length w h q hw b, hlen, hr]
  · apply hp.of_length_eq
    erw [Path.length_comp, alongSdpMap_length w h q hw a,
      alongSdpMap_length w h q hw b, hlen, hr]
  · intro e he
    erw [alongSdpMap_edges] at he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact Or.inr ⟨f, ha f hf, rfl⟩
  · intro e he
    erw [alongSdpMap_edges] at he
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
    exact ⟨f, hb f hf, rfl⟩
  · intro s hs
    obtain ⟨z, hz, heq⟩ := sdpCloseMap_vertices F b _ hs
    have hid := congrArg PresentVertex.id heq
    erw [leftAlongRawSdpGeodesic_vertex] at hid
    have hzq : z = ((Q q).initial s).1 := congrArg PresentVertex.mk
      (sdpCloseVertex_injective w h hid)
    exact ht s (hzq ▸ hz)


/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
First-entry localization and hatted exchange prove the full raw SDP exchange. -/
theorem leftAlongRawSdpGeodesicExchange_proved (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (q : SdpDomain)
    (hw : (W q) = hatCodes w h) : LeftAlongSdpRawGeodesicExchange w h q hw := by
  intro x hx y hy p hp
  obtain ⟨v, hv, hvy⟩ := hy
  have hyEq : y = (⟨hatLimitVertexMap w h v⟩ : PresentVertex w) :=
    (congrArg PresentVertex.mk hvy).symm
  subst y
  rcases hx with hx | ⟨u, hu, hux⟩
  · have hyHat : (⟨hatLimitVertexMap w h v⟩ : PresentVertex w) ∈ leftHatVertices w :=
      alloc_reachable (hatLimitExplicitInput w h) (kmswVertexAllocated_all _ ⟨v⟩)
    obtain ⟨z, hz, c, d, hsplit, hc, _⟩ :=
      leftAlongSdp_firstEntry_closedLeft w h q p hx hyHat
    obtain ⟨u, hu, huz⟩ := leftAlongSdpEntryLocalization_proved w h hfin q hw z hz
    have hzEq : z = (⟨hatLimitVertexMap w h u⟩ : PresentVertex w) :=
      (congrArg PresentVertex.mk huz).symm
    subst z
    have hd : IsShortest d := by
      have hh : IsShortest (c.comp d) := hsplit ▸ hp
      exact hh.of_comp_right
    obtain ⟨t, a, b, hlen, _, ha, hb, ht⟩ :=
      sdpCloseHat_exchange w h q hw ⟨u⟩ ⟨v⟩ hu hv d hd
    refine ⟨t, c.comp a, b, ?_, ?_, ?_, hb, ht⟩
    · rw [Path.length_comp, hsplit, Path.length_comp]
      omega
    · apply hp.of_length_eq
      simp only [Path.length_comp]
      rw [hsplit, Path.length_comp]
      omega
    · intro e he
      rw [pathEdgeList_comp] at he
      exact (List.mem_append.mp he).elim (hc e) (ha e)
  · have hxEq : x = (⟨hatLimitVertexMap w h u⟩ : PresentVertex w) :=
      (congrArg PresentVertex.mk hux).symm
    subst x
    exact sdpCloseHat_exchange w h q hw ⟨u⟩ ⟨v⟩ hu hv p hp


end DirectedDistances.Recursive
